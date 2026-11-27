(* 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Lists.Streams List Arith Lia ZifyNat ZifyN ZifyBool NArith ZArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---").
Arguments tm _ : simpl never.

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

(* ========================================================================== *)
(* Reachability Combinators & Micro-Step Automation                           *)
(* ========================================================================== *)

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma ps_trans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma sp_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Lemma evstep_eq_both {c1 c2 d1 d2 : Q * tape} :
  c1 -->* c2 -> c1 = d1 -> c2 = d2 -> d1 -->* d2.
Proof. intros H <- <-. exact H. Qed.

Lemma progress_eq_both {c1 c2 d1 d2 : Q * tape} :
  c1 -->+ c2 -> c1 = d1 -> c2 = d2 -> d1 -->+ d2.
Proof. intros H <- <-. exact H. Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; cbn [Streams.hd Streams.tl]; repeat rewrite <- const_unfold; reflexivity)
  || finish_progress.

Ltac fast_execute :=
  intros;
  repeat (
    lazymatch goal with
    | |- (?q, _) -->+ (?q, _) => try solve [fast_finish]
    | |- (?q, _) -->* (?q, _) => try solve [fast_finish]
    | _ => idtac
    end;
    fast_step).

Ltac fast_start_progress :=
  intros;
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  fast_execute.

(* ========================================================================== *)
(* List / Stream Power & Blank-Stream Helpers                                 *)
(* ========================================================================== *)

Lemma cons_zero_0inf : S0 >> 0inf = 0inf.
Proof. symmetry. apply const_unfold. Qed.

Lemma lpow_0 {A : Type} (u : list A) : u ^^ 0 = [].
Proof. reflexivity. Qed.

Lemma lpow_1 {A : Type} (u : list A) : u ^^ 1 = u.
Proof. cbn [lpow]. apply app_nil_r. Qed.

Lemma Str_app_nil (s : side) : [] *> s = s.
Proof. reflexivity. Qed.

Lemma Str_app_lpow_succ (u : list Sym) (k : nat) (s : side) :
  (u ^^ (k + 1)) *> s = u *> (u ^^ k) *> s.
Proof.
  replace (k + 1) with (S k) by lia.
  cbn [lpow]. apply Str_app_assoc.
Qed.

Lemma Str_app_lpow_comm (u : list Sym) (k : nat) (s : side) :
  (u ^^ k) *> u *> s = u *> (u ^^ k) *> s.
Proof.
  apply lpow_shift'.
Qed.

Lemma Str_app_lpow_add (u : list Sym) (a b : nat) (s : side) :
  (u ^^ (a + b)) *> s = (u ^^ a) *> (u ^^ b) *> s.
Proof.
  rewrite lpow_add. apply Str_app_assoc.
Qed.

Lemma pow_append_pow (u : list Sym) (a b : nat) (s : side) :
  (u ^^ a) *> (u ^^ b) *> s = (u ^^ (a + b)) *> s.
Proof.
  symmetry. apply Str_app_lpow_add.
Qed.

Lemma repeat_eq_lpow {A : Type} (a : A) (n : nat) :
  repeat a n = [a] ^^ n.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [repeat lpow app]. f_equal. exact IH.
Qed.

Lemma lpow_mul_comm {A : Type} (u : list A) (a b : nat) :
  (u ^^ a) ^^ b = u ^^ (a * b).
Proof.
  rewrite Nat.mul_comm. symmetry. apply lpow_mul.
Qed.

Lemma zeros_append_0inf (k : nat) : ([S0] ^^ k) *> 0inf = 0inf.
Proof.
  induction k as [| k IH]; [reflexivity |].
  cbn [lpow app Str_app]. rewrite IH. exact cons_zero_0inf.
Qed.

Lemma zpad_eq_0inf (k : nat) : repeat S0 k *> 0inf = 0inf.
Proof.
  rewrite repeat_eq_lpow. apply zeros_append_0inf.
Qed.

(* ========================================================================== *)
(* Part 1: Tape Words, Transitions, Towers, & Era Lemmas                      *)
(* ========================================================================== *)

Inductive Mode : Type :=
  | mA
  | mD
  | mE
  | mHalt.

Inductive RTok : Type :=
  | rpair (z o c : nat)
  | rmid (c : nat).

Definition pWord (z o : nat) : list Sym :=
  repeat S0 z ++ repeat S1 (o + 1).

Definition wZ : list Sym := [S0; S0; S1].
Definition wT : list Sym := [S0; S1; S1].
Definition wLM : list Sym := [S0; S1; S1; S0; S0; S1; S0; S0; S1].
Definition wRM : list Sym := [S0; S1; S1; S0; S1; S1; S0; S0; S1].

Fixpoint encR (ts : list RTok) : side :=
  match ts with
  | [] => 0inf
  | rpair z o c :: rest => ((pWord z o) ^^ (c + 1)) *> encR rest
  | rmid c :: rest => (wRM ^^ (c + 1)) *> encR rest
  end.

Definition cfgA (l r : side) : Q * tape := l {{A}}> r.
Definition cfgD (l r : side) : Q * tape := l <{{D}} r.
Definition cfgE (l r : side) : Q * tape := l <{{E}} r.
Definition cfgHalt (l r : side) : Q * tape := (S1 >> l) <{{F}} r.

Definition decPairR (z o c : nat) (ts : list RTok) : list RTok :=
  match c with
  | 0 => ts
  | S c' => rpair z o c' :: ts
  end.

Definition decMidR (c : nat) (ts : list RTok) : list RTok :=
  match c with
  | 0 => ts
  | S c' => rmid c' :: ts
  end.

Definition pushRM (k : nat) (R : list RTok) : list RTok :=
  match k with
  | 0 => R
  | S k' =>
    match R with
    | rmid c :: ts => rmid (c + k' + 1) :: ts
    | ts => rmid k' :: ts
    end
  end.

Definition coalesceR (R : list RTok) : list RTok :=
  match R with
  | rpair 1 1 1 :: rpair 2 0 c1 :: rest =>
    pushRM 1 (decPairR 2 0 c1 rest)
  | _ => R
  end.

Definition pushRPPre (z o k' : nat) (R : list RTok) : list RTok :=
  match R with
  | rpair z' o' c :: ts =>
    if andb (Nat.eqb z z') (Nat.eqb o o') then rpair z o (c + k' + 1) :: ts
    else rpair z o k' :: rpair z' o' c :: ts
  | ts => rpair z o k' :: ts
  end.

Definition pushRP (z o k : nat) (R : list RTok) : list RTok :=
  match k with
  | 0 => R
  | S k' => coalesceR (pushRPPre z o k' R)
  end.

Definition pushWRMSem (k : nat) (R : list RTok) : list RTok :=
  match k with
  | 0 => R
  | S k' => pushRM k' (pushRP 1 1 2 (pushRP 2 0 1 R))
  end.

Lemma pWord_2_0 : pWord 2 0 = wZ. Proof. reflexivity. Qed.
Lemma pWord_1_1 : pWord 1 1 = wT. Proof. reflexivity. Qed.
Lemma pWord_1_2 : pWord 1 2 = [S0; S1; S1; S1]. Proof. reflexivity. Qed.
Lemma pWord_1_0 : pWord 1 0 = [S0; S1]. Proof. reflexivity. Qed.
Lemma pWord_0_0 : pWord 0 0 = [S1]. Proof. reflexivity. Qed.
Lemma pWord_0_1 : pWord 0 1 = [S1; S1]. Proof. reflexivity. Qed.

Lemma pWord_zero_eq (o : nat) : pWord 0 o = [S1] ^^ (o + 1).
Proof.
  unfold pWord. cbn [repeat app]. apply repeat_eq_lpow.
Qed.

Lemma encR_decPairR (z o c : nat) (ts : list RTok) :
  (pWord z o) *> encR (decPairR z o c ts) = encR (rpair z o c :: ts).
Proof.
  destruct c as [| c'].
  - cbn [decPairR encR]. rewrite lpow_1. reflexivity.
  - cbn [decPairR encR]. replace (S c' + 1) with ((c' + 1) + 1) by lia.
    symmetry. apply Str_app_lpow_succ.
Qed.

Lemma encR_decMidR (c : nat) (ts : list RTok) :
  wRM *> encR (decMidR c ts) = encR (rmid c :: ts).
Proof.
  destruct c as [| c'].
  - cbn [decMidR encR]. rewrite lpow_1. reflexivity.
  - cbn [decMidR encR]. replace (S c' + 1) with ((c' + 1) + 1) by lia.
    symmetry. apply Str_app_lpow_succ.
Qed.

Lemma encR_pushRM (k : nat) (R : list RTok) :
  encR (pushRM k R) = (wRM ^^ k) *> encR R.
Proof.
  destruct k as [| k']; [reflexivity |].
  destruct R as [| [z' o' c | c] ts].
  - cbn [pushRM encR]. replace (k' + 1) with (S k') by lia. reflexivity.
  - cbn [pushRM encR]. replace (k' + 1) with (S k') by lia. reflexivity.
  - cbn [pushRM encR].
    replace (c + k' + 1 + 1) with ((S k') + (c + 1)) by lia.
    rewrite Str_app_lpow_add. reflexivity.
Qed.

Lemma encR_coalesceR (R : list RTok) :
  encR (coalesceR R) = encR R.
Proof.
  destruct R as [| [z0 o0 c0 | c0] R1]; [reflexivity | | reflexivity].
  destruct z0 as [| [| z0]]; try reflexivity.
  destruct o0 as [| [| o0]]; try reflexivity.
  destruct c0 as [| [| c0]]; try reflexivity.
  destruct R1 as [| [z1 o1 c1 | c1] rest]; [reflexivity | | reflexivity].
  destruct z1 as [| [| [| z1]]]; try reflexivity.
  destruct o1 as [| o1]; try reflexivity.
  cbn [coalesceR].
  rewrite encR_pushRM, lpow_1.
  pose proof (encR_decPairR 2 0 c1 rest) as htail.
  rewrite pWord_2_0 in htail.
  cbn [encR] in htail |- *.
  rewrite pWord_1_1, <- htail.
  reflexivity.
Qed.

Lemma encR_pushRP (z o k : nat) (R : list RTok) :
  encR (pushRP z o k R) = ((pWord z o) ^^ k) *> encR R.
Proof.
  destruct k as [| k']; [reflexivity |].
  cbn [pushRP]. rewrite encR_coalesceR.
  destruct R as [| [z' o' c | c] ts].
  - cbn [pushRPPre encR]. replace (k' + 1) with (S k') by lia. reflexivity.
  - cbn [pushRPPre].
    destruct (andb (Nat.eqb z z') (Nat.eqb o o')) eqn:Heq.
    + apply andb_true_iff in Heq. destruct Heq as [Hz Ho].
      apply Nat.eqb_eq in Hz. apply Nat.eqb_eq in Ho. subst z' o'.
      cbn [encR].
      replace (c + k' + 1 + 1) with ((S k') + (c + 1)) by lia.
      rewrite Str_app_lpow_add. reflexivity.
    + cbn [encR]. replace (k' + 1) with (S k') by lia. reflexivity.
  - cbn [pushRPPre encR]. replace (k' + 1) with (S k') by lia. reflexivity.
Qed.

Lemma encR_pushWRMSem (k : nat) (R : list RTok) :
  encR (pushWRMSem k R) = (wRM ^^ k) *> encR R.
Proof.
  destruct k as [| k']; [reflexivity |].
  cbn [pushWRMSem].
  rewrite encR_pushRM, !encR_pushRP, pWord_1_1, pWord_2_0.
  assert (h1 : (wT ^^ 2) *> (wZ ^^ 1) *> encR R = (wRM ^^ 1) *> encR R) by reflexivity.
  rewrite h1, pow_append_pow.
  replace (k' + 1) with (S k') by lia. reflexivity.
Qed.

(* ========================================================================== *)
(* Micro-Step & Word-Sweep Lemmas                                             *)
(* ========================================================================== *)

Lemma step_a_01 (l r : side) :
  cfgA l ([S0; S1] *> r) -->+ cfgA ([S0; S1] *> l) r.
Proof. unfold cfgA. fast_start_progress. Qed.

Lemma step_a_01_pow (k : nat) : forall (l r : side),
  cfgA l (([S0; S1] ^^ k) *> r) -->* cfgA (([S0; S1] ^^ k) *> l) r.
Proof.
  induction k as [| k IH]; intros l r.
  - apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite Str_app_lpow_succ.
    eapply etrans; [exact (pev (step_a_01 l _)) |].
    eapply etrans; [exact (IH ([S0; S1] *> l) r) |].
    rewrite Str_app_lpow_comm, <- Str_app_lpow_succ.
    apply evstep_refl.
Qed.

Lemma step_a_101 (l r : side) :
  cfgA l ([S1; S0; S1] *> r) -->+ cfgA (wZ *> l) r.
Proof. unfold cfgA, wZ. fast_start_progress. Qed.

Lemma step_a_101_pow (k : nat) : forall (l r : side),
  cfgA l ([S1] *> (wT ^^ k) *> r) -->* cfgA ((wZ ^^ k) *> l) ([S1] *> r).
Proof.
  induction k as [| k IH]; intros l r.
  - apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite Str_app_lpow_succ.
    change ([S1] *> wT *> (wT ^^ k) *> r) with ([S1; S0; S1] *> [S1] *> (wT ^^ k) *> r).
    eapply etrans; [exact (pev (step_a_101 l _)) |].
    eapply etrans; [exact (IH (wZ *> l) r) |].
    rewrite Str_app_lpow_comm, <- Str_app_lpow_succ.
    apply evstep_refl.
Qed.

Lemma step_d_001 (l r : side) :
  cfgD (wZ *> l) r -->+ cfgD l (wT *> r).
Proof. unfold cfgD, wZ, wT. fast_start_progress. Qed.

Lemma step_d_001_pow (k : nat) : forall (l r : side),
  cfgD ((wZ ^^ k) *> l) r -->* cfgD l ((wT ^^ k) *> r).
Proof.
  induction k as [| k IH]; intros l r.
  - apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite Str_app_lpow_succ.
    eapply etrans; [exact (pev (step_d_001 _ r)) |].
    eapply etrans; [exact (IH l (wT *> r)) |].
    rewrite Str_app_lpow_comm, <- Str_app_lpow_succ.
    apply evstep_refl.
Qed.

Lemma step_e_one (l r : side) :
  cfgE ([S1] *> l) r -->+ cfgE l ([S0] *> r).
Proof. unfold cfgE. fast_start_progress. Qed.

Lemma step_e_ones (k : nat) : forall (l r : side),
  cfgE (([S1] ^^ k) *> l) r -->* cfgE l (([S0] ^^ k) *> r).
Proof.
  induction k as [| k IH]; intros l r.
  - apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite Str_app_lpow_succ.
    eapply etrans; [exact (pev (step_e_one _ r)) |].
    eapply etrans; [exact (IH l ([S0] *> r)) |].
    rewrite Str_app_lpow_comm, <- Str_app_lpow_succ.
    apply evstep_refl.
Qed.

Lemma exit_a_00 (l r : side) :
  cfgA l ([S0; S0] *> r) -->+ cfgD l ([S0; S1] *> r).
Proof. unfold cfgA, cfgD. fast_start_progress. Qed.

Lemma exit_a_11 (l r : side) :
  cfgA l ([S1; S1] *> r) -->+ cfgE ([S1] *> l) ([S0] *> r).
Proof. unfold cfgA, cfgE. fast_start_progress. Qed.

Lemma exit_a_100 (l r : side) :
  cfgA l ([S1; S0; S0] *> r) -->+ cfgE ([S1] *> l) ([S0; S1] *> r).
Proof. unfold cfgA, cfgE. fast_start_progress. Qed.

Lemma exit_d_11_halt (l r : side) :
  cfgD ([S1; S1] *> l) r -->+ cfgHalt l ([S0] *> r).
Proof. unfold cfgD, cfgHalt. fast_start_progress. Qed.

Lemma exit_d_100 (l r : side) :
  cfgD ([S1; S0; S0] *> l) r -->+ cfgD l ([S0; S1; S0] *> r).
Proof. unfold cfgD. fast_start_progress. Qed.

Lemma exit_d_101 (l r : side) :
  cfgD ([S1; S0; S1] *> l) r -->+ cfgE ([S1] *> l) ([S0; S1] *> r).
Proof. unfold cfgD, cfgE. fast_start_progress. Qed.

Lemma exit_d_01 (l r : side) :
  cfgD ([S0; S1] *> l) r -->+ cfgA ([S0] *> l) ([S1] *> r).
Proof. unfold cfgD, cfgA. fast_start_progress. Qed.

Lemma exit_d_0000 (l r : side) :
  cfgD ([S0; S0; S0; S0] *> l) r -->+ cfgA ([S0; S1] *> l) ([S1; S1] *> r).
Proof. unfold cfgD, cfgA. fast_start_progress. Qed.

Lemma exit_d_0001 (l r : side) :
  cfgD ([S0; S0; S0; S1] *> l) r -->+ cfgE ([S1] *> l) ([S0; S1; S1] *> r).
Proof. unfold cfgD, cfgE. fast_start_progress. Qed.

Lemma exit_e_0_r1 (l r : side) :
  cfgE ([S0] *> l) ([S1] *> r) -->+ cfgA ([S0; S0] *> l) r.
Proof. unfold cfgE, cfgA. fast_start_progress. Qed.

Lemma exit_e_00_r0 (l r : side) :
  cfgE ([S0; S0] *> l) ([S0] *> r) -->+ cfgA ([S0; S1] *> l) ([S1] *> r).
Proof. unfold cfgE, cfgA. fast_start_progress. Qed.

Lemma exit_e_01_r0 (l r : side) :
  cfgE ([S0; S1] *> l) ([S0] *> r) -->+ cfgE ([S1] *> l) ([S0; S1] *> r).
Proof. unfold cfgE. fast_start_progress. Qed.

Lemma step_a_1011_wT (l r : side) :
  cfgA l ([S1; S0; S1; S1] *> wT *> r) -->+ cfgA (wZ *> l) ([S1; S0; S1; S1] *> r).
Proof. unfold cfgA, wT, wZ. fast_start_progress. Qed.

Lemma step_a_1011_wT_pow (k : nat) : forall (l r : side),
  cfgA l ([S1; S0; S1; S1] *> (wT ^^ k) *> r) -->* cfgA ((wZ ^^ k) *> l) ([S1; S0; S1; S1] *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_a_1011_wT l _)) |].
  eapply etrans; [exact (IH (wZ *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_a_1011_wT_pow_plus (k : nat) (l r : side) :
  cfgA l ([S1; S0; S1; S1] *> (wT ^^ (k + 1)) *> r) -->+
  cfgA ((wZ ^^ (k + 1)) *> l) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_a_1011_wT l _) |].
  eapply etrans; [exact (step_a_1011_wT_pow k (wZ *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_a_1011_wZ (l r : side) :
  cfgA l ([S1; S0; S1; S1] *> wZ *> r) -->+ cfgA (wT *> l) ([S1; S0; S1; S1] *> r).
Proof. unfold cfgA, wZ, wT. fast_start_progress. Qed.

Lemma step_a_1011_wZ_pow (k : nat) : forall (l r : side),
  cfgA l ([S1; S0; S1; S1] *> (wZ ^^ k) *> r) -->* cfgA ((wT ^^ k) *> l) ([S1; S0; S1; S1] *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_a_1011_wZ l _)) |].
  eapply etrans; [exact (IH (wT *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_a_1011_wZ_pow_plus (k : nat) (l r : side) :
  cfgA l ([S1; S0; S1; S1] *> (wZ ^^ (k + 1)) *> r) -->+
  cfgA ((wT ^^ (k + 1)) *> l) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_a_1011_wZ l _) |].
  eapply etrans; [exact (step_a_1011_wZ_pow k (wT *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_a_1011_wRM (l r : side) :
  cfgA l ([S1; S0; S1; S1] *> wRM *> r) -->+ cfgA (wLM *> l) ([S1; S0; S1; S1] *> r).
Proof.
  change (wRM *> r) with (wT *> wT *> wZ *> r).
  eapply ptrans; [exact (step_a_1011_wT l (wT *> wZ *> r)) |].
  eapply ptrans; [exact (step_a_1011_wT (wZ *> l) (wZ *> r)) |].
  exact (step_a_1011_wZ (wZ *> wZ *> l) r).
Qed.

Lemma step_a_1011_wRM_pow (k : nat) : forall (l r : side),
  cfgA l ([S1; S0; S1; S1] *> (wRM ^^ k) *> r) -->* cfgA ((wLM ^^ k) *> l) ([S1; S0; S1; S1] *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_a_1011_wRM l _)) |].
  eapply etrans; [exact (IH (wLM *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_a_1011_wRM_pow_plus (k : nat) (l r : side) :
  cfgA l ([S1; S0; S1; S1] *> (wRM ^^ (k + 1)) *> r) -->+
  cfgA ((wLM ^^ (k + 1)) *> l) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_a_1011_wRM l _) |].
  eapply etrans; [exact (step_a_1011_wRM_pow k (wLM *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_e_1011_wZ (l r : side) :
  cfgE ([S1; S0; S1; S1] *> wZ *> l) r -->+ cfgE ([S1; S0; S1; S1] *> l) (wT *> r).
Proof. unfold cfgE, wZ, wT. fast_start_progress. Qed.

Lemma step_e_1011_wZ_pow (k : nat) : forall (l r : side),
  cfgE ([S1; S0; S1; S1] *> (wZ ^^ k) *> l) r -->* cfgE ([S1; S0; S1; S1] *> l) ((wT ^^ k) *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_e_1011_wZ _ r)) |].
  eapply etrans; [exact (IH l (wT *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_e_1011_wZ_pow_plus (k : nat) (l r : side) :
  cfgE ([S1; S0; S1; S1] *> (wZ ^^ (k + 1)) *> l) r -->+
  cfgE ([S1; S0; S1; S1] *> l) ((wT ^^ (k + 1)) *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_e_1011_wZ _ r) |].
  eapply etrans; [exact (step_e_1011_wZ_pow k l (wT *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_e_1011_wT (l r : side) :
  cfgE ([S1; S0; S1; S1] *> wT *> l) r -->+ cfgE ([S1; S0; S1; S1] *> l) (wZ *> r).
Proof. unfold cfgE, wT, wZ. fast_start_progress. Qed.

Lemma step_e_1011_wT_pow (k : nat) : forall (l r : side),
  cfgE ([S1; S0; S1; S1] *> (wT ^^ k) *> l) r -->* cfgE ([S1; S0; S1; S1] *> l) ((wZ ^^ k) *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_e_1011_wT _ r)) |].
  eapply etrans; [exact (IH l (wZ *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_e_1011_wT_pow_plus (k : nat) (l r : side) :
  cfgE ([S1; S0; S1; S1] *> (wT ^^ (k + 1)) *> l) r -->+
  cfgE ([S1; S0; S1; S1] *> l) ((wZ ^^ (k + 1)) *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_e_1011_wT _ r) |].
  eapply etrans; [exact (step_e_1011_wT_pow k l (wZ *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_e_1011_wLM (l r : side) :
  cfgE ([S1; S0; S1; S1] *> wLM *> l) r -->+ cfgE ([S1; S0; S1; S1] *> l) (wRM *> r).
Proof.
  change (wLM *> l) with (wT *> wZ *> wZ *> l).
  eapply ptrans; [exact (step_e_1011_wT (wZ *> wZ *> l) r) |].
  eapply ptrans; [exact (step_e_1011_wZ (wZ *> l) (wZ *> r)) |].
  exact (step_e_1011_wZ l (wT *> wZ *> r)).
Qed.

Lemma step_e_1011_wLM_pow (k : nat) : forall (l r : side),
  cfgE ([S1; S0; S1; S1] *> (wLM ^^ k) *> l) r -->* cfgE ([S1; S0; S1; S1] *> l) ((wRM ^^ k) *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_e_1011_wLM _ r)) |].
  eapply etrans; [exact (IH l (wRM *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_e_1011_wLM_pow_plus (k : nat) (l r : side) :
  cfgE ([S1; S0; S1; S1] *> (wLM ^^ (k + 1)) *> l) r -->+
  cfgE ([S1; S0; S1; S1] *> l) ((wRM ^^ (k + 1)) *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_e_1011_wLM _ r) |].
  eapply etrans; [exact (step_e_1011_wLM_pow k l (wRM *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_dl_1_wZ (l r : side) :
  cfgD ([S1] *> wZ *> l) ([S0; S1] *> r) -->+ cfgD ([S1] *> l) ([S0; S1] *> wZ *> r).
Proof. unfold cfgD, wZ. fast_start_progress. Qed.

Lemma step_dl_1_wZ_pow (k : nat) : forall (l r : side),
  cfgD ([S1] *> (wZ ^^ k) *> l) ([S0; S1] *> r) -->*
  cfgD ([S1] *> l) ([S0; S1] *> (wZ ^^ k) *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_dl_1_wZ _ r)) |].
  eapply etrans; [exact (IH l (wZ *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_dl_1_wZ_pow_plus (k : nat) (l r : side) :
  cfgD ([S1] *> (wZ ^^ (k + 1)) *> l) ([S0; S1] *> r) -->+
  cfgD ([S1] *> l) ([S0; S1] *> (wZ ^^ (k + 1)) *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_dl_1_wZ _ r) |].
  eapply etrans; [exact (step_dl_1_wZ_pow k l (wZ *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_el_11_01 (l r : side) :
  cfgE ([S1; S1] *> wT *> l) ([S0; S1] *> r) -->+
  cfgE ([S1; S1] *> l) ([S0; S1] *> wZ *> r).
Proof. unfold cfgE, wT, wZ. fast_start_progress. Qed.

Lemma step_el_11_01_pow (k : nat) : forall (l r : side),
  cfgE ([S1; S1] *> (wT ^^ k) *> l) ([S0; S1] *> r) -->*
  cfgE ([S1; S1] *> l) ([S0; S1] *> (wZ ^^ k) *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_el_11_01 _ r)) |].
  eapply etrans; [exact (IH l (wZ *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_el_11_01_pow_plus (k : nat) (l r : side) :
  cfgE ([S1; S1] *> (wT ^^ (k + 1)) *> l) ([S0; S1] *> r) -->+
  cfgE ([S1; S1] *> l) ([S0; S1] *> (wZ ^^ (k + 1)) *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_el_11_01 _ r) |].
  eapply etrans; [exact (step_el_11_01_pow k l (wZ *> r)) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_ar_10101_wZ (l r : side) :
  cfgA l ([S1; S0; S1; S0; S1; S0; S1; S1] *> wZ *> r) -->+
  cfgA (wT *> l) ([S1; S0; S1; S0; S1; S0; S1; S1] *> r).
Proof. unfold cfgA, wZ, wT. fast_start_progress. Qed.

Lemma step_ar_10101_wZ_pow (k : nat) : forall (l r : side),
  cfgA l ([S1; S0; S1; S0; S1; S0; S1; S1] *> (wZ ^^ k) *> r) -->*
  cfgA ((wT ^^ k) *> l) ([S1; S0; S1; S0; S1; S0; S1; S1] *> r).
Proof.
  induction k as [| k IH]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite Str_app_lpow_succ.
  eapply etrans; [exact (pev (step_ar_10101_wZ l _)) |].
  eapply etrans; [exact (IH (wT *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

Lemma step_ar_10101_wZ_pow_plus (k : nat) (l r : side) :
  cfgA l ([S1; S0; S1; S0; S1; S0; S1; S1] *> (wZ ^^ (k + 1)) *> r) -->+
  cfgA ((wT ^^ (k + 1)) *> l) ([S1; S0; S1; S0; S1; S0; S1; S1] *> r).
Proof.
  rewrite Str_app_lpow_succ.
  eapply ps_trans; [exact (step_ar_10101_wZ l _) |].
  eapply etrans; [exact (step_ar_10101_wZ_pow k (wT *> l) r) |].
  rewrite Str_app_lpow_comm, <- Str_app_lpow_succ. apply evstep_refl.
Qed.

(* ========================================================================== *)
(* Middle-Region (`MidItem`) Round-Trips                                      *)
(* ========================================================================== *)

Inductive MidItem : Type :=
  | mi_mid (cnt : nat)
  | mi_t (cnt : nat)
  | mi_z (cnt : nat).

Definition encMidItemR (m : MidItem) (r : side) : side :=
  match m with
  | mi_mid k => (wRM ^^ k) *> r
  | mi_t k => (wT ^^ k) *> r
  | mi_z k => (wZ ^^ k) *> r
  end.

Fixpoint encMidR (ms : list MidItem) (r : side) : side :=
  match ms with
  | [] => r
  | m :: ms' => encMidItemR m (encMidR ms' r)
  end.

Lemma encMidR_append (xs ys : list MidItem) (r : side) :
  encMidR (xs ++ ys) r = encMidR xs (encMidR ys r).
Proof.
  induction xs as [| m xs IH]; [reflexivity |].
  cbn [app encMidR]. rewrite IH. reflexivity.
Qed.

Fixpoint rebuildMR (ms : list MidItem) (tail : list RTok) : list RTok :=
  match ms with
  | [] => tail
  | mi_mid k :: ms' => pushWRMSem k (rebuildMR ms' tail)
  | mi_t k :: ms' => pushRP 1 1 k (rebuildMR ms' tail)
  | mi_z k :: ms' => pushRP 2 0 k (rebuildMR ms' tail)
  end.

Lemma encR_rebuildMR (ms : list MidItem) (tail : list RTok) :
  encR (rebuildMR ms tail) = encMidR ms (encR tail).
Proof.
  induction ms as [| [k | k | k] ms IH]; [reflexivity | | |];
    cbn [rebuildMR encMidR encMidItemR].
  - rewrite encR_pushWRMSem, IH. reflexivity.
  - rewrite encR_pushRP, pWord_1_1, IH. reflexivity.
  - rewrite encR_pushRP, pWord_2_0, IH. reflexivity.
Qed.

Definition encMidItemL (m : MidItem) (l : side) : side :=
  match m with
  | mi_mid k => (wLM ^^ k) *> l
  | mi_t k => (wT ^^ k) *> l
  | mi_z k => (wZ ^^ k) *> l
  end.

Fixpoint encMidL (ms : list MidItem) (l : side) : side :=
  match ms with
  | [] => l
  | m :: ms' => encMidItemL m (encMidL ms' l)
  end.

Lemma bounce_M_thm {W W' : side}
  (hW : forall l, cfgA l ([S1; S0; S1; S1] *> W) -->+ cfgE ([S1; S0; S1; S1] *> l) W') :
  forall (ms : list MidItem) (l : side),
    cfgA l ([S1; S0; S1; S1] *> encMidR ms W) -->+
    cfgE ([S1; S0; S1; S1] *> l) (encMidR ms W').
Proof.
  induction ms as [| [k | k | k] ms IH]; intros l; cbn [encMidR encMidItemR].
  - exact (hW l).
  - eapply sp_trans; [exact (step_a_1011_wRM_pow k l (encMidR ms W)) |].
    eapply ps_trans; [exact (IH ((wLM ^^ k) *> l)) |].
    exact (step_e_1011_wLM_pow k l (encMidR ms W')).
  - eapply sp_trans; [exact (step_a_1011_wT_pow k l (encMidR ms W)) |].
    eapply ps_trans; [exact (IH ((wZ ^^ k) *> l)) |].
    exact (step_e_1011_wZ_pow k l (encMidR ms W')).
  - eapply sp_trans; [exact (step_a_1011_wZ_pow k l (encMidR ms W)) |].
    eapply ps_trans; [exact (IH ((wT ^^ k) *> l)) |].
    exact (step_e_1011_wT_pow k l (encMidR ms W')).
Qed.

Lemma roundtrip_mid_L {T_in T_out : side}
  (hT : forall r, cfgE ([S1; S0; S1; S1] *> T_in) r -->+ cfgA T_out ([S1; S0; S1; S1] *> r)) :
  forall (ms : list MidItem) (r : side),
    cfgE ([S1; S0; S1; S1] *> encMidL ms T_in) r -->+
    cfgA (encMidL ms T_out) ([S1; S0; S1; S1] *> r).
Proof.
  induction ms as [| [k | k | k] ms IH]; intros r; cbn [encMidL encMidItemL].
  - exact (hT r).
  - eapply sp_trans; [exact (step_e_1011_wLM_pow k (encMidL ms T_in) r) |].
    eapply ps_trans; [exact (IH ((wRM ^^ k) *> r)) |].
    exact (step_a_1011_wRM_pow k (encMidL ms T_out) r).
  - eapply sp_trans; [exact (step_e_1011_wT_pow k (encMidL ms T_in) r) |].
    eapply ps_trans; [exact (IH ((wZ ^^ k) *> r)) |].
    exact (step_a_1011_wZ_pow k (encMidL ms T_out) r).
  - eapply sp_trans; [exact (step_e_1011_wZ_pow k (encMidL ms T_in) r) |].
    eapply ps_trans; [exact (IH ((wT ^^ k) *> r)) |].
    exact (step_a_1011_wT_pow k (encMidL ms T_out) r).
Qed.

(* ========================================================================== *)
(* Tower Reflections (`refl_d0_1`, `refl_d1_empty_1`, `refl_d1_mid_1`)        *)
(* ========================================================================== *)

Definition d1P0 : list Sym := [S0; S1; S0; S0; S1; S0; S0; S1].
Definition d1P1 : list Sym := [S0; S0; S0; S1; S0; S1; S1; S0; S0; S1].

Lemma refl_d0_1 (l r : side) :
  cfgA l ([S1; S0; S1; S1] *> [S0; S1; S1; S1] *> wT *> r) -->+
  cfgE ([S1; S0; S1; S1] *> l) (wT *> [S0; S1; S1; S1] *> r).
Proof. unfold cfgA, cfgE, wT. fast_start_progress. Qed.

Lemma d1_entry_8 (l r : side) :
  cfgA l ([S1; S0; S1; S1; S0; S1; S0; S1] *> r) -->+ cfgA (d1P0 *> l) r.
Proof. unfold cfgA, d1P0. fast_start_progress. Qed.

Lemma d1_mid_35 (l r : side) :
  cfgE ([S1; S0; S1; S1; S0; S1] *> d1P0 *> l) ([S0] *> r) -->+
  cfgA (d1P1 *> l) ([S1; S0; S1; S1; S0] *> r).
Proof. unfold cfgE, cfgA, d1P0, d1P1. fast_start_progress. Qed.

Lemma d1_exit_50 (l r : side) :
  cfgE ([S1; S0; S1; S1] *> d1P1 *> l) ([S0] *> r) -->+
  cfgE ([S1; S0; S1; S1] *> l) (wT *> [S0; S1; S0; S1] *> wT *> [S0] *> r).
Proof. unfold cfgE, d1P1, wT. fast_start_progress. Qed.

Lemma d1_empty_tf0_57 (l r : side) :
  cfgA l ([S1; S0; S1; S1; S0; S1; S0; S1; S0; S1; S1; S1] *> wT *> wT *> r) -->+
  cfgE ([S1; S0; S1; S1] *> d1P1 *> l) ([S0] *> [S1; S1; S1] *> r).
Proof. unfold cfgA, cfgE, wT, d1P1. fast_start_progress. Qed.

Lemma d1_empty_tf0_107 (l r : side) :
  cfgA l ([S1; S0; S1; S1; S0; S1; S0; S1; S0; S1; S1; S1] *> wT *> wT *> r) -->+
  cfgE ([S1; S0; S1; S1] *> l) (wT *> [S0; S1; S0; S1] *> wT *> [S0; S1; S1; S1] *> r).
Proof.
  eapply ptrans; [exact (d1_empty_tf0_57 l r) |].
  exact (d1_exit_50 l ([S1; S1; S1] *> r)).
Qed.

Lemma d1_empty_turn_14 (l r : side) :
  cfgA (wZ *> l) ([S1; S1] *> wT *> r) -->+
  cfgE ([S1; S0; S1; S1] *> l) ([S0; S1; S1; S1] *> r).
Proof. unfold cfgA, cfgE, wZ, wT. fast_start_progress. Qed.

Lemma d1_turn_wZ_12 (l r : side) :
  cfgA (wZ *> l) ([S1] *> wZ *> r) -->+ cfgA (wT *> l) ([S1; S0; S1; S1] *> r).
Proof. unfold cfgA, wZ, wT. fast_start_progress. Qed.

Lemma wT_pow_succ_0111 (k : nat) (r : side) :
  (wT ^^ (k + 1)) *> [S0; S1; S1; S1] *> r =
  [S0; S1] *> [S1] *> (wT ^^ (k + 1)) *> [S1] *> r.
Proof.
  induction k as [| k IH].
  - rewrite lpow_1. reflexivity.
  - replace (S k + 1) with ((k + 1) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (k + 1)).
    rewrite IH.
    change (wT *> [S0; S1] *> [S1] *> (wT ^^ (k + 1)) *> [S1] *> r)
      with ([S0; S1] *> [S1] *> wT *> (wT ^^ (k + 1)) *> [S1] *> r).
    rewrite <- (Str_app_lpow_succ wT (k + 1)).
    reflexivity.
Qed.

Lemma wT_pow_succ_succ_split (u : nat) (r : side) :
  (wT ^^ (u + 2)) *> r = [S0; S1] *> [S1] *> (wT ^^ (u + 1)) *> r.
Proof.
  induction u as [| u IH].
  - reflexivity.
  - replace (S u + 2) with ((u + 2) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (u + 2)), IH.
    replace (S u + 1) with ((u + 1) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (u + 1)).
    reflexivity.
Qed.

Lemma wT_pow_0111_zero_head (k : nat) (r : side) :
  exists tail,
    (wT ^^ k) *> [S0; S1; S1; S1] *> r = [S0] *> tail /\
    [S1; S0; S1; S1; S0] *> tail = [S1; S0; S1; S1] *> (wT ^^ k) *> [S0; S1; S1; S1] *> r /\
    wT *> [S0] *> tail = (wT ^^ (k + 1)) *> [S0; S1; S1; S1] *> r.
Proof.
  destruct k as [| k'].
  - exists ([S1; S1; S1] *> r). rewrite lpow_1. repeat split; reflexivity.
  - replace (S k') with (k' + 1) by lia.
    exists ([S1; S1] *> (wT ^^ k') *> [S0; S1; S1; S1] *> r).
    rewrite (Str_app_lpow_succ wT (k' + 1)), (Str_app_lpow_succ wT k').
    repeat split; reflexivity.
Qed.

Lemma wT_pow_wZ_zero_head (u : nat) (r : side) :
  exists tail,
    (wT ^^ u) *> wZ *> r = [S0] *> tail /\
    [S1; S0; S1; S1; S0] *> tail = [S1; S0; S1; S1] *> (wT ^^ u) *> wZ *> r /\
    wT *> [S0] *> tail = (wT ^^ (u + 1)) *> wZ *> r.
Proof.
  destruct u as [| u'].
  - exists ([S0; S1] *> r). rewrite lpow_1. repeat split; reflexivity.
  - replace (S u') with (u' + 1) by lia.
    exists ([S1; S1] *> (wT ^^ u') *> wZ *> r).
    rewrite (Str_app_lpow_succ wT (u' + 1)), (Str_app_lpow_succ wT u').
    repeat split; reflexivity.
Qed.

Lemma refl_d1_empty_1 (tf b : nat) (l rt : side) :
  cfgA l ([S1; S0; S1; S1] *> [S0; S1; S0; S1] *> (wT ^^ tf) *>
    [S0; S1; S1; S1] *> (wT ^^ (b + 2)) *> rt) -->+
  cfgE ([S1; S0; S1; S1] *> l) (wT *> [S0; S1; S0; S1] *> (wT ^^ (tf + 1)) *>
    [S0; S1; S1; S1] *> (wT ^^ b) *> rt).
Proof.
  destruct tf as [| t'].
  - assert (hin :
      [S1; S0; S1; S1] *> [S0; S1; S0; S1] *> (wT ^^ 0) *>
        [S0; S1; S1; S1] *> (wT ^^ (b + 2)) *> rt =
      [S1; S0; S1; S1; S0; S1; S0; S1; S0; S1; S1; S1] *> wT *> wT *> (wT ^^ b) *> rt).
    { replace (b + 2) with (1 + (1 + b)) by lia.
      rewrite (Str_app_lpow_add wT 1 (1 + b)), (Str_app_lpow_add wT 1 b), lpow_1.
      reflexivity. }
    rewrite hin, lpow_1.
    exact (d1_empty_tf0_107 l ((wT ^^ b) *> rt)).
  - replace (S t') with (t' + 1) by lia.
    assert (hin :
      [S1; S0; S1; S1] *> [S0; S1; S0; S1] *> (wT ^^ (t' + 1)) *>
        [S0; S1; S1; S1] *> (wT ^^ (b + 2)) *> rt =
      [S1; S0; S1; S1; S0; S1; S0; S1] *> [S0; S1] *> [S1] *> (wT ^^ (t' + 1)) *>
        [S1] *> wT *> wT *> (wT ^^ b) *> rt).
    { rewrite (wT_pow_succ_0111 t' ((wT ^^ (b + 2)) *> rt)).
      replace (b + 2) with (1 + (1 + b)) by lia.
      rewrite (Str_app_lpow_add wT 1 (1 + b)), (Str_app_lpow_add wT 1 b), lpow_1.
      reflexivity. }
    rewrite hin.
    pose proof (d1_entry_8 l ([S0; S1] *> [S1] *> (wT ^^ (t' + 1)) *>
      [S1] *> wT *> wT *> (wT ^^ b) *> rt)) as h1.
    pose proof (step_a_01 (d1P0 *> l) ([S1] *> (wT ^^ (t' + 1)) *>
      [S1] *> wT *> wT *> (wT ^^ b) *> rt)) as h2.
    pose proof (step_a_101_pow (t' + 1) ([S0; S1] *> d1P0 *> l)
      ([S1] *> wT *> wT *> (wT ^^ b) *> rt)) as h3.
    rewrite (Str_app_lpow_succ wZ t') in h3.
    change ([S1] *> [S1] *> wT *> wT *> (wT ^^ b) *> rt)
      with ([S1; S1] *> wT *> wT *> (wT ^^ b) *> rt) in h3.
    pose proof (d1_empty_turn_14 ((wZ ^^ t') *> [S0; S1] *> d1P0 *> l)
      (wT *> (wT ^^ b) *> rt)) as h4.
    pose proof (step_e_1011_wZ_pow t' ([S0; S1] *> d1P0 *> l)
      ([S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt)) as h5.
    change ([S1; S0; S1; S1] *> [S0; S1] *> d1P0 *> l)
      with ([S1; S0; S1; S1; S0; S1] *> d1P0 *> l) in h5.
    destruct (wT_pow_0111_zero_head t' (wT *> (wT ^^ b) *> rt))
      as [tail1 [ht1_eq [ht1_mid _]]].
    rewrite ht1_eq in h5.
    pose proof (d1_mid_35 l tail1) as h6.
    rewrite ht1_mid in h6.
    pose proof (bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^^ b) *> rt))
      [mi_t t'] (d1P1 *> l)) as h7.
    cbn [encMidR encMidItemR] in h7.
    rewrite (Str_app_lpow_comm wT t'), <- (Str_app_lpow_succ wT t') in h7.
    destruct (wT_pow_0111_zero_head (t' + 1) ((wT ^^ b) *> rt))
      as [tail2 [ht2_eq [_ ht2_exit]]].
    rewrite ht2_eq in h7.
    pose proof (d1_exit_50 l tail2) as h8.
    rewrite ht2_exit in h8.
    exact (ptrans h1 (ptrans h2 (sp_trans h3 (ptrans h4
      (sp_trans h5 (ptrans h6 (ptrans h7 h8))))))).
Qed.

Lemma refl_d1_mid_1 (u cz b : nat) (ms' : list MidItem) (l rt : side) :
  cfgA l ([S1; S0; S1; S1] *> [S0; S1; S0; S1] *> (wT ^^ (u + 2)) *>
    encMidR (mi_z (cz + 1) :: ms') ([S0; S1; S1; S1] *> (wT ^^ (b + 2)) *> rt)) -->+
  cfgE ([S1; S0; S1; S1] *> l) (wT *> [S0; S1; S0; S1] *> (wT ^^ (u + 1)) *>
    encMidR (mi_z (cz + 1) :: ms') ((wT ^^ 2) *> [S0; S1; S1; S1] *> (wT ^^ b) *> rt)).
Proof.
  assert (hin :
    [S1; S0; S1; S1] *> [S0; S1; S0; S1] *> (wT ^^ (u + 2)) *>
      encMidR (mi_z (cz + 1) :: ms') ([S0; S1; S1; S1] *> (wT ^^ (b + 2)) *> rt) =
    [S1; S0; S1; S1; S0; S1; S0; S1] *> [S0; S1] *> [S1] *> (wT ^^ (u + 1)) *>
      wZ *> encMidR (mi_z cz :: ms')
        ([S0; S1; S1; S1] *> wT *> wT *> (wT ^^ b) *> rt)).
  { rewrite (wT_pow_succ_succ_split u).
    cbn [encMidR encMidItemR].
    rewrite (Str_app_lpow_succ wZ cz).
    replace (b + 2) with (1 + (1 + b)) by lia.
    rewrite (Str_app_lpow_add wT 1 (1 + b)), (Str_app_lpow_add wT 1 b), lpow_1.
    reflexivity. }
  rewrite hin.
  pose proof (d1_entry_8 l ([S0; S1] *> [S1] *> (wT ^^ (u + 1)) *>
    wZ *> encMidR (mi_z cz :: ms') ([S0; S1; S1; S1] *> wT *> wT *> (wT ^^ b) *> rt))) as h1.
  pose proof (step_a_01 (d1P0 *> l) ([S1] *> (wT ^^ (u + 1)) *>
    wZ *> encMidR (mi_z cz :: ms') ([S0; S1; S1; S1] *> wT *> wT *> (wT ^^ b) *> rt))) as h2.
  pose proof (step_a_101_pow (u + 1) ([S0; S1] *> d1P0 *> l)
    (wZ *> encMidR (mi_z cz :: ms') ([S0; S1; S1; S1] *> wT *> wT *> (wT ^^ b) *> rt))) as h3.
  rewrite (Str_app_lpow_succ wZ u) in h3.
  pose proof (d1_turn_wZ_12 ((wZ ^^ u) *> [S0; S1] *> d1P0 *> l)
    (encMidR (mi_z cz :: ms') ([S0; S1; S1; S1] *> wT *> wT *> (wT ^^ b) *> rt))) as h4.
  pose proof (bounce_M_thm (fun l' => refl_d0_1 l' (wT *> (wT ^^ b) *> rt))
    (mi_z cz :: ms') (wT *> (wZ ^^ u) *> [S0; S1] *> d1P0 *> l)) as h5.
  pose proof (step_e_1011_wT ((wZ ^^ u) *> [S0; S1] *> d1P0 *> l)
    (encMidR (mi_z cz :: ms') (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt))) as h6.
  assert (h6R :
    wZ *> encMidR (mi_z cz :: ms') (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt) =
    encMidR (mi_z (cz + 1) :: ms') (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt)).
  { cbn [encMidR encMidItemR]. symmetry. apply Str_app_lpow_succ. }
  rewrite h6R in h6.
  pose proof (step_e_1011_wZ_pow u ([S0; S1] *> d1P0 *> l)
    (encMidR (mi_z (cz + 1) :: ms') (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt))) as h7.
  change ([S1; S0; S1; S1] *> [S0; S1] *> d1P0 *> l)
    with ([S1; S0; S1; S1; S0; S1] *> d1P0 *> l) in h7.
  assert (h7R :
    (wT ^^ u) *> encMidR (mi_z (cz + 1) :: ms')
      (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt) =
    (wT ^^ u) *> wZ *> encMidR (mi_z cz :: ms')
      (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt)).
  { cbn [encMidR encMidItemR]. rewrite (Str_app_lpow_succ wZ cz). reflexivity. }
  destruct (wT_pow_wZ_zero_head u (encMidR (mi_z cz :: ms')
    (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt)))
    as [tail1 [ht1_eq [ht1_mid _]]].
  rewrite h7R, ht1_eq in h7.
  pose proof (d1_mid_35 l tail1) as h8.
  rewrite ht1_mid, <- h7R in h8.
  assert (h8R :
    [S1; S0; S1; S1] *> (wT ^^ u) *> encMidR (mi_z (cz + 1) :: ms')
      (wT *> [S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt) =
    [S1; S0; S1; S1] *> encMidR ([mi_t u] ++ (mi_z (cz + 1) :: ms') ++ [mi_t 1])
      ([S0; S1; S1; S1] *> wT *> (wT ^^ b) *> rt)).
  { rewrite !encMidR_append. cbn [encMidR encMidItemR]. rewrite lpow_1. reflexivity. }
  rewrite h8R in h8.
  pose proof (bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^^ b) *> rt))
    ([mi_t u] ++ (mi_z (cz + 1) :: ms') ++ [mi_t 1]) (d1P1 *> l)) as h9.
  assert (h9R :
    encMidR ([mi_t u] ++ (mi_z (cz + 1) :: ms') ++ [mi_t 1])
      (wT *> [S0; S1; S1; S1] *> (wT ^^ b) *> rt) =
    (wT ^^ u) *> wZ *> encMidR (mi_z cz :: ms')
      ((wT ^^ 2) *> [S0; S1; S1; S1] *> (wT ^^ b) *> rt)).
  { rewrite !encMidR_append. cbn [encMidR encMidItemR].
    rewrite (Str_app_lpow_succ wZ cz). reflexivity. }
  destruct (wT_pow_wZ_zero_head u (encMidR (mi_z cz :: ms')
    ((wT ^^ 2) *> [S0; S1; S1; S1] *> (wT ^^ b) *> rt)))
    as [tail2 [ht2_eq [_ ht2_exit]]].
  rewrite h9R, ht2_eq in h9.
  pose proof (d1_exit_50 l tail2) as h10.
  rewrite ht2_exit in h10.
  assert (h10R :
    (wT ^^ (u + 1)) *> wZ *> encMidR (mi_z cz :: ms')
      ((wT ^^ 2) *> [S0; S1; S1; S1] *> (wT ^^ b) *> rt) =
    (wT ^^ (u + 1)) *> encMidR (mi_z (cz + 1) :: ms')
      ((wT ^^ 2) *> [S0; S1; S1; S1] *> (wT ^^ b) *> rt)).
  { cbn [encMidR encMidItemR]. rewrite (Str_app_lpow_succ wZ cz). reflexivity. }
  rewrite h10R in h10.
  exact (ptrans h1 (ptrans h2 (sp_trans h3 (ptrans h4 (ptrans h5
    (ptrans h6 (sp_trans h7 (ptrans h8 (ptrans h9 h10))))))))).
Qed.

(* ========================================================================== *)
(* `TowerD01` & Single-Step Reflection                                        *)
(* ========================================================================== *)

Inductive TowerD01 : Type :=
  | td0 (B : nat) (rt : list RTok)
  | td1Empty (tf B : nat) (rt : list RTok)
  | td1Mid (tf cz : nat) (ms' : list MidItem) (B : nat) (rt : list RTok).

Definition TowerWF (tw : TowerD01) : Prop :=
  match tw with
  | td0 _ _ => True
  | td1Empty _ _ _ => True
  | td1Mid tf _ _ _ _ => 2 <= tf
  end.

Definition maxReflD01 (tw : TowerD01) : nat :=
  match tw with
  | td0 vb _ => vb
  | td1Empty _ vb _ => vb / 2
  | td1Mid tf _ _ vb _ => Nat.min (vb / 2) (tf - 1)
  end.

Definition buildAdvTowerD01 (tw : TowerD01) (n : nat) : list RTok :=
  match tw with
  | td0 vb rt =>
    pushRP 1 2 1 (pushRP 1 1 (vb - n) rt)
  | td1Empty tf vb rt =>
    let inner := pushRP 1 2 1 (pushRP 1 1 (vb - 2 * n) rt) in
    pushRP 1 0 2 (pushRP 1 1 (tf + n) inner)
  | td1Mid tf cz ms' vb rt =>
    let inner := pushRP 1 2 1 (pushRP 1 1 (vb - 2 * n) rt) in
    let afterM := rebuildMR (mi_z (cz + 1) :: ms') (pushRP 1 1 (2 * n) inner) in
    pushRP 1 0 2 (pushRP 1 1 (tf - n) afterM)
  end.

Lemma refl_tower_d01_step (tw : TowerD01) (htw : TowerWF tw)
  (j : nat) (hj : j < maxReflD01 tw) (l : side) :
  cfgA l ([S1; S0; S1; S1] *> encR (buildAdvTowerD01 tw j)) -->+
  cfgE ([S1; S0; S1; S1] *> l) (wT *> encR (buildAdvTowerD01 tw (j + 1))).
Proof.
  destruct tw as [vb rt | tf vb rt | tf cz ms' vb rt].
  - cbn [maxReflD01] in hj.
    cbn [buildAdvTowerD01].
    rewrite !encR_pushRP, pWord_1_2, pWord_1_1, lpow_1.
    replace (vb - j) with ((vb - (j + 1)) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (vb - (j + 1))).
    exact (refl_d0_1 l ((wT ^^ (vb - (j + 1))) *> encR rt)).
  - cbn [maxReflD01] in hj.
    cbn [buildAdvTowerD01].
    rewrite !encR_pushRP, pWord_1_0, pWord_1_1, pWord_1_2, lpow_1.
    change (([S0; S1] ^^ 2)) with [S0; S1; S0; S1].
    replace (vb - 2 * j) with ((vb - 2 * (j + 1)) + 2) by lia.
    replace (tf + (j + 1)) with ((tf + j) + 1) by lia.
    exact (refl_d1_empty_1 (tf + j) (vb - 2 * (j + 1)) l (encR rt)).
  - cbn [TowerWF] in htw.
    cbn [maxReflD01] in hj.
    set (u := tf - (j + 1) - 1).
    set (b := vb - 2 * (j + 1)).
    assert (hu : tf - j = u + 2) by lia.
    assert (hu1 : tf - (j + 1) = u + 1) by lia.
    assert (hb : vb - 2 * j = b + 2) by lia.
    eapply progress_eq_both;
      [exact (refl_d1_mid_1 u cz b (ms' ++ [mi_t (2 * j)]) l (encR rt)) | |].
    + unfold buildAdvTowerD01.
      rewrite !encR_pushRP, !encR_rebuildMR, !encR_pushRP,
        !pWord_1_0, !pWord_1_1, !pWord_1_2, !lpow_1.
      change ([S0; S1] ^^ 2) with [S0; S1; S0; S1].
      rewrite hu, hb.
      cbn [encMidR]. rewrite encMidR_append. cbn [encMidR encMidItemR].
      reflexivity.
    + unfold buildAdvTowerD01.
      rewrite !encR_pushRP, !encR_rebuildMR, !encR_pushRP,
        !pWord_1_0, !pWord_1_1, !pWord_1_2, !lpow_1.
      change ([S0; S1] ^^ 2) with [S0; S1; S0; S1].
      fold b. rewrite hu1.
      cbn [encMidR]. rewrite encMidR_append. cbn [encMidR encMidItemR].
      rewrite pow_append_pow. replace (2 * j + 2) with (2 * (j + 1)) by lia.
      reflexivity.
Qed.

(* ========================================================================== *)
(* Era 1: `era_conv_loop`                                                     *)
(* ========================================================================== *)

Lemma ec_entry_6 (l r : side) :
  cfgE ([S1] *> wZ *> wZ *> l) (wT *> r) -->+
  cfgA (wT *> wZ *> l) ([S1; S0; S1; S1] *> r).
Proof. unfold cfgE, cfgA, wZ, wT. fast_start_progress. Qed.

Lemma ec_right_6 (l : side) :
  cfgA l ([S1; S0; S1] *> 0inf) -->+ cfgD (wZ *> l) ([S0; S1] *> 0inf).
Proof.
  eapply ptrans; [exact (step_a_101 l 0inf) |].
  assert (hd : 0inf = [S0; S0] *> 0inf).
  { cbn [Str_app]. rewrite !cons_zero_0inf. reflexivity. }
  rewrite hd at 1.
  exact (exit_a_00 (wZ *> l) 0inf).
Qed.

Lemma step_d_01 (l r : side) :
  cfgD ([S0; S1] *> l) r -->+ cfgA ([S0] *> l) ([S1] *> r).
Proof. exact (exit_d_01 l r). Qed.

Lemma ec_exit_5 (l r : side) :
  cfgD ([S0; S0; S0; S1] *> l) r -->+ cfgE ([S1] *> l) (wT *> r).
Proof. unfold cfgD, cfgE, wT. fast_start_progress. Qed.

Lemma era_conv_one (b' : nat) (l : side) :
  cfgE ([S1] *> (wZ ^^ 2) *> wZ *> l) ((wT ^^ (b' + 2)) *> [S0; S1] *> 0inf) -->+
  cfgE ([S1] *> wZ *> l) ((wT ^^ (b' + 6)) *> [S0; S1] *> 0inf).
Proof.
  change ((wZ ^^ 2) *> wZ *> l) with (wZ *> wZ *> wZ *> l).
  replace (b' + 2) with ((b' + 1) + 1) by lia.
  rewrite (Str_app_lpow_succ wT (b' + 1)).
  pose proof (ec_entry_6 (wZ *> l) ((wT ^^ (b' + 1)) *> [S0; S1] *> 0inf)) as h1.
  assert (h1R :
    [S1; S0; S1; S1] *> (wT ^^ (b' + 1)) *> [S0; S1] *> 0inf =
    [S1] *> (wT ^^ (b' + 2)) *> [S0; S1] *> 0inf).
  { replace (b' + 2) with ((b' + 1) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (b' + 1)). reflexivity. }
  rewrite h1R in h1.
  pose proof (step_a_101_pow (b' + 2) (wT *> wZ *> wZ *> l) ([S0; S1] *> 0inf)) as h2.
  pose proof (ec_right_6 ((wZ ^^ (b' + 2)) *> wT *> wZ *> wZ *> l)) as h3.
  rewrite <- (Str_app_lpow_succ wZ (b' + 2)) in h3.
  replace (b' + 2 + 1) with (b' + 3) in h3 by lia.
  pose proof (step_d_001_pow (b' + 3) (wT *> wZ *> wZ *> l) ([S0; S1] *> 0inf)) as h4.
  pose proof (step_d_01 ([S1] *> wZ *> wZ *> l) ((wT ^^ (b' + 3)) *> [S0; S1] *> 0inf)) as h5.
  pose proof (step_a_101_pow (b' + 3) ([S0; S1] *> wZ *> wZ *> l) ([S0; S1] *> 0inf)) as h6.
  pose proof (ec_right_6 ((wZ ^^ (b' + 3)) *> [S0; S1] *> wZ *> wZ *> l)) as h7.
  rewrite <- (Str_app_lpow_succ wZ (b' + 3)) in h7.
  replace (b' + 3 + 1) with (b' + 4) in h7 by lia.
  pose proof (step_d_001_pow (b' + 4) ([S0; S1] *> wZ *> wZ *> l) ([S0; S1] *> 0inf)) as h8.
  pose proof (step_d_01 (wZ *> wZ *> l) ((wT ^^ (b' + 4)) *> [S0; S1] *> 0inf)) as h9.
  change ([S0] *> wZ *> wZ *> l) with ([S0; S0; S0; S1] *> wZ *> l) in h9.
  pose proof (step_a_101_pow (b' + 4) ([S0; S0; S0; S1] *> wZ *> l) ([S0; S1] *> 0inf)) as h10.
  pose proof (ec_right_6 ((wZ ^^ (b' + 4)) *> [S0; S0; S0; S1] *> wZ *> l)) as h11.
  rewrite <- (Str_app_lpow_succ wZ (b' + 4)) in h11.
  replace (b' + 4 + 1) with (b' + 5) in h11 by lia.
  pose proof (step_d_001_pow (b' + 5) ([S0; S0; S0; S1] *> wZ *> l) ([S0; S1] *> 0inf)) as h12.
  pose proof (ec_exit_5 (wZ *> l) ((wT ^^ (b' + 5)) *> [S0; S1] *> 0inf)) as h13.
  rewrite <- (Str_app_lpow_succ wT (b' + 5)) in h13.
  replace (b' + 5 + 1) with (b' + 6) in h13 by lia.
  exact (ptrans h1 (sp_trans h2 (ptrans h3 (sp_trans h4 (ptrans h5
    (sp_trans h6 (ptrans h7 (sp_trans h8 (ptrans h9 (sp_trans h10
      (ptrans h11 (sp_trans h12 h13)))))))))))).
Qed.

Lemma era_conv_loop (K : nat) : forall (z_rem b' : nat) (l : side),
  cfgE ([S1] *> (wZ ^^ (2 * K + (z_rem + 1))) *> l) ((wT ^^ (b' + 2)) *> [S0; S1] *> 0inf) -->*
  cfgE ([S1] *> (wZ ^^ (z_rem + 1)) *> l) ((wT ^^ (b' + 2 + 4 * K)) *> [S0; S1] *> 0inf).
Proof.
  induction K as [| K IH]; intros z_rem b' l.
  - replace (2 * 0 + (z_rem + 1)) with (z_rem + 1) by lia.
    replace (b' + 2 + 4 * 0) with (b' + 2) by lia.
    apply evstep_refl.
  - replace (2 * S K + (z_rem + 1)) with (2 + (2 * K + (z_rem + 1))) by lia.
    rewrite (Str_app_lpow_add wZ 2 (2 * K + (z_rem + 1))).
    pose proof (era_conv_one b' ((wZ ^^ (2 * K + z_rem)) *> l)) as h1.
    rewrite <- (Str_app_lpow_succ wZ (2 * K + z_rem)) in h1.
    replace ((2 * K + z_rem) + 1) with (2 * K + (z_rem + 1)) in h1 by lia.
    replace (b' + 6) with ((b' + 4) + 2) in h1 by lia.
    pose proof (IH z_rem (b' + 4) l) as h2.
    replace ((b' + 4) + 2 + 4 * K) with (b' + 2 + 4 * S K) in h2 by lia.
    exact (etrans (pev h1) h2).
Qed.

Lemma era_conv_loop_plus (K z_rem b' : nat) (l : side) (hK : 1 <= K) :
  cfgE ([S1] *> (wZ ^^ (2 * K + (z_rem + 1))) *> l) ((wT ^^ (b' + 2)) *> [S0; S1] *> 0inf) -->+
  cfgE ([S1] *> (wZ ^^ (z_rem + 1)) *> l) ((wT ^^ (b' + 2 + 4 * K)) *> [S0; S1] *> 0inf).
Proof.
  destruct K as [| K']; [lia |].
  replace (2 * S K' + (z_rem + 1)) with (2 + (2 * K' + (z_rem + 1))) by lia.
  rewrite (Str_app_lpow_add wZ 2 (2 * K' + (z_rem + 1))).
  pose proof (era_conv_one b' ((wZ ^^ (2 * K' + z_rem)) *> l)) as h1.
  rewrite <- (Str_app_lpow_succ wZ (2 * K' + z_rem)) in h1.
  replace ((2 * K' + z_rem) + 1) with (2 * K' + (z_rem + 1)) in h1 by lia.
  replace (b' + 6) with ((b' + 4) + 2) in h1 by lia.
  pose proof (era_conv_loop K' z_rem (b' + 4) l) as h2.
  replace ((b' + 4) + 2 + 4 * K') with (b' + 2 + 4 * S K') in h2 by lia.
  exact (ps_trans h1 h2).
Qed.

(* ========================================================================== *)
(* Left-Boundary Turns (`left_turn_0..5`)                                     *)
(* ========================================================================== *)

Definition tailL0 : side := wT *> [S0; S1] *> 0inf.
Definition tailL1 : side := wT *> wZ *> 0inf.
Definition tailL2 : side := wT *> [S0; S1] *> wZ *> [S0; S1] *> 0inf.
Definition tailL3 : side := wT *> wZ *> [S0; S1; S0; S1] *> 0inf.
Definition tailL4 : side := wT *> wZ *> [S0; S0; S0; S1] *> [S0; S1] *> 0inf.
Definition tailL5 : side := wT *> [S0; S1; S0; S1; S0; S1] *> wZ *> [S0; S1] *> 0inf.
Definition tailL6 : side := wLM *> tailL0.

Lemma left_turn_0 (r : side) :
  cfgE ([S1; S0; S1; S1] *> tailL0) r -->+ cfgA tailL1 ([S1; S0; S1; S1] *> r).
Proof.
  unfold tailL0, tailL1.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 15) at 1.
  unfold cfgE, cfgA, wT, wZ. cbn [repeat]. fast_start_progress.
Qed.

Lemma left_turn_1 (r : side) :
  cfgE ([S1; S0; S1; S1] *> tailL1) r -->+ cfgA tailL2 ([S1; S0; S1; S1] *> r).
Proof.
  unfold tailL1, tailL2.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 12) at 1.
  unfold cfgE, cfgA, wT, wZ. cbn [repeat]. fast_start_progress.
Qed.

Lemma left_turn_2 (r : side) :
  cfgE ([S1; S0; S1; S1] *> tailL2) r -->+ cfgA tailL3 ([S1; S0; S1; S1] *> r).
Proof.
  unfold tailL2, tailL3.
  rewrite <- (zpad_eq_0inf 16).
  unfold cfgE, cfgA, wT, wZ. cbn [repeat]. fast_start_progress.
Qed.

Lemma left_turn_3 (r : side) :
  cfgE ([S1; S0; S1; S1] *> tailL3) r -->+ cfgA tailL4 ([S1; S0; S1; S1] *> r).
Proof.
  unfold tailL3, tailL4.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 14) at 1.
  unfold cfgE, cfgA, wT, wZ. cbn [repeat]. fast_start_progress.
Qed.

Lemma left_turn_4 (r : side) :
  cfgE ([S1; S0; S1; S1] *> tailL4) r -->+ cfgA tailL5 ([S1; S0; S1; S1] *> r).
Proof.
  unfold tailL4, tailL5.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 14) at 1.
  unfold cfgE, cfgA, wT, wZ. cbn [repeat]. fast_start_progress.
Qed.

Lemma left_turn_5 (r : side) :
  cfgE ([S1; S0; S1; S1] *> tailL5) r -->+ cfgA tailL6 ([S1; S0; S1; S1] *> r).
Proof.
  unfold tailL5, tailL6, tailL0.
  rewrite <- (zpad_eq_0inf 16).
  unfold cfgE, cfgA, wT, wZ, wLM. cbn [repeat]. fast_start_progress.
Qed.

(* ========================================================================== *)
(* Era 2: `era_E_loop` (`E_L` Right-Reflection Era for `d in {0, 1}`)         *)
(* ========================================================================== *)

Definition eL1 : list Sym := [S0; S1; S1; S0; S1; S0; S0; S1; S0; S1].
Definition eL2 : list Sym := [S0; S1; S1; S0; S0; S1; S0; S1; S0; S1].
Definition eL3 : list Sym := [S0; S1; S1; S0; S0; S1; S0; S0; S0; S1; S0; S1].
Definition eL4 : list Sym := [S0; S1; S1; S0; S1; S0; S1; S0; S1; S0; S0; S1; S0; S1].
Definition eL5 : list Sym := [S0; S1; S1; S0; S0; S1; S0; S0; S1; S0; S1; S1; S0; S1].

Lemma eraE_turn_0 (r : side) :
  cfgE ([S1; S0; S1; S1] *> 0inf) (wT *> wZ *> r) -->+
  cfgA (eL1 *> 0inf) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 12) at 1.
  unfold cfgE, cfgA, wT, wZ, eL1. cbn [repeat]. fast_start_progress.
Qed.

Lemma eraE_turn_1 (r : side) :
  cfgE ([S1; S0; S1; S1] *> eL1 *> 0inf) r -->+
  cfgA (eL2 *> 0inf) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite <- (zpad_eq_0inf 16).
  unfold cfgE, cfgA, eL1, eL2. cbn [repeat]. fast_start_progress.
Qed.

Lemma eraE_turn_2 (r : side) :
  cfgE ([S1; S0; S1; S1] *> eL2 *> 0inf) r -->+
  cfgA (eL3 *> 0inf) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 14) at 1.
  unfold cfgE, cfgA, eL2, eL3. cbn [repeat]. fast_start_progress.
Qed.

Lemma eraE_turn_3 (r : side) :
  cfgE ([S1; S0; S1; S1] *> eL3 *> 0inf) r -->+
  cfgA (eL4 *> 0inf) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 14) at 1.
  unfold cfgE, cfgA, eL3, eL4. cbn [repeat]. fast_start_progress.
Qed.

Lemma eraE_turn_4 (r : side) :
  cfgE ([S1; S0; S1; S1] *> eL4 *> 0inf) r -->+
  cfgA (eL5 *> 0inf) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite <- (zpad_eq_0inf 16).
  unfold cfgE, cfgA, eL4, eL5. cbn [repeat]. fast_start_progress.
Qed.

Lemma eraE_turn_5a (r : side) :
  cfgE ([S1; S0; S1; S1] *> eL5 *> 0inf) r -->+
  cfgE 0inf ((wZ ^^ 3) *> wRM *> r).
Proof.
  rewrite <- (zpad_eq_0inf 16).
  unfold cfgE, eL5, wZ, wRM. cbn [lpow app repeat]. fast_start_progress.
Qed.

Lemma eraE_turn_5b (r : side) :
  cfgE 0inf ((wZ ^^ 3) *> wRM *> r) -->+
  cfgA (wLM *> wT *> wZ *> 0inf) ([S1; S0; S1; S1] *> r).
Proof.
  rewrite <- (zpad_eq_0inf 16), <- (zpad_eq_0inf 15) at 1.
  unfold cfgE, cfgA, wZ, wRM, wLM, wT. cbn [lpow app repeat]. fast_start_progress.
Qed.

Lemma eraE_turn_5 (r : side) :
  cfgE ([S1; S0; S1; S1] *> eL5 *> 0inf) r -->+
  cfgA (wLM *> wT *> wZ *> 0inf) ([S1; S0; S1; S1] *> r).
Proof.
  exact (ptrans (eraE_turn_5a r) (eraE_turn_5b r)).
Qed.

Definition eraECfg (ms : list MidItem) (tw : TowerD01) (j : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> wZ *> (wRM ^^ j) *>
      encMidR ms ((wT ^^ (6 * j)) *> encR (buildAdvTowerD01 tw (6 * j)))).

Lemma eraE_advance_t (ms : list MidItem) (j k : nat) (W : side) :
  encMidR ([mi_mid j] ++ ms ++ [mi_t k]) (wT *> W) =
  encMidR ([mi_mid j] ++ ms ++ [mi_t (k + 1)]) W.
Proof.
  rewrite !encMidR_append. cbn [encMidR encMidItemR].
  rewrite (Str_app_lpow_comm wT k), <- (Str_app_lpow_succ wT k).
  reflexivity.
Qed.

Lemma era_E_one_cycle (ms : list MidItem) (tw : TowerD01) (htw : TowerWF tw)
  (j : nat) (hj : 6 * (j + 1) <= maxReflD01 tw) :
  eraECfg ms tw j -->+ eraECfg ms tw (j + 1).
Proof.
  unfold eraECfg.
  assert (hR0 :
    (wRM ^^ j) *> encMidR ms ((wT ^^ (6 * j)) *> encR (buildAdvTowerD01 tw (6 * j))) =
    encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * j)]) (encR (buildAdvTowerD01 tw (6 * j)))).
  { rewrite !encMidR_append. reflexivity. }
  rewrite hR0.
  assert (hj0 : 6 * j < maxReflD01 tw) by lia.
  assert (hj1 : 6 * j + 1 < maxReflD01 tw) by lia.
  assert (hj2 : 6 * j + 2 < maxReflD01 tw) by lia.
  assert (hj3 : 6 * j + 3 < maxReflD01 tw) by lia.
  assert (hj4 : 6 * j + 4 < maxReflD01 tw) by lia.
  assert (hj5 : 6 * j + 5 < maxReflD01 tw) by lia.
  pose proof (eraE_turn_0
    (encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * j)]) (encR (buildAdvTowerD01 tw (6 * j))))) as t0.
  pose proof (bounce_M_thm (refl_tower_d01_step tw htw (6 * j) hj0)
    ([mi_mid j] ++ ms ++ [mi_t (6 * j)]) (eL1 *> 0inf)) as b0.
  rewrite eraE_advance_t in b0.
  pose proof (eraE_turn_1
    (encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * j + 1)]) (encR (buildAdvTowerD01 tw (6 * j + 1))))) as t1.
  pose proof (bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 1) hj1)
    ([mi_mid j] ++ ms ++ [mi_t (6 * j + 1)]) (eL2 *> 0inf)) as b1.
  rewrite eraE_advance_t in b1.
  replace (6 * j + 1 + 1) with (6 * j + 2) in b1 by lia.
  pose proof (eraE_turn_2
    (encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * j + 2)]) (encR (buildAdvTowerD01 tw (6 * j + 2))))) as t2.
  pose proof (bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 2) hj2)
    ([mi_mid j] ++ ms ++ [mi_t (6 * j + 2)]) (eL3 *> 0inf)) as b2.
  rewrite eraE_advance_t in b2.
  replace (6 * j + 2 + 1) with (6 * j + 3) in b2 by lia.
  pose proof (eraE_turn_3
    (encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * j + 3)]) (encR (buildAdvTowerD01 tw (6 * j + 3))))) as t3.
  pose proof (bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 3) hj3)
    ([mi_mid j] ++ ms ++ [mi_t (6 * j + 3)]) (eL4 *> 0inf)) as b3.
  rewrite eraE_advance_t in b3.
  replace (6 * j + 3 + 1) with (6 * j + 4) in b3 by lia.
  pose proof (eraE_turn_4
    (encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * j + 4)]) (encR (buildAdvTowerD01 tw (6 * j + 4))))) as t4.
  pose proof (bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 4) hj4)
    ([mi_mid j] ++ ms ++ [mi_t (6 * j + 4)]) (eL5 *> 0inf)) as b4.
  rewrite eraE_advance_t in b4.
  replace (6 * j + 4 + 1) with (6 * j + 5) in b4 by lia.
  pose proof (eraE_turn_5
    (encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * j + 5)]) (encR (buildAdvTowerD01 tw (6 * j + 5))))) as t5.
  pose proof (bounce_M_thm (refl_tower_d01_step tw htw (6 * j + 5) hj5)
    ([mi_mid j] ++ ms ++ [mi_t (6 * j + 5)]) (wLM *> wT *> wZ *> 0inf)) as b5.
  rewrite eraE_advance_t in b5.
  replace (6 * j + 5 + 1) with (6 * (j + 1)) in b5 by lia.
  assert (hR6 :
    encMidR ([mi_mid j] ++ ms ++ [mi_t (6 * (j + 1))])
      (encR (buildAdvTowerD01 tw (6 * (j + 1)))) =
    (wRM ^^ j) *> encMidR ms ((wT ^^ (6 * (j + 1))) *> encR (buildAdvTowerD01 tw (6 * (j + 1))))).
  { rewrite !encMidR_append. reflexivity. }
  rewrite hR6 in b5.
  pose proof (step_e_1011_wLM (wT *> wZ *> 0inf)
    ((wRM ^^ j) *> encMidR ms ((wT ^^ (6 * (j + 1))) *> encR (buildAdvTowerD01 tw (6 * (j + 1)))))) as e1.
  rewrite <- (Str_app_lpow_succ wRM j) in e1.
  pose proof (step_e_1011_wT (wZ *> 0inf)
    ((wRM ^^ (j + 1)) *> encMidR ms ((wT ^^ (6 * (j + 1))) *>
      encR (buildAdvTowerD01 tw (6 * (j + 1)))))) as e2.
  pose proof (step_e_1011_wZ 0inf
    (wZ *> (wRM ^^ (j + 1)) *> encMidR ms ((wT ^^ (6 * (j + 1))) *>
      encR (buildAdvTowerD01 tw (6 * (j + 1)))))) as e3.
  exact (ptrans t0 (ptrans b0 (ptrans t1 (ptrans b1 (ptrans t2 (ptrans b2
    (ptrans t3 (ptrans b3 (ptrans t4 (ptrans b4 (ptrans t5 (ptrans b5
      (ptrans e1 (ptrans e2 e3)))))))))))))).
Qed.

Lemma era_E_loop (ms : list MidItem) (tw : TowerD01) (htw : TowerWF tw) :
  forall (n : nat), 6 * n <= maxReflD01 tw ->
    eraECfg ms tw 0 -->* eraECfg ms tw n.
Proof.
  induction n as [| n IH]; intros hn.
  - apply evstep_refl.
  - assert (hn0 : 6 * n <= maxReflD01 tw) by lia.
    assert (hn1 : 6 * (n + 1) <= maxReflD01 tw) by lia.
    replace (S n) with (n + 1) by lia.
    exact (etrans (IH hn0) (pev (era_E_one_cycle ms tw htw n hn1))).
Qed.

Lemma era_E_loop_plus (ms : list MidItem) (tw : TowerD01) (htw : TowerWF tw)
  (n : nat) (hn1 : 1 <= n) (hn6 : 6 * n <= maxReflD01 tw) :
  eraECfg ms tw 0 -->+ eraECfg ms tw n.
Proof.
  destruct n as [| n']; [lia |].
  assert (h0 : 6 * (0 + 1) <= maxReflD01 tw) by lia.
  clear hn1.
  induction n' as [| n' IH].
  - exact (era_E_one_cycle ms tw htw 0 h0).
  - assert (hn6' : 6 * S n' <= maxReflD01 tw) by lia.
    assert (hstep : 6 * (S n' + 1) <= maxReflD01 tw) by lia.
    replace (S (S n')) with (S n' + 1) by lia.
    exact (ptrans (IH hn6') (era_E_one_cycle ms tw htw (S n') hstep)).
Qed.

(* ========================================================================== *)
(* Era 3: `era_L11_d0_loop`                                                   *)
(* ========================================================================== *)

Lemma L11_peel_01_13 (l r : side) :
  cfgE ([S1; S0; S1; S1; S0; S1] *> wLM *> l) ([S0] *> r) -->+
  cfgE ([S1; S0; S1; S1] *> wZ *> wZ *> l) ([S0; S1] *> wZ *> [S0] *> r).
Proof. unfold cfgE, wLM, wZ. fast_start_progress. Qed.

Lemma L11_mid_dip_23 (l r : side) :
  cfgA ((wZ ^^ 2) *> wLM *> l) ([S1; S0; S1; S1; S0; S1] *> wZ *> r) -->+
  cfgA ([S0; S1] *> (wZ ^^ 2) *> l) ([S1; S0; S1; S1] *> (wT ^^ 4) *> r).
Proof. unfold cfgA, wZ, wLM, wT. cbn [lpow app]. fast_start_progress. Qed.

Lemma L11_dip_wZ_30 (l r : side) :
  cfgE ([S1; S0; S1; S1; S0; S1] *> wZ *> l) (wT *> r) -->+
  cfgA ([S0; S1] *> l) ([S1; S0; S1; S1] *> (wT ^^ 2) *> r).
Proof. unfold cfgE, cfgA, wZ, wT. cbn [lpow app]. fast_start_progress. Qed.

Lemma encMidR_zero_head (ms : list MidItem) : forall (r : side),
  (exists tail, r = [S0] *> tail) -> exists tail', encMidR ms r = [S0] *> tail'.
Proof.
  induction ms as [| [[| k] | [| k] | [| k]] ms IH]; intros r hr;
    [exact hr | exact (IH r hr) | | exact (IH r hr) | | exact (IH r hr) |];
    cbn [encMidR encMidItemR];
    replace (S k) with (k + 1) by lia.
  - rewrite (Str_app_lpow_succ wRM k).
    exists ([S1; S1; S0; S1; S1; S0; S0; S1] *> (wRM ^^ k) *> encMidR ms r). reflexivity.
  - rewrite (Str_app_lpow_succ wT k).
    exists ([S1; S1] *> (wT ^^ k) *> encMidR ms r). reflexivity.
  - rewrite (Str_app_lpow_succ wZ k).
    exists ([S0; S1] *> (wZ ^^ k) *> encMidR ms r). reflexivity.
Qed.

Lemma wT_pow_zero_head (q : nat) (r : side) (hr : exists tail, r = [S0] *> tail) :
  exists tail', (wT ^^ q) *> r = [S0] *> tail'.
Proof.
  destruct q as [| q']; [exact hr |].
  replace (S q') with (q' + 1) by lia.
  rewrite (Str_app_lpow_succ wT q').
  exists ([S1; S1] *> (wT ^^ q') *> r). reflexivity.
Qed.

Lemma L11_step3 {T_in T_out : side}
  (m_mid m_out q tb b_rem : nat) (ms : list MidItem) (rt : side)
  (hT : forall r,
    cfgE ([S1; S0; S1; S1] *> (wLM ^^ m_mid) *> T_in) r -->+
    cfgA (wLM *> (wLM ^^ m_out) *> T_out) ([S1; S0; S1; S1] *> r)) :
  cfgE ([S1; S0; S1; S1] *> [S0; S1] *> wLM *> (wLM ^^ m_mid) *> T_in)
    ((wT ^^ q) *> encMidR ms ((wT ^^ (tb + 1)) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 2)) *> rt)) -->+
  cfgA ([S0; S1] *> (wLM ^^ m_out) *> T_out)
    ([S1; S0; S1; S1] *> (wT ^^ (q + 6)) *>
      encMidR ms ((wT ^^ (tb + 3)) *> [S0; S1; S1; S1] *> (wT ^^ b_rem) *> rt)).
Proof.
  set (R_start := (wT ^^ q) *> encMidR ms ((wT ^^ (tb + 1)) *>
    [S0; S1; S1; S1] *> (wT ^^ (b_rem + 2)) *> rt)).
  assert (hR0 : exists tail0, R_start = [S0] *> tail0).
  { unfold R_start. apply wT_pow_zero_head. apply encMidR_zero_head.
    rewrite (Str_app_lpow_succ wT tb).
    exists ([S1; S1] *> (wT ^^ tb) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 2)) *> rt).
    reflexivity. }
  destruct hR0 as [tail0 htail0].
  change ([S1; S0; S1; S1] *> [S0; S1] *> wLM *> (wLM ^^ m_mid) *> T_in)
    with ([S1; S0; S1; S1; S0; S1] *> wLM *> (wLM ^^ m_mid) *> T_in).
  pose proof (L11_peel_01_13 ((wLM ^^ m_mid) *> T_in) tail0) as s1.
  rewrite <- htail0 in s1.
  pose proof (step_e_1011_wZ (wZ *> (wLM ^^ m_mid) *> T_in) ([S0; S1] *> wZ *> R_start)) as s2a.
  pose proof (step_e_1011_wZ ((wLM ^^ m_mid) *> T_in) (wT *> [S0; S1] *> wZ *> R_start)) as s2b.
  pose proof (hT (wT *> wT *> [S0; S1] *> wZ *> R_start)) as s3.
  pose proof (step_a_1011_wT (wLM *> (wLM ^^ m_out) *> T_out)
    (wT *> [S0; S1] *> wZ *> R_start)) as s4a.
  pose proof (step_a_1011_wT (wZ *> wLM *> (wLM ^^ m_out) *> T_out)
    ([S0; S1] *> wZ *> R_start)) as s4b.
  change (wZ *> wZ *> wLM *> (wLM ^^ m_out) *> T_out)
    with ((wZ ^^ 2) *> wLM *> (wLM ^^ m_out) *> T_out) in s4b.
  change ([S1; S0; S1; S1] *> [S0; S1] *> wZ *> R_start)
    with ([S1; S0; S1; S1; S0; S1] *> wZ *> R_start) in s4b.
  pose proof (L11_mid_dip_23 ((wLM ^^ m_out) *> T_out) R_start) as s5.
  assert (hRA :
    (wT ^^ 4) *> R_start =
    encMidR ([mi_t (4 + q)] ++ ms ++ [mi_t (tb + 1)])
      ([S0; S1; S1; S1] *> wT *> (wT ^^ (b_rem + 1)) *> rt)).
  { unfold R_start. rewrite !encMidR_append. cbn [encMidR encMidItemR].
    replace (b_rem + 2) with ((b_rem + 1) + 1) by lia.
    rewrite (pow_append_pow wT 4 q), (Str_app_lpow_succ wT (b_rem + 1)).
    reflexivity. }
  rewrite hRA in s5.
  pose proof (bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^^ (b_rem + 1)) *> rt))
    ([mi_t (4 + q)] ++ ms ++ [mi_t (tb + 1)])
    ([S0; S1] *> (wZ ^^ 2) *> (wLM ^^ m_out) *> T_out)) as bA.
  change ([S1; S0; S1; S1] *> [S0; S1] *> (wZ ^^ 2) *> (wLM ^^ m_out) *> T_out)
    with ([S1; S0; S1; S1; S0; S1] *> wZ *> wZ *> (wLM ^^ m_out) *> T_out) in bA.
  assert (hbAR :
    encMidR ([mi_t (4 + q)] ++ ms ++ [mi_t (tb + 1)])
      (wT *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 1)) *> rt) =
    wT *> (wT ^^ (3 + q)) *> encMidR ms
      ((wT ^^ (tb + 2)) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 1)) *> rt)).
  { rewrite !encMidR_append. cbn [encMidR encMidItemR].
    replace (4 + q) with ((3 + q) + 1) by lia.
    replace (tb + 2) with ((tb + 1) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (3 + q)),
      (Str_app_lpow_comm wT (tb + 1)), <- (Str_app_lpow_succ wT (tb + 1)).
    reflexivity. }
  rewrite hbAR in bA.
  pose proof (L11_dip_wZ_30 (wZ *> (wLM ^^ m_out) *> T_out)
    ((wT ^^ (3 + q)) *> encMidR ms
      ((wT ^^ (tb + 2)) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 1)) *> rt))) as s6.
  assert (hs6R :
    (wT ^^ 2) *> (wT ^^ (3 + q)) *> encMidR ms
      ((wT ^^ (tb + 2)) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 1)) *> rt) =
    encMidR ([mi_t (5 + q)] ++ ms ++ [mi_t (tb + 2)])
      ([S0; S1; S1; S1] *> wT *> (wT ^^ b_rem) *> rt)).
  { rewrite !encMidR_append. cbn [encMidR encMidItemR].
    rewrite (pow_append_pow wT 2 (3 + q)), (Str_app_lpow_succ wT b_rem).
    replace (2 + (3 + q)) with (5 + q) by lia. reflexivity. }
  rewrite hs6R in s6.
  pose proof (bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^^ b_rem) *> rt))
    ([mi_t (5 + q)] ++ ms ++ [mi_t (tb + 2)])
    ([S0; S1] *> wZ *> (wLM ^^ m_out) *> T_out)) as bB.
  change ([S1; S0; S1; S1] *> [S0; S1] *> wZ *> (wLM ^^ m_out) *> T_out)
    with ([S1; S0; S1; S1; S0; S1] *> wZ *> (wLM ^^ m_out) *> T_out) in bB.
  assert (hbBR :
    encMidR ([mi_t (5 + q)] ++ ms ++ [mi_t (tb + 2)])
      (wT *> [S0; S1; S1; S1] *> (wT ^^ b_rem) *> rt) =
    wT *> (wT ^^ (4 + q)) *> encMidR ms
      ((wT ^^ (tb + 3)) *> [S0; S1; S1; S1] *> (wT ^^ b_rem) *> rt)).
  { rewrite !encMidR_append. cbn [encMidR encMidItemR].
    replace (5 + q) with ((4 + q) + 1) by lia.
    replace (tb + 3) with ((tb + 2) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (4 + q)),
      (Str_app_lpow_comm wT (tb + 2)), <- (Str_app_lpow_succ wT (tb + 2)).
    reflexivity. }
  rewrite hbBR in bB.
  pose proof (L11_dip_wZ_30 ((wLM ^^ m_out) *> T_out)
    ((wT ^^ (4 + q)) *> encMidR ms
      ((wT ^^ (tb + 3)) *> [S0; S1; S1; S1] *> (wT ^^ b_rem) *> rt))) as s7.
  rewrite (pow_append_pow wT 2 (4 + q)) in s7.
  replace (2 + (4 + q)) with (q + 6) in s7 by lia.
  exact (ptrans s1 (ptrans s2a (ptrans s2b (ptrans s3 (ptrans s4a
    (ptrans s4b (ptrans s5 (ptrans bA (ptrans s6 (ptrans bB s7)))))))))).
Qed.

Lemma L11_bounce_step {T_cur : side}
  (m_out q tb b_rem : nat) (ms : list MidItem) (rt : side) :
  cfgA ([S0; S1] *> (wLM ^^ (m_out + 1)) *> T_cur)
    ([S1; S0; S1; S1] *> (wT ^^ q) *>
      encMidR ms ((wT ^^ tb) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 3)) *> rt)) -->+
  cfgE ([S1; S0; S1; S1] *> [S0; S1] *> wLM *> (wLM ^^ m_out) *> T_cur)
    ((wT ^^ q) *> encMidR ms
      ((wT ^^ (tb + 1)) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 2)) *> rt)).
Proof.
  rewrite (Str_app_lpow_succ wLM m_out).
  assert (hR_in :
    (wT ^^ q) *> encMidR ms ((wT ^^ tb) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 3)) *> rt) =
    encMidR ([mi_t q] ++ ms ++ [mi_t tb]) ([S0; S1; S1; S1] *> wT *> (wT ^^ (b_rem + 2)) *> rt)).
  { rewrite !encMidR_append. cbn [encMidR encMidItemR].
    replace (b_rem + 3) with ((b_rem + 2) + 1) by lia.
    rewrite (Str_app_lpow_succ wT (b_rem + 2)). reflexivity. }
  rewrite hR_in.
  pose proof (bounce_M_thm (fun l' => refl_d0_1 l' ((wT ^^ (b_rem + 2)) *> rt))
    ([mi_t q] ++ ms ++ [mi_t tb]) ([S0; S1] *> wLM *> (wLM ^^ m_out) *> T_cur)) as hb.
  assert (hR_out :
    encMidR ([mi_t q] ++ ms ++ [mi_t tb])
      (wT *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 2)) *> rt) =
    (wT ^^ q) *> encMidR ms ((wT ^^ (tb + 1)) *> [S0; S1; S1; S1] *> (wT ^^ (b_rem + 2)) *> rt)).
  { rewrite !encMidR_append. cbn [encMidR encMidItemR].
    rewrite (Str_app_lpow_comm wT tb), <- (Str_app_lpow_succ wT tb). reflexivity. }
  rewrite hR_out in hb. exact hb.
Qed.

Lemma L11_turn_succ {T_in T_out : side}
  (hT : forall r, cfgE ([S1; S0; S1; S1] *> T_in) r -->+ cfgA T_out ([S1; S0; S1; S1] *> r))
  (m_out : nat) (r : side) :
  cfgE ([S1; S0; S1; S1] *> (wLM ^^ (m_out + 1)) *> T_in) r -->+
  cfgA (wLM *> (wLM ^^ m_out) *> T_out) ([S1; S0; S1; S1] *> r).
Proof.
  pose proof (roundtrip_mid_L hT [mi_mid (m_out + 1)] r) as h.
  cbn [encMidL encMidItemL] in h.
  rewrite (Str_app_lpow_succ wLM m_out T_out) in h.
  exact h.
Qed.

Lemma L11_turn_last (m_out : nat) (r : side) :
  cfgE ([S1; S0; S1; S1] *> (wLM ^^ m_out) *> tailL5) r -->+
  cfgA (wLM *> (wLM ^^ m_out) *> tailL0) ([S1; S0; S1; S1] *> r).
Proof.
  pose proof (roundtrip_mid_L left_turn_5 [mi_mid m_out] r) as h.
  cbn [encMidL encMidItemL] in h. unfold tailL6 in h.
  rewrite (Str_app_lpow_comm wLM m_out) in h.
  exact h.
Qed.

Definition eraL11Cfg (remMidL : nat) (ms : list MidItem) (B : nat) (rt : side)
  (K n : nat) : Q * tape :=
  cfgA ([S0; S1] *> (wLM ^^ (remMidL + 11 * (K - n))) *> tailL0)
    ([S1; S0; S1; S1] *> (wT ^^ (36 * n)) *>
      encMidR ms ((wT ^^ (18 * n)) *> [S0; S1; S1; S1] *> (wT ^^ (B - 18 * n)) *> rt)).

Lemma era_L11_d0_one (remMidL : nat) (ms : list MidItem) (B : nat) (rt : side)
  (K n : nat) (hn : n < K) (hB : 18 * K <= B) :
  eraL11Cfg remMidL ms B rt K n -->+ eraL11Cfg remMidL ms B rt K (n + 1).
Proof.
  unfold eraL11Cfg.
  set (m' := remMidL + 11 * (K - 1 - n)).
  set (q0 := 36 * n).
  set (tb0 := 18 * n).
  set (b0 := B - 18 * (n + 1)).
  replace (remMidL + 11 * (K - n)) with (((m' + 9) + 1) + 1) by lia.
  replace (B - tb0) with ((b0 + 15) + 3) by lia.
  replace (remMidL + 11 * (K - (n + 1))) with m' by lia.
  replace (36 * (n + 1)) with ((q0 + 30) + 6) by lia.
  replace (18 * (n + 1)) with ((tb0 + 15) + 3) by lia.
  eapply ptrans; [exact (@L11_bounce_step tailL0 ((m' + 9) + 1) q0 tb0 (b0 + 15) ms rt) |].
  eapply ptrans; [exact (L11_step3 ((m' + 9) + 1) (m' + 9) q0 tb0 (b0 + 15) ms rt
    (L11_turn_succ left_turn_0 (m' + 9))) |].
  replace (m' + 9) with (((m' + 7) + 1) + 1) by lia.
  replace (b0 + 15) with ((b0 + 12) + 3) by lia.
  eapply ptrans; [exact (@L11_bounce_step tailL1 ((m' + 7) + 1) (q0 + 6) (tb0 + 3) (b0 + 12) ms rt) |].
  eapply ptrans; [exact (L11_step3 ((m' + 7) + 1) (m' + 7) (q0 + 6) (tb0 + 3) (b0 + 12) ms rt
    (L11_turn_succ left_turn_1 (m' + 7))) |].
  replace (m' + 7) with (((m' + 5) + 1) + 1) by lia.
  replace (b0 + 12) with ((b0 + 9) + 3) by lia.
  replace ((q0 + 6) + 6) with (q0 + 12) by lia.
  replace ((tb0 + 3) + 3) with (tb0 + 6) by lia.
  eapply ptrans; [exact (@L11_bounce_step tailL2 ((m' + 5) + 1) (q0 + 12) (tb0 + 6) (b0 + 9) ms rt) |].
  eapply ptrans; [exact (L11_step3 ((m' + 5) + 1) (m' + 5) (q0 + 12) (tb0 + 6) (b0 + 9) ms rt
    (L11_turn_succ left_turn_2 (m' + 5))) |].
  replace (m' + 5) with (((m' + 3) + 1) + 1) by lia.
  replace (b0 + 9) with ((b0 + 6) + 3) by lia.
  replace ((q0 + 12) + 6) with (q0 + 18) by lia.
  replace ((tb0 + 6) + 3) with (tb0 + 9) by lia.
  eapply ptrans; [exact (@L11_bounce_step tailL3 ((m' + 3) + 1) (q0 + 18) (tb0 + 9) (b0 + 6) ms rt) |].
  eapply ptrans; [exact (L11_step3 ((m' + 3) + 1) (m' + 3) (q0 + 18) (tb0 + 9) (b0 + 6) ms rt
    (L11_turn_succ left_turn_3 (m' + 3))) |].
  replace (m' + 3) with (((m' + 1) + 1) + 1) by lia.
  replace (b0 + 6) with ((b0 + 3) + 3) by lia.
  replace ((q0 + 18) + 6) with (q0 + 24) by lia.
  replace ((tb0 + 9) + 3) with (tb0 + 12) by lia.
  eapply ptrans; [exact (@L11_bounce_step tailL4 ((m' + 1) + 1) (q0 + 24) (tb0 + 12) (b0 + 3) ms rt) |].
  eapply ptrans; [exact (L11_step3 ((m' + 1) + 1) (m' + 1) (q0 + 24) (tb0 + 12) (b0 + 3) ms rt
    (L11_turn_succ left_turn_4 (m' + 1))) |].
  replace ((q0 + 24) + 6) with (q0 + 30) by lia.
  replace ((tb0 + 12) + 3) with (tb0 + 15) by lia.
  eapply ptrans; [exact (@L11_bounce_step tailL5 m' (q0 + 30) (tb0 + 15) b0 ms rt) |].
  exact (L11_step3 m' m' (q0 + 30) (tb0 + 15) b0 ms rt (L11_turn_last m')).
Qed.

Lemma era_L11_d0_loop (remMidL : nat) (ms : list MidItem) (B : nat) (rt : side)
  (K : nat) (hB : 18 * K <= B) :
  forall (n : nat), n <= K ->
    eraL11Cfg remMidL ms B rt K 0 -->* eraL11Cfg remMidL ms B rt K n.
Proof.
  induction n as [| n IH]; intros hn.
  - apply evstep_refl.
  - assert (hn0 : n <= K) by lia.
    assert (hn1 : n < K) by lia.
    replace (S n) with (n + 1) by lia.
    exact (etrans (IH hn0) (pev (era_L11_d0_one remMidL ms B rt K n hn1 hB))).
Qed.

Lemma era_L11_d0_loop_plus (remMidL : nat) (ms : list MidItem) (B : nat) (rt : side)
  (K : nat) (hK : 1 <= K) (hB : 18 * K <= B) :
  eraL11Cfg remMidL ms B rt K 0 -->+ eraL11Cfg remMidL ms B rt K K.
Proof.
  destruct K as [| K']; [lia |].
  assert (h0 : 0 < S K') by lia.
  pose proof (era_L11_d0_one remMidL ms B rt (S K') 0 h0 hB) as s0.
  cbn [Nat.add] in s0.
  destruct K' as [| K'']; [exact s0 |].
  assert (hrec : forall m, m <= S K'' ->
    eraL11Cfg remMidL ms B rt (S (S K'')) 1 -->*
    eraL11Cfg remMidL ms B rt (S (S K'')) (1 + m)).
  { induction m as [| m IHm]; intros hm.
    - apply evstep_refl.
    - assert (hm0 : m <= S K'') by lia.
      assert (hm1 : 1 + m < S (S K'')) by lia.
      replace (1 + S m) with ((1 + m) + 1) by lia.
      exact (etrans (IHm hm0)
        (pev (era_L11_d0_one remMidL ms B rt (S (S K'')) (1 + m) hm1 hB))). }
  exact (ps_trans s0 (hrec (S K'') (Nat.le_refl _))).
Qed.

(* ========================================================================== *)
(* Part 2: Symbolic Linear-Form (`SymN`) Engine & Soundness                   *)
(* ========================================================================== *)

Lemma app_Str_app (u v : list Sym) (s : side) :
  (u ++ v) *> s = u *> v *> s.
Proof.
  induction u as [| a u IH]; [reflexivity |].
  cbn [app Str_app]. f_equal. exact IH.
Qed.

Lemma repeat_add {X : Type} (x : X) (a b : nat) :
  repeat x (a + b) = repeat x a ++ repeat x b.
Proof.
  induction a as [| a IH]; [reflexivity |].
  cbn [Nat.add repeat app]. f_equal. exact IH.
Qed.

Lemma pWord_add_zeros (z k o : nat) :
  pWord (z + k) o = ([S0] ^^ k) ++ pWord z o.
Proof.
  unfold pWord. rewrite (Nat.add_comm z k), repeat_add, <- app_assoc, repeat_eq_lpow.
  reflexivity.
Qed.

Lemma pWord_0_S (o' : nat) : pWord 0 (S o') = [S1] ++ pWord 0 o'.
Proof. reflexivity. Qed.

Lemma pWord_S_z (z' o : nat) : pWord (S z') o = [S0] ++ pWord z' o.
Proof. reflexivity. Qed.

Lemma pWord_1_S (o' : nat) : pWord 1 (S o') = [S0; S1; S1] ++ ([S1] ^^ o').
Proof.
  unfold pWord. replace (S o' + 1) with (S (S o')) by lia.
  cbn [repeat app]. rewrite repeat_eq_lpow. reflexivity.
Qed.

Lemma pWord_1_succ (k : nat) : pWord 1 (S k) = [S0; S1] ++ ([S1] ^^ (S k)).
Proof.
  unfold pWord. replace (S k + 1) with (S (S k)) by lia.
  remember (S k) as m eqn:Hm.
  cbn [repeat app]. rewrite repeat_eq_lpow. reflexivity.
Qed.

Lemma pWord_2_S (o' : nat) : pWord 2 (S o') = wZ ++ ([S1] ^^ (S o')).
Proof.
  unfold pWord, wZ. replace (S o' + 1) with (S (S o')) by lia.
  remember (S o') as m eqn:Hm.
  cbn [repeat app]. rewrite repeat_eq_lpow. reflexivity.
Qed.

Record SymN : Type := mkSymN {
  sc0 : N;
  sc1 : N;
  sc2 : N;
  sc3 : N;
  sc4 : N;
  sk  : N
}.

Record V5 : Type := mkV5 {
  v0 : nat;
  v1 : nat;
  v2 : nat;
  v3 : nat;
  v4 : nat
}.

Definition v5 := mkV5.

Definition evalSymN (v : V5) (x : SymN) : nat :=
  #(sc0 x) * v0 v + #(sc1 x) * v1 v + #(sc2 x) * v2 v +
  #(sc3 x) * v3 v + #(sc4 x) * v4 v + #(sk x).

Definition symConst (k : N) : SymN := mkSymN 0%N 0%N 0%N 0%N 0%N k.
Definition symZero : SymN := mkSymN 0%N 0%N 0%N 0%N 0%N 0%N.
Definition symOne : SymN := mkSymN 0%N 0%N 0%N 0%N 0%N 1%N.

Definition symIsConst (x : SymN) : bool :=
  andb (andb (andb (andb
    (N.eqb (sc0 x) 0%N)
    (N.eqb (sc1 x) 0%N))
    (N.eqb (sc2 x) 0%N))
    (N.eqb (sc3 x) 0%N))
    (N.eqb (sc4 x) 0%N).

Definition symIsZero (x : SymN) : bool :=
  andb (symIsConst x) (N.eqb (sk x) 0%N).

Definition symIsConst1 (x : SymN) : bool :=
  andb (symIsConst x) (N.eqb (sk x) 1%N).

Definition symAdd (x y : SymN) : SymN :=
  mkSymN (sc0 x + sc0 y)%N (sc1 x + sc1 y)%N (sc2 x + sc2 y)%N
    (sc3 x + sc3 y)%N (sc4 x + sc4 y)%N (sk x + sk y)%N.

Definition symAdd1 (x y : SymN) : SymN :=
  mkSymN (sc0 x + sc0 y)%N (sc1 x + sc1 y)%N (sc2 x + sc2 y)%N
    (sc3 x + sc3 y)%N (sc4 x + sc4 y)%N (sk x + sk y + 1)%N.

Definition symAddConst (x : SymN) (n : N) : SymN :=
  mkSymN (sc0 x) (sc1 x) (sc2 x) (sc3 x) (sc4 x) (sk x + n)%N.

Definition symScale (m : N) (x : SymN) : SymN :=
  mkSymN (m * sc0 x)%N (m * sc1 x)%N (m * sc2 x)%N
    (m * sc3 x)%N (m * sc4 x)%N (m * sk x)%N.

Definition symSub (x y : SymN) : option SymN :=
  if andb (andb (andb (andb (andb
      (N.leb (sc0 y) (sc0 x))
      (N.leb (sc1 y) (sc1 x)))
      (N.leb (sc2 y) (sc2 x)))
      (N.leb (sc3 y) (sc3 x)))
      (N.leb (sc4 y) (sc4 x)))
      (N.leb (sk y) (sk x)) then
    Some (mkSymN (sc0 x - sc0 y)%N (sc1 x - sc1 y)%N (sc2 x - sc2 y)%N
      (sc3 x - sc3 y)%N (sc4 x - sc4 y)%N (sk x - sk y)%N)
  else None.

Definition symLe (x y : SymN) : bool :=
  andb (andb (andb (andb (andb
    (N.leb (sc0 x) (sc0 y))
    (N.leb (sc1 x) (sc1 y)))
    (N.leb (sc2 x) (sc2 y)))
    (N.leb (sc3 x) (sc3 y)))
    (N.leb (sc4 x) (sc4 y)))
    (N.leb (sk x) (sk y)).

Definition symDivMod (x : SymN) (d : N) : option (SymN * N) :=
  if andb (andb (andb (andb (andb
      (N.ltb 0%N d)
      (N.eqb (N.modulo (sc0 x) d) 0%N))
      (N.eqb (N.modulo (sc1 x) d) 0%N))
      (N.eqb (N.modulo (sc2 x) d) 0%N))
      (N.eqb (N.modulo (sc3 x) d) 0%N))
      (N.eqb (N.modulo (sc4 x) d) 0%N) then
    Some (mkSymN (N.div (sc0 x) d) (N.div (sc1 x) d) (N.div (sc2 x) d)
      (N.div (sc3 x) d) (N.div (sc4 x) d) (N.div (sk x) d), N.modulo (sk x) d)
  else None.

Inductive SymDec : Type :=
  | sd_zero
  | sd_succ (x' : SymN)
  | sd_stuck.

Definition symDec (x : SymN) : SymDec :=
  if N.eqb (sk x) 0%N then
    if symIsConst x then sd_zero else sd_stuck
  else
    sd_succ (mkSymN (sc0 x) (sc1 x) (sc2 x) (sc3 x) (sc4 x) (sk x - 1)%N).

Ltac split_andb :=
  repeat match goal with
  | H : andb _ _ = true |- _ => apply Bool.andb_true_iff in H; destruct H
  | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
  | H : N.eqb _ _ = false |- _ => apply N.eqb_neq in H
  | H : N.leb _ _ = true |- _ => apply N.leb_le in H
  | H : N.ltb _ _ = true |- _ => apply N.ltb_lt in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
  | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
  end.

Lemma evalSymN_const (v : V5) (k : N) :
  evalSymN v (symConst k) = #k.
Proof. unfold evalSymN, symConst. cbn [sc0 sc1 sc2 sc3 sc4 sk]. lia. Qed.

Lemma evalSymN_zero (v : V5) : evalSymN v symZero = 0.
Proof. reflexivity. Qed.

Lemma evalSymN_one (v : V5) : evalSymN v symOne = 1.
Proof. unfold evalSymN, symOne. cbn [sc0 sc1 sc2 sc3 sc4 sk]. lia. Qed.

Lemma evalSymN_isConst {v : V5} {x : SymN} (h : symIsConst x = true) :
  evalSymN v x = #(sk x).
Proof.
  unfold symIsConst in h. split_andb.
  unfold evalSymN. rewrite H, H3, H2, H1, H0. lia.
Qed.

Lemma evalSymN_isZero {v : V5} {x : SymN} (h : symIsZero x = true) :
  evalSymN v x = 0.
Proof.
  unfold symIsZero in h. split_andb.
  rewrite (evalSymN_isConst H), H0. reflexivity.
Qed.

Lemma evalSymN_isConst1 {v : V5} {x : SymN} (h : symIsConst1 x = true) :
  evalSymN v x = 1.
Proof.
  unfold symIsConst1 in h. split_andb.
  rewrite (evalSymN_isConst H), H0. reflexivity.
Qed.

Lemma evalSymN_add (v : V5) (x y : SymN) :
  evalSymN v (symAdd x y) = evalSymN v x + evalSymN v y.
Proof.
  unfold evalSymN, symAdd. cbn [sc0 sc1 sc2 sc3 sc4 sk].
  repeat rewrite N2Nat.inj_add. ring.
Qed.

Lemma evalSymN_add1 (v : V5) (x y : SymN) :
  evalSymN v (symAdd1 x y) = evalSymN v x + evalSymN v y + 1.
Proof.
  unfold evalSymN, symAdd1. cbn [sc0 sc1 sc2 sc3 sc4 sk].
  repeat rewrite N2Nat.inj_add. change (#1) with 1. ring.
Qed.

Lemma evalSymN_addConst (v : V5) (x : SymN) (n : N) :
  evalSymN v (symAddConst x n) = evalSymN v x + #n.
Proof.
  unfold evalSymN, symAddConst. cbn [sc0 sc1 sc2 sc3 sc4 sk]. lia.
Qed.

Lemma evalSymN_scale (v : V5) (m : N) (x : SymN) :
  evalSymN v (symScale m x) = #m * evalSymN v x.
Proof.
  unfold evalSymN, symScale. cbn [sc0 sc1 sc2 sc3 sc4 sk].
  repeat rewrite N2Nat.inj_mul. ring.
Qed.

Lemma N_le_mul_to_nat (a b : N) (k : nat) :
  (a <= b)%N -> #a * k <= #b * k.
Proof.
  intros h. apply Nat.mul_le_mono_r. lia.
Qed.

Lemma evalSymN_le {v : V5} {x y : SymN} (h : symLe x y = true) :
  evalSymN v x <= evalSymN v y.
Proof.
  unfold symLe in h. split_andb.
  pose proof (N_le_mul_to_nat _ _ (v0 v) H) as m0.
  pose proof (N_le_mul_to_nat _ _ (v1 v) H4) as m1.
  pose proof (N_le_mul_to_nat _ _ (v2 v) H3) as m2.
  pose proof (N_le_mul_to_nat _ _ (v3 v) H2) as m3.
  pose proof (N_le_mul_to_nat _ _ (v4 v) H1) as m4.
  unfold evalSymN. lia.
Qed.

Lemma N_sub_mul_add_to_nat (a b : N) (k : nat) :
  (b <= a)%N -> #(a - b) * k + #b * k = #a * k.
Proof.
  intros h. assert (#b <= #a) by lia.
  rewrite <- Nat.mul_add_distr_r. f_equal. lia.
Qed.

Lemma evalSymN_sub {v : V5} {x y d : SymN} (h : symSub x y = Some d) :
  evalSymN v y <= evalSymN v x /\ evalSymN v d = evalSymN v x - evalSymN v y.
Proof.
  unfold symSub in h.
  destruct (andb _ _) eqn:Hc; [| discriminate].
  inversion h; subst d; clear h.
  split_andb.
  assert (heq : evalSymN v (mkSymN (sc0 x - sc0 y)%N (sc1 x - sc1 y)%N (sc2 x - sc2 y)%N
    (sc3 x - sc3 y)%N (sc4 x - sc4 y)%N (sk x - sk y)%N) + evalSymN v y = evalSymN v x).
  { pose proof (N_sub_mul_add_to_nat _ _ (v0 v) H) as s0.
    pose proof (N_sub_mul_add_to_nat _ _ (v1 v) H4) as s1.
    pose proof (N_sub_mul_add_to_nat _ _ (v2 v) H3) as s2.
    pose proof (N_sub_mul_add_to_nat _ _ (v3 v) H2) as s3.
    pose proof (N_sub_mul_add_to_nat _ _ (v4 v) H1) as s4.
    assert (sk_eq : #(sk x - sk y) + #(sk y) = #(sk x)) by lia.
    unfold evalSymN. cbn [sc0 sc1 sc2 sc3 sc4 sk].
    clear - s0 s1 s2 s3 s4 sk_eq. lia. }
  clear - heq. lia.
Qed.

Lemma N_div_exact_to_nat (c d : N) :
  (0 < d)%N -> N.modulo c d = 0%N -> #c = #d * #(N.div c d).
Proof.
  intros hd hm.
  pose proof (N.div_mod c d ltac:(lia)) as hdm.
  rewrite hm, N.add_0_r in hdm.
  rewrite hdm at 1. apply N2Nat.inj_mul.
Qed.

Lemma N_div_mod_to_nat (c d : N) :
  (0 < d)%N -> #(N.modulo c d) < #d /\ #c = #d * #(N.div c d) + #(N.modulo c d).
Proof.
  intros hd.
  pose proof (N.mod_lt c d ltac:(lia)) as hlt.
  pose proof (N.div_mod c d ltac:(lia)) as hdm.
  split; [lia |].
  rewrite hdm at 1. rewrite N2Nat.inj_add, N2Nat.inj_mul. reflexivity.
Qed.

Lemma evalSymN_divMod {v : V5} {x q : SymN} {d rem : N}
  (h : symDivMod x d = Some (q, rem)) :
  0 < #d /\ #rem < #d /\ evalSymN v x = #d * evalSymN v q + #rem.
Proof.
  unfold symDivMod in h.
  destruct (andb _ _) eqn:Hc; [| discriminate].
  inversion h; subst q rem; clear h.
  split_andb.
  pose proof (N_div_exact_to_nat (sc0 x) d H H4) as q0.
  pose proof (N_div_exact_to_nat (sc1 x) d H H3) as q1.
  pose proof (N_div_exact_to_nat (sc2 x) d H H2) as q2.
  pose proof (N_div_exact_to_nat (sc3 x) d H H1) as q3.
  pose proof (N_div_exact_to_nat (sc4 x) d H H0) as q4.
  destruct (N_div_mod_to_nat (sk x) d H) as [hrem qk].
  split; [clear - H; lia | split; [exact hrem |]].
  unfold evalSymN. cbn [sc0 sc1 sc2 sc3 sc4 sk].
  rewrite q0, q1, q2, q3, q4, qk. ring.
Qed.

Lemma symDec_isZero {v : V5} {x : SymN} (h : symDec x = sd_zero) :
  evalSymN v x = 0.
Proof.
  unfold symDec in h.
  destruct (N.eqb (sk x) 0%N) eqn:Hk; [| discriminate].
  destruct (symIsConst x) eqn:Hc; [| discriminate].
  split_andb. rewrite (evalSymN_isConst Hc), Hk. reflexivity.
Qed.

Lemma symDec_isSucc {v : V5} {x x' : SymN} (h : symDec x = sd_succ x') :
  evalSymN v x = evalSymN v x' + 1.
Proof.
  unfold symDec in h.
  destruct (N.eqb (sk x) 0%N) eqn:Hk.
  - destruct (symIsConst x); discriminate.
  - inversion h; subst x'; clear h.
    split_andb. unfold evalSymN. cbn [sc0 sc1 sc2 sc3 sc4 sk]. lia.
Qed.

Lemma evalSymN_ge_k (v : V5) (x : SymN) : #(sk x) <= evalSymN v x.
Proof. unfold evalSymN. lia. Qed.

(* ========================================================================== *)
(* Symbolic Stack Types & Encoding                                            *)
(* ========================================================================== *)

Inductive SymLTok : Type :=
  | sl_pair (z o : nat) (c : SymN)
  | sl_mid (c : SymN).

Inductive SymRTok : Type :=
  | sr_pair (z o : nat) (c : SymN)
  | sr_mid (c : SymN).

Definition SymState : Type := Mode * list SymLTok * list SymRTok.

Fixpoint encSL (v : V5) (vl : list SymLTok) : side :=
  match vl with
  | [] => 0inf
  | sl_pair z o c :: ts => ((pWord z o) ^^ (evalSymN v c + 1)) *> encSL v ts
  | sl_mid c :: ts => (wLM ^^ (evalSymN v c + 1)) *> encSL v ts
  end.

Fixpoint encSR (v : V5) (vr : list SymRTok) : side :=
  match vr with
  | [] => 0inf
  | sr_pair z o c :: ts => ((pWord z o) ^^ (evalSymN v c + 1)) *> encSR v ts
  | sr_mid c :: ts => (wRM ^^ (evalSymN v c + 1)) *> encSR v ts
  end.

Definition evalSym (v : V5) (s : SymState) : Q * tape :=
  let '(m, vl, vr) := s in
  match m with
  | mA => cfgA (encSL v vl) (encSR v vr)
  | mD => cfgD (encSL v vl) (encSR v vr)
  | mE => cfgE (encSL v vl) (encSR v vr)
  | mHalt => cfgHalt (encSL v vl) (encSR v vr)
  end.

Definition evalRTok (v : V5) (t : SymRTok) : RTok :=
  match t with
  | sr_pair z o c => rpair z o (evalSymN v c)
  | sr_mid c => rmid (evalSymN v c)
  end.

Lemma encSR_eq_encR_map (v : V5) : forall (vr : list SymRTok),
  encSR v vr = encR (map (evalRTok v) vr).
Proof.
  induction vr as [| [z o c | c] ts IH]; [reflexivity | |];
    cbn [encSR map evalRTok encR]; rewrite IH; reflexivity.
Qed.

(* ========================================================================== *)
(* Symbolic Stack Constructors & Soundness                                    *)
(* ========================================================================== *)

Definition symDecPairL (z o : nat) (c : SymN) (ts : list SymLTok) : option (list SymLTok) :=
  match symDec c with
  | sd_zero => Some ts
  | sd_succ c' => Some (sl_pair z o c' :: ts)
  | sd_stuck => None
  end.

Definition symDecMidL (c : SymN) (ts : list SymLTok) : option (list SymLTok) :=
  match symDec c with
  | sd_zero => Some ts
  | sd_succ c' => Some (sl_mid c' :: ts)
  | sd_stuck => None
  end.

Definition symDecPairR (z o : nat) (c : SymN) (ts : list SymRTok) : option (list SymRTok) :=
  match symDec c with
  | sd_zero => Some ts
  | sd_succ c' => Some (sr_pair z o c' :: ts)
  | sd_stuck => None
  end.

Definition symDecMidR (c : SymN) (ts : list SymRTok) : option (list SymRTok) :=
  match symDec c with
  | sd_zero => Some ts
  | sd_succ c' => Some (sr_mid c' :: ts)
  | sd_stuck => None
  end.

Definition symPushLM (k : SymN) (vl : list SymLTok) : option (list SymLTok) :=
  match symDec k with
  | sd_zero => Some vl
  | sd_succ k' =>
    match vl with
    | sl_mid c :: ts => Some (sl_mid (symAdd1 c k') :: ts)
    | ts => Some (sl_mid k' :: ts)
    end
  | sd_stuck => None
  end.

Definition symCoalesceL (vl : list SymLTok) : option (list SymLTok) :=
  match vl with
  | sl_pair 1 1 c0 :: sl_pair 2 0 c2 :: rest =>
    if symIsZero c0 then
      if symIsConst1 c2 then
        symPushLM symOne rest
      else if N.leb 2%N (sk c2) then
        symPushLM symOne
          (sl_pair 2 0 (mkSymN (sc0 c2) (sc1 c2) (sc2 c2) (sc3 c2) (sc4 c2) (sk c2 - 2)%N) :: rest)
      else if symIsZero c2 then
        Some (sl_pair 1 1 c0 :: sl_pair 2 0 c2 :: rest)
      else None
    else Some (sl_pair 1 1 c0 :: sl_pair 2 0 c2 :: rest)
  | _ => Some vl
  end.

Definition symPushLPPre (z o : nat) (k' : SymN) (vl : list SymLTok) : list SymLTok :=
  match vl with
  | sl_pair z' o' c :: ts =>
    if andb (Nat.eqb z z') (Nat.eqb o o') then sl_pair z o (symAdd1 c k') :: ts
    else sl_pair z o k' :: sl_pair z' o' c :: ts
  | ts => sl_pair z o k' :: ts
  end.

Definition symPushLP (z o : nat) (k : SymN) (vl : list SymLTok) : option (list SymLTok) :=
  match symDec k with
  | sd_zero => Some vl
  | sd_succ k' => symCoalesceL (symPushLPPre z o k' vl)
  | sd_stuck => None
  end.

Definition symNormL (vl : list SymLTok) : option (list SymLTok) :=
  match vl with
  | sl_mid c :: ts =>
    match symDecMidL c ts with
    | None => None
    | Some ts' => Some (sl_pair 1 1 symZero :: sl_pair 2 0 symOne :: ts')
    end
  | _ => Some vl
  end.

Definition symPushZerosL (k : nat) (vl : list SymLTok) : option (list SymLTok) :=
  if Nat.eqb k 0 then Some vl
  else
    match symNormL vl with
    | None => None
    | Some [] => Some []
    | Some (sl_pair z o c :: ts) =>
      match symDecPairL z o c ts with
      | None => None
      | Some ts' => symPushLP (z + k) o symOne ts'
      end
    | Some (sl_mid _ :: _) => None
    end.

Definition symPushOnesL (k : nat) (vl : list SymLTok) : option (list SymLTok) :=
  match k with
  | 0 => Some vl
  | S k' =>
    match vl with
    | [] => Some [sl_pair 0 k' symZero]
    | sl_pair 0 o c :: ts =>
      match symDecPairL 0 o c ts with
      | None => None
      | Some ts' => symPushLP 0 (o + k' + 1) symOne ts'
      end
    | sl_pair (S z') o c :: ts => symPushLP 0 k' symOne (sl_pair (S z') o c :: ts)
    | sl_mid c :: ts => symPushLP 0 k' symOne (sl_mid c :: ts)
    end
  end.

Definition symPushWLMSem (k : SymN) (vl : list SymLTok) : option (list SymLTok) :=
  match symDec k with
  | sd_zero => Some vl
  | sd_succ k' =>
    match symPushLP 2 0 (symConst 2%N) vl with
    | None => None
    | Some vl1 =>
      match symPushLP 1 1 symOne vl1 with
      | None => None
      | Some vl2 => symPushLM k' vl2
      end
    end
  | sd_stuck => None
  end.

Definition symPopBitL (vl : list SymLTok) : option (Sym * list SymLTok) :=
  match symNormL vl with
  | None => None
  | Some [] => Some (S0, [])
  | Some (sl_pair 0 0 c :: ts) =>
    match symDecPairL 0 0 c ts with
    | None => None
    | Some ts' => Some (S1, ts')
    end
  | Some (sl_pair 0 (S o') c :: ts) =>
    match symDecPairL 0 (S o') c ts with
    | None => None
    | Some ts' =>
      match symPushLP 0 o' symOne ts' with
      | None => None
      | Some vl' => Some (S1, vl')
      end
    end
  | Some (sl_pair (S z') o c :: ts) =>
    match symDecPairL (S z') o c ts with
    | None => None
    | Some ts' =>
      match symPushLP z' o symOne ts' with
      | None => None
      | Some vl' => Some (S0, vl')
      end
    end
  | Some (sl_mid _ :: _) => None
  end.

Definition symPushRM (k : SymN) (vr : list SymRTok) : option (list SymRTok) :=
  match symDec k with
  | sd_zero => Some vr
  | sd_succ k' =>
    match vr with
    | sr_mid c :: ts => Some (sr_mid (symAdd1 c k') :: ts)
    | ts => Some (sr_mid k' :: ts)
    end
  | sd_stuck => None
  end.

Definition symCoalesceR (vr : list SymRTok) : option (list SymRTok) :=
  match vr with
  | sr_pair 1 1 c0 :: sr_pair 2 0 c1 :: rest =>
    if symIsConst1 c0 then
      match symDecPairR 2 0 c1 rest with
      | None => None
      | Some rest' => symPushRM symOne rest'
      end
    else Some (sr_pair 1 1 c0 :: sr_pair 2 0 c1 :: rest)
  | _ => Some vr
  end.

Definition symPushRPPre (z o : nat) (k' : SymN) (vr : list SymRTok) : list SymRTok :=
  match vr with
  | sr_pair z' o' c :: ts =>
    if andb (Nat.eqb z z') (Nat.eqb o o') then sr_pair z o (symAdd1 c k') :: ts
    else sr_pair z o k' :: sr_pair z' o' c :: ts
  | ts => sr_pair z o k' :: ts
  end.

Definition symPushRP (z o : nat) (k : SymN) (vr : list SymRTok) : option (list SymRTok) :=
  match symDec k with
  | sd_zero => Some vr
  | sd_succ k' => symCoalesceR (symPushRPPre z o k' vr)
  | sd_stuck => None
  end.

Definition symNormR (vr : list SymRTok) : option (list SymRTok) :=
  match vr with
  | sr_mid c :: ts =>
    match symDecMidR c ts with
    | None => None
    | Some ts' => Some (sr_pair 1 1 symOne :: sr_pair 2 0 symZero :: ts')
    end
  | _ => Some vr
  end.

Definition symPushZerosR (k : nat) (vr : list SymRTok) : option (list SymRTok) :=
  if Nat.eqb k 0 then Some vr
  else
    match symNormR vr with
    | None => None
    | Some [] => Some []
    | Some (sr_pair z o c :: ts) =>
      match symDecPairR z o c ts with
      | None => None
      | Some ts' => symPushRP (z + k) o symOne ts'
      end
    | Some (sr_mid _ :: _) => None
    end.

Definition symPushOnesR (k : nat) (vr : list SymRTok) : option (list SymRTok) :=
  match k with
  | 0 => Some vr
  | S k' =>
    match vr with
    | [] => Some [sr_pair 0 k' symZero]
    | sr_pair 0 o c :: ts =>
      match symDecPairR 0 o c ts with
      | None => None
      | Some ts' => symPushRP 0 (o + k' + 1) symOne ts'
      end
    | sr_pair (S z') o c :: ts => symPushRP 0 k' symOne (sr_pair (S z') o c :: ts)
    | sr_mid c :: ts => symPushRP 0 k' symOne (sr_mid c :: ts)
    end
  end.

Definition symPushWRMSem (k : SymN) (vr : list SymRTok) : option (list SymRTok) :=
  match symDec k with
  | sd_zero => Some vr
  | sd_succ k' =>
    match symPushRP 2 0 symOne vr with
    | None => None
    | Some vr1 =>
      match symPushRP 1 1 (symConst 2%N) vr1 with
      | None => None
      | Some vr2 => symPushRM k' vr2
      end
    end
  | sd_stuck => None
  end.

Definition symPopBitR (vr : list SymRTok) : option (Sym * list SymRTok) :=
  match symNormR vr with
  | None => None
  | Some [] => Some (S0, [])
  | Some (sr_pair 0 0 c :: ts) =>
    match symDecPairR 0 0 c ts with
    | None => None
    | Some ts' => Some (S1, ts')
    end
  | Some (sr_pair 0 (S o') c :: ts) =>
    match symDecPairR 0 (S o') c ts with
    | None => None
    | Some ts' =>
      match symPushRP 0 o' symOne ts' with
      | None => None
      | Some vr' => Some (S1, vr')
      end
    end
  | Some (sr_pair (S z') o c :: ts) =>
    match symDecPairR (S z') o c ts with
    | None => None
    | Some ts' =>
      match symPushRP z' o symOne ts' with
      | None => None
      | Some vr' => Some (S0, vr')
      end
    end
  | Some (sr_mid _ :: _) => None
  end.

(* ========================================================================== *)
(* Symbolic Stack Encoding Proofs                                             *)
(* ========================================================================== *)

Lemma encSL_decPairL {v : V5} {z o : nat} {c : SymN} {ts out : list SymLTok}
  (h : symDecPairL z o c ts = Some out) :
  (pWord z o) *> encSL v out = encSL v (sl_pair z o c :: ts).
Proof.
  unfold symDecPairL in h.
  destruct (symDec c) as [| c' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    cbn [encSL]. rewrite (symDec_isZero hd), lpow_1. reflexivity.
  - inversion h; subst out; clear h.
    cbn [encSL]. rewrite (symDec_isSucc hd).
    symmetry. apply Str_app_lpow_succ.
Qed.

Lemma encSL_decMidL {v : V5} {c : SymN} {ts out : list SymLTok}
  (h : symDecMidL c ts = Some out) :
  wLM *> encSL v out = encSL v (sl_mid c :: ts).
Proof.
  unfold symDecMidL in h.
  destruct (symDec c) as [| c' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    cbn [encSL]. rewrite (symDec_isZero hd), lpow_1. reflexivity.
  - inversion h; subst out; clear h.
    cbn [encSL]. rewrite (symDec_isSucc hd).
    symmetry. apply Str_app_lpow_succ.
Qed.

Lemma encSR_decPairR {v : V5} {z o : nat} {c : SymN} {ts out : list SymRTok}
  (h : symDecPairR z o c ts = Some out) :
  (pWord z o) *> encSR v out = encSR v (sr_pair z o c :: ts).
Proof.
  unfold symDecPairR in h.
  destruct (symDec c) as [| c' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    cbn [encSR]. rewrite (symDec_isZero hd), lpow_1. reflexivity.
  - inversion h; subst out; clear h.
    cbn [encSR]. rewrite (symDec_isSucc hd).
    symmetry. apply Str_app_lpow_succ.
Qed.

Lemma encSR_decMidR {v : V5} {c : SymN} {ts out : list SymRTok}
  (h : symDecMidR c ts = Some out) :
  wRM *> encSR v out = encSR v (sr_mid c :: ts).
Proof.
  unfold symDecMidR in h.
  destruct (symDec c) as [| c' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    cbn [encSR]. rewrite (symDec_isZero hd), lpow_1. reflexivity.
  - inversion h; subst out; clear h.
    cbn [encSR]. rewrite (symDec_isSucc hd).
    symmetry. apply Str_app_lpow_succ.
Qed.

Lemma encSL_pushLM {v : V5} {k : SymN} {vl out : list SymLTok}
  (h : symPushLM k vl = Some out) :
  encSL v out = (wLM ^^ evalSymN v k) *> encSL v vl.
Proof.
  unfold symPushLM in h.
  destruct (symDec k) as [| k' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    rewrite (symDec_isZero hd). reflexivity.
  - rewrite (symDec_isSucc hd).
    destruct vl as [| [z' o' c | c] ts]; inversion h; subst out; clear h.
    + reflexivity.
    + reflexivity.
    + cbn [encSL]. rewrite evalSymN_add1, pow_append_pow.
      f_equal. f_equal. lia.
Qed.

Lemma encSL_coalesceL {v : V5} {vl out : list SymLTok}
  (h : symCoalesceL vl = Some out) :
  encSL v out = encSL v vl.
Proof.
  destruct vl as [| [z0 o0 c0 | c0] vl1];
    [inversion h; reflexivity | | inversion h; reflexivity].
  destruct z0 as [| [| z0]]; try (inversion h; reflexivity).
  destruct o0 as [| [| o0]]; try (inversion h; reflexivity).
  destruct vl1 as [| [z1 o1 c2 | c2] rest];
    [inversion h; reflexivity | | inversion h; reflexivity].
  destruct z1 as [| [| [| z1]]]; try (inversion h; reflexivity).
  destruct o1 as [| o1]; try (inversion h; reflexivity).
  cbn [symCoalesceL] in h.
  destruct (symIsZero c0) eqn:h0; [| inversion h; reflexivity].
  destruct (symIsConst1 c2) eqn:h1.
  - rewrite (encSL_pushLM h), evalSymN_one, lpow_1.
    cbn [encSL]. rewrite (evalSymN_isZero h0), (evalSymN_isConst1 h1), pWord_1_1, pWord_2_0.
    reflexivity.
  - destruct (N.leb 2%N (sk c2)) eqn:h2.
    + rewrite (encSL_pushLM h), evalSymN_one, lpow_1.
      cbn [encSL]. rewrite (evalSymN_isZero h0), pWord_1_1, pWord_2_0.
      split_andb.
      assert (hsub : evalSymN v c2 + 1 =
        2 + (evalSymN v (mkSymN (sc0 c2) (sc1 c2) (sc2 c2) (sc3 c2) (sc4 c2) (sk c2 - 2)%N) + 1)).
      { unfold evalSymN. cbn [sc0 sc1 sc2 sc3 sc4 sk]. lia. }
      rewrite hsub, (Str_app_lpow_add wZ 2). reflexivity.
    + destruct (symIsZero c2); [inversion h; reflexivity | discriminate].
Qed.

Lemma encSL_pushLP {v : V5} {z o : nat} {k : SymN} {vl out : list SymLTok}
  (h : symPushLP z o k vl = Some out) :
  encSL v out = ((pWord z o) ^^ evalSymN v k) *> encSL v vl.
Proof.
  unfold symPushLP in h.
  destruct (symDec k) as [| k' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    rewrite (symDec_isZero hd). reflexivity.
  - rewrite (symDec_isSucc hd), (encSL_coalesceL h).
    destruct vl as [| [z' o' c | c] ts]; [reflexivity | | reflexivity].
    cbn [symPushLPPre].
    destruct (andb (Nat.eqb z z') (Nat.eqb o o')) eqn:heq.
    + split_andb. subst z' o'.
      cbn [encSL]. rewrite evalSymN_add1, pow_append_pow.
      f_equal. f_equal. lia.
    + reflexivity.
Qed.

Lemma encSL_normL {v : V5} {vl out : list SymLTok}
  (h : symNormL vl = Some out) :
  encSL v out = encSL v vl.
Proof.
  destruct vl as [| [z o c | c] ts];
    [inversion h; reflexivity | inversion h; reflexivity |].
  cbn [symNormL] in h.
  destruct (symDecMidL c ts) as [ts' |] eqn:hd; [| discriminate].
  inversion h; subst out; clear h.
  rewrite <- (encSL_decMidL hd).
  cbn [encSL]. rewrite evalSymN_zero, evalSymN_one, pWord_1_1, pWord_2_0.
  reflexivity.
Qed.

Lemma encSL_pushZerosL {v : V5} {k : nat} {vl out : list SymLTok}
  (h : symPushZerosL k vl = Some out) :
  encSL v out = (([S0] ^^ k) *> encSL v vl).
Proof.
  unfold symPushZerosL in h.
  destruct (Nat.eqb k 0) eqn:hk.
  - inversion h; subst out; clear h. split_andb. subst k. reflexivity.
  - destruct (symNormL vl) as [nvl |] eqn:hn; [| discriminate].
    rewrite <- (encSL_normL hn).
    destruct nvl as [| [z o c | c] ts].
    + inversion h; subst out; clear h.
      cbn [encSL]. symmetry. apply zeros_append_0inf.
    + destruct (symDecPairL z o c ts) as [ts' |] eqn:hd; [| discriminate].
      rewrite (encSL_pushLP h), evalSymN_one, lpow_1, <- (encSL_decPairL hd).
      rewrite pWord_add_zeros, app_Str_app. reflexivity.
    + discriminate.
Qed.

Lemma encSL_pushOnesL {v : V5} {k : nat} {vl out : list SymLTok}
  (h : symPushOnesL k vl = Some out) :
  encSL v out = (([S1] ^^ k) *> encSL v vl).
Proof.
  destruct k as [| k'].
  - cbn [symPushOnesL] in h. inversion h; reflexivity.
  - destruct vl as [| [[| z'] o c | c] ts]; cbn [symPushOnesL] in h.
    + inversion h; subst out; clear h.
      cbn [encSL]. rewrite evalSymN_zero, lpow_1, pWord_zero_eq.
      replace (k' + 1) with (S k') by lia. reflexivity.
    + destruct (symDecPairL 0 o c ts) as [ts' |] eqn:hd; [| discriminate].
      rewrite (encSL_pushLP h), evalSymN_one, lpow_1, <- (encSL_decPairL hd).
      rewrite !pWord_zero_eq, pow_append_pow.
      f_equal. f_equal. lia.
    + rewrite (encSL_pushLP h), evalSymN_one, lpow_1, pWord_zero_eq.
      replace (k' + 1) with (S k') by lia. reflexivity.
    + rewrite (encSL_pushLP h), evalSymN_one, lpow_1, pWord_zero_eq.
      replace (k' + 1) with (S k') by lia. reflexivity.
Qed.

Lemma encSL_pushWLMSem {v : V5} {k : SymN} {vl out : list SymLTok}
  (h : symPushWLMSem k vl = Some out) :
  encSL v out = (wLM ^^ evalSymN v k) *> encSL v vl.
Proof.
  unfold symPushWLMSem in h.
  destruct (symDec k) as [| k' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    rewrite (symDec_isZero hd). reflexivity.
  - rewrite (symDec_isSucc hd).
    destruct (symPushLP 2 0 (symConst 2%N) vl) as [vl1 |] eqn:h1; [| discriminate].
    destruct (symPushLP 1 1 symOne vl1) as [vl2 |] eqn:h2; [| discriminate].
    rewrite (encSL_pushLM h), (encSL_pushLP h2), (encSL_pushLP h1),
      evalSymN_one, evalSymN_const, pWord_1_1, pWord_2_0.
    change (#2) with 2.
    assert (heq : (wT ^^ 1) *> (wZ ^^ 2) *> encSL v vl = (wLM ^^ 1) *> encSL v vl) by reflexivity.
    rewrite heq, pow_append_pow. reflexivity.
Qed.

Lemma encSL_popBitL {v : V5} {vl out : list SymLTok} {b : Sym}
  (h : symPopBitL vl = Some (b, out)) :
  encSL v vl = b >> encSL v out.
Proof.
  unfold symPopBitL in h.
  destruct (symNormL vl) as [nvl |] eqn:hn; [| discriminate].
  rewrite <- (encSL_normL hn).
  destruct nvl as [| [[| z'] [| o'] c | c] ts].
  - inversion h; subst b out; clear h.
    cbn [encSL]. symmetry. exact cons_zero_0inf.
  - destruct (symDecPairL 0 0 c ts) as [ts' |] eqn:hd; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite <- (encSL_decPairL hd). reflexivity.
  - destruct (symDecPairL 0 (S o') c ts) as [ts' |] eqn:hd; [| discriminate].
    destruct (symPushLP 0 o' symOne ts') as [vl' |] eqn:hp; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite (encSL_pushLP hp), evalSymN_one, lpow_1, <- (encSL_decPairL hd).
    rewrite pWord_0_S, app_Str_app. reflexivity.
  - destruct (symDecPairL (S z') 0 c ts) as [ts' |] eqn:hd; [| discriminate].
    destruct (symPushLP z' 0 symOne ts') as [vl' |] eqn:hp; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite (encSL_pushLP hp), evalSymN_one, lpow_1, <- (encSL_decPairL hd).
    rewrite pWord_S_z, app_Str_app. reflexivity.
  - destruct (symDecPairL (S z') (S o') c ts) as [ts' |] eqn:hd; [| discriminate].
    destruct (symPushLP z' (S o') symOne ts') as [vl' |] eqn:hp; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite (encSL_pushLP hp), evalSymN_one, lpow_1, <- (encSL_decPairL hd).
    rewrite pWord_S_z, app_Str_app. reflexivity.
  - discriminate.
Qed.

Lemma encSR_pushRM {v : V5} {k : SymN} {vr out : list SymRTok}
  (h : symPushRM k vr = Some out) :
  encSR v out = (wRM ^^ evalSymN v k) *> encSR v vr.
Proof.
  unfold symPushRM in h.
  destruct (symDec k) as [| k' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    rewrite (symDec_isZero hd). reflexivity.
  - rewrite (symDec_isSucc hd).
    destruct vr as [| [z' o' c | c] ts]; inversion h; subst out; clear h.
    + reflexivity.
    + reflexivity.
    + cbn [encSR]. rewrite evalSymN_add1, pow_append_pow.
      f_equal. f_equal. lia.
Qed.

Lemma encSR_coalesceR {v : V5} {vr out : list SymRTok}
  (h : symCoalesceR vr = Some out) :
  encSR v out = encSR v vr.
Proof.
  destruct vr as [| [z0 o0 c0 | c0] vr1];
    [inversion h; reflexivity | | inversion h; reflexivity].
  destruct z0 as [| [| z0]]; try (inversion h; reflexivity).
  destruct o0 as [| [| o0]]; try (inversion h; reflexivity).
  destruct vr1 as [| [z1 o1 c1 | c1] rest];
    [inversion h; reflexivity | | inversion h; reflexivity].
  destruct z1 as [| [| [| z1]]]; try (inversion h; reflexivity).
  destruct o1 as [| o1]; try (inversion h; reflexivity).
  cbn [symCoalesceR] in h.
  destruct (symIsConst1 c0) eqn:h1; [| inversion h; reflexivity].
  destruct (symDecPairR 2 0 c1 rest) as [rest' |] eqn:hd; [| discriminate].
  rewrite (encSR_pushRM h), evalSymN_one, lpow_1.
  pose proof (@encSR_decPairR v 2 0 c1 rest rest' hd) as htail.
  rewrite pWord_2_0 in htail.
  cbn [encSR] in htail |- *.
  rewrite (evalSymN_isConst1 h1), pWord_1_1, <- htail.
  reflexivity.
Qed.

Lemma encSR_pushRP {v : V5} {z o : nat} {k : SymN} {vr out : list SymRTok}
  (h : symPushRP z o k vr = Some out) :
  encSR v out = ((pWord z o) ^^ evalSymN v k) *> encSR v vr.
Proof.
  unfold symPushRP in h.
  destruct (symDec k) as [| k' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    rewrite (symDec_isZero hd). reflexivity.
  - rewrite (symDec_isSucc hd), (encSR_coalesceR h).
    destruct vr as [| [z' o' c | c] ts]; [reflexivity | | reflexivity].
    cbn [symPushRPPre].
    destruct (andb (Nat.eqb z z') (Nat.eqb o o')) eqn:heq.
    + split_andb. subst z' o'.
      cbn [encSR]. rewrite evalSymN_add1, pow_append_pow.
      f_equal. f_equal. lia.
    + reflexivity.
Qed.

Lemma encSR_normR {v : V5} {vr out : list SymRTok}
  (h : symNormR vr = Some out) :
  encSR v out = encSR v vr.
Proof.
  destruct vr as [| [z o c | c] ts];
    [inversion h; reflexivity | inversion h; reflexivity |].
  cbn [symNormR] in h.
  destruct (symDecMidR c ts) as [ts' |] eqn:hd; [| discriminate].
  inversion h; subst out; clear h.
  rewrite <- (encSR_decMidR hd).
  cbn [encSR]. rewrite evalSymN_zero, evalSymN_one, pWord_1_1, pWord_2_0.
  reflexivity.
Qed.

Lemma encSR_pushZerosR {v : V5} {k : nat} {vr out : list SymRTok}
  (h : symPushZerosR k vr = Some out) :
  encSR v out = (([S0] ^^ k) *> encSR v vr).
Proof.
  unfold symPushZerosR in h.
  destruct (Nat.eqb k 0) eqn:hk.
  - inversion h; subst out; clear h. split_andb. subst k. reflexivity.
  - destruct (symNormR vr) as [nvr |] eqn:hn; [| discriminate].
    rewrite <- (encSR_normR hn).
    destruct nvr as [| [z o c | c] ts].
    + inversion h; subst out; clear h.
      cbn [encSR]. symmetry. apply zeros_append_0inf.
    + destruct (symDecPairR z o c ts) as [ts' |] eqn:hd; [| discriminate].
      rewrite (encSR_pushRP h), evalSymN_one, lpow_1, <- (encSR_decPairR hd).
      rewrite pWord_add_zeros, app_Str_app. reflexivity.
    + discriminate.
Qed.

Lemma encSR_pushOnesR {v : V5} {k : nat} {vr out : list SymRTok}
  (h : symPushOnesR k vr = Some out) :
  encSR v out = (([S1] ^^ k) *> encSR v vr).
Proof.
  destruct k as [| k'].
  - cbn [symPushOnesR] in h. inversion h; reflexivity.
  - destruct vr as [| [[| z'] o c | c] ts]; cbn [symPushOnesR] in h.
    + inversion h; subst out; clear h.
      cbn [encSR]. rewrite evalSymN_zero, lpow_1, pWord_zero_eq.
      replace (k' + 1) with (S k') by lia. reflexivity.
    + destruct (symDecPairR 0 o c ts) as [ts' |] eqn:hd; [| discriminate].
      rewrite (encSR_pushRP h), evalSymN_one, lpow_1, <- (encSR_decPairR hd).
      rewrite !pWord_zero_eq, pow_append_pow.
      f_equal. f_equal. lia.
    + rewrite (encSR_pushRP h), evalSymN_one, lpow_1, pWord_zero_eq.
      replace (k' + 1) with (S k') by lia. reflexivity.
    + rewrite (encSR_pushRP h), evalSymN_one, lpow_1, pWord_zero_eq.
      replace (k' + 1) with (S k') by lia. reflexivity.
Qed.

Lemma encSR_pushWRMSem {v : V5} {k : SymN} {vr out : list SymRTok}
  (h : symPushWRMSem k vr = Some out) :
  encSR v out = (wRM ^^ evalSymN v k) *> encSR v vr.
Proof.
  unfold symPushWRMSem in h.
  destruct (symDec k) as [| k' |] eqn:hd; [| | discriminate].
  - inversion h; subst out; clear h.
    rewrite (symDec_isZero hd). reflexivity.
  - rewrite (symDec_isSucc hd).
    destruct (symPushRP 2 0 symOne vr) as [vr1 |] eqn:h1; [| discriminate].
    destruct (symPushRP 1 1 (symConst 2%N) vr1) as [vr2 |] eqn:h2; [| discriminate].
    rewrite (encSR_pushRM h), (encSR_pushRP h2), (encSR_pushRP h1),
      evalSymN_one, evalSymN_const, pWord_1_1, pWord_2_0.
    change (#2) with 2.
    assert (heq : (wT ^^ 2) *> (wZ ^^ 1) *> encSR v vr = (wRM ^^ 1) *> encSR v vr) by reflexivity.
    rewrite heq, pow_append_pow. reflexivity.
Qed.

Lemma encSR_popBitR {v : V5} {vr out : list SymRTok} {b : Sym}
  (h : symPopBitR vr = Some (b, out)) :
  encSR v vr = b >> encSR v out.
Proof.
  unfold symPopBitR in h.
  destruct (symNormR vr) as [nvr |] eqn:hn; [| discriminate].
  rewrite <- (encSR_normR hn).
  destruct nvr as [| [[| z'] [| o'] c | c] ts].
  - inversion h; subst b out; clear h.
    cbn [encSR]. symmetry. exact cons_zero_0inf.
  - destruct (symDecPairR 0 0 c ts) as [ts' |] eqn:hd; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite <- (encSR_decPairR hd). reflexivity.
  - destruct (symDecPairR 0 (S o') c ts) as [ts' |] eqn:hd; [| discriminate].
    destruct (symPushRP 0 o' symOne ts') as [vr' |] eqn:hp; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite (encSR_pushRP hp), evalSymN_one, lpow_1, <- (encSR_decPairR hd).
    rewrite pWord_0_S, app_Str_app. reflexivity.
  - destruct (symDecPairR (S z') 0 c ts) as [ts' |] eqn:hd; [| discriminate].
    destruct (symPushRP z' 0 symOne ts') as [vr' |] eqn:hp; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite (encSR_pushRP hp), evalSymN_one, lpow_1, <- (encSR_decPairR hd).
    rewrite pWord_S_z, app_Str_app. reflexivity.
  - destruct (symDecPairR (S z') (S o') c ts) as [ts' |] eqn:hd; [| discriminate].
    destruct (symPushRP z' (S o') symOne ts') as [vr' |] eqn:hp; [| discriminate].
    inversion h; subst b out; clear h.
    rewrite (encSR_pushRP hp), evalSymN_one, lpow_1, <- (encSR_decPairR hd).
    rewrite pWord_S_z, app_Str_app. reflexivity.
  - discriminate.
Qed.

(* ========================================================================== *)
(* Symbolic Sweeps & Base Step (`symStepBase`)                                *)
(* ========================================================================== *)

Fixpoint symSweepARAux (ts : list SymRTok) (after1 : bool) (vl : list SymLTok)
  : option (list SymLTok * list SymRTok) :=
  match ts with
  | [] =>
    if after1 then Some (vl, [sr_pair 0 0 symZero]) else Some (vl, [])
  | sr_mid c :: rest =>
    if after1 then
      match symPushLP 2 0 (symConst 2%N) vl with
      | None => None
      | Some vl1 =>
        match symDecMidR c rest with
        | None => None
        | Some rest' => Some (vl1, sr_pair 0 0 symZero :: sr_pair 2 0 symZero :: rest')
        end
      end
    else
      match symPushLP 1 0 symOne vl with
      | None => None
      | Some vl1 =>
        match symPushLP 2 0 symOne vl1 with
        | None => None
        | Some vl2 =>
          match symDecMidR c rest with
          | None => None
          | Some rest' => Some (vl2, sr_pair 0 0 symZero :: sr_pair 2 0 symZero :: rest')
          end
        end
      end
  | sr_pair 0 o c :: rest =>
    if after1 then
      match symPushOnesR 1 (sr_pair 0 o c :: rest) with
      | None => None
      | Some vr' => Some (vl, vr')
      end
    else
      match o with
      | 0 =>
        if symIsZero c then symSweepARAux rest true vl
        else Some (vl, sr_pair 0 0 c :: rest)
      | S o' => Some (vl, sr_pair 0 (S o') c :: rest)
      end
  | sr_pair 1 0 c :: rest =>
    if after1 then
      match symDec c with
      | sd_zero =>
        match symPushLP 2 0 symOne vl with
        | None => None
        | Some vl1 => symSweepARAux rest false vl1
        end
      | sd_succ _ =>
        match symPushLP 2 0 symOne vl with
        | None => None
        | Some vl1 =>
          match symPushLP 1 0 c vl1 with
          | None => None
          | Some vl2 => symSweepARAux rest false vl2
          end
        end
      | sd_stuck => None
      end
    else
      match symPushLP 1 0 (symAddConst c 1%N) vl with
      | None => None
      | Some vl1 => symSweepARAux rest false vl1
      end
  | sr_pair 1 1 c :: rest =>
    if after1 then
      match symPushLP 2 0 (symAddConst c 1%N) vl with
      | None => None
      | Some vl1 => symSweepARAux rest true vl1
      end
    else
      match symDec c with
      | sd_zero =>
        match symPushLP 1 0 symOne vl with
        | None => None
        | Some vl1 => symSweepARAux rest true vl1
        end
      | sd_succ _ =>
        match symPushLP 1 0 symOne vl with
        | None => None
        | Some vl1 =>
          match symPushLP 2 0 c vl1 with
          | None => None
          | Some vl2 => symSweepARAux rest true vl2
          end
        end
      | sd_stuck => None
      end
  | sr_pair 1 (S (S o'')) c :: rest =>
    if after1 then
      match symPushLP 2 0 symOne vl with
      | None => None
      | Some vl1 =>
        match symDecPairR 1 (S (S o'')) c rest with
        | None => None
        | Some r1 =>
          match symPushOnesR (S (S o'')) r1 with
          | None => None
          | Some vr' => Some (vl1, vr')
          end
        end
      end
    else
      match symPushLP 1 0 symOne vl with
      | None => None
      | Some vl1 =>
        match symDecPairR 1 (S (S o'')) c rest with
        | None => None
        | Some r1 =>
          match symPushOnesR (S (S o'')) r1 with
          | None => None
          | Some vr' => Some (vl1, vr')
          end
        end
      end
  | sr_pair (S (S z'')) o c :: rest =>
    if after1 then
      match symPushOnesR 1 (sr_pair (S (S z'')) o c :: rest) with
      | None => None
      | Some vr' => Some (vl, vr')
      end
    else Some (vl, sr_pair (S (S z'')) o c :: rest)
  end.

Lemma symSweepARAux_sound (v : V5) :
  forall (ts : list SymRTok) (after1 : bool) (vl vl' : list SymLTok) (vr' : list SymRTok),
    symSweepARAux ts after1 vl = Some (vl', vr') ->
    cfgA (encSL v vl) (if after1 then [S1] *> encSR v ts else encSR v ts) -->*
    cfgA (encSL v vl') (encSR v vr').
Proof.
  induction ts as [| tok rest IH]; intros after1 vl vl' vr' h.
  - destruct after1; cbn [symSweepARAux] in h; inversion h; subst vl' vr'; clear h.
    + apply evstep_refl.
    + apply evstep_refl.
  - destruct tok as [[| [| z'']] o c | c].
    + destruct after1.
      * cbn [symSweepARAux] in h.
        destruct (symPushOnesR 1 (sr_pair 0 o c :: rest)) as [r1 |] eqn:hp; [| discriminate].
        inversion h; subst vl' vr'; clear h.
        rewrite (encSR_pushOnesR hp), lpow_1. apply evstep_refl.
      * destruct o as [| o']; cbn [symSweepARAux] in h.
        { destruct (symIsZero c) eqn:hz.
          - pose proof (IH true vl vl' vr' h) as ih.
            cbn [encSR]. rewrite (evalSymN_isZero hz), pWord_0_0, lpow_1. exact ih.
          - inversion h; subst vl' vr'; apply evstep_refl. }
        { inversion h; subst vl' vr'; apply evstep_refl. }
    + destruct o as [| [| o'']].
      * destruct after1; cbn [symSweepARAux] in h.
        { destruct (symDec c) as [| c' |] eqn:hd; [| | discriminate].
          - destruct (symPushLP 2 0 symOne vl) as [vl1 |] eqn:h1; [| discriminate].
            pose proof (IH false vl1 vl' vr' h) as ih.
            cbn [encSR]. rewrite (symDec_isZero hd), pWord_1_0, lpow_1.
            change ([S1] *> [S0; S1] *> encSR v rest) with ([S1; S0; S1] *> encSR v rest).
            pose proof (step_a_101 (encSL v vl) (encSR v rest)) as s1.
            rewrite (encSL_pushLP h1), evalSymN_one, pWord_2_0, lpow_1 in ih.
            exact (etrans (pev s1) ih).
          - destruct (symPushLP 2 0 symOne vl) as [vl1 |] eqn:h1; [| discriminate].
            destruct (symPushLP 1 0 c vl1) as [vl2 |] eqn:h2; [| discriminate].
            pose proof (IH false vl2 vl' vr' h) as ih.
            cbn [encSR]. rewrite pWord_1_0, Str_app_lpow_succ.
            change ([S1] *> [S0; S1] *> (([S0; S1] ^^ evalSymN v c) *> encSR v rest))
              with ([S1; S0; S1] *> (([S0; S1] ^^ evalSymN v c) *> encSR v rest)).
            pose proof (step_a_101 (encSL v vl) (([S0; S1] ^^ evalSymN v c) *> encSR v rest)) as s1.
            pose proof (step_a_01_pow (evalSymN v c) (encSL v vl1) (encSR v rest)) as s2.
            rewrite (encSL_pushLP h1), evalSymN_one, pWord_2_0, lpow_1 in s2.
            rewrite (encSL_pushLP h2), pWord_1_0, (encSL_pushLP h1), evalSymN_one, pWord_2_0, lpow_1 in ih.
            exact (etrans (pev s1) (etrans s2 ih)). }
        { destruct (symPushLP 1 0 (symAddConst c 1%N) vl) as [vl1 |] eqn:h1; [| discriminate].
          pose proof (IH false vl1 vl' vr' h) as ih.
          cbn [encSR]. rewrite pWord_1_0.
          pose proof (step_a_01_pow (evalSymN v c + 1) (encSL v vl) (encSR v rest)) as hs.
          rewrite (encSL_pushLP h1), evalSymN_addConst, pWord_1_0 in ih.
          change (#1) with 1 in ih.
          exact (etrans hs ih). }
      * destruct after1; cbn [symSweepARAux] in h.
        { destruct (symPushLP 2 0 (symAddConst c 1%N) vl) as [vl1 |] eqn:h1; [| discriminate].
          pose proof (IH true vl1 vl' vr' h) as ih.
          cbn [encSR]. rewrite pWord_1_1.
          pose proof (step_a_101_pow (evalSymN v c + 1) (encSL v vl) (encSR v rest)) as hs.
          rewrite (encSL_pushLP h1), evalSymN_addConst, pWord_2_0 in ih.
          change (#1) with 1 in ih.
          exact (etrans hs ih). }
        { destruct (symDec c) as [| c' |] eqn:hd; [| | discriminate].
          - destruct (symPushLP 1 0 symOne vl) as [vl1 |] eqn:h1; [| discriminate].
            pose proof (IH true vl1 vl' vr' h) as ih.
            cbn [encSR]. rewrite (symDec_isZero hd), pWord_1_1, lpow_1.
            change (wT *> encSR v rest) with ([S0; S1] *> [S1] *> encSR v rest).
            pose proof (step_a_01 (encSL v vl) ([S1] *> encSR v rest)) as s1.
            rewrite (encSL_pushLP h1), evalSymN_one, pWord_1_0, lpow_1 in ih.
            exact (etrans (pev s1) ih).
          - destruct (symPushLP 1 0 symOne vl) as [vl1 |] eqn:h1; [| discriminate].
            destruct (symPushLP 2 0 c vl1) as [vl2 |] eqn:h2; [| discriminate].
            pose proof (IH true vl2 vl' vr' h) as ih.
            cbn [encSR]. rewrite pWord_1_1, Str_app_lpow_succ.
            change (wT *> (wT ^^ evalSymN v c) *> encSR v rest)
              with ([S0; S1] *> [S1] *> (wT ^^ evalSymN v c) *> encSR v rest).
            pose proof (step_a_01 (encSL v vl) ([S1] *> (wT ^^ evalSymN v c) *> encSR v rest)) as s1.
            pose proof (step_a_101_pow (evalSymN v c) (encSL v vl1) (encSR v rest)) as s2.
            rewrite (encSL_pushLP h1), evalSymN_one, pWord_1_0, lpow_1 in s2.
            rewrite (encSL_pushLP h2), pWord_2_0, (encSL_pushLP h1), evalSymN_one, pWord_1_0, lpow_1 in ih.
            exact (etrans (pev s1) (etrans s2 ih)). }
      * destruct after1; cbn [symSweepARAux] in h.
        { destruct (symPushLP 2 0 symOne vl) as [vl1 |] eqn:h1; [| discriminate].
          destruct (symDecPairR 1 (S (S o'')) c rest) as [r1 |] eqn:hd; [| discriminate].
          destruct (symPushOnesR (S (S o'')) r1) as [r2 |] eqn:h2; [| discriminate].
          inversion h; subst vl' vr'; clear h.
          rewrite <- (encSR_decPairR hd), (encSL_pushLP h1), (encSR_pushOnesR h2),
            evalSymN_one, pWord_2_0, lpow_1, pWord_1_succ, app_Str_app.
          change ([S1] *> [S0; S1] *> ([S1] ^^ S (S o'')) *> encSR v r1)
            with ([S1; S0; S1] *> ([S1] ^^ S (S o'')) *> encSR v r1).
          exact (pev (step_a_101 (encSL v vl) _)). }
        { destruct (symPushLP 1 0 symOne vl) as [vl1 |] eqn:h1; [| discriminate].
          destruct (symDecPairR 1 (S (S o'')) c rest) as [r1 |] eqn:hd; [| discriminate].
          destruct (symPushOnesR (S (S o'')) r1) as [r2 |] eqn:h2; [| discriminate].
          inversion h; subst vl' vr'; clear h.
          rewrite <- (encSR_decPairR hd), (encSL_pushLP h1), (encSR_pushOnesR h2),
            evalSymN_one, pWord_1_0, lpow_1, pWord_1_succ, app_Str_app.
          exact (pev (step_a_01 (encSL v vl) _)). }
    + destruct after1; cbn [symSweepARAux] in h.
      * destruct (symPushOnesR 1 (sr_pair (S (S z'')) o c :: rest)) as [r1 |] eqn:hp; [| discriminate].
        inversion h; subst vl' vr'; clear h.
        rewrite (encSR_pushOnesR hp), lpow_1. apply evstep_refl.
      * inversion h; subst vl' vr'; apply evstep_refl.
    + destruct after1; cbn [symSweepARAux] in h.
      * destruct (symPushLP 2 0 (symConst 2%N) vl) as [vl1 |] eqn:h1; [| discriminate].
        destruct (symDecMidR c rest) as [rest' |] eqn:hd; [| discriminate].
        inversion h; subst vl' vr'; clear h.
        rewrite <- (encSR_decMidR hd), (encSL_pushLP h1), evalSymN_const, pWord_2_0.
        change (#2) with 2.
        cbn [encSR]. rewrite evalSymN_zero, pWord_0_0, pWord_2_0, lpow_1.
        change ([S1] *> wRM *> encSR v rest') with ([S1] *> (wT ^^ 2) *> wZ *> encSR v rest').
        exact (step_a_101_pow 2 (encSL v vl) (wZ *> encSR v rest')).
      * destruct (symPushLP 1 0 symOne vl) as [vl1 |] eqn:h1; [| discriminate].
        destruct (symPushLP 2 0 symOne vl1) as [vl2 |] eqn:h2; [| discriminate].
        destruct (symDecMidR c rest) as [rest' |] eqn:hd; [| discriminate].
        inversion h; subst vl' vr'; clear h.
        rewrite <- (encSR_decMidR hd), (encSL_pushLP h2), (encSL_pushLP h1),
          evalSymN_one, pWord_2_0, pWord_1_0, !lpow_1.
        cbn [encSR]. rewrite evalSymN_zero, pWord_0_0, pWord_2_0, lpow_1.
        change (wRM *> encSR v rest') with ([S0; S1] *> [S1; S0; S1] *> [S1] *> wZ *> encSR v rest').
        exact (pev (ptrans (step_a_01 (encSL v vl) _) (step_a_101 ([S0; S1] *> encSL v vl) _))).
Qed.

Fixpoint symSweepDL (ts : list SymLTok) (vr : list SymRTok)
  : option (list SymLTok * list SymRTok) :=
  match ts with
  | [] => Some ([], vr)
  | sl_mid c :: rest => Some (sl_mid c :: rest, vr)
  | sl_pair 0 o c :: rest => Some (sl_pair 0 o c :: rest, vr)
  | sl_pair 1 o c :: rest => Some (sl_pair 1 o c :: rest, vr)
  | sl_pair 2 0 c :: rest =>
    match symPushRP 1 1 (symAddConst c 1%N) vr with
    | None => None
    | Some vr1 => symSweepDL rest vr1
    end
  | sl_pair 2 (S o') c :: rest =>
    match symDecPairL 2 (S o') c rest with
    | None => None
    | Some l1 =>
      match symPushOnesL (S o') l1 with
      | None => None
      | Some vl' =>
        match symPushRP 1 1 symOne vr with
        | None => None
        | Some vr' => Some (vl', vr')
        end
      end
    end
  | sl_pair (S (S (S z'''))) o c :: rest => Some (sl_pair (S (S (S z'''))) o c :: rest, vr)
  end.

Lemma symSweepDL_sound (v : V5) :
  forall (ts : list SymLTok) (vr : list SymRTok) (vl' : list SymLTok) (vr' : list SymRTok),
    symSweepDL ts vr = Some (vl', vr') ->
    cfgD (encSL v ts) (encSR v vr) -->* cfgD (encSL v vl') (encSR v vr').
Proof.
  induction ts as [| [[| [| [| z''']]] o c | c] rest IH]; intros vr vl' vr' h;
    try (cbn [symSweepDL] in h; inversion h; subst vl' vr'; apply evstep_refl).
  destruct o as [| o']; cbn [symSweepDL] in h.
  - destruct (symPushRP 1 1 (symAddConst c 1%N) vr) as [vr1 |] eqn:h1; [| discriminate].
    pose proof (IH vr1 vl' vr' h) as ih.
    cbn [encSL]. rewrite pWord_2_0.
    pose proof (step_d_001_pow (evalSymN v c + 1) (encSL v rest) (encSR v vr)) as hs.
    rewrite (encSR_pushRP h1), evalSymN_addConst, pWord_1_1 in ih.
    change (#1) with 1 in ih.
    exact (etrans hs ih).
  - destruct (symDecPairL 2 (S o') c rest) as [l1 |] eqn:hd; [| discriminate].
    destruct (symPushOnesL (S o') l1) as [l2 |] eqn:h1; [| discriminate].
    destruct (symPushRP 1 1 symOne vr) as [r2 |] eqn:h2; [| discriminate].
    inversion h; subst vl' vr'; clear h.
    rewrite <- (encSL_decPairL hd), (encSL_pushOnesL h1), (encSR_pushRP h2),
      evalSymN_one, pWord_1_1, lpow_1, pWord_2_S, app_Str_app.
    exact (pev (step_d_001 _ (encSR v vr))).
Qed.

Fixpoint symSweepEL (ts : list SymLTok) (vr : list SymRTok)
  : option (list SymLTok * list SymRTok) :=
  match ts with
  | [] => Some ([], vr)
  | sl_mid c :: rest => Some (sl_mid c :: rest, vr)
  | sl_pair 0 o c :: rest =>
    if symIsConst c then
      let k := (o + 1) * (#(sk c) + 1) in
      match symPushZerosR k vr with
      | None => None
      | Some vr1 => symSweepEL rest vr1
      end
    else None
  | sl_pair (S z') o c :: rest => Some (sl_pair (S z') o c :: rest, vr)
  end.

Lemma symSweepEL_sound (v : V5) :
  forall (ts : list SymLTok) (vr : list SymRTok) (vl' : list SymLTok) (vr' : list SymRTok),
    symSweepEL ts vr = Some (vl', vr') ->
    cfgE (encSL v ts) (encSR v vr) -->* cfgE (encSL v vl') (encSR v vr').
Proof.
  induction ts as [| [[| z'] o c | c] rest IH]; intros vr vl' vr' h;
    try (cbn [symSweepEL] in h; inversion h; subst vl' vr'; apply evstep_refl).
  cbn [symSweepEL] in h.
  destruct (symIsConst c) eqn:hc; [| discriminate].
  destruct (symPushZerosR ((o + 1) * (#(sk c) + 1)) vr) as [vr1 |] eqn:h1; [| discriminate].
  pose proof (IH vr1 vl' vr' h) as ih.
  cbn [encSL]. rewrite (evalSymN_isConst hc), pWord_zero_eq, lpow_mul_comm.
  pose proof (step_e_ones ((o + 1) * (#(sk c) + 1)) (encSL v rest) (encSR v vr)) as hs.
  rewrite (encSR_pushZerosR h1) in ih.
  exact (etrans hs ih).
Qed.

Definition symStepBase (s : SymState) : option SymState :=
  let '(m, vl0, vr0) := s in
  match m with
  | mHalt => None
  | mA =>
    match symSweepARAux vr0 false vl0 with
    | None => None
    | Some (vl, vr) =>
      match symPopBitR vr with
      | None => None
      | Some (r1, vr1) =>
        match r1 with
        | S0 =>
          match symPopBitR vr1 with
          | None => None
          | Some (r2, vr2) =>
            match r2 with
            | S0 =>
              match symPushOnesR 1 vr2 with
              | None => None
              | Some vra =>
                match symPushZerosR 1 vra with
                | None => None
                | Some vrb => Some (mD, vl, vrb)
                end
              end
            | S1 =>
              match symPushOnesL 1 vl with
              | None => None
              | Some vla =>
                match symPushZerosL 1 vla with
                | None => None
                | Some vlb => Some (mA, vlb, vr2)
                end
              end
            end
          end
        | S1 =>
          match symPopBitR vr1 with
          | None => None
          | Some (r2, vr2) =>
            match r2 with
            | S1 =>
              match symPushOnesL 1 vl with
              | None => None
              | Some vla =>
                match symPushZerosR 1 vr2 with
                | None => None
                | Some vra => Some (mE, vla, vra)
                end
              end
            | S0 =>
              match symPopBitR vr2 with
              | None => None
              | Some (r3, vr3) =>
                match r3 with
                | S0 =>
                  match symPushOnesL 1 vl with
                  | None => None
                  | Some vla =>
                    match symPushOnesR 1 vr3 with
                    | None => None
                    | Some vra =>
                      match symPushZerosR 1 vra with
                      | None => None
                      | Some vrb => Some (mE, vla, vrb)
                      end
                    end
                  end
                | S1 =>
                  match symPushLP 2 0 symOne vl with
                  | None => None
                  | Some vla => Some (mA, vla, vr3)
                  end
                end
              end
            end
          end
        end
      end
    end
  | mD =>
    match symSweepDL vl0 vr0 with
    | None => None
    | Some (vl, vr) =>
      match symPopBitL vl with
      | None => None
      | Some (l1, vl1) =>
        match l1 with
        | S1 =>
          match symPopBitL vl1 with
          | None => None
          | Some (l2, vl2) =>
            match l2 with
            | S1 =>
              match symPushZerosR 1 vr with
              | None => None
              | Some vra => Some (mHalt, vl2, vra)
              end
            | S0 =>
              match symPopBitL vl2 with
              | None => None
              | Some (l3, vl3) =>
                match l3 with
                | S0 =>
                  match symPushZerosR 1 vr with
                  | None => None
                  | Some vra =>
                    match symPushOnesR 1 vra with
                    | None => None
                    | Some vrb =>
                      match symPushZerosR 1 vrb with
                      | None => None
                      | Some vrc => Some (mD, vl3, vrc)
                      end
                    end
                  end
                | S1 =>
                  match symPushOnesL 1 vl3 with
                  | None => None
                  | Some vla =>
                    match symPushOnesR 1 vr with
                    | None => None
                    | Some vra =>
                      match symPushZerosR 1 vra with
                      | None => None
                      | Some vrb => Some (mE, vla, vrb)
                      end
                    end
                  end
                end
              end
            end
          end
        | S0 =>
          match symPopBitL vl1 with
          | None => None
          | Some (l2, vl2) =>
            match l2 with
            | S1 =>
              match symPushZerosL 1 vl2 with
              | None => None
              | Some vla =>
                match symPushOnesR 1 vr with
                | None => None
                | Some vra => Some (mA, vla, vra)
                end
              end
            | S0 =>
              match symPopBitL vl2 with
              | None => None
              | Some (l3, vl3) =>
                match l3 with
                | S1 =>
                  match symPushRP 1 1 symOne vr with
                  | None => None
                  | Some vra => Some (mD, vl3, vra)
                  end
                | S0 =>
                  match symPopBitL vl3 with
                  | None => None
                  | Some (l4, vl4) =>
                    match l4 with
                    | S0 =>
                      match symPushOnesL 1 vl4 with
                      | None => None
                      | Some vla =>
                        match symPushZerosL 1 vla with
                        | None => None
                        | Some vlb =>
                          match symPushOnesR 2 vr with
                          | None => None
                          | Some vra => Some (mA, vlb, vra)
                          end
                        end
                      end
                    | S1 =>
                      match symPushOnesL 1 vl4 with
                      | None => None
                      | Some vla =>
                        match symPushOnesR 2 vr with
                        | None => None
                        | Some vra =>
                          match symPushZerosR 1 vra with
                          | None => None
                          | Some vrb => Some (mE, vla, vrb)
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  | mE =>
    match symSweepEL vl0 vr0 with
    | None => None
    | Some (vl, vr) =>
      match symPopBitL vl with
      | None => None
      | Some (l1, vl1) =>
        match l1 with
        | S1 =>
          match symPushZerosR 1 vr with
          | None => None
          | Some vra => Some (mE, vl1, vra)
          end
        | S0 =>
          match symPopBitR vr with
          | None => None
          | Some (r1, vr1) =>
            match r1 with
            | S1 =>
              match symPushZerosL 2 vl1 with
              | None => None
              | Some vla => Some (mA, vla, vr1)
              end
            | S0 =>
              match symPopBitL vl1 with
              | None => None
              | Some (l2, vl2) =>
                match l2 with
                | S0 =>
                  match symPushOnesL 1 vl2 with
                  | None => None
                  | Some vla =>
                    match symPushZerosL 1 vla with
                    | None => None
                    | Some vlb =>
                      match symPushOnesR 1 vr1 with
                      | None => None
                      | Some vra => Some (mA, vlb, vra)
                      end
                    end
                  end
                | S1 =>
                  match symPushOnesL 1 vl2 with
                  | None => None
                  | Some vla =>
                    match symPushOnesR 1 vr1 with
                    | None => None
                    | Some vra =>
                      match symPushZerosR 1 vra with
                      | None => None
                      | Some vrb => Some (mE, vla, vrb)
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  end.

Lemma symStepBase_sound (v : V5) {s s' : SymState}
  (h : symStepBase s = Some s') :
  evalSym v s -->+ evalSym v s'.
Proof.
  destruct s as [[m vl0] vr0].
  destruct m; cbn [symStepBase evalSym] in h |- *.
  - (* mA *)
    destruct (symSweepARAux vr0 false vl0) as [[vl vr] |] eqn:hsw; [| discriminate].
    pose proof (symSweepARAux_sound v vr0 false vl0 vl vr hsw) as hsw'.
    destruct (symPopBitR vr) as [[r1 vr1] |] eqn:hp1; [| discriminate].
    pose proof (@encSR_popBitR v vr vr1 r1 hp1) as hr1.
    destruct r1.
    + (* r1 = S0 *)
      destruct (symPopBitR vr1) as [[r2 vr2] |] eqn:hp2; [| discriminate].
      pose proof (@encSR_popBitR v vr1 vr2 r2 hp2) as hr2.
      destruct r2.
      * destruct (symPushOnesR 1 vr2) as [vra |] eqn:h1; [| discriminate].
        destruct (symPushZerosR 1 vra) as [vrb |] eqn:h2; [| discriminate].
        inversion h; subst s'; clear h. cbn [evalSym].
        rewrite hr2 in hr1. rewrite hr1 in hsw'.
        rewrite (encSR_pushZerosR h2), (encSR_pushOnesR h1), !lpow_1.
        exact (sp_trans hsw' (exit_a_00 (encSL v vl) (encSR v vr2))).
      * destruct (symPushOnesL 1 vl) as [vla |] eqn:h1; [| discriminate].
        destruct (symPushZerosL 1 vla) as [vlb |] eqn:h2; [| discriminate].
        inversion h; subst s'; clear h. cbn [evalSym].
        rewrite hr2 in hr1. rewrite hr1 in hsw'.
        rewrite (encSL_pushZerosL h2), (encSL_pushOnesL h1), !lpow_1.
        exact (sp_trans hsw' (step_a_01 (encSL v vl) (encSR v vr2))).
    + (* r1 = S1 *)
      destruct (symPopBitR vr1) as [[r2 vr2] |] eqn:hp2; [| discriminate].
      pose proof (@encSR_popBitR v vr1 vr2 r2 hp2) as hr2.
      destruct r2.
      * destruct (symPopBitR vr2) as [[r3 vr3] |] eqn:hp3; [| discriminate].
        pose proof (@encSR_popBitR v vr2 vr3 r3 hp3) as hr3.
        destruct r3.
        { destruct (symPushOnesL 1 vl) as [vla |] eqn:h1; [| discriminate].
          destruct (symPushOnesR 1 vr3) as [vra |] eqn:h2; [| discriminate].
          destruct (symPushZerosR 1 vra) as [vrb |] eqn:h3; [| discriminate].
          inversion h; subst s'; clear h. cbn [evalSym].
          rewrite hr3 in hr2. rewrite hr2 in hr1. rewrite hr1 in hsw'.
          rewrite (encSL_pushOnesL h1), (encSR_pushZerosR h3), (encSR_pushOnesR h2), !lpow_1.
          exact (sp_trans hsw' (exit_a_100 (encSL v vl) (encSR v vr3))). }
        { destruct (symPushLP 2 0 symOne vl) as [vla |] eqn:h1; [| discriminate].
          inversion h; subst s'; clear h. cbn [evalSym].
          rewrite hr3 in hr2. rewrite hr2 in hr1. rewrite hr1 in hsw'.
          rewrite (encSL_pushLP h1), evalSymN_one, pWord_2_0, lpow_1.
          exact (sp_trans hsw' (step_a_101 (encSL v vl) (encSR v vr3))). }
      * destruct (symPushOnesL 1 vl) as [vla |] eqn:h1; [| discriminate].
        destruct (symPushZerosR 1 vr2) as [vra |] eqn:h2; [| discriminate].
        inversion h; subst s'; clear h. cbn [evalSym].
        rewrite hr2 in hr1. rewrite hr1 in hsw'.
        rewrite (encSL_pushOnesL h1), (encSR_pushZerosR h2), !lpow_1.
        exact (sp_trans hsw' (exit_a_11 (encSL v vl) (encSR v vr2))).
  - (* mD *)
    destruct (symSweepDL vl0 vr0) as [[vl vr] |] eqn:hsw; [| discriminate].
    pose proof (symSweepDL_sound v vl0 vr0 vl vr hsw) as hsw'.
    destruct (symPopBitL vl) as [[l1 vl1] |] eqn:hp1; [| discriminate].
    pose proof (@encSL_popBitL v vl vl1 l1 hp1) as hl1.
    destruct l1.
    + (* l1 = S0 *)
      destruct (symPopBitL vl1) as [[l2 vl2] |] eqn:hp2; [| discriminate].
      pose proof (@encSL_popBitL v vl1 vl2 l2 hp2) as hl2.
      destruct l2.
      * destruct (symPopBitL vl2) as [[l3 vl3] |] eqn:hp3; [| discriminate].
        pose proof (@encSL_popBitL v vl2 vl3 l3 hp3) as hl3.
        destruct l3.
        { destruct (symPopBitL vl3) as [[l4 vl4] |] eqn:hp4; [| discriminate].
          pose proof (@encSL_popBitL v vl3 vl4 l4 hp4) as hl4.
          destruct l4.
          - destruct (symPushOnesL 1 vl4) as [vla |] eqn:h1; [| discriminate].
            destruct (symPushZerosL 1 vla) as [vlb |] eqn:h2; [| discriminate].
            destruct (symPushOnesR 2 vr) as [vra |] eqn:h3; [| discriminate].
            inversion h; subst s'; clear h. cbn [evalSym].
            rewrite hl4 in hl3. rewrite hl3 in hl2. rewrite hl2 in hl1. rewrite hl1 in hsw'.
            rewrite (encSL_pushZerosL h2), (encSL_pushOnesL h1), (encSR_pushOnesR h3), !lpow_1.
            exact (sp_trans hsw' (exit_d_0000 (encSL v vl4) (encSR v vr))).
          - destruct (symPushOnesL 1 vl4) as [vla |] eqn:h1; [| discriminate].
            destruct (symPushOnesR 2 vr) as [vra |] eqn:h2; [| discriminate].
            destruct (symPushZerosR 1 vra) as [vrb |] eqn:h3; [| discriminate].
            inversion h; subst s'; clear h. cbn [evalSym].
            rewrite hl4 in hl3. rewrite hl3 in hl2. rewrite hl2 in hl1. rewrite hl1 in hsw'.
            rewrite (encSL_pushOnesL h1), (encSR_pushZerosR h3), (encSR_pushOnesR h2), !lpow_1.
            exact (sp_trans hsw' (exit_d_0001 (encSL v vl4) (encSR v vr))). }
        { destruct (symPushRP 1 1 symOne vr) as [vra |] eqn:h1; [| discriminate].
          inversion h; subst s'; clear h. cbn [evalSym].
          rewrite hl3 in hl2. rewrite hl2 in hl1. rewrite hl1 in hsw'.
          rewrite (encSR_pushRP h1), evalSymN_one, pWord_1_1, lpow_1.
          exact (sp_trans hsw' (step_d_001 (encSL v vl3) (encSR v vr))). }
      * destruct (symPushZerosL 1 vl2) as [vla |] eqn:h1; [| discriminate].
        destruct (symPushOnesR 1 vr) as [vra |] eqn:h2; [| discriminate].
        inversion h; subst s'; clear h. cbn [evalSym].
        rewrite hl2 in hl1. rewrite hl1 in hsw'.
        rewrite (encSL_pushZerosL h1), (encSR_pushOnesR h2), !lpow_1.
        exact (sp_trans hsw' (exit_d_01 (encSL v vl2) (encSR v vr))).
    + (* l1 = S1 *)
      destruct (symPopBitL vl1) as [[l2 vl2] |] eqn:hp2; [| discriminate].
      pose proof (@encSL_popBitL v vl1 vl2 l2 hp2) as hl2.
      destruct l2.
      * destruct (symPopBitL vl2) as [[l3 vl3] |] eqn:hp3; [| discriminate].
        pose proof (@encSL_popBitL v vl2 vl3 l3 hp3) as hl3.
        destruct l3.
        { destruct (symPushZerosR 1 vr) as [vra |] eqn:h1; [| discriminate].
          destruct (symPushOnesR 1 vra) as [vrb |] eqn:h2; [| discriminate].
          destruct (symPushZerosR 1 vrb) as [vrc |] eqn:h3; [| discriminate].
          inversion h; subst s'; clear h. cbn [evalSym].
          rewrite hl3 in hl2. rewrite hl2 in hl1. rewrite hl1 in hsw'.
          rewrite (encSR_pushZerosR h3), (encSR_pushOnesR h2), (encSR_pushZerosR h1), !lpow_1.
          exact (sp_trans hsw' (exit_d_100 (encSL v vl3) (encSR v vr))). }
        { destruct (symPushOnesL 1 vl3) as [vla |] eqn:h1; [| discriminate].
          destruct (symPushOnesR 1 vr) as [vra |] eqn:h2; [| discriminate].
          destruct (symPushZerosR 1 vra) as [vrb |] eqn:h3; [| discriminate].
          inversion h; subst s'; clear h. cbn [evalSym].
          rewrite hl3 in hl2. rewrite hl2 in hl1. rewrite hl1 in hsw'.
          rewrite (encSL_pushOnesL h1), (encSR_pushZerosR h3), (encSR_pushOnesR h2), !lpow_1.
          exact (sp_trans hsw' (exit_d_101 (encSL v vl3) (encSR v vr))). }
      * destruct (symPushZerosR 1 vr) as [vra |] eqn:h1; [| discriminate].
        inversion h; subst s'; clear h. cbn [evalSym].
        rewrite hl2 in hl1. rewrite hl1 in hsw'.
        rewrite (encSR_pushZerosR h1), lpow_1.
        exact (sp_trans hsw' (exit_d_11_halt (encSL v vl2) (encSR v vr))).
  - (* mE *)
    destruct (symSweepEL vl0 vr0) as [[vl vr] |] eqn:hsw; [| discriminate].
    pose proof (symSweepEL_sound v vl0 vr0 vl vr hsw) as hsw'.
    destruct (symPopBitL vl) as [[l1 vl1] |] eqn:hp1; [| discriminate].
    pose proof (@encSL_popBitL v vl vl1 l1 hp1) as hl1.
    destruct l1.
    + (* l1 = S0 *)
      destruct (symPopBitR vr) as [[r1 vr1] |] eqn:hq1; [| discriminate].
      pose proof (@encSR_popBitR v vr vr1 r1 hq1) as hr1.
      destruct r1.
      * destruct (symPopBitL vl1) as [[l2 vl2] |] eqn:hp2; [| discriminate].
        pose proof (@encSL_popBitL v vl1 vl2 l2 hp2) as hl2.
        destruct l2.
        { destruct (symPushOnesL 1 vl2) as [vla |] eqn:h1; [| discriminate].
          destruct (symPushZerosL 1 vla) as [vlb |] eqn:h2; [| discriminate].
          destruct (symPushOnesR 1 vr1) as [vra |] eqn:h3; [| discriminate].
          inversion h; subst s'; clear h. cbn [evalSym].
          rewrite hl2 in hl1. rewrite hl1, hr1 in hsw'.
          rewrite (encSL_pushZerosL h2), (encSL_pushOnesL h1), (encSR_pushOnesR h3), !lpow_1.
          exact (sp_trans hsw' (exit_e_00_r0 (encSL v vl2) (encSR v vr1))). }
        { destruct (symPushOnesL 1 vl2) as [vla |] eqn:h1; [| discriminate].
          destruct (symPushOnesR 1 vr1) as [vra |] eqn:h2; [| discriminate].
          destruct (symPushZerosR 1 vra) as [vrb |] eqn:h3; [| discriminate].
          inversion h; subst s'; clear h. cbn [evalSym].
          rewrite hl2 in hl1. rewrite hl1, hr1 in hsw'.
          rewrite (encSL_pushOnesL h1), (encSR_pushZerosR h3), (encSR_pushOnesR h2), !lpow_1.
          exact (sp_trans hsw' (exit_e_01_r0 (encSL v vl2) (encSR v vr1))). }
      * destruct (symPushZerosL 2 vl1) as [vla |] eqn:h1; [| discriminate].
        inversion h; subst s'; clear h. cbn [evalSym].
        rewrite hl1, hr1 in hsw'.
        rewrite (encSL_pushZerosL h1).
        exact (sp_trans hsw' (exit_e_0_r1 (encSL v vl1) (encSR v vr1))).
    + (* l1 = S1 *)
      destruct (symPushZerosR 1 vr) as [vra |] eqn:h1; [| discriminate].
      inversion h; subst s'; clear h. cbn [evalSym].
      rewrite hl1 in hsw'.
      rewrite (encSR_pushZerosR h1), lpow_1.
      exact (sp_trans hsw' (step_e_one (encSL v vl1) (encSR v vr))).
  - (* mHalt *)
    discriminate.
Qed.

(* ========================================================================== *)
(* Symbolic `[1,0,1,1]` Transducers (`symStepTrans`) & Linear Sweeps          *)
(* ========================================================================== *)

Definition symPush1011L (vl : list SymLTok) : option (list SymLTok) :=
  match symPushOnesL 2 vl with
  | None => None
  | Some vl1 =>
    match symPushZerosL 1 vl1 with
    | None => None
    | Some vl2 => symPushOnesL 1 vl2
    end
  end.

Definition symPush1011R (vr : list SymRTok) : option (list SymRTok) :=
  match symPushOnesR 2 vr with
  | None => None
  | Some vr1 =>
    match symPushZerosR 1 vr1 with
    | None => None
    | Some vr2 => symPushOnesR 1 vr2
    end
  end.

Lemma encSL_push1011L {v : V5} {vl out : list SymLTok}
  (h : symPush1011L vl = Some out) :
  encSL v out = [S1; S0; S1; S1] *> encSL v vl.
Proof.
  unfold symPush1011L in h.
  destruct (symPushOnesL 2 vl) as [vl1 |] eqn:h1; [| discriminate].
  destruct (symPushZerosL 1 vl1) as [vl2 |] eqn:h2; [| discriminate].
  rewrite (encSL_pushOnesL h), (encSL_pushZerosL h2), (encSL_pushOnesL h1).
  reflexivity.
Qed.

Lemma encSR_push1011R {v : V5} {vr out : list SymRTok}
  (h : symPush1011R vr = Some out) :
  encSR v out = [S1; S0; S1; S1] *> encSR v vr.
Proof.
  unfold symPush1011R in h.
  destruct (symPushOnesR 2 vr) as [vr1 |] eqn:h1; [| discriminate].
  destruct (symPushZerosR 1 vr1) as [vr2 |] eqn:h2; [| discriminate].
  rewrite (encSR_pushOnesR h), (encSR_pushZerosR h2), (encSR_pushOnesR h1).
  reflexivity.
Qed.

Definition symPeel1011L (vl : list SymLTok) : option (list SymLTok) :=
  match symNormL vl with
  | Some (sl_pair 0 0 c0 :: rest0) =>
    if symIsZero c0 then
      match symNormL rest0 with
      | Some (sl_pair 1 (S o') c :: rest1) =>
        match symDecPairL 1 (S o') c rest1 with
        | None => None
        | Some l1 => symPushOnesL o' l1
        end
      | _ => None
      end
    else None
  | _ => None
  end.

Definition symPeel1011R (vr : list SymRTok) : option (list SymRTok) :=
  match symNormR vr with
  | Some (sr_pair 0 0 c0 :: rest0) =>
    if symIsZero c0 then
      match symNormR rest0 with
      | Some (sr_pair 1 (S o') c :: rest1) =>
        match symDecPairR 1 (S o') c rest1 with
        | None => None
        | Some r1 => symPushOnesR o' r1
        end
      | _ => None
      end
    else None
  | _ => None
  end.

Lemma symPeel1011L_spec {v : V5} {vl lt : list SymLTok}
  (h : symPeel1011L vl = Some lt) :
  encSL v vl = [S1; S0; S1; S1] *> encSL v lt.
Proof.
  unfold symPeel1011L in h.
  destruct (symNormL vl) as [n0 |] eqn:hn0; [| discriminate].
  rewrite <- (encSL_normL hn0).
  destruct n0 as [| [[| z0] [| o0] c0 | c0] rest0]; try discriminate.
  destruct (symIsZero c0) eqn:hz0; [| discriminate].
  cbn [encSL]. rewrite (evalSymN_isZero hz0), pWord_0_0, lpow_1.
  destruct (symNormL rest0) as [n1 |] eqn:hn1; [| discriminate].
  rewrite <- (encSL_normL hn1).
  destruct n1 as [| [[| [| z1]] [| o'] c1 | c1] rest1]; try discriminate.
  destruct (symDecPairL 1 (S o') c1 rest1) as [l1 |] eqn:hd; [| discriminate].
  rewrite (encSL_pushOnesL h), <- (encSL_decPairL hd), pWord_1_S, app_Str_app.
  reflexivity.
Qed.

Lemma symPeel1011R_spec {v : V5} {vr rt : list SymRTok}
  (h : symPeel1011R vr = Some rt) :
  encSR v vr = [S1; S0; S1; S1] *> encSR v rt.
Proof.
  unfold symPeel1011R in h.
  destruct (symNormR vr) as [n0 |] eqn:hn0; [| discriminate].
  rewrite <- (encSR_normR hn0).
  destruct n0 as [| [[| z0] [| o0] c0 | c0] rest0]; try discriminate.
  destruct (symIsZero c0) eqn:hz0; [| discriminate].
  cbn [encSR]. rewrite (evalSymN_isZero hz0), pWord_0_0, lpow_1.
  destruct (symNormR rest0) as [n1 |] eqn:hn1; [| discriminate].
  rewrite <- (encSR_normR hn1).
  destruct n1 as [| [[| [| z1]] [| o'] c1 | c1] rest1]; try discriminate.
  destruct (symDecPairR 1 (S o') c1 rest1) as [r1 |] eqn:hd; [| discriminate].
  rewrite (encSR_pushOnesR h), <- (encSR_decPairR hd), pWord_1_S, app_Str_app.
  reflexivity.
Qed.

Fixpoint symConsumeAR1011 (rt : list SymRTok) (vl : list SymLTok) (did : bool)
  : option (list SymRTok * list SymLTok * bool) :=
  match rt with
  | [] => Some ([], vl, did)
  | sr_mid c :: rest =>
    match symPushWLMSem (symAddConst c 1%N) vl with
    | None => None
    | Some vl1 => symConsumeAR1011 rest vl1 true
    end
  | sr_pair 0 o c :: rest => Some (sr_pair 0 o c :: rest, vl, did)
  | sr_pair 1 0 c :: rest => Some (sr_pair 1 0 c :: rest, vl, did)
  | sr_pair 1 1 c :: rest =>
    match symPushLP 2 0 (symAddConst c 1%N) vl with
    | None => None
    | Some vl1 => symConsumeAR1011 rest vl1 true
    end
  | sr_pair 1 (S (S o'')) c :: rest => Some (sr_pair 1 (S (S o'')) c :: rest, vl, did)
  | sr_pair 2 0 c :: rest =>
    match symPushLP 1 1 (symAddConst c 1%N) vl with
    | None => None
    | Some vl1 => symConsumeAR1011 rest vl1 true
    end
  | sr_pair 2 (S o') c :: rest => Some (sr_pair 2 (S o') c :: rest, vl, did)
  | sr_pair (S (S (S z'''))) o c :: rest => Some (sr_pair (S (S (S z'''))) o c :: rest, vl, did)
  end.

Lemma symConsumeAR1011_star (v : V5) :
  forall (rt : list SymRTok) (vl : list SymLTok) (did : bool)
    (rt' : list SymRTok) (vl' : list SymLTok) (did' : bool),
    symConsumeAR1011 rt vl did = Some (rt', vl', did') ->
    cfgA (encSL v vl) ([S1; S0; S1; S1] *> encSR v rt) -->*
    cfgA (encSL v vl') ([S1; S0; S1; S1] *> encSR v rt').
Proof.
  induction rt as [| [[| [| [| z''']]] o c | c] rest IH]; intros vl did rt' vl' did' h;
    try (cbn [symConsumeAR1011] in h; inversion h; subst rt' vl' did'; apply evstep_refl).
  - destruct o as [| [| o'']]; cbn [symConsumeAR1011] in h;
      try (inversion h; subst rt' vl' did'; apply evstep_refl).
    destruct (symPushLP 2 0 (symAddConst c 1%N) vl) as [vl1 |] eqn:hp; [| discriminate].
    pose proof (IH vl1 true rt' vl' did' h) as ih.
    cbn [encSR]. rewrite pWord_1_1.
    pose proof (step_a_1011_wT_pow (evalSymN v c + 1) (encSL v vl) (encSR v rest)) as hs.
    rewrite (encSL_pushLP hp), evalSymN_addConst, pWord_2_0 in ih.
    change (#1) with 1 in ih.
    exact (etrans hs ih).
  - destruct o as [| o']; cbn [symConsumeAR1011] in h;
      try (inversion h; subst rt' vl' did'; apply evstep_refl).
    destruct (symPushLP 1 1 (symAddConst c 1%N) vl) as [vl1 |] eqn:hp; [| discriminate].
    pose proof (IH vl1 true rt' vl' did' h) as ih.
    cbn [encSR]. rewrite pWord_2_0.
    pose proof (step_a_1011_wZ_pow (evalSymN v c + 1) (encSL v vl) (encSR v rest)) as hs.
    rewrite (encSL_pushLP hp), evalSymN_addConst, pWord_1_1 in ih.
    change (#1) with 1 in ih.
    exact (etrans hs ih).
  - cbn [symConsumeAR1011] in h.
    destruct (symPushWLMSem (symAddConst c 1%N) vl) as [vl1 |] eqn:hp; [| discriminate].
    pose proof (IH vl1 true rt' vl' did' h) as ih.
    cbn [encSR].
    pose proof (step_a_1011_wRM_pow (evalSymN v c + 1) (encSL v vl) (encSR v rest)) as hs.
    rewrite (encSL_pushWLMSem hp), evalSymN_addConst in ih.
    change (#1) with 1 in ih.
    exact (etrans hs ih).
Qed.

Lemma symConsumeAR1011_plus (v : V5) :
  forall (rt : list SymRTok) (vl : list SymLTok) (rt' : list SymRTok) (vl' : list SymLTok),
    symConsumeAR1011 rt vl false = Some (rt', vl', true) ->
    cfgA (encSL v vl) ([S1; S0; S1; S1] *> encSR v rt) -->+
    cfgA (encSL v vl') ([S1; S0; S1; S1] *> encSR v rt').
Proof.
  intros [| [[| [| [| z''']]] o c | c] rest] vl rt' vl' h;
    try (cbn [symConsumeAR1011] in h; discriminate).
  - destruct o as [| [| o'']]; cbn [symConsumeAR1011] in h; try discriminate.
    destruct (symPushLP 2 0 (symAddConst c 1%N) vl) as [vl1 |] eqn:hp; [| discriminate].
    pose proof (symConsumeAR1011_star v rest vl1 true rt' vl' true h) as hr2.
    cbn [encSR]. rewrite pWord_1_1.
    pose proof (step_a_1011_wT_pow_plus (evalSymN v c) (encSL v vl) (encSR v rest)) as hs.
    rewrite (encSL_pushLP hp), evalSymN_addConst, pWord_2_0 in hr2.
    change (#1) with 1 in hr2.
    exact (ps_trans hs hr2).
  - destruct o as [| o']; cbn [symConsumeAR1011] in h; try discriminate.
    destruct (symPushLP 1 1 (symAddConst c 1%N) vl) as [vl1 |] eqn:hp; [| discriminate].
    pose proof (symConsumeAR1011_star v rest vl1 true rt' vl' true h) as hr2.
    cbn [encSR]. rewrite pWord_2_0.
    pose proof (step_a_1011_wZ_pow_plus (evalSymN v c) (encSL v vl) (encSR v rest)) as hs.
    rewrite (encSL_pushLP hp), evalSymN_addConst, pWord_1_1 in hr2.
    change (#1) with 1 in hr2.
    exact (ps_trans hs hr2).
  - cbn [symConsumeAR1011] in h.
    destruct (symPushWLMSem (symAddConst c 1%N) vl) as [vl1 |] eqn:hp; [| discriminate].
    pose proof (symConsumeAR1011_star v rest vl1 true rt' vl' true h) as hr2.
    cbn [encSR].
    pose proof (step_a_1011_wRM_pow_plus (evalSymN v c) (encSL v vl) (encSR v rest)) as hs.
    rewrite (encSL_pushWLMSem hp), evalSymN_addConst in hr2.
    change (#1) with 1 in hr2.
    exact (ps_trans hs hr2).
Qed.

Fixpoint symConsumeEL1011 (lt : list SymLTok) (vr : list SymRTok) (did : bool)
  : option (list SymLTok * list SymRTok * bool) :=
  match lt with
  | [] => Some ([], vr, did)
  | sl_mid c :: rest =>
    match symPushWRMSem (symAddConst c 1%N) vr with
    | None => None
    | Some vr1 => symConsumeEL1011 rest vr1 true
    end
  | sl_pair 0 o c :: rest => Some (sl_pair 0 o c :: rest, vr, did)
  | sl_pair 1 0 c :: rest => Some (sl_pair 1 0 c :: rest, vr, did)
  | sl_pair 1 1 c :: rest =>
    match symPushRP 2 0 (symAddConst c 1%N) vr with
    | None => None
    | Some vr1 => symConsumeEL1011 rest vr1 true
    end
  | sl_pair 1 (S (S o'')) c :: rest => Some (sl_pair 1 (S (S o'')) c :: rest, vr, did)
  | sl_pair 2 0 c :: rest =>
    match symPushRP 1 1 (symAddConst c 1%N) vr with
    | None => None
    | Some vr1 => symConsumeEL1011 rest vr1 true
    end
  | sl_pair 2 (S o') c :: rest => Some (sl_pair 2 (S o') c :: rest, vr, did)
  | sl_pair (S (S (S z'''))) o c :: rest => Some (sl_pair (S (S (S z'''))) o c :: rest, vr, did)
  end.

Lemma symConsumeEL1011_star (v : V5) :
  forall (lt : list SymLTok) (vr : list SymRTok) (did : bool)
    (lt' : list SymLTok) (vr' : list SymRTok) (did' : bool),
    symConsumeEL1011 lt vr did = Some (lt', vr', did') ->
    cfgE ([S1; S0; S1; S1] *> encSL v lt) (encSR v vr) -->*
    cfgE ([S1; S0; S1; S1] *> encSL v lt') (encSR v vr').
Proof.
  induction lt as [| [[| [| [| z''']]] o c | c] rest IH]; intros vr did lt' vr' did' h;
    try (cbn [symConsumeEL1011] in h; inversion h; subst lt' vr' did'; apply evstep_refl).
  - destruct o as [| [| o'']]; cbn [symConsumeEL1011] in h;
      try (inversion h; subst lt' vr' did'; apply evstep_refl).
    destruct (symPushRP 2 0 (symAddConst c 1%N) vr) as [vr1 |] eqn:hp; [| discriminate].
    pose proof (IH vr1 true lt' vr' did' h) as ih.
    cbn [encSL]. rewrite pWord_1_1.
    pose proof (step_e_1011_wT_pow (evalSymN v c + 1) (encSL v rest) (encSR v vr)) as hs.
    rewrite (encSR_pushRP hp), evalSymN_addConst, pWord_2_0 in ih.
    change (#1) with 1 in ih.
    exact (etrans hs ih).
  - destruct o as [| o']; cbn [symConsumeEL1011] in h;
      try (inversion h; subst lt' vr' did'; apply evstep_refl).
    destruct (symPushRP 1 1 (symAddConst c 1%N) vr) as [vr1 |] eqn:hp; [| discriminate].
    pose proof (IH vr1 true lt' vr' did' h) as ih.
    cbn [encSL]. rewrite pWord_2_0.
    pose proof (step_e_1011_wZ_pow (evalSymN v c + 1) (encSL v rest) (encSR v vr)) as hs.
    rewrite (encSR_pushRP hp), evalSymN_addConst, pWord_1_1 in ih.
    change (#1) with 1 in ih.
    exact (etrans hs ih).
  - cbn [symConsumeEL1011] in h.
    destruct (symPushWRMSem (symAddConst c 1%N) vr) as [vr1 |] eqn:hp; [| discriminate].
    pose proof (IH vr1 true lt' vr' did' h) as ih.
    cbn [encSL].
    pose proof (step_e_1011_wLM_pow (evalSymN v c + 1) (encSL v rest) (encSR v vr)) as hs.
    rewrite (encSR_pushWRMSem hp), evalSymN_addConst in ih.
    change (#1) with 1 in ih.
    exact (etrans hs ih).
Qed.

Lemma symConsumeEL1011_plus (v : V5) :
  forall (lt : list SymLTok) (vr : list SymRTok) (lt' : list SymLTok) (vr' : list SymRTok),
    symConsumeEL1011 lt vr false = Some (lt', vr', true) ->
    cfgE ([S1; S0; S1; S1] *> encSL v lt) (encSR v vr) -->+
    cfgE ([S1; S0; S1; S1] *> encSL v lt') (encSR v vr').
Proof.
  intros [| [[| [| [| z''']]] o c | c] rest] vr lt' vr' h;
    try (cbn [symConsumeEL1011] in h; discriminate).
  - destruct o as [| [| o'']]; cbn [symConsumeEL1011] in h; try discriminate.
    destruct (symPushRP 2 0 (symAddConst c 1%N) vr) as [vr1 |] eqn:hp; [| discriminate].
    pose proof (symConsumeEL1011_star v rest vr1 true lt' vr' true h) as hr2.
    cbn [encSL]. rewrite pWord_1_1.
    pose proof (step_e_1011_wT_pow_plus (evalSymN v c) (encSL v rest) (encSR v vr)) as hs.
    rewrite (encSR_pushRP hp), evalSymN_addConst, pWord_2_0 in hr2.
    change (#1) with 1 in hr2.
    exact (ps_trans hs hr2).
  - destruct o as [| o']; cbn [symConsumeEL1011] in h; try discriminate.
    destruct (symPushRP 1 1 (symAddConst c 1%N) vr) as [vr1 |] eqn:hp; [| discriminate].
    pose proof (symConsumeEL1011_star v rest vr1 true lt' vr' true h) as hr2.
    cbn [encSL]. rewrite pWord_2_0.
    pose proof (step_e_1011_wZ_pow_plus (evalSymN v c) (encSL v rest) (encSR v vr)) as hs.
    rewrite (encSR_pushRP hp), evalSymN_addConst, pWord_1_1 in hr2.
    change (#1) with 1 in hr2.
    exact (ps_trans hs hr2).
  - cbn [symConsumeEL1011] in h.
    destruct (symPushWRMSem (symAddConst c 1%N) vr) as [vr1 |] eqn:hp; [| discriminate].
    pose proof (symConsumeEL1011_star v rest vr1 true lt' vr' true h) as hr2.
    cbn [encSL].
    pose proof (step_e_1011_wLM_pow_plus (evalSymN v c) (encSL v rest) (encSR v vr)) as hs.
    rewrite (encSR_pushWRMSem hp), evalSymN_addConst in hr2.
    change (#1) with 1 in hr2.
    exact (ps_trans hs hr2).
Qed.

Definition symStepTrans (s : SymState) : option SymState :=
  let '(m, vl, vr) := s in
  match m with
  | mA =>
    match symPeel1011R vr with
    | Some rt0 =>
      match symConsumeAR1011 rt0 vl false with
      | Some (rt, vl2, true) =>
        match symPush1011R rt with
        | None => None
        | Some vr' => Some (mA, vl2, vr')
        end
      | Some (_, _, false) => symStepBase (mA, vl, vr)
      | None => None
      end
    | None => symStepBase (mA, vl, vr)
    end
  | mE =>
    match symPeel1011L vl with
    | Some lt0 =>
      match symConsumeEL1011 lt0 vr false with
      | Some (lt, vr2, true) =>
        match symPush1011L lt with
        | None => None
        | Some vl' => Some (mE, vl', vr2)
        end
      | Some (_, _, false) => symStepBase (mE, vl, vr)
      | None => None
      end
    | None => symStepBase (mE, vl, vr)
    end
  | _ => symStepBase s
  end.

Lemma symStepTrans_sound (v : V5) {s s' : SymState}
  (h : symStepTrans s = Some s') :
  evalSym v s -->+ evalSym v s'.
Proof.
  destruct s as [[m vl] vr].
  destruct m; cbn [symStepTrans] in h.
  - destruct (symPeel1011R vr) as [rt0 |] eqn:hp; [| exact (symStepBase_sound v h)].
    destruct (symConsumeAR1011 rt0 vl false) as [[[rt vl2] did] |] eqn:hc; [| discriminate].
    destruct did; [| exact (symStepBase_sound v h)].
    destruct (symPush1011R rt) as [vr' |] eqn:hpu; [| discriminate].
    inversion h; subst s'; clear h.
    cbn [evalSym]. rewrite (symPeel1011R_spec hp), (encSR_push1011R hpu).
    exact (symConsumeAR1011_plus v rt0 vl rt vl2 hc).
  - exact (symStepBase_sound v h).
  - destruct (symPeel1011L vl) as [lt0 |] eqn:hp; [| exact (symStepBase_sound v h)].
    destruct (symConsumeEL1011 lt0 vr false) as [[[lt vr2] did] |] eqn:hc; [| discriminate].
    destruct did; [| exact (symStepBase_sound v h)].
    destruct (symPush1011L lt) as [vl' |] eqn:hpu; [| discriminate].
    inversion h; subst s'; clear h.
    cbn [evalSym]. rewrite (symPeel1011L_spec hp), (encSL_push1011L hpu).
    exact (symConsumeEL1011_plus v lt0 vr lt vr2 hc).
  - exact (symStepBase_sound v h).
Qed.

(* ========================================================================== *)
(* Linear Sweeps & Era Accelerators                                           *)
(* ========================================================================== *)

Definition symTryDL1WZ (vl : list SymLTok) (vr : list SymRTok) : option SymState :=
  match vl, vr with
  | sl_pair 0 0 c0 :: vl1, sr_pair 1 0 cr :: vr1 =>
    if symIsZero c0 then
      match symNormL vl1 with
      | Some (sl_pair 2 0 cz :: lRest) =>
        match symDecPairR 1 0 cr vr1 with
        | None => None
        | Some rAfter =>
          match symPushRP 2 0 (symAddConst cz 1%N) rAfter with
          | None => None
          | Some r1 =>
            match symPushRP 1 0 symOne r1 with
            | None => None
            | Some r2 => Some (mD, sl_pair 0 0 symZero :: lRest, r2)
            end
          end
        end
      | _ => None
      end
    else None
  | _, _ => None
  end.

Lemma symTryDL1WZ_sound (v : V5) {vl : list SymLTok} {vr : list SymRTok} {s' : SymState}
  (h : symTryDL1WZ vl vr = Some s') :
  evalSym v (mD, vl, vr) -->+ evalSym v s'.
Proof.
  destruct vl as [| [[| z0] [| o0] c0 | c0] vl1]; try discriminate.
  destruct vr as [| [[| [| zr]] [| or_] cr | cr] vr1]; try discriminate.
  cbn [symTryDL1WZ] in h.
  destruct (symIsZero c0) eqn:hz0; [| discriminate].
  destruct (symNormL vl1) as [n1 |] eqn:hn; [| discriminate].
  destruct n1 as [| [[| [| [| z1]]] [| o1] cz | cz] lRest]; try discriminate.
  destruct (symDecPairR 1 0 cr vr1) as [rAfter |] eqn:hd; [| discriminate].
  destruct (symPushRP 2 0 (symAddConst cz 1%N) rAfter) as [r1 |] eqn:h1; [| discriminate].
  destruct (symPushRP 1 0 symOne r1) as [r2 |] eqn:h2; [| discriminate].
  inversion h; subst s'; clear h.
  cbn [evalSym encSL].
  rewrite (evalSymN_isZero hz0), evalSymN_zero, pWord_0_0, lpow_1, <- (encSL_normL hn).
  cbn [encSL]. rewrite pWord_2_0, <- (encSR_decPairR hd), pWord_1_0.
  rewrite (encSR_pushRP h2), (encSR_pushRP h1), evalSymN_one, evalSymN_addConst,
    pWord_1_0, pWord_2_0, lpow_1.
  change (#1) with 1.
  exact (step_dl_1_wZ_pow_plus (evalSymN v cz) (encSL v lRest) (encSR v rAfter)).
Qed.

Definition symTryEL1101 (vl : list SymLTok) (vr : list SymRTok) : option SymState :=
  match vl, vr with
  | sl_pair 0 1 c0 :: vl1, sr_pair 1 0 cr :: vr1 =>
    if symIsZero c0 then
      match symNormL vl1 with
      | Some (sl_pair 1 1 ct :: lRest) =>
        match symDecPairR 1 0 cr vr1 with
        | None => None
        | Some rAfter =>
          match symPushRP 2 0 (symAddConst ct 1%N) rAfter with
          | None => None
          | Some r1 =>
            match symPushRP 1 0 symOne r1 with
            | None => None
            | Some r2 => Some (mE, sl_pair 0 1 symZero :: lRest, r2)
            end
          end
        end
      | _ => None
      end
    else None
  | _, _ => None
  end.

Lemma symTryEL1101_sound (v : V5) {vl : list SymLTok} {vr : list SymRTok} {s' : SymState}
  (h : symTryEL1101 vl vr = Some s') :
  evalSym v (mE, vl, vr) -->+ evalSym v s'.
Proof.
  destruct vl as [| [[| z0] [| [| o0]] c0 | c0] vl1]; try discriminate.
  destruct vr as [| [[| [| zr]] [| or_] cr | cr] vr1]; try discriminate.
  cbn [symTryEL1101] in h.
  destruct (symIsZero c0) eqn:hz0; [| discriminate].
  destruct (symNormL vl1) as [n1 |] eqn:hn; [| discriminate].
  destruct n1 as [| [[| [| z1]] [| [| o1]] ct | ct] lRest]; try discriminate.
  destruct (symDecPairR 1 0 cr vr1) as [rAfter |] eqn:hd; [| discriminate].
  destruct (symPushRP 2 0 (symAddConst ct 1%N) rAfter) as [r1 |] eqn:h1; [| discriminate].
  destruct (symPushRP 1 0 symOne r1) as [r2 |] eqn:h2; [| discriminate].
  inversion h; subst s'; clear h.
  cbn [evalSym encSL].
  rewrite (evalSymN_isZero hz0), evalSymN_zero, pWord_0_1, lpow_1, <- (encSL_normL hn).
  cbn [encSL]. rewrite pWord_1_1, <- (encSR_decPairR hd), pWord_1_0.
  rewrite (encSR_pushRP h2), (encSR_pushRP h1), evalSymN_one, evalSymN_addConst,
    pWord_1_0, pWord_2_0, lpow_1.
  change (#1) with 1.
  exact (step_el_11_01_pow_plus (evalSymN v ct) (encSL v lRest) (encSR v rAfter)).
Qed.

Fixpoint symPeelLeadingWZL (cur : list SymLTok) (z0 : SymN) : SymN * list SymLTok :=
  match cur with
  | [] => (z0, [])
  | sl_pair 2 0 c :: rest => symPeelLeadingWZL rest (symAdd z0 (symAddConst c 1%N))
  | ts => (z0, ts)
  end.

Lemma symPeelLeadingWZL_spec (v : V5) :
  forall (cur : list SymLTok) (z0 : SymN),
    let res := symPeelLeadingWZL cur z0 in
    evalSymN v z0 <= evalSymN v (fst res) /\
    encSL v cur = (wZ ^^ (evalSymN v (fst res) - evalSymN v z0)) *> encSL v (snd res).
Proof.
  induction cur as [| [[| [| [| z''']]] [| o'] c | c] rest IH]; intros z0;
    try (cbn [symPeelLeadingWZL fst snd]; split; [lia | rewrite Nat.sub_diag; reflexivity]).
  cbn [symPeelLeadingWZL encSL].
  destruct (IH (symAdd z0 (symAddConst c 1%N))) as [hle henc].
  rewrite evalSymN_add, evalSymN_addConst in hle, henc.
  change (#1) with 1 in hle, henc.
  split; [lia |].
  rewrite pWord_2_0, henc, pow_append_pow.
  f_equal. f_equal. lia.
Qed.

Definition symTryEraConv (vl : list SymLTok) (vr : list SymRTok) : option SymState :=
  match vl, vr with
  | sl_pair 0 0 c0 :: lRest0, [sr_pair 1 1 cb; sr_pair 1 0 c1] =>
    if andb (symIsZero c0) (symIsZero c1) then
      let vb := symAddConst cb 1%N in
      if N.leb 2%N (sk vb) then
        let '(zTot, lTail) := symPeelLeadingWZL lRest0 symZero in
        if N.leb 3%N (sk zTot) then
          match symDivMod (mkSymN (sc0 zTot) (sc1 zTot) (sc2 zTot) (sc3 zTot) (sc4 zTot) (sk zTot - 1)%N) 2%N with
          | Some (vk, rem) =>
            if N.leb 1%N (sk vk) then
              match symPushLP 2 0 (symConst (1 + rem)%N) lTail with
              | None => None
              | Some l1 =>
                let b4k := symAdd vb (symScale 4%N vk) in
                Some (mE, sl_pair 0 0 symZero :: l1,
                  [sr_pair 1 1 (mkSymN (sc0 b4k) (sc1 b4k) (sc2 b4k) (sc3 b4k) (sc4 b4k) (sk b4k - 1)%N);
                   sr_pair 1 0 symZero])
              end
            else None
          | None => None
          end
        else None
      else None
    else None
  | _, _ => None
  end.

Lemma symTryEraConv_sound (v : V5) {vl : list SymLTok} {vr : list SymRTok} {s' : SymState}
  (h : symTryEraConv vl vr = Some s') :
  evalSym v (mE, vl, vr) -->+ evalSym v s'.
Proof.
  destruct vl as [| [[| z0] [| o0] c0 | c0] lRest0]; try discriminate.
  destruct vr as [| [[| [| zr0]] [| [| or0]] cb | cb] [| [[| [| zr1]] [| or1] c1 | c1] [| ? ?]]];
    try discriminate.
  cbn [symTryEraConv] in h.
  destruct (andb (symIsZero c0) (symIsZero c1)) eqn:hz01; [| discriminate].
  split_andb.
  destruct (N.leb 2%N (sk (symAddConst cb 1%N))) eqn:hB; [| discriminate].
  pose proof (symPeelLeadingWZL_spec v lRest0 symZero) as hp.
  destruct (symPeelLeadingWZL lRest0 symZero) as [zTot lTail] eqn:hpz.
  cbn [fst snd] in hp. destruct hp as [hp_le hp_enc].
  destruct (N.leb 3%N (sk zTot)) eqn:hz; [| discriminate].
  destruct (symDivMod (mkSymN (sc0 zTot) (sc1 zTot) (sc2 zTot) (sc3 zTot) (sc4 zTot) (sk zTot - 1)%N) 2%N)
    as [[vk rem] |] eqn:hdm; [| discriminate].
  destruct (N.leb 1%N (sk vk)) eqn:hK; [| discriminate].
  destruct (symPushLP 2 0 (symConst (1 + rem)%N) lTail) as [l1 |] eqn:hpl; [| discriminate].
  inversion h; subst s'; clear h.
  split_andb.
  destruct (evalSymN_divMod (v := v) hdm) as [_ [hrem2 hdiv]].
  pose proof (evalSymN_ge_k v vk) as hvk_ge.
  pose proof (evalSymN_ge_k v cb) as hcb_ge.
  pose proof (evalSymN_ge_k v zTot) as hz_ge.
  cbn [symAddConst sk] in hB.
  assert (hKz : 1 <= evalSymN v vk) by lia.
  assert (hsub1 : evalSymN v (mkSymN (sc0 zTot) (sc1 zTot) (sc2 zTot) (sc3 zTot) (sc4 zTot) (sk zTot - 1)%N) =
    evalSymN v zTot - 1).
  { unfold evalSymN. cbn [sc0 sc1 sc2 sc3 sc4 sk]. lia. }
  rewrite hsub1 in hdiv.
  change (#2) with 2 in hdiv, hrem2.
  eapply progress_eq_both;
    [exact (era_conv_loop_plus (evalSymN v vk) (#rem) (evalSymN v cb - 1) (encSL v lTail) hKz) | |].
  - cbn [evalSym encSL encSR].
    rewrite (evalSymN_isZero H), (evalSymN_isZero H0), hp_enc, ?evalSymN_zero, Nat.sub_0_r,
      pWord_0_0, pWord_1_1, pWord_1_0, ?lpow_1.
    replace (evalSymN v zTot) with (2 * evalSymN v vk + (#rem + 1)) by lia.
    replace (evalSymN v cb + 1) with ((evalSymN v cb - 1) + 2) by lia.
    reflexivity.
  - cbn [evalSym encSL encSR].
    rewrite ?evalSymN_zero, pWord_0_0, pWord_1_1, pWord_1_0, ?lpow_1,
      (encSL_pushLP hpl), evalSymN_const, pWord_2_0.
    f_equal.
    + f_equal. f_equal. f_equal. lia.
    + f_equal. f_equal. unfold evalSymN. cbn [sc0 sc1 sc2 sc3 sc4 sk].
      change (match sc0 vk with 0%N => 0%N | N.pos q => N.pos q~0~0 end) with (4 * sc0 vk)%N.
      change (match sc1 vk with 0%N => 0%N | N.pos q => N.pos q~0~0 end) with (4 * sc1 vk)%N.
      change (match sc2 vk with 0%N => 0%N | N.pos q => N.pos q~0~0 end) with (4 * sc2 vk)%N.
      change (match sc3 vk with 0%N => 0%N | N.pos q => N.pos q~0~0 end) with (4 * sc3 vk)%N.
      change (match sc4 vk with 0%N => 0%N | N.pos q => N.pos q~0~0 end) with (4 * sc4 vk)%N.
      change (match sk vk with 0%N => 0%N | N.pos q => N.pos q~0~0 end) with (4 * sk vk)%N.
      lia.
Qed.

Inductive SymMidItem : Type :=
  | smi_mid (cnt : SymN)
  | smi_t (cnt : SymN)
  | smi_z (cnt : SymN).

Definition evalMidItem (v : V5) (m : SymMidItem) : MidItem :=
  match m with
  | smi_mid c => mi_mid (evalSymN v c)
  | smi_t c => mi_t (evalSymN v c)
  | smi_z c => mi_z (evalSymN v c)
  end.

Fixpoint symRebuildMR (ms : list SymMidItem) (tail : list SymRTok) : option (list SymRTok) :=
  match ms with
  | [] => Some tail
  | smi_mid k :: rest =>
    match symRebuildMR rest tail with
    | None => None
    | Some t1 => symPushWRMSem k t1
    end
  | smi_t k :: rest =>
    match symRebuildMR rest tail with
    | None => None
    | Some t1 => symPushRP 1 1 k t1
    end
  | smi_z k :: rest =>
    match symRebuildMR rest tail with
    | None => None
    | Some t1 => symPushRP 2 0 k t1
    end
  end.

Lemma encSR_symRebuildMR (v : V5) :
  forall (ms : list SymMidItem) (tail out : list SymRTok),
    symRebuildMR ms tail = Some out ->
    encSR v out = encMidR (map (evalMidItem v) ms) (encSR v tail).
Proof.
  induction ms as [| [k | k | k] rest IH]; intros tail out h.
  - cbn [symRebuildMR] in h. inversion h; reflexivity.
  - cbn [symRebuildMR] in h.
    destruct (symRebuildMR rest tail) as [t1 |] eqn:hr; [| discriminate].
    rewrite (encSR_pushWRMSem h), (IH tail t1 hr). reflexivity.
  - cbn [symRebuildMR] in h.
    destruct (symRebuildMR rest tail) as [t1 |] eqn:hr; [| discriminate].
    rewrite (encSR_pushRP h), pWord_1_1, (IH tail t1 hr). reflexivity.
  - cbn [symRebuildMR] in h.
    destruct (symRebuildMR rest tail) as [t1 |] eqn:hr; [| discriminate].
    rewrite (encSR_pushRP h), pWord_2_0, (IH tail t1 hr). reflexivity.
Qed.

Fixpoint symPeelLeadingWTR (cur : list SymRTok) (tf0 : SymN) : option (SymN * list SymRTok) :=
  match cur with
  | [] => Some (tf0, [])
  | sr_mid c :: rest =>
    match symDecMidR c rest with
    | None => None
    | Some rest' => Some (symAddConst tf0 2%N, sr_pair 2 0 symZero :: rest')
    end
  | sr_pair 1 1 c :: rest => symPeelLeadingWTR rest (symAdd tf0 (symAddConst c 1%N))
  | _ => Some (tf0, cur)
  end.

Lemma symPeelLeadingWTR_spec (v : V5) :
  forall (cur : list SymRTok) (tf0 tf1 : SymN) (rem : list SymRTok),
    symPeelLeadingWTR cur tf0 = Some (tf1, rem) ->
    evalSymN v tf0 <= evalSymN v tf1 /\
    encSR v cur = (wT ^^ (evalSymN v tf1 - evalSymN v tf0)) *> encSR v rem.
Proof.
  induction cur as [| [[| [| z'']] [| [| o'']] c | c] rest IH]; intros tf0 tf1 rem h;
    try (cbn [symPeelLeadingWTR] in h; inversion h; subst tf1 rem;
         split; [lia | rewrite Nat.sub_diag; reflexivity]).
  - cbn [symPeelLeadingWTR] in h.
    destruct (IH (symAdd tf0 (symAddConst c 1%N)) tf1 rem h) as [hle henc].
    rewrite evalSymN_add, evalSymN_addConst in hle, henc.
    change (#1) with 1 in hle, henc.
    split; [lia |].
    cbn [encSR]. rewrite pWord_1_1, henc, pow_append_pow.
    f_equal. f_equal. lia.
  - cbn [symPeelLeadingWTR] in h.
    destruct (symDecMidR c rest) as [rest' |] eqn:hd; [| discriminate].
    inversion h; subst tf1 rem; clear h.
    rewrite evalSymN_addConst. change (#2) with 2.
    split; [lia |].
    replace (evalSymN v tf0 + 2 - evalSymN v tf0) with 2 by lia.
    rewrite <- (encSR_decMidR hd).
    cbn [encSR]. rewrite evalSymN_zero, pWord_2_0. reflexivity.
Qed.

Inductive SymTowerD01 : Type :=
  | st_d0 (vb : SymN) (rt : list SymRTok)
  | st_d1Empty (tf vb : SymN) (rt : list SymRTok)
  | st_d1Mid (tf cz : SymN) (ms' : list SymMidItem) (vb : SymN) (rt : list SymRTok).

Definition evalTower (v : V5) (tw : SymTowerD01) : TowerD01 :=
  match tw with
  | st_d0 vb rt => td0 (evalSymN v vb) (map (evalRTok v) rt)
  | st_d1Empty tf vb rt => td1Empty (evalSymN v tf) (evalSymN v vb) (map (evalRTok v) rt)
  | st_d1Mid tf cz ms' vb rt =>
    td1Mid (evalSymN v tf) (evalSymN v cz) (map (evalMidItem v) ms') (evalSymN v vb) (map (evalRTok v) rt)
  end.

Fixpoint symScanStageMidR (cur : list SymRTok) : option (list SymMidItem * list SymRTok) :=
  match cur with
  | [] => None
  | sr_mid c :: rest =>
    match symScanStageMidR rest with
    | Some (ms, tail) => Some (smi_mid (symAddConst c 1%N) :: ms, tail)
    | None => None
    end
  | sr_pair 1 1 c :: rest =>
    match symScanStageMidR rest with
    | Some (ms, tail) => Some (smi_t (symAddConst c 1%N) :: ms, tail)
    | None => None
    end
  | sr_pair 1 2 c :: rest =>
    if symIsZero c then Some ([], rest) else None
  | sr_pair 2 0 c :: rest =>
    match symScanStageMidR rest with
    | Some (ms, tail) => Some (smi_z (symAddConst c 1%N) :: ms, tail)
    | None => None
    end
  | _ => None
  end.

Lemma symScanStageMidR_spec (v : V5) :
  forall (cur : list SymRTok) {ms : list SymMidItem} {tail : list SymRTok},
    symScanStageMidR cur = Some (ms, tail) ->
    encSR v cur = encMidR (map (evalMidItem v) ms) ([S0; S1; S1; S1] *> encSR v tail).
Proof.
  induction cur as [| [[| [| [| z''']]] [| [| [| o''']]] c | c] rest IH];
    intros ms tail h; try discriminate; cbn [symScanStageMidR] in h.
  - destruct (symScanStageMidR rest) as [[ms0 tail0] |]; [| discriminate].
    inversion h; subst ms tail; clear h.
    cbn [encSR map encMidR evalMidItem encMidItemR].
    rewrite pWord_1_1, evalSymN_addConst, (IH ms0 tail0 eq_refl). reflexivity.
  - destruct (symIsZero c) eqn:hz; [| discriminate].
    inversion h; subst ms tail; clear h.
    cbn [encSR map encMidR]. rewrite (evalSymN_isZero hz), pWord_1_2, lpow_1. reflexivity.
  - destruct (symScanStageMidR rest) as [[ms0 tail0] |]; [| discriminate].
    inversion h; subst ms tail; clear h.
    cbn [encSR map encMidR evalMidItem encMidItemR].
    rewrite pWord_2_0, evalSymN_addConst, (IH ms0 tail0 eq_refl). reflexivity.
  - destruct (symScanStageMidR rest) as [[ms0 tail0] |]; [| discriminate].
    inversion h; subst ms tail; clear h.
    cbn [encSR map encMidR evalMidItem encMidItemR].
    rewrite evalSymN_addConst, (IH ms0 tail0 eq_refl). reflexivity.
Qed.

Definition symParseTowerD01 (cur : list SymRTok) : option SymTowerD01 :=
  match cur with
  | sr_pair 1 0 c0 :: rest0 =>
    if symIsConst1 c0 then
      match symPeelLeadingWTR rest0 symZero with
      | Some (tf, sr_pair 1 2 c1 :: rest2) =>
        if symIsZero c1 then
          match symPeelLeadingWTR rest2 symZero with
          | Some (vb, rt) => if N.leb 1%N (sk vb) then Some (st_d1Empty tf vb rt) else None
          | None => None
          end
        else None
      | Some (tf, sr_pair 2 0 cz :: rest1') =>
        if N.leb 2%N (sk tf) then
          match symScanStageMidR rest1' with
          | Some (ms', rest2) =>
            match symPeelLeadingWTR rest2 symZero with
            | Some (vb, rt) => if N.leb 1%N (sk vb) then Some (st_d1Mid tf cz ms' vb rt) else None
            | None => None
            end
          | None => None
          end
        else None
      | _ => None
      end
    else None
  | sr_pair 1 2 c0 :: rest0 =>
    if symIsZero c0 then
      match symPeelLeadingWTR rest0 symZero with
      | Some (vb, rt) => if N.leb 1%N (sk vb) then Some (st_d0 vb rt) else None
      | None => None
      end
    else None
  | _ => None
  end.

Fixpoint symScanMAndTowerD01 (cur : list SymRTok) : option (list SymMidItem * SymTowerD01) :=
  match cur with
  | [] => None
  | sr_mid c :: rest =>
    match symScanMAndTowerD01 rest with
    | Some (ms, tw) => Some (smi_mid (symAddConst c 1%N) :: ms, tw)
    | None => None
    end
  | sr_pair 1 0 c :: rest =>
    if symIsConst1 c then
      match symParseTowerD01 (sr_pair 1 0 c :: rest) with
      | Some tw => Some ([], tw)
      | None => None
      end
    else None
  | sr_pair 1 1 c :: rest =>
    match symScanMAndTowerD01 rest with
    | Some (ms, tw) => Some (smi_t (symAddConst c 1%N) :: ms, tw)
    | None => None
    end
  | sr_pair 1 2 c :: rest =>
    if symIsZero c then
      match symParseTowerD01 (sr_pair 1 2 c :: rest) with
      | Some tw => Some ([], tw)
      | None => None
      end
    else None
  | sr_pair 2 0 c :: rest =>
    match symScanMAndTowerD01 rest with
    | Some (ms, tw) => Some (smi_z (symAddConst c 1%N) :: ms, tw)
    | None => None
    end
  | _ => None
  end.

Lemma symParseTowerD01_spec (v : V5) :
  forall {cur : list SymRTok} {tw : SymTowerD01},
    symParseTowerD01 cur = Some tw ->
    TowerWF (evalTower v tw) /\ encSR v cur = encR (buildAdvTowerD01 (evalTower v tw) 0).
Proof.
  intros [| [[| [| z0]] [| [| [| o0]]] c0 | c0] rest0] tw h; try discriminate;
    cbn [symParseTowerD01] in h.
  - destruct (symIsConst1 c0) eqn:hc1; [| discriminate].
    destruct (symPeelLeadingWTR rest0 symZero) as [[tf rest1] |] eqn:hp1; [| discriminate].
    destruct (symPeelLeadingWTR_spec v rest0 symZero tf rest1 hp1) as [_ he1].
    rewrite evalSymN_zero, Nat.sub_0_r in he1.
    destruct rest1 as [| [[| [| [| z1]]] [| [| [| o1]]] c1 | c1] rest1']; try discriminate.
    + destruct (symIsZero c1) eqn:hz1; [| discriminate].
      destruct (symPeelLeadingWTR rest1' symZero) as [[vb rt] |] eqn:hp2; [| discriminate].
      destruct (N.leb 1%N (sk vb)) eqn:hB; [| discriminate].
      inversion h; subst tw; clear h.
      destruct (symPeelLeadingWTR_spec v rest1' symZero vb rt hp2) as [_ he2].
      rewrite evalSymN_zero, Nat.sub_0_r in he2.
      split; [exact I |].
      cbn [encSR evalTower buildAdvTowerD01].
      rewrite (evalSymN_isConst1 hc1), pWord_1_0, he1.
      cbn [encSR]. rewrite (evalSymN_isZero hz1), pWord_1_2, lpow_1, he2.
      rewrite !encR_pushRP, <- encSR_eq_encR_map, pWord_1_0, pWord_1_1, pWord_1_2, lpow_1.
      rewrite Nat.add_0_r, Nat.sub_0_r. reflexivity.
    + destruct (N.leb 2%N (sk tf)) eqn:htf; [| discriminate].
      destruct (symScanStageMidR rest1') as [[ms' rest2] |] eqn:hsm; [| discriminate].
      destruct (symPeelLeadingWTR rest2 symZero) as [[vb rt] |] eqn:hp2; [| discriminate].
      destruct (N.leb 1%N (sk vb)) eqn:hB; [| discriminate].
      inversion h; subst tw; clear h.
      split_andb.
      pose proof (evalSymN_ge_k v tf) as htf_ge.
      destruct (symPeelLeadingWTR_spec v rest2 symZero vb rt hp2) as [_ he2].
      rewrite evalSymN_zero, Nat.sub_0_r in he2.
      pose proof (symScanStageMidR_spec v rest1' hsm) as he'.
      split; [cbn [evalTower TowerWF]; lia |].
      cbn [encSR evalTower buildAdvTowerD01].
      rewrite (evalSymN_isConst1 hc1), pWord_1_0, he1.
      cbn [encSR]. rewrite pWord_2_0, he', he2.
      rewrite !encR_pushRP, !encR_rebuildMR, !encR_pushRP, <- encSR_eq_encR_map,
        pWord_1_0, pWord_1_1, pWord_1_2, lpow_1, !Nat.sub_0_r.
      cbn [encMidR encMidItemR]. reflexivity.
  - destruct (symIsZero c0) eqn:hz0; [| discriminate].
    destruct (symPeelLeadingWTR rest0 symZero) as [[vb rt] |] eqn:hp0; [| discriminate].
    destruct (N.leb 1%N (sk vb)) eqn:hB; [| discriminate].
    inversion h; subst tw; clear h.
    destruct (symPeelLeadingWTR_spec v rest0 symZero vb rt hp0) as [_ he0].
    rewrite evalSymN_zero, Nat.sub_0_r in he0.
    split; [exact I |].
    cbn [encSR evalTower buildAdvTowerD01].
    rewrite (evalSymN_isZero hz0), pWord_1_2, lpow_1, he0.
    rewrite !encR_pushRP, <- encSR_eq_encR_map, pWord_1_2, pWord_1_1, lpow_1, Nat.sub_0_r.
    reflexivity.
Qed.

Lemma symScanMAndTowerD01_spec (v : V5) :
  forall (cur : list SymRTok) {ms : list SymMidItem} {tw : SymTowerD01},
    symScanMAndTowerD01 cur = Some (ms, tw) ->
    TowerWF (evalTower v tw) /\
    encSR v cur = encMidR (map (evalMidItem v) ms) (encR (buildAdvTowerD01 (evalTower v tw) 0)).
Proof.
  induction cur as [| [[| [| [| z''']]] [| [| [| o''']]] c | c] rest IH];
    intros ms tw h; try discriminate; cbn [symScanMAndTowerD01] in h.
  - destruct (symIsConst1 c) eqn:hc1; [| discriminate].
    destruct (symParseTowerD01 (sr_pair 1 0 c :: rest)) as [tw0 |] eqn:hp; [| discriminate].
    inversion h; subst ms tw; clear h.
    exact (symParseTowerD01_spec v hp).
  - destruct (symScanMAndTowerD01 rest) as [[ms0 tw0] |]; [| discriminate].
    inversion h; subst ms tw; clear h.
    destruct (IH ms0 tw0 eq_refl) as [htw he].
    split; [exact htw |].
    cbn [encSR map encMidR evalMidItem encMidItemR].
    rewrite pWord_1_1, evalSymN_addConst, he. reflexivity.
  - destruct (symIsZero c) eqn:hz0; [| discriminate].
    destruct (symParseTowerD01 (sr_pair 1 2 c :: rest)) as [tw0 |] eqn:hp; [| discriminate].
    inversion h; subst ms tw; clear h.
    exact (symParseTowerD01_spec v hp).
  - destruct (symScanMAndTowerD01 rest) as [[ms0 tw0] |]; [| discriminate].
    inversion h; subst ms tw; clear h.
    destruct (IH ms0 tw0 eq_refl) as [htw he].
    split; [exact htw |].
    cbn [encSR map encMidR evalMidItem encMidItemR].
    rewrite pWord_2_0, evalSymN_addConst, he. reflexivity.
  - destruct (symScanMAndTowerD01 rest) as [[ms0 tw0] |]; [| discriminate].
    inversion h; subst ms tw; clear h.
    destruct (IH ms0 tw0 eq_refl) as [htw he].
    split; [exact htw |].
    cbn [encSR map encMidR evalMidItem encMidItemR].
    rewrite evalSymN_addConst, he. reflexivity.
Qed.

Definition symBuildAdvTowerD01 (tw : SymTowerD01) (vn : SymN) : option (list SymRTok) :=
  match tw with
  | st_d0 vb rt =>
    match symSub vb vn with
    | None => None
    | Some d =>
      match symPushRP 1 1 d rt with
      | None => None
      | Some r1 => symPushRP 1 2 symOne r1
      end
    end
  | st_d1Empty tf vb rt =>
    match symSub vb (symScale 2%N vn) with
    | None => None
    | Some d =>
      match symPushRP 1 1 d rt with
      | None => None
      | Some r1 =>
        match symPushRP 1 2 symOne r1 with
        | None => None
        | Some r2 =>
          match symPushRP 1 1 (symAdd tf vn) r2 with
          | None => None
          | Some r3 => symPushRP 1 0 (symConst 2%N) r3
          end
        end
      end
    end
  | st_d1Mid tf cz ms' vb rt =>
    match symSub vb (symScale 2%N vn) with
    | None => None
    | Some dB =>
      match symSub tf vn with
      | None => None
      | Some dtf =>
        match symPushRP 1 1 dB rt with
        | None => None
        | Some r1 =>
          match symPushRP 1 2 symOne r1 with
          | None => None
          | Some r2 =>
            match symPushRP 1 1 (symScale 2%N vn) r2 with
            | None => None
            | Some r3 =>
              match symRebuildMR (smi_z (symAddConst cz 1%N) :: ms') r3 with
              | None => None
              | Some r4 =>
                match symPushRP 1 1 dtf r4 with
                | None => None
                | Some r5 => symPushRP 1 0 (symConst 2%N) r5
                end
              end
            end
          end
        end
      end
    end
  end.

Lemma symBuildAdvTowerD01_spec (v : V5) {tw : SymTowerD01} {vn : SymN}
  {out : list SymRTok} (h : symBuildAdvTowerD01 tw vn = Some out) :
  encSR v out = encR (buildAdvTowerD01 (evalTower v tw) (evalSymN v vn)).
Proof.
  destruct tw as [vb rt | tf vb rt | tf cz ms' vb rt]; cbn [symBuildAdvTowerD01] in h.
  - destruct (symSub vb vn) as [d |] eqn:hs; [| discriminate].
    destruct (symPushRP 1 1 d rt) as [r1 |] eqn:h1; [| discriminate].
    destruct (evalSymN_sub (v := v) hs) as [_ hd].
    cbn [evalTower buildAdvTowerD01].
    rewrite (encSR_pushRP h), (encSR_pushRP h1), !encR_pushRP,
      evalSymN_one, hd, encSR_eq_encR_map.
    reflexivity.
  - destruct (symSub vb (symScale 2%N vn)) as [d |] eqn:hs; [| discriminate].
    destruct (symPushRP 1 1 d rt) as [r1 |] eqn:h1; [| discriminate].
    destruct (symPushRP 1 2 symOne r1) as [r2 |] eqn:h2; [| discriminate].
    destruct (symPushRP 1 1 (symAdd tf vn) r2) as [r3 |] eqn:h3; [| discriminate].
    destruct (evalSymN_sub (v := v) hs) as [_ hd].
    rewrite evalSymN_scale in hd. change (#2) with 2 in hd.
    cbn [evalTower buildAdvTowerD01].
    rewrite (encSR_pushRP h), (encSR_pushRP h3), (encSR_pushRP h2), (encSR_pushRP h1),
      !encR_pushRP, evalSymN_const, evalSymN_add, evalSymN_one, hd, encSR_eq_encR_map.
    reflexivity.
  - destruct (symSub vb (symScale 2%N vn)) as [dB |] eqn:hsB; [| discriminate].
    destruct (symSub tf vn) as [dtf |] eqn:hstf; [| discriminate].
    destruct (symPushRP 1 1 dB rt) as [r1 |] eqn:h1; [| discriminate].
    destruct (symPushRP 1 2 symOne r1) as [r2 |] eqn:h2; [| discriminate].
    destruct (symPushRP 1 1 (symScale 2%N vn) r2) as [r3 |] eqn:h3; [| discriminate].
    destruct (symRebuildMR (smi_z (symAddConst cz 1%N) :: ms') r3) as [r4 |] eqn:h4; [| discriminate].
    destruct (symPushRP 1 1 dtf r4) as [r5 |] eqn:h5; [| discriminate].
    destruct (evalSymN_sub (v := v) hsB) as [_ hdB]. rewrite evalSymN_scale in hdB. change (#2) with 2 in hdB.
    destruct (evalSymN_sub (v := v) hstf) as [_ hdtf].
    cbn [evalTower buildAdvTowerD01].
    rewrite (encSR_pushRP h), (encSR_pushRP h5), (encSR_symRebuildMR v _ _ _ h4),
      (encSR_pushRP h3), (encSR_pushRP h2), (encSR_pushRP h1),
      !encR_pushRP, !encR_rebuildMR, !encR_pushRP,
      evalSymN_const, evalSymN_scale, evalSymN_one, hdB, hdtf, encSR_eq_encR_map.
    cbn [map evalMidItem]. rewrite evalSymN_addConst. reflexivity.
Qed.

Definition symEraEK (tw : SymTowerD01) : option SymN :=
  match tw with
  | st_d0 vb _ =>
    match symDivMod vb 6%N with
    | Some (vk, _) => if N.leb 1%N (sk vk) then Some vk else None
    | None => None
    end
  | st_d1Empty _ vb _ =>
    match symDivMod vb 12%N with
    | Some (vk, _) => if N.leb 1%N (sk vk) then Some vk else None
    | None => None
    end
  | st_d1Mid tf _ _ vb _ =>
    if N.leb 1%N (sk tf) then
      let tf1 := mkSymN (sc0 tf) (sc1 tf) (sc2 tf) (sc3 tf) (sc4 tf) (sk tf - 1)%N in
      match symDivMod tf1 6%N with
      | Some (vk, _) =>
        if andb (N.leb 1%N (sk vk)) (symLe (symScale 12%N vk) vb) then Some vk
        else
          match symDivMod vb 12%N with
          | Some (vk2, _) =>
            if andb (N.leb 1%N (sk vk2)) (symLe (symScale 6%N vk2) tf1) then Some vk2 else None
          | None => None
          end
      | None =>
        match symDivMod vb 12%N with
        | Some (vk2, _) =>
          if andb (N.leb 1%N (sk vk2)) (symLe (symScale 6%N vk2) tf1) then Some vk2 else None
        | None => None
        end
      end
    else None
  end.

Lemma symEraEK_spec (v : V5) {tw : SymTowerD01} {vk : SymN}
  (h : symEraEK tw = Some vk) :
  1 <= evalSymN v vk /\ 6 * evalSymN v vk <= maxReflD01 (evalTower v tw).
Proof.
  destruct tw as [vb rt | tf vb rt | tf cz ms' vb rt]; cbn [symEraEK] in h.
  - destruct (symDivMod vb 6%N) as [[vk0 rem] |] eqn:hdm; [| discriminate].
    destruct (N.leb 1%N (sk vk0)) eqn:hK; [| discriminate].
    inversion h; subst vk; clear h. split_andb.
    destruct (evalSymN_divMod (v := v) hdm) as [_ [_ hdiv]].
    pose proof (evalSymN_ge_k v vk0) as hge.
    change (#6) with 6 in hdiv. cbn [evalTower maxReflD01]. lia.
  - destruct (symDivMod vb 12%N) as [[vk0 rem] |] eqn:hdm; [| discriminate].
    destruct (N.leb 1%N (sk vk0)) eqn:hK; [| discriminate].
    inversion h; subst vk; clear h. split_andb.
    destruct (evalSymN_divMod (v := v) hdm) as [_ [_ hdiv]].
    pose proof (evalSymN_ge_k v vk0) as hge.
    change (#12) with 12 in hdiv. cbn [evalTower maxReflD01]. lia.
  - destruct (N.leb 1%N (sk tf)) eqn:htf; [| discriminate].
    set (tf1 := mkSymN (sc0 tf) (sc1 tf) (sc2 tf) (sc3 tf) (sc4 tf) (sk tf - 1)%N) in *.
    assert (htf1 : evalSymN v tf1 = evalSymN v tf - 1).
    { split_andb. unfold tf1, evalSymN. cbn [sc0 sc1 sc2 sc3 sc4 sk]. lia. }
    destruct (symDivMod tf1 6%N) as [[vk1 rem1] |] eqn:hdm1.
    + destruct (andb (N.leb 1%N (sk vk1)) (symLe (symScale 12%N vk1) vb)) eqn:hc1.
      * inversion h; subst vk; clear h.
        apply Bool.andb_true_iff in hc1; destruct hc1 as [hk1 hle1].
        split_andb.
        destruct (evalSymN_divMod (v := v) hdm1) as [_ [_ hdiv1]].
        pose proof (evalSymN_le (v := v) hle1) as hle.
        rewrite evalSymN_scale in hle. change (#12) with 12 in hle.
        change (#6) with 6 in hdiv1.
        pose proof (evalSymN_ge_k v vk1) as hge.
        cbn [evalTower maxReflD01]. lia.
      * destruct (symDivMod vb 12%N) as [[vk2 rem2] |] eqn:hdm2; [| discriminate].
        destruct (andb (N.leb 1%N (sk vk2)) (symLe (symScale 6%N vk2) tf1)) eqn:hc2; [| discriminate].
        inversion h; subst vk; clear h.
        apply Bool.andb_true_iff in hc2; destruct hc2 as [hk2 hle2].
        split_andb.
        destruct (evalSymN_divMod (v := v) hdm2) as [_ [_ hdiv2]].
        pose proof (evalSymN_le (v := v) hle2) as hle.
        rewrite evalSymN_scale, htf1 in hle. change (#6) with 6 in hle.
        change (#12) with 12 in hdiv2.
        pose proof (evalSymN_ge_k v vk2) as hge.
        cbn [evalTower maxReflD01]. lia.
    + destruct (symDivMod vb 12%N) as [[vk2 rem2] |] eqn:hdm2; [| discriminate].
      destruct (andb (N.leb 1%N (sk vk2)) (symLe (symScale 6%N vk2) tf1)) eqn:hc2; [| discriminate].
      inversion h; subst vk; clear h.
      apply Bool.andb_true_iff in hc2; destruct hc2 as [hk2 hle2].
      split_andb.
      destruct (evalSymN_divMod (v := v) hdm2) as [_ [_ hdiv2]].
      pose proof (evalSymN_le (v := v) hle2) as hle.
      rewrite evalSymN_scale, htf1 in hle. change (#6) with 6 in hle.
      change (#12) with 12 in hdiv2.
      pose proof (evalSymN_ge_k v vk2) as hge.
      cbn [evalTower maxReflD01]. lia.
Qed.

Definition symTryEraED01 (vl : list SymLTok) (vr : list SymRTok) : option SymState :=
  match vl, vr with
  | [sl_pair 0 0 c0; sl_pair 1 1 c1], sr_pair 1 1 cr0 :: sr_pair 2 0 cz0 :: rRest0 =>
    if andb (andb (symIsZero c0) (symIsZero c1)) (symIsZero cr0) then
      match symDecPairR 2 0 cz0 rRest0 with
      | None => None
      | Some cur =>
        match symScanMAndTowerD01 cur with
        | Some (ms, tw) =>
          match symEraEK tw with
          | Some vk =>
            let k6 := symScale 6%N vk in
            match symBuildAdvTowerD01 tw k6 with
            | None => None
            | Some tw' =>
              match symPushRP 1 1 k6 tw' with
              | None => None
              | Some out0 =>
                match symRebuildMR ms out0 with
                | None => None
                | Some out1 =>
                  match symPushWRMSem vk out1 with
                  | None => None
                  | Some out2 =>
                    match symPushRP 2 0 symOne out2 with
                    | None => None
                    | Some out3 =>
                      match symPushRP 1 1 symOne out3 with
                      | None => None
                      | Some out => Some (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero], out)
                      end
                    end
                  end
                end
              end
            end
          | None => None
          end
        | None => None
        end
      end
    else None
  | _, _ => None
  end.

Lemma symTryEraED01_sound (v : V5) {vl : list SymLTok} {vr : list SymRTok} {s' : SymState}
  (h : symTryEraED01 vl vr = Some s') :
  evalSym v (mE, vl, vr) -->+ evalSym v s'.
Proof.
  destruct vl as [| [[| zl0] [| ol0] c0 | c0] [| [[| [| zl1]] [| [| ol1]] c1 | c1] [| ? ?]]];
    try discriminate.
  destruct vr as [| [[| [| zr0]] [| [| or0]] cr0 | cr0] [| [[| [| [| zr1]]] [| or1] cz0 | cz0] rRest0]];
    try discriminate.
  cbn [symTryEraED01] in h.
  destruct (andb (andb (symIsZero c0) (symIsZero c1)) (symIsZero cr0)) eqn:hz; [| discriminate].
  apply Bool.andb_true_iff in hz; destruct hz as [hz01 hzr0].
  apply Bool.andb_true_iff in hz01; destruct hz01 as [hz0 hz1].
  destruct (symDecPairR 2 0 cz0 rRest0) as [cur |] eqn:hd; [| discriminate].
  destruct (symScanMAndTowerD01 cur) as [[ms tw] |] eqn:hs; [| discriminate].
  destruct (symEraEK tw) as [vk |] eqn:hK; [| discriminate].
  destruct (symBuildAdvTowerD01 tw (symScale 6%N vk)) as [tw' |] eqn:hb; [| discriminate].
  destruct (symPushRP 1 1 (symScale 6%N vk) tw') as [out0 |] eqn:ho0; [| discriminate].
  destruct (symRebuildMR ms out0) as [out1 |] eqn:ho1; [| discriminate].
  destruct (symPushWRMSem vk out1) as [out2 |] eqn:ho2; [| discriminate].
  destruct (symPushRP 2 0 symOne out2) as [out3 |] eqn:ho3; [| discriminate].
  destruct (symPushRP 1 1 symOne out3) as [out |] eqn:ho4; [| discriminate].
  inversion h; subst s'; clear h.
  destruct (symScanMAndTowerD01_spec v cur hs) as [htw henc].
  destruct (symEraEK_spec v hK) as [hK1 hK6].
  eapply progress_eq_both;
    [exact (era_E_loop_plus (map (evalMidItem v) ms) (evalTower v tw) htw (evalSymN v vk) hK1 hK6) | |].
  - unfold eraECfg. cbn [evalSym].
    assert (hL : encSL v [sl_pair 0 0 c0; sl_pair 1 1 c1] = [S1; S0; S1; S1] *> 0inf).
    { cbn [encSL]. rewrite (evalSymN_isZero hz0), (evalSymN_isZero hz1), pWord_0_0, pWord_1_1, !lpow_1.
      reflexivity. }
    assert (hR : encSR v (sr_pair 1 1 cr0 :: sr_pair 2 0 cz0 :: rRest0) = wT *> wZ *> encSR v cur).
    { change (encSR v (sr_pair 1 1 cr0 :: sr_pair 2 0 cz0 :: rRest0))
        with ((pWord 1 1 ^^ (evalSymN v cr0 + 1)) *> encSR v (sr_pair 2 0 cz0 :: rRest0)).
      rewrite <- (@encSR_decPairR v 2 0 cz0 rRest0 cur hd),
        (evalSymN_isZero hzr0), pWord_1_1, pWord_2_0, lpow_1.
      reflexivity. }
    rewrite hL, hR, henc. reflexivity.
  - unfold eraECfg. cbn [evalSym].
    assert (hL : encSL v [sl_pair 0 0 symZero; sl_pair 1 1 symZero] = [S1; S0; S1; S1] *> 0inf)
      by reflexivity.
    rewrite hL, (encSR_pushRP ho4), (encSR_pushRP ho3), (encSR_pushWRMSem ho2),
      (encSR_symRebuildMR v _ _ _ ho1), (encSR_pushRP ho0), (symBuildAdvTowerD01_spec v hb),
      evalSymN_one, evalSymN_scale, pWord_1_1, pWord_2_0, !lpow_1.
    reflexivity.
Qed.

Definition symTryEraL11D0Aux (remMidL : SymN) (ms : list SymMidItem) (tw : SymTowerD01) (vk : SymN)
  : option SymState :=
  match symPushWLMSem remMidL [sl_pair 1 1 symZero; sl_pair 1 0 symZero] with
  | None => None
  | Some luRem =>
    match symPushLP 1 0 symOne luRem with
    | None => None
    | Some vl_out =>
      let k18 := symScale 18%N vk in
      match symBuildAdvTowerD01 tw k18 with
      | None => None
      | Some tw' =>
        match symPushRP 1 1 k18 tw' with
        | None => None
        | Some out0 =>
          match symRebuildMR ms out0 with
          | None => None
          | Some out1 =>
            match symPushRP 1 1 (symScale 36%N vk) out1 with
            | None => None
            | Some out2 =>
              match symPush1011R out2 with
              | None => None
              | Some vr_out => Some (mA, vl_out, vr_out)
              end
            end
          end
        end
      end
    end
  end.

Definition symTryEraL11D0 (vl : list SymLTok) (vr : list SymRTok) : option SymState :=
  match vl with
  | [sl_pair 1 0 c0; sl_mid cm; sl_pair 1 1 c1; sl_pair 1 0 c2] =>
    if andb (andb (symIsZero c0) (symIsZero c1)) (symIsZero c2) then
      let midL := symAddConst cm 1%N in
      if N.leb 11%N (sk midL) then
        match symPeel1011R vr with
        | Some rt0 =>
          match symScanMAndTowerD01 rt0 with
          | Some (ms, st_d0 vb rt) =>
            match symDivMod midL 11%N with
            | Some (vk, rem) =>
              if andb (N.leb 1%N (sk vk)) (symLe (symScale 18%N vk) vb) then
                symTryEraL11D0Aux (symConst rem) ms (st_d0 vb rt) vk
              else
                match symDivMod vb 18%N with
                | Some (vk2, _) =>
                  if N.leb 1%N (sk vk2) then
                    match symSub midL (symScale 11%N vk2) with
                    | Some remM => symTryEraL11D0Aux remM ms (st_d0 vb rt) vk2
                    | None => None
                    end
                  else None
                | None => None
                end
            | None =>
              match symDivMod vb 18%N with
              | Some (vk2, _) =>
                if N.leb 1%N (sk vk2) then
                  match symSub midL (symScale 11%N vk2) with
                  | Some remM => symTryEraL11D0Aux remM ms (st_d0 vb rt) vk2
                  | None => None
                  end
                else None
              | None => None
              end
            end
          | _ => None
          end
        | None => None
        end
      else None
    else None
  | _ => None
  end.

Lemma symTryEraL11D0Aux_sound (v : V5)
  {cm remMidL vb vk : SymN} {ms : list SymMidItem} {rt vr : list SymRTok} {s' : SymState}
  (hR : encSR v vr = [S1; S0; S1; S1] *>
    encMidR (map (evalMidItem v) ms) (encR (buildAdvTowerD01 (td0 (evalSymN v vb) (map (evalRTok v) rt)) 0)))
  (hK : 1 <= evalSymN v vk)
  (hmid : evalSymN v cm + 1 = evalSymN v remMidL + 11 * evalSymN v vk)
  (hB : 18 * evalSymN v vk <= evalSymN v vb)
  (h : symTryEraL11D0Aux remMidL ms (st_d0 vb rt) vk = Some s') :
  cfgA ([S0; S1] *> (wLM ^^ (evalSymN v cm + 1)) *> tailL0) (encSR v vr) -->+ evalSym v s'.
Proof.
  unfold symTryEraL11D0Aux in h.
  destruct (symPushWLMSem remMidL [sl_pair 1 1 symZero; sl_pair 1 0 symZero]) as [luRem |] eqn:h1; [| discriminate].
  destruct (symPushLP 1 0 symOne luRem) as [vl_out |] eqn:h2; [| discriminate].
  destruct (symBuildAdvTowerD01 (st_d0 vb rt) (symScale 18%N vk)) as [tw' |] eqn:h3; [| discriminate].
  destruct (symPushRP 1 1 (symScale 18%N vk) tw') as [out0 |] eqn:h4; [| discriminate].
  destruct (symRebuildMR ms out0) as [out1 |] eqn:h5; [| discriminate].
  destruct (symPushRP 1 1 (symScale 36%N vk) out1) as [out2 |] eqn:h6; [| discriminate].
  destruct (symPush1011R out2) as [vr_out |] eqn:h7; [| discriminate].
  inversion h; subst s'; clear h.
  eapply progress_eq_both;
    [exact (era_L11_d0_loop_plus (evalSymN v remMidL) (map (evalMidItem v) ms)
       (evalSymN v vb) (encSR v rt) (evalSymN v vk) hK hB) | |].
  - unfold eraL11Cfg.
    replace (evalSymN v remMidL + 11 * (evalSymN v vk - 0)) with (evalSymN v cm + 1) by lia.
    rewrite hR. cbn [buildAdvTowerD01].
    rewrite !encR_pushRP, <- encSR_eq_encR_map, pWord_1_2, pWord_1_1, lpow_1,
      !Nat.sub_0_r, !Nat.mul_0_r, !lpow_0, !Str_app_nil.
    reflexivity.
  - unfold eraL11Cfg. cbn [evalSym].
    assert (htail : encSL v [sl_pair 1 1 symZero; sl_pair 1 0 symZero] = tailL0) by reflexivity.
    rewrite (encSL_pushLP h2), (encSL_pushWLMSem h1), htail, evalSymN_one, pWord_1_0, lpow_1,
      (encSR_push1011R h7), (encSR_pushRP h6), (encSR_symRebuildMR v _ _ _ h5),
      (encSR_pushRP h4), (symBuildAdvTowerD01_spec v h3).
    cbn [evalTower buildAdvTowerD01].
    rewrite !encR_pushRP, <- encSR_eq_encR_map, !evalSymN_scale,
      pWord_1_1, pWord_1_2, lpow_1, !Nat.sub_diag, !Nat.mul_0_r, !Nat.add_0_r.
    reflexivity.
Qed.

Lemma symTryEraL11D0_sound (v : V5) {vl : list SymLTok} {vr : list SymRTok} {s' : SymState}
  (h : symTryEraL11D0 vl vr = Some s') :
  evalSym v (mA, vl, vr) -->+ evalSym v s'.
Proof.
  unfold symTryEraL11D0 in h.
  destruct vl as [| [[| [| z0]] [| o0] c0 | c0]
    [| [z1 o1 cm | cm]
    [| [[| [| z2]] [| [| o2]] c1 | c1]
    [| [[| [| z3]] [| o3] c2 | c2] [| ? ?]]]]]; try discriminate.
  destruct (andb (andb (symIsZero c0) (symIsZero c1)) (symIsZero c2)) eqn:hz; [| discriminate].
  apply Bool.andb_true_iff in hz; destruct hz as [hz01 hz2].
  apply Bool.andb_true_iff in hz01; destruct hz01 as [hz0 hz1].
  destruct (N.leb 11%N (sk (symAddConst cm 1%N))) eqn:h11; [| discriminate].
  destruct (symPeel1011R vr) as [rt0 |] eqn:hp; [| discriminate].
  destruct (symScanMAndTowerD01 rt0) as [[ms tw] |] eqn:hs; [| discriminate].
  destruct tw as [vb rt | ? ? ? | ? ? ? ? ?]; [| discriminate | discriminate].
  destruct (symScanMAndTowerD01_spec v rt0 hs) as [_ henc].
  cbn [evalTower] in henc.
  assert (hR : encSR v vr = [S1; S0; S1; S1] *>
    encMidR (map (evalMidItem v) ms) (encR (buildAdvTowerD01 (td0 (evalSymN v vb) (map (evalRTok v) rt)) 0))).
  { rewrite (symPeel1011R_spec hp), henc. reflexivity. }
  assert (hL : evalSym v (mA, [sl_pair 1 0 c0; sl_mid cm; sl_pair 1 1 c1; sl_pair 1 0 c2], vr) =
    cfgA ([S0; S1] *> (wLM ^^ (evalSymN v cm + 1)) *> tailL0) (encSR v vr)).
  { cbn [evalSym encSL].
    rewrite (evalSymN_isZero hz0), (evalSymN_isZero hz1), (evalSymN_isZero hz2),
      pWord_1_0, pWord_1_1, !lpow_1.
    reflexivity. }
  rewrite hL.
  destruct (symDivMod (symAddConst cm 1%N) 11%N) as [[vk rem] |] eqn:hdm1.
  - destruct (andb (N.leb 1%N (sk vk)) (symLe (symScale 18%N vk) vb)) eqn:hc.
    + apply Bool.andb_true_iff in hc; destruct hc as [hk1 hle1].
      split_andb.
      destruct (evalSymN_divMod (v := v) hdm1) as [_ [_ hdivM]].
      rewrite evalSymN_addConst in hdivM. change (#1) with 1 in hdivM. change (#11) with 11 in hdivM.
      pose proof (evalSymN_le (v := v) hle1) as hleB.
      rewrite evalSymN_scale in hleB. change (#18) with 18 in hleB.
      pose proof (evalSymN_ge_k v vk) as hge.
      eapply symTryEraL11D0Aux_sound with (cm := cm); [exact hR | .. | exact h];
        try rewrite evalSymN_const; lia.
    + destruct (symDivMod vb 18%N) as [[vk2 r2] |] eqn:hdm2; [| discriminate].
      destruct (N.leb 1%N (sk vk2)) eqn:hk2; [| discriminate].
      destruct (symSub (symAddConst cm 1%N) (symScale 11%N vk2)) as [remM |] eqn:hsub; [| discriminate].
      split_andb.
      destruct (evalSymN_divMod (v := v) hdm2) as [_ [_ hdivB]].
      destruct (evalSymN_sub (v := v) hsub) as [hleM hrem].
      rewrite evalSymN_addConst, evalSymN_scale in hleM, hrem.
      change (#1) with 1 in hleM, hrem. change (#11) with 11 in hleM, hrem.
      change (#18) with 18 in hdivB.
      pose proof (evalSymN_ge_k v vk2) as hge.
      eapply symTryEraL11D0Aux_sound with (cm := cm); [exact hR | .. | exact h]; lia.
  - destruct (symDivMod vb 18%N) as [[vk2 r2] |] eqn:hdm2; [| discriminate].
    destruct (N.leb 1%N (sk vk2)) eqn:hk2; [| discriminate].
    destruct (symSub (symAddConst cm 1%N) (symScale 11%N vk2)) as [remM |] eqn:hsub; [| discriminate].
    split_andb.
    destruct (evalSymN_divMod (v := v) hdm2) as [_ [_ hdivB]].
    destruct (evalSymN_sub (v := v) hsub) as [hleM hrem].
    rewrite evalSymN_addConst, evalSymN_scale in hleM, hrem.
    change (#1) with 1 in hleM, hrem. change (#11) with 11 in hleM, hrem.
    change (#18) with 18 in hdivB.
    pose proof (evalSymN_ge_k v vk2) as hge.
    eapply symTryEraL11D0Aux_sound with (cm := cm); [exact hR | .. | exact h]; lia.
Qed.

(* ========================================================================== *)
(* `symTryAR10101WZ` (`A_R` Sweep over `wZ^k`)                                *)
(* ========================================================================== *)

Definition symTryAR10101WZ (vl : list SymLTok) (vr : list SymRTok) : option SymState :=
  match vr with
  | sr_pair 0 0 c0 :: sr_pair 1 0 c1 :: sr_pair 1 1 c2 :: sr_pair 2 0 cz :: rRest =>
    if andb (andb (symIsZero c0) (symIsConst1 c1)) (symIsZero c2) then
      match symPushLP 1 1 (symAddConst cz 1%N) vl with
      | None => None
      | Some vl' => Some (mA, vl', sr_pair 0 0 symZero :: sr_pair 1 0 symOne :: sr_pair 1 1 symZero :: rRest)
      end
    else None
  | _ => None
  end.

Lemma symTryAR10101WZ_sound (v : V5) {vl : list SymLTok} {vr : list SymRTok}
  {s' : SymState} (h : symTryAR10101WZ vl vr = Some s') :
  evalSym v (mA, vl, vr) -->+ evalSym v s'.
Proof.
  unfold symTryAR10101WZ in h.
  destruct vr as [| [[| z0] [| o0] c0 | c0]
    [| [[| [| z1]] [| o1] c1 | c1]
    [| [[| [| z2]] [| [| o2]] c2 | c2]
    [| [[| [| [| z3]]] [| o3] cz | cz] rRest]]]]; try discriminate.
  destruct (andb (andb (symIsZero c0) (symIsConst1 c1)) (symIsZero c2)) eqn:hc; [| discriminate].
  apply Bool.andb_true_iff in hc; destruct hc as [hc01 h2].
  apply Bool.andb_true_iff in hc01; destruct hc01 as [h0 h1].
  destruct (symPushLP 1 1 (symAddConst cz 1%N) vl) as [vl' |] eqn:hp; [| discriminate].
  inversion h; subst s'; clear h.
  cbn [evalSym].
  rewrite (encSL_pushLP hp), evalSymN_addConst, pWord_1_1.
  change (#1) with 1.
  assert (hrIn : encSR v (sr_pair 0 0 c0 :: sr_pair 1 0 c1 :: sr_pair 1 1 c2 :: sr_pair 2 0 cz :: rRest) =
    [S1; S0; S1; S0; S1; S0; S1; S1] *> (wZ ^^ (evalSymN v cz + 1)) *> encSR v rRest).
  { cbn [encSR].
    rewrite (evalSymN_isZero h0), (evalSymN_isConst1 h1), (evalSymN_isZero h2),
      pWord_0_0, pWord_1_0, pWord_1_1, pWord_2_0.
    reflexivity. }
  assert (hrOut : encSR v (sr_pair 0 0 symZero :: sr_pair 1 0 symOne :: sr_pair 1 1 symZero :: rRest) =
    [S1; S0; S1; S0; S1; S0; S1; S1] *> encSR v rRest).
  { cbn [encSR]. rewrite evalSymN_zero, evalSymN_one, pWord_0_0, pWord_1_0, pWord_1_1. reflexivity. }
  rewrite hrIn, hrOut.
  exact (step_ar_10101_wZ_pow_plus (evalSymN v cz) (encSL v vl) (encSR v rRest)).
Qed.

(* ========================================================================== *)
(* Top-Level Symbolic Dispatcher (`symStep`) & Binary-Doubling Runner         *)
(* ========================================================================== *)

Definition symStep (s : SymState) : option SymState :=
  let '(m, vl, vr) := s in
  match m with
  | mA =>
    match symTryEraL11D0 vl vr with
    | Some res => Some res
    | None =>
      match symTryAR10101WZ vl vr with
      | Some res => Some res
      | None => symStepTrans (mA, vl, vr)
      end
    end
  | mD =>
    match symTryDL1WZ vl vr with
    | Some res => Some res
    | None => symStepTrans (mD, vl, vr)
    end
  | mE =>
    match symTryEraED01 vl vr with
    | Some res => Some res
    | None =>
      match symTryEraConv vl vr with
      | Some res => Some res
      | None =>
        match symTryEL1101 vl vr with
        | Some res => Some res
        | None => symStepTrans (mE, vl, vr)
        end
      end
    end
  | mHalt => symStepTrans (mHalt, vl, vr)
  end.

Lemma symStep_sound (v : V5) {s s' : SymState}
  (h : symStep s = Some s') :
  evalSym v s -->+ evalSym v s'.
Proof.
  destruct s as [[m vl] vr]; destruct m; cbn [symStep] in h.
  - destruct (symTryEraL11D0 vl vr) as [res1 |] eqn:r1.
    + inversion h; subst s'; exact (symTryEraL11D0_sound v r1).
    + destruct (symTryAR10101WZ vl vr) as [res2 |] eqn:r2.
      * inversion h; subst s'; exact (symTryAR10101WZ_sound v r2).
      * exact (symStepTrans_sound v h).
  - destruct (symTryDL1WZ vl vr) as [res1 |] eqn:r1.
    + inversion h; subst s'; exact (symTryDL1WZ_sound v r1).
    + exact (symStepTrans_sound v h).
  - destruct (symTryEraED01 vl vr) as [res1 |] eqn:r1.
    + inversion h; subst s'; exact (symTryEraED01_sound v r1).
    + destruct (symTryEraConv vl vr) as [res2 |] eqn:r2.
      * inversion h; subst s'; exact (symTryEraConv_sound v r2).
      * destruct (symTryEL1101 vl vr) as [res3 |] eqn:r3.
        { inversion h; subst s'; exact (symTryEL1101_sound v r3). }
        { exact (symStepTrans_sound v h). }
  - exact (symStepTrans_sound v h).
Qed.

Fixpoint symIterPow2 (k : nat) (s : SymState) : option SymState :=
  match k with
  | 0 => symStep s
  | S k' =>
    match symIterPow2 k' s with
    | None => None
    | Some s1 => symIterPow2 k' s1
    end
  end.

Lemma symIterPow2_sound (v : V5) :
  forall (k : nat) {s s' : SymState},
    symIterPow2 k s = Some s' ->
    evalSym v s -->+ evalSym v s'.
Proof.
  induction k as [| k' IH]; intros s s' h.
  - exact (symStep_sound v h).
  - cbn [symIterPow2] in h.
    destruct (symIterPow2 k' s) as [s1 |] eqn:h1; [| discriminate].
    exact (ptrans (IH s s1 h1) (IH s1 s' h)).
Qed.

Fixpoint symRunBits (ks : list nat) (s : SymState) : option SymState :=
  match ks with
  | [] => Some s
  | k :: rest =>
    match symIterPow2 k s with
    | None => None
    | Some s1 => symRunBits rest s1
    end
  end.

Lemma symRunBits_sound_star (v : V5) :
  forall (ks : list nat) {s s' : SymState},
    symRunBits ks s = Some s' ->
    evalSym v s -->* evalSym v s'.
Proof.
  induction ks as [| k rest IH]; intros s s' h; cbn [symRunBits] in h.
  - inversion h; subst s'; apply evstep_refl.
  - destruct (symIterPow2 k s) as [s1 |] eqn:h1; [| discriminate].
    exact (etrans (pev (symIterPow2_sound v k h1)) (IH s1 s' h)).
Qed.

Lemma symRunBits_sound_plus (v : V5) {k : nat} {ks : list nat}
  {s s' : SymState} (h : symRunBits (k :: ks) s = Some s') :
  evalSym v s -->+ evalSym v s'.
Proof.
  cbn [symRunBits] in h.
  destruct (symIterPow2 k s) as [s1 |] eqn:h1; [| discriminate].
  exact (ps_trans (symIterPow2_sound v k h1) (symRunBits_sound_star v ks h)).
Qed.

(* ========================================================================== *)
(* Part 3: Canonical Configurations, Parametric Invariants, & Closure         *)
(* ========================================================================== *)

Ltac clear_steps :=
  repeat match goal with
  | H : _ -->+ _ |- _ => clear H
  | H : _ -->* _ |- _ => clear H
  end.

Ltac clear_hyps_and_bodies :=
  repeat match goal with
  | H : ?T |- _ =>
    lazymatch type of T with
    | Prop => clear H
    end
  end;
  repeat match goal with
  | x := _ |- _ => clearbody x
  end.

Ltac unfold_locals :=
  repeat match goal with
  | x := _ |- _ => subst x
  end.

Ltac fast_lia :=
  try solve [clear_hyps_and_bodies; zify; cbn [Z.of_N Pos.to_nat]; xlia zchecker];
  clear_steps; unfold_locals; cbv zeta in *;
  zify; cbn [Z.of_N Pos.to_nat] in *; xlia zchecker.

Ltac solve_eval_eq :=
  unfold evalSymN, symZero, symOne, symConst, v5;
  cbn [v0 v1 v2 v3 v4 sc0 sc1 sc2 sc3 sc4 sk];
  try reflexivity;
  fast_lia.

Definition symTail (i : nat) : list SymLTok :=
  match i with
  | 0 => [sl_pair 1 1 symZero; sl_pair 1 0 symZero]
  | 1 => [sl_pair 1 1 symZero; sl_pair 2 0 symZero]
  | 2 => [sl_pair 1 1 symZero; sl_pair 1 0 symZero; sl_pair 2 0 symZero; sl_pair 1 0 symZero]
  | 3 => [sl_pair 1 1 symZero; sl_pair 2 0 symZero; sl_pair 3 0 symZero; sl_pair 1 0 symZero]
  | 4 => [sl_pair 1 1 symZero; sl_pair 1 0 (symConst 2%N); sl_pair 2 0 symZero; sl_pair 1 0 symZero]
  | _ => [sl_pair 1 1 symZero; sl_pair 2 0 symZero; sl_pair 1 0 symOne]
  end.

Definition encTail (i : nat) : side := encSL (v5 0 0 0 0 0) (symTail i).

Lemma encSL_symTail (v : V5) (i : nat) : encSL v (symTail i) = encTail i.
Proof.
  destruct i as [| [| [| [| [| i']]]]];
    unfold symTail, encTail; cbn [encSL];
    rewrite !evalSymN_zero, ?evalSymN_one, ?evalSymN_const;
    reflexivity.
Qed.

Lemma wRM_eq_wT2_wZ (s : side) : wRM *> s = (wT ^^ 2) *> (wZ *> s).
Proof. reflexivity. Qed.

Lemma wT_pow_wRM_eq (a : nat) (s : side) :
  (wT ^^ a) *> (wRM *> s) = (wT ^^ (a + 2)) *> (wZ *> s).
Proof. rewrite wRM_eq_wT2_wZ, pow_append_pow. reflexivity. Qed.

Lemma wZ_add_pow (a b : nat) (s : side) :
  (wZ ^^ a) *> ((wZ ^^ b) *> s) = (wZ ^^ (a + b)) *> s.
Proof. exact (pow_append_pow wZ a b s). Qed.

Lemma wZ_cons_pow (a : nat) (s : side) :
  wZ *> ((wZ ^^ a) *> s) = (wZ ^^ (a + 1)) *> s.
Proof. rewrite (Nat.add_comm a 1), <- pow_append_pow, lpow_1. reflexivity. Qed.

Lemma wT_cons_pow (a : nat) (s : side) :
  wT *> ((wT ^^ a) *> s) = (wT ^^ (a + 1)) *> s.
Proof. rewrite (Nat.add_comm a 1), <- pow_append_pow, lpow_1. reflexivity. Qed.

Lemma list_1011_eq (s : side) :
  [S1; S0; S1; S1] *> s = [S1] *> (wT *> s).
Proof. reflexivity. Qed.

Lemma reachesPlus_eq_both {a a' b b' : Q * tape}
  (h : a -->+ b) (ha : a = a') (hb : b = b') : a' -->+ b'.
Proof. subst a' b'. exact h. Qed.

(* ========================================================================== *)
(* Canonical Configurations                                                   *)
(* ========================================================================== *)

Definition mCfg (m z c k : nat) : Q * tape :=
  cfgA ([S0; S1] *> ((wLM ^^ m) *> tailL0))
    ([S1] *> ((wT ^^ (6 * k + 7)) *> ((wZ ^^ z) *> ((wT ^^ (3 * k + 1)) *>
      ([S0; S1; S1; S1] *> ((wT ^^ c) *> ([S0; S1] *> 0inf))))))).

Definition postL11Cfg (r u z c : nat) : Q * tape :=
  cfgA ([S0; S1] *> ((wLM ^^ r) *> tailL0))
    ([S1] *> ((wT ^^ (6 * u + #115)) *> ((wZ ^^ z) *> ((wT ^^ (3 * u + #55)) *>
      ([S0; S1; S1; S1] *> ((wT ^^ c) *> ([S0; S1] *> 0inf))))))).

Definition convMLoopCfg (i pA pM pZ pC : nat) : Q * tape :=
  cfgE ([S1] *> (wT *> ((wZ ^^ (pA + 1)) *> ((wLM ^^ pM) *> encTail i))))
    (wT *> ((wZ ^^ pZ) *> ((wT ^^ pC) *> ([S0; S1] *> 0inf)))).

Definition convSimpleCfg (i pA pM R0 : nat) : Q * tape :=
  cfgE ([S1] *> ((wZ ^^ pA) *> ((wLM ^^ pM) *> encTail i)))
    ((wT ^^ R0) *> ([S0; S1] *> 0inf)).

Definition convEntryCfg (i pB z pA pM R0 : nat) : Q * tape :=
  cfgE ([S1] *> ((wZ ^^ pB) *> ((wT ^^ (z - 1)) *> (wLM *> ((wZ ^^ pA) *> ((wLM ^^ pM) *> encTail i))))))
    ((wT ^^ R0) *> ([S0; S1] *> 0inf)).

Definition eMidExtra0Cfg (pM pA d pC : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> (wZ *> ((wRM ^^ pM) *> ((wT ^^ pA) *> (wRM *> (wZ *> ((wT ^^ d) *>
      ([S0; S1; S1; S1] *> ((wT ^^ pC) *> ([S0; S1] *> 0inf)))))))))).

Definition eMidExtra12Cfg (pM pA z Bm d pC : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> (wZ *> ((wRM ^^ pM) *> ((wT ^^ pA) *> (wRM *> ((wZ ^^ (z - 1)) *>
      ((wT ^^ Bm) *> (wRM *> (wZ *> ((wT ^^ d) *>
        ([S0; S1; S1; S1] *> ((wT ^^ pC) *> ([S0; S1] *> 0inf))))))))))))).

Definition eMid0Cfg (pM pA pB pC : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> (wZ *> ((wRM ^^ pM) *> ((wT ^^ pA) *> (([S0; S1] ^^ 2) *> ((wT ^^ pB) *>
      ([S0; S1; S1; S1] *> ((wT ^^ pC) *> ([S0; S1] *> 0inf))))))))).

Definition eMid12Cfg (pM pA z pB pC : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> (wZ *> ((wRM ^^ pM) *> ((wT ^^ pA) *> (wRM *> ((wZ ^^ (z - 1)) *>
      ((wT ^^ 2) *> (([S0; S1] ^^ 2) *> ((wT ^^ pB) *>
        ([S0; S1; S1; S1] *> ((wT ^^ pC) *> ([S0; S1] *> 0inf)))))))))))).

Definition eCleanCfg (pA z pB pC : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> (wZ *> ((wT ^^ pA) *> (wRM *> ((wZ ^^ (z - 1)) *> ((wT ^^ pB) *>
      ([S0; S1; S1; S1] *> ((wT ^^ pC) *> ([S0; S1] *> 0inf))))))))).

Definition e0111Cfg (pA z pB pC : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> (wZ *> ((wT ^^ 8) *> ([S0; S1; S1; S1] *> ((wT ^^ pA) *> ((wZ ^^ z) *>
      ((wT ^^ pB) *> ([S0; S1; S1; S1] *> ((wT ^^ pC) *> ([S0; S1] *> 0inf)))))))))).

Definition e0101Cfg (pA z pB pC : nat) : Q * tape :=
  cfgE ([S1; S0; S1; S1] *> 0inf)
    (wT *> (wZ *> ((wT ^^ 9) *> (([S0; S1] ^^ 2) *> ((wT ^^ pA) *> (wRM *> ((wZ ^^ (z - 1)) *>
      ((wT ^^ pB) *> ([S0; S1; S1; S1] *> ((wT ^^ pC) *> ([S0; S1] *> 0inf))))))))))).

(* ========================================================================== *)
(* Fast Symbolic-to-Canonical Evaluation Bridge Lemmas                        *)
(* ========================================================================== *)

Lemma add_one_0 : 0 + 1 = 1. Proof. reflexivity. Qed.
Lemma add_one_1 : 1 + 1 = 2. Proof. reflexivity. Qed.
Lemma add_one_7 : #7 + 1 = 8. Proof. reflexivity. Qed.
Lemma add_one_8 : #8 + 1 = 9. Proof. reflexivity. Qed.

Ltac norm_eval :=
  cbn [app encSL encSR];
  rewrite ?encSL_symTail;
  rewrite ?evalSymN_zero, ?evalSymN_one, ?evalSymN_const;
  rewrite ?add_one_0, ?add_one_1, ?add_one_7, ?add_one_8, ?Nat.sub_diag;
  rewrite ?pWord_0_0, ?pWord_1_0, ?pWord_1_1, ?pWord_1_2, ?pWord_2_0;
  rewrite ?lpow_1, ?lpow_0, ?Str_app_nil, ?list_1011_eq.

Lemma eval_mCfg_z1 (v : V5) (cm ca cb cc : SymN) (m c k : nat)
  (hm : evalSymN v cm + 1 = m) (ha : evalSymN v ca + 3 = 6 * k + 7)
  (hb : evalSymN v cb + 1 = 3 * k + 1) (hc : evalSymN v cc + 1 = c) :
  evalSym v (mA, [sl_pair 1 0 symZero; sl_mid cm; sl_pair 1 1 symZero; sl_pair 1 0 symZero],
    [sr_pair 0 0 symZero; sr_pair 1 1 ca; sr_mid symZero; sr_pair 1 1 cb;
     sr_pair 1 2 symZero; sr_pair 1 1 cc; sr_pair 1 0 symZero]) = mCfg m 1 c k.
Proof.
  unfold evalSym, mCfg, tailL0. norm_eval.
  rewrite hm, hb, hc, wT_pow_wRM_eq.
  replace (evalSymN v ca + 1 + 2) with (6 * k + 7) by fast_lia.
  reflexivity.
Qed.

Lemma eval_mCfg_z2 (v : V5) (cm ca cz cb cc : SymN) (m z c k : nat)
  (hm : evalSymN v cm + 1 = m) (ha : evalSymN v ca + 1 = 6 * k + 7)
  (hz : evalSymN v cz + 1 = z) (hb : evalSymN v cb + 1 = 3 * k + 1)
  (hc : evalSymN v cc + 1 = c) :
  evalSym v (mA, [sl_pair 1 0 symZero; sl_mid cm; sl_pair 1 1 symZero; sl_pair 1 0 symZero],
    [sr_pair 0 0 symZero; sr_pair 1 1 ca; sr_pair 2 0 cz; sr_pair 1 1 cb;
     sr_pair 1 2 symZero; sr_pair 1 1 cc; sr_pair 1 0 symZero]) = mCfg m z c k.
Proof.
  unfold evalSym, mCfg, tailL0. norm_eval.
  rewrite hm, ha, hz, hb, hc. reflexivity.
Qed.

Lemma eval_postL11_r0_z1 (v : V5) (ca cb cc : SymN) (u c : nat)
  (ha : evalSymN v ca + 3 = 6 * u + #115) (hb : evalSymN v cb + 1 = 3 * u + #55)
  (hc : evalSymN v cc + 1 = c) :
  evalSym v (mA, [sl_pair 1 0 symZero; sl_pair 1 1 symZero; sl_pair 1 0 symZero],
    [sr_pair 0 0 symZero; sr_pair 1 1 ca; sr_mid symZero; sr_pair 1 1 cb;
     sr_pair 1 2 symZero; sr_pair 1 1 cc; sr_pair 1 0 symZero]) = postL11Cfg 0 u 1 c.
Proof.
  unfold evalSym, postL11Cfg, tailL0. norm_eval.
  rewrite hb, hc, wT_pow_wRM_eq.
  replace (evalSymN v ca + 1 + 2) with (6 * u + #115) by fast_lia.
  reflexivity.
Qed.

Lemma eval_postL11_r0_z2 (v : V5) (ca cz cb cc : SymN) (u z c : nat)
  (ha : evalSymN v ca + 1 = 6 * u + #115) (hz : evalSymN v cz + 1 = z)
  (hb : evalSymN v cb + 1 = 3 * u + #55) (hc : evalSymN v cc + 1 = c) :
  evalSym v (mA, [sl_pair 1 0 symZero; sl_pair 1 1 symZero; sl_pair 1 0 symZero],
    [sr_pair 0 0 symZero; sr_pair 1 1 ca; sr_pair 2 0 cz; sr_pair 1 1 cb;
     sr_pair 1 2 symZero; sr_pair 1 1 cc; sr_pair 1 0 symZero]) = postL11Cfg 0 u z c.
Proof.
  unfold evalSym, postL11Cfg, tailL0. norm_eval.
  rewrite ha, hz, hb, hc. reflexivity.
Qed.

Lemma eval_postL11_r1_z1 (v : V5) (cr ca cb cc : SymN) (r u c : nat)
  (hr : evalSymN v cr + 1 = r) (ha : evalSymN v ca + 3 = 6 * u + #115)
  (hb : evalSymN v cb + 1 = 3 * u + #55) (hc : evalSymN v cc + 1 = c) :
  evalSym v (mA, [sl_pair 1 0 symZero; sl_mid cr; sl_pair 1 1 symZero; sl_pair 1 0 symZero],
    [sr_pair 0 0 symZero; sr_pair 1 1 ca; sr_mid symZero; sr_pair 1 1 cb;
     sr_pair 1 2 symZero; sr_pair 1 1 cc; sr_pair 1 0 symZero]) = postL11Cfg r u 1 c.
Proof.
  unfold evalSym, postL11Cfg, tailL0. norm_eval.
  rewrite hr, hb, hc, wT_pow_wRM_eq.
  replace (evalSymN v ca + 1 + 2) with (6 * u + #115) by fast_lia.
  reflexivity.
Qed.

Lemma eval_postL11_r1_z2 (v : V5) (cr ca cz cb cc : SymN) (r u z c : nat)
  (hr : evalSymN v cr + 1 = r) (ha : evalSymN v ca + 1 = 6 * u + #115)
  (hz : evalSymN v cz + 1 = z) (hb : evalSymN v cb + 1 = 3 * u + #55)
  (hc : evalSymN v cc + 1 = c) :
  evalSym v (mA, [sl_pair 1 0 symZero; sl_mid cr; sl_pair 1 1 symZero; sl_pair 1 0 symZero],
    [sr_pair 0 0 symZero; sr_pair 1 1 ca; sr_pair 2 0 cz; sr_pair 1 1 cb;
     sr_pair 1 2 symZero; sr_pair 1 1 cc; sr_pair 1 0 symZero]) = postL11Cfg r u z c.
Proof.
  unfold evalSym, postL11Cfg, tailL0. norm_eval.
  rewrite hr, ha, hz, hb, hc. reflexivity.
Qed.

Lemma eval_convMLoop (v : V5) (i : nat) (cA cM cZ cC : SymN) (pA pM pZ pC : nat)
  (hA : evalSymN v cA + 1 = pA) (hM : evalSymN v cM + 1 = pM)
  (hZ : evalSymN v cZ + 1 = pZ) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE,
    [sl_pair 0 0 symZero; sl_pair 1 1 symZero; sl_pair 2 0 symZero; sl_pair 2 0 cA; sl_mid cM] ++ symTail i,
    [sr_pair 1 1 symZero; sr_pair 2 0 cZ; sr_pair 1 1 cC; sr_pair 1 0 symZero]) =
    convMLoopCfg i pA pM pZ pC.
Proof.
  unfold evalSym, convMLoopCfg. norm_eval.
  rewrite hA, hM, hZ, hC, wZ_cons_pow. reflexivity.
Qed.

Lemma eval_convSimple_1 (v : V5) (i : nat) (cA cM cR : SymN) (pA pM R0 : nat)
  (hA : evalSymN v cA + 1 = pA) (hM : evalSymN v cM + 1 = pM) (hR : evalSymN v cR + 1 = R0) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 2 0 cA; sl_mid cM] ++ symTail i,
    [sr_pair 1 1 cR; sr_pair 1 0 symZero]) = convSimpleCfg i pA pM R0.
Proof.
  unfold evalSym, convSimpleCfg. norm_eval.
  rewrite hA, hM, hR. reflexivity.
Qed.

Lemma eval_convSimple_2 (v : V5) (i : nat) (cA1 cA2 cM cR : SymN) (pA pM R0 : nat)
  (hA : evalSymN v cA1 + 1 + (evalSymN v cA2 + 1) = pA)
  (hM : evalSymN v cM + 1 = pM) (hR : evalSymN v cR + 1 = R0) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 2 0 cA1; sl_pair 2 0 cA2; sl_mid cM] ++ symTail i,
    [sr_pair 1 1 cR; sr_pair 1 0 symZero]) = convSimpleCfg i pA pM R0.
Proof.
  unfold evalSym, convSimpleCfg. norm_eval.
  rewrite hM, hR, wZ_add_pow, hA. reflexivity.
Qed.

Lemma eval_convEntry_1_z1 (v : V5) (i : nat) (cB cA cM cR : SymN) (pB pA pM R0 : nat)
  (hB : evalSymN v cB + 1 = pB) (hA : evalSymN v cA + 1 = pA)
  (hM : evalSymN v cM + 1 = pM) (hR : evalSymN v cR + 1 = R0) :
  evalSym v (mE,
    [sl_pair 0 0 symZero; sl_pair 2 0 cB; sl_mid symZero; sl_pair 2 0 cA; sl_mid cM] ++ symTail i,
    [sr_pair 1 1 cR; sr_pair 1 0 symZero]) = convEntryCfg i pB 1 pA pM R0.
Proof.
  unfold evalSym, convEntryCfg. norm_eval.
  rewrite hB, hA, hM, hR. reflexivity.
Qed.

Lemma eval_convEntry_1_z2 (v : V5) (i : nat) (cB cz cA cM cR : SymN)
  (pB z pA pM R0 : nat)
  (hB : evalSymN v cB + 1 = pB) (hz : evalSymN v cz + 1 = z - 1)
  (hA : evalSymN v cA + 1 = pA) (hM : evalSymN v cM + 1 = pM) (hR : evalSymN v cR + 1 = R0) :
  evalSym v (mE,
    [sl_pair 0 0 symZero; sl_pair 2 0 cB; sl_pair 1 1 cz; sl_mid symZero; sl_pair 2 0 cA; sl_mid cM] ++ symTail i,
    [sr_pair 1 1 cR; sr_pair 1 0 symZero]) = convEntryCfg i pB z pA pM R0.
Proof.
  unfold evalSym, convEntryCfg. norm_eval.
  rewrite hB, hz, hA, hM, hR. reflexivity.
Qed.

Lemma eval_convEntry_2_z1 (v : V5) (i : nat) (cB1 cB2 cA cM cR : SymN)
  (pB pA pM R0 : nat)
  (hB : evalSymN v cB1 + 1 + (evalSymN v cB2 + 1) = pB)
  (hA : evalSymN v cA + 1 = pA) (hM : evalSymN v cM + 1 = pM) (hR : evalSymN v cR + 1 = R0) :
  evalSym v (mE,
    [sl_pair 0 0 symZero; sl_pair 2 0 cB1; sl_pair 2 0 cB2; sl_mid symZero; sl_pair 2 0 cA; sl_mid cM] ++ symTail i,
    [sr_pair 1 1 cR; sr_pair 1 0 symZero]) = convEntryCfg i pB 1 pA pM R0.
Proof.
  unfold evalSym, convEntryCfg. norm_eval.
  rewrite hA, hM, hR, wZ_add_pow, hB. reflexivity.
Qed.

Lemma eval_convEntry_2_z2 (v : V5) (i : nat) (cB1 cB2 cz cA cM cR : SymN)
  (pB z pA pM R0 : nat)
  (hB : evalSymN v cB1 + 1 + (evalSymN v cB2 + 1) = pB) (hz : evalSymN v cz + 1 = z - 1)
  (hA : evalSymN v cA + 1 = pA) (hM : evalSymN v cM + 1 = pM) (hR : evalSymN v cR + 1 = R0) :
  evalSym v (mE,
    [sl_pair 0 0 symZero; sl_pair 2 0 cB1; sl_pair 2 0 cB2; sl_pair 1 1 cz; sl_mid symZero; sl_pair 2 0 cA; sl_mid cM] ++ symTail i,
    [sr_pair 1 1 cR; sr_pair 1 0 symZero]) = convEntryCfg i pB z pA pM R0.
Proof.
  unfold evalSym, convEntryCfg. norm_eval.
  rewrite hz, hA, hM, hR, wZ_add_pow, hB. reflexivity.
Qed.

Lemma eval_eMidExtra0_c0 (v : V5) (cM cA cd : SymN) (pM pA d : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA) (hd : evalSymN v cd + 1 = d) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero;
     sr_pair 2 0 symZero; sr_pair 1 1 cd; sr_pair 1 2 symZero; sr_pair 1 0 symZero]) =
    eMidExtra0Cfg pM pA d 0.
Proof.
  unfold evalSym, eMidExtra0Cfg. norm_eval.
  rewrite hM, hA, hd. reflexivity.
Qed.

Lemma eval_eMidExtra0_c1 (v : V5) (cM cA cd cC : SymN) (pM pA d pC : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA)
  (hd : evalSymN v cd + 1 = d) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero;
     sr_pair 2 0 symZero; sr_pair 1 1 cd; sr_pair 1 2 symZero; sr_pair 1 1 cC; sr_pair 1 0 symZero]) =
    eMidExtra0Cfg pM pA d pC.
Proof.
  unfold evalSym, eMidExtra0Cfg. norm_eval.
  rewrite hM, hA, hd, hC. reflexivity.
Qed.

Lemma eval_eMidExtra12_z1_c0 (v : V5) (cM cA cBm cd : SymN) (pM pA Bm d : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA)
  (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero;
     sr_pair 1 1 cBm; sr_mid symZero; sr_pair 2 0 symZero; sr_pair 1 1 cd; sr_pair 1 2 symZero;
     sr_pair 1 0 symZero]) = eMidExtra12Cfg pM pA 1 Bm d 0.
Proof.
  unfold evalSym, eMidExtra12Cfg. norm_eval.
  rewrite hM, hA, hBm, hd. reflexivity.
Qed.

Lemma eval_eMidExtra12_z1_c1 (v : V5) (cM cA cBm cd cC : SymN) (pM pA Bm d pC : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA)
  (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero;
     sr_pair 1 1 cBm; sr_mid symZero; sr_pair 2 0 symZero; sr_pair 1 1 cd; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = eMidExtra12Cfg pM pA 1 Bm d pC.
Proof.
  unfold evalSym, eMidExtra12Cfg. norm_eval.
  rewrite hM, hA, hBm, hd, hC. reflexivity.
Qed.

Lemma eval_eMidExtra12_z2_c0 (v : V5) (cM cA cz cBm cd : SymN) (pM pA z Bm d : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA) (hz : evalSymN v cz + 1 = z - 1)
  (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero; sr_pair 2 0 cz;
     sr_pair 1 1 cBm; sr_mid symZero; sr_pair 2 0 symZero; sr_pair 1 1 cd; sr_pair 1 2 symZero;
     sr_pair 1 0 symZero]) = eMidExtra12Cfg pM pA z Bm d 0.
Proof.
  unfold evalSym, eMidExtra12Cfg. norm_eval.
  rewrite hM, hA, hz, hBm, hd. reflexivity.
Qed.

Lemma eval_eMidExtra12_z2_c1 (v : V5) (cM cA cz cBm cd cC : SymN)
  (pM pA z Bm d pC : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA) (hz : evalSymN v cz + 1 = z - 1)
  (hBm : evalSymN v cBm + 1 = Bm) (hd : evalSymN v cd + 1 = d) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero; sr_pair 2 0 cz;
     sr_pair 1 1 cBm; sr_mid symZero; sr_pair 2 0 symZero; sr_pair 1 1 cd; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = eMidExtra12Cfg pM pA z Bm d pC.
Proof.
  unfold evalSym, eMidExtra12Cfg. norm_eval.
  rewrite hM, hA, hz, hBm, hd, hC. reflexivity.
Qed.

Lemma eval_eMid0 (v : V5) (cM cA cB cC : SymN) (pM pA pB pC : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA)
  (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_pair 1 0 symOne;
     sr_pair 1 1 cB; sr_pair 1 2 symZero; sr_pair 1 1 cC; sr_pair 1 0 symZero]) =
    eMid0Cfg pM pA pB pC.
Proof.
  unfold evalSym, eMid0Cfg. norm_eval.
  rewrite hM, hA, hB, hC. reflexivity.
Qed.

Lemma eval_eMid12_z1 (v : V5) (cM cA cB cC : SymN) (pM pA pB pC : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA)
  (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero;
     sr_pair 1 1 symOne; sr_pair 1 0 symOne; sr_pair 1 1 cB; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = eMid12Cfg pM pA 1 pB pC.
Proof.
  unfold evalSym, eMid12Cfg. norm_eval.
  rewrite hM, hA, hB, hC. reflexivity.
Qed.

Lemma eval_eMid12_z2 (v : V5) (cM cA cz cB cC : SymN) (pM pA z pB pC : nat)
  (hM : evalSymN v cM + 1 = pM) (hA : evalSymN v cA + 1 = pA) (hz : evalSymN v cz + 1 = z - 1)
  (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_mid cM; sr_pair 1 1 cA; sr_mid symZero; sr_pair 2 0 cz;
     sr_pair 1 1 symOne; sr_pair 1 0 symOne; sr_pair 1 1 cB; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = eMid12Cfg pM pA z pB pC.
Proof.
  unfold evalSym, eMid12Cfg. norm_eval.
  rewrite hM, hA, hz, hB, hC. reflexivity.
Qed.

Lemma eval_eClean_z1 (v : V5) (cA cB cC : SymN) (pA pB pC : nat)
  (hA : evalSymN v cA + 1 = pA) (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_pair 1 1 cA; sr_mid symZero;
     sr_pair 1 1 cB; sr_pair 1 2 symZero; sr_pair 1 1 cC; sr_pair 1 0 symZero]) =
    eCleanCfg pA 1 pB pC.
Proof.
  unfold evalSym, eCleanCfg. norm_eval.
  rewrite hA, hB, hC. reflexivity.
Qed.

Lemma eval_eClean_z2 (v : V5) (cA cz cB cC : SymN) (pA z pB pC : nat)
  (hA : evalSymN v cA + 1 = pA) (hz : evalSymN v cz + 1 = z - 1)
  (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_pair 1 1 cA; sr_mid symZero; sr_pair 2 0 cz;
     sr_pair 1 1 cB; sr_pair 1 2 symZero; sr_pair 1 1 cC; sr_pair 1 0 symZero]) =
    eCleanCfg pA z pB pC.
Proof.
  unfold evalSym, eCleanCfg. norm_eval.
  rewrite hA, hz, hB, hC. reflexivity.
Qed.

Lemma eval_e0111_z1 (v : V5) (cA cB cC : SymN) (pA pB pC : nat)
  (hA : evalSymN v cA + 3 = pA) (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_pair 1 1 (symConst 7%N); sr_pair 1 2 symZero;
     sr_pair 1 1 cA; sr_mid symZero; sr_pair 1 1 cB; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = e0111Cfg pA 1 pB pC.
Proof.
  unfold evalSym, e0111Cfg. norm_eval.
  rewrite hB, hC, wT_pow_wRM_eq.
  replace (evalSymN v cA + 1 + 2) with pA by fast_lia.
  reflexivity.
Qed.

Lemma eval_e0111_z2 (v : V5) (cA cz cB cC : SymN) (pA z pB pC : nat)
  (hA : evalSymN v cA + 1 = pA) (hz : evalSymN v cz + 1 = z)
  (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_pair 1 1 (symConst 7%N); sr_pair 1 2 symZero;
     sr_pair 1 1 cA; sr_pair 2 0 cz; sr_pair 1 1 cB; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = e0111Cfg pA z pB pC.
Proof.
  unfold evalSym, e0111Cfg. norm_eval.
  rewrite hA, hz, hB, hC. reflexivity.
Qed.

Lemma eval_e0101_z1 (v : V5) (cA cB cC : SymN) (pA pB pC : nat)
  (hA : evalSymN v cA + 1 = pA) (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_pair 1 1 (symConst 8%N); sr_pair 1 0 symOne;
     sr_pair 1 1 cA; sr_mid symZero; sr_pair 1 1 cB; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = e0101Cfg pA 1 pB pC.
Proof.
  unfold evalSym, e0101Cfg. norm_eval.
  rewrite hA, hB, hC. reflexivity.
Qed.

Lemma eval_e0101_z2 (v : V5) (cA cz cB cC : SymN) (pA z pB pC : nat)
  (hA : evalSymN v cA + 1 = pA) (hz : evalSymN v cz + 1 = z - 1)
  (hB : evalSymN v cB + 1 = pB) (hC : evalSymN v cC + 1 = pC) :
  evalSym v (mE, [sl_pair 0 0 symZero; sl_pair 1 1 symZero],
    [sr_pair 1 1 symZero; sr_pair 2 0 symZero; sr_pair 1 1 (symConst 8%N); sr_pair 1 0 symOne;
     sr_pair 1 1 cA; sr_mid symZero; sr_pair 2 0 cz; sr_pair 1 1 cB; sr_pair 1 2 symZero;
     sr_pair 1 1 cC; sr_pair 1 0 symZero]) = e0101Cfg pA z pB pC.
Proof.
  unfold evalSym, e0101Cfg. norm_eval.
  rewrite hA, hz, hB, hC. reflexivity.
Qed.

(* ========================================================================== *)
(* Parametric Invariants                                                      *)
(* ========================================================================== *)

Definition InvM (m z c k : nat) : Prop :=
  k <= 5 /\ 1 <= z /\ 33 <= m /\ 9 * m <= c /\ #2100 <= c.

Definition InvConvMLoop (i pA pM pZ pC : nat) : Prop :=
  #50 <= pA /\ 46 <= pM /\ 1 <= pZ /\ 9 * pM + (if Nat.eqb i 4 then 4 else 0) <= pC /\ #2120 <= pC.

Definition InvConvSimple (_i pA pM R0 : nat) : Prop :=
  #50 <= pA /\ 46 <= pM /\ 4 <= R0 /\ 9 * pM <= R0 + 2 * pA /\ #2120 <= R0 + 2 * pA.

Definition InvConvEntryZ2 (_i pB pA pM R0 : nat) : Prop :=
  #50 <= pA /\ 20 <= pB /\ 46 <= pM /\ 4 <= R0 /\ 9 * pM <= R0 + 2 * pB + pA /\ #2120 <= R0 + 2 * pB + pA.

Definition InvConvEntry (_i pB z pA pM R0 : nat) : Prop :=
  #50 <= pA /\ 20 <= pB /\ 1 <= z /\ 46 <= pM /\ 4 <= R0 /\ 9 * pM + 6 <= R0 + 2 * pB /\ #2120 <= R0 + 2 * pB.

Definition InvEmidExtraPost0 (pM pA Bd rC2 : nat) : Prop :=
  rC2 < 6 /\ #50 <= pA /\ 46 <= pM /\ 20 <= Bd /\ 9 * pM <= 2 * Bd + pA /\ #2120 <= 2 * Bd + pA.

Definition InvEmidExtraPost12 (pM pA z Bm Bd rC2 : nat) : Prop :=
  rC2 < 6 /\ 1 <= z /\ #50 <= pA /\ 46 <= pM /\ 20 <= Bm /\ 20 <= Bd /\ (Bd + rC2) mod 2 = 1 /\
    9 * pM <= 2 * Bd + 2 * Bm /\ #2120 <= 2 * Bd + 2 * Bm.

Definition InvEmidExtra0 (pM pA d pC : nat) : Prop :=
  1 <= d /\ #50 <= pA /\ #120 <= pC /\ #282 <= 6 * pM + pC /\ 18 * pM + 1 <= pC + 2 * pA /\ #2128 <= 2 * pC + pA.

Definition InvEmidExtra12 (pM pA z Bm d pC : nat) : Prop :=
  1 <= d /\ 1 <= z /\ #50 <= pA /\ 20 <= Bm /\ #120 <= pC /\ #282 <= 6 * pM + pC /\
    18 * pM + 1 <= pC + 4 * Bm /\ #2128 <= 2 * pC + 2 * Bm /\ (d + pC) mod 2 = 1.

Definition InvEmid0 (pM pA pB pC : nat) : Prop :=
  #50 <= pA /\ 19 <= pM /\ #50 <= pB /\ #60 <= pC /\ #560 <= 12 * pM + pC /\
    36 * pM + #80 <= pC + 4 * pB + 4 * pA /\ #2120 <= 2 * pC + 2 * pB + pA.

Definition InvEmid12 (pM pA z pB pC : nat) : Prop :=
  1 <= z /\ #50 <= pA /\ 19 <= pM /\ #50 <= pB /\ #60 <= pC /\ #560 <= 12 * pM + pC /\
    36 * pM + #80 <= 3 * pC + 4 * pB /\ #1060 <= pC + pB.

Definition InvEclean (pA z pB pC : nat) : Prop :=
  1 <= z /\ #50 <= pA /\ #50 <= pB /\ #282 <= pC /\ #1060 <= pC + pB.

Definition ReachesInvM (cfg : Q * tape) : Prop :=
  exists m' z' c' k', InvM m' z' c' k' /\ cfg -->+ mCfg m' z' c' k'.

Ltac solve_inv :=
  clear_steps;
  unfold InvM, InvConvMLoop, InvConvSimple, InvConvEntryZ2, InvConvEntry,
    InvEmidExtraPost0, InvEmidExtraPost12, InvEmidExtra0, InvEmidExtra12,
    InvEmid0, InvEmid12, InvEclean;
  cbn [Nat.eqb];
  repeat split; fast_lia.



End TM1.
