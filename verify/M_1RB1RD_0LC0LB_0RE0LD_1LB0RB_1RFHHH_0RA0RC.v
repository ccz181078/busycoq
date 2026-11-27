(* BB(6) holdout 608:#228 / 797:#308: 1RB1RD_0LC0LB_0RE0LD_1LB0RB_1RF---_0RA0RC halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import String Bool Lists.List PeanoNat ArithRing NArith PArith ZifyNat Lia.
Import ListNotations.
Set Default Goal Selector "!".

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1RD_0LC0LB_0RE0LD_1LB0RB_1RF---_0RA0RC").

Module Internal.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Local Arguments lpow : simpl never.

(* ========================================================================= *)
(* Section 1: Preliminaries, Stream/Power Helpers, and Binary-N Bridge       *)
(* ========================================================================= *)

Lemma halted_halts (c : Q * tape) : halted tm c -> halts tm c.
Proof.
  intros H. exists 0, c. split; [constructor | exact H].
Qed.

Lemma ev_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof.
  exact (@evstep_trans tm c1 c2 c3).
Qed.

Lemma evstep_halts {c c' : Q * tape} : c -->* c' -> halts tm c' -> halts tm c.
Proof.
  induction 1 as [c | c c1 c2 H1 _ IH]; [auto |].
  intros H2. apply IH in H2. destruct H2 as [n [ch [Hm Hh]]].
  exists (S n), ch. split; [econstructor; eauto | exact Hh].
Qed.

Lemma app_str {X : Type} (xs ys : list X) (s : Stream X) :
  (xs ++ ys) *> s = xs *> (ys *> s).
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma lpow_0 {X : Type} (u : list X) : u ^^ 0 = [].
Proof. reflexivity. Qed.

Lemma lpow_1 {X : Type} (u : list X) : u ^^ 1 = u.
Proof. change (u ^^ 1) with (u ++ []). apply app_nil_r. Qed.

Lemma lpow_S_l {X : Type} (u : list X) (n : nat) : u ^^ S n = u ++ u ^^ n.
Proof. reflexivity. Qed.

Lemma lpow_add1_l {X : Type} (u : list X) (n : nat) : u ^^ (n + 1) = u ++ u ^^ n.
Proof. replace (n + 1) with (S n) by lia. reflexivity. Qed.

Lemma lpow_add_eq {X : Type} (u : list X) (m n : nat) :
  u ^^ (m + n) = u ^^ m ++ u ^^ n.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - simpl Nat.add. rewrite !lpow_S_l, IH, app_assoc. reflexivity.
Qed.

Lemma lpow_add1_r {X : Type} (u : list X) (n : nat) : u ^^ (n + 1) = u ^^ n ++ u.
Proof. rewrite lpow_add_eq, lpow_1. reflexivity. Qed.

Lemma str_lpow_S {X : Type} (u : list X) (n : nat) (s : Stream X) :
  (u ^^ (n + 1)) *> s = u *> ((u ^^ n) *> s).
Proof. rewrite lpow_add1_l, app_str. reflexivity. Qed.

Lemma str_lpow_S_r {X : Type} (u : list X) (n : nat) (s : Stream X) :
  (u ^^ (n + 1)) *> s = (u ^^ n) *> (u *> s).
Proof. rewrite lpow_add1_r, app_str. reflexivity. Qed.

Lemma str_lpow_add {X : Type} (u : list X) (m n : nat) (s : Stream X) :
  (u ^^ (m + n)) *> s = (u ^^ m) *> ((u ^^ n) *> s).
Proof. rewrite lpow_add_eq, app_str. reflexivity. Qed.

Lemma pow_append_pow {X : Type} (u : list X) (m n : nat) (s : Stream X) :
  (u ^^ m) *> ((u ^^ n) *> s) = (u ^^ (m + n)) *> s.
Proof. symmetry. apply str_lpow_add. Qed.

Lemma cons_zero_const0 : S0 >> const S0 = const S0.
Proof. rewrite <- const_unfold. reflexivity. Qed.

Lemma N_eqb_eq_true (a b : N) : N.eqb a b = true -> a = b.
Proof. apply N.eqb_eq. Qed.

Lemma N_eqb_false_nat (a b : N) : N.eqb a b = false -> N.to_nat a <> N.to_nat b.
Proof. rewrite N.eqb_neq, N2Nat.inj_iff. auto. Qed.

Lemma N_eqb_false_intro (a b : N) : N.to_nat a <> N.to_nat b -> N.eqb a b = false.
Proof.
  intros Hne. destruct (N.eqb a b) eqn:Heq; [| reflexivity].
  apply N.eqb_eq in Heq. subst b. exfalso; apply Hne; reflexivity.
Qed.

Lemma N_leb_true_nat (a b : N) : N.leb a b = true -> N.to_nat a <= N.to_nat b.
Proof.
  rewrite N.leb_le. unfold N.le.
  rewrite N2Nat.inj_compare, <- Nat.compare_le_iff. auto.
Qed.

Lemma N_leb_true_intro (a b : N) : N.to_nat a <= N.to_nat b -> N.leb a b = true.
Proof.
  intros Hle. apply N.leb_le. unfold N.le.
  rewrite N2Nat.inj_compare. apply Nat.compare_le_iff. exact Hle.
Qed.

Lemma N2Nat_inj_pow7 (k : nat) :
  N.to_nat (N.pow 7%N (N.of_nat k)) = Nat.pow 7 k.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - rewrite Nat2N.inj_succ, N.pow_succ_r'.
    rewrite N2Nat.inj_mul, IH.
    change (N.to_nat 7%N) with 7.
    simpl (Nat.pow 7 (S k)). reflexivity.
Qed.

Ltac nat_norm :=
  repeat (
    rewrite N2Nat.inj_add in * ||
    rewrite N2Nat.inj_sub in * ||
    rewrite N2Nat.inj_mul in * ||
    rewrite N2Nat_inj_pow7 in * ||
    rewrite Nat2N.id in *
  );
  repeat match goal with
  | |- context [N.to_nat (Npos ?p)] => progress change (N.to_nat (Npos p)) with (Pos.to_nat p)
  | H : context [N.to_nat (Npos ?p)] |- _ => progress change (N.to_nat (Npos p)) with (Pos.to_nat p) in H
  end;
  repeat change (N.to_nat 0%N) with 0 in *;
  repeat change (Pos.to_nat 1%positive) with 1 in *;
  repeat change (Pos.to_nat 2%positive) with 2 in *;
  repeat change (Pos.to_nat 3%positive) with 3 in *;
  repeat change (Pos.to_nat 4%positive) with 4 in *;
  repeat change (Pos.to_nat 7%positive) with 7 in *;
  repeat change (Pos.to_nat 12%positive) with 12 in *;
  repeat change (Pos.to_nat 14%positive) with 14 in *.

Ltac nlia := nat_norm; lia.

(* ========================================================================= *)
(* Section 2: Modes, Binary-N Tokens, Encoding, and Primitive Operations     *)
(* ========================================================================= *)

Inductive WordMode : Type :=
| CR | CL | DL | BL | HALT.

Inductive Tok : Type :=
| b0
| b1
| w001 (d : N).

Inductive StepRes : Type :=
| st_ok (m : WordMode) (ls rs : list Tok)
| st_halted
| st_err.

Definition wZ : list Sym := [S0; S0; S1].

Fixpoint encHalf (xs : list Tok) : side :=
  match xs with
  | [] => const S0
  | b0 :: rest => [S0] *> encHalf rest
  | b1 :: rest => [S1] *> encHalf rest
  | w001 d :: rest => (wZ ^^ (N.to_nat d + 1)) *> encHalf rest
  end.

Definition encode (m : WordMode) (ls rs : list Tok) : Q * tape :=
  match m with
  | CR => (encHalf ls) {{C}}> (encHalf rs)
  | CL => (encHalf ls) <{{C}} (encHalf rs)
  | DL => (encHalf ls) <{{D}} (encHalf rs)
  | BL => (encHalf ls) <{{B}} (encHalf rs)
  | HALT => (encHalf ls) {{E}}> ([S1] *> encHalf rs)
  end.

Definition bitList (b : bool) : list Sym :=
  if b then [S1] else [S0].

Local Open Scope N_scope.

Definition push001K (d : N) (xs : list Tok) : list Tok :=
  match xs with
  | w001 d' :: rest => w001 (d + 1 + d') :: rest
  | _ => w001 d :: xs
  end.

Definition pushCnt001K (d : N) (xs : list Tok) : list Tok :=
  if N.eqb d 0 then xs else push001K (d - 1) xs.

Definition push0K (xs : list Tok) : list Tok :=
  match xs with
  | b0 :: b1 :: rest => push001K 0 rest
  | _ => b0 :: xs
  end.

Definition push1K (xs : list Tok) : list Tok := b1 :: xs.

Definition peel001K (d : N) (rest : list Tok) : list Tok :=
  if N.eqb d 0 then rest else w001 (d - 1) :: rest.

Definition popBitK (xs : list Tok) : bool * list Tok :=
  match xs with
  | [] => (false, [])
  | b0 :: rest => (false, rest)
  | b1 :: rest => (true, rest)
  | w001 d :: rest => (false, b0 :: b1 :: peel001K d rest)
  end.

Local Open Scope nat_scope.

Lemma encHalf_push001K (d : N) (xs : list Tok) :
  encHalf (push001K d xs) = (wZ ^^ (N.to_nat d + 1)) *> encHalf xs.
Proof.
  destruct xs as [| [| | d'] rest]; try reflexivity.
  cbn [push001K encHalf].
  rewrite pow_append_pow. f_equal. f_equal. nlia.
Qed.

Lemma encHalf_pushCnt001K (d : N) (xs : list Tok) :
  encHalf (pushCnt001K d xs) = (wZ ^^ N.to_nat d) *> encHalf xs.
Proof.
  unfold pushCnt001K. destruct (N.eqb d 0%N) eqn:Hd0.
  - apply N_eqb_eq_true in Hd0; subst d. simpl. reflexivity.
  - apply N_eqb_false_nat in Hd0.
    rewrite encHalf_push001K. f_equal. f_equal. nlia.
Qed.

Lemma encHalf_push0K (xs : list Tok) :
  encHalf (push0K xs) = [S0] *> encHalf xs.
Proof.
  destruct xs as [| t1 [| t2 rest]].
  - reflexivity.
  - destruct t1; reflexivity.
  - destruct t1, t2; try reflexivity.
    cbn [push0K]. rewrite encHalf_push001K.
    nat_norm. rewrite lpow_1. reflexivity.
Qed.

Lemma encHalf_push1K (xs : list Tok) :
  encHalf (push1K xs) = [S1] *> encHalf xs.
Proof. reflexivity. Qed.

Lemma encHalf_peel001K (d : N) (rest : list Tok) :
  encHalf (w001 d :: rest) = wZ *> encHalf (peel001K d rest).
Proof.
  unfold peel001K. destruct (N.eqb d 0%N) eqn:Hd0.
  - apply N_eqb_eq_true in Hd0; subst d.
    cbn [encHalf]. nat_norm. rewrite lpow_1. reflexivity.
  - apply N_eqb_false_nat in Hd0.
    cbn [encHalf]. rewrite <- str_lpow_S.
    f_equal. f_equal. nlia.
Qed.

Lemma encHalf_popBitK (xs : list Tok) :
  encHalf xs = bitList (fst (popBitK xs)) *> encHalf (snd (popBitK xs)).
Proof.
  destruct xs as [| [| | d] rest].
  - simpl. symmetry. exact cons_zero_const0.
  - reflexivity.
  - reflexivity.
  - cbn [popBitK fst snd bitList].
    rewrite encHalf_peel001K. reflexivity.
Qed.

Lemma encHalf_of_popBitK {xs rest : list Tok} {b : bool} (H : popBitK xs = (b, rest)) :
  encHalf xs = bitList b *> encHalf rest.
Proof.
  pose proof (encHalf_popBitK xs) as H0.
  rewrite H in H0. exact H0.
Qed.

(* ========================================================================= *)
(* Section 3: Base Sweeps & stepFastK Soundness                              *)
(* ========================================================================= *)

Local Open Scope N_scope.

Definition stepERK (ls rs : list Tok) : StepRes :=
  match popBitK rs with
  | (true, _) => st_halted
  | (false, r1) =>
    match popBitK r1 with
    | (true, r2) => st_ok CR (push0K (push1K ls)) r2
    | (false, r2) =>
      match popBitK r2 with
      | (false, r3) =>
        match popBitK r3 with
        | (false, r4) => st_ok CL (push1K (push0K (push1K ls))) (push0K r4)
        | (true, r4) => st_ok CL (push1K ls) (push0K (push0K (push0K r4)))
        end
      | (true, r3) =>
        match popBitK r3 with
        | (false, r4) => st_ok CL (push1K ls) (push001K 0 r4)
        | (true, r4) =>
          match popBitK r4 with
          | (false, r5) => st_ok CL (push0K (push1K (push0K (push1K ls)))) (push0K r5)
          | (true, r5) => st_ok CL (push1K (push0K (push1K ls))) (push0K (push0K r5))
          end
        end
      end
    end
  end.

Definition stepDLFallbackK (ls rs : list Tok) : StepRes :=
  match popBitK ls with
  | (true, l1) =>
    match popBitK rs with
    | (true, r1) => st_ok BL (push1K (push0K l1)) r1
    | (false, r1) => st_ok BL (push0K (push0K l1)) r1
    end
  | (false, l1) =>
    match popBitK l1 with
    | (false, l2) => st_ok CL l2 (push0K (push1K rs))
    | (true, l2) =>
      match popBitK l2 with
      | (false, l3) => st_ok CL l3 (push001K 0 rs)
      | (true, l3) => st_ok BL l3 (push0K (push0K (push1K rs)))
      end
    end
  end.

Definition stepDLBaseK (ls rs : list Tok) : StepRes :=
  match ls with
  | w001 d :: lr => st_ok DL lr (push001K d rs)
  | _ => stepDLFallbackK ls rs
  end.

Fixpoint unwindCLFuelK (fuel : nat) (ls rs : list Tok) : StepRes :=
  match fuel with
  | 0%nat => st_ok CL ls rs
  | S fuel' =>
    match ls with
    | b1 :: b0 :: b1 :: w001 d :: b0 :: lr =>
      unwindCLFuelK fuel' lr (push001K 0 (push0K (push001K d rs)))
    | _ => st_ok CL ls rs
    end
  end.

Fixpoint unwindDLFuelK (fuel : nat) (ls rs : list Tok) : StepRes :=
  match fuel with
  | 0%nat => st_ok DL ls rs
  | S fuel' =>
    match ls with
    | b0 :: b1 :: b0 :: b1 :: w001 d :: lr =>
      unwindDLFuelK fuel' lr (push001K d (push0K (push001K 0 rs)))
    | _ => st_ok DL ls rs
    end
  end.

Definition stepCRFallbackK (ls rs : list Tok) : StepRes :=
  match popBitK rs with
  | (true, r1) => stepDLBaseK ls (push0K r1)
  | (false, r1) => stepERK (push0K ls) r1
  end.

Definition stepCLFallbackK (ls rs : list Tok) : StepRes :=
  match popBitK ls with
  | (true, l1) => stepDLBaseK l1 (push0K rs)
  | (false, l1) => stepERK (push0K l1) rs
  end.

Definition stepBLK (ls rs : list Tok) : StepRes :=
  match popBitK ls with
  | (true, l1) => st_ok BL l1 (push0K rs)
  | (false, l1) => st_ok CL l1 (push0K rs)
  end.

Definition stepFastK (f1024 : nat) (m : WordMode) (ls rs : list Tok) : StepRes :=
  match m with
  | HALT => st_halted
  | CR =>
    match rs with
    | w001 d :: rr => st_ok CR (push0K (push1K (pushCnt001K d (push0K ls)))) rr
    | _ => stepCRFallbackK ls rs
    end
  | CL =>
    match ls with
    | b1 :: b0 :: b1 :: w001 d :: b0 :: lr =>
      unwindCLFuelK f1024 lr (push001K 0 (push0K (push001K d rs)))
    | b1 :: b0 :: b1 :: w001 d :: lr =>
      st_ok CL (b1 :: b0 :: b1 :: lr) (push001K d rs)
    | _ => stepCLFallbackK ls rs
    end
  | DL =>
    match ls with
    | b0 :: b1 :: b0 :: b1 :: w001 d :: lr =>
      unwindDLFuelK f1024 lr (push001K d (push0K (push001K 0 rs)))
    | _ => stepDLBaseK ls rs
    end
  | BL => stepBLK ls rs
  end.

Definition stepResK (f1024 : nat) (st : StepRes) : StepRes :=
  match st with
  | st_ok m ls rs => stepFastK f1024 m ls rs
  | st_halted => st_halted
  | st_err => st_err
  end.

Fixpoint runStepsK (f1024 n : nat) (st : StepRes) : StepRes :=
  match n with
  | 0%nat => st
  | S n' => runStepsK f1024 n' (stepResK f1024 st)
  end.

Local Open Scope nat_scope.

Lemma step3_ER_01_001 (l r : side) :
  (l {{E}}> ([S0; S1] *> (wZ *> r))) -->*
  ((wZ *> l) {{E}}> ([S0; S1] *> r)).
Proof. unfold wZ; simpl Str_app; execute. Qed.

Lemma walk_ER_01_001 (d : nat) : forall (l r : side),
  (l {{E}}> ([S0; S1] *> ((wZ ^^ d) *> r))) -->*
  (((wZ ^^ d) *> l) {{E}}> ([S0; S1] *> r)).
Proof.
  induction d as [|d IH]; intros l r.
  - apply evstep_refl.
  - replace (S d) with (d + 1) by lia.
    rewrite str_lpow_S.
    eapply ev_trans; [apply step3_ER_01_001 |].
    pose proof (IH (wZ *> l) r) as H2.
    rewrite <- str_lpow_S_r in H2. exact H2.
Qed.

Lemma walk_CR_001_raw (d : nat) (l r : side) :
  (l {{C}}> ((wZ ^^ (d + 1)) *> r)) -->*
  (([S0] *> ([S1] *> (((wZ ^^ d) *> ([S0] *> l))))) {{C}}> r).
Proof.
  rewrite str_lpow_S.
  assert (H1 : (l {{C}}> (wZ *> ((wZ ^^ d) *> r))) -->*
               (([S0] *> l) {{E}}> ([S0; S1] *> ((wZ ^^ d) *> r)))).
  { unfold wZ at 1; simpl Str_app; execute. }
  pose proof (walk_ER_01_001 d ([S0] *> l) r) as H2.
  assert (H3 : (((wZ ^^ d) *> ([S0] *> l)) {{E}}> ([S0; S1] *> r)) -->*
               (([S0] *> ([S1] *> ((wZ ^^ d) *> ([S0] *> l)))) {{C}}> r)).
  { simpl Str_app; execute. }
  exact (ev_trans (ev_trans H1 H2) H3).
Qed.

Lemma step3_DL_001 (l r : side) :
  ((wZ *> l) <{{D}} r) -->* (l <{{D}} (wZ *> r)).
Proof. unfold wZ; simpl Str_app; execute. Qed.

Lemma walk_DL_001 (k : nat) : forall (l r : side),
  (((wZ ^^ k) *> l) <{{D}} r) -->* (l <{{D}} ((wZ ^^ k) *> r)).
Proof.
  induction k as [|k IH]; intros l r.
  - apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite str_lpow_S.
    eapply ev_trans; [apply step3_DL_001 |].
    pose proof (IH l (wZ *> r)) as H2.
    rewrite <- str_lpow_S_r in H2. exact H2.
Qed.

Lemma step11_CL_101_001 (l r : side) :
  (([S1] *> ([S0] *> ([S1] *> (wZ *> l)))) <{{C}} r) -->*
  (([S1] *> ([S0] *> ([S1] *> l))) <{{C}} (wZ *> r)).
Proof. unfold wZ; simpl Str_app; execute. Qed.

Lemma walk_CL_101_001 (k : nat) : forall (l r : side),
  (([S1] *> ([S0] *> ([S1] *> ((wZ ^^ k) *> l)))) <{{C}} r) -->*
  (([S1] *> ([S0] *> ([S1] *> l))) <{{C}} ((wZ ^^ k) *> r)).
Proof.
  induction k as [|k IH]; intros l r.
  - apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite str_lpow_S.
    eapply ev_trans; [apply step11_CL_101_001 |].
    pose proof (IH l (wZ *> r)) as H2.
    rewrite <- str_lpow_S_r in H2. exact H2.
Qed.

Definition ResSound (c : Q * tape) (st : StepRes) : Prop :=
  match st with
  | st_ok m ls rs => c -->* encode m ls rs
  | st_halted => halts tm c
  | st_err => False
  end.

Lemma resSound_trans {c1 c2 : Q * tape} {res : StepRes}
  (H1 : c1 -->* c2) (H2 : ResSound c2 res) : ResSound c1 res.
Proof.
  destruct res as [m ls rs | |].
  - exact (ev_trans H1 H2).
  - exact (evstep_halts H1 H2).
  - exact H2.
Qed.

Lemma stepERK_sound (ls rs : list Tok) :
  ResSound ((encHalf ls) {{E}}> (encHalf rs)) (stepERK ls rs).
Proof.
  unfold stepERK.
  destruct (popBitK rs) as [b1 r1] eqn:Hp1.
  rewrite (encHalf_of_popBitK Hp1).
  destruct b1.
  - cbn [ResSound bitList]. apply halted_halts. reflexivity.
  - destruct (popBitK r1) as [b2 r2] eqn:Hp2.
    rewrite (encHalf_of_popBitK Hp2).
    destruct b2.
    + cbn [ResSound encode bitList].
      rewrite !encHalf_push0K, !encHalf_push1K. simpl Str_app; execute.
    + destruct (popBitK r2) as [b3 r3] eqn:Hp3.
      rewrite (encHalf_of_popBitK Hp3).
      destruct b3.
      * destruct (popBitK r3) as [b4 r4] eqn:Hp4.
        rewrite (encHalf_of_popBitK Hp4).
        destruct b4.
        -- destruct (popBitK r4) as [b5 r5] eqn:Hp5.
           rewrite (encHalf_of_popBitK Hp5).
           destruct b5.
           ++ cbn [ResSound encode bitList].
              rewrite !encHalf_push0K, !encHalf_push1K. simpl Str_app; execute.
           ++ cbn [ResSound encode bitList].
              rewrite !encHalf_push0K, !encHalf_push1K. simpl Str_app; execute.
        -- cbn [ResSound encode bitList].
           rewrite !encHalf_push001K, !encHalf_push1K.
           nat_norm. rewrite lpow_1. unfold wZ; simpl Str_app; execute.
      * destruct (popBitK r3) as [b4 r4] eqn:Hp4.
        rewrite (encHalf_of_popBitK Hp4).
        destruct b4.
        -- cbn [ResSound encode bitList].
           rewrite !encHalf_push0K, !encHalf_push1K. simpl Str_app; execute.
        -- cbn [ResSound encode bitList].
           rewrite !encHalf_push0K, !encHalf_push1K. simpl Str_app; execute.
Qed.

Lemma stepDLFallbackK_sound (ls rs : list Tok) :
  ResSound ((encHalf ls) <{{D}} (encHalf rs)) (stepDLFallbackK ls rs).
Proof.
  unfold stepDLFallbackK.
  destruct (popBitK ls) as [b1 l1] eqn:Hp1.
  rewrite (encHalf_of_popBitK Hp1).
  destruct b1.
  - destruct (popBitK rs) as [bR r1] eqn:HpR.
    rewrite (encHalf_of_popBitK HpR).
    destruct bR.
    + cbn [ResSound encode bitList].
      rewrite !encHalf_push1K, !encHalf_push0K. simpl Str_app; execute.
    + cbn [ResSound encode bitList].
      rewrite !encHalf_push0K. simpl Str_app; execute.
  - destruct (popBitK l1) as [b2 l2] eqn:Hp2.
    rewrite (encHalf_of_popBitK Hp2).
    destruct b2.
    + destruct (popBitK l2) as [b3 l3] eqn:Hp3.
      rewrite (encHalf_of_popBitK Hp3).
      destruct b3.
      * cbn [ResSound encode bitList].
        rewrite !encHalf_push0K, !encHalf_push1K. simpl Str_app; execute.
      * cbn [ResSound encode bitList].
        rewrite !encHalf_push001K. nat_norm. rewrite lpow_1.
        unfold wZ; simpl Str_app; execute.
    + cbn [ResSound encode bitList].
      rewrite !encHalf_push0K, !encHalf_push1K. simpl Str_app; execute.
Qed.

Lemma stepDLBaseK_sound (ls rs : list Tok) :
  ResSound ((encHalf ls) <{{D}} (encHalf rs)) (stepDLBaseK ls rs).
Proof.
  destruct ls as [| [| | d] lr].
  - exact (stepDLFallbackK_sound [] rs).
  - exact (stepDLFallbackK_sound (b0 :: lr) rs).
  - exact (stepDLFallbackK_sound (b1 :: lr) rs).
  - cbn [stepDLBaseK ResSound encode encHalf].
    rewrite encHalf_push001K.
    exact (walk_DL_001 (N.to_nat d + 1) (encHalf lr) (encHalf rs)).
Qed.

Lemma step1_CR_0 (ls r1 : list Tok) :
  ((encHalf ls) {{C}}> ([S0] *> encHalf r1)) -->*
  ((encHalf (push0K ls)) {{E}}> encHalf r1).
Proof. rewrite encHalf_push0K; simpl Str_app; execute. Qed.

Lemma step1_CR_1 (ls r1 : list Tok) :
  ((encHalf ls) {{C}}> ([S1] *> encHalf r1)) -->*
  ((encHalf ls) <{{D}} encHalf (push0K r1)).
Proof. rewrite encHalf_push0K; simpl Str_app; execute. Qed.

Lemma step1_CL_0 (l1 rs : list Tok) :
  (([S0] *> encHalf l1) <{{C}} (encHalf rs)) -->*
  ((encHalf (push0K l1)) {{E}}> encHalf rs).
Proof. rewrite encHalf_push0K; simpl Str_app; execute. Qed.

Lemma step1_CL_1 (l1 rs : list Tok) :
  (([S1] *> encHalf l1) <{{C}} (encHalf rs)) -->*
  ((encHalf l1) <{{D}} encHalf (push0K rs)).
Proof. rewrite encHalf_push0K; simpl Str_app; execute. Qed.

Lemma stepCRFallbackK_sound (ls rs : list Tok) :
  ResSound (encode CR ls rs) (stepCRFallbackK ls rs).
Proof.
  unfold stepCRFallbackK; cbn [encode].
  destruct (popBitK rs) as [b1 r1] eqn:Hp1.
  rewrite (encHalf_of_popBitK Hp1).
  destruct b1; cbn [bitList].
  - exact (resSound_trans (step1_CR_1 ls r1) (stepDLBaseK_sound ls (push0K r1))).
  - exact (resSound_trans (step1_CR_0 ls r1) (stepERK_sound (push0K ls) r1)).
Qed.

Lemma stepCLFallbackK_sound (ls rs : list Tok) :
  ResSound (encode CL ls rs) (stepCLFallbackK ls rs).
Proof.
  unfold stepCLFallbackK; cbn [encode].
  destruct (popBitK ls) as [b1 l1] eqn:Hp1.
  rewrite (encHalf_of_popBitK Hp1).
  destruct b1; cbn [bitList].
  - exact (resSound_trans (step1_CL_1 l1 rs) (stepDLBaseK_sound l1 (push0K rs))).
  - exact (resSound_trans (step1_CL_0 l1 rs) (stepERK_sound (push0K l1) rs)).
Qed.

Lemma stepBLK_sound (ls rs : list Tok) :
  ResSound (encode BL ls rs) (stepBLK ls rs).
Proof.
  unfold stepBLK; cbn [encode].
  destruct (popBitK ls) as [b1 l1] eqn:Hp1.
  rewrite (encHalf_of_popBitK Hp1).
  destruct b1; cbn [ResSound encode bitList]; rewrite encHalf_push0K; simpl Str_app; execute.
Qed.

Lemma cl_frame_step (d : N) (lr rs : list Tok) :
  encode CL (b1 :: b0 :: b1 :: w001 d :: b0 :: lr) rs -->*
  encode CL lr (push001K 0%N (push0K (push001K d rs))).
Proof.
  cbn [encode encHalf].
  pose proof (walk_CL_101_001 (N.to_nat d + 1) ([S0] *> encHalf lr) (encHalf rs)) as H1.
  rewrite <- (encHalf_push001K d rs) in H1.
  assert (H2 : (([S1] *> ([S0] *> ([S1] *> ([S0] *> encHalf lr)))) <{{C}} encHalf (push001K d rs)) -->*
               ((encHalf lr) <{{C}} (wZ *> ([S0] *> encHalf (push001K d rs))))).
  { unfold wZ; simpl Str_app; execute. }
  rewrite encHalf_push001K, encHalf_push0K.
  nat_norm. rewrite lpow_1.
  exact (ev_trans H1 H2).
Qed.

Lemma dl_frame_step (d : N) (lr rs : list Tok) :
  encode DL (b0 :: b1 :: b0 :: b1 :: w001 d :: lr) rs -->*
  encode DL lr (push001K d (push0K (push001K 0%N rs))).
Proof.
  cbn [encode encHalf].
  assert (H1 : (([S0] *> ([S1] *> ([S0] *> ([S1] *> ((wZ ^^ (N.to_nat d + 1)) *> encHalf lr))))) <{{D}} encHalf rs) -->*
               (((wZ ^^ (N.to_nat d + 1)) *> encHalf lr) <{{D}} ([S0] *> (wZ *> encHalf rs)))).
  { unfold wZ at 2; simpl Str_app; execute. }
  pose proof (walk_DL_001 (N.to_nat d + 1) (encHalf lr) ([S0] *> (wZ *> encHalf rs))) as H2.
  rewrite encHalf_push001K, encHalf_push0K, encHalf_push001K.
  nat_norm. rewrite lpow_1.
  exact (ev_trans H1 H2).
Qed.

Lemma unwindCLFuelK_sound (fuel : nat) : forall (ls rs : list Tok),
  ResSound (encode CL ls rs) (unwindCLFuelK fuel ls rs).
Proof.
  induction fuel as [|fuel IH]; intros ls rs.
  - apply evstep_refl.
  - cbn [unwindCLFuelK].
    destruct ls as [| [| | ?] [| [| | ?] [| [| | ?] [| [| | d] [| [| | ?] lr]]]]];
      try apply evstep_refl.
    exact (resSound_trans (cl_frame_step d lr rs) (IH lr _)).
Qed.

Lemma unwindDLFuelK_sound (fuel : nat) : forall (ls rs : list Tok),
  ResSound (encode DL ls rs) (unwindDLFuelK fuel ls rs).
Proof.
  induction fuel as [|fuel IH]; intros ls rs.
  - apply evstep_refl.
  - cbn [unwindDLFuelK].
    destruct ls as [| [| | ?] [| [| | ?] [| [| | ?] [| [| | ?] [| [| | d] lr]]]]];
      try apply evstep_refl.
    exact (resSound_trans (dl_frame_step d lr rs) (IH lr _)).
Qed.

Lemma stepFastK_sound (f1024 : nat) (m : WordMode) (ls rs : list Tok) :
  ResSound (encode m ls rs) (stepFastK f1024 m ls rs).
Proof.
  destruct m.
  - (* CR *)
    cbn [stepFastK].
    destruct rs as [| [| | d] rr].
    + exact (stepCRFallbackK_sound ls []).
    + exact (stepCRFallbackK_sound ls (b0 :: rr)).
    + exact (stepCRFallbackK_sound ls (b1 :: rr)).
    + cbn [ResSound encode encHalf].
      rewrite encHalf_push0K, encHalf_push1K, encHalf_pushCnt001K, encHalf_push0K.
      exact (walk_CR_001_raw (N.to_nat d) (encHalf ls) (encHalf rr)).
  - (* CL *)
    destruct ls as [| [| | ?] [| [| | ?] [| [| | ?] [| [| | d] [| [| | d5] lr]]]]];
      try apply stepCLFallbackK_sound.
    + cbn [stepFastK ResSound encode encHalf].
      rewrite encHalf_push001K.
      exact (walk_CL_101_001 (N.to_nat d + 1) (encHalf []) (encHalf rs)).
    + cbn [stepFastK].
      exact (resSound_trans (cl_frame_step d lr rs) (unwindCLFuelK_sound f1024 lr _)).
    + cbn [stepFastK ResSound encode encHalf].
      rewrite encHalf_push001K.
      exact (walk_CL_101_001 (N.to_nat d + 1) (encHalf (b1 :: lr)) (encHalf rs)).
    + cbn [stepFastK ResSound encode encHalf].
      rewrite encHalf_push001K.
      exact (walk_CL_101_001 (N.to_nat d + 1) (encHalf (w001 d5 :: lr)) (encHalf rs)).
  - (* DL *)
    destruct ls as [| [| | ?] [| [| | ?] [| [| | ?] [| [| | ?] [| [| | d] lr]]]]];
      try apply stepDLBaseK_sound.
    cbn [stepFastK].
    exact (resSound_trans (dl_frame_step d lr rs) (unwindDLFuelK_sound f1024 lr _)).
  - (* BL *)
    exact (stepBLK_sound ls rs).
  - (* HALT *)
    cbn [stepFastK ResSound encode]. apply halted_halts. reflexivity.
Qed.

Lemma stepResK_sound (f1024 : nat) {c : Q * tape} {st : StepRes}
  (H : ResSound c st) : ResSound c (stepResK f1024 st).
Proof.
  destruct st as [m ls rs | |].
  - exact (resSound_trans H (stepFastK_sound f1024 m ls rs)).
  - exact H.
  - exact H.
Qed.

Lemma runStepsK_sound (f1024 n : nat) : forall {c : Q * tape} {st : StepRes},
  ResSound c st -> ResSound c (runStepsK f1024 n st).
Proof.
  induction n as [|n IH]; intros c st H.
  - exact H.
  - cbn [runStepsK]. exact (IH c (stepResK f1024 st) (stepResK_sound f1024 H)).
Qed.

(* ========================================================================= *)
(* Section 4: Arbitrary-Depth 7^k Recursive Tower Soundness                  *)
(* ========================================================================= *)

Local Open Scope N_scope.

Fixpoint splitPairsK (k : nat) (acc : list N) (rem : list Tok) : option (list N * list Tok) :=
  match k with
  | 0%nat => Some (acc, rem)
  | S k' =>
    match rem with
    | w001 d :: b0 :: rem' => splitPairsK k' (d :: acc) rem'
    | _ => None
    end
  end.

Definition splitActiveK (k : nat) (rs : list Tok) : option (N * list N * list Tok) :=
  match rs with
  | b0 :: b1 :: w001 d0 :: b0 :: rem =>
    match splitPairsK k [] rem with
    | None => None
    | Some (revDs, tail) => Some (d0, revDs, tail)
    end
  | _ => None
  end.

Fixpoint prependPairsK (ds : list N) (tail : list Tok) : list Tok :=
  match ds with
  | [] => tail
  | d :: ds' => prependPairsK ds' (w001 d :: b0 :: tail)
  end.

Fixpoint prependPairsFwdK (ds : list N) (tail : list Tok) : list Tok :=
  match ds with
  | [] => tail
  | d :: ds' => w001 d :: b0 :: prependPairsFwdK ds' tail
  end.

Definition mkActiveK (d0 : N) (revDs : list N) (tail : list Tok) : list Tok :=
  b0 :: b1 :: w001 d0 :: b0 :: prependPairsK revDs tail.

Fixpoint subPow7K (m : N) (ds : list N) : option (list N) :=
  match ds with
  | [] => Some []
  | d :: ds_rest =>
    if N.leb (m + 1) d then
      match subPow7K (7 * m) ds_rest with
      | None => None
      | Some ds' => Some ((d - m) :: ds')
      end
    else None
  end.

Definition subPow7OptK (m : N) (ds : list N) : option (list N) :=
  if N.eqb m 0 then Some ds else subPow7K m ds.

Fixpoint extractExcessK (p7 : N) (ds : list N) : option (list N) :=
  match ds with
  | [] => Some []
  | d :: ds_rest =>
    let req := 2 * p7 + 1 in
    if N.leb req d then
      match extractExcessK (7 * p7) ds_rest with
      | None => None
      | Some es => Some ((d - req) :: es)
      end
    else None
  end.

Fixpoint framesLK (es : list N) (acc : list Tok) : list Tok :=
  match es with
  | [] => acc
  | e :: es' => b1 :: b0 :: b1 :: w001 e :: b0 :: framesLK es' acc
  end.

Definition peel4K (dc : N) (rest : list Tok) : list Tok :=
  if N.eqb dc 3 then rest else w001 (dc - 4) :: rest.

Definition towerK (k : nat) (rs : list Tok) : StepRes :=
  match k with
  | 0%nat => st_err
  | S km1 =>
    match splitActiveK km1 rs with
    | None => st_err
    | Some (d0, revDs, rem) =>
      match rem with
      | w001 dc :: rest =>
        if N.leb 3 dc then
          match extractExcessK 7 revDs with
          | None => st_err
          | Some es =>
            let d0' := d0 + N.pow 7 (N.of_nat k) in
            st_ok CR
              (b0 :: b1 :: b0 :: framesLK es [b1; b0; b1; w001 d0'; b0])
              (peel4K dc rest)
          end
        else st_err
      | _ => st_err
      end
    end
  end.

Local Open Scope nat_scope.

Fixpoint bumpExcess (p : N) (es : list N) : list N :=
  match es with
  | [] => []
  | e :: rest => (e + p)%N :: bumpExcess (7 * p)%N rest
  end.

Fixpoint framesR_raw (p7 : N) (es : list N) (tail : side) : side :=
  match es with
  | [] => tail
  | e :: rest =>
    framesR_raw (7 * p7)%N rest
      ((wZ ^^ (N.to_nat e + 2 * N.to_nat p7 + 2)) *> ([S0] *> tail))
  end.

Fixpoint framesR_inc (es : list N) (tail : side) : side :=
  match es with
  | [] => tail
  | u :: rest =>
    framesR_inc rest ((wZ ^^ (N.to_nat u + 2)) *> ([S0] *> tail))
  end.

Lemma bumpExcess_zero (es : list N) : bumpExcess 0%N es = es.
Proof.
  induction es as [|e rest IH]; [reflexivity |].
  cbn [bumpExcess]. rewrite N.add_0_r. change (7 * 0)%N with 0%N.
  rewrite IH. reflexivity.
Qed.

Lemma length_bumpExcess (es : list N) : forall (p : N),
  length (bumpExcess p es) = length es.
Proof.
  induction es as [|e rest IH]; intros p; [reflexivity |].
  cbn [bumpExcess length]. rewrite IH. reflexivity.
Qed.

Lemma framesR_raw_seven (es : list N) : forall (p7 : N) (tail : side),
  framesR_raw (7 * p7)%N es tail = framesR_raw p7 (bumpExcess (12 * p7)%N es) tail.
Proof.
  induction es as [|e rest IH]; intros p7 tail; [reflexivity |].
  cbn [framesR_raw bumpExcess].
  replace (N.to_nat (e + 12 * p7)%N + 2 * N.to_nat p7 + 2)
    with (N.to_nat e + 2 * N.to_nat (7 * p7)%N + 2) by nlia.
  replace (7 * (12 * p7))%N with (12 * (7 * p7))%N by (apply N2Nat.inj; nlia).
  apply IH.
Qed.

Lemma framesR_inc_bump (es : list N) : forall (p7 : N) (j : nat) (tail : side),
  framesR_inc (bumpExcess (N.of_nat (2 * (j + 1)) * p7)%N es) tail =
  framesR_raw p7 (bumpExcess (N.of_nat (2 * j) * p7)%N es) tail.
Proof.
  induction es as [|e rest IH]; intros p7 j tail; [reflexivity |].
  cbn [framesR_inc framesR_raw bumpExcess].
  replace (N.to_nat (e + N.of_nat (2 * (j + 1)) * p7)%N + 2)
    with (N.to_nat (e + N.of_nat (2 * j) * p7)%N + 2 * N.to_nat p7 + 2) by nlia.
  replace (7 * (N.of_nat (2 * (j + 1)) * p7))%N
    with (N.of_nat (2 * (j + 1)) * (7 * p7))%N by (apply N2Nat.inj; nlia).
  replace (7 * (N.of_nat (2 * j) * p7))%N
    with (N.of_nat (2 * j) * (7 * p7))%N by (apply N2Nat.inj; nlia).
  apply IH.
Qed.

Definition tailP (p : nat) (r : side) : side :=
  match p with
  | 0 => (wZ ^^ 4) *> r
  | 1 => [S0; S0; S1; S0; S1; S0; S0; S1; S0; S0; S1] *> r
  | 2 => [S0; S0; S1; S1; S0; S0; S1; S0; S0; S1] *> r
  | 3 => [S0; S0; S1; S0; S0; S0; S1; S0; S1] *> r
  | 4 => [S0; S0; S1; S0; S0; S1; S0; S1] *> r
  | 5 => [S0; S0; S1; S0; S1; S0; S1] *> r
  | _ => [S0; S0; S1; S1; S0; S1] *> r
  end.

Lemma sweep010_CR_001_any (e : nat) (lf r : side) :
  (([S0; S1; S0] *> lf) {{C}}> ((wZ ^^ e) *> r)) -->*
  (([S0; S1] *> ((wZ ^^ e) *> ([S0] *> lf))) {{C}}> r).
Proof.
  destruct e as [|d].
  - apply evstep_refl.
  - replace (S d) with (d + 1) by lia.
    pose proof (walk_CR_001_raw d ([S0; S1; S0] *> lf) r) as H.
    assert (Hmerge :
      [S0] *> ([S1] *> ((wZ ^^ d) *> ([S0] *> ([S0; S1; S0] *> lf)))) =
      [S0; S1] *> ((wZ ^^ (d + 1)) *> ([S0] *> lf))).
    { change ([S0] *> ([S0; S1; S0] *> lf)) with (wZ *> ([S0] *> lf)).
      rewrite <- str_lpow_S_r. reflexivity. }
    rewrite Hmerge in H. exact H.
Qed.

Lemma turn_bare_sound (k : nat) (lf r : side) :
  (([S0; S1] *> ((wZ ^^ k) *> lf)) {{C}}> ([S0] *> ([S0; S0; S1; S0; S0; S1] *> r))) -->*
  (([S1] *> ((wZ ^^ (k + 1)) *> lf)) <{{C}} ([S0; S0; S1; S0; S1] *> r)).
Proof.
  rewrite str_lpow_S. unfold wZ at 2; simpl Str_app; execute.
Qed.

Lemma turn_p0_sound (k : nat) (lf r : side) :
  (([S0; S1] *> ((wZ ^^ k) *> lf)) {{C}}> ([S0] *> ([S0; S0; S1; S0; S1] *> r))) -->*
  (([S1] *> ((wZ ^^ (k + 1)) *> lf)) <{{C}} ([S0; S0; S1; S1] *> r)).
Proof.
  rewrite str_lpow_S. unfold wZ at 2; simpl Str_app; execute.
Qed.

Lemma turn_phase_sound (p : nat) (Hp : p < 6) (k : nat) (lf r : side) :
  (([S0; S1] *> ((wZ ^^ k) *> lf)) {{C}}> ([S0] *> tailP p r)) -->*
  (([S1] *> ((wZ ^^ (k + 1)) *> lf)) <{{C}} tailP (p + 1) r).
Proof.
  rewrite str_lpow_S.
  destruct p as [|[|[|[|[|[|p]]]]]]; try lia.
  - cbn [tailP]. replace (wZ ^^ 4) with (wZ ++ wZ ++ wZ ++ wZ) by reflexivity.
    unfold wZ at 2 3 4 5 6; simpl app; simpl Str_app; execute.
  - cbn [tailP]; unfold wZ at 2; simpl Str_app; execute.
  - cbn [tailP]; unfold wZ at 2; simpl Str_app; execute.
  - cbn [tailP]; unfold wZ at 2; simpl Str_app; execute.
  - cbn [tailP]; unfold wZ at 2; simpl Str_app; execute.
  - cbn [tailP]; unfold wZ at 2; simpl Str_app; execute.
Qed.

Lemma unwind_one_frame (w u : nat) (lf r : side) :
  (([S1] *> ((wZ ^^ (w + 1)) *> ([S0] *> ([S1; S0; S1] *> ((wZ ^^ (u + 1)) *> ([S0] *> lf)))))) <{{C}} r) -->*
  (([S1] *> ((wZ ^^ (u + 1)) *> ([S0] *> lf))) <{{C}} ((wZ ^^ (w + 2)) *> ([S0] *> r))).
Proof.
  assert (H1 :
    (([S1] *> ((wZ ^^ (w + 1)) *> ([S0] *> ([S1; S0; S1] *> ((wZ ^^ (u + 1)) *> ([S0] *> lf)))))) <{{C}} r) -->*
    (((wZ ^^ (w + 1)) *> ([S0] *> ([S1; S0; S1] *> ((wZ ^^ (u + 1)) *> ([S0] *> lf))))) <{{D}} ([S0] *> r))).
  { simpl Str_app; execute. }
  pose proof (walk_DL_001 (w + 1)
    ([S0] *> ([S1; S0; S1] *> ((wZ ^^ (u + 1)) *> ([S0] *> lf)))) ([S0] *> r)) as H2.
  assert (H3 :
    (([S0] *> ([S1; S0; S1] *> ((wZ ^^ (u + 1)) *> ([S0] *> lf)))) <{{D}}
      ((wZ ^^ (w + 1)) *> ([S0] *> r))) -->*
    (([S1] *> ((wZ ^^ (u + 1)) *> ([S0] *> lf))) <{{C}}
      (wZ *> ((wZ ^^ (w + 1)) *> ([S0] *> r))))).
  { unfold wZ at 3; simpl Str_app; execute. }
  replace (w + 2) with ((w + 1) + 1) by lia.
  rewrite (str_lpow_S wZ (w + 1)).
  exact (ev_trans (ev_trans H1 H2) H3).
Qed.

Lemma unwind_bottom (w : nat) (r : side) :
  (([S1] *> ((wZ ^^ (w + 1)) *> ([S0] *> const S0))) <{{C}} r) -->*
  (const S0 <{{C}} ([S0; S1] *> ((wZ ^^ (w + 1)) *> ([S0] *> r)))).
Proof.
  assert (H1 :
    (([S1] *> ((wZ ^^ (w + 1)) *> ([S0] *> const S0))) <{{C}} r) -->*
    (((wZ ^^ (w + 1)) *> ([S0] *> const S0)) <{{D}} ([S0] *> r))).
  { simpl Str_app; execute. }
  pose proof (walk_DL_001 (w + 1) ([S0] *> const S0) ([S0] *> r)) as H2.
  assert (H3 :
    (([S0] *> const S0) <{{D}} ((wZ ^^ (w + 1)) *> ([S0] *> r))) -->*
    (const S0 <{{C}} ([S0; S1] *> ((wZ ^^ (w + 1)) *> ([S0] *> r))))).
  { rewrite <- cons_zero_const0 at 1. simpl Str_app; execute. }
  exact (ev_trans (ev_trans H1 H2) H3).
Qed.

Lemma unwind_framesL (us : list N) : forall (w : nat) (dBot : N) (r : side),
  (([S1] *> ((wZ ^^ (w + 1)) *>
    ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])))) <{{C}} r) -->*
  (const S0 <{{C}}
    ([S0; S1] *> ((wZ ^^ (N.to_nat dBot + 1)) *>
      ([S0] *> framesR_inc us ((wZ ^^ (w + 2)) *> ([S0] *> r)))))).
Proof.
  induction us as [|u rest IH]; intros w dBot r.
  - cbn [framesLK framesR_inc encHalf].
    change ([S1] *> ([S0] *> ([S1] *> ((wZ ^^ (N.to_nat dBot + 1)) *> ([S0] *> const S0)))))
      with ([S1; S0; S1] *> ((wZ ^^ (N.to_nat dBot + 1)) *> ([S0] *> const S0))).
    exact (ev_trans
      (unwind_one_frame w (N.to_nat dBot) (const S0) r)
      (unwind_bottom (N.to_nat dBot) ((wZ ^^ (w + 2)) *> ([S0] *> r)))).
  - cbn [framesLK framesR_inc].
    change (encHalf (b1 :: b0 :: b1 :: w001 u :: b0 :: framesLK rest [b1; b0; b1; w001 dBot; b0]))
      with ([S1; S0; S1] *> ((wZ ^^ (N.to_nat u + 1)) *>
        ([S0] *> encHalf (framesLK rest [b1; b0; b1; w001 dBot; b0])))).
    exact (ev_trans
      (unwind_one_frame w (N.to_nat u) (encHalf (framesLK rest [b1; b0; b1; w001 dBot; b0])) r)
      (IH (N.to_nat u) dBot ((wZ ^^ (w + 2)) *> ([S0] *> r)))).
Qed.

Lemma inter_cycle_sound (p : nat) (Hp : p < 6) (us : list N) (dBot : N) (zm1 : nat) (r : side) :
  ((encHalf (b0 :: b1 :: b0 :: framesLK us [b1; b0; b1; w001 dBot; b0])) {{C}}>
    ((wZ ^^ (zm1 + 1)) *> ([S0] *> tailP p r))) -->*
  (const S0 <{{C}}
    ([S0; S1] *> ((wZ ^^ (N.to_nat dBot + 1)) *>
      ([S0] *> framesR_inc us ((wZ ^^ (zm1 + 3)) *> ([S0] *> tailP (p + 1) r)))))).
Proof.
  change (encHalf (b0 :: b1 :: b0 :: framesLK us [b1; b0; b1; w001 dBot; b0]))
    with ([S0; S1; S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])).
  pose proof (sweep010_CR_001_any (zm1 + 1)
    (encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])) ([S0] *> tailP p r)) as H1.
  pose proof (turn_phase_sound p Hp (zm1 + 1)
    ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])) r) as H2.
  pose proof (unwind_framesL us (zm1 + 1) dBot (tailP (p + 1) r)) as H3.
  replace (zm1 + 1 + 2) with (zm1 + 3) in H3 by lia.
  exact (ev_trans (ev_trans H1 H2) H3).
Qed.

Lemma p5_exit_step (e : nat) (lf r : side) :
  (([S0; S1] *> ((wZ ^^ e) *> lf)) {{C}}> ([S0] *> tailP 6 r)) -->*
  (([S0; S1; S0; S1; S0; S1] *> ((wZ ^^ (e + 1)) *> lf)) {{C}}> r).
Proof.
  rewrite str_lpow_S. cbn [tailP]; unfold wZ at 2; simpl Str_app; execute.
Qed.

Lemma tail_exit_sound (e : nat) (lf r : side) :
  (([S0; S1; S0] *> lf) {{C}}> ((wZ ^^ e) *> ([S0] *> tailP 6 r))) -->*
  (([S0; S1; S0; S1; S0; S1] *> ((wZ ^^ (e + 1)) *> ([S0] *> lf))) {{C}}> r).
Proof.
  exact (ev_trans (sweep010_CR_001_any e lf ([S0] *> tailP 6 r)) (p5_exit_step e ([S0] *> lf) r)).
Qed.

Lemma base_bounce_sound (p : nat) (Hp : p < 6) (d : nat) (r : side) :
  (const S0 <{{C}} ([S0; S1] *> ((wZ ^^ (d + 1)) *> ([S0] *> tailP p r)))) -->*
  (const S0 <{{C}} ([S0; S1] *> ((wZ ^^ (d + 2)) *> ([S0] *> tailP (p + 1) r)))).
Proof.
  assert (H0 :
    (const S0 <{{C}} ([S0; S1] *> ((wZ ^^ (d + 1)) *> ([S0] *> tailP p r)))) -->*
    (([S0; S1; S0] *> const S0) {{C}}> ((wZ ^^ (d + 1)) *> ([S0] *> tailP p r)))).
  { rewrite <- cons_zero_const0 at 1. simpl Str_app; execute. }
  pose proof (sweep010_CR_001_any (d + 1) (const S0) ([S0] *> tailP p r)) as H1.
  pose proof (turn_phase_sound p Hp (d + 1) ([S0] *> const S0) r) as H2.
  pose proof (unwind_bottom (d + 1) (tailP (p + 1) r)) as H3.
  replace (d + 1 + 1) with (d + 2) in H2, H3 by lia.
  exact (ev_trans (ev_trans (ev_trans H0 H1) H2) H3).
Qed.

Lemma tower_base_sound (d0 : N) (r : side) :
  (const S0 <{{C}} ([S0; S1] *> ((wZ ^^ (N.to_nat d0 + 1)) *> ([S0] *> tailP 0 r)))) -->*
  ((encHalf (b0 :: b1 :: b0 :: framesLK [] [b1; b0; b1; w001 (d0 + 7)%N; b0])) {{C}}> r).
Proof.
  set (d := N.to_nat d0).
  pose proof (base_bounce_sound 0 ltac:(lia) d r) as Hb0.
  pose proof (base_bounce_sound 1 ltac:(lia) (d + 1) r) as Hb1.
  pose proof (base_bounce_sound 2 ltac:(lia) (d + 2) r) as Hb2.
  pose proof (base_bounce_sound 3 ltac:(lia) (d + 3) r) as Hb3.
  pose proof (base_bounce_sound 4 ltac:(lia) (d + 4) r) as Hb4.
  pose proof (base_bounce_sound 5 ltac:(lia) (d + 5) r) as Hb5.
  replace (d + 1 + 1) with (d + 2) in Hb1 by lia.
  replace (d + 1 + 2) with (d + 3) in Hb1 by lia.
  replace (d + 2 + 2) with (d + 4) in Hb2 by lia.
  replace (d + 3 + 2) with (d + 5) in Hb3 by lia.
  replace (d + 4 + 2) with (d + 6) in Hb4 by lia.
  replace (d + 5 + 2) with (d + 7) in Hb5 by lia.
  replace (d + 2 + 1) with (d + 3) in Hb2 by lia.
  replace (d + 3 + 1) with (d + 4) in Hb3 by lia.
  replace (d + 4 + 1) with (d + 5) in Hb4 by lia.
  replace (d + 5 + 1) with (d + 6) in Hb5 by lia.
  assert (Hstart7 :
    (const S0 <{{C}} ([S0; S1] *> ((wZ ^^ (d + 7)) *> ([S0] *> tailP 6 r)))) -->*
    (([S0; S1; S0] *> const S0) {{C}}> ((wZ ^^ (d + 7)) *> ([S0] *> tailP 6 r)))).
  { rewrite <- cons_zero_const0 at 1. simpl Str_app; execute. }
  pose proof (tail_exit_sound (d + 7) (const S0) r) as Hexit.
  cbn [framesLK encHalf].
  replace (N.to_nat (d0 + 7)%N + 1) with (d + 7 + 1) by (unfold d; nlia).
  change ([S0] *> ([S1] *> ([S0] *> ([S1] *> ([S0] *> ([S1] *> ((wZ ^^ (d + 7 + 1)) *> ([S0] *> const S0))))))))
    with ([S0; S1; S0; S1; S0; S1] *> ((wZ ^^ (d + 7 + 1)) *> ([S0] *> const S0))).
  exact (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans Hb0 Hb1) Hb2) Hb3) Hb4) Hb5) Hstart7) Hexit).
Qed.

Lemma pow4_split (m : nat) (s : side) :
  (wZ ^^ (m + 4)) *> s = tailP 0 ((wZ ^^ m) *> s).
Proof.
  cbn [tailP]. replace (m + 4) with (4 + m) by lia.
  apply str_lpow_add.
Qed.

Lemma tower_raw_sound_len (n : nat) : forall (es : list N) (d0 : N) (r : side),
  length es = n ->
  (const S0 <{{C}}
    ([S0; S1] *> ((wZ ^^ (N.to_nat d0 + 1)) *>
      ([S0] *> framesR_raw 7%N es (tailP 0 r))))) -->*
  ((encHalf (b0 :: b1 :: b0 :: framesLK es
      [b1; b0; b1; w001 (d0 + N.pow 7%N (N.of_nat (n + 1)))%N; b0])) {{C}}> r).
Proof.
  induction n as [|n IH]; intros es d0 r Hlen.
  - destruct es as [|? ?]; [| simpl in Hlen; lia].
    simpl (0 + 1). change (N.pow 7%N (N.of_nat 1)) with 7%N.
    exact (tower_base_sound d0 r).
  - destruct es as [|e rest]; [simpl in Hlen; lia |].
    simpl in Hlen. assert (Hrest : length rest = n) by lia. clear Hlen.
    set (P := N.pow 7%N (N.of_nat (n + 1))).
    assert (Hin0 :
      framesR_raw 7%N (e :: rest) (tailP 0 r) =
      framesR_raw 7%N (bumpExcess (N.of_nat (2 * 6) * 7)%N rest)
        (tailP 0 ((wZ ^^ (N.to_nat e + 12)) *> ([S0] *> tailP 0 r)))).
    { cbn [framesR_raw]. rewrite (framesR_raw_seven rest 7%N).
      replace (12 * 7)%N with (N.of_nat (2 * 6) * 7)%N by reflexivity.
      replace (N.to_nat e + 2 * N.to_nat 7%N + 2) with ((N.to_nat e + 12) + 4) by nlia.
      rewrite pow4_split. reflexivity. }
    rewrite Hin0.
    pose proof (IH (bumpExcess (N.of_nat (2 * 6) * 7)%N rest) d0
      ((wZ ^^ (N.to_nat e + 12)) *> ([S0] *> tailP 0 r))
      ltac:(rewrite length_bumpExcess; exact Hrest)) as Hc0.
    fold P in Hc0.
    replace (N.to_nat e + 12) with ((N.to_nat e + 11) + 1) in Hc0 |- * by lia.
    pose proof (inter_cycle_sound 0 ltac:(lia) (bumpExcess (N.of_nat (2 * 6) * 7)%N rest)
      (d0 + P)%N (N.to_nat e + 11) r) as Hi0.
    replace (N.to_nat e + 11 + 3) with ((N.to_nat e + 10) + 4) in Hi0 by lia.
    rewrite pow4_split in Hi0.
    change (2 * 6) with (2 * (5 + 1)) in Hi0.
    rewrite (framesR_inc_bump rest 7%N 5) in Hi0.

    pose proof (IH (bumpExcess (N.of_nat (2 * 5) * 7)%N rest) (d0 + P)%N
      ((wZ ^^ (N.to_nat e + 10)) *> ([S0] *> tailP 1 r))
      ltac:(rewrite length_bumpExcess; exact Hrest)) as Hc1.
    fold P in Hc1.
    replace (d0 + P + P)%N with (d0 + 2 * P)%N in Hc1 by (apply N2Nat.inj; nlia).
    replace (N.to_nat e + 10) with ((N.to_nat e + 9) + 1) in Hi0, Hc1 by lia.
    pose proof (inter_cycle_sound 1 ltac:(lia) (bumpExcess (N.of_nat (2 * 5) * 7)%N rest)
      (d0 + 2 * P)%N (N.to_nat e + 9) r) as Hi1.
    replace (N.to_nat e + 9 + 3) with ((N.to_nat e + 8) + 4) in Hi1 by lia.
    rewrite pow4_split in Hi1.
    change (2 * 5) with (2 * (4 + 1)) in Hi1.
    rewrite (framesR_inc_bump rest 7%N 4) in Hi1.

    pose proof (IH (bumpExcess (N.of_nat (2 * 4) * 7)%N rest) (d0 + 2 * P)%N
      ((wZ ^^ (N.to_nat e + 8)) *> ([S0] *> tailP 2 r))
      ltac:(rewrite length_bumpExcess; exact Hrest)) as Hc2.
    fold P in Hc2.
    replace (d0 + 2 * P + P)%N with (d0 + 3 * P)%N in Hc2 by (apply N2Nat.inj; nlia).
    replace (N.to_nat e + 8) with ((N.to_nat e + 7) + 1) in Hi1, Hc2 by lia.
    pose proof (inter_cycle_sound 2 ltac:(lia) (bumpExcess (N.of_nat (2 * 4) * 7)%N rest)
      (d0 + 3 * P)%N (N.to_nat e + 7) r) as Hi2.
    replace (N.to_nat e + 7 + 3) with ((N.to_nat e + 6) + 4) in Hi2 by lia.
    rewrite pow4_split in Hi2.
    change (2 * 4) with (2 * (3 + 1)) in Hi2.
    rewrite (framesR_inc_bump rest 7%N 3) in Hi2.

    pose proof (IH (bumpExcess (N.of_nat (2 * 3) * 7)%N rest) (d0 + 3 * P)%N
      ((wZ ^^ (N.to_nat e + 6)) *> ([S0] *> tailP 3 r))
      ltac:(rewrite length_bumpExcess; exact Hrest)) as Hc3.
    fold P in Hc3.
    replace (d0 + 3 * P + P)%N with (d0 + 4 * P)%N in Hc3 by (apply N2Nat.inj; nlia).
    replace (N.to_nat e + 6) with ((N.to_nat e + 5) + 1) in Hi2, Hc3 by lia.
    pose proof (inter_cycle_sound 3 ltac:(lia) (bumpExcess (N.of_nat (2 * 3) * 7)%N rest)
      (d0 + 4 * P)%N (N.to_nat e + 5) r) as Hi3.
    replace (N.to_nat e + 5 + 3) with ((N.to_nat e + 4) + 4) in Hi3 by lia.
    rewrite pow4_split in Hi3.
    change (2 * 3) with (2 * (2 + 1)) in Hi3.
    rewrite (framesR_inc_bump rest 7%N 2) in Hi3.

    pose proof (IH (bumpExcess (N.of_nat (2 * 2) * 7)%N rest) (d0 + 4 * P)%N
      ((wZ ^^ (N.to_nat e + 4)) *> ([S0] *> tailP 4 r))
      ltac:(rewrite length_bumpExcess; exact Hrest)) as Hc4.
    fold P in Hc4.
    replace (d0 + 4 * P + P)%N with (d0 + 5 * P)%N in Hc4 by (apply N2Nat.inj; nlia).
    replace (N.to_nat e + 4) with ((N.to_nat e + 3) + 1) in Hi3, Hc4 by lia.
    pose proof (inter_cycle_sound 4 ltac:(lia) (bumpExcess (N.of_nat (2 * 2) * 7)%N rest)
      (d0 + 5 * P)%N (N.to_nat e + 3) r) as Hi4.
    replace (N.to_nat e + 3 + 3) with ((N.to_nat e + 2) + 4) in Hi4 by lia.
    rewrite pow4_split in Hi4.
    change (2 * 2) with (2 * (1 + 1)) in Hi4.
    rewrite (framesR_inc_bump rest 7%N 1) in Hi4.

    pose proof (IH (bumpExcess (N.of_nat (2 * 1) * 7)%N rest) (d0 + 5 * P)%N
      ((wZ ^^ (N.to_nat e + 2)) *> ([S0] *> tailP 5 r))
      ltac:(rewrite length_bumpExcess; exact Hrest)) as Hc5.
    fold P in Hc5.
    replace (d0 + 5 * P + P)%N with (d0 + 6 * P)%N in Hc5 by (apply N2Nat.inj; nlia).
    replace (N.to_nat e + 2) with ((N.to_nat e + 1) + 1) in Hi4, Hc5 by lia.
    pose proof (inter_cycle_sound 5 ltac:(lia) (bumpExcess (N.of_nat (2 * 1) * 7)%N rest)
      (d0 + 6 * P)%N (N.to_nat e + 1) r) as Hi5.
    replace (N.to_nat e + 1 + 3) with (N.to_nat e + 4) in Hi5 by lia.
    rewrite pow4_split in Hi5.
    change (2 * 1) with (2 * (0 + 1)) in Hi5.
    rewrite (framesR_inc_bump rest 7%N 0) in Hi5.
    change (N.of_nat (2 * 0) * 7)%N with 0%N in Hi5.
    rewrite bumpExcess_zero in Hi5.

    pose proof (IH rest (d0 + 6 * P)%N
      ((wZ ^^ N.to_nat e) *> ([S0] *> tailP 6 r)) Hrest) as Hc6.
    fold P in Hc6.
    replace (d0 + 6 * P + P)%N with (d0 + 7 * P)%N in Hc6 by (apply N2Nat.inj; nlia).
    pose proof (tail_exit_sound (N.to_nat e)
      (encHalf (framesLK rest [b1; b0; b1; w001 (d0 + 7 * P)%N; b0])) r) as Hexit.
    assert (Hout :
      encHalf (b0 :: b1 :: b0 :: framesLK (e :: rest)
        [b1; b0; b1; w001 (d0 + N.pow 7%N (N.of_nat (S n + 1)))%N; b0]) =
      [S0; S1; S0; S1; S0; S1] *> ((wZ ^^ (N.to_nat e + 1)) *>
        ([S0] *> encHalf (framesLK rest [b1; b0; b1; w001 (d0 + 7 * P)%N; b0])))).
    { cbn [framesLK].
      replace (d0 + N.pow 7%N (N.of_nat (S n + 1)))%N with (d0 + 7 * P)%N.
      - reflexivity.
      - unfold P. apply N2Nat.inj. nat_norm.
        replace (S n + 1) with (S (n + 1)) by lia.
        simpl (Nat.pow 7 (S (n + 1))). lia. }
    rewrite Hout.
    exact (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans
            (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans Hc0 Hi0) Hc1) Hi1) Hc2) Hi2) Hc3) Hi3)
            Hc4) Hi4) Hc5) Hi5) Hc6) Hexit).
Qed.

Lemma tower_raw_sound (es : list N) (d0 : N) (r : side) :
  (const S0 <{{C}}
    ([S0; S1] *> ((wZ ^^ (N.to_nat d0 + 1)) *>
      ([S0] *> framesR_raw 7%N es (tailP 0 r))))) -->*
  ((encHalf (b0 :: b1 :: b0 :: framesLK es
      [b1; b0; b1; w001 (d0 + N.pow 7%N (N.of_nat (length es + 1)))%N; b0])) {{C}}> r).
Proof.
  exact (tower_raw_sound_len (length es) es d0 r eq_refl).
Qed.

(* ========================================================================= *)
(* Section 5: Active-Stack Splitting & towerK Soundness                      *)
(* ========================================================================= *)

Lemma splitPairsK_sound (k : nat) : forall (acc : list N) (rem : list Tok)
  {revDs : list N} {tail : list Tok},
  splitPairsK k acc rem = Some (revDs, tail) ->
  length revDs = k + length acc /\ prependPairsK revDs tail = prependPairsK acc rem.
Proof.
  induction k as [|k IH]; intros acc rem revDs tail H.
  - cbn [splitPairsK] in H. injection H as H1 H2; subst. split; [lia | reflexivity].
  - cbn [splitPairsK] in H.
    destruct rem as [| [| | d] [| [| | ?] rem']]; try discriminate H.
    destruct (IH (d :: acc) rem' revDs tail H) as [Hlen Hpre].
    simpl in Hlen. split; [lia | exact Hpre].
Qed.

Lemma splitActiveK_sound (k : nat) (rs : list Tok)
  {d0 : N} {revDs : list N} {tail : list Tok}
  (H : splitActiveK k rs = Some (d0, revDs, tail)) :
  length revDs = k /\ rs = mkActiveK d0 revDs tail.
Proof.
  unfold splitActiveK in H.
  destruct rs as [| [| | ?] [| [| | ?] [| [| | d] [| [| | ?] rem]]]]; try discriminate H.
  destruct (splitPairsK k [] rem) as [[rv tl] |] eqn:Hs; [| discriminate H].
  injection H as H1 H2 H3; subst.
  destruct (splitPairsK_sound k [] rem Hs) as [Hlen Hpre].
  simpl in Hlen. split; [lia |].
  unfold mkActiveK. rewrite Hpre. reflexivity.
Qed.

Lemma extractExcessK_sound (revDs : list N) : forall (p7 : N) {es : list N} (rem : list Tok),
  extractExcessK p7 revDs = Some es ->
  length es = length revDs /\ encHalf (prependPairsK revDs rem) = framesR_raw p7 es (encHalf rem).
Proof.
  induction revDs as [|d ds IH]; intros p7 es rem H.
  - cbn [extractExcessK] in H. injection H as H'; subst es. split; reflexivity.
  - cbn [extractExcessK] in H.
    destruct (N.leb (2 * p7 + 1)%N d) eqn:Hle; [| discriminate H].
    apply N_leb_true_nat in Hle.
    destruct (extractExcessK (7 * p7)%N ds) as [es' |] eqn:Hex; [| discriminate H].
    injection H as H'; subst es.
    destruct (IH (7 * p7)%N es' (w001 d :: b0 :: rem) Hex) as [Hlen Henc].
    split; [simpl; lia |].
    cbn [prependPairsK framesR_raw]. rewrite Henc.
    cbn [encHalf].
    replace (N.to_nat d + 1)
      with (N.to_nat (d - (2 * p7 + 1))%N + 2 * N.to_nat p7 + 2) by nlia.
    reflexivity.
Qed.

Lemma encHalf_peel4K (dc : N) (rest : list Tok) (Hge : 3 <= N.to_nat dc) :
  encHalf (w001 dc :: rest) = tailP 0 (encHalf (peel4K dc rest)).
Proof.
  unfold peel4K. destruct (N.eqb dc 3%N) eqn:H3.
  - apply N_eqb_eq_true in H3; subst dc. reflexivity.
  - apply N_eqb_false_nat in H3.
    cbn [encHalf tailP].
    replace (N.to_nat dc + 1) with (4 + (N.to_nat (dc - 4)%N + 1)) by nlia.
    apply str_lpow_add.
Qed.

Lemma towerK_sound (k : nat) (rs : list Tok) :
  towerK k rs <> st_err -> ResSound (encode CL [] rs) (towerK k rs).
Proof.
  intros Hne. unfold towerK in *.
  destruct k as [|km1]; [exfalso; apply Hne; reflexivity |].
  destruct (splitActiveK km1 rs) as [[[d0 revDs] rem] |] eqn:Hsp;
    [| exfalso; apply Hne; reflexivity].
  destruct rem as [| [| | dc] rest]; try (exfalso; apply Hne; reflexivity).
  destruct (N.leb 3%N dc) eqn:H3; [| exfalso; apply Hne; reflexivity].
  apply N_leb_true_nat in H3. nat_norm.
  destruct (extractExcessK 7%N revDs) as [es |] eqn:Hex;
    [| exfalso; apply Hne; reflexivity].
  cbn [ResSound encode].
  destruct (splitActiveK_sound km1 rs Hsp) as [HlenR Hreq].
  destruct (extractExcessK_sound revDs 7%N (w001 dc :: rest) Hex) as [HlenE Henc].
  rewrite Hreq. cbn [mkActiveK encHalf].
  rewrite Henc, (encHalf_peel4K dc rest H3).
  pose proof (tower_raw_sound es d0 (encHalf (peel4K dc rest))) as Htw.
  replace (length es + 1) with (S km1) in Htw by lia.
  exact Htw.
Qed.

(* ========================================================================= *)
(* Section 6: Base-6 Phase-Carry & Base-7 Horner Waves                       *)
(* ========================================================================= *)

Local Open Scope N_scope.

Fixpoint carryFuelK (fuel : nat) (tail : list Tok) : option (list N * list Tok) :=
  match fuel with
  | 0%nat => None
  | S fuel' =>
    match tail with
    | w001 x :: rest =>
      if N.eqb x 0 then
        match rest with
        | b0 :: r1 =>
          match r1 with
          | w001 y :: b0 :: b1 :: r =>
            if N.eqb y 0 then Some ([], w001 1 :: b0 :: b1 :: r) else None
          | b1 :: r2 =>
            match r2 with
            | b0 :: b1 :: r => Some ([], w001 0 :: b1 :: b0 :: b1 :: r)
            | _ => Some ([], w001 0 :: b1 :: r2)
            end
          | _ => None
          end
        | b1 :: r1 =>
          match r1 with
          | b0 :: b1 :: w001 z :: b0 :: r =>
            match carryFuelK fuel' r with
            | None => None
            | Some (absFwd, r') => Some ((z + 2) :: absFwd, r')
            end
          | w001 z :: r =>
            if N.leb 2 z then
              Some ([], w001 0 :: b0 :: w001 0 :: b0 :: b1 :: w001 (z - 2) :: r)
            else None
          | _ => None
          end
        | _ => None
        end
      else if N.eqb x 1 then
        match rest with
        | b0 :: b1 :: r => Some ([], w001 0 :: b0 :: b1 :: b0 :: b1 :: r)
        | _ => None
        end
      else
        if N.leb 2 x then
          Some ([], w001 0 :: b0 :: b1 :: w001 (x - 2) :: rest)
        else None
    | _ => None
    end
  end.

Fixpoint carryNK (f512 q : nat) (tail : list Tok) : option (list Tok) :=
  match q with
  | 0%nat => Some tail
  | S q' =>
    match carryFuelK f512 tail with
    | Some ([], tail') => carryNK f512 q' tail'
    | _ => None
    end
  end.

Fixpoint carryUntilAbsK (f512 fuel : nat) (c : N) (tail : list Tok)
  : option (N * list N * list Tok) :=
  match fuel with
  | 0%nat => None
  | S fuel' =>
    match carryFuelK f512 tail with
    | None => None
    | Some ([], tail') => carryUntilAbsK f512 fuel' (c + 1) tail'
    | Some (a :: abs_rest, tail') => Some (c + 1, a :: abs_rest, tail')
    end
  end.

Fixpoint upChainAuxK (f512 eb : nat) (tail : list Tok) : option (N * list N * list Tok) :=
  match eb with
  | 0%nat => Some (0, [], tail)
  | S eb' =>
    match carryUntilAbsK f512 7%nat 0 tail with
    | None => None
    | Some (c, abs1, tail1) =>
      match upChainAuxK f512 eb' tail1 with
      | None => None
      | Some (S_rest, restFwd, tail2) =>
        if N.eqb S_rest 0 then
          Some (c, abs1 ++ restFwd, tail2)
        else
          let abs1_rev := rev_append abs1 [] in
          match subPow7K (2 * S_rest) abs1_rev with
          | None => None
          | Some abs1_rev' =>
            let S_tot := c + S_rest * N.pow 7 (N.of_nat (length abs1)) in
            Some (S_tot, rev_append abs1_rev' [] ++ restFwd, tail2)
          end
      end
    end
  end.

Definition upChainK (f512 k eb : nat) (rs : list Tok) : StepRes :=
  match splitActiveK k rs with
  | None => st_err
  | Some (d0, revDs, tail) =>
    match upChainAuxK f512 eb tail with
    | None => st_err
    | Some (S_val, fwdAbs, tail') =>
      match subPow7OptK (2 * S_val) revDs with
      | None => st_err
      | Some revDs' =>
        let d0' := d0 + S_val * N.pow 7 (N.of_nat k) in
        st_ok CL [] (mkActiveK d0' revDs' (prependPairsFwdK fwdAbs tail'))
      end
    end
  end.

Definition mod8 (c : N) : nat :=
  match c with
  | N0 => 0%nat
  | Npos xH => 1%nat
  | Npos (xO xH) => 2%nat
  | Npos (xI xH) => 3%nat
  | Npos (xO (xO xH)) => 4%nat
  | Npos (xI (xO xH)) => 5%nat
  | Npos (xO (xI xH)) => 6%nat
  | Npos (xI (xI xH)) => 7%nat
  | Npos (xO (xO (xO _))) => 0%nat
  | Npos (xI (xO (xO _))) => 1%nat
  | Npos (xO (xI (xO _))) => 2%nat
  | Npos (xI (xI (xO _))) => 3%nat
  | Npos (xO (xO (xI _))) => 4%nat
  | Npos (xI (xO (xI _))) => 5%nat
  | Npos (xO (xI (xI _))) => 6%nat
  | Npos (xI (xI (xI _))) => 7%nat
  end.

Definition div8 (c : N) : N :=
  match c with
  | Npos (xO (xO (xO p)))
  | Npos (xI (xO (xO p)))
  | Npos (xO (xI (xO p)))
  | Npos (xI (xI (xO p)))
  | Npos (xO (xO (xI p)))
  | Npos (xI (xO (xI p)))
  | Npos (xO (xI (xI p)))
  | Npos (xI (xI (xI p))) => Npos p
  | _ => N0
  end.

Fixpoint downChainAuxK (f512 len : nat) (code T : N) (revDs : list N) (tail : list Tok)
  : option (N * list N * list Tok) :=
  match len with
  | 0%nat => Some (T, revDs, tail)
  | 1%nat =>
    let q := mod8 code in
    match carryNK f512 q tail with
    | None => None
    | Some tail' => Some (T + N.of_nat q, revDs, tail')
    end
  | S (S _ as len') =>
    let q := mod8 code in
    let code' := div8 code in
    match carryNK f512 q tail with
    | None => None
    | Some tail' =>
      let Tq := T + N.of_nat q in
      match revDs with
      | [] => None
      | d_top :: revDs' =>
        if N.eqb Tq 0 then
          downChainAuxK f512 len' code' 0 revDs' (w001 d_top :: b0 :: tail')
        else
          let loss := 2 * Tq in
          if N.leb (loss + 1) d_top then
            downChainAuxK f512 len' code' (7 * Tq) revDs' (w001 (d_top - loss) :: b0 :: tail')
          else None
      end
    end
  end.

Definition downChainK (f512 k len : nat) (code : N) (rs : list Tok) : StepRes :=
  match splitActiveK k rs with
  | None => st_err
  | Some (d0, revDs, tail) =>
    match downChainAuxK f512 len code 0 revDs tail with
    | None => st_err
    | Some (T_fin, revDs_fin, tail_fin) =>
      match subPow7OptK (2 * T_fin) revDs_fin with
      | None => st_err
      | Some revDs_out =>
        let d0' := d0 + T_fin * N.pow 7 (N.of_nat (length revDs_fin)) in
        st_ok CL [] (mkActiveK d0' revDs_out tail_fin)
      end
    end
  end.

Local Open Scope nat_scope.

Lemma pow7_pos (k : nat) : 1 <= Nat.pow 7 k.
Proof.
  induction k as [|k IH]; [simpl; lia | simpl (Nat.pow 7 (S k)); lia].
Qed.

Lemma prependPairsFwdK_append (xs : list N) : forall (ys : list N) (tail : list Tok),
  prependPairsFwdK (xs ++ ys) tail = prependPairsFwdK xs (prependPairsFwdK ys tail).
Proof.
  induction xs as [|x xs IH]; intros ys tail; [reflexivity |].
  simpl app. cbn [prependPairsFwdK]. rewrite IH. reflexivity.
Qed.

Lemma prependPairsK_append (xs : list N) : forall (ys : list N) (tail : list Tok),
  prependPairsK (xs ++ ys) tail = prependPairsK ys (prependPairsK xs tail).
Proof.
  induction xs as [|x xs IH]; intros ys tail; [reflexivity |].
  simpl app. cbn [prependPairsK]. apply IH.
Qed.

Lemma prependPairsK_rev (xs : list N) : forall (tail : list Tok),
  prependPairsK (rev xs) tail = prependPairsFwdK xs tail.
Proof.
  induction xs as [|x xs IH]; intros tail; [reflexivity |].
  simpl rev. rewrite prependPairsK_append. cbn [prependPairsK prependPairsFwdK].
  rewrite IH. reflexivity.
Qed.

Lemma subPow7K_len (ds : list N) : forall (m : N) {ds' : list N},
  subPow7K m ds = Some ds' -> length ds' = length ds.
Proof.
  induction ds as [|d ds IH]; intros m ds' H.
  - cbn [subPow7K] in H. injection H as H'; subst. reflexivity.
  - cbn [subPow7K] in H.
    destruct (N.leb (m + 1)%N d); [| discriminate H].
    destruct (subPow7K (7 * m)%N ds) as [rest' |] eqn:Hs; [| discriminate H].
    injection H as H'; subst. simpl. f_equal. exact (IH (7 * m)%N rest' Hs).
Qed.

Lemma subPow7OptK_len (m : N) (ds : list N) {ds' : list N}
  (H : subPow7OptK m ds = Some ds') : length ds' = length ds.
Proof.
  unfold subPow7OptK in H.
  destruct (N.eqb m 0%N).
  - injection H as H'; subst. reflexivity.
  - exact (subPow7K_len ds m H).
Qed.

Lemma subPow7K_add (ds : list N) : forall (m1 m2 : N) {ds'' : list N},
  subPow7K (m1 + m2)%N ds = Some ds'' ->
  exists ds', subPow7K m1 ds = Some ds' /\ subPow7K m2 ds' = Some ds''.
Proof.
  induction ds as [|d ds IH]; intros m1 m2 ds'' H.
  - cbn [subPow7K] in H. injection H as H'; subst. exists (@nil N). split; reflexivity.
  - cbn [subPow7K] in H.
    destruct (N.leb (m1 + m2 + 1)%N d) eqn:Hle; [| discriminate H].
    apply N_leb_true_nat in Hle.
    destruct (subPow7K (7 * (m1 + m2))%N ds) as [rest'' |] eqn:Hs; [| discriminate H].
    injection H as H'; subst ds''.
    replace (7 * (m1 + m2))%N with (7 * m1 + 7 * m2)%N in Hs by (apply N2Nat.inj; nlia).
    destruct (IH (7 * m1)%N (7 * m2)%N rest'' Hs) as [rest' [H1 H2]].
    exists ((d - m1)%N :: rest'). split.
    + cbn [subPow7K].
      rewrite (N_leb_true_intro (m1 + 1)%N d ltac:(nlia)), H1. reflexivity.
    + cbn [subPow7K].
      rewrite (N_leb_true_intro (m2 + 1)%N (d - m1)%N ltac:(nlia)), H2.
      f_equal. f_equal. apply N2Nat.inj. nlia.
Qed.

Lemma subPow7OptK_add (m1 m2 : N) (ds : list N) {ds'' : list N}
  (H : subPow7OptK (m1 + m2)%N ds = Some ds'') :
  exists ds', subPow7OptK m1 ds = Some ds' /\ subPow7OptK m2 ds' = Some ds''.
Proof.
  destruct (N.eqb m1 0%N) eqn:Hm1.
  - apply N_eqb_eq_true in Hm1; subst m1.
    rewrite N.add_0_l in H.
    exists ds. split; [reflexivity | exact H].
  - destruct (N.eqb m2 0%N) eqn:Hm2.
    + apply N_eqb_eq_true in Hm2; subst m2.
      rewrite N.add_0_r in H.
      exists ds''. split; [exact H | reflexivity].
    + apply N_eqb_false_nat in Hm1. apply N_eqb_false_nat in Hm2.
      unfold subPow7OptK in *.
      rewrite (N_eqb_false_intro (m1 + m2)%N 0%N ltac:(nlia)) in H.
      rewrite (N_eqb_false_intro m1 0%N ltac:(nlia)).
      rewrite (N_eqb_false_intro m2 0%N ltac:(nlia)).
      exact (subPow7K_add ds m1 m2 H).
Qed.

Lemma subPow7K_append (xs : list N) : forall (m : N) (ys : list N) {xs' ys' : list N},
  subPow7K m xs = Some xs' ->
  subPow7K (m * N.pow 7%N (N.of_nat (length xs)))%N ys = Some ys' ->
  subPow7K m (xs ++ ys) = Some (xs' ++ ys').
Proof.
  induction xs as [|x xs IH]; intros m ys xs' ys' Hx Hy.
  - cbn [subPow7K] in Hx. injection Hx as H'; subst xs'.
    simpl in Hy. rewrite N.mul_1_r in Hy. exact Hy.
  - cbn [subPow7K] in Hx.
    destruct (N.leb (m + 1)%N x) eqn:Hle; [| discriminate Hx].
    destruct (subPow7K (7 * m)%N xs) as [xs1 |] eqn:Hxs; [| discriminate Hx].
    injection Hx as H'; subst xs'.
    simpl app. cbn [subPow7K]. rewrite Hle.
    assert (Hy' : subPow7K (7 * m * N.pow 7%N (N.of_nat (length xs)))%N ys = Some ys').
    { replace (7 * m * N.pow 7%N (N.of_nat (length xs)))%N
        with (m * N.pow 7%N (N.of_nat (length (x :: xs))))%N.
      - exact Hy.
      - apply N2Nat.inj. nat_norm. simpl length. simpl (Nat.pow 7 (S (length xs))). lia. }
    rewrite (IH (7 * m)%N ys xs1 ys' Hxs Hy'). reflexivity.
Qed.

Lemma subPow7OptK_append (m : N) (xs ys : list N) {xs' ys' : list N}
  (Hx : subPow7OptK m xs = Some xs')
  (Hy : subPow7OptK (m * N.pow 7%N (N.of_nat (length xs)))%N ys = Some ys') :
  subPow7OptK m (xs ++ ys) = Some (xs' ++ ys').
Proof.
  destruct (N.eqb m 0%N) eqn:Hm.
  - apply N_eqb_eq_true in Hm; subst m.
    rewrite N.mul_0_l in Hy.
    unfold subPow7OptK in *. simpl in Hx, Hy |- *.
    injection Hx as H1; injection Hy as H2; subst. reflexivity.
  - apply N_eqb_false_nat in Hm.
    pose proof (pow7_pos (length xs)) as Hpow.
    unfold subPow7OptK in *.
    rewrite (N_eqb_false_intro m 0%N Hm) in Hx |- *.
    rewrite (N_eqb_false_intro (m * N.pow 7%N (N.of_nat (length xs)))%N 0%N
      ltac:(nat_norm; nia)) in Hy.
    exact (subPow7K_append xs m ys Hx Hy).
Qed.

Lemma subPow7K_to_extractExcessK (ds : list N) : forall (p7 : N) {ds' : list N},
  subPow7K (2 * p7)%N ds = Some ds' ->
  exists es, extractExcessK p7 ds = Some es /\ length es = length ds /\
    (forall tail, framesR_inc es (encHalf tail) = encHalf (prependPairsK ds' tail)).
Proof.
  induction ds as [|d ds IH]; intros p7 ds' H.
  - cbn [subPow7K] in H. injection H as H'; subst ds'.
    exists (@nil N). split; [reflexivity | split; [reflexivity | intros tail; reflexivity]].
  - cbn [subPow7K] in H.
    destruct (N.leb (2 * p7 + 1)%N d) eqn:Hle; [| discriminate H].
    apply N_leb_true_nat in Hle.
    destruct (subPow7K (7 * (2 * p7))%N ds) as [ds1 |] eqn:Hs; [| discriminate H].
    injection H as H'; subst ds'.
    replace (7 * (2 * p7))%N with (2 * (7 * p7))%N in Hs by (apply N2Nat.inj; nlia).
    destruct (IH (7 * p7)%N ds1 Hs) as [es1 [Hex1 [Hlen1 Hfr1]]].
    exists ((d - (2 * p7 + 1))%N :: es1). split; [| split].
    + cbn [extractExcessK].
      rewrite (N_leb_true_intro (2 * p7 + 1)%N d Hle), Hex1. reflexivity.
    + simpl; lia.
    + intros tail. cbn [prependPairsK framesR_inc].
      rewrite <- Hfr1.
      cbn [encHalf].
      replace (N.to_nat (d - (2 * p7 + 1))%N + 2)
        with (N.to_nat (d - 2 * p7)%N + 1) by nlia.
      reflexivity.
Qed.

Lemma carryFuelK_sound_frames (fuel : nat) :
  forall (tail : list Tok) (us : list N) (w : nat) (dBot : N)
    {absFwd : list N} {tail' : list Tok},
    carryFuelK fuel tail = Some (absFwd, tail') ->
    (([S0; S1] *> ((wZ ^^ w) *>
      ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])))) {{C}}>
      ([S0] *> encHalf tail)) -->*
    (const S0 <{{C}}
      ([S0; S1] *> ((wZ ^^ (N.to_nat dBot + 1)) *>
        ([S0] *> framesR_inc us
          ((wZ ^^ (w + 2)) *> ([S0] *> encHalf (prependPairsFwdK absFwd tail'))))))).
Proof.
  induction fuel as [|fuel IH]; intros tail us w dBot absFwd tail' Hc.
  - discriminate Hc.
  - cbn [carryFuelK] in Hc.
    destruct tail as [| [| | x] rest]; try discriminate Hc.
    destruct (N.eqb x 0%N) eqn:Hx0.
    + apply N_eqb_eq_true in Hx0; subst x.
      destruct rest as [| [| | ?] r1]; try discriminate Hc.
      * (* rest = b0 :: r1 *)
        destruct r1 as [| [| | y] r2]; try discriminate Hc.
        -- (* r1 = b1 :: r2 *)
           destruct r2 as [| t3 [| t4 r]].
           ++ injection Hc as H1 H2; subst. cbn [prependPairsFwdK encHalf].
              nat_norm. rewrite lpow_1.
              exact (ev_trans
                (turn_p0_sound w ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])) (encHalf []))
                (unwind_framesL us w dBot ([S0; S0; S1; S1] *> encHalf []))).
           ++ destruct t3; injection Hc as H1 H2; subst; cbn [prependPairsFwdK encHalf];
                nat_norm; rewrite lpow_1;
                exact (ev_trans
                  (turn_p0_sound w ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])) _)
                  (unwind_framesL us w dBot _)).
           ++ destruct t3, t4; injection Hc as H1 H2; subst; cbn [prependPairsFwdK encHalf];
                nat_norm; rewrite lpow_1;
                exact (ev_trans
                  (turn_p0_sound w ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])) _)
                  (unwind_framesL us w dBot _)).
        -- (* r1 = w001 y :: r2 *)
           destruct r2 as [| [| | ?] [| [| | ?] r]]; try discriminate Hc.
           destruct (N.eqb y 0%N) eqn:Hy0; [| discriminate Hc].
           apply N_eqb_eq_true in Hy0; subst y.
           injection Hc as H1 H2; subst. cbn [prependPairsFwdK encHalf].
           nat_norm. rewrite lpow_1.
           change (1 + 1) with 2. replace (wZ ^^ 2) with (wZ ++ wZ) by reflexivity.
           pose proof (turn_phase_sound 3 ltac:(lia) w
             ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])) (encHalf r)) as H1.
           pose proof (unwind_framesL us w dBot (tailP 4 (encHalf r))) as H2.
           exact (ev_trans H1 H2).
      * (* rest = b1 :: r1 *)
        destruct r1 as [| [| | z] r2]; try discriminate Hc.
        -- (* r1 = b0 :: r2 *)
           destruct r2 as [| [| | ?] [| [| | z] [| [| | ?] r]]]; try discriminate Hc.
           destruct (carryFuelK fuel r) as [[absInner r'] |] eqn:Hrec; [| discriminate Hc].
           injection Hc as H1 H2; subst.
           pose proof (p5_exit_step w
             ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0]))
             (encHalf (w001 z :: b0 :: r))) as Hexit.
           assert (Hleq :
             [S0; S1; S0; S1; S0; S1] *> ((wZ ^^ (w + 1)) *>
               ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0]))) =
             [S0; S1; S0] *> encHalf (framesLK (N.of_nat w :: us) [b1; b0; b1; w001 dBot; b0])).
           { cbn [framesLK encHalf]. rewrite Nat2N.id. reflexivity. }
           rewrite Hleq in Hexit.
           pose proof (sweep010_CR_001_any (N.to_nat z + 1)
             (encHalf (framesLK (N.of_nat w :: us) [b1; b0; b1; w001 dBot; b0]))
             ([S0] *> encHalf r)) as Hsw.
           pose proof (IH r (N.of_nat w :: us) (N.to_nat z + 1) dBot absInner tail' Hrec) as Hih.
           cbn [framesR_inc] in Hih. rewrite Nat2N.id in Hih.
           cbn [prependPairsFwdK encHalf].
           replace (N.to_nat (z + 2)%N + 1) with (N.to_nat z + 1 + 2) by nlia.
           exact (ev_trans (ev_trans Hexit Hsw) Hih).
        -- (* r1 = w001 z :: r2 *)
           destruct (N.leb 2%N z) eqn:H2z; [| discriminate Hc].
           apply N_leb_true_nat in H2z.
           injection Hc as H1 H2; subst.
           cbn [prependPairsFwdK encHalf]. nat_norm. rewrite lpow_1.
           replace (N.to_nat z + 1) with (2 + (N.to_nat z - 2 + 1)) by lia.
           rewrite str_lpow_add.
           replace (wZ ^^ 2) with [S0; S0; S1; S0; S0; S1] by reflexivity.
           pose proof (turn_phase_sound 2 ltac:(lia) w
             ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0]))
             ((wZ ^^ (N.to_nat z - 2 + 1)) *> encHalf r2)) as H1.
           pose proof (unwind_framesL us w dBot
             (tailP 3 ((wZ ^^ (N.to_nat z - 2 + 1)) *> encHalf r2))) as H2.
           exact (ev_trans H1 H2).
    + destruct (N.eqb x 1%N) eqn:Hx1.
      * apply N_eqb_eq_true in Hx1; subst x.
        destruct rest as [| [| | ?] [| [| | ?] r]]; try discriminate Hc.
        injection Hc as H1 H2; subst.
        cbn [prependPairsFwdK encHalf]. nat_norm. rewrite lpow_1.
        change (1 + 1) with 2. replace (wZ ^^ 2) with [S0; S0; S1; S0; S0; S1] by reflexivity.
        pose proof (turn_phase_sound 4 ltac:(lia) w
          ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0])) (encHalf r)) as H1.
        pose proof (unwind_framesL us w dBot (tailP 5 (encHalf r))) as H2.
        exact (ev_trans H1 H2).
      * destruct (N.leb 2%N x) eqn:Hx2; [| discriminate Hc].
        apply N_leb_true_nat in Hx2.
        injection Hc as H1 H2; subst.
        cbn [prependPairsFwdK encHalf]. nat_norm. rewrite lpow_1.
        replace (N.to_nat x + 1) with (2 + (N.to_nat x - 2 + 1)) by lia.
        rewrite str_lpow_add.
        replace (wZ ^^ 2) with [S0; S0; S1; S0; S0; S1] by reflexivity.
        pose proof (turn_bare_sound w
          ([S0] *> encHalf (framesLK us [b1; b0; b1; w001 dBot; b0]))
          ((wZ ^^ (N.to_nat x - 2 + 1)) *> encHalf rest)) as H1.
        pose proof (unwind_framesL us w dBot
          ([S0; S0; S1; S0; S1] *> ((wZ ^^ (N.to_nat x - 2 + 1)) *> encHalf rest))) as H2.
        exact (ev_trans H1 H2).
Qed.

Lemma carryFuelK_sound_zero (fuel : nat) (tail : list Tok) (d0 : N)
  {absFwd : list N} {tail' : list Tok}
  (Hc : carryFuelK fuel tail = Some (absFwd, tail')) :
  encode CL [] (mkActiveK d0 [] tail) -->*
  encode CL [] (mkActiveK (d0 + 1)%N [] (prependPairsFwdK absFwd tail')).
Proof.
  destruct fuel as [|fuel]; [discriminate Hc |].
  cbn [encode mkActiveK prependPairsK encHalf].
  assert (H0 :
    (const S0 <{{C}} ([S0] *> ([S1] *> ((wZ ^^ (N.to_nat d0 + 1)) *> ([S0] *> encHalf tail))))) -->*
    (([S0; S1; S0] *> const S0) {{C}}> ((wZ ^^ (N.to_nat d0 + 1)) *> ([S0] *> encHalf tail)))).
  { rewrite <- cons_zero_const0 at 1. simpl Str_app; execute. }
  pose proof (sweep010_CR_001_any (N.to_nat d0 + 1) (const S0) ([S0] *> encHalf tail)) as Hsw.
  eapply ev_trans; [exact (ev_trans H0 Hsw) |].
  replace (N.to_nat (d0 + 1)%N + 1) with ((N.to_nat d0 + 1) + 1) by nlia.
  set (w := N.to_nat d0 + 1).
  cbn [carryFuelK] in Hc.
  destruct tail as [| [| | x] rest]; try discriminate Hc.
  destruct (N.eqb x 0%N) eqn:Hx0.
  - apply N_eqb_eq_true in Hx0; subst x.
    destruct rest as [| [| | ?] r1]; try discriminate Hc.
    + destruct r1 as [| [| | y] r2]; try discriminate Hc.
      * destruct r2 as [| t3 [| t4 r]].
        -- injection Hc as H1 H2; subst. cbn [prependPairsFwdK encHalf].
           nat_norm. rewrite lpow_1.
           exact (ev_trans
             (turn_p0_sound w ([S0] *> const S0) (encHalf []))
             (unwind_bottom w ([S0; S0; S1; S1] *> encHalf []))).
        -- destruct t3; injection Hc as H1 H2; subst; cbn [prependPairsFwdK encHalf];
             nat_norm; rewrite lpow_1;
             exact (ev_trans (turn_p0_sound w ([S0] *> const S0) _) (unwind_bottom w _)).
        -- destruct t3, t4; injection Hc as H1 H2; subst; cbn [prependPairsFwdK encHalf];
             nat_norm; rewrite lpow_1;
             exact (ev_trans (turn_p0_sound w ([S0] *> const S0) _) (unwind_bottom w _)).
      * destruct r2 as [| [| | ?] [| [| | ?] r]]; try discriminate Hc.
        destruct (N.eqb y 0%N) eqn:Hy0; [| discriminate Hc].
        apply N_eqb_eq_true in Hy0; subst y.
        injection Hc as H1 H2; subst. cbn [prependPairsFwdK encHalf].
        nat_norm. rewrite lpow_1.
        change (1 + 1) with 2. replace (wZ ^^ 2) with (wZ ++ wZ) by reflexivity.
        exact (ev_trans
          (turn_phase_sound 3 ltac:(lia) w ([S0] *> const S0) (encHalf r))
          (unwind_bottom w (tailP 4 (encHalf r)))).
    + destruct r1 as [| [| | z] r2]; try discriminate Hc.
      * destruct r2 as [| [| | ?] [| [| | z] [| [| | ?] r]]]; try discriminate Hc.
        destruct (carryFuelK fuel r) as [[absInner r'] |] eqn:Hrec; [| discriminate Hc].
        injection Hc as H1 H2; subst.
        pose proof (p5_exit_step w ([S0] *> const S0) (encHalf (w001 z :: b0 :: r))) as Hexit.
        assert (Hleq :
          [S0; S1; S0; S1; S0; S1] *> ((wZ ^^ (w + 1)) *> ([S0] *> const S0)) =
          [S0; S1; S0] *> encHalf (framesLK [] [b1; b0; b1; w001 (d0 + 1)%N; b0])).
        { cbn [framesLK encHalf].
          replace (N.to_nat (d0 + 1)%N + 1) with (w + 1) by (unfold w; nlia).
          reflexivity. }
        rewrite Hleq in Hexit.
        pose proof (sweep010_CR_001_any (N.to_nat z + 1)
          (encHalf (framesLK [] [b1; b0; b1; w001 (d0 + 1)%N; b0])) ([S0] *> encHalf r)) as Hsw2.
        pose proof (carryFuelK_sound_frames fuel r [] (N.to_nat z + 1) (d0 + 1)%N Hrec) as Hih.
        cbn [framesR_inc] in Hih.
        replace (N.to_nat (d0 + 1)%N + 1) with (w + 1) in Hih by (unfold w; nlia).
        cbn [prependPairsFwdK encHalf].
        replace (N.to_nat (z + 2)%N + 1) with (N.to_nat z + 1 + 2) by nlia.
        exact (ev_trans (ev_trans Hexit Hsw2) Hih).
      * destruct (N.leb 2%N z) eqn:H2z; [| discriminate Hc].
        apply N_leb_true_nat in H2z.
        injection Hc as H1 H2; subst.
        cbn [prependPairsFwdK encHalf]. nat_norm. rewrite lpow_1.
        replace (N.to_nat z + 1) with (2 + (N.to_nat z - 2 + 1)) by lia.
        rewrite str_lpow_add.
        replace (wZ ^^ 2) with [S0; S0; S1; S0; S0; S1] by reflexivity.
        exact (ev_trans
          (turn_phase_sound 2 ltac:(lia) w ([S0] *> const S0)
            ((wZ ^^ (N.to_nat z - 2 + 1)) *> encHalf r2))
          (unwind_bottom w (tailP 3 ((wZ ^^ (N.to_nat z - 2 + 1)) *> encHalf r2)))).
  - destruct (N.eqb x 1%N) eqn:Hx1.
    + apply N_eqb_eq_true in Hx1; subst x.
      destruct rest as [| [| | ?] [| [| | ?] r]]; try discriminate Hc.
      injection Hc as H1 H2; subst.
      cbn [prependPairsFwdK encHalf]. nat_norm. rewrite lpow_1.
      change (1 + 1) with 2. replace (wZ ^^ 2) with [S0; S0; S1; S0; S0; S1] by reflexivity.
      exact (ev_trans
        (turn_phase_sound 4 ltac:(lia) w ([S0] *> const S0) (encHalf r))
        (unwind_bottom w (tailP 5 (encHalf r)))).
    + destruct (N.leb 2%N x) eqn:Hx2; [| discriminate Hc].
      apply N_leb_true_nat in Hx2.
      injection Hc as H1 H2; subst.
      cbn [prependPairsFwdK encHalf]. nat_norm. rewrite lpow_1.
      replace (N.to_nat x + 1) with (2 + (N.to_nat x - 2 + 1)) by lia.
      rewrite str_lpow_add.
      replace (wZ ^^ 2) with [S0; S0; S1; S0; S0; S1] by reflexivity.
      exact (ev_trans
        (turn_bare_sound w ([S0] *> const S0)
          ((wZ ^^ (N.to_nat x - 2 + 1)) *> encHalf rest))
        (unwind_bottom w ([S0; S0; S1; S0; S1] *> ((wZ ^^ (N.to_nat x - 2 + 1)) *> encHalf rest)))).
Qed.

Lemma tower_carry_sound (f512 : nat) (d0 : N) (revDs : list N) (tail : list Tok)
  {revDs' absFwd : list N} {tail' : list Tok}
  (Hsub : subPow7K 2%N revDs = Some revDs')
  (Hc : carryFuelK f512 tail = Some (absFwd, tail')) :
  encode CL [] (mkActiveK d0 revDs tail) -->*
  encode CL [] (mkActiveK (d0 + N.pow 7%N (N.of_nat (length revDs)))%N revDs'
                  (prependPairsFwdK absFwd tail')).
Proof.
  destruct revDs as [|dc ds].
  - cbn [subPow7K] in Hsub. injection Hsub as H'; subst revDs'.
    simpl length. change (N.pow 7%N (N.of_nat 0)) with 1%N.
    exact (carryFuelK_sound_zero f512 tail d0 Hc).
  - cbn [subPow7K] in Hsub. change (2 + 1)%N with 3%N in Hsub.
    destruct (N.leb 3%N dc) eqn:Hle; [| discriminate Hsub].
    apply N_leb_true_nat in Hle.
    destruct (subPow7K (7 * 2)%N ds) as [ds' |] eqn:Hs; [| discriminate Hsub].
    injection Hsub as H'; subst revDs'.
    change (7 * 2)%N with (2 * 7)%N in Hs.
    destruct (subPow7K_to_extractExcessK ds 7%N Hs) as [es [Hex [Hlen Hfr]]].
    destruct (extractExcessK_sound ds 7%N (w001 dc :: b0 :: tail) Hex) as [_ Henc].
    cbn [encode mkActiveK prependPairsK encHalf].
    rewrite Henc.
    assert (Hsplit :
      encHalf (w001 dc :: b0 :: tail) =
      tailP 0 ((wZ ^^ (N.to_nat dc - 3)) *> ([S0] *> encHalf tail))).
    { cbn [encHalf tailP].
      replace (N.to_nat dc + 1) with (4 + (N.to_nat dc - 3)) by nlia.
      apply str_lpow_add. }
    rewrite Hsplit.
    pose proof (tower_raw_sound es d0 ((wZ ^^ (N.to_nat dc - 3)) *> ([S0] *> encHalf tail))) as Htw.
    pose proof (sweep010_CR_001_any (N.to_nat dc - 3)
      (encHalf (framesLK es [b1; b0; b1; w001 (d0 + N.pow 7%N (N.of_nat (length es + 1)))%N; b0]))
      ([S0] *> encHalf tail)) as Hsw.
    pose proof (carryFuelK_sound_frames f512 tail es (N.to_nat dc - 3)
      (d0 + N.pow 7%N (N.of_nat (length es + 1)))%N Hc) as Hcar.
    assert (Hlen_eq : length es + 1 = length (dc :: ds)) by (simpl; lia).
    rewrite Hlen_eq in Htw, Hsw, Hcar.
    assert (Hfin :
      framesR_inc es ((wZ ^^ (N.to_nat dc - 3 + 2)) *>
        ([S0] *> encHalf (prependPairsFwdK absFwd tail'))) =
      encHalf (prependPairsK ds' (w001 (dc - 2)%N :: b0 :: prependPairsFwdK absFwd tail'))).
    { rewrite <- Hfr.
      cbn [encHalf].
      replace (N.to_nat (dc - 2)%N + 1) with (N.to_nat dc - 3 + 2) by nlia.
      reflexivity. }
    rewrite Hfin in Hcar.
    exact (ev_trans (ev_trans Htw Hsw) Hcar).
Qed.

Lemma tower_carryNK_sound (f512 q : nat) :
  forall (d0 : N) (revDs : list N) (tail : list Tok) {revDs' : list N} {tail' : list Tok},
    subPow7OptK (N.of_nat (2 * q)) revDs = Some revDs' ->
    carryNK f512 q tail = Some tail' ->
    encode CL [] (mkActiveK d0 revDs tail) -->*
    encode CL [] (mkActiveK (d0 + N.of_nat q * N.pow 7%N (N.of_nat (length revDs)))%N revDs' tail').
Proof.
  induction q as [|q IH]; intros d0 revDs tail revDs' tail' Hsub Hc.
  - cbn [carryNK] in Hc. injection Hc as H1; subst tail'.
    simpl in Hsub. injection Hsub as H2; subst revDs'.
    simpl (N.of_nat 0). rewrite N.mul_0_l, N.add_0_r. apply evstep_refl.
  - cbn [carryNK] in Hc.
    destruct (carryFuelK f512 tail) as [[abs1 tail1] |] eqn:H1; [| discriminate Hc].
    destruct abs1 as [|? ?]; [| discriminate Hc].
    replace (N.of_nat (2 * S q)) with (2 + N.of_nat (2 * q))%N in Hsub by (apply N2Nat.inj; nlia).
    destruct (subPow7OptK_add 2%N (N.of_nat (2 * q)) revDs Hsub) as [revDs1 [Hs1 Hs2]].
    change (subPow7OptK 2%N revDs) with (subPow7K 2%N revDs) in Hs1.
    pose proof (tower_carry_sound f512 d0 revDs tail Hs1 H1) as Hst1.
    cbn [prependPairsFwdK] in Hst1.
    pose proof (subPow7K_len revDs 2%N Hs1) as Hlen.
    pose proof (IH (d0 + N.pow 7%N (N.of_nat (length revDs)))%N revDs1 tail1 revDs' tail' Hs2 Hc) as Hst2.
    rewrite Hlen in Hst2.
    replace (d0 + N.pow 7%N (N.of_nat (length revDs)) +
             N.of_nat q * N.pow 7%N (N.of_nat (length revDs)))%N
      with (d0 + N.of_nat (S q) * N.pow 7%N (N.of_nat (length revDs)))%N in Hst2
      by (apply N2Nat.inj; nat_norm; nia).
    exact (ev_trans Hst1 Hst2).
Qed.

Lemma carryUntilAbsK_sound (f512 fuel : nat) :
  forall (c0 d0 : N) (revDs : list N) (tail : list Tok)
    {c_tot : N} {absFwd revDs' : list N} {tail' : list Tok},
    carryUntilAbsK f512 fuel c0 tail = Some (c_tot, absFwd, tail') ->
    N.to_nat c0 < N.to_nat c_tot /\
    (subPow7K (2 * (c_tot - c0))%N revDs = Some revDs' ->
      encode CL [] (mkActiveK d0 revDs tail) -->*
      encode CL [] (mkActiveK (d0 + (c_tot - c0) * N.pow 7%N (N.of_nat (length revDs)))%N
                      revDs' (prependPairsFwdK absFwd tail'))).
Proof.
  induction fuel as [|fuel IH]; intros c0 d0 revDs tail c_tot absFwd revDs' tail' H.
  - discriminate H.
  - cbn [carryUntilAbsK] in H.
    destruct (carryFuelK f512 tail) as [[abs1 tail1] |] eqn:H1; [| discriminate H].
    destruct abs1 as [|a abs_rest].
    + destruct (IH (c0 + 1)%N (d0 + N.pow 7%N (N.of_nat (length revDs)))%N revDs tail1
                  c_tot absFwd (@nil N) tail' H) as [Hlt _].
      split; [nlia | intros Hsub].
      replace (2 * (c_tot - c0))%N
        with (2 + 2 * (c_tot - (c0 + 1)))%N in Hsub by (apply N2Nat.inj; nlia).
      destruct (subPow7K_add revDs 2%N (2 * (c_tot - (c0 + 1)))%N Hsub) as [revDs1 [Hs1 Hs2]].
      pose proof (tower_carry_sound f512 d0 revDs tail Hs1 H1) as Hst1.
      cbn [prependPairsFwdK] in Hst1.
      pose proof (subPow7K_len revDs 2%N Hs1) as Hlen.
      destruct (IH (c0 + 1)%N (d0 + N.pow 7%N (N.of_nat (length revDs)))%N revDs1 tail1
                  c_tot absFwd revDs' tail' H) as [_ Hrec].
      pose proof (Hrec Hs2) as Hst2.
      rewrite Hlen in Hst2.
      replace (d0 + N.pow 7%N (N.of_nat (length revDs)) +
               (c_tot - (c0 + 1)) * N.pow 7%N (N.of_nat (length revDs)))%N
        with (d0 + (c_tot - c0) * N.pow 7%N (N.of_nat (length revDs)))%N in Hst2
        by (apply N2Nat.inj; nat_norm; nia).
      exact (ev_trans Hst1 Hst2).
    + injection H as Hc Habs Htl; subst c_tot absFwd tail'.
      split; [nlia | intros Hsub].
      replace (c0 + 1 - c0)%N with 1%N in Hsub |- * by (apply N2Nat.inj; nlia).
      rewrite N.mul_1_r in Hsub. rewrite N.mul_1_l.
      exact (tower_carry_sound f512 d0 revDs tail Hsub H1).
Qed.

Lemma upChainAuxK_sound (f512 eb : nat) :
  forall (d0 : N) (revDs : list N) (tail : list Tok)
    {S_val : N} {fwdAbs revDs' : list N} {tail' : list Tok},
    upChainAuxK f512 eb tail = Some (S_val, fwdAbs, tail') ->
    subPow7OptK (2 * S_val)%N revDs = Some revDs' ->
    encode CL [] (mkActiveK d0 revDs tail) -->*
    encode CL [] (mkActiveK (d0 + S_val * N.pow 7%N (N.of_nat (length revDs)))%N
                    revDs' (prependPairsFwdK fwdAbs tail')).
Proof.
  induction eb as [|eb IH]; intros d0 revDs tail S_val fwdAbs revDs'' tail'' H Hsub.
  - cbn [upChainAuxK] in H. injection H as H1 H2 H3; subst.
    change (subPow7OptK (2 * 0)%N revDs) with (Some revDs) in Hsub. injection Hsub as H4; subst.
    cbn [prependPairsFwdK]. rewrite N.mul_0_l, N.add_0_r. apply evstep_refl.
  - cbn [upChainAuxK] in H.
    destruct (carryUntilAbsK f512 7 0%N tail) as [[[c abs1] tail1] |] eqn:Hc; [| discriminate H].
    destruct (upChainAuxK f512 eb tail1) as [[[S_rest restFwd] tail2] |] eqn:Hrec; [| discriminate H].
    destruct (N.eqb S_rest 0%N) eqn:Hs0.
    + apply N_eqb_eq_true in Hs0; subst S_rest.
      injection H as H1 H2 H3; subst S_val fwdAbs tail''.
      destruct (carryUntilAbsK_sound f512 7 0%N d0 revDs tail (revDs' := revDs'') Hc) as [Hcpos Hcar].
      unfold subPow7OptK in Hsub.
      rewrite (N_eqb_false_intro (2 * c)%N 0%N ltac:(nlia)) in Hsub.
      rewrite N.sub_0_r in Hcar.
      pose proof (Hcar Hsub) as Hst1.
      pose proof (IH (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N
        (rev abs1 ++ revDs'') tail1 0%N restFwd (rev abs1 ++ revDs'') tail2 Hrec eq_refl) as Hst2.
      rewrite N.mul_0_l, N.add_0_r in Hst2.
      assert (Hmid :
        mkActiveK (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N (rev abs1 ++ revDs'') tail1 =
        mkActiveK (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N revDs'' (prependPairsFwdK abs1 tail1)).
      { unfold mkActiveK. rewrite prependPairsK_append, prependPairsK_rev. reflexivity. }
      assert (Hend :
        mkActiveK (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N (rev abs1 ++ revDs'')
          (prependPairsFwdK restFwd tail2) =
        mkActiveK (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N revDs''
          (prependPairsFwdK (abs1 ++ restFwd) tail2)).
      { unfold mkActiveK. rewrite prependPairsK_append, prependPairsK_rev, prependPairsFwdK_append.
        reflexivity. }
      rewrite Hmid, Hend in Hst2.
      exact (ev_trans Hst1 Hst2).
    + apply N_eqb_false_nat in Hs0.
      rewrite <- !rev_alt in H.
      destruct (subPow7K (2 * S_rest)%N (rev abs1)) as [abs1_rev' |] eqn:Hab; [| discriminate H].
      injection H as H1 H2 H3; subst S_val fwdAbs tail''.
      assert (Hsplit :
        (2 * (c + S_rest * N.pow 7%N (N.of_nat (length abs1))))%N =
        (2 * c + 2 * S_rest * N.pow 7%N (N.of_nat (length (rev abs1))))%N).
      { rewrite length_rev. apply N2Nat.inj. nat_norm. nia. }
      rewrite Hsplit in Hsub.
      destruct (subPow7OptK_add (2 * c)%N (2 * S_rest * N.pow 7%N (N.of_nat (length (rev abs1))))%N
                  revDs Hsub) as [revDs' [Hs1 Hs2]].
      destruct (carryUntilAbsK_sound f512 7 0%N d0 revDs tail (revDs' := revDs') Hc) as [Hcpos Hcar].
      unfold subPow7OptK in Hs1.
      rewrite (N_eqb_false_intro (2 * c)%N 0%N ltac:(nlia)) in Hs1.
      rewrite N.sub_0_r in Hcar.
      pose proof (Hcar Hs1) as Hst1.
      assert (Hab_opt : subPow7OptK (2 * S_rest)%N (rev abs1) = Some abs1_rev').
      { unfold subPow7OptK. rewrite (N_eqb_false_intro (2 * S_rest)%N 0%N ltac:(nlia)). exact Hab. }
      pose proof (subPow7OptK_append (2 * S_rest)%N (rev abs1) revDs' Hab_opt Hs2) as Hcomb.
      pose proof (IH (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N
        (rev abs1 ++ revDs') tail1 S_rest restFwd (abs1_rev' ++ revDs'') tail2 Hrec Hcomb) as Hst2.
      assert (Hmid :
        mkActiveK (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N (rev abs1 ++ revDs') tail1 =
        mkActiveK (d0 + c * N.pow 7%N (N.of_nat (length revDs)))%N revDs' (prependPairsFwdK abs1 tail1)).
      { unfold mkActiveK. rewrite prependPairsK_append, prependPairsK_rev. reflexivity. }
      pose proof (subPow7K_len revDs (2 * c)%N Hs1) as Hlen_rv.
      assert (Hd0 :
        (d0 + c * N.pow 7%N (N.of_nat (length revDs)) +
         S_rest * N.pow 7%N (N.of_nat (length (rev abs1 ++ revDs'))))%N =
        (d0 + (c + S_rest * N.pow 7%N (N.of_nat (length abs1))) * N.pow 7%N (N.of_nat (length revDs)))%N).
      { apply N2Nat.inj. nat_norm.
        rewrite length_app, length_rev, Hlen_rv, Nat.pow_add_r. nia. }
      assert (Hend :
        mkActiveK (d0 + (c + S_rest * N.pow 7%N (N.of_nat (length abs1))) * N.pow 7%N (N.of_nat (length revDs)))%N
          (abs1_rev' ++ revDs'') (prependPairsFwdK restFwd tail2) =
        mkActiveK (d0 + (c + S_rest * N.pow 7%N (N.of_nat (length abs1))) * N.pow 7%N (N.of_nat (length revDs)))%N
          revDs'' (prependPairsFwdK (rev abs1_rev' ++ restFwd) tail2)).
      { unfold mkActiveK. rewrite prependPairsK_append.
        pose proof (prependPairsK_rev (rev abs1_rev') (prependPairsFwdK restFwd tail2)) as Hr.
        rewrite rev_involutive in Hr. rewrite Hr, prependPairsFwdK_append. reflexivity. }
      rewrite Hmid, Hd0, Hend in Hst2.
      rewrite <- rev_alt.
      exact (ev_trans Hst1 Hst2).
Qed.

Lemma upChainK_sound (f512 k eb : nat) (rs : list Tok) :
  upChainK f512 k eb rs <> st_err -> ResSound (encode CL [] rs) (upChainK f512 k eb rs).
Proof.
  intros Hne. unfold upChainK in *.
  destruct (splitActiveK k rs) as [[[d0 revDs] tail] |] eqn:Hsp;
    [| exfalso; apply Hne; reflexivity].
  destruct (upChainAuxK f512 eb tail) as [[[S_val fwdAbs] tail'] |] eqn:Hup;
    [| exfalso; apply Hne; reflexivity].
  destruct (subPow7OptK (2 * S_val)%N revDs) as [revDs' |] eqn:Hsub;
    [| exfalso; apply Hne; reflexivity].
  cbn [ResSound].
  destruct (splitActiveK_sound k rs Hsp) as [Hlen Hreq].
  rewrite Hreq, <- Hlen.
  exact (upChainAuxK_sound f512 eb d0 revDs tail Hup Hsub).
Qed.

Lemma downChainAuxK_sound (f512 len : nat) :
  forall (code T : N) (revDs : list N) (tail : list Tok)
    {T_fin : N} {revDs_fin : list N} {tail_fin : list Tok} {revDs_out : list N},
    downChainAuxK f512 len code T revDs tail = Some (T_fin, revDs_fin, tail_fin) ->
    subPow7OptK (2 * T_fin)%N revDs_fin = Some revDs_out ->
    exists revDs_cur, subPow7OptK (2 * T)%N revDs = Some revDs_cur /\
      (forall d0,
        encode CL [] (mkActiveK (d0 + T * N.pow 7%N (N.of_nat (length revDs)))%N revDs_cur tail) -->*
        encode CL [] (mkActiveK (d0 + T_fin * N.pow 7%N (N.of_nat (length revDs_fin)))%N revDs_out tail_fin)).
Proof.
  induction len as [|len IH]; intros code T revDs tail T_fin revDs_fin tail_fin revDs_out H Hsub.
  - cbn [downChainAuxK] in H. injection H as H1 H2 H3; subst.
    exists revDs_out. split; [exact Hsub | intros d0; apply evstep_refl].
  - destruct len as [|len'].
    + (* len = 1 *)
      cbn [downChainAuxK] in H.
      set (q := mod8 code) in *.
      destruct (carryNK f512 q tail) as [tail' |] eqn:Hc; [| discriminate H].
      injection H as H1 H2 H3; subst T_fin revDs_fin tail_fin.
      replace (2 * (T + N.of_nat q))%N
        with (2 * T + N.of_nat (2 * q))%N in Hsub by (apply N2Nat.inj; nlia).
      destruct (subPow7OptK_add (2 * T)%N (N.of_nat (2 * q)) revDs Hsub) as [revDs_cur [Hs1 Hs2]].
      pose proof (subPow7OptK_len (2 * T)%N revDs Hs1) as Hlen.
      exists revDs_cur. split; [exact Hs1 | intros d0].
      pose proof (tower_carryNK_sound f512 q (d0 + T * N.pow 7%N (N.of_nat (length revDs)))%N
        revDs_cur tail Hs2 Hc) as Hst.
      rewrite Hlen in Hst.
      replace (d0 + T * N.pow 7%N (N.of_nat (length revDs)) +
               N.of_nat q * N.pow 7%N (N.of_nat (length revDs)))%N
        with (d0 + (T + N.of_nat q) * N.pow 7%N (N.of_nat (length revDs)))%N in Hst
        by (apply N2Nat.inj; nat_norm; nia).
      exact Hst.
    + (* len = S (S len') *)
      change (downChainAuxK f512 (S (S len')) code T revDs tail)
        with (match carryNK f512 (mod8 code) tail with
              | None => None
              | Some tail' =>
                match revDs with
                | [] => None
                | d_top :: revDs' =>
                  if N.eqb (T + N.of_nat (mod8 code))%N 0%N then
                    downChainAuxK f512 (S len') (div8 code) 0%N revDs' (w001 d_top :: b0 :: tail')
                  else
                    if N.leb (2 * (T + N.of_nat (mod8 code)) + 1)%N d_top then
                      downChainAuxK f512 (S len') (div8 code) (7 * (T + N.of_nat (mod8 code)))%N revDs'
                        (w001 (d_top - 2 * (T + N.of_nat (mod8 code)))%N :: b0 :: tail')
                    else None
                end
              end) in H.
      set (q := mod8 code) in *.
      set (code' := div8 code) in *.
      destruct (carryNK f512 q tail) as [tail' |] eqn:Hc; [| discriminate H].
      destruct revDs as [|d_top revDs']; [discriminate H |].
      destruct (N.eqb (T + N.of_nat q)%N 0%N) eqn:Htq0.
      * apply N_eqb_eq_true in Htq0.
        assert (HT0 : T = 0%N) by (apply N2Nat.inj; nlia).
        assert (Hq0 : q = 0) by nlia.
        clearbody q; subst T q.
        cbn [carryNK] in Hc. injection Hc as Htl; subst tail'.
        destruct (IH code' 0%N revDs' (w001 d_top :: b0 :: tail) T_fin revDs_fin tail_fin revDs_out H Hsub)
          as [revDs'_cur [Hs_rec Hreach]].
        change (subPow7OptK (2 * 0)%N revDs') with (Some revDs') in Hs_rec. injection Hs_rec as Hrv; subst revDs'_cur.
        exists (d_top :: revDs'). split; [reflexivity | intros d0].
        pose proof (Hreach d0) as Hst.
        rewrite N.mul_0_l, N.add_0_r in Hst |- *.
        exact Hst.
      * apply N_eqb_false_nat in Htq0.
        destruct (N.leb (2 * (T + N.of_nat q) + 1)%N d_top) eqn:Hle; [| discriminate H].
        destruct (IH code' (7 * (T + N.of_nat q))%N revDs'
                    (w001 (d_top - 2 * (T + N.of_nat q))%N :: b0 :: tail')
                    T_fin revDs_fin tail_fin revDs_out H Hsub)
          as [revDs'_after [Hs_rec Hreach]].
        assert (Hcomb :
          subPow7OptK (2 * (T + N.of_nat q))%N (d_top :: revDs') =
          Some ((d_top - 2 * (T + N.of_nat q))%N :: revDs'_after)).
        { unfold subPow7OptK in Hs_rec |- *.
          rewrite (N_eqb_false_intro (2 * (T + N.of_nat q))%N 0%N ltac:(nlia)).
          rewrite (N_eqb_false_intro (2 * (7 * (T + N.of_nat q)))%N 0%N ltac:(nlia)) in Hs_rec.
          cbn [subPow7K]. rewrite Hle.
          replace (7 * (2 * (T + N.of_nat q)))%N with (2 * (7 * (T + N.of_nat q)))%N
            by (apply N2Nat.inj; nlia).
          rewrite Hs_rec. reflexivity. }
        replace (2 * (T + N.of_nat q))%N with (2 * T + N.of_nat (2 * q))%N in Hcomb
          by (apply N2Nat.inj; nlia).
        destruct (subPow7OptK_add (2 * T)%N (N.of_nat (2 * q)) (d_top :: revDs') Hcomb)
          as [revDs_cur [Hs1 Hs2]].
        pose proof (subPow7OptK_len (2 * T)%N (d_top :: revDs') Hs1) as Hlen.
        exists revDs_cur. split; [exact Hs1 | intros d0].
        pose proof (tower_carryNK_sound f512 q
          (d0 + T * N.pow 7%N (N.of_nat (length (d_top :: revDs'))))%N revDs_cur tail Hs2 Hc) as Hst1.
        assert (Heq1 :
          (d0 + T * N.pow 7%N (N.of_nat (length (d_top :: revDs'))) +
           N.of_nat q * N.pow 7%N (N.of_nat (length revDs_cur)))%N =
          (d0 + 7 * (T + N.of_nat q) * N.pow 7%N (N.of_nat (length revDs')))%N).
        { apply N2Nat.inj. nat_norm. rewrite Hlen. simpl length.
          simpl (Nat.pow 7 (S (length revDs'))). nia. }
        rewrite Heq1 in Hst1.
        replace (2 * T + N.of_nat (2 * q))%N with (2 * (T + N.of_nat q))%N in Hst1
          by (apply N2Nat.inj; nlia).
        change (mkActiveK (d0 + 7 * (T + N.of_nat q) * N.pow 7%N (N.of_nat (length revDs')))%N
                  ((d_top - 2 * (T + N.of_nat q))%N :: revDs'_after) tail')
          with (mkActiveK (d0 + 7 * (T + N.of_nat q) * N.pow 7%N (N.of_nat (length revDs')))%N
                  revDs'_after (w001 (d_top - 2 * (T + N.of_nat q))%N :: b0 :: tail')) in Hst1.
        exact (ev_trans Hst1 (Hreach d0)).
Qed.

Lemma downChainK_sound (f512 k len : nat) (code : N) (rs : list Tok) :
  downChainK f512 k len code rs <> st_err ->
  ResSound (encode CL [] rs) (downChainK f512 k len code rs).
Proof.
  intros Hne. unfold downChainK in *.
  destruct (splitActiveK k rs) as [[[d0 revDs] tail] |] eqn:Hsp;
    [| exfalso; apply Hne; reflexivity].
  destruct (downChainAuxK f512 len code 0%N revDs tail) as [[[T_fin revDs_fin] tail_fin] |] eqn:Hdn;
    [| exfalso; apply Hne; reflexivity].
  destruct (subPow7OptK (2 * T_fin)%N revDs_fin) as [revDs_out |] eqn:Hsub;
    [| exfalso; apply Hne; reflexivity].
  cbn [ResSound].
  destruct (splitActiveK_sound k rs Hsp) as [_ Hreq].
  destruct (downChainAuxK_sound f512 len code 0%N revDs tail Hdn Hsub) as [revDs_cur [Hs0 Hreach]].
  change (subPow7OptK (2 * 0)%N revDs) with (Some revDs) in Hs0. injection Hs0 as Hrv; subst revDs_cur.
  rewrite Hreq.
  pose proof (Hreach d0) as Hst.
  rewrite N.mul_0_l, N.add_0_r in Hst.
  exact Hst.
Qed.

(* ========================================================================= *)
(* Section 7: Certificate VM & Entry Soundness                               *)
(* ========================================================================= *)

Inductive Op : Type :=
| OpRun (steps : N)
| OpTower (k : N)
| OpUp (k eb : N)
| OpDown (k len code : N).

Definition execOpK (f512 f1024 : nat) (op : Op) (st : StepRes) : StepRes :=
  match op with
  | OpRun steps => runStepsK f1024 (N.to_nat steps) st
  | OpTower k =>
    match st with
    | st_ok CL [] rs => towerK (N.to_nat k) rs
    | _ => st_err
    end
  | OpUp k eb =>
    match st with
    | st_ok CL [] rs => upChainK f512 (N.to_nat k) (N.to_nat eb) rs
    | _ => st_err
    end
  | OpDown k len code =>
    match st with
    | st_ok CL [] rs => downChainK f512 (N.to_nat k) (N.to_nat len) code rs
    | _ => st_err
    end
  end.

Fixpoint execOpsK (f512 f1024 : nat) (ops : list Op) (st : StepRes) : StepRes :=
  match ops with
  | [] => st
  | op :: rest =>
    match execOpK f512 f1024 op st with
    | st_ok m ls rs => execOpsK f512 f1024 rest (st_ok m ls rs)
    | st_halted => st_halted
    | st_err => st_err
    end
  end.

Fixpoint execChunksK (f512 f1024 : nat) (chunks : list (list Op)) (st : StepRes) : StepRes :=
  match chunks with
  | [] => st
  | ch :: rest =>
    match execOpsK f512 f1024 ch st with
    | st_ok m ls rs => execChunksK f512 f1024 rest (st_ok m ls rs)
    | st_halted => st_halted
    | st_err => st_err
    end
  end.

Lemma execOpK_sound (f512 f1024 : nat) (op : Op) {c : Q * tape} {st : StepRes}
  (H : ResSound c st) (Hne : execOpK f512 f1024 op st <> st_err) :
  ResSound c (execOpK f512 f1024 op st).
Proof.
  destruct op as [steps | k | k eb | k len code].
  - exact (runStepsK_sound f1024 (N.to_nat steps) H).
  - destruct st as [[| | | |] [|? ?] rs | |]; try (exfalso; apply Hne; reflexivity).
    exact (resSound_trans H (towerK_sound (N.to_nat k) rs Hne)).
  - destruct st as [[| | | |] [|? ?] rs | |]; try (exfalso; apply Hne; reflexivity).
    exact (resSound_trans H (upChainK_sound f512 (N.to_nat k) (N.to_nat eb) rs Hne)).
  - destruct st as [[| | | |] [|? ?] rs | |]; try (exfalso; apply Hne; reflexivity).
    exact (resSound_trans H (downChainK_sound f512 (N.to_nat k) (N.to_nat len) code rs Hne)).
Qed.

Lemma execOpsK_sound (f512 f1024 : nat) (ops : list Op) :
  forall {c : Q * tape} {st : StepRes},
    ResSound c st -> execOpsK f512 f1024 ops st <> st_err ->
    ResSound c (execOpsK f512 f1024 ops st).
Proof.
  induction ops as [|op rest IH]; intros c st H Hne.
  - exact H.
  - cbn [execOpsK] in Hne |- *.
    destruct (execOpK f512 f1024 op st) as [m ls rs | |] eqn:H1.
    + pose proof (execOpK_sound f512 f1024 op H ltac:(rewrite H1; discriminate)) as Hs.
      rewrite H1 in Hs. exact (IH c (st_ok m ls rs) Hs Hne).
    + pose proof (execOpK_sound f512 f1024 op H ltac:(rewrite H1; discriminate)) as Hs.
      rewrite H1 in Hs. exact Hs.
    + exfalso; apply Hne; reflexivity.
Qed.

Lemma execChunksK_sound (f512 f1024 : nat) (chunks : list (list Op)) :
  forall {c : Q * tape} {st : StepRes},
    ResSound c st -> execChunksK f512 f1024 chunks st <> st_err ->
    ResSound c (execChunksK f512 f1024 chunks st).
Proof.
  induction chunks as [|ch rest IH]; intros c st H Hne.
  - exact H.
  - cbn [execChunksK] in Hne |- *.
    destruct (execOpsK f512 f1024 ch st) as [m ls rs | |] eqn:H1.
    + pose proof (execOpsK_sound f512 f1024 ch H ltac:(rewrite H1; discriminate)) as Hs.
      rewrite H1 in Hs. exact (IH c (st_ok m ls rs) Hs Hne).
    + pose proof (execOpsK_sound f512 f1024 ch H ltac:(rewrite H1; discriminate)) as Hs.
      rewrite H1 in Hs. exact Hs.
    + exfalso; apply Hne; reflexivity.
Qed.

Lemma entry_steps : c0 -->* encode CL [b1] [].
Proof.
  cbn [encode encHalf]. unfold c0, tape0; simpl Str_app; execute.
Qed.

Definition is_halted (st : StepRes) : bool :=
  match st with
  | st_halted => true
  | _ => false
  end.

(* ========================================================================= *)
(* Section 8: Fast Pos.sub_mask & Accumulator VM Equivalence                 *)
(* ========================================================================= *)

Local Open Scope N_scope.

Fixpoint sub2Pow7Pair (t : positive) (ds : list N) : option (list N * positive) :=
  match ds with
  | [] => Some ([], t)
  | d :: ds_rest =>
    match d with
    | N0 => None
    | Npos pd =>
      match Pos.sub_mask pd (xO t) with
      | IsPos diff =>
        match sub2Pow7Pair (7 * t)%positive ds_rest with
        | None => None
        | Some (ds', t_end) => Some (Npos diff :: ds', t_end)
        end
      | _ => None
      end
    end
  end.

Definition sub2Pow7OptPair (t : N) (ds : list N) : option (list N * N) :=
  match t with
  | N0 => Some (ds, N0)
  | Npos pt =>
    match sub2Pow7Pair pt ds with
    | None => None
    | Some (ds', pt_end) => Some (ds', Npos pt_end)
    end
  end.

Fixpoint extractExcessPair (p7 : positive) (ds : list N) : option (list N * positive) :=
  match ds with
  | [] => Some ([], p7)
  | d :: ds_rest =>
    match d with
    | N0 => None
    | Npos pd =>
      match Pos.sub_mask pd (xI p7) with
      | IsPos diff =>
        match extractExcessPair (7 * p7)%positive ds_rest with
        | None => None
        | Some (es, p7_end) => Some (Npos diff :: es, p7_end)
        end
      | IsNul =>
        match extractExcessPair (7 * p7)%positive ds_rest with
        | None => None
        | Some (es, p7_end) => Some (N0 :: es, p7_end)
        end
      | IsNeg => None
      end
    end
  end.

Definition fastTowerK (k : nat) (rs : list Tok) : StepRes :=
  match k with
  | 0%nat => st_err
  | S km1 =>
    match splitActiveK km1 rs with
    | None => st_err
    | Some (d0, revDs, rem) =>
      match rem with
      | w001 dc :: rest =>
        if N.leb 3 dc then
          match extractExcessPair 7%positive revDs with
          | None => st_err
          | Some (es, p7_end) =>
            let d0' := d0 + Npos p7_end in
            st_ok CR
              (b0 :: b1 :: b0 :: framesLK es [b1; b0; b1; w001 d0'; b0])
              (peel4K dc rest)
          end
        else st_err
      | _ => st_err
      end
    end
  end.

Fixpoint upChainAuxF (f512 eb : nat) (tail : list Tok) : option (N * list N * list Tok) :=
  match eb with
  | 0%nat => Some (0, [], tail)
  | S eb' =>
    match carryUntilAbsK f512 7%nat 0 tail with
    | None => None
    | Some (c, abs1, tail1) =>
      match upChainAuxF f512 eb' tail1 with
      | None => None
      | Some (S_rest, restFwd, tail2) =>
        match S_rest with
        | N0 => Some (c, abs1 ++ restFwd, tail2)
        | Npos ps =>
          let abs1_rev := rev_append abs1 [] in
          match sub2Pow7Pair ps abs1_rev with
          | None => None
          | Some (abs1_rev', ps_end) =>
            Some (c + Npos ps_end, rev_append abs1_rev' [] ++ restFwd, tail2)
          end
        end
      end
    end
  end.

Definition fastUpChainK (f512 k eb : nat) (rs : list Tok) : StepRes :=
  match splitActiveK k rs with
  | None => st_err
  | Some (d0, revDs, tail) =>
    match upChainAuxF f512 eb tail with
    | None => st_err
    | Some (S_val, fwdAbs, tail') =>
      match sub2Pow7OptPair S_val revDs with
      | None => st_err
      | Some (revDs', sv_end) =>
        st_ok CL [] (mkActiveK (d0 + sv_end) revDs' (prependPairsFwdK fwdAbs tail'))
      end
    end
  end.

Fixpoint downChainAuxF (f512 len : nat) (code T : N) (revDs : list N) (tail : list Tok)
  : option (N * list N * list Tok) :=
  match len with
  | 0%nat => Some (T, revDs, tail)
  | 1%nat =>
    let q := mod8 code in
    match carryNK f512 q tail with
    | None => None
    | Some tail' => Some (T + N.of_nat q, revDs, tail')
    end
  | S (S _ as len') =>
    let q := mod8 code in
    let code' := div8 code in
    match carryNK f512 q tail with
    | None => None
    | Some tail' =>
      let Tq := T + N.of_nat q in
      match revDs with
      | [] => None
      | d_top :: revDs' =>
        match Tq with
        | N0 => downChainAuxF f512 len' code' 0 revDs' (w001 d_top :: b0 :: tail')
        | Npos ptq =>
          match d_top with
          | N0 => None
          | Npos pd =>
            match Pos.sub_mask pd (xO ptq) with
            | IsPos diff =>
              downChainAuxF f512 len' code' (Npos (7 * ptq)%positive) revDs' (w001 (Npos diff) :: b0 :: tail')
            | _ => None
            end
          end
        end
      end
    end
  end.

Definition fastDownChainK (f512 k len : nat) (code : N) (rs : list Tok) : StepRes :=
  match splitActiveK k rs with
  | None => st_err
  | Some (d0, revDs, tail) =>
    match downChainAuxF f512 len code 0 revDs tail with
    | None => st_err
    | Some (T_fin, revDs_fin, tail_fin) =>
      match sub2Pow7OptPair T_fin revDs_fin with
      | None => st_err
      | Some (revDs_out, tf_end) =>
        st_ok CL [] (mkActiveK (d0 + tf_end) revDs_out tail_fin)
      end
    end
  end.

Definition execOpF (f512 f1024 : nat) (op : Op) (st : StepRes) : StepRes :=
  match op with
  | OpRun steps => runStepsK f1024 (N.to_nat steps) st
  | OpTower k =>
    match st with
    | st_ok CL [] rs => fastTowerK (N.to_nat k) rs
    | _ => st_err
    end
  | OpUp k eb =>
    match st with
    | st_ok CL [] rs => fastUpChainK f512 (N.to_nat k) (N.to_nat eb) rs
    | _ => st_err
    end
  | OpDown k len code =>
    match st with
    | st_ok CL [] rs => fastDownChainK f512 (N.to_nat k) (N.to_nat len) code rs
    | _ => st_err
    end
  end.

Fixpoint execOpsF (f512 f1024 : nat) (ops : list Op) (st : StepRes) : StepRes :=
  match ops with
  | [] => st
  | op :: rest =>
    match execOpF f512 f1024 op st with
    | st_ok m ls rs => execOpsF f512 f1024 rest (st_ok m ls rs)
    | st_halted => st_halted
    | st_err => st_err
    end
  end.

Fixpoint execChunksF (f512 f1024 : nat) (chunks : list (list Op)) (st : StepRes) : StepRes :=
  match chunks with
  | [] => st
  | ch :: rest =>
    match execOpsF f512 f1024 ch st with
    | st_ok m ls rs => execChunksF f512 f1024 rest (st_ok m ls rs)
    | st_halted => st_halted
    | st_err => st_err
    end
  end.

Local Open Scope nat_scope.

Lemma sub_mask_lt_spec (pd q : positive) :
  match Pos.sub_mask pd q with
  | IsPos diff => (N.leb (Npos q + 1)%N (Npos pd) = true /\ (Npos pd - Npos q)%N = Npos diff)
  | _ => N.leb (Npos q + 1)%N (Npos pd) = false
  end.
Proof.
  destruct (Pos.sub_mask_spec pd q) as [Heq | diff Hsum | diff Hsum].
  - subst pd.
    destruct (N.leb (Npos q + 1)%N (Npos q)) eqn:Hb; [| reflexivity].
    apply N_leb_true_nat in Hb. exfalso; nlia.
  - assert (Hnat : Pos.to_nat pd = Pos.to_nat q + Pos.to_nat diff).
    { rewrite <- Hsum, Pos2Nat.inj_add. reflexivity. }
    pose proof (Pos2Nat.is_pos diff) as Hpos.
    split.
    + apply N_leb_true_intro. nlia.
    + apply N2Nat.inj. nlia.
  - assert (Hnat : Pos.to_nat q = Pos.to_nat pd + Pos.to_nat diff).
    { rewrite <- Hsum, Pos2Nat.inj_add. reflexivity. }
    pose proof (Pos2Nat.is_pos diff) as Hpos.
    destruct (N.leb (Npos q + 1)%N (Npos pd)) eqn:Hb; [| reflexivity].
    apply N_leb_true_nat in Hb. exfalso; nlia.
Qed.

Lemma sub_mask_le_spec (pd q : positive) :
  match Pos.sub_mask pd q with
  | IsPos diff => (N.leb (Npos q) (Npos pd) = true /\ (Npos pd - Npos q)%N = Npos diff)
  | IsNul => (N.leb (Npos q) (Npos pd) = true /\ (Npos pd - Npos q)%N = N0)
  | IsNeg => N.leb (Npos q) (Npos pd) = false
  end.
Proof.
  destruct (Pos.sub_mask_spec pd q) as [Heq | diff Hsum | diff Hsum].
  - subst pd. split.
    + apply N_leb_true_intro. lia.
    + apply N2Nat.inj. nlia.
  - assert (Hnat : Pos.to_nat pd = Pos.to_nat q + Pos.to_nat diff).
    { rewrite <- Hsum, Pos2Nat.inj_add. reflexivity. }
    pose proof (Pos2Nat.is_pos diff) as Hpos.
    split.
    + apply N_leb_true_intro. nlia.
    + apply N2Nat.inj. nlia.
  - assert (Hnat : Pos.to_nat q = Pos.to_nat pd + Pos.to_nat diff).
    { rewrite <- Hsum, Pos2Nat.inj_add. reflexivity. }
    pose proof (Pos2Nat.is_pos diff) as Hpos.
    destruct (N.leb (Npos q) (Npos pd)) eqn:Hb; [| reflexivity].
    apply N_leb_true_nat in Hb. exfalso; nlia.
Qed.

Lemma sub2Pow7Pair_spec (ds : list N) : forall (pt : positive),
  sub2Pow7Pair pt ds =
  match subPow7K (2 * Npos pt)%N ds with
  | None => None
  | Some ds' =>
    let p_end := match (Npos pt * N.pow 7%N (N.of_nat (length ds)))%N with
                 | Npos p => p | N0 => xH end in
    Some (ds', p_end)
  end /\
  (forall ds' pt_end, sub2Pow7Pair pt ds = Some (ds', pt_end) ->
    Npos pt_end = (Npos pt * N.pow 7%N (N.of_nat (length ds)))%N).
Proof.
  induction ds as [|d ds IH]; intros pt.
  - simpl length. change (N.pow 7%N (N.of_nat 0)) with 1%N. rewrite N.mul_1_r.
    split; [reflexivity | intros ds' pt_end H; injection H as _ H2; subst; reflexivity].
  - cbn [sub2Pow7Pair subPow7K].
    change (2 * Npos pt)%N with (Npos (xO pt)).
    destruct d as [|pd].
    + change (N.leb (Npos (xO pt) + 1)%N N0) with false.
      split; [reflexivity | intros ? ? H; discriminate H].
    + pose proof (sub_mask_lt_spec pd (xO pt)) as Hspec.
      destruct (Pos.sub_mask pd (xO pt)) as [|diff|].
      * rewrite Hspec. split; [reflexivity | intros ? ? H; discriminate H].
      * destruct Hspec as [Hleb Hsub]. rewrite Hleb, Hsub.
        change (7 * Npos (xO pt))%N with (2 * Npos (7 * pt)%positive)%N.
        destruct (IH (7 * pt)%positive) as [Heq Hval].
        rewrite Heq.
        destruct (subPow7K (2 * Npos (7 * pt)%positive)%N ds) as [ds1 |].
        -- assert (Hmul :
             (Npos (7 * pt)%positive * N.pow 7%N (N.of_nat (length ds)))%N =
             (Npos pt * N.pow 7%N (N.of_nat (length (Npos pd :: ds))))%N).
           { apply N2Nat.inj.
             change (Npos (7 * pt)%positive) with (7 * Npos pt)%N.
             nat_norm. simpl length. simpl (Nat.pow 7 (S (length ds))). nia. }
           rewrite Hmul.
           assert (Hpos : (1 <= N.to_nat (Npos pt * N.pow 7%N (N.of_nat (length (Npos pd :: ds))))%N)).
           { nat_norm. pose proof (Pos2Nat.is_pos pt).
             pose proof (pow7_pos (length (Npos pd :: ds))). nia. }
           destruct (Npos pt * N.pow 7%N (N.of_nat (length (Npos pd :: ds))))%N as [|pend].
           ++ simpl in Hpos; lia.
           ++ split; [reflexivity | intros ? ? H; injection H as _ H2; subst; reflexivity].
        -- split; [reflexivity | intros ? ? H; discriminate H].
      * rewrite Hspec. split; [reflexivity | intros ? ? H; discriminate H].
Qed.

Lemma sub2Pow7OptPair_spec (t : N) (ds : list N) :
  match sub2Pow7OptPair t ds with
  | None => subPow7OptK (2 * t)%N ds = None
  | Some (ds', t_end) =>
    subPow7OptK (2 * t)%N ds = Some ds' /\
    t_end = (t * N.pow 7%N (N.of_nat (length ds)))%N
  end.
Proof.
  destruct t as [|pt].
  - cbn [sub2Pow7OptPair]. change (subPow7OptK (2 * 0)%N ds) with (Some ds).
    rewrite N.mul_0_l. split; reflexivity.
  - cbn [sub2Pow7OptPair].
    change (subPow7OptK (2 * Npos pt)%N ds) with (subPow7K (2 * Npos pt)%N ds).
    destruct (sub2Pow7Pair_spec ds pt) as [Heq Hval].
    destruct (sub2Pow7Pair pt ds) as [[ds' pt_end] |].
    + pose proof (Hval ds' pt_end eq_refl) as Hpe.
      destruct (subPow7K (2 * Npos pt)%N ds) as [ds1 |]; [| discriminate Heq].
      injection Heq as Hd _; subst ds1.
      split; [reflexivity | exact Hpe].
    + destruct (subPow7K (2 * Npos pt)%N ds); [discriminate Heq | reflexivity].
Qed.

Lemma extractExcessPair_spec (ds : list N) : forall (p7 : positive),
  match extractExcessPair p7 ds with
  | None => extractExcessK (Npos p7) ds = None
  | Some (es, p7_end) =>
    extractExcessK (Npos p7) ds = Some es /\
    Npos p7_end = (Npos p7 * N.pow 7%N (N.of_nat (length ds)))%N
  end.
Proof.
  induction ds as [|d ds IH]; intros p7.
  - cbn [extractExcessPair extractExcessK]. simpl length.
    change (N.pow 7%N (N.of_nat 0)) with 1%N. rewrite N.mul_1_r.
    split; reflexivity.
  - cbn [extractExcessPair extractExcessK].
    change (2 * Npos p7 + 1)%N with (Npos (xI p7)).
    change (7 * Npos p7)%N with (Npos (7 * p7)%positive).
    destruct d as [|pd].
    + reflexivity.
    + pose proof (sub_mask_le_spec pd (xI p7)) as Hspec.
      pose proof (IH (7 * p7)%positive) as Hrec.
      assert (Hmul :
        (Npos (7 * p7)%positive * N.pow 7%N (N.of_nat (length ds)))%N =
        (Npos p7 * N.pow 7%N (N.of_nat (length (Npos pd :: ds))))%N).
      { apply N2Nat.inj. change (Npos (7 * p7)%positive) with (7 * Npos p7)%N.
        nat_norm. simpl length. simpl (Nat.pow 7 (S (length ds))). nia. }
      destruct (Pos.sub_mask pd (xI p7)) as [|diff|].
      * destruct Hspec as [Hleb Hsub]. rewrite Hleb, Hsub.
        destruct (extractExcessPair (7 * p7)%positive ds) as [[es p7_end] |].
        -- destruct Hrec as [Hex Hp7]. rewrite Hex, Hp7, Hmul. split; reflexivity.
        -- rewrite Hrec. reflexivity.
      * destruct Hspec as [Hleb Hsub]. rewrite Hleb, Hsub.
        destruct (extractExcessPair (7 * p7)%positive ds) as [[es p7_end] |].
        -- destruct Hrec as [Hex Hp7]. rewrite Hex, Hp7, Hmul. split; reflexivity.
        -- rewrite Hrec. reflexivity.
      * rewrite Hspec. reflexivity.
Qed.

Lemma fastTowerK_eq (k : nat) (rs : list Tok) :
  fastTowerK k rs = towerK k rs.
Proof.
  unfold fastTowerK, towerK.
  destruct k as [|km1]; [reflexivity |].
  destruct (splitActiveK km1 rs) as [[[d0 revDs] rem] |] eqn:Hsp; [| reflexivity].
  destruct rem as [| [| | dc] rest]; try reflexivity.
  destruct (N.leb 3%N dc); [| reflexivity].
  pose proof (extractExcessPair_spec revDs 7%positive) as Hspec.
  destruct (extractExcessPair 7%positive revDs) as [[es p7_end] |].
  - destruct Hspec as [Hex Hp7]. rewrite Hex, Hp7.
    destruct (splitActiveK_sound km1 rs Hsp) as [Hlen _].
    rewrite Hlen.
    replace (7 * N.pow 7%N (N.of_nat km1))%N with (N.pow 7%N (N.of_nat (S km1)))%N.
    + reflexivity.
    + apply N2Nat.inj. nat_norm. simpl (Nat.pow 7 (S km1)). lia.
  - rewrite Hspec. reflexivity.
Qed.

Lemma upChainAuxF_eq (f512 eb : nat) : forall (tail : list Tok),
  upChainAuxF f512 eb tail = upChainAuxK f512 eb tail.
Proof.
  induction eb as [|eb IH]; intros tail; [reflexivity |].
  cbn [upChainAuxF upChainAuxK].
  destruct (carryUntilAbsK f512 7 0%N tail) as [[[c abs1] tail1] |]; [| reflexivity].
  rewrite IH.
  destruct (upChainAuxK f512 eb tail1) as [[[S_rest restFwd] tail2] |]; [| reflexivity].
  destruct S_rest as [|ps].
  - reflexivity.
  - change (N.eqb (Npos ps) 0%N) with false.
    pose proof (sub2Pow7OptPair_spec (Npos ps) (rev_append abs1 [])) as Hspec.
    cbn [sub2Pow7OptPair] in Hspec.
    change (subPow7OptK (2 * Npos ps)%N (rev_append abs1 []))
      with (subPow7K (2 * Npos ps)%N (rev_append abs1 [])) in Hspec.
    destruct (sub2Pow7Pair ps (rev_append abs1 [])) as [[abs1_rev' ps_end] |].
    + destruct Hspec as [Hsub Hpe]. rewrite Hsub, Hpe.
      rewrite <- rev_alt, length_rev. reflexivity.
    + rewrite Hspec. reflexivity.
Qed.

Lemma fastUpChainK_eq (f512 k eb : nat) (rs : list Tok) :
  fastUpChainK f512 k eb rs = upChainK f512 k eb rs.
Proof.
  unfold fastUpChainK, upChainK.
  destruct (splitActiveK k rs) as [[[d0 revDs] tail] |] eqn:Hsp; [| reflexivity].
  rewrite upChainAuxF_eq.
  destruct (upChainAuxK f512 eb tail) as [[[S_val fwdAbs] tail'] |]; [| reflexivity].
  pose proof (sub2Pow7OptPair_spec S_val revDs) as Hspec.
  destruct (sub2Pow7OptPair S_val revDs) as [[revDs' sv_end] |].
  - destruct Hspec as [Hsub Hsv]. rewrite Hsub, Hsv.
    destruct (splitActiveK_sound k rs Hsp) as [Hlen _].
    rewrite Hlen. reflexivity.
  - rewrite Hspec. reflexivity.
Qed.

Lemma downChainAuxF_eq (f512 len : nat) :
  forall (code T : N) (revDs : list N) (tail : list Tok),
    downChainAuxF f512 len code T revDs tail = downChainAuxK f512 len code T revDs tail.
Proof.
  induction len as [|len IH]; intros code T revDs tail; [reflexivity |].
  destruct len as [|len']; [reflexivity |].
  change (downChainAuxF f512 (S (S len')) code T revDs tail)
    with (match carryNK f512 (mod8 code) tail with
          | None => None
          | Some tail' =>
            let Tq := (T + N.of_nat (mod8 code))%N in
            match revDs with
            | [] => None
            | d_top :: revDs' =>
              match Tq with
              | N0 => downChainAuxF f512 (S len') (div8 code) 0%N revDs' (w001 d_top :: b0 :: tail')
              | Npos ptq =>
                match d_top with
                | N0 => None
                | Npos pd =>
                  match Pos.sub_mask pd (xO ptq) with
                  | IsPos diff =>
                    downChainAuxF f512 (S len') (div8 code) (Npos (7 * ptq)%positive) revDs'
                      (w001 (Npos diff) :: b0 :: tail')
                  | _ => None
                  end
                end
              end
            end
          end).
  change (downChainAuxK f512 (S (S len')) code T revDs tail)
    with (match carryNK f512 (mod8 code) tail with
          | None => None
          | Some tail' =>
            let Tq := (T + N.of_nat (mod8 code))%N in
            match revDs with
            | [] => None
            | d_top :: revDs' =>
              if N.eqb Tq 0%N then
                downChainAuxK f512 (S len') (div8 code) 0%N revDs' (w001 d_top :: b0 :: tail')
              else
                if N.leb (2 * Tq + 1)%N d_top then
                  downChainAuxK f512 (S len') (div8 code) (7 * Tq)%N revDs'
                    (w001 (d_top - 2 * Tq)%N :: b0 :: tail')
                else None
            end
          end).
  destruct (carryNK f512 (mod8 code) tail) as [tail' |]; [| reflexivity].
  destruct revDs as [|d_top revDs']; [reflexivity |].
  cbv zeta.
  destruct (T + N.of_nat (mod8 code))%N as [|ptq].
  - apply IH.
  - change (N.eqb (Npos ptq) 0%N) with false.
    change (2 * Npos ptq)%N with (Npos (xO ptq)).
    change (7 * Npos ptq)%N with (Npos (7 * ptq)%positive).
    destruct d_top as [|pd]; [reflexivity |].
    pose proof (sub_mask_lt_spec pd (xO ptq)) as Hspec.
    destruct (Pos.sub_mask pd (xO ptq)) as [|diff|].
    + rewrite Hspec. reflexivity.
    + destruct Hspec as [Hleb Hsub]. rewrite Hleb, Hsub. apply IH.
    + rewrite Hspec. reflexivity.
Qed.

Lemma fastDownChainK_eq (f512 k len : nat) (code : N) (rs : list Tok) :
  fastDownChainK f512 k len code rs = downChainK f512 k len code rs.
Proof.
  unfold fastDownChainK, downChainK.
  destruct (splitActiveK k rs) as [[[d0 revDs] tail] |]; [| reflexivity].
  rewrite downChainAuxF_eq.
  destruct (downChainAuxK f512 len code 0%N revDs tail) as [[[T_fin revDs_fin] tail_fin] |]; [| reflexivity].
  pose proof (sub2Pow7OptPair_spec T_fin revDs_fin) as Hspec.
  destruct (sub2Pow7OptPair T_fin revDs_fin) as [[revDs_out tf_end] |].
  - destruct Hspec as [Hsub Htf]. rewrite Hsub, Htf. reflexivity.
  - rewrite Hspec. reflexivity.
Qed.

Lemma execOpF_eq (f512 f1024 : nat) (op : Op) (st : StepRes) :
  execOpF f512 f1024 op st = execOpK f512 f1024 op st.
Proof.
  destruct op as [steps | k | k eb | k len code].
  - reflexivity.
  - destruct st as [[| | | |] [|? ?] rs | |]; try reflexivity.
    apply fastTowerK_eq.
  - destruct st as [[| | | |] [|? ?] rs | |]; try reflexivity.
    apply fastUpChainK_eq.
  - destruct st as [[| | | |] [|? ?] rs | |]; try reflexivity.
    apply fastDownChainK_eq.
Qed.

Lemma execOpsF_eq (f512 f1024 : nat) (ops : list Op) : forall (st : StepRes),
  execOpsF f512 f1024 ops st = execOpsK f512 f1024 ops st.
Proof.
  induction ops as [|op rest IH]; intros st; [reflexivity |].
  cbn [execOpsF execOpsK]. rewrite execOpF_eq.
  destruct (execOpK f512 f1024 op st); [apply IH | reflexivity | reflexivity].
Qed.

Lemma execChunksF_eq (f512 f1024 : nat) (chunks : list (list Op)) : forall (st : StepRes),
  execChunksF f512 f1024 chunks st = execChunksK f512 f1024 chunks st.
Proof.
  induction chunks as [|ch rest IH]; intros st; [reflexivity |].
  cbn [execChunksF execChunksK]. rewrite execOpsF_eq.
  destruct (execOpsK f512 f1024 ch st); [apply IH | reflexivity | reflexivity].
Qed.


Local Open Scope N_scope.

(* c is the amount of base-seven wave that this active prefix can pay. *)
Definition carryCapacity (c : option N) (d : N) : option N :=
  let credit := N.div2 (N.pred d) in
  Some (match c with None => credit | Some p => N.min credit (p / 7) end).

Definition canPay (c : option N) (n : N) : bool :=
  match c with None => true | Some p => n <=? p end.

Definition spend (c : option N) (n : N) : option N :=
  option_map (fun p => p - n) c.

Definition towerReady (c : option N) (tail : list Tok) : bool :=
  match tail with
  | w001 d :: _ => (3 <=? d) && canPay c 7
  | _ => false
  end.

(* After a carry costing q, subtract q from the old cut's allowance,
   then cross each absorbed pair in tape order.  Thus we can keep the
   longest affordable prefix of absorptions on a single forward scan. *)
Fixpoint planUp (fuel limit : nat) (c : option N) (tail : list Tok)
  : nat * nat :=
  match limit with
  | O => (O,O)
  | S limit' =>
    if towerReady c tail || negb (canPay c 1) then (O,O) else
      match carryUntilAbsK fuel 7 0 tail with
      | Some (q, ds, tail') =>
        if canPay c q then
          let c' := fold_left carryCapacity ds (spend c q) in
          let '(m, depth) := planUp fuel limit' c' tail' in
          (S m, (length ds + depth)%nat)
        else (O,O)
      | None => (O,O)
      end
  end.

Fixpoint planPhases (fuel limit : nat) (c : option N) (tail : list Tok)
  : N * list Tok :=
  match limit with
  | O => (0, tail)
  | S limit' =>
    if canPay c 1 && negb (towerReady c tail) then
      match carryFuelK fuel tail with
      | Some ([], tail') =>
        let '(q, tail'') := planPhases fuel limit' (spend c 1) tail' in
        (1 + q, tail'')
      | _ => (0, tail)
      end
    else (0, tail)
  end.

(* While descending, the spent amount t includes the previous digits, at
   the current cut's scale.  Stop before a payable tower; otherwise drop
   one frame and continue with the newly exposed tail.  A zero digit can
   connect two nonzero digits, but a zero-only suffix adds no progress. *)
Fixpoint planDown (fuel : nat) (outer : list (N * option N))
    (c : option N) (t : N) (tail : list Tok) (allowZero : bool) {struct outer}
  : nat * N :=
  let '(q, tail') := planPhases fuel 7 (spend c t) tail in
  let v := t + q in
  let here := (1%nat,q) in
  match outer with
  | (d,c') :: rest =>
    if (allowZero || negb (q =? 0)) &&
       canPay c v && negb (towerReady (spend c v) tail') then
      let '(len, code) := planDown fuel rest c' (7*v)
                           (w001 (d-2*v) :: b0 :: tail') true in
      if code =? 0 then here else (S len, q + 8*code)
    else here
  | [] => here
  end.

Definition Candidate := (nat * nat * nat * Op)%type.

Definition maxCandidate (a b : option Candidate) : option Candidate :=
  match a, b with
  | Some (i,p,n,_), Some (j,q,m,_) =>
    if Nat.ltb i j ||
       (Nat.eqb i j && (Nat.ltb p q || (Nat.eqb p q && Nat.leb n m)))
    then b else a
  | None, _ => b
  | _, None => a
  end.

(* Prefer reaching the deepest frame.  At that frame, a tower beats an
   upward group, and an upward group beats a downward group.  The last
   score breaks ties in favor of the larger group. *)
Fixpoint findJump (fuel k : nat) (c : option N) (tail : list Tok)
    (outer : list (N * option N)) {struct tail}
  : option Candidate :=
  match tail with
  | w001 d :: rest =>
    let deeper :=
      match rest with
      | b0 :: next =>
        let c' := carryCapacity c d in
        if canPay c' 1 then findJump fuel (S k) c' next ((d,c)::outer)
        else None
      | _ => None
      end in
    if towerReady c tail then
      match deeper with
      | None => Some (k,2%nat,O,OpTower (N.of_nat (S k)))
      | Some _ => deeper
      end
    else
      let '(n, depth) := planUp fuel 512 c tail in
      if Nat.eqb n O then
        match deeper with
        | Some _ => deeper
        | None =>
          let '(len, code) := planDown fuel outer c 0 tail false in
          if code =? 0 then None else Some (k,O,len,OpDown (N.of_nat k) (N.of_nat len) code)
        end
      else
        maxCandidate (Some (Nat.pred (k + depth)%nat,1%nat,n,OpUp (N.of_nat k) (N.of_nat n))) deeper
  | _ => None
  end.

Definition chooseJump (fuel : nat) (s : StepRes) : option Op :=
  match s with
  | st_ok CL [] (b0 :: b1 :: w001 _ :: b0 :: tail) =>
    option_map (fun '(_,_,_,op) => op) (findJump fuel O None tail [])
  | _ => None
  end.

Definition autoStep (f512 f1024 : nat) (s : StepRes) : StepRes :=
  match chooseJump f512 s with
  | None => stepResK f1024 s
  | Some op =>
    match execOpF f512 f1024 op s with
    | st_err => stepResK f1024 s
    | r => r
    end
  end.

Lemma autoStep_sound f512 f1024 s c :
  ResSound c s -> ResSound c (autoStep f512 f1024 s).
Proof.
  intros H. unfold autoStep.
  destruct (chooseJump f512 s) as [op|]; [|now apply stepResK_sound].
  destruct (execOpF f512 f1024 op s) eqn:E; [| |now apply stepResK_sound].
  all: rewrite execOpF_eq in E;
       match type of E with
       | execOpK _ _ ?operation _ = _ =>
         pose proof (execOpK_sound f512 f1024 operation H ltac:(rewrite E; discriminate)) as HS
       end;
       now rewrite E in HS.
Qed.

(* A tail-recursive replay does not retain the configurations already used.
   Reaching a rejected rule or exhausting the budget is not a halt. *)
Fixpoint runAutoTail (f512 f1024 fuel : nat) (s : StepRes) : bool :=
  match s with
  | st_halted => true
  | st_err => false
  | st_ok _ _ _ =>
    match fuel with
    | O => false
    | S f => runAutoTail f512 f1024 f (autoStep f512 f1024 s)
    end
  end.

Lemma runAutoTail_sound f512 f1024 fuel c s :
  ResSound c s -> runAutoTail f512 f1024 fuel s = true -> halts tm c.
Proof.
  revert s. induction fuel as [|f IH]; intros [m l r| |] H E;
    cbn [runAutoTail] in E; try discriminate; try exact H.
  exact (IH _ (autoStep_sound f512 f1024 _ _ H) E).
Qed.

End Internal.

Theorem halt : halts tm c0.
Proof.
  apply (Internal.runAutoTail_sound 512 1024 300000 c0
    (Internal.st_ok Internal.CL [Internal.b1] []) Internal.entry_steps).
  native_check_eq.
Qed.

End TM1.

Print Assumptions TM1.halt.
