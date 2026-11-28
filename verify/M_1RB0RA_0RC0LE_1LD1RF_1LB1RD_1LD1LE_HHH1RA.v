(* 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA never halts. *)

From Coq Require Import Lia ZifyNat ZifyBool PeanoNat Bool String Lists.Streams List.
From BusyCoq Require Import Individual62.
Import ListNotations.

Open Scope list_scope.
Open Scope sym_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm := Eval compute in
  (TM_from_str "1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA").

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

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; repeat rewrite <- const_unfold; reflexivity) || finish_progress.

Ltac fast_start_progress :=
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

(* ========================================================================== *)
(* Section 1: Tape Algebra, Shift Rules, Sweeps, and Finite Bridges           *)
(* ========================================================================== *)

Definition O_u : list Sym := [1]%sym.
Definition Z_u : list Sym := [0]%sym.

Lemma z0_const : 0%sym >> 0inf%sym = 0inf%sym.
Proof. symmetry. apply const_unfold. Qed.

Lemma l_app_app (s : side) (l1 l2 : list Sym) :
  (s <* l1) <* l2 = s <* (l2 ++ l1).
Proof. symmetry. apply Str_app_assoc. Qed.

Lemma lpow_append_one {A : Type} (u : list A) (k : nat) :
  u ^^ k ++ u = u ^^ (k + 1).
Proof.
  rewrite lpow_add. cbn [lpow]. rewrite app_nil_r. reflexivity.
Qed.

Lemma pow_add_append_right (u : list Sym) (m n : nat) (r : side) :
  u ^^ (m + n) *> r = u ^^ m *> (u ^^ n *> r).
Proof.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma pow_succ_append_right (u : list Sym) (n : nat) (r : side) :
  u ^^ (n + 1) *> r = u *> (u ^^ n *> r).
Proof.
  replace (n + 1) with (S n) by lia.
  cbn [lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma pow_add_append_left (s : side) (u : list Sym) (m n : nat) :
  s <* (u ^^ (m + n)) = (s <* (u ^^ m)) <* (u ^^ n).
Proof.
  replace (m + n) with (n + m) by lia.
  rewrite lpow_add, <- l_app_app. reflexivity.
Qed.

Lemma shift_A_right_1 (k : nat) (l r : side) :
  (l {{A}}> (O_u ^^ k *> r)) -->* ((l <* Z_u ^^ k) {{A}}> r).
Proof. unfold O_u, Z_u. shift_rule. steps; finish. Qed.

Lemma shift_E_left_1 (k : nat) (l r : side) :
  ((l <* O_u ^^ k) <{{E}} r) -->* (l <{{E}} (O_u ^^ k *> r)).
Proof. unfold O_u. shift_rule. steps; finish. Qed.

Lemma shift_D_right_1 (k : nat) (l r : side) :
  (l {{D}}> (O_u ^^ k *> r)) -->* ((l <* O_u ^^ k) {{D}}> r).
Proof. unfold O_u. shift_rule. steps; finish. Qed.

Lemma sweep_R (k : nat) (l r : side) :
  (l {{B}}> ([0]%sym *> (O_u ^^ (k + 5) *> ([0; 1]%sym *> r)))) -->+
  (((l <* [1; 1; 0]%sym) <* Z_u ^^ k) {{B}}> ([0; 1; 1; 1; 0]%sym *> r)).
Proof.
  replace (k + 5) with ((k + 3) + 1 + 1) by lia.
  rewrite (pow_succ_append_right O_u (k + 3 + 1)).
  rewrite (pow_succ_append_right O_u (k + 3)).
  apply (@ptrans _ ((l <* [1; 1; 0]%sym) {{A}}> (O_u ^^ (k + 3) *> ([0; 1]%sym *> r))) _).
  - unfold O_u at 1 2. fast_start_progress.
  - eapply ep_trans; [apply shift_A_right_1 |].
    replace (k + 3) with (k + 1 + 1 + 1) by lia.
    rewrite (pow_add_append_left _ Z_u (k + 1 + 1) 1).
    rewrite (pow_add_append_left _ Z_u (k + 1) 1).
    rewrite (pow_add_append_left _ Z_u k 1).
    cbn [lpow app]. unfold Z_u at 2 3 4.
    fast_start_progress.
Qed.

Lemma sweep_blank_R (k : nat) (l : side) :
  (l {{B}}> ([0]%sym *> (O_u ^^ (k + 4) *> 0inf%sym))) -->+
  (((l <* [1; 1; 0]%sym) <* Z_u ^^ k) {{D}}> ([0; 1; 0; 1; 1]%sym *> 0inf%sym)).
Proof.
  replace (k + 4) with ((k + 2) + 1 + 1) by lia.
  rewrite (pow_succ_append_right O_u (k + 2 + 1)).
  rewrite (pow_succ_append_right O_u (k + 2)).
  apply (@ptrans _ ((l <* [1; 1; 0]%sym) {{A}}> (O_u ^^ (k + 2) *> 0inf%sym)) _).
  - unfold O_u at 1 2. fast_start_progress.
  - eapply ep_trans; [apply shift_A_right_1 |].
    replace (k + 2) with (k + 1 + 1) by lia.
    rewrite (pow_add_append_left _ Z_u (k + 1) 1).
    rewrite (pow_add_append_left _ Z_u k 1).
    cbn [lpow app]. unfold Z_u at 2 3.
    fast_start_progress.
Qed.

Lemma left_sweep_to_hub (k : nat) (l r : side) :
  (((l <* [0; 0]%sym) <* O_u ^^ (k + 1)) {{D}}> ([0]%sym *> r)) -->+
  (l {{D}}> ([0]%sym *> (O_u ^^ (k + 1) *> ([0; 1]%sym *> r)))).
Proof.
  rewrite (pow_add_append_left (l <* [0; 0]%sym) O_u k 1).
  cbn [lpow app].
  apply (@ptrans _ (((l <* [0; 0]%sym) <* O_u ^^ k) <{{E}} ([0; 1]%sym *> r)) _).
  - unfold O_u at 2. fast_start_progress.
  - eapply ep_trans; [apply shift_E_left_1 |].
    rewrite (pow_succ_append_right O_u k).
    unfold O_u at 1. fast_start_progress.
Qed.

Lemma left_sweep_to_B (k : nat) (l r : side) :
  (((l <* [0; 0; 0]%sym) <* O_u ^^ (k + 1)) {{D}}> ([0]%sym *> r)) -->+
  (l {{B}}> ([0]%sym *> (O_u ^^ (k + 2) *> ([0; 1]%sym *> r)))).
Proof.
  change (l <* [0; 0; 0]%sym) with ((l <* [0]%sym) <* [0; 0]%sym).
  eapply ptrans; [apply left_sweep_to_hub |].
  replace (k + 2) with ((k + 1) + 1) by lia.
  rewrite (pow_succ_append_right O_u (k + 1)).
  unfold O_u at 1. fast_start_progress.
Qed.

Lemma merge_011 (k : nat) (l r : side) :
  (((l <* [0; 1; 1; 0]%sym) <* O_u ^^ (k + 1)) {{D}}> ([0]%sym *> r)) -->+
  (((l <* [0]%sym) <* O_u ^^ (k + 3)) {{D}}> ([0; 1]%sym *> r)).
Proof.
  rewrite (pow_add_append_left (l <* [0; 1; 1; 0]%sym) O_u k 1).
  cbn [lpow app].
  apply (@ptrans _ (((l <* [0; 1; 1; 0]%sym) <* O_u ^^ k) <{{E}} ([0; 1]%sym *> r)) _).
  - unfold O_u at 2. fast_start_progress.
  - eapply ep_trans; [apply shift_E_left_1 |].
    apply (@pe_trans _ (((l <* [0]%sym) <* O_u ^^ 3) {{D}}> (O_u ^^ k *> ([0; 1]%sym *> r))) _).
    + cbn [lpow app]; unfold O_u at 1 2 3. fast_start_progress.
    + replace (k + 3) with (3 + k) by lia.
      rewrite (pow_add_append_left (l <* [0]%sym) O_u 3 k).
      apply shift_D_right_1.
Qed.

Lemma merge_p5 (k : nat) (l r : side) :
  (((l <* [0; 1; 0; 1; 1; 0]%sym) <* O_u ^^ (k + 1)) {{D}}> ([0]%sym *> r)) -->+
  (((l <* [0]%sym) <* O_u ^^ (k + 4)) {{D}}> ([0; 1; 1]%sym *> r)).
Proof.
  rewrite (pow_add_append_left (l <* [0; 1; 0; 1; 1; 0]%sym) O_u k 1).
  cbn [lpow app].
  apply (@ptrans _ (((l <* [0; 1; 0; 1; 1; 0]%sym) <* O_u ^^ k) <{{E}} ([0; 1]%sym *> r)) _).
  - unfold O_u at 2. fast_start_progress.
  - eapply ep_trans; [apply shift_E_left_1 |].
    apply (@ptrans _ (((l <* [0; 1; 1; 0]%sym) <* O_u ^^ 2) {{D}}> (O_u ^^ k *> ([0; 1]%sym *> r))) _).
    + cbn [lpow app]; unfold O_u at 1 2. fast_start_progress.
    + eapply ep_trans; [apply shift_D_right_1 |].
      rewrite <- (pow_add_append_left (l <* [0; 1; 1; 0]%sym) O_u 2 k).
      replace (2 + k) with ((k + 1) + 1) by lia.
      replace (k + 4) with ((k + 1) + 3) by lia.
      change ([0; 1; 1]%sym *> r) with ([0; 1]%sym *> ([1]%sym *> r)).
      apply (merge_011 (k + 1) l ([1]%sym *> r)).
Qed.

Lemma thm_A_0 (l r : side) :
  (l {{B}}> ([0; 1; 1; 1; 0; 1]%sym *> r)) -->+
  (((l <* [0]%sym) <* O_u ^^ 4) {{D}}> ([0]%sym *> r)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

Lemma step_D_0011 (l r : side) :
  ((l <* [1; 1; 0; 0; 0]%sym) {{D}}> ([0; 1]%sym *> r)) -->+
  (((l <* [0]%sym) <* O_u ^^ 4) {{D}}> ([0; 1]%sym *> r)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

Lemma step_D_p3z1_pop (l r : side) :
  ((l <* [1; 1; 0; 0]%sym) {{D}}> ([0; 1]%sym *> r)) -->+
  (l {{D}}> ([0; 1; 1; 0; 1; 1]%sym *> r)).
Proof. fast_start_progress. Qed.

Lemma bridge_b2_m0 (l r : side) :
  (l {{B}}> ([0; 1; 1; 1; 1; 1; 0; 1; 1]%sym *> r)) -->+
  (((l <* [0]%sym) <* O_u ^^ 6) {{D}}> ([0; 1]%sym *> r)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

Lemma bridge_b2_tail (l r : side) :
  ((l <* [0; 0]%sym) {{B}}> ([0; 1; 1; 1; 0; 1]%sym *> r)) -->+
  (l {{B}}> ([0; 1; 1; 1; 1; 1; 0; 1]%sym *> r)).
Proof. fast_start_progress. Qed.

Lemma bridge_b5a (l : side) :
  (l {{B}}> ([0; 1; 1; 1; 1; 1; 0; 1]%sym *> 0inf%sym)) -->+
  (((l <* [0]%sym) <* O_u ^^ 5) {{D}}> ([0; 1; 1; 1]%sym *> 0inf%sym)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

Lemma bridge_b5b_pre (l r : side) :
  (l {{B}}> ([0; 1; 1; 1; 1; 1; 0; 1; 0]%sym *> r)) -->+
  (((l <* [1; 1; 0]%sym) <* [1; 0; 1; 1; 0]%sym) {{B}}> ([0]%sym *> r)).
Proof. fast_start_progress. Qed.

Lemma bridge_b5b_d0_blank (l : side) :
  (((l <* [1; 1; 0]%sym) <* [1; 0; 1; 1; 0]%sym) {{B}}> ([0; 1; 1]%sym *> 0inf%sym)) -->+
  ((((l <* [1; 1; 0]%sym) <* [0]%sym) <* O_u ^^ 6) {{D}}> ([0; 1; 1; 1]%sym *> 0inf%sym)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

Lemma bridge_b5b_d1_blank (l : side) :
  (((l <* [1; 1; 0]%sym) <* [1; 0; 1; 1; 0]%sym) {{B}}> ([0; 1; 1; 1]%sym *> 0inf%sym)) -->+
  (((((l <* [1; 1; 0]%sym) <* [1; 1; 0]%sym) <* [0]%sym) <* O_u ^^ 4) {{D}}> ([0; 1; 1; 1]%sym *> 0inf%sym)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

Lemma bridge_b5b_d2_blank (l : side) :
  (((l <* [1; 1; 0]%sym) <* [1; 0; 1; 1; 0]%sym) {{B}}> ([0; 1; 1; 1; 1]%sym *> 0inf%sym)) -->+
  ((((l <* [1; 1; 0]%sym) <* [0]%sym) <* O_u ^^ 5) {{D}}> ([0; 1; 1; 1; 0; 1; 1]%sym *> 0inf%sym)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

Lemma bridge_blank_apos_tail (l : side) :
  ((l <* [0; 0; 0]%sym) {{D}}> ([0; 1; 0; 1; 1]%sym *> 0inf%sym)) -->+
  (((l <* [0]%sym) <* O_u ^^ 5) {{D}}> ([0; 1; 1; 1]%sym *> 0inf%sym)).
Proof. cbn [lpow app]; unfold O_u. fast_start_progress. Qed.

(* ========================================================================== *)
(* Section 2: State270 Configuration Space, Step Function, and Invariant      *)
(* ========================================================================== *)

Inductive LTok : Type :=
  | p3z (m : nat)
  | p5.

Fixpoint evalL (ls : list LTok) : side :=
  match ls with
  | [] => 0inf%sym
  | p3z m :: ls' => (evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ m
  | p5 :: ls' => evalL ls' <* [1; 0; 1; 1; 0]%sym
  end.

Fixpoint evalR (ds : list nat) : side :=
  match ds with
  | [] => 0inf%sym
  | d :: ds' => [0]%sym *> (O_u ^^ (d + 2) *> evalR ds')
  end.

Inductive State270 : Type :=
  | ModeE_c1 (ls : list LTok) (k : nat) (ds : list nat)
  | ModeE_ge2 (ls : list LTok) (k : nat) (c : nat) (ds : list nat)
  | ModeB_ge3 (ls : list LTok) (a : nat) (c : nat) (ds : list nat)
  | ModeB_b2 (ls : list LTok) (m : nat) (ds : list nat)
  | ModeB_blank (ls : list LTok) (a : nat).

Definition k0Of (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => k' + 2
  end.

Definition m0Of (m : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => m' + 2
  end.

Definition toCfg (s : State270) : Q * tape :=
  match s with
  | ModeE_c1 ls k ds =>
      (((evalL ls <* [0]%sym) <* O_u ^^ (k0Of k + 4)) {{D}}> ([0; 1]%sym *> evalR ds))
  | ModeE_ge2 ls k c ds =>
      (((evalL ls <* [0]%sym) <* O_u ^^ (k + 4)) {{D}}> ([0]%sym *> (O_u ^^ (c + 2) *> evalR ds)))
  | ModeB_ge3 ls a c ds =>
      (evalL ls {{B}}> ([0]%sym *> (O_u ^^ (a + 5) *> ([0]%sym *> (O_u ^^ (c + 3) *> evalR ds)))))
  | ModeB_b2 ls m ds =>
      (evalL ls {{B}}> ([0]%sym *> (O_u ^^ (m0Of m + 5) *> ([0; 1; 1]%sym *> evalR ds))))
  | ModeB_blank ls a =>
      (evalL ls {{B}}> ([0]%sym *> (O_u ^^ (a + 5) *> 0inf%sym)))
  end.

Fixpoint nextModeE_p3z1 (ls : list LTok) (b : nat) (ds : list nat) : State270 :=
  match ls with
  | [] => ModeE_ge2 [] 0 b ds
  | p3z 0 :: ls'' => ModeE_ge2 ls'' 0 (b + 1) ds
  | p3z 1 :: ls'' => nextModeE_p3z1 ls'' 0 ((b + 1) :: ds)
  | p3z (S (S m2)) :: ls'' => ModeE_ge2 (p3z m2 :: ls'') 0 b ds
  | p5 :: ls'' => ModeE_ge2 ls'' 1 (b + 2) ds
  end.

Definition nextState (s : State270) : State270 :=
  match s with
  | ModeE_c1 [] k ds => ModeB_b2 [] k ds
  | ModeE_c1 (p3z 0 :: ls') k ds => ModeE_ge2 ls' (k0Of k + 2) 0 ds
  | ModeE_c1 (p3z 1 :: ls') k ds => nextModeE_p3z1 ls' (k0Of k + 2) (0 :: ds)
  | ModeE_c1 (p3z (S (S m2)) :: ls') k ds => ModeB_b2 (p3z m2 :: ls') k ds
  | ModeE_c1 (p5 :: ls') k ds => ModeE_ge2 ls' (k0Of k + 3) 1 ds
  | ModeE_ge2 [] k c ds => ModeB_ge3 [] k c ds
  | ModeE_ge2 (p3z 0 :: ls') k c ds => ModeE_ge2 ls' (k + 2) (c + 1) ds
  | ModeE_ge2 (p3z 1 :: ls') k c ds => nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)
  | ModeE_ge2 (p3z (S (S m2)) :: ls') k c ds => ModeB_ge3 (p3z m2 :: ls') k c ds
  | ModeE_ge2 (p5 :: ls') k c ds => ModeE_ge2 ls' (k + 3) (c + 2) ds
  | ModeB_ge3 ls a 0 ds => ModeE_c1 (p3z a :: ls) 0 ds
  | ModeB_ge3 ls a (S c') ds => ModeE_ge2 (p3z a :: ls) 0 c' ds
  | ModeB_b2 ls 0 ds => ModeE_c1 ls 1 ds
  | ModeB_b2 ls (S m') ds =>
      match ds with
      | [] => ModeE_ge2 (p3z m' :: ls) 1 1 []
      | [0] => ModeE_ge2 (p3z 0 :: p3z m' :: ls) 2 1 []
      | [1] => ModeE_ge2 (p3z 0 :: p3z 0 :: p3z m' :: ls) 0 1 []
      | [2] => ModeE_ge2 (p3z 0 :: p3z m' :: ls) 1 1 [0]
      | [S (S (S m''))] => ModeB_blank (p5 :: p3z 0 :: p3z m' :: ls) m''
      | S (S (S m'')) :: 0 :: ds'' =>
          match m'' with
          | S (S m4) => ModeB_b2 (p5 :: p3z 0 :: p3z m' :: ls) (m4 + 1) ds''
          | _ => ModeB_b2 ls (S m') ds
          end
      | S (S (S m'')) :: S c' :: ds'' =>
          ModeB_ge3 (p5 :: p3z 0 :: p3z m' :: ls) m'' c' ds''
      | _ => ModeB_b2 ls (S m') ds
      end
  | ModeB_blank ls (S (S a'')) => ModeE_ge2 (p3z a'' :: ls) 1 1 []
  | ModeB_blank ls a => ModeB_blank ls a
  end.

Lemma init_to_s0 : c0 -->+ toCfg (ModeB_ge3 [] 1 1 []).
Proof.
  unfold c0, tape0, q0, s0, toCfg, evalL, evalR.
  cbn [Nat.add lpow app]. unfold O_u.
  fast_start_progress.
Qed.

(* Boolean helpers for list equality and arithmetic predicates *)
Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (x =? y) && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma nat_list_eqb_spec (xs ys : list nat) : Bool.reflect (xs = ys) (nat_list_eqb xs ys).
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; cbn.
  - constructor; reflexivity.
  - constructor; discriminate.
  - constructor; discriminate.
  - destruct (Nat.eqb_spec x y); subst; cbn.
    + destruct (IH ys); constructor; congruence.
    + constructor; congruence.
Qed.

Fixpoint z0 (ls : list LTok) : nat :=
  match ls with
  | p3z 0 :: ls' => 1 + z0 ls'
  | _ => 0
  end.

Fixpoint dropZ0 (ls : list LTok) : list LTok :=
  match ls with
  | p3z 0 :: ls' => dropZ0 ls'
  | _ => ls
  end.

Fixpoint z0Rep (n : nat) (rest : list LTok) : list LTok :=
  match n with
  | 0 => rest
  | S n' => p3z 0 :: z0Rep n' rest
  end.

Fixpoint ep (ls : list LTok) : nat :=
  match ls with
  | p3z m :: ls' => if m mod 2 =? 1 then 0 else 1 + ep ls'
  | _ => 0
  end.

Fixpoint epW (ls : list LTok) : nat :=
  match ls with
  | p3z m :: ls' =>
      if m mod 2 =? 1 then 0
      else match ls' with
           | p5 :: _ => 0
           | _ => 1 + epW ls'
           end
  | _ => 0
  end.

Fixpoint prefSumW (ls : list LTok) : nat :=
  match ls with
  | p3z m :: ls' =>
      if m mod 2 =? 1 then 0
      else match ls' with
           | p5 :: _ => 0
           | _ => m + prefSumW ls'
           end
  | _ => 0
  end.

Fixpoint epSum (ls : list LTok) : nat :=
  match ls with
  | p3z m :: ls' => if m mod 2 =? 1 then m - 1 else m + epSum ls'
  | _ => 0
  end.

Fixpoint hasOdd (ls : list LTok) : bool :=
  match ls with
  | p3z m :: ls' => if m mod 2 =? 1 then true else hasOdd ls'
  | _ => false
  end.

Fixpoint hasP5 (ls : list LTok) : bool :=
  match ls with
  | [] => false
  | p5 :: _ => true
  | p3z _ :: ls' => hasP5 ls'
  end.

Fixpoint preP5Val (ls : list LTok) : nat :=
  match ls with
  | p3z m :: ls' =>
      match ls' with
      | p5 :: _ => m
      | _ => preP5Val ls'
      end
  | _ => 0
  end.

Fixpoint MustDrain (ls : list LTok) : bool :=
  match ls with
  | p3z m :: ls' =>
      if m mod 2 =? 1 then
        match ls' with
        | p5 :: _ => false
        | _ => true
        end
      else MustDrain ls'
  | _ => false
  end.

Fixpoint p5Suf (ls : list LTok) : list LTok :=
  match ls with
  | [] => []
  | p5 :: ls' => ls'
  | p3z _ :: ls' => p5Suf ls'
  end.

Definition isHeadP5 (ls : list LTok) : bool :=
  match ls with
  | p5 :: _ => true
  | _ => false
  end.

Definition isHeadP3z1 (ls : list LTok) : bool :=
  match ls with
  | p3z 1 :: _ => true
  | _ => false
  end.

Definition headP3zVal (ls : list LTok) : nat :=
  match ls with
  | p3z m :: _ => m
  | _ => 0
  end.

Definition isP3zGe1P5 (ls : list LTok) : bool :=
  match ls with
  | p3z (S _) :: p5 :: _ => true
  | _ => false
  end.

Definition isP3zP5 (ls : list LTok) : bool :=
  match ls with
  | p3z _ :: p5 :: _ => true
  | _ => false
  end.

Definition drop1L (ls : list LTok) : list LTok :=
  match ls with
  | [] => []
  | _ :: xs => xs
  end.

Definition drop2L (ls : list LTok) : list LTok :=
  match ls with
  | _ :: _ :: xs => xs
  | _ => []
  end.

Definition headNat (ds : list nat) : nat :=
  match ds with
  | [] => 0
  | d :: _ => d
  end.

Fixpoint ValidP5Chain (ls : list LTok) : bool :=
  match ls with
  | [] => true
  | p3z 0 :: ls' => ValidP5Chain ls'
  | p5 :: suf => (18 <=? z0 suf) && ValidP5Chain suf
  | p3z (S _) :: p5 :: suf => (18 <=? z0 suf) && ValidP5Chain suf
  | _ => false
  end.

Definition ValidAfterOdd (ls : list LTok) : bool :=
  match ls with
  | [] => true
  | p5 :: suf => (18 <=? z0 suf) && ValidP5Chain suf
  | p3z _ :: p5 :: suf => (18 <=? z0 suf) && ValidP5Chain suf
  | _ => false
  end.

Fixpoint ValidEvenLs (ls : list LTok) : bool :=
  match ls with
  | [] => true
  | p5 :: suf => (18 <=? z0 suf) && ValidP5Chain suf
  | p3z m :: rest =>
      if m mod 2 =? 0 then ValidEvenLs rest
      else ValidAfterOdd rest
  end.

Definition isOddDrain1 (d : nat) : bool :=
  (d =? 9) || (d =? 11) || (d =? 13) || (d =? 15) || (d =? 17).

Definition isOddDrainDs (ds : list nat) : bool :=
  match ds with
  | [d] => isOddDrain1 d
  | [d; 0] => isOddDrain1 d
  | _ => false
  end.

Definition isDrainRstDs (ds : list nat) : bool :=
  match ds with
  | [d] => 8 <=? d
  | [d; 0] => 8 <=? d
  | _ => false
  end.

Definition isRank0 (ds : list nat) : bool :=
  match ds with
  | [] => true
  | [0] => true
  | [1] => true
  | [2] => true
  | _ => false
  end.

Definition GoodDs1 (d : nat) : bool :=
  (d <=? 2) || (8 <=? d).

Definition GoodDs2 (d d2 : nat) : bool :=
  if d2 =? 0 then 8 <=? d
  else if d2 =? 1 then (d =? 3) || (25 <=? d)
  else if d2 <? 3 then false
  else if isOddDrain1 d2 && (d <? 19) then false
  else if (d <? 17) || negb (GoodDs1 d2) then false
  else if ((d mod 2 =? 0) && (d <=? 2 * d2 + 4)) && negb (GoodDs1 (d2 - 1)) then false
  else if ((d mod 2 =? 0) && (d + 14 <=? 2 * d2)) && negb (GoodDs1 (d2 - 2)) then false
  else true.

Fixpoint GoodDsAux (d : nat) (ds : list nat) : bool :=
  match ds with
  | [] => GoodDs1 d
  | d2 :: ds2 =>
      match ds2 with
      | [] => GoodDs2 d d2
      | d3 :: ds3 =>
          if d2 <? 3 then false
          else if (d2 =? 3) && (d3 =? 1) && nat_list_eqb ds3 [] && (d <? 19) then false
          else if isOddDrainDs (d2 :: d3 :: ds3) && (d <? 19) then false
          else if (25 <=? d2) && (d3 =? 1) && nat_list_eqb ds3 [] && (d <? 39) then false
          else if (d <? 17) || negb (GoodDsAux d2 ds2) then false
          else if ((d mod 2 =? 0) && (d <=? 2 * d2 + 4)) && negb (GoodDsAux (d2 - 1) ds2) then false
          else if ((d mod 2 =? 0) && (d + 14 <=? 2 * d2)) && negb (GoodDsAux (d2 - 2) ds2) then false
          else true
      end
  end.

Definition GoodDs (ds : list nat) : bool :=
  match ds with
  | [] => true
  | d :: ds' => GoodDsAux d ds'
  end.

Definition isDGe25One (ds : list nat) : bool :=
  match ds with
  | [d; 1] => 25 <=? d
  | _ => false
  end.

Definition GoodPhiW (phiW : nat) (ds : list nat) (is_start : bool) : bool :=
  if nat_list_eqb ds [2] then phiW =? 4
  else if nat_list_eqb ds [0] then 6 <=? phiW
  else if nat_list_eqb ds [1] then 1 <=? phiW
  else if nat_list_eqb ds [] then is_start || (6 <=? phiW)
  else if isDGe25One ds then 35 <=? phiW
  else if isOddDrainDs ds then 17 <=? phiW
  else 15 <=? phiW.

Definition GoodPsi (psi : nat) (ds : list nat) : bool :=
  GoodDs ((psi + 1) :: ds).

Fixpoint checkChainAux (fuel : nat) (b : bool) (ls : list LTok)
    (c1 k1 margin : nat) (ds : list nat) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
      match b with
      | false =>
          let cz := c1 + z0 ls in
          let kz := k1 + 2 * z0 ls in
          let rem := dropZ0 ls in
          if negb (isHeadP5 rem) && negb (GoodPhiW (cz - 1) ds false) then false
          else match rem with
          | [] => GoodPsi (cz - 1) ds && checkChainAux fuel' true [] (kz + 2) 0 (2 * (kz + 1) + 4) (cz :: ds)
          | p5 :: suf => checkChainAux fuel' true suf (cz + 3) (kz + 3) (2 * (cz + 2) + 4) ds
          | p3z m :: rest =>
              let suf := drop1L rest in
              if m =? 1 then
                GoodPsi cz ds && checkChainAux fuel' false suf (kz + 4) 1 0 ((cz + 1) :: ds)
              else if negb (GoodPsi (cz - 1) ds) then false
              else if (m mod 2 =? 0) && (m <=? 2 * kz + 10) then
                checkChainAux fuel' false suf (kz + 4) (m + 1) 0 (cz :: ds)
              else if (m mod 2 =? 1) && (m <=? 2 * kz + 11) then
                GoodDs ((kz + 2) :: cz :: ds) && checkChainAux fuel' false suf (m - 1) 1 0 ((kz + 2) :: cz :: ds)
              else
                checkChainAux fuel' true (p3z (m - 4) :: p5 :: suf) (kz + 2) 0 (2 * (kz + 1) + 4) (cz :: ds)
          end
      | true =>
          let cp1 := c1 in
          let kb := k1 in
          if hasOdd ls && (kb + epSum ls <=? margin) then
            let psip1 := cp1 + ep ls in
            let xi := kb + epSum ls + 2 * ep ls in
            let suf := p5Suf ls in
            if negb (MustDrain ls) then
              if negb (hasP5 ls) then
                checkChainAux fuel' true [] (xi + 3) 0 (2 * (xi + 2) + 4) (psip1 :: ds)
              else
                GoodDs (psip1 :: ds) && checkChainAux fuel' false suf (xi + 4) 1 0 (psip1 :: ds)
            else if hasP5 ls then
              let m2 := preP5Val ls in
              if (m2 mod 2 =? 0) && (m2 <=? 2 * xi + 10) then
                checkChainAux fuel' false suf (xi + 5) (m2 + 3) 0 (psip1 :: ds)
              else if (m2 mod 2 =? 1) && (m2 <=? 2 * xi + 11) then
                GoodDs ((xi + 3) :: psip1 :: ds) && checkChainAux fuel' false suf (m2 + 1) 1 0 ((xi + 3) :: psip1 :: ds)
              else
                checkChainAux fuel' true (p3z (m2 - 2) :: p5 :: suf) (xi + 3) 0 (2 * (xi + 2) + 4) (psip1 :: ds)
            else
              checkChainAux fuel' true [] (xi + 3) 0 (2 * (xi + 2) + 4) (psip1 :: ds)
          else if negb (hasOdd ls) && hasP5 ls && (isHeadP5 ls || (kb + epSum ls <=? margin)) then
            checkChainAux fuel' false (p5Suf ls) (cp1 + ep ls + 1) (kb + epSum ls + 2 * ep ls + 3) 0 ds
          else if isDrainRstDs ds then
            let phiWp1 := cp1 + epW ls in
            let reqp1 := if isOddDrainDs ds then 18 else 16 in
            if phiWp1 <? reqp1 then false
            else
              let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (margin + 2) in
              let tail_b2 := if hasP5 ls then p3z m_rem :: p5 :: p5Suf ls else [] in
              let suf_b2 := z0Rep (phiWp1 + 2) tail_b2 in
              let m_rst := headNat ds - 7 in
              if m_rst =? 1 then
                checkChainAux fuel' false suf_b2 2 1 0 [3; 1]
              else
                checkChainAux fuel' true (p3z (m_rst - 2) :: p5 :: suf_b2) 3 0 8 [1]
          else if isRank0 ds then
            let phiWp1 := cp1 + epW ls in
            if phiWp1 <? 2 then true
            else
              let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (margin + 2) in
              let tail_b2 := if hasP5 ls then p3z m_rem :: p5 :: p5Suf ls else [] in
              if nat_list_eqb ds [] then
                checkChainAux fuel' false (z0Rep (phiWp1 + 1) tail_b2) 1 1 0 []
              else if nat_list_eqb ds [0] then
                checkChainAux fuel' true (z0Rep (phiWp1 + 2) tail_b2) 2 2 6 []
              else if nat_list_eqb ds [1] then
                checkChainAux fuel' true (z0Rep (phiWp1 + 3) tail_b2) 2 0 6 []
              else
                checkChainAux fuel' false (z0Rep (phiWp1 + 2) tail_b2) 1 1 0 [0]
          else match ds with
          | d :: d2 :: ds2 =>
              if (3 <=? d) && (1 <=? d2) then
                if (d mod 2 =? 0) && (d <=? 2 * d2 + 4) && negb (GoodDs ((d2 - 1) :: ds2)) then false
                else if (d mod 2 =? 0) && (d + 14 <=? 2 * d2) && negb (GoodDs ((d2 - 2) :: ds2)) then false
                else if cp1 + epW ls <? 16 then false
                else
                  let phiWp1 := cp1 + epW ls in
                  let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (margin + 2) in
                  let tail_b2 := if hasP5 ls then p3z m_rem :: p5 :: p5Suf ls else [] in
                  let ls_b2 := z0Rep phiWp1 tail_b2 in
                  if (d2 =? 1) && nat_list_eqb ds2 [] && (25 <=? d) then
                    checkChainAux fuel' true (p3z (d - 11) :: p5 :: p3z 0 :: p3z 0 :: ls_b2) 5 0 12 [2]
                  else
                    let nls_pop := p3z (d - 3) :: p5 :: p3z 0 :: p3z 0 :: ls_b2 in
                    checkChainAux fuel' true nls_pop (d2 - 1) 0 (2 * d2) ds2
              else true
          | _ => true
          end
      end
  end.

Definition checkResetSufAux (fuel m : nat) (suf : list LTok) : bool :=
  if m =? 1 then
    checkChainAux fuel false suf 2 1 0 [3; 1]
  else
    checkChainAux fuel true (p3z (m - 2) :: p5 :: suf) 3 0 8 [1].

Definition checkDs2 (s : State270) : bool :=
  match s with
  | ModeB_blank _ _ => true
  | ModeE_ge2 ls k c ds =>
      if negb (nat_list_eqb ds [2]) then true
      else hasP5 ls && negb (MustDrain ls) && (38 <=? z0 (p5Suf ls)) &&
           (k mod 2 =? 0) && negb (isHeadP5 ls) && (2 * c + 6 <=? k + epSum ls)
  | ModeB_ge3 ls a c ds =>
      if negb (nat_list_eqb ds [2]) then true
      else hasP5 ls && negb (MustDrain ls) && (38 <=? z0 (p5Suf ls)) &&
           (a mod 2 =? 0) && negb (isHeadP5 ls) && (2 * c + 4 <=? a + epSum ls)
  | ModeE_c1 ls k ds =>
      if negb (nat_list_eqb ds [2]) then true
      else hasP5 ls && negb (MustDrain ls) && (38 <=? z0 (p5Suf ls)) &&
           negb (isHeadP5 ls) && (4 <=? 2 * k + epSum ls)
  | ModeB_b2 ls m ds =>
      if negb (nat_list_eqb ds [2]) then true
      else hasP5 ls && negb (MustDrain ls) && (38 <=? z0 (p5Suf ls)) &&
           negb (isHeadP5 ls) && (2 <=? 2 * m + epSum ls)
  end.

Definition checkDs1Phi1 (s : State270) : bool :=
  match s with
  | ModeB_blank _ _ => true
  | ModeE_ge2 ls k c ds =>
      if negb (nat_list_eqb ds [1]) then true
      else
        let phi1_case :=
          if k mod 2 =? 0 then
            let pw := if isHeadP5 ls then c - 1 else c + epW ls in
            pw =? 1
          else false in
        if negb phi1_case then true
        else hasP5 ls && negb (MustDrain ls) && negb (isHeadP5 ls) && (2 * c + 14 <=? k + epSum ls)
  | ModeB_ge3 ls a c ds =>
      if negb (nat_list_eqb ds [1]) then true
      else
        let phi1_case :=
          if a mod 2 =? 0 then
            let pw := if isHeadP5 ls then c - 1 else c + epW ls in
            pw =? 1
          else c =? 2 in
        if negb phi1_case then true
        else
          let nls := p3z a :: ls in
          hasP5 nls && negb (MustDrain nls) && negb (isHeadP5 nls) &&
          (if a mod 2 =? 0 then 2 * c + 12 <=? a + epSum ls else 2 * c + 13 <=? a)
  | ModeE_c1 ls k ds =>
      if negb (nat_list_eqb ds [1]) then true
      else if negb (epW ls =? 2) then true
      else hasP5 ls && negb (MustDrain ls) && negb (isHeadP5 ls) && (12 <=? 2 * k + epSum ls)
  | ModeB_b2 ls m ds =>
      if negb (nat_list_eqb ds [1]) then true
      else if negb (epW ls =? 2) then true
      else hasP5 ls && negb (MustDrain ls) && negb (isHeadP5 ls) && (10 <=? 2 * m + epSum ls)
  end.

Definition invCore (s : State270) : bool :=
  match s with
  | ModeB_blank ls a =>
      (5 <=? a) && isHeadP5 ls &&
      (let suf := drop1L ls in (18 <=? z0 suf) && ValidP5Chain suf)
  | ModeE_ge2 ls k c ds =>
      if negb (GoodDs ds) || negb (checkDs2 s) || negb (checkDs1Phi1 s) then false
      else if k mod 2 =? 0 then
        if negb (ValidEvenLs ls) then false
        else if negb ((k <=? 2 * c + 4) && (k + prefSumW ls <=? 2 * c + 6)) then false
        else
          let ok_phi :=
            if negb (isHeadP5 ls) then
              let is_start := isHeadP3z1 ls && ((k =? 0) && (c =? 0) && nat_list_eqb ds []) in
              let is_phi1 := (nat_list_eqb ds [] && (c + epW ls =? 1)) && MustDrain ls &&
                ((c + ep ls =? 1) && (k + epSum ls + 2 * ep ls =? 2)) &&
                hasP5 ls && ((16 <=? preP5Val ls) && (38 <=? z0 (p5Suf ls))) in
              is_phi1 || GoodPhiW (c + epW ls) ds is_start
            else
              ((c =? 0) && nat_list_eqb ds [] && (k =? 2)) || ((1 <=? c) && GoodPhiW (c - 1) ds false) in
          if negb ok_phi then false
          else if MustDrain ls && (2 * c + 4 <? k + epSum ls) then false
          else
            let is_reset := ((k =? 0) && (c =? 0) && nat_list_eqb ds []) && isHeadP3z1 ls in
            let ok_rst :=
              if is_reset then
                match drop1L ls with
                | [] => true
                | rest => isP3zGe1P5 rest
                end
              else true in
            if negb ok_rst then false
            else if hasOdd ls && (k + epSum ls <=? 2 * c + 4) then
              let psi := c + ep ls in
              let xi := k + epSum ls + 2 * ep ls in
              if is_reset then true
              else
                GoodPsi psi ds &&
                (negb (nat_list_eqb ds [1] && (24 <=? psi)) || (36 <=? xi)) &&
                (negb ((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (8 <=? psi) && (negb (hasP5 ls) || MustDrain ls)) || (16 <=? xi)) &&
                (negb (MustDrain ls) || ((14 <=? xi) && (7 <=? psi)) ||
                  (nat_list_eqb ds [] && (psi =? 1) && (xi =? 2) && (16 <=? preP5Val ls) && (38 <=? z0 (p5Suf ls))))
            else true
      else
        if negb (ValidP5Chain ls) then false
        else if negb ((1 <=? c) && (k <=? 2 * c + 3)) then false
        else
          let cz := c + z0 ls in
          let kz := k + 2 * z0 ls in
          if nat_list_eqb ds [] && (k =? 1) && (c =? 1) && isP3zP5 ls && (3 <=? headP3zVal ls) then true
          else if nat_list_eqb ds [] &&
              (((k =? 1) && (c =? 1) && (z0 ls =? 1)) || ((k =? 3) && (c =? 2) && (z0 ls =? 0))) &&
              isP3zP5 (dropZ0 ls) && (18 <=? headP3zVal (dropZ0 ls)) && (38 <=? z0 (p5Suf ls)) then true
          else
            let ok_base :=
              if match ds with | d :: _ => 3 <=? d | [] => false end then (20 <=? cz) && (15 <=? kz)
              else (8 <=? cz) && (15 <=? kz) in
            ok_base &&
            (negb (((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (9 <=? cz)) || isOddDrainDs ds) || (17 <=? kz)) &&
            (negb (nat_list_eqb ds [1]) || (37 <=? kz)) &&
            (negb (isDGe25One ds) || (36 <=? cz))
  | ModeB_ge3 ls a c ds =>
      if negb (GoodDs ds) || negb (checkDs2 s) || negb (checkDs1Phi1 s) then false
      else if a mod 2 =? 0 then
        if negb (ValidEvenLs ls) then false
        else
          let ok_phi :=
            if negb (isHeadP5 ls) then
              let is_phi1 := (nat_list_eqb ds [] && (c + epW ls =? 1)) && MustDrain ls &&
                ((c + ep ls =? 1) && (a + epSum ls + 2 * ep ls + 2 =? 2)) &&
                hasP5 ls && ((16 <=? preP5Val ls) && (38 <=? z0 (p5Suf ls))) in
              (a + prefSumW ls <=? 2 * c + 4) &&
              (is_phi1 || GoodPhiW (c + epW ls) ds false) &&
              (negb (c =? 0) || (1 <=? epW (p3z a :: ls)))
            else
              if c =? 0 then nat_list_eqb ds [] && ((a =? 0) || ((22 <=? a) && (38 <=? z0 (p5Suf ls))))
              else GoodPhiW (c - 1) ds false in
          if negb ok_phi then false
          else if MustDrain ls && (2 * c + 2 <? a + epSum ls) then false
          else if hasOdd ls && (a + epSum ls <=? 2 * c + 2) then
            let psi := c + ep ls in
            let xi := a + epSum ls + 2 * ep ls + 2 in
            GoodPsi psi ds &&
            (negb (nat_list_eqb ds [1] && (24 <=? psi)) || (36 <=? xi)) &&
            (negb ((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (8 <=? psi) && (negb (hasP5 ls) || MustDrain ls)) || (16 <=? xi)) &&
            (negb (MustDrain ls) || ((14 <=? xi) && (7 <=? psi)) ||
              (nat_list_eqb ds [] && (psi =? 1) && (xi =? 2) && (16 <=? preP5Val ls) && (38 <=? z0 (p5Suf ls))))
          else true
      else
        if (c =? 0) && negb (nat_list_eqb ds [] && (23 <=? a) && isHeadP5 ls && (38 <=? z0 (p5Suf ls))) then false
        else
          let nls := p3z a :: ls in
          if negb (ValidEvenLs nls) then false
          else
            let is_reset := (a =? 1) && (c =? 1) && nat_list_eqb ds [] in
            let ok_c1 :=
              if 1 <=? c then
                let is_phi1 := (nat_list_eqb ds [] && (c =? 2) && (a =? 3)) && MustDrain nls &&
                  hasP5 ls && ((16 <=? preP5Val nls) && (38 <=? z0 (p5Suf ls))) in
                if negb is_reset then is_phi1 || GoodPhiW (c - 1) ds false
                else match ls with | [] => true | _ => isP3zGe1P5 ls end
              else true in
            if negb ok_c1 then false
            else if MustDrain nls && (2 * c + 3 <? a) then false
            else if a <=? 2 * c + 3 then
              let psi := c - 1 in
              if is_reset then true
              else
                GoodPsi psi ds &&
                (negb (nat_list_eqb ds [1] && (24 <=? psi)) || (37 <=? a)) &&
                (negb ((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (8 <=? psi) && (negb (hasP5 ls) || MustDrain nls)) || (17 <=? a)) &&
                (negb (MustDrain nls) || ((15 <=? a) && (7 <=? psi)) ||
                  (nat_list_eqb ds [] && (psi =? 1) && (a =? 3) && (16 <=? preP5Val nls) && (38 <=? z0 (p5Suf ls))))
            else true
  | ModeE_c1 ls k ds =>
      if negb (GoodDs ds) || negb (checkDs2 s) || negb (checkDs1Phi1 s) || negb (ValidEvenLs ls) then false
      else
        let ok_phi :=
          if nat_list_eqb ds [] && (epW ls =? 0) then
            (k <=? 1) && isP3zP5 ls &&
            (let m0 := headP3zVal ls in
             ((k =? 0) && (m0 =? 0)) || ((22 - 2 * k <=? m0) && (38 <=? z0 (p5Suf ls))))
          else
            ((k <=? 1) && (1 <=? epW ls) && (2 * k + prefSumW ls <=? 4)) && GoodPhiW (epW ls - 1) ds false in
        if negb ok_phi then false
        else if MustDrain ls && (2 <? 2 * k + epSum ls) then false
        else if hasOdd ls && (2 * k + epSum ls <=? 2) then
          let psi := ep ls - 1 in
          let xi := 2 * k + epSum ls + 2 * ep ls in
          GoodPsi psi ds &&
          (negb (nat_list_eqb ds [1] && (24 <=? psi)) || (36 <=? xi)) &&
          (negb ((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (8 <=? psi) && (negb (hasP5 ls) || MustDrain ls)) || (16 <=? xi)) &&
          (negb (MustDrain ls) || ((14 <=? xi) && (7 <=? psi)))
        else true
  | ModeB_b2 ls m ds =>
      if negb (GoodDs ds) || negb (checkDs2 s) || negb (checkDs1Phi1 s) || negb (ValidEvenLs ls) then false
      else if 2 <=? m then (nat_list_eqb ds [] && (4 <=? m)) && isHeadP5 ls
      else
        let ok_phi :=
          if nat_list_eqb ds [] && (epW ls =? 0) then
            (m <=? 1) && isP3zP5 ls &&
            (let m0 := headP3zVal ls in (20 - 2 * m <=? m0) && (38 <=? z0 (p5Suf ls)))
          else
            ((m <=? 1) && (1 <=? epW ls) && (2 * m + prefSumW ls <=? 2)) && GoodPhiW (epW ls - 1) ds false in
        if negb ok_phi then false
        else if MustDrain ls && (0 <? 2 * m + epSum ls) then false
        else if hasOdd ls && (2 * m + epSum ls <=? 0) then
          let psi := ep ls - 1 in
          let xi := 2 * m + epSum ls + 2 * ep ls + 2 in
          GoodPsi psi ds &&
          (negb (nat_list_eqb ds [1] && (24 <=? psi)) || (36 <=? xi)) &&
          (negb ((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (8 <=? psi) && (negb (hasP5 ls) || MustDrain ls)) || (16 <=? xi)) &&
          (negb (MustDrain ls) || ((14 <=? xi) && (7 <=? psi)))
        else true
  end.

Definition invChain (fuel : nat) (s : State270) : bool :=
  match s with
  | ModeB_blank ls a =>
      checkResetSufAux fuel (a - 4) (drop1L ls)
  | ModeE_ge2 ls k c ds =>
      if k mod 2 =? 0 then
        if (k =? 0) && (c =? 0) && nat_list_eqb ds [] && isHeadP3z1 ls then
          match drop1L ls with
          | [] => checkChainAux fuel true [] 3 0 8 [1]
          | rest => checkResetSufAux fuel (headP3zVal rest) (drop2L rest)
          end
        else
          checkChainAux fuel true ls (c + 1) k (2 * c + 4) ds
      else
        if nat_list_eqb ds [] && (k =? 1) && (c =? 1) && isP3zP5 ls && (3 <=? headP3zVal ls) then
          checkResetSufAux fuel (headP3zVal ls - 2) (drop2L ls)
        else if nat_list_eqb ds [] &&
            (((k =? 1) && (c =? 1) && (z0 ls =? 1)) || ((k =? 3) && (c =? 2) && (z0 ls =? 0))) &&
            isP3zP5 (dropZ0 ls) && (18 <=? headP3zVal (dropZ0 ls)) && (38 <=? z0 (p5Suf ls)) then
          let rem := dropZ0 ls in
          checkChainAux fuel true (p3z (headP3zVal rem - 4) :: p5 :: drop2L rem) 5 0 12 [2]
        else
          checkChainAux fuel false ls c k 0 ds
  | ModeB_ge3 ls a c ds =>
      if a mod 2 =? 0 then
        let ok := checkChainAux fuel true (p3z a :: ls) c 0 (2 * c + 2) ds in
        if isHeadP5 ls && (c =? 0) && (22 <=? a) then
          ok && checkChainAux fuel true (p3z (a - 8) :: p5 :: drop1L ls) 5 0 12 [2]
        else ok
      else
        if (a =? 1) && (c =? 1) && nat_list_eqb ds [] then
          match ls with
          | [] => checkChainAux fuel true [] 3 0 8 [1]
          | _ => checkResetSufAux fuel (headP3zVal ls) (drop2L ls)
          end
        else
          let ok := checkChainAux fuel true (p3z a :: ls) c 0 (2 * c + 2) ds in
          if c =? 0 then
            ok && checkChainAux fuel true (p3z (a - 8) :: p5 :: drop1L ls) 5 0 12 [2]
          else ok
  | ModeE_c1 ls k ds =>
      let ok := checkChainAux fuel true ls 0 (2 * k) 2 ds in
      if nat_list_eqb ds [] && (epW ls =? 0) then
        let m0 := headP3zVal ls in
        if negb ((k =? 0) && (m0 =? 0)) then
          ok && checkChainAux fuel true (p3z (m0 - 6 - 2 * (1 - k)) :: p5 :: drop2L ls) 5 0 12 [2]
        else ok
      else ok
  | ModeB_b2 ls m ds =>
      if 2 <=? m then
        checkResetSufAux fuel (m - 3) (drop1L ls)
      else
        let ok := checkChainAux fuel true ls 0 2 (2 - 2 * m) ds in
        if nat_list_eqb ds [] && (epW ls =? 0) then
          let m0 := headP3zVal ls in
          ok && checkChainAux fuel true (p3z (m0 - 4 - 2 * (1 - m)) :: p5 :: drop2L ls) 5 0 12 [2]
        else ok
  end.

Definition Inv (s : State270) : Prop :=
  invCore s = true /\ forall fuel : nat, invChain fuel s = true.

(* ========================================================================== *)
(* Section 3: TM Step Simulation (`step_toCfg`)                               *)
(* ========================================================================== *)

Ltac step_if_in H :=
  lazymatch type of H with
  | (if ?c then _ else _) = _ => destruct c eqn:?; cbn [andb orb negb] in H
  end.

Lemma GoodDs_pair_ge3 (d d2 : nat) (ds2 : list nat) :
  GoodDs (d :: d2 :: ds2) = true -> 3 <= d.
Proof.
  destruct ds2 as [|d3 ds3]; unfold GoodDs; cbn [GoodDsAux]; unfold GoodDs2; intro H.
  - step_if_in H; [lia |].
    step_if_in H; [lia |].
    step_if_in H; [discriminate |].
    step_if_in H; [discriminate |].
    step_if_in H; [discriminate | lia].
  - step_if_in H; [discriminate |].
    step_if_in H; [discriminate |].
    step_if_in H; [discriminate |].
    step_if_in H; [discriminate |].
    step_if_in H; [discriminate | lia].
Qed.

Lemma GoodDs_second_zero_ge8 (d : nat) (ds2 : list nat) :
  GoodDs (d :: 0 :: ds2) = true -> 8 <= d.
Proof.
  destruct ds2 as [|d3 ds3]; unfold GoodDs; cbn [GoodDsAux]; unfold GoodDs2; intro H.
  - change (0 =? 0) with true in H; cbn [andb orb negb] in H; lia.
  - change (0 <? 3) with true in H; cbn [andb orb negb] in H; discriminate.
Qed.

Lemma default_append_zeros2 :
  (0inf%sym <* [1; 1; 0]%sym) = (0inf%sym <* [1; 1; 0; 0; 0]%sym).
Proof.
  cbn [Str_app]. repeat f_equal.
  rewrite z0_const, z0_const. reflexivity.
Qed.

Lemma default_append_zeros3 :
  (0inf%sym <* [0]%sym) = (0inf%sym <* [0; 0; 0]%sym).
Proof.
  cbn [Str_app]. rewrite !z0_const. reflexivity.
Qed.

Lemma o_one_split (n : nat) (r : side) :
  [0]%sym *> (O_u ^^ (n + 1) *> r) = [0; 1]%sym *> (O_u ^^ n *> r).
Proof.
  rewrite (pow_succ_append_right O_u n).
  unfold O_u at 1. rewrite <- Str_app_assoc. reflexivity.
Qed.

Lemma o_two_split (n : nat) (r : side) :
  [0]%sym *> (O_u ^^ (n + 2) *> r) = [0; 1; 1]%sym *> (O_u ^^ n *> r).
Proof.
  replace (n + 2) with (2 + n) by lia.
  rewrite (pow_add_append_right O_u 2 n).
  cbn [lpow app]; unfold O_u at 1 2; rewrite <- Str_app_assoc. reflexivity.
Qed.

Lemma step_ModeE_p3z1_after_sweep (ls' : list LTok) (b : nat) (ds : list nat) :
  ((evalL ls' <* [1; 1; 0]%sym) {{D}}> ([0]%sym *> (O_u ^^ (b + 2) *> evalR ds))) -->+
  toCfg (nextModeE_p3z1 ls' b ds).
Proof.
  revert b ds. induction ls' as [|[m' | ] ls'' IH]; intros b ds.
  - cbn [nextModeE_p3z1 toCfg evalL Nat.add].
    rewrite default_append_zeros2.
    replace (b + 2) with ((b + 1) + 1) by lia.
    rewrite !o_one_split.
    apply step_D_0011.
  - destruct m' as [|[|m2]].
    + cbn [nextModeE_p3z1 toCfg evalL Nat.add].
      change (((evalL ls'' <* [1; 1; 0]%sym) <* Z_u ^^ 0) <* [1; 1; 0]%sym)
        with ((evalL ls'' <* [0; 1; 1; 0]%sym) <* O_u ^^ (1 + 1)).
      replace (b + 1 + 2) with ((b + 2) + 1) by lia.
      rewrite (o_one_split (b + 2)).
      apply (merge_011 1 (evalL ls'') (O_u ^^ (b + 2) *> evalR ds)).
    + cbn [nextModeE_p3z1 evalL].
      change (((evalL ls'' <* [1; 1; 0]%sym) <* Z_u ^^ 1) <* [1; 1; 0]%sym)
        with ((evalL ls'' <* [1; 1; 0]%sym) <* [1; 1; 0; 0]%sym).
      replace (b + 2) with ((b + 1) + 1) by lia.
      rewrite (o_one_split (b + 1)).
      eapply ptrans; [apply step_D_p3z1_pop |].
      replace ([0; 1; 1; 0; 1; 1]%sym *> (O_u ^^ (b + 1) *> evalR ds))
        with ([0]%sym *> (O_u ^^ (0 + 2) *> evalR ((b + 1) :: ds))).
      * apply IH.
      * cbn [evalR Nat.add]. unfold O_u at 1 2.
        replace (b + 1 + 2) with ((b + 1) + 2) by lia.
        rewrite (o_two_split (b + 1)).
        cbn [Str_app]. reflexivity.
    + cbn [nextModeE_p3z1 toCfg evalL].
      replace (S (S m2)) with (m2 + 2) by lia.
      rewrite (pow_add_append_left (evalL ls'' <* [1; 1; 0]%sym) Z_u m2 2).
      change ((((evalL ls'' <* [1; 1; 0]%sym) <* Z_u ^^ m2) <* Z_u ^^ 2) <* [1; 1; 0]%sym)
        with (((evalL ls'' <* [1; 1; 0]%sym) <* Z_u ^^ m2) <* [1; 1; 0; 0; 0]%sym).
      replace (b + 2) with ((b + 1) + 1) by lia.
      rewrite !o_one_split.
      change (0 + 4) with 4.
      apply step_D_0011.
  - cbn [nextModeE_p3z1 toCfg evalL].
    change ((evalL ls'' <* [1; 0; 1; 1; 0]%sym) <* [1; 1; 0]%sym)
      with ((evalL ls'' <* [0; 1; 0; 1; 1; 0]%sym) <* O_u ^^ (1 + 1)).
    replace (b + 2 + 2) with ((b + 2) + 2) by lia.
    rewrite (o_two_split (b + 2)).
    change (1 + 4) with (1 + 4).
    apply (merge_p5 1 (evalL ls'') (O_u ^^ (b + 2) *> evalR ds)).
Qed.

Lemma step_toCfg (s : State270) :
  Inv s -> toCfg s -->+ toCfg (nextState s).
Proof.
  intros [Hcore _].
  destruct s as [ls k ds | ls k c ds | ls a c ds | ls m ds | ls a].
  - (* ModeE_c1 *)
    destruct ls as [|[m | ] ls'].
    + cbn [nextState toCfg evalL].
      rewrite default_append_zeros3.
      replace (m0Of k + 5) with ((k0Of k + 3) + 2) by (destruct k; cbn [m0Of k0Of]; lia).
      replace (k0Of k + 4) with ((k0Of k + 3) + 1) by lia.
      change ([0; 1; 1]%sym *> evalR ds) with ([0; 1]%sym *> ([1]%sym *> evalR ds)).
      apply (left_sweep_to_B (k0Of k + 3) 0inf%sym ([1]%sym *> evalR ds)).
    + destruct m as [|[|m2]].
      * cbn [nextState toCfg evalL].
        change (((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ 0) <* [0]%sym)
          with (evalL ls' <* [0; 1; 1; 0]%sym).
        replace (k0Of k + 4) with ((k0Of k + 3) + 1) by lia.
        replace (k0Of k + 2 + 4) with ((k0Of k + 3) + 3) by lia.
        change ([0]%sym *> (O_u ^^ (0 + 2) *> evalR ds))
          with ([0; 1]%sym *> ([1]%sym *> evalR ds)).
        apply (merge_011 (k0Of k + 3) (evalL ls') ([1]%sym *> evalR ds)).
      * cbn [nextState toCfg evalL].
        change (((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ 1) <* [0]%sym)
          with ((evalL ls' <* [1; 1; 0]%sym) <* [0; 0]%sym).
        replace (k0Of k + 4) with ((k0Of k + 3) + 1) by lia.
        eapply ptrans; [apply (left_sweep_to_hub (k0Of k + 3) (evalL ls' <* [1; 1; 0]%sym) ([1]%sym *> evalR ds)) |].
        replace (k0Of k + 3 + 1) with (k0Of k + 2 + 2) by lia.
        change ([0; 1]%sym *> ([1]%sym *> evalR ds)) with (evalR (0 :: ds)).
        apply step_ModeE_p3z1_after_sweep.
      * cbn [nextState toCfg evalL].
        replace (S (S m2)) with (m2 + 2) by lia.
        rewrite (pow_add_append_left (evalL ls' <* [1; 1; 0]%sym) Z_u m2 2).
        change ((((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ m2) <* Z_u ^^ 2) <* [0]%sym)
          with (((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ m2) <* [0; 0; 0]%sym).
        replace (m0Of k + 5) with ((k0Of k + 3) + 2) by (destruct k; cbn [m0Of k0Of]; lia).
        replace (k0Of k + 4) with ((k0Of k + 3) + 1) by lia.
        change ([0; 1; 1]%sym *> evalR ds) with ([0; 1]%sym *> ([1]%sym *> evalR ds)).
        apply (left_sweep_to_B (k0Of k + 3) ((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ m2) ([1]%sym *> evalR ds)).
    + cbn [nextState toCfg evalL].
      change ((evalL ls' <* [1; 0; 1; 1; 0]%sym) <* [0]%sym)
        with (evalL ls' <* [0; 1; 0; 1; 1; 0]%sym).
      replace (k0Of k + 4) with ((k0Of k + 3) + 1) by lia.
      replace (k0Of k + 3 + 4) with ((k0Of k + 3) + 4) by lia.
      change ([0]%sym *> (O_u ^^ (1 + 2) *> evalR ds))
        with ([0; 1; 1]%sym *> ([1]%sym *> evalR ds)).
      apply (merge_p5 (k0Of k + 3) (evalL ls') ([1]%sym *> evalR ds)).
  - (* ModeE_ge2 *)
    destruct ls as [|[m | ] ls'].
    + cbn [nextState toCfg evalL].
      rewrite default_append_zeros3.
      replace (k + 4) with ((k + 3) + 1) by lia.
      replace (k + 5) with ((k + 3) + 2) by lia.
      replace (c + 3) with ((c + 2) + 1) by lia.
      rewrite (o_one_split (c + 2)).
      apply (left_sweep_to_B (k + 3) 0inf%sym (O_u ^^ (c + 2) *> evalR ds)).
    + destruct m as [|[|m2]].
      * cbn [nextState toCfg evalL].
        change (((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ 0) <* [0]%sym)
          with (evalL ls' <* [0; 1; 1; 0]%sym).
        replace (k + 4) with ((k + 3) + 1) by lia.
        replace (k + 2 + 4) with ((k + 3) + 3) by lia.
        replace (c + 1 + 2) with ((c + 2) + 1) by lia.
        rewrite (o_one_split (c + 2)).
        apply (merge_011 (k + 3) (evalL ls') (O_u ^^ (c + 2) *> evalR ds)).
      * cbn [nextState toCfg evalL].
        change (((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ 1) <* [0]%sym)
          with ((evalL ls' <* [1; 1; 0]%sym) <* [0; 0]%sym).
        replace (k + 4) with ((k + 3) + 1) by lia.
        eapply ptrans; [apply (left_sweep_to_hub (k + 3) (evalL ls' <* [1; 1; 0]%sym) (O_u ^^ (c + 2) *> evalR ds)) |].
        replace (k + 3 + 1) with (k + 2 + 2) by lia.
        replace ([0; 1]%sym *> (O_u ^^ (c + 2) *> evalR ds)) with (evalR ((c + 1) :: ds)).
        -- apply step_ModeE_p3z1_after_sweep.
        -- cbn [evalR]. replace (c + 1 + 2) with ((c + 2) + 1) by lia.
           apply o_one_split.
      * cbn [nextState toCfg evalL].
        replace (S (S m2)) with (m2 + 2) by lia.
        rewrite (pow_add_append_left (evalL ls' <* [1; 1; 0]%sym) Z_u m2 2).
        change ((((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ m2) <* Z_u ^^ 2) <* [0]%sym)
          with (((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ m2) <* [0; 0; 0]%sym).
        replace (k + 4) with ((k + 3) + 1) by lia.
        replace (k + 5) with ((k + 3) + 2) by lia.
        replace (c + 3) with ((c + 2) + 1) by lia.
        rewrite (o_one_split (c + 2)).
        apply (left_sweep_to_B (k + 3) ((evalL ls' <* [1; 1; 0]%sym) <* Z_u ^^ m2) (O_u ^^ (c + 2) *> evalR ds)).
    + cbn [nextState toCfg evalL].
      change ((evalL ls' <* [1; 0; 1; 1; 0]%sym) <* [0]%sym)
        with (evalL ls' <* [0; 1; 0; 1; 1; 0]%sym).
      replace (k + 4) with ((k + 3) + 1) by lia.
      replace (k + 3 + 4) with ((k + 3) + 4) by lia.
      replace (c + 2 + 2) with ((c + 2) + 2) by lia.
      rewrite (o_two_split (c + 2)).
      apply (merge_p5 (k + 3) (evalL ls') (O_u ^^ (c + 2) *> evalR ds)).
  - (* ModeB_ge3 *)
    cbn [toCfg].
    replace (c + 3) with ((c + 1) + 2) by lia.
    rewrite (o_two_split (c + 1)).
    change ([0; 1; 1]%sym *> (O_u ^^ (c + 1) *> evalR ds))
      with ([0; 1]%sym *> ([1]%sym *> (O_u ^^ (c + 1) *> evalR ds))).
    eapply ptrans; [apply sweep_R |].
    change ([0; 1; 1; 1; 0]%sym *> ([1]%sym *> (O_u ^^ (c + 1) *> evalR ds)))
      with ([0; 1; 1; 1; 0; 1]%sym *> (O_u ^^ (c + 1) *> evalR ds)).
    eapply pe_trans; [apply thm_A_0 |].
    destruct c as [|c'].
    + cbn [nextState toCfg evalL k0Of Nat.add lpow app Str_app].
      apply evstep_refl'; reflexivity.
    + cbn [nextState toCfg evalL Nat.add].
      replace (S (c' + 1)) with (c' + 2) by lia.
      apply evstep_refl'; reflexivity.
  - (* ModeB_b2 *)
    assert (Hgd : GoodDs ds = true).
    { cbn [invCore] in Hcore.
      destruct (GoodDs ds); [reflexivity | discriminate]. }
    destruct m as [|m'].
    + cbn [nextState toCfg m0Of k0Of Nat.add lpow app Str_app].
      apply bridge_b2_m0.
    + cbn [toCfg m0Of].
      change ([0; 1; 1]%sym *> evalR ds) with ([0; 1]%sym *> ([1]%sym *> evalR ds)).
      eapply ptrans; [apply (sweep_R (m' + 2) (evalL ls) ([1]%sym *> evalR ds)) |].
      rewrite (pow_add_append_left (evalL ls <* [1; 1; 0]%sym) Z_u m' 2).
      change (Z_u ^^ 2) with [0; 0]%sym.
      change ([0; 1; 1; 1; 0]%sym *> ([1]%sym *> evalR ds))
        with ([0; 1; 1; 1; 0; 1]%sym *> evalR ds).
      eapply ptrans; [apply bridge_b2_tail |].
      set (l_base := (evalL ls <* [1; 1; 0]%sym) <* Z_u ^^ m').
      destruct ds as [|d' ds'].
      * cbn [nextState toCfg evalL evalR].
        apply bridge_b5a.
      * cbn [evalR].
        change ([0; 1; 1; 1; 1; 1; 0; 1]%sym *> ([0]%sym *> (O_u ^^ (d' + 2) *> evalR ds')))
          with ([0; 1; 1; 1; 1; 1; 0; 1; 0]%sym *> (O_u ^^ (d' + 2) *> evalR ds')).
        eapply pe_trans; [apply bridge_b5b_pre |].
        destruct d' as [|[|[|m'']]].
        -- destruct ds' as [|d2 ds'']; [| exfalso; pose proof (GoodDs_pair_ge3 _ _ _ Hgd); lia].
           cbn [nextState toCfg evalL evalR Nat.add lpow app Str_app].
           apply pev, bridge_b5b_d0_blank.
        -- destruct ds' as [|d2 ds'']; [| exfalso; pose proof (GoodDs_pair_ge3 _ _ _ Hgd); lia].
           cbn [nextState toCfg evalL evalR Nat.add lpow app Str_app].
           apply pev, bridge_b5b_d1_blank.
        -- destruct ds' as [|d2 ds'']; [| exfalso; pose proof (GoodDs_pair_ge3 _ _ _ Hgd); lia].
           cbn [nextState toCfg evalL evalR Nat.add lpow app Str_app].
           apply pev, bridge_b5b_d2_blank.
        -- destruct ds' as [|d_next ds''].
           ++ cbn [nextState toCfg evalL evalR].
              replace (S (S (S m'')) + 2) with (m'' + 5) by lia.
              apply evstep_refl'; reflexivity.
           ++ destruct d_next as [|c'].
              ** destruct m'' as [|[|m4]];
                   [exfalso; pose proof (GoodDs_second_zero_ge8 _ _ Hgd); lia .. |].
                 cbn [nextState toCfg evalL evalR m0Of].
                 replace (S (S (S (S (S m4)))) + 2) with (m4 + 2 + 5) by lia.
                 replace (m4 + 1) with (S m4) by lia.
                 cbn [m0Of evalR Nat.add lpow app Str_app].
                 apply evstep_refl'; reflexivity.
              ** cbn [nextState toCfg evalL evalR].
                 replace (S (S (S m'')) + 2) with (m'' + 5) by lia.
                 replace (S c' + 2) with (c' + 3) by lia.
                 apply evstep_refl'; reflexivity.
  - (* ModeB_blank *)
    assert (Ha5 : 5 <= a).
    { cbn [invCore] in Hcore.
      destruct (5 <=? a) eqn:Ea; [lia | discriminate]. }
    destruct a as [|[|a'']]; [lia | lia |].
    cbn [nextState toCfg evalL evalR].
    replace (S (S a'') + 5) with ((a'' + 3) + 4) by lia.
    eapply ptrans; [apply sweep_blank_R |].
    rewrite (pow_add_append_left (evalL ls <* [1; 1; 0]%sym) Z_u a'' 3).
    change (Z_u ^^ 3) with [0; 0; 0]%sym.
    change (1 + 4) with 5.
    change (1 + 2) with 3.
    cbn [lpow app]; unfold O_u at 2; cbn [Str_app].
    apply bridge_blank_apos_tail.
Qed.

(* ========================================================================== *)


(* Section 4: Inductive Invariant Preservation (`step_Inv`)                   *)
(* ========================================================================== *)

Lemma nat_list_eqb_refl (xs : list nat) : nat_list_eqb xs xs = true.
Proof. destruct (nat_list_eqb_spec xs xs); [reflexivity | congruence]. Qed.

Lemma nat_list_eqb_true (xs ys : list nat) : nat_list_eqb xs ys = true <-> xs = ys.
Proof. destruct (nat_list_eqb_spec xs ys); split; congruence. Qed.

Lemma nat_list_eqb_false (xs ys : list nat) : nat_list_eqb xs ys = false <-> xs <> ys.
Proof. destruct (nat_list_eqb_spec xs ys); split; congruence. Qed.

Lemma if_pos_b {A : Type} {c : bool} {t e : A} :
  c = true -> (if c then t else e) = t.
Proof. intro Hc; rewrite Hc; reflexivity. Qed.

Lemma if_neg_b {A : Type} {c : bool} {t e : A} :
  c = false -> (if c then t else e) = e.
Proof. intro Hc; rewrite Hc; reflexivity. Qed.

Lemma if_false_true (c rest : bool) :
  c = false -> rest = true -> (if c then false else rest) = true.
Proof. intros -> ->; reflexivity. Qed.

Lemma if_negb_false_true (g rest : bool) :
  g = true -> rest = true -> (if negb g then false else rest) = true.
Proof. intros -> ->; reflexivity. Qed.

Lemma unpack_if_false (c rest : bool) :
  (if c then false else rest) = true -> c = false /\ rest = true.
Proof. destruct c, rest; cbn; intros; split; congruence. Qed.

Lemma unpack_if_negb_false (g rest : bool) :
  (if negb g then false else rest) = true -> g = true /\ rest = true.
Proof. destruct g, rest; cbn; intros; split; congruence. Qed.

Ltac find_top_if e :=
  lazymatch e with
  | if ?c then _ else _ =>
      lazymatch c with
      | context [if _ then _ else _] => find_top_if c
      | _ => c
      end
  | negb ?a => find_top_if a
  | ?a =? ?b =>
      lazymatch a with
      | context [if _ then _ else _] => find_top_if a
      | _ => find_top_if b
      end
  | ?a <=? ?b =>
      lazymatch a with
      | context [if _ then _ else _] => find_top_if a
      | _ => find_top_if b
      end
  | ?a <? ?b =>
      lazymatch a with
      | context [if _ then _ else _] => find_top_if a
      | _ => find_top_if b
      end
  | ?a <= ?b =>
      lazymatch a with
      | context [if _ then _ else _] => find_top_if a
      | _ => find_top_if b
      end
  | ?a || ?b =>
      lazymatch a with
      | context [if _ then _ else _] => find_top_if a
      | _ => find_top_if b
      end
  | ?a && ?b =>
      lazymatch a with
      | context [if _ then _ else _] => find_top_if a
      | _ => find_top_if b
      end
  | ?lhs = ?rhs =>
      lazymatch lhs with
      | context [if _ then _ else _] => find_top_if lhs
      | _ => find_top_if rhs
      end
  end.

Ltac rw_if_pos tac :=
  let g := match goal with |- ?G => G end in
  let c := find_top_if g in
  rewrite (@if_pos_b _ c _ _ ltac:(tac)).

Ltac rw_if_neg tac :=
  let g := match goal with |- ?G => G end in
  let c := find_top_if g in
  rewrite (@if_neg_b _ c _ _ ltac:(tac)).

Ltac rw_if_pos_in H tac :=
  let t := type of H in
  let c := find_top_if t in
  rewrite (@if_pos_b _ c _ _ ltac:(tac)) in H.

Ltac rw_if_neg_in H tac :=
  let t := type of H in
  let c := find_top_if t in
  rewrite (@if_neg_b _ c _ _ ltac:(tac)) in H.

Lemma z0_z0Rep (n : nat) (rest : list LTok) : z0 (z0Rep n rest) = n + z0 rest.
Proof. induction n as [|n IH]; cbn [z0Rep z0]; lia. Qed.

Lemma ep_z0Rep (n : nat) (rest : list LTok) : ep (z0Rep n rest) = n + ep rest.
Proof. induction n as [|n IH]; cbn [z0Rep ep]; [lia | change (0 mod 2 =? 1) with false; lia]. Qed.

Lemma epSum_z0Rep (n : nat) (rest : list LTok) : epSum (z0Rep n rest) = epSum rest.
Proof. induction n as [|n IH]; cbn [z0Rep epSum]; [reflexivity | change (0 mod 2 =? 1) with false; lia]. Qed.

Lemma hasOdd_z0Rep (n : nat) (rest : list LTok) : hasOdd (z0Rep n rest) = hasOdd rest.
Proof. induction n as [|n IH]; cbn [z0Rep hasOdd]; [reflexivity | exact IH]. Qed.

Lemma hasP5_z0Rep (n : nat) (rest : list LTok) : hasP5 (z0Rep n rest) = hasP5 rest.
Proof. induction n as [|n IH]; cbn [z0Rep hasP5]; [reflexivity | exact IH]. Qed.

Lemma MustDrain_z0Rep (n : nat) (rest : list LTok) : MustDrain (z0Rep n rest) = MustDrain rest.
Proof. induction n as [|n IH]; cbn [z0Rep MustDrain]; [reflexivity | exact IH]. Qed.

Lemma p5Suf_z0Rep (n : nat) (rest : list LTok) : p5Suf (z0Rep n rest) = p5Suf rest.
Proof. induction n as [|n IH]; cbn [z0Rep p5Suf]; [reflexivity | exact IH]. Qed.

Lemma ValidP5Chain_z0Rep (n : nat) (rest : list LTok) :
  ValidP5Chain (z0Rep n rest) = ValidP5Chain rest.
Proof. induction n as [|n IH]; cbn [z0Rep ValidP5Chain]; [reflexivity | exact IH]. Qed.

Lemma z0Rep_succ_right (n : nat) (rest : list LTok) :
  z0Rep n (p3z 0 :: rest) = z0Rep (n + 1) rest.
Proof.
  induction n as [|n IH]; [reflexivity |].
  replace (S n + 1) with (S (n + 1)) by lia.
  cbn [z0Rep]. rewrite IH. reflexivity.
Qed.

Lemma hasOdd_p3z_add2 (m : nat) (ls : list LTok) :
  hasOdd (p3z (m + 2) :: ls) = hasOdd (p3z m :: ls).
Proof. cbn [hasOdd]. replace ((m + 2) mod 2 =? 1) with (m mod 2 =? 1) by lia. reflexivity. Qed.

Lemma ep_p3z_add2 (m : nat) (ls : list LTok) :
  ep (p3z (m + 2) :: ls) = ep (p3z m :: ls).
Proof. cbn [ep]. replace ((m + 2) mod 2 =? 1) with (m mod 2 =? 1) by lia. reflexivity. Qed.

Lemma epW_p3z_add2 (m : nat) (ls : list LTok) :
  epW (p3z (m + 2) :: ls) = epW (p3z m :: ls).
Proof. cbn [epW]. replace ((m + 2) mod 2 =? 1) with (m mod 2 =? 1) by lia. reflexivity. Qed.

Lemma GoodPhiW_mono (phiW : nat) (ds : list nat) (b : bool) :
  GoodPhiW phiW ds false = true -> GoodPhiW phiW ds b = true.
Proof.
  unfold GoodPhiW; intro H.
  repeat (destruct (if _ then _ else _) eqn:? in * || step_if_in H); try congruence.
  destruct b; cbn in *; congruence.
Qed.

Lemma prefSumW_p3z_add2 (m : nat) (ls : list LTok) :
  m mod 2 = 0 -> isHeadP5 ls = false ->
  prefSumW (p3z (m + 2) :: ls) = prefSumW (p3z m :: ls) + 2.
Proof.
  intros Hm Hnp5. cbn [prefSumW].
  rewrite !if_neg_b by lia.
  destruct ls as [|[m2 | ] s]; [lia | lia | discriminate].
Qed.

Lemma epSum_p3z_add2 (m : nat) (ls : list LTok) :
  epSum (p3z (m + 2) :: ls) = epSum (p3z m :: ls) + 2.
Proof.
  cbn [epSum]. destruct (m mod 2 =? 1) eqn:E.
  - rw_if_pos ltac:(lia). lia.
  - rw_if_neg ltac:(lia). lia.
Qed.

Lemma MustDrain_p3z_add2 (m : nat) (ls : list LTok) :
  MustDrain (p3z (m + 2) :: ls) = MustDrain (p3z m :: ls).
Proof. cbn [MustDrain]. replace ((m + 2) mod 2 =? 1) with (m mod 2 =? 1) by lia. reflexivity. Qed.

Lemma ValidEvenLs_p3z_add2 (m : nat) (ls : list LTok) :
  ValidEvenLs (p3z (m + 2) :: ls) = ValidEvenLs (p3z m :: ls).
Proof. cbn [ValidEvenLs]. replace ((m + 2) mod 2 =? 0) with (m mod 2 =? 0) by lia. reflexivity. Qed.

Lemma preP5Val_p3z_add2_of_not_headP5 (m : nat) (ls : list LTok) :
  isHeadP5 ls = false -> preP5Val (p3z (m + 2) :: ls) = preP5Val (p3z m :: ls).
Proof. destruct ls as [|[|] ?]; cbn; congruence. Qed.

Lemma not_isHeadP5_of_MustDrain_p3z (m : nat) (ls : list LTok) :
  MustDrain (p3z m :: ls) = true -> isHeadP5 ls = false.
Proof.
  destruct ls as [|[|] ?]; cbn [MustDrain isHeadP5]; try reflexivity.
  destruct (m mod 2 =? 1); cbn; congruence.
Qed.

Lemma hasOdd_p3z_even_cons (k : nat) (ls : list LTok) :
  k mod 2 = 0 -> hasOdd (p3z k :: ls) = hasOdd ls.
Proof. intro Hk; cbn [hasOdd]; rw_if_neg ltac:(lia); reflexivity. Qed.

Lemma ep_p3z_even_cons (k : nat) (ls : list LTok) :
  k mod 2 = 0 -> ep (p3z k :: ls) = 1 + ep ls.
Proof. intro Hk; cbn [ep]; rw_if_neg ltac:(lia); reflexivity. Qed.

Lemma epW_p3z_even_cons (k : nat) (ls : list LTok) :
  k mod 2 = 0 -> isHeadP5 ls = false -> epW (p3z k :: ls) = 1 + epW ls.
Proof.
  intros Hk Hnp5; cbn [epW]; rw_if_neg ltac:(lia).
  destruct ls as [|[|] ?]; cbn in *; congruence.
Qed.

Lemma prefSumW_p3z_even_cons (k : nat) (ls : list LTok) :
  k mod 2 = 0 -> isHeadP5 ls = false -> prefSumW (p3z k :: ls) = k + prefSumW ls.
Proof.
  intros Hk Hnp5; cbn [prefSumW]; rw_if_neg ltac:(lia).
  destruct ls as [|[|] ?]; cbn in *; congruence.
Qed.

Lemma epSum_p3z_even_cons (k : nat) (ls : list LTok) :
  k mod 2 = 0 -> epSum (p3z k :: ls) = k + epSum ls.
Proof. intro Hk; cbn [epSum]; rw_if_neg ltac:(lia); reflexivity. Qed.

Lemma MustDrain_p3z_even_cons (k : nat) (ls : list LTok) :
  k mod 2 = 0 -> MustDrain (p3z k :: ls) = MustDrain ls.
Proof. intro Hk; cbn [MustDrain]; rw_if_neg ltac:(lia); reflexivity. Qed.

Lemma ValidEvenLs_p3z_even_cons (k : nat) (ls : list LTok) :
  k mod 2 = 0 -> ValidEvenLs (p3z k :: ls) = ValidEvenLs ls.
Proof. intro Hk; cbn [ValidEvenLs]; rw_if_pos ltac:(lia); reflexivity. Qed.

Lemma preP5Val_p3z_cons_of_not_headP5 (k : nat) (ls : list LTok) :
  isHeadP5 ls = false -> preP5Val (p3z k :: ls) = preP5Val ls.
Proof. destruct ls as [|[|] ?]; cbn; congruence. Qed.

Lemma epSum_even (ls : list LTok) : epSum ls mod 2 = 0.
Proof.
  induction ls as [|[m | ] rest IH]; cbn [epSum]; [lia | | lia].
  destruct (m mod 2 =? 1) eqn:E; lia.
Qed.

Lemma ValidP5Chain_imp_ValidEvenLs (ls : list LTok) :
  ValidP5Chain ls = true -> ValidEvenLs ls = true.
Proof.
  induction ls as [|[m | ] rest IH]; intro H; [reflexivity | | exact H].
  destruct m as [|m'].
  - cbn [ValidP5Chain] in H. cbn [ValidEvenLs]. exact (IH H).
  - destruct rest as [|[|] suf]; cbn [ValidP5Chain] in H; try discriminate.
    cbn [ValidEvenLs ValidAfterOdd]. destruct (S m' mod 2 =? 0); exact H.
Qed.

Lemma ls_eq_z0Rep_of_prefSumW_zero (ls : list LTok) :
  ValidEvenLs ls = true ->
  prefSumW ls = 0 ->
  MustDrain ls = false ->
  isHeadP5 ls = false ->
  ls = (if hasP5 ls then
          z0Rep (epW ls) (p3z (epSum ls + (if hasOdd ls then 1 else 0)) :: p5 :: p5Suf ls)
        else
          z0Rep (epW ls) []) /\
  (hasP5 ls = false -> hasOdd ls = false).
Proof.
  induction ls as [|[m | ] rest IH]; intros Heven Hpref Hmd Hnp5.
  - cbn; split; auto.
  - destruct (m mod 2 =? 1) eqn:Hm.
    + cbn [MustDrain] in Hmd. rewrite Hm in Hmd.
      destruct rest as [|[|] suf]; try discriminate.
      split; [| intro Habs; discriminate].
      cbn [hasP5 epW epSum hasOdd p5Suf]. rewrite Hm. cbn [z0Rep].
      f_equal; f_equal; clear - Hm; lia.
    + assert (Hm0 : m mod 2 = 0) by (clear - Hm; lia).
      destruct rest as [|[m2 | ] s2].
      * cbn [prefSumW] in Hpref. rewrite Hm in Hpref.
        assert (m = 0) by (clear - Hpref; lia); subst m.
        cbn; split; auto.
      * change (prefSumW (p3z m :: p3z m2 :: s2)) with
          (if m mod 2 =? 1 then 0 else m + prefSumW (p3z m2 :: s2)) in Hpref.
        rewrite Hm in Hpref.
        assert (m = 0) by (clear - Hpref; lia); subst m.
        cbn [ValidEvenLs] in Heven.
        cbn [MustDrain] in Hmd.
        destruct (IH Heven Hpref Hmd eq_refl) as [IH1 IH2].
        split; [| exact IH2].
        rewrite (epW_p3z_even_cons 0 (p3z m2 :: s2) eq_refl eq_refl).
        rewrite (epSum_p3z_even_cons 0 (p3z m2 :: s2) eq_refl), Nat.add_0_l.
        rewrite (hasOdd_p3z_even_cons 0 (p3z m2 :: s2) eq_refl).
        change (hasP5 (p3z 0 :: p3z m2 :: s2)) with (hasP5 (p3z m2 :: s2)).
        change (p5Suf (p3z 0 :: p3z m2 :: s2)) with (p5Suf (p3z m2 :: s2)).
        rewrite IH1 at 1.
        destruct (hasP5 (p3z m2 :: s2)); reflexivity.
      * split; [| intro Habs; discriminate].
        cbn [hasP5 epW epSum hasOdd p5Suf]. rewrite Hm. cbn [z0Rep].
        f_equal; f_equal; clear; lia.
  - discriminate.
Qed.

Lemma checkChainAux_false_p3z0 (fuel : nat) (ls : list LTok) (c k m_dummy : nat) (ds : list nat) :
  checkChainAux fuel false (p3z 0 :: ls) c k m_dummy ds =
  checkChainAux fuel false ls (c + 1) (k + 2) m_dummy ds.
Proof.
  destruct fuel as [|fuel]; [reflexivity |].
  cbn [checkChainAux z0 dropZ0].
  replace (c + (1 + z0 ls)) with (c + 1 + z0 ls) by lia.
  replace (k + 2 * (1 + z0 ls)) with (k + 2 + 2 * z0 ls) by lia.
  reflexivity.
Qed.

Lemma checkChainAux_true_congr (fuel : nat) (ls1 ls2 : list LTok)
    (cp1_1 kb_1 margin_1 cp1_2 kb_2 margin_2 : nat) (ds : list nat) :
  isHeadP5 ls1 = false ->
  isHeadP5 ls2 = false ->
  hasOdd ls1 = hasOdd ls2 ->
  (kb_1 + epSum ls1 <=? margin_1) = (kb_2 + epSum ls2 <=? margin_2) ->
  cp1_1 + ep ls1 = cp1_2 + ep ls2 ->
  (kb_1 + epSum ls1 <= margin_1 -> kb_1 + epSum ls1 + 2 * ep ls1 = kb_2 + epSum ls2 + 2 * ep ls2) ->
  p5Suf ls1 = p5Suf ls2 ->
  MustDrain ls1 = MustDrain ls2 ->
  hasP5 ls1 = hasP5 ls2 ->
  (MustDrain ls1 = true -> preP5Val ls1 = preP5Val ls2) ->
  cp1_1 + epW ls1 = cp1_2 + epW ls2 ->
  (~ (kb_1 + epSum ls1 <= margin_1) ->
    kb_1 + epSum ls1 + (if hasOdd ls1 then 1 else 0) - (margin_1 + 2) =
    kb_2 + epSum ls2 + (if hasOdd ls2 then 1 else 0) - (margin_2 + 2)) ->
  checkChainAux fuel true ls1 cp1_1 kb_1 margin_1 ds =
  checkChainAux fuel true ls2 cp1_2 kb_2 margin_2 ds.
Proof.
  intros Hnp1 Hnp2 Hodd Hdec Hep Hxi Hsuf Hmd Hp5 Hm2 Hepw Hrem.
  destruct fuel as [|fuel]; [reflexivity |].
  cbn [checkChainAux].
  rewrite Hnp1, Hnp2, !orb_false_l.
  destruct (kb_1 + epSum ls1 <=? margin_1) eqn:Ege1.
  - assert (Ege2 : (kb_2 + epSum ls2 <=? margin_2) = true) by congruence.
    pose proof (Hxi ltac:(clear - Ege1; lia)) as Hxi'.
    rewrite Ege2, !andb_true_r.
    rewrite <- Hodd, <- Hp5, <- Hsuf, <- Hep, <- Hxi', <- Hmd, <- Hepw.
    destruct (hasOdd ls1) eqn:Ho; cbn [andb orb negb].
    + destruct (MustDrain ls1) eqn:Hm; cbn [andb orb negb]; [| reflexivity].
      rewrite (Hm2 eq_refl). reflexivity.
    + destruct (hasP5 ls1); reflexivity.
  - assert (Ege2 : (kb_2 + epSum ls2 <=? margin_2) = false) by congruence.
    pose proof (Hrem ltac:(clear - Ege1; lia)) as Hrem'.
    rewrite Ege2, !andb_false_r.
    rewrite Hrem', <- Hodd, <- Hepw, <- Hp5, <- Hsuf.
    reflexivity.
Qed.

Lemma checkChainAux_true_no_odd_no_p5 (fuel : nat) (ls1 ls2 : list LTok)
    (cp1_1 kb_1 margin_1 cp1_2 kb_2 margin_2 : nat) (ds : list nat) :
  hasOdd ls1 = false -> hasOdd ls2 = false ->
  hasP5 ls1 = false -> hasP5 ls2 = false ->
  cp1_1 + epW ls1 = cp1_2 + epW ls2 ->
  checkChainAux fuel true ls1 cp1_1 kb_1 margin_1 ds =
  checkChainAux fuel true ls2 cp1_2 kb_2 margin_2 ds.
Proof.
  intros Ho1 Ho2 Hp1 Hp2 Hepw.
  destruct fuel as [|fuel]; [reflexivity |].
  cbn [checkChainAux].
  rewrite Ho1, Ho2, Hp1, Hp2, Hepw; cbn [andb orb negb].
  reflexivity.
Qed.

Lemma checkChainAux_true_p3z0 (fuel : nat) (ls : list LTok) (cp1 kb margin : nat) (ds : list nat) :
  (isHeadP5 ls = false \/ kb + epSum ls <= margin) ->
  checkChainAux fuel true (p3z 0 :: ls) cp1 kb margin ds =
  checkChainAux fuel true ls (cp1 + 1) (kb + 2) (margin + 2) ds.
Proof.
  intro H. destruct (isHeadP5 ls) eqn:Hp5.
  - destruct H as [H1 | Hge]; [congruence |].
    destruct ls as [|[|] suf]; try discriminate.
    cbn [epSum] in Hge.
    destruct fuel as [|fuel]; [reflexivity |].
    cbn [checkChainAux].
    change (hasOdd (p3z 0 :: p5 :: suf)) with false.
    change (epSum (p3z 0 :: p5 :: suf)) with 0.
    change (ep (p3z 0 :: p5 :: suf)) with 1.
    change (hasOdd (p5 :: suf)) with false.
    change (epSum (p5 :: suf)) with 0.
    change (ep (p5 :: suf)) with 0.
    cbn [hasP5 isHeadP5 p5Suf andb orb negb].
    rw_if_pos lia.
    replace (cp1 + 1 + 1) with (cp1 + 1 + 0 + 1) by lia.
    replace (kb + 0 + 2 * 1 + 3) with (kb + 2 + 0 + 2 * 0 + 3) by lia.
    reflexivity.
  - apply checkChainAux_true_congr; auto.
    + rewrite (epSum_p3z_even_cons 0 ls eq_refl); lia.
    + rewrite (ep_p3z_even_cons 0 ls eq_refl); lia.
    + intro; rewrite (epSum_p3z_even_cons 0 ls eq_refl), (ep_p3z_even_cons 0 ls eq_refl); lia.
    + intro; exact (preP5Val_p3z_cons_of_not_headP5 0 ls Hp5).
    + rewrite (epW_p3z_even_cons 0 ls eq_refl Hp5); lia.
    + intro; rewrite (epSum_p3z_even_cons 0 ls eq_refl), (hasOdd_p3z_even_cons 0 ls eq_refl); lia.
Qed.

Lemma checkChainAux_true_E_ge2_to_B_ge3_nil (fuel : nat) (k c : nat) (ds : list nat) :
  k mod 2 = 0 ->
  checkChainAux fuel true [] (c + 1) k (2 * c + 4) ds =
  checkChainAux fuel true [p3z k] c 0 (2 * c + 2) ds.
Proof.
  intro Hk. apply checkChainAux_true_no_odd_no_p5; auto.
  - rewrite (hasOdd_p3z_even_cons k [] Hk); reflexivity.
  - rewrite (epW_p3z_even_cons k [] Hk eq_refl); cbn [epW]; lia.
Qed.

Lemma checkChainAux_true_E_ge2_to_B_ge3_even (fuel m : nat) (ls' : list LTok) (k c : nat) (ds : list nat) :
  k mod 2 = 0 ->
  checkChainAux fuel true (p3z (m + 2) :: ls') (c + 1) k (2 * c + 4) ds =
  checkChainAux fuel true (p3z k :: p3z m :: ls') c 0 (2 * c + 2) ds.
Proof.
  intro Hk. apply checkChainAux_true_congr; auto.
  - rewrite hasOdd_p3z_add2, (hasOdd_p3z_even_cons k _ Hk); reflexivity.
  - rewrite epSum_p3z_add2, (epSum_p3z_even_cons k _ Hk); lia.
  - rewrite ep_p3z_add2, (ep_p3z_even_cons k _ Hk); lia.
  - intro; rewrite epSum_p3z_add2, (epSum_p3z_even_cons k _ Hk), ep_p3z_add2, (ep_p3z_even_cons k _ Hk); lia.
  - rewrite MustDrain_p3z_add2, (MustDrain_p3z_even_cons k _ Hk); reflexivity.
  - intro Hmd1; rewrite MustDrain_p3z_add2 in Hmd1.
    rewrite (preP5Val_p3z_add2_of_not_headP5 m ls' (not_isHeadP5_of_MustDrain_p3z m ls' Hmd1)).
    rewrite (preP5Val_p3z_cons_of_not_headP5 k (p3z m :: ls') eq_refl); reflexivity.
  - rewrite epW_p3z_add2, (epW_p3z_even_cons k (p3z m :: ls') Hk eq_refl); lia.
  - intro; rewrite epSum_p3z_add2, (epSum_p3z_even_cons k _ Hk), hasOdd_p3z_add2, (hasOdd_p3z_even_cons k _ Hk); lia.
Qed.

Lemma checkChainAux_true_E_c1_to_B_b2 (fuel m : nat) (ls' : list LTok) (k : nat) (ds : list nat) :
  k <= 1 ->
  checkChainAux fuel true (p3z (m + 2) :: ls') 0 (2 * k) 2 ds =
  checkChainAux fuel true (p3z m :: ls') 0 2 (2 - 2 * k) ds.
Proof.
  intro Hk. pose proof (epSum_even (p3z m :: ls')) as Hev.
  apply checkChainAux_true_congr; auto.
  - apply hasOdd_p3z_add2.
  - rewrite epSum_p3z_add2; lia.
  - apply ep_p3z_add2.
  - intro Hge; rewrite epSum_p3z_add2 in Hge |- *; rewrite ep_p3z_add2; lia.
  - apply MustDrain_p3z_add2.
  - intro Hmd1; rewrite MustDrain_p3z_add2 in Hmd1.
    exact (preP5Val_p3z_add2_of_not_headP5 m ls' (not_isHeadP5_of_MustDrain_p3z m ls' Hmd1)).
  - rewrite epW_p3z_add2; reflexivity.
  - intro Hlt; rewrite epSum_p3z_add2 in Hlt |- *; rewrite hasOdd_p3z_add2; lia.
Qed.

Local Opaque checkChainAux.

Lemma step_Inv_ModeB_blank (ls : list LTok) (a : nat) :
  Inv (ModeB_blank ls a) -> Inv (nextState (ModeB_blank ls a)).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  destruct ls as [|[|] suf]; cbn [isHeadP5 drop1L andb] in Hc; try (rewrite andb_false_r in Hc; discriminate).
  assert (Ha5 : 5 <= a) by lia.
  destruct a as [|[|[|a3]]]; try lia.
  cbn [nextState].
  assert (Hvp5' : ValidP5Chain (p3z (S a3) :: p5 :: suf) = true).
  { cbn [ValidP5Chain]. lia. }
  split.
  - cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb isP3zP5 headP3zVal].
    change (1 mod 2 =? 0) with false.
    rewrite Hvp5'; cbn [andb orb negb].
    rw_if_neg ltac:(lia).
    rw_if_pos ltac:(lia). reflexivity.
  - intro fuel. specialize (Hch fuel).
    cbn [invChain drop1L nat_list_eqb isP3zP5 headP3zVal drop2L] in Hch |- *.
    change (1 mod 2 =? 0) with false; cbn [andb orb negb].
    rw_if_pos ltac:(lia).
    replace (S a3 - 2) with (S (S (S a3)) - 4) by lia.
    exact Hch.
Qed.

Lemma drop2L_cons (t1 t2 : LTok) (ls : list LTok) :
  drop2L (t1 :: ls) = drop2L (t2 :: ls).
Proof. destruct ls; reflexivity. Qed.

Lemma k0Of_eq_two_mul (k : nat) : k <= 1 -> k0Of k = 2 * k.
Proof. destruct k as [|[|?]]; cbn; lia. Qed.

Lemma step_Inv_ModeB_b2_m0 (ls : list LTok) (ds : list nat) :
  Inv (ModeB_b2 ls 0 ds) -> Inv (ModeE_c1 ls 1 ds).
Proof.
  intros [Hc Hch].
  assert (Hds2 : checkDs2 (ModeE_c1 ls 1 ds) = checkDs2 (ModeB_b2 ls 0 ds)).
  { cbn [checkDs2]. destruct (nat_list_eqb ds [2]); cbn [negb]; [| reflexivity].
    f_equal; lia. }
  assert (Hds1 : checkDs1Phi1 (ModeE_c1 ls 1 ds) = checkDs1Phi1 (ModeB_b2 ls 0 ds)).
  { cbn [checkDs1Phi1]. destruct (nat_list_eqb ds [1]); cbn [negb]; [| reflexivity].
    destruct (epW ls =? 2); cbn [negb]; [| reflexivity].
    f_equal; lia. }
  split.
  - assert (Hceq : invCore (ModeE_c1 ls 1 ds) = invCore (ModeB_b2 ls 0 ds)).
    { cbn [invCore]. rewrite Hds2, Hds1.
      change (2 <=? 0) with false.
      replace ((1 <=? 1) && isP3zP5 ls &&
        (((1 =? 0) && (headP3zVal ls =? 0)) || ((22 - 2 * 1 <=? headP3zVal ls) && (38 <=? z0 (p5Suf ls)))))
        with ((0 <=? 1) && isP3zP5 ls && ((20 - 2 * 0 <=? headP3zVal ls) && (38 <=? z0 (p5Suf ls)))) by lia.
      replace ((1 <=? 1) && (1 <=? epW ls) && (2 * 1 + prefSumW ls <=? 4))
        with ((0 <=? 1) && (1 <=? epW ls) && (2 * 0 + prefSumW ls <=? 2)) by lia.
      replace (2 <? 2 * 1 + epSum ls) with (0 <? 2 * 0 + epSum ls) by lia.
      replace (2 * 1 + epSum ls <=? 2) with (2 * 0 + epSum ls <=? 0) by lia.
      replace (2 * 1 + epSum ls + 2 * ep ls) with (2 * 0 + epSum ls + 2 * ep ls + 2) by lia.
      reflexivity. }
    congruence.
  - intro fuel. specialize (Hch fuel).
    cbn [invChain] in Hch |- *.
    change (2 <=? 0) with false in Hch.
    destruct (nat_list_eqb ds [] && (epW ls =? 0)); [| exact Hch].
    change (negb ((1 =? 0) && (headP3zVal ls =? 0))) with true.
    replace (headP3zVal ls - 6 - 2 * (1 - 1)) with (headP3zVal ls - 4 - 2 * (1 - 0)) by lia.
    exact Hch.
Qed.

Lemma step_Inv_ModeE_c1 (ls : list LTok) (k : nat) (ds : list nat) :
  Inv (ModeE_c1 ls k ds) -> Inv (nextState (ModeE_c1 ls k ds)).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeE_c1 ls k ds) = true) by (destruct (checkDs2 (ModeE_c1 ls k ds)); cbn in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeE_c1 ls k ds) = true) by (destruct (checkDs1Phi1 (ModeE_c1 ls k ds)); cbn in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  assert (Heven : ValidEvenLs ls = true) by (destruct (ValidEvenLs ls); cbn in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  apply unpack_if_negb_false in Hc as [Hok_phi Hc].
  apply unpack_if_false in Hc as [Hmd_bound Hodd_branch].
  assert (Hk : k <= 1).
  { clear - Hok_phi. destruct (nat_list_eqb ds [] && (epW ls =? 0)); lia. }
  destruct ls as [|[m | ] ls'].
  - exfalso. clear - Hok_phi. destruct (nat_list_eqb ds [] && (epW [] =? 0)); cbn [isP3zP5 epW] in Hok_phi; lia.
  - destruct m as [|[|m2]].
    + (* m = 0 *)
      cbn [nextState]. rewrite (k0Of_eq_two_mul k Hk).
      destruct (nat_list_eqb ds [] && (epW (p3z 0 :: ls') =? 0)) eqn:Hemp.
      * apply andb_true_iff in Hemp as [Hds_eqb Hepw_eqb].
        apply nat_list_eqb_true in Hds_eqb; subst ds.
        apply Nat.eqb_eq in Hepw_eqb.
        destruct ls' as [|[n|] suf];
          [cbn [epW Nat.modulo Nat.eqb Nat.add] in Hepw_eqb; discriminate
          |change (epW (p3z 0 :: p3z n :: suf)) with (S (epW (p3z n :: suf))) in Hepw_eqb; discriminate
          |].
        cbn [headP3zVal isP3zP5 p5Suf] in Hok_phi.
        assert (k = 0) by (clear - Hok_phi Hk; lia); subst k.
        split.
        -- assert (Heven' : ValidEvenLs (p5 :: suf) = true)
             by (rewrite <- (ValidEvenLs_p3z_even_cons 0 (p5 :: suf) eq_refl); exact Heven).
           cbn [invCore GoodDs checkDs2 checkDs1Phi1 isHeadP5 MustDrain hasOdd prefSumW nat_list_eqb
                Nat.modulo Nat.eqb Nat.leb Nat.ltb Nat.add Nat.mul Nat.sub andb orb negb].
           rewrite Heven'; reflexivity.
        -- intro fuel. specialize (Hch fuel).
           cbn [invChain isHeadP3z1 nat_list_eqb epW headP3zVal
                Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul andb orb negb] in Hch |- *.
           pose proof (checkChainAux_true_p3z0 fuel (p5 :: suf) 0 0 2 [] (or_intror (Nat.le_0_l 2))) as Hsh.
           cbn [Nat.add] in Hsh. congruence.
      * assert (Hepw_pos : 1 <= epW (p3z 0 :: ls')) by (clear - Hok_phi; lia).
        assert (Hpref_le : 2 * k + prefSumW (p3z 0 :: ls') <= 4) by (clear - Hok_phi; lia).
        assert (Hphiw : GoodPhiW (epW (p3z 0 :: ls') - 1) ds false = true) by (clear - Hok_phi; lia).
        assert (Hnp5 : isHeadP5 ls' = false).
        { destruct ls' as [|[|] ?]; [reflexivity | reflexivity | cbn [epW Nat.modulo Nat.divmod Nat.sub snd Nat.eqb] in Hepw_pos; clear - Hepw_pos; lia]. }
        pose proof (epW_p3z_even_cons 0 ls' eq_refl Hnp5) as Hepw_eq.
        pose proof (prefSumW_p3z_even_cons 0 ls' eq_refl Hnp5) as Hpref_eq.
        pose proof (epSum_p3z_even_cons 0 ls' eq_refl) as Hepsum_eq.
        pose proof (ep_p3z_even_cons 0 ls' eq_refl) as Hep_eq.
        pose proof (hasOdd_p3z_even_cons 0 ls' eq_refl) as Hodd_eq.
        pose proof (MustDrain_p3z_even_cons 0 ls' eq_refl) as Hmd_eq.
        assert (Heven' : ValidEvenLs ls' = true) by (rewrite <- (ValidEvenLs_p3z_even_cons 0 ls' eq_refl); exact Heven).
        assert (Hds2' : checkDs2 (ModeE_ge2 ls' (2 * k + 2) 0 ds) = true).
        { cbn [checkDs2] in Hds2 |- *. destruct (nat_list_eqb ds [2]); cbn [negb] in *; [| reflexivity].
          rewrite Hepsum_eq, Hmd_eq in Hds2; cbn [hasP5 p5Suf isHeadP5] in Hds2.
          rewrite Hnp5; clear - Hds2; lia. }
        assert (Hds1' : checkDs1Phi1 (ModeE_ge2 ls' (2 * k + 2) 0 ds) = true).
        { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
          rw_if_pos ltac:(clear - Hk; lia). rewrite Hnp5; cbn [Nat.add].
          destruct (epW ls' =? 1) eqn:Ee1; cbn [negb]; [| reflexivity].
          rw_if_neg_in Hds1 ltac:(clear - Hepw_eq Ee1; lia).
          rewrite Hmd_eq, Hepsum_eq in Hds1; cbn [hasP5 isHeadP5 andb orb negb] in Hds1 |- *.
          clear - Hds1; lia. }
        split.
        -- cbn [invCore].
           apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
           rw_if_pos ltac:(clear; lia).
           apply if_negb_false_true; [exact Heven' |].
           apply if_negb_false_true; [clear - Hk Hpref_le Hpref_eq; lia |].
           apply if_negb_false_true.
           { rewrite Hnp5; cbn [negb Nat.add].
             replace (epW ls') with (epW (p3z 0 :: ls') - 1) by (clear - Hepw_eq; lia).
             rewrite (GoodPhiW_mono _ _ _ Hphiw), orb_true_r; reflexivity. }
           apply if_false_true; [clear - Hmd_bound Hmd_eq Hepsum_eq; lia |].
           rw_if_neg ltac:(clear; lia).
           apply if_negb_false_true; [reflexivity |].
           rewrite Hodd_eq, Hepsum_eq in Hodd_branch.
           replace (2 * k + 2 + epSum ls' <=? 2 * 0 + 4) with (2 * k + (0 + epSum ls') <=? 2) by (clear; lia).
           destruct (hasOdd ls' && (2 * k + (0 + epSum ls') <=? 2)) eqn:Econd; [| reflexivity].
           rw_if_neg ltac:(clear; lia).
           replace (0 + ep ls') with (ep (p3z 0 :: ls') - 1) by (clear - Hep_eq; lia).
           replace (2 * k + 2 + epSum ls' + 2 * ep ls') with (2 * k + (0 + epSum ls') + 2 * ep (p3z 0 :: ls')) by (clear - Hep_eq; lia).
           rewrite <- Hmd_eq.
           change (hasP5 ls') with (hasP5 (p3z 0 :: ls')).
           clear - Hodd_branch; lia.
        -- intro fuel. specialize (Hch fuel).
           cbn [invChain] in Hch |- *.
           rewrite Hemp in Hch; cbn [andb] in Hch.
           rw_if_pos ltac:(clear; lia).
           rw_if_neg ltac:(clear; lia).
           rewrite (checkChainAux_true_p3z0 fuel ls' 0 (2 * k) 2 ds (or_introl Hnp5)) in Hch.
           exact Hch.
    + (* m = 1: impossible *)
      exfalso. clear - Hok_phi Hk.
      change (epW (p3z 1 :: ls')) with 0 in Hok_phi.
      change (headP3zVal (p3z 1 :: ls')) with 1 in Hok_phi.
      destruct (nat_list_eqb ds []); cbn [andb orb negb Nat.eqb Nat.leb] in Hok_phi; lia.
    + (* m = m2 + 2 *)
      cbn [nextState].
      replace (S (S m2)) with (m2 + 2) in * by (clear; lia).
      pose proof (epW_p3z_add2 m2 ls') as Hepw_eq.
      pose proof (ep_p3z_add2 m2 ls') as Hep_eq.
      pose proof (epSum_p3z_add2 m2 ls') as Hepsum_eq.
      pose proof (hasOdd_p3z_add2 m2 ls') as Hodd_eq.
      pose proof (MustDrain_p3z_add2 m2 ls') as Hmd_eq.
      pose proof (ValidEvenLs_p3z_add2 m2 ls') as Heven_eq.
      assert (Hds2' : checkDs2 (ModeB_b2 (p3z m2 :: ls') k ds) = true).
      { cbn [checkDs2] in Hds2 |- *. destruct (nat_list_eqb ds [2]); cbn [negb] in *; [| reflexivity].
        rewrite Hmd_eq, Hepsum_eq in Hds2; cbn [hasP5 p5Suf isHeadP5] in Hds2 |- *; clear - Hds2; lia. }
      assert (Hds1' : checkDs1Phi1 (ModeB_b2 (p3z m2 :: ls') k ds) = true).
      { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
        rewrite Hepw_eq, Hmd_eq, Hepsum_eq in Hds1.
        destruct (epW (p3z m2 :: ls') =? 2); cbn [negb] in *; [| reflexivity].
        cbn [hasP5 isHeadP5] in Hds1 |- *; clear - Hds1; lia. }
      split.
      * cbn [invCore].
        rewrite Heven_eq in Heven.
        apply if_false_true; [rewrite Hgd, Hds2', Hds1', Heven; reflexivity |].
        rw_if_neg ltac:(clear - Hk; lia).
        apply if_negb_false_true.
        { rewrite Hepw_eq in Hok_phi.
          destruct (nat_list_eqb ds [] && (epW (p3z m2 :: ls') =? 0)) eqn:Eemp.
          - assert (Hp3p5 : isP3zP5 (p3z (m2 + 2) :: ls') = isP3zP5 (p3z m2 :: ls'))
              by (destruct ls' as [|[|] ?]; reflexivity).
            rewrite Hp3p5 in Hok_phi; cbn [headP3zVal p5Suf] in Hok_phi |- *; clear - Hok_phi; lia.
          - assert (Hepw1 : 1 <= epW (p3z m2 :: ls')) by (clear - Hok_phi; lia).
            assert (Hm2_ev : m2 mod 2 = 0) by (cbn [epW] in Hepw1; destruct (m2 mod 2 =? 1) eqn:Emod; clear - Hepw1 Emod; lia).
            assert (Hnp5 : isHeadP5 ls' = false).
            { destruct ls' as [|[|] ?]; [reflexivity | reflexivity | cbn [epW] in Hepw1; rw_if_neg_in Hepw1 ltac:(clear - Hm2_ev; lia); clear - Hepw1; lia]. }
            rewrite (prefSumW_p3z_add2 m2 ls' Hm2_ev Hnp5) in Hok_phi; clear - Hok_phi; lia. }
        apply if_false_true; [clear - Hmd_bound Hmd_eq Hepsum_eq; lia |].
        rewrite Hodd_eq, Hepsum_eq, Hep_eq, Hmd_eq in Hodd_branch.
        replace (2 * k + epSum (p3z m2 :: ls') <=? 0)
          with (2 * k + (epSum (p3z m2 :: ls') + 2) <=? 2) by (clear; lia).
        replace (2 * k + epSum (p3z m2 :: ls') + 2 * ep (p3z m2 :: ls') + 2)
          with (2 * k + (epSum (p3z m2 :: ls') + 2) + 2 * ep (p3z m2 :: ls')) by (clear; lia).
        change (hasP5 (p3z (m2 + 2) :: ls')) with (hasP5 (p3z m2 :: ls')) in Hodd_branch.
        exact Hodd_branch.
      * intro fuel. specialize (Hch fuel).
        cbn [invChain] in Hch |- *.
        rw_if_neg ltac:(clear - Hk; lia).
        rewrite Hepw_eq, (checkChainAux_true_E_c1_to_B_b2 fuel m2 ls' k ds Hk) in Hch.
        destruct (nat_list_eqb ds [] && (epW (p3z m2 :: ls') =? 0)); [| exact Hch].
        cbn [headP3zVal] in Hch |- *.
        rw_if_pos_in Hch ltac:(clear; lia).
        rewrite (drop2L_cons (p3z (m2 + 2)) (p3z m2) ls') in Hch.
        replace (m2 + 2 - 6 - 2 * (1 - k)) with (m2 - 4 - 2 * (1 - k)) in Hch by (clear; lia).
        exact Hch.
  - (* p5: impossible *)
    exfalso. clear - Hok_phi. destruct (nat_list_eqb ds [] && (epW (p5 :: ls') =? 0)); cbn [isP3zP5 epW] in Hok_phi; lia.
Qed.

Lemma step_Inv_ModeB_ge3_c0 (ls : list LTok) (a : nat) (ds : list nat) :
  Inv (ModeB_ge3 ls a 0 ds) -> Inv (ModeE_c1 (p3z a :: ls) 0 ds).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeB_ge3 ls a 0 ds) = true) by (destruct (checkDs2 (ModeB_ge3 ls a 0 ds)); cbn in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeB_ge3 ls a 0 ds) = true) by (destruct (checkDs1Phi1 (ModeB_ge3 ls a 0 ds)); cbn in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  destruct (a mod 2 =? 0) eqn:Ea.
  - assert (Ha : a mod 2 = 0) by (clear - Ea; lia).
    apply unpack_if_negb_false in Hc as [Heven Hc].
    apply unpack_if_negb_false in Hc as [Hok_phi Hc].
    apply unpack_if_false in Hc as [Hmd_bound Hodd_branch].
    assert (Heven' : ValidEvenLs (p3z a :: ls) = true) by (rewrite (ValidEvenLs_p3z_even_cons a ls Ha); exact Heven).
    pose proof (MustDrain_p3z_even_cons a ls Ha) as Hmd_eq.
    pose proof (epSum_p3z_even_cons a ls Ha) as Hepsum_eq.
    pose proof (ep_p3z_even_cons a ls Ha) as Hep_eq.
    pose proof (hasOdd_p3z_even_cons a ls Ha) as Hodd_eq.
    assert (Hds2' : checkDs2 (ModeE_c1 (p3z a :: ls) 0 ds) = true).
    { cbn [checkDs2] in Hds2 |- *. destruct (nat_list_eqb ds [2]); cbn [negb] in *; [| reflexivity].
      rewrite Ea in Hds2; rewrite Hmd_eq, Hepsum_eq; cbn [hasP5 p5Suf isHeadP5] in *; clear - Hds2; lia. }
    assert (Hds1' : checkDs1Phi1 (ModeE_c1 (p3z a :: ls) 0 ds) = true).
    { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
      rewrite !Ea in Hds1; cbn [andb orb negb] in Hds1.
      destruct (epW (p3z a :: ls) =? 2) eqn:Ee2; cbn [negb]; [| reflexivity].
      assert (Hnp5 : isHeadP5 ls = false).
      { destruct ls as [|[|] ?]; [reflexivity | reflexivity | cbn [epW] in Ee2; rw_if_neg_in Ee2 ltac:(clear - Ha; lia); clear - Ee2; lia]. }
      pose proof (epW_p3z_even_cons a ls Ha Hnp5) as Hepw_c.
      rewrite Hnp5 in Hds1. cbn [Nat.add] in Hds1.
      rw_if_neg_in Hds1 ltac:(clear - Hepw_c Ee2; lia).
      rewrite Hepsum_eq; clear - Hds1; lia. }
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1', Heven'; reflexivity |].
      destruct (isHeadP5 ls) eqn:Hp5.
      * destruct ls as [|[|] suf]; try discriminate.
        cbn [isHeadP5 negb Nat.eqb] in Hok_phi.
        assert (Hds_nil : ds = []) by (apply nat_list_eqb_true; clear - Hok_phi; lia).
        subst ds.
        assert (Hepw0 : epW (p3z a :: p5 :: suf) = 0) by (cbn [epW]; rw_if_neg ltac:(clear - Ha; lia); reflexivity).
        apply if_negb_false_true.
        { rewrite Hepw0; cbn [nat_list_eqb Nat.eqb andb isP3zP5 headP3zVal p5Suf] in Hok_phi |- *; clear - Hok_phi; lia. }
        assert (Hmd0 : MustDrain (p3z a :: p5 :: suf) = false) by (rewrite (MustDrain_p3z_even_cons a _ Ha); reflexivity).
        assert (Hodd0 : hasOdd (p3z a :: p5 :: suf) = false) by (rewrite (hasOdd_p3z_even_cons a _ Ha); reflexivity).
        rewrite Hmd0, Hodd0; reflexivity.
      * cbn [negb] in Hok_phi.
        pose proof (epW_p3z_even_cons a ls Ha Hp5) as Hepw_eq.
        pose proof (prefSumW_p3z_even_cons a ls Ha Hp5) as Hpref_eq.
        apply if_negb_false_true.
        { rw_if_neg ltac:(clear - Hepw_eq; lia).
          replace (epW (p3z a :: ls) - 1) with (0 + epW ls) by (clear - Hepw_eq; lia).
          assert (Hphiw : GoodPhiW (0 + epW ls) ds false = true) by (clear - Hok_phi; lia).
          clear - Hok_phi Hpref_eq Hepw_eq Hphiw; lia. }
        apply if_false_true; [clear - Hmd_bound Hmd_eq Hepsum_eq; lia |].
        rewrite Hodd_eq, Hepsum_eq.
        replace (2 * 0 + (a + epSum ls) <=? 2) with (a + epSum ls <=? 2 * 0 + 2) by (clear; lia).
        destruct (hasOdd ls && (a + epSum ls <=? 2 * 0 + 2)) eqn:Econd; [| reflexivity].
        replace (ep (p3z a :: ls) - 1) with (0 + ep ls) by (clear - Hep_eq; lia).
        replace (2 * 0 + (a + epSum ls) + 2 * ep (p3z a :: ls))
          with (a + epSum ls + 2 * ep ls + 2) by (clear - Hep_eq; lia).
        rewrite Hmd_eq. change (hasP5 (p3z a :: ls)) with (hasP5 ls).
        clear - Hodd_branch; lia.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain] in Hch |- *.
      rewrite Ea in Hch; cbn [andb orb negb] in Hch.
      destruct (isHeadP5 ls) eqn:Hp5; cbn [andb orb negb] in Hch.
      * destruct ls as [|[|] suf]; try discriminate.
        cbn [isHeadP5 negb Nat.eqb] in Hok_phi.
        assert (Hds_nil : ds = []) by (apply nat_list_eqb_true; clear - Hok_phi; lia).
        subst ds.
        assert (Hepw0 : epW (p3z a :: p5 :: suf) = 0) by (cbn [epW]; rw_if_neg ltac:(clear - Ha; lia); reflexivity).
        rewrite Hepw0; cbn [nat_list_eqb Nat.eqb andb headP3zVal drop2L drop1L] in *.
        destruct (a =? 0) eqn:Ea0.
        -- assert (a = 0) by (clear - Ea0; lia); subst a; cbn in Hch |- *; exact Hch.
        -- assert (Ha22 : 22 <= a) by (cbn [p5Suf] in Hok_phi; clear - Hok_phi Ea0; lia).
           rw_if_pos_in Hch ltac:(clear - Ha22; lia).
           rw_if_pos ltac:(clear - Ha22; lia).
           replace (a - 6 - 2 * (1 - 0)) with (a - 8) by (clear; lia).
           exact Hch.
      * pose proof (epW_p3z_even_cons a ls Ha Hp5) as Hepw_eq.
        cbn [Nat.eqb andb] in Hch.
        rw_if_neg ltac:(clear - Hepw_eq; lia).
        exact Hch.
  - (* a odd *)
    assert (Hm1 : a mod 2 = 1) by (clear - Ea; lia).
    apply unpack_if_false in Hc as [Hc0 Hc].
    apply unpack_if_negb_false in Hc as [Heven _].
    cbn [Nat.eqb andb] in Hc0.
    assert (Hds_nil : ds = []) by (apply nat_list_eqb_true; clear - Hc0; lia).
    subst ds.
    assert (Ha23 : 23 <= a) by (clear - Hc0; lia).
    assert (Hp5 : isHeadP5 ls = true) by (clear - Hc0; lia).
    assert (Hz38 : 38 <= z0 (p5Suf ls)) by (clear - Hc0; lia).
    destruct ls as [|[|] suf]; try discriminate.
    assert (Hepw0 : epW (p3z a :: p5 :: suf) = 0) by (cbn [epW]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
    split.
    + cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb].
      apply if_false_true; [rewrite Heven; reflexivity |].
      rewrite Hepw0; cbn [Nat.eqb andb isP3zP5 headP3zVal p5Suf].
      cbn [p5Suf] in Hz38.
      apply if_negb_false_true; [clear - Ha23 Hz38; lia |].
      assert (Hmd0 : MustDrain (p3z a :: p5 :: suf) = false) by (cbn [MustDrain]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
      assert (Hepsum : epSum (p3z a :: p5 :: suf) = a - 1) by (cbn [epSum]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
      rewrite Hmd0, Hepsum; cbn [andb].
      rw_if_neg ltac:(clear - Ha23; lia); reflexivity.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain] in Hch |- *.
      rewrite Ea in Hch; cbn [andb orb negb] in Hch.
      rw_if_neg_in Hch ltac:(clear - Ha23; lia).
      cbn [Nat.eqb] in Hch.
      rewrite Hepw0; cbn [nat_list_eqb Nat.eqb andb headP3zVal drop2L drop1L].
      rw_if_pos ltac:(clear - Ha23; lia).
      replace (a - 6 - 2 * (1 - 0)) with (a - 8) by (clear; lia).
      exact Hch.
Qed.

Lemma isHeadP3z1_p3z (a : nat) (ls : list LTok) : isHeadP3z1 (p3z a :: ls) = (a =? 1).
Proof. destruct a as [|[|?]]; reflexivity. Qed.

Lemma step_Inv_ModeB_ge3_cpos (ls : list LTok) (a c' : nat) (ds : list nat) :
  Inv (ModeB_ge3 ls a (S c') ds) -> Inv (ModeE_ge2 (p3z a :: ls) 0 c' ds).
Proof.
  intros [Hc Hch].
  replace (S c') with (c' + 1) in * by (clear; lia).
  cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeB_ge3 ls a (c' + 1) ds) = true) by (destruct (checkDs2 (ModeB_ge3 ls a (c' + 1) ds)); cbn in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeB_ge3 ls a (c' + 1) ds) = true) by (destruct (checkDs1Phi1 (ModeB_ge3 ls a (c' + 1) ds)); cbn in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  destruct (a mod 2 =? 0) eqn:Ea.
  - (* a even *)
    assert (Ha : a mod 2 = 0) by (clear - Ea; lia).
    apply unpack_if_negb_false in Hc as [Heven Hc].
    apply unpack_if_negb_false in Hc as [Hok_phi Hc].
    apply unpack_if_false in Hc as [Hmd_bound Hodd_branch].
    assert (Heven' : ValidEvenLs (p3z a :: ls) = true) by (rewrite (ValidEvenLs_p3z_even_cons a ls Ha); exact Heven).
    pose proof (MustDrain_p3z_even_cons a ls Ha) as Hmd_eq.
    pose proof (epSum_p3z_even_cons a ls Ha) as Hepsum_eq.
    pose proof (ep_p3z_even_cons a ls Ha) as Hep_eq.
    pose proof (hasOdd_p3z_even_cons a ls Ha) as Hodd_eq.
    assert (Hds2' : checkDs2 (ModeE_ge2 (p3z a :: ls) 0 c' ds) = true).
    { cbn [checkDs2] in Hds2 |- *. destruct (nat_list_eqb ds [2]); cbn [negb] in *; [| reflexivity].
      rewrite Ea in Hds2; rewrite Hmd_eq, Hepsum_eq; cbn [hasP5 p5Suf isHeadP5] in *; clear - Hds2; lia. }
    assert (Hds1' : checkDs1Phi1 (ModeE_ge2 (p3z a :: ls) 0 c' ds) = true).
    { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
      rewrite !Ea in Hds1; cbn [andb orb negb] in Hds1.
      change (0 mod 2 =? 0) with true; cbn [andb orb negb].
      change (isHeadP5 (p3z a :: ls)) with false in *.
      destruct (isHeadP5 ls) eqn:Hp5; cbn [andb orb negb] in Hds1.
      - destruct ls as [|[|] suf]; try discriminate.
        assert (Hepw0 : epW (p3z a :: p5 :: suf) = 0) by (cbn [epW]; rw_if_neg ltac:(clear - Ha; lia); reflexivity).
        rewrite Hepw0, Nat.add_0_r.
        replace (c' + 1 - 1) with c' in Hds1 by (clear; lia).
        destruct (c' =? 1) eqn:Ec1; cbn [negb] in *; [| reflexivity].
        rewrite Hepsum_eq; clear - Hds1 Ec1; lia.
      - pose proof (epW_p3z_even_cons a ls Ha Hp5) as Hepw_c.
        replace (c' + epW (p3z a :: ls)) with (c' + 1 + epW ls) by (clear - Hepw_c; lia).
        destruct (c' + 1 + epW ls =? 1); cbn [negb] in *; [| reflexivity].
        rewrite Hepsum_eq; clear - Hds1; lia. }
    assert (Hnp3z1 : isHeadP3z1 (p3z a :: ls) = false) by (rewrite isHeadP3z1_p3z; clear - Ha; lia).
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      change (0 mod 2 =? 0) with true.
      apply if_negb_false_true; [exact Heven' |].
      destruct (isHeadP5 ls) eqn:Hp5.
      * destruct ls as [|[|] suf]; try discriminate.
        cbn [isHeadP5 negb] in Hok_phi. rw_if_neg_in Hok_phi ltac:(clear; lia).
        replace (c' + 1 - 1) with c' in Hok_phi by (clear; lia).
        assert (Hpref0 : prefSumW (p3z a :: p5 :: suf) = 0) by (cbn [prefSumW]; rw_if_neg ltac:(clear - Ha; lia); reflexivity).
        assert (Hepw0 : epW (p3z a :: p5 :: suf) = 0) by (cbn [epW]; rw_if_neg ltac:(clear - Ha; lia); reflexivity).
        apply if_negb_false_true; [clear - Hpref0; lia |].
        apply if_negb_false_true.
        { cbn [isHeadP5 negb]. rewrite Hepw0, Nat.add_0_r, (GoodPhiW_mono _ _ _ Hok_phi), orb_true_r; reflexivity. }
        assert (Hmd0 : MustDrain (p3z a :: p5 :: suf) = false) by (rewrite (MustDrain_p3z_even_cons a _ Ha); reflexivity).
        assert (Hodd0 : hasOdd (p3z a :: p5 :: suf) = false) by (rewrite (hasOdd_p3z_even_cons a _ Ha); reflexivity).
        rewrite Hmd0, Hnp3z1, Hodd0, andb_false_r; reflexivity.
      * cbn [negb] in Hok_phi.
        pose proof (epW_p3z_even_cons a ls Ha Hp5) as Hepw_eq.
        pose proof (prefSumW_p3z_even_cons a ls Ha Hp5) as Hpref_eq.
        pose proof (preP5Val_p3z_cons_of_not_headP5 a ls Hp5) as Hpre_eq.
        apply if_negb_false_true; [clear - Hok_phi Hpref_eq; lia |].
        apply if_negb_false_true.
        { cbn [isHeadP5 negb].
          assert (Hphi_or : ((nat_list_eqb ds [] && (c' + 1 + epW ls =? 1)) && MustDrain ls &&
                    ((c' + 1 + ep ls =? 1) && (a + epSum ls + 2 * ep ls + 2 =? 2)) &&
                    hasP5 ls && ((16 <=? preP5Val ls) && (38 <=? z0 (p5Suf ls)))) ||
                    GoodPhiW (c' + 1 + epW ls) ds false = true) by (clear - Hok_phi; lia).
          apply orb_true_iff in Hphi_or as [Hphi1 | Hphiw]; apply orb_true_iff.
          - left. rewrite Hmd_eq, Hpre_eq, Hepw_eq, Hep_eq, Hepsum_eq; cbn [hasP5 p5Suf]; clear - Hphi1; lia.
          - right. replace (c' + epW (p3z a :: ls)) with (c' + 1 + epW ls) by (clear - Hepw_eq; lia).
            exact (GoodPhiW_mono _ _ _ Hphiw). }
        apply if_false_true; [clear - Hmd_bound Hmd_eq Hepsum_eq; lia |].
        rewrite Hnp3z1, andb_false_r; cbn [negb].
        rewrite Hodd_eq, Hepsum_eq.
        replace (0 + (a + epSum ls) <=? 2 * c' + 4) with (a + epSum ls <=? 2 * (c' + 1) + 2) by (clear; lia).
        destruct (hasOdd ls && (a + epSum ls <=? 2 * (c' + 1) + 2)) eqn:Econd; [| reflexivity].
        replace (c' + ep (p3z a :: ls)) with (c' + 1 + ep ls) by (clear - Hep_eq; lia).
        replace (0 + (a + epSum ls) + 2 * ep (p3z a :: ls))
          with (a + epSum ls + 2 * ep ls + 2) by (clear - Hep_eq; lia).
        rewrite Hmd_eq, Hpre_eq; cbn [hasP5 p5Suf].
        exact Hodd_branch.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain] in Hch |- *.
      rewrite Ea in Hch; cbn [andb orb negb] in Hch. rw_if_neg_in Hch ltac:(clear; lia).
      change (0 mod 2 =? 0) with true.
      rewrite Hnp3z1, andb_false_r; cbn [andb orb negb].
      replace (2 * c' + 4) with (2 * (c' + 1) + 2) by (clear; lia).
      exact Hch.
  - (* a odd *)
    assert (Hm1 : a mod 2 = 1) by (clear - Ea; lia).
    apply unpack_if_false in Hc as [_ Hc].
    apply unpack_if_negb_false in Hc as [Heven Hc].
    apply unpack_if_negb_false in Hc as [Hok_c1 Hc].
    rw_if_pos_in Hok_c1 ltac:(clear; lia).
    apply unpack_if_false in Hc as [Hmd_bound Hodd_branch].
    assert (Hepw0 : epW (p3z a :: ls) = 0) by (cbn [epW]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
    assert (Hpref0 : prefSumW (p3z a :: ls) = 0) by (cbn [prefSumW]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
    assert (Hep0 : ep (p3z a :: ls) = 0) by (cbn [ep]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
    assert (Hepsum_odd : epSum (p3z a :: ls) = a - 1) by (cbn [epSum]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
    assert (Hodd_true : hasOdd (p3z a :: ls) = true) by (cbn [hasOdd]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
    assert (Hds2' : checkDs2 (ModeE_ge2 (p3z a :: ls) 0 c' ds) = true).
    { cbn [checkDs2] in Hds2 |- *. destruct (nat_list_eqb ds [2]); cbn [negb] in *; [| reflexivity].
      rewrite Ea in Hds2; clear - Hds2; lia. }
    assert (Hds1' : checkDs1Phi1 (ModeE_ge2 (p3z a :: ls) 0 c' ds) = true).
    { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
      rewrite !Ea in Hds1; cbn [andb orb negb] in Hds1.
      change (0 mod 2 =? 0) with true; cbn [andb orb negb].
      change (isHeadP5 (p3z a :: ls)) with false in *.
      rewrite Hepw0, Nat.add_0_r.
      replace (c' + 1 =? 2) with (c' =? 1) in Hds1 by (clear; lia).
      destruct (c' =? 1); cbn [negb] in *; [| reflexivity].
      rewrite Hepsum_odd; clear - Hds1 Hm1; lia. }
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      change (0 mod 2 =? 0) with true.
      apply if_negb_false_true; [exact Heven |].
      apply if_negb_false_true; [clear - Hpref0; lia |].
      destruct ((a =? 1) && (c' =? 0) && nat_list_eqb ds []) eqn:Erst.
      * assert (a = 1 /\ c' = 0 /\ ds = []).
        { repeat split; [clear - Erst; lia | clear - Erst; lia | apply nat_list_eqb_true; clear - Erst; lia]. }
        destruct H as [-> [-> ->]].
        cbn [isHeadP5 isHeadP3z1 GoodPhiW nat_list_eqb negb orb andb Nat.eqb Nat.add drop1L] in *.
        rewrite Hepsum_odd, Hodd_true, orb_true_r; cbn [Nat.add Nat.mul Nat.ltb Nat.leb Nat.sub andb orb negb].
        rewrite andb_false_r.
        destruct ls; [reflexivity | rewrite Hok_c1; reflexivity].
      * assert (Erst_b : ((a =? 1) && (c' + 1 =? 1) && nat_list_eqb ds []) = false) by (clear - Erst; lia).
        assert (Erst_e : ((0 =? 0) && (c' =? 0) && nat_list_eqb ds [] && isHeadP3z1 (p3z a :: ls)) = false)
          by (rewrite isHeadP3z1_p3z; clear - Erst; lia).
        assert (Estart_e : (isHeadP3z1 (p3z a :: ls) && ((0 =? 0) && (c' =? 0) && nat_list_eqb ds [])) = false)
          by (rewrite isHeadP3z1_p3z; clear - Erst; lia).
        rewrite Erst_b in Hok_c1; cbn [negb] in Hok_c1.
        apply if_negb_false_true.
        { cbn [isHeadP5 negb]. rewrite Hepw0, Hep0, Hepsum_odd, Estart_e, !Nat.add_0_r, !Nat.add_0_l.
          apply orb_true_iff in Hok_c1 as [Hphi1 | Hphiw]; apply orb_true_iff.
          - left. cbn [hasP5 p5Suf] in *; clear - Hphi1 Hm1; lia.
          - right. replace (c' + 1 - 1) with c' in Hphiw by (clear; lia); exact Hphiw. }
        apply if_false_true; [rewrite Hepsum_odd; clear - Hmd_bound Hm1; lia |].
        rewrite Erst_e; cbn [negb].
        rewrite Hodd_true, Hepsum_odd, Hep0, !Nat.add_0_r, !Nat.add_0_l; cbn [andb].
        replace (a - 1 <=? 2 * c' + 4) with (a <=? 2 * (c' + 1) + 3) by (clear - Hm1; lia).
        destruct (a <=? 2 * (c' + 1) + 3) eqn:Ele; [| reflexivity].
        rewrite Erst_b in Hodd_branch; cbn [andb orb negb] in Hodd_branch.
        replace (c' + 1 - 1) with c' in Hodd_branch by (clear; lia).
        cbn [hasP5 p5Suf] in *; clear - Hodd_branch Hm1; lia.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain] in Hch |- *.
      rewrite Ea in Hch; cbn [andb orb negb] in Hch. change (0 mod 2 =? 0) with true; cbn [andb orb negb].
      destruct ((a =? 1) && (c' =? 0) && nat_list_eqb ds []) eqn:Erst.
      * assert (a = 1 /\ c' = 0 /\ ds = []).
        { repeat split; [clear - Erst; lia | clear - Erst; lia | apply nat_list_eqb_true; clear - Erst; lia]. }
        destruct H as [-> [-> ->]].
        cbn [Nat.eqb nat_list_eqb andb isHeadP3z1 drop1L] in Hch |- *.
        destruct ls; exact Hch.
      * rw_if_neg_in Hch ltac:(clear - Erst; lia).
        rw_if_neg_in Hch ltac:(clear; lia).
        rw_if_neg ltac:(rewrite isHeadP3z1_p3z; clear - Erst; lia).
        replace (2 * c' + 4) with (2 * (c' + 1) + 2) by (clear; lia).
        exact Hch.
Qed.


(* ========================================================================== *)
(* Section 4 Part B1: ModeB_b2 + ModeE_ge2 Helpers                            *)
(* ========================================================================== *)

Lemma ValidEvenLs_p5Suf (ls : list LTok) :
  ValidEvenLs ls = true -> hasP5 ls = true ->
  18 <= z0 (p5Suf ls) /\ ValidP5Chain (p5Suf ls) = true.
Proof.
  induction ls as [|[m | ] rest IH]; intros Heven Hp5.
  - discriminate.
  - cbn [ValidEvenLs] in Heven. cbn [hasP5 p5Suf] in Hp5 |- *.
    destruct (m mod 2 =? 0) eqn:Hm.
    + exact (IH Heven Hp5).
    + destruct rest as [|[m2 | ] s2]; [discriminate | |].
      * destruct s2 as [|[|] s3]; cbn [ValidAfterOdd p5Suf] in Heven |- *; try discriminate.
        apply andb_true_iff in Heven as [H1 H2]; split; [clear - H1; lia | exact H2].
      * cbn [ValidAfterOdd p5Suf] in Heven |- *.
        apply andb_true_iff in Heven as [H1 H2]; split; [clear - H1; lia | exact H2].
  - cbn [ValidEvenLs p5Suf] in Heven |- *.
    apply andb_true_iff in Heven as [H1 H2]; split; [clear - H1; lia | exact H2].
Qed.

Lemma ValidP5Chain_p3z_p5 (m : nat) (suf : list LTok) :
  18 <= z0 suf -> ValidP5Chain suf = true ->
  ValidP5Chain (p3z m :: p5 :: suf) = true.
Proof.
  intros Hz Hv. destruct m as [|m']; cbn [ValidP5Chain]; (apply andb_true_iff; split; [lia | exact Hv]).
Qed.

Lemma ValidP5Chain_of_ValidEvenLs_z0Rep (ls : list LTok) :
  ValidEvenLs ls = true -> prefSumW ls = 0 ->
  MustDrain ls = false -> isHeadP5 ls = false ->
  ValidP5Chain ls = true /\ epW ls <= z0 ls.
Proof.
  intros Heven Hpref Hmd Hnp5.
  destruct (ls_eq_z0Rep_of_prefSumW_zero ls Heven Hpref Hmd Hnp5) as [Hls _].
  destruct (hasP5 ls) eqn:Hp5.
  - destruct (ValidEvenLs_p5Suf ls Heven Hp5) as [Hz18 Hv].
    split.
    + rewrite Hls, ValidP5Chain_z0Rep. exact (ValidP5Chain_p3z_p5 _ _ Hz18 Hv).
    + pose proof (f_equal z0 Hls) as Hz. rewrite z0_z0Rep in Hz. clear - Hz; lia.
  - split.
    + rewrite Hls, ValidP5Chain_z0Rep; reflexivity.
    + pose proof (f_equal z0 Hls) as Hz. rewrite z0_z0Rep in Hz. cbn [z0] in Hz. clear - Hz; lia.
Qed.

Lemma GoodDs_d1_valid {d : nat} : 3 <= d -> GoodDs [d] = true -> 8 <= d.
Proof.
  intros Hd H. unfold GoodDs, GoodDsAux, GoodDs1 in H.
  apply orb_true_iff in H as [H | H]; clear - Hd H; lia.
Qed.

Lemma GoodDs_pair_d2_cases {d d2 : nat} {ds2 : list nat} :
  GoodDs (d :: d2 :: ds2) = true ->
  (d2 = 0 /\ ds2 = [] /\ 8 <= d) \/
  (d2 = 1 /\ ds2 = [] /\ (d = 3 \/ 25 <= d)) \/
  (3 <= d2 /\ 17 <= d /\ GoodDs (d2 :: ds2) = true /\
    (d mod 2 = 0 /\ d <= 2 * d2 + 4 -> GoodDs ((d2 - 1) :: ds2) = true) /\
    (d mod 2 = 0 /\ d + 14 <= 2 * d2 -> GoodDs ((d2 - 2) :: ds2) = true)).
Proof.
  intro H. destruct ds2 as [|d3 ds3].
  - unfold GoodDs, GoodDsAux, GoodDs2 in H.
    destruct (d2 =? 0) eqn:E0; [left; split; [lia | split; [reflexivity | clear - H; lia]] |].
    destruct (d2 =? 1) eqn:E1;
      [right; left; split; [lia | split; [reflexivity | apply orb_true_iff in H as [H|H]; lia]] |].
    destruct (d2 <? 3) eqn:E3; [discriminate |].
    apply unpack_if_false in H as [_ H].
    apply unpack_if_false in H as [Hd17_gd H].
    apply orb_false_iff in Hd17_gd as [Hd17 Hgd].
    apply unpack_if_false in H as [Hsub1 H].
    apply unpack_if_false in H as [Hsub2 _].
    apply Bool.negb_false_iff in Hgd.
    right; right.
    split; [clear - E3; lia |].
    split; [clear - Hd17; lia |].
    split; [exact Hgd |].
    split.
    + intros [Hm Hle]. apply andb_false_iff in Hsub1 as [Hsub1 | Hsub1]; [clear - Hm Hle Hsub1; lia | apply Bool.negb_false_iff in Hsub1; exact Hsub1].
    + intros [Hm Hle]. apply andb_false_iff in Hsub2 as [Hsub2 | Hsub2]; [clear - Hm Hle Hsub2; lia | apply Bool.negb_false_iff in Hsub2; exact Hsub2].
  - cbn [GoodDs GoodDsAux] in H |- *.
    destruct (d2 <? 3) eqn:E3; cbn [andb orb negb] in H; [discriminate |].
    apply unpack_if_false in H as [_ H].
    apply unpack_if_false in H as [_ H].
    apply unpack_if_false in H as [_ H].
    apply unpack_if_false in H as [Hd17_gd H].
    apply orb_false_iff in Hd17_gd as [Hd17 Hgd].
    apply Bool.negb_false_iff in Hgd.
    apply unpack_if_false in H as [Hsub1 H].
    apply unpack_if_false in H as [Hsub2 _].
    right; right.
    split; [clear - E3; lia |].
    split; [clear - Hd17; lia |].
    split; [exact Hgd |].
    split.
    + intros [Hm Hle]. apply andb_false_iff in Hsub1 as [Hsub1 | Hsub1]; [clear - Hm Hle Hsub1; lia | apply Bool.negb_false_iff in Hsub1; exact Hsub1].
    + intros [Hm Hle]. apply andb_false_iff in Hsub2 as [Hsub2 | Hsub2]; [clear - Hm Hle Hsub2; lia | apply Bool.negb_false_iff in Hsub2; exact Hsub2].
Qed.

Lemma GoodDs_d31 {d : nat} : GoodDs [d; 3; 1] = true -> 19 <= d.
Proof.
  intro H. cbn [GoodDs GoodDsAux nat_list_eqb Nat.eqb andb] in H.
  destruct (d <? 19) eqn:E; [discriminate | clear - E; lia].
Qed.

Lemma GoodDs_d_ge25_1 {d d2 : nat} : 25 <= d2 -> GoodDs [d; d2; 1] = true -> 39 <= d.
Proof.
  intros Hd2 H. cbn [GoodDs GoodDsAux] in H.
  rw_if_neg_in H ltac:(clear - Hd2; lia).
  apply unpack_if_false in H as [_ H].
  apply unpack_if_false in H as [_ H].
  apply unpack_if_false in H as [H39 _].
  cbn [nat_list_eqb Nat.eqb] in H39.
  clear - Hd2 H39; lia.
Qed.

Lemma GoodDs_isOddDrainDs_ge19 {d2 : nat} {ds2 : list nat} :
  3 <= d2 -> isOddDrainDs ds2 = true -> GoodDs (d2 :: ds2) = true -> 19 <= d2.
Proof.
  intros Hd2 Hod H.
  destruct ds2 as [|d3 [|d4 ds4]].
  - discriminate.
  - cbn [isOddDrainDs] in Hod.
    assert (Hd3 : 3 <= d3) by (unfold isOddDrain1 in Hod; clear - Hod; lia).
    unfold GoodDs, GoodDsAux, GoodDs2 in H.
    rw_if_neg_in H ltac:(clear - Hd3; lia).
    rw_if_neg_in H ltac:(clear - Hd3; lia).
    rw_if_neg_in H ltac:(clear - Hd3; lia).
    rewrite Hod, Bool.andb_true_l in H.
    destruct (d2 <? 19) eqn:E; [discriminate | clear - E; lia].
  - assert (Hd3 : 3 <= d3).
    { destruct ds4 as [|? ?]; destruct d4 as [|?]; try discriminate.
      cbn [isOddDrainDs] in Hod; unfold isOddDrain1 in Hod; clear - Hod; lia. }
    cbn [GoodDs GoodDsAux] in H.
    rw_if_neg_in H ltac:(clear - Hd3; lia).
    apply unpack_if_false in H as [_ H].
    apply unpack_if_false in H as [H19 _].
    rewrite Hod, Bool.andb_true_l in H19.
    clear - H19; lia.
Qed.

Lemma GoodPhiW_of_GoodDs_sub2 {d2 : nat} {ds2 : list nat} :
  3 <= d2 -> GoodDs (d2 :: ds2) = true -> GoodPhiW (d2 - 2) ds2 false = true.
Proof.
  intros Hd2 H. destruct ds2 as [|d3 ds3].
  - pose proof (GoodDs_d1_valid Hd2 H) as Hd8.
    unfold GoodPhiW; cbn [nat_list_eqb orb]. clear - Hd8; lia.
  - destruct (GoodDs_pair_d2_cases H) as [[-> [-> Hd8]] | [[-> [-> Hd_or]] | [Hd3_3 [Hd2_17 _]]]].
    + unfold GoodPhiW; cbn [nat_list_eqb Nat.eqb andb]. clear - Hd8; lia.
    + unfold GoodPhiW; cbn [nat_list_eqb Nat.eqb andb]. clear - Hd_or; lia.
    + unfold GoodPhiW.
      replace (nat_list_eqb (d3 :: ds3) [2]) with false
        by (destruct (nat_list_eqb (d3 :: ds3) [2]) eqn:E; [apply nat_list_eqb_true in E; injection E as -> ->; clear - Hd3_3; lia | reflexivity]).
      replace (nat_list_eqb (d3 :: ds3) [0]) with false
        by (destruct (nat_list_eqb (d3 :: ds3) [0]) eqn:E; [apply nat_list_eqb_true in E; injection E as -> ->; clear - Hd3_3; lia | reflexivity]).
      replace (nat_list_eqb (d3 :: ds3) [1]) with false
        by (destruct (nat_list_eqb (d3 :: ds3) [1]) eqn:E; [apply nat_list_eqb_true in E; injection E as -> ->; clear - Hd3_3; lia | reflexivity]).
      cbn [nat_list_eqb].
      destruct (isDGe25One (d3 :: ds3)) eqn:E25.
      * unfold isDGe25One in E25.
        destruct ds3 as [|d4 ds4]; [discriminate |].
        destruct d4 as [|[|?]]; try discriminate.
        destruct ds4 as [|? ?]; try discriminate.
        pose proof (GoodDs_d_ge25_1 (d := d2) (d2 := d3) ltac:(clear - E25; lia) H) as Hd39.
        clear - Hd39; lia.
      * destruct (isOddDrainDs (d3 :: ds3)) eqn:Eod.
        -- pose proof (GoodDs_isOddDrainDs_ge19 Hd2 Eod H) as Hd19.
           clear - Hd19; lia.
        -- clear - Hd2_17; lia.
Qed.

Lemma checkChainAux_B_ge3_c0_ok_ge22 (fuel a : nat) (suf : list LTok) :
  22 <= a -> checkChainAux fuel true (p3z a :: p5 :: suf) 0 0 2 [] = true.
Proof.
  intro Ha. destruct fuel as [|fuel]; [reflexivity |].
  Local Transparent checkChainAux.
  cbn [checkChainAux].
  Local Opaque checkChainAux.
  assert (Hdec : (0 + epSum (p3z a :: p5 :: suf) <=? 2) = false).
  { cbn [epSum]. destruct (a mod 2 =? 1); clear - Ha; lia. }
  assert (Hepw0 : epW (p3z a :: p5 :: suf) = 0).
  { cbn [epW]. destruct (a mod 2 =? 1); reflexivity. }
  rewrite Hdec, Hepw0; cbn [isHeadP5 orb]; rewrite !andb_false_r.
  cbn [isDrainRstDs isRank0 nat_list_eqb Nat.add andb orb negb].
  reflexivity.
Qed.

#[local] Opaque checkChainAux.

Lemma GoodDs_tail_any {d : nat} {ds : list nat} :
  GoodDs (d :: ds) = true -> GoodDs ds = true /\ ds <> [2].
Proof.
  intro H. destruct ds as [|d2 ds2].
  - split; [reflexivity | discriminate].
  - destruct (GoodDs_pair_d2_cases H) as [[-> [-> _]] | [[-> [-> _]] | [Hd2_3 [_ [Hgd2 _]]]]].
    + split; [reflexivity | discriminate].
    + split; [reflexivity | discriminate].
    + split; [exact Hgd2 | intro Heq; injection Heq as -> _; clear - Hd2_3; lia].
Qed.

Lemma step_Inv_ModeB_b2_mge2 (ls : list LTok) (m'' : nat) (ds : list nat) :
  Inv (ModeB_b2 ls (m'' + 2) ds) -> Inv (nextState (ModeB_b2 ls (m'' + 2) ds)).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Heven : ValidEvenLs ls = true)
    by (destruct (ValidEvenLs ls); cbn in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  rw_if_pos_in Hc ltac:(clear; lia).
  assert (Hds_nil : ds = []) by (apply nat_list_eqb_true; clear - Hc; lia).
  assert (Hm4 : 4 <= m'' + 2) by (clear - Hc; lia).
  assert (Hp5 : isHeadP5 ls = true) by (clear - Hc; lia).
  subst ds.
  destruct ls as [|[|] suf]; try discriminate.
  cbn [ValidEvenLs] in Heven.
  apply andb_true_iff in Heven as [Hz18_b Hvp5].
  assert (Hz18 : 18 <= z0 suf) by (clear - Hz18_b; lia).
  replace (m'' + 2) with (S (m'' + 1)) in * by (clear; lia).
  cbn [nextState].
  pose proof (ValidP5Chain_p3z_p5 (m'' + 1) suf Hz18 Hvp5) as Hvp5'.
  split.
  - cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul andb orb negb].
    rewrite Hvp5'; change ((1 <=? 1) && (1 <=? 5)) with true; cbn [negb].
    cbn [isP3zP5 headP3zVal andb].
    rw_if_pos ltac:(clear - Hm4; lia); reflexivity.
  - intro fuel. specialize (Hch fuel).
    cbn [invChain headP3zVal drop2L drop1L isP3zP5 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb] in Hch |- *.
    rw_if_pos_in Hch ltac:(clear - Hm4; lia).
    rw_if_pos ltac:(clear - Hm4; lia).
    replace (m'' + 1 - 2) with (S (m'' + 1) - 3) by (clear; lia).
    exact Hch.
Qed.

Lemma step_Inv_ModeB_b2_m1 (ls : list LTok) (ds : list nat) :
  Inv (ModeB_b2 ls 1 ds) -> Inv (nextState (ModeB_b2 ls 1 ds)).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeB_b2 ls 1 ds) = true) by (destruct (checkDs2 (ModeB_b2 ls 1 ds)); cbn in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeB_b2 ls 1 ds) = true) by (destruct (checkDs1Phi1 (ModeB_b2 ls 1 ds)); cbn in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  assert (Heven : ValidEvenLs ls = true) by (destruct (ValidEvenLs ls); cbn in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  change (2 <=? 1) with false in Hc; cbn [andb orb negb] in Hc.
  apply unpack_if_negb_false in Hc as [Hok_phi Hc].
  apply unpack_if_false in Hc as [Hmd_bound _].
  destruct (nat_list_eqb ds [] && (epW ls =? 0)) eqn:Hemp; cbn [andb orb negb] in Hok_phi.
  - apply andb_true_iff in Hemp as [Hds_eqb Hepw_eqb].
    apply nat_list_eqb_true in Hds_eqb; subst ds.
    apply Nat.eqb_eq in Hepw_eqb.
    assert (Hp3p5 : isP3zP5 ls = true) by (clear - Hok_phi; lia).
    destruct ls as [|[m0 | ] [|[|] suf]]; try discriminate.
    cbn [isP3zP5 headP3zVal p5Suf Nat.add Nat.sub Nat.mul andb] in Hok_phi.
    assert (Hm0_18 : 18 <= m0) by (clear - Hok_phi; lia).
    assert (Hz38 : 38 <= z0 suf) by (clear - Hok_phi; lia).
    destruct (ValidEvenLs_p5Suf (p3z m0 :: p5 :: suf) Heven eq_refl) as [Hz18 Hvp5].
    cbn [p5Suf] in Hz18, Hvp5.
    cbn [nextState].
    assert (Hvp5' : ValidP5Chain (p3z 0 :: p3z m0 :: p5 :: suf) = true)
      by (cbn [ValidP5Chain]; exact (ValidP5Chain_p3z_p5 m0 suf Hz18 Hvp5)).
    destruct m0 as [|m0']; [clear - Hm0_18; lia |].
    split.
    + cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb isP3zP5 headP3zVal z0 dropZ0 p5Suf Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul andb orb negb].
      rewrite Hvp5'; change ((1 <=? 1) && (1 <=? 5)) with true; cbn [negb andb orb].
      rw_if_pos ltac:(clear - Hm0_18 Hz38; lia); reflexivity.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain nat_list_eqb isP3zP5 headP3zVal z0 dropZ0 p5Suf drop2L Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul andb orb negb] in Hch |- *.
      change (2 <=? 1) with false in Hch.
      rewrite Hepw_eqb in Hch; cbn [Nat.eqb andb] in Hch.
      rw_if_pos ltac:(clear - Hm0_18 Hz38; lia).
      rewrite Nat.sub_0_r in Hch; clear - Hch; lia.
  - assert (Hepw_pos : 1 <= epW ls) by (clear - Hok_phi; lia).
    assert (Hpref0 : prefSumW ls = 0) by (clear - Hok_phi; lia).
    assert (Hphiw : GoodPhiW (epW ls - 1) ds false = true) by (clear - Hok_phi; lia).
    assert (Hmd0 : MustDrain ls = false) by (clear - Hmd_bound; lia).
    assert (Hnp5 : isHeadP5 ls = false)
      by (destruct ls as [|[|] ?]; [reflexivity | reflexivity | cbn [epW] in Hepw_pos; clear - Hepw_pos; lia]).
    destruct (ValidP5Chain_of_ValidEvenLs_z0Rep ls Heven Hpref0 Hmd0 Hnp5) as [Hvp5 Hz0_ge].
    destruct (ls_eq_z0Rep_of_prefSumW_zero ls Heven Hpref0 Hmd0 Hnp5) as [Hls_z0 Hodd_imp_p5].
    assert (Hep_ge_epw : epW ls <= ep ls).
    { pose proof (f_equal ep Hls_z0) as Heq.
      destruct (hasP5 ls); rewrite ep_z0Rep in Heq; clear - Heq; lia. }
    set (tail_b2 := if hasP5 ls then p3z (2 + epSum ls + (if hasOdd ls then 1 else 0) - (0 + 2)) :: p5 :: p5Suf ls else []).
    assert (Hz_ls0 : z0Rep (0 + epW ls) tail_b2 = ls).
    { unfold tail_b2.
      replace (2 + epSum ls + (if hasOdd ls then 1 else 0) - (0 + 2))
        with (epSum ls + (if hasOdd ls then 1 else 0)) by (clear; lia).
      rewrite Nat.add_0_l. symmetry. rewrite Hls_z0 at 1.
      destruct (hasP5 ls); reflexivity. }
    assert (Hz_ls1 : z0Rep (0 + epW ls + 1) tail_b2 = p3z 0 :: ls)
      by (replace (0 + epW ls + 1) with (S (0 + epW ls)) by (clear; lia); cbn [z0Rep]; rewrite Hz_ls0; reflexivity).
    assert (Hz_ls2 : z0Rep (0 + epW ls + 2) tail_b2 = p3z 0 :: p3z 0 :: ls)
      by (replace (0 + epW ls + 2) with (S (0 + epW ls + 1)) by (clear; lia); cbn [z0Rep]; rewrite Hz_ls1; reflexivity).
    assert (Hz_ls3 : z0Rep (0 + epW ls + 3) tail_b2 = p3z 0 :: p3z 0 :: p3z 0 :: ls)
      by (replace (0 + epW ls + 3) with (S (0 + epW ls + 2)) by (clear; lia); cbn [z0Rep]; rewrite Hz_ls2; reflexivity).
    assert (Hch_step : forall fuel,
      checkChainAux (S fuel) true ls 0 2 0 ds = true).
    { intro fuel. specialize (Hch (S fuel)).
      cbn [invChain] in Hch. change (2 <=? 1) with false in Hch.
      rewrite Hemp in Hch; exact Hch. }
    assert (Hdec_0_2 : (2 + epSum ls <=? 0) = false) by (clear; lia).
    destruct ds as [|d ds'].
    + (* ds = [] *)
      cbn [nextState].
      cbn [GoodPhiW nat_list_eqb orb] in Hphiw.
      assert (Hepw7 : 7 <= epW ls) by (clear - Hphiw; lia).
      assert (Hvp5' : ValidP5Chain (p3z 0 :: ls) = true) by exact Hvp5.
      assert (Hz0' : z0 (p3z 0 :: ls) = 1 + z0 ls) by reflexivity.
      split.
      * cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb headP3zVal isDGe25One isOddDrainDs Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
        rewrite Hvp5', Hz0'; change ((1 <=? 1) && (1 <=? 2 * 1 + 3)) with true; change (3 <=? 0) with false; cbn [negb andb orb].
        rw_if_neg ltac:(clear; lia).
        rw_if_neg ltac:(clear - Hepw7 Hz0_ge; lia).
        clear - Hepw7 Hz0_ge; lia.
      * intro fuel. pose proof (Hch_step fuel) as Hf.
        Local Transparent checkChainAux.
        cbn [checkChainAux] in Hf.
        Local Opaque checkChainAux.
        rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf; cbn [isDrainRstDs isRank0 andb orb negb nat_list_eqb] in Hf.
        rw_if_neg_in Hf ltac:(clear - Hepw7; lia).
        fold tail_b2 in Hf. rewrite Hz_ls1 in Hf.
        cbn [invChain nat_list_eqb headP3zVal Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
        rw_if_neg ltac:(clear; lia).
        rewrite Hz0'. rw_if_neg ltac:(clear - Hepw7 Hz0_ge; lia).
        exact Hf.
    + destruct d as [|[|[|m'']]].
      * (* d = 0 *)
        destruct ds' as [|d2 ds'']; [| exfalso; pose proof (GoodDs_pair_ge3 _ _ _ Hgd); clear - H; lia].
        cbn [nextState].
        unfold GoodPhiW in Hphiw; cbn [nat_list_eqb Nat.eqb andb] in Hphiw.
        assert (Hepw7 : 7 <= epW ls) by (clear - Hphiw; lia).
        assert (Heven2 : ValidEvenLs (p3z 0 :: p3z 0 :: ls) = true) by exact Heven.
        assert (Hepw2 : epW (p3z 0 :: p3z 0 :: ls) = 2 + epW ls)
          by (rewrite (epW_p3z_even_cons 0 (p3z 0 :: ls) eq_refl eq_refl), (epW_p3z_even_cons 0 ls eq_refl Hnp5); clear; lia).
        assert (Hpref2 : prefSumW (p3z 0 :: p3z 0 :: ls) = 0)
          by (rewrite (prefSumW_p3z_even_cons 0 (p3z 0 :: ls) eq_refl eq_refl), (prefSumW_p3z_even_cons 0 ls eq_refl Hnp5); exact Hpref0).
        assert (Hep2 : ep (p3z 0 :: p3z 0 :: ls) = 2 + ep ls)
          by (rewrite (ep_p3z_even_cons 0 (p3z 0 :: ls) eq_refl), (ep_p3z_even_cons 0 ls eq_refl); clear; lia).
        split.
        -- cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb isHeadP5 isHeadP3z1 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
           rewrite Heven2, Hpref2, Hepw2, Hep2; cbn [negb andb orb].
           assert (Hphiw2 : GoodPhiW (1 + (2 + epW ls)) [] false = true)
             by (unfold GoodPhiW; cbn [nat_list_eqb orb]; clear - Hepw7; lia).
           rewrite Hphiw2, orb_true_r; cbn [negb].
           change (2 + 0 <=? 2 * 1 + 4) with true; cbn [andb negb].
           change (MustDrain (p3z 0 :: p3z 0 :: ls)) with (MustDrain ls).
           rewrite Hmd0; cbn [andb negb].
           change (hasOdd (p3z 0 :: p3z 0 :: ls)) with (hasOdd ls).
           change (hasP5 (p3z 0 :: p3z 0 :: ls)) with (hasP5 ls).
           destruct (hasOdd ls && (2 + epSum (p3z 0 :: p3z 0 :: ls) <=? 2 * 1 + 4)) eqn:Eoc; [| reflexivity].
           assert (Hp5_t : hasP5 ls = true).
           { destruct (hasP5 ls) eqn:Ep; [reflexivity |].
             rewrite (Hodd_imp_p5 eq_refl) in Eoc; discriminate. }
           assert (Hgp : GoodPsi (1 + (2 + ep ls)) [] = true)
             by (unfold GoodPsi, GoodDs, GoodDsAux, GoodDs1; clear - Hepw7 Hep_ge_epw; lia).
           rewrite Hgp, Hp5_t; cbn [negb orb andb]; try rewrite !orb_false_r; try rewrite !andb_false_r; cbn [negb orb andb]; try rewrite !orb_true_l; reflexivity.
        -- intro fuel. pose proof (Hch_step fuel) as Hf.
           Local Transparent checkChainAux.
           cbn [checkChainAux] in Hf.
           Local Opaque checkChainAux.
           rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf; cbn [isDrainRstDs isRank0 andb orb negb nat_list_eqb Nat.eqb] in Hf.
           try (change (8 <=? 0) with false in Hf; change (0 <=? 2) with true in Hf);
           try (change (8 <=? 1) with false in Hf; change (1 <=? 2) with true in Hf);
           try (change (8 <=? 2) with false in Hf; change (2 <=? 2) with true in Hf);
           cbn [andb orb negb] in Hf.
           rw_if_neg_in Hf ltac:(clear - Hepw7; lia).
           fold tail_b2 in Hf. rewrite Hz_ls2 in Hf.
           cbn [invChain nat_list_eqb isHeadP3z1 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
           exact Hf.
      * (* d = 1 *)
        destruct ds' as [|d2 ds'']; [| exfalso; pose proof (GoodDs_pair_ge3 _ _ _ Hgd); clear - H; lia].
        cbn [nextState].
        unfold GoodPhiW in Hphiw; cbn [nat_list_eqb Nat.eqb andb] in Hphiw.
        assert (Hepw2_ge : 2 <= epW ls) by (clear - Hphiw; lia).
        assert (Heven3 : ValidEvenLs (p3z 0 :: p3z 0 :: p3z 0 :: ls) = true) by exact Heven.
        assert (Hepw3 : epW (p3z 0 :: p3z 0 :: p3z 0 :: ls) = 3 + epW ls)
          by (rewrite (epW_p3z_even_cons 0 (p3z 0 :: p3z 0 :: ls) eq_refl eq_refl), (epW_p3z_even_cons 0 (p3z 0 :: ls) eq_refl eq_refl), (epW_p3z_even_cons 0 ls eq_refl Hnp5); clear; lia).
        assert (Hpref3 : prefSumW (p3z 0 :: p3z 0 :: p3z 0 :: ls) = 0)
          by (rewrite (prefSumW_p3z_even_cons 0 (p3z 0 :: p3z 0 :: ls) eq_refl eq_refl), (prefSumW_p3z_even_cons 0 (p3z 0 :: ls) eq_refl eq_refl), (prefSumW_p3z_even_cons 0 ls eq_refl Hnp5); exact Hpref0).
        assert (Hep3 : ep (p3z 0 :: p3z 0 :: p3z 0 :: ls) = 3 + ep ls)
          by (rewrite (ep_p3z_even_cons 0 (p3z 0 :: p3z 0 :: ls) eq_refl), (ep_p3z_even_cons 0 (p3z 0 :: ls) eq_refl), (ep_p3z_even_cons 0 ls eq_refl); clear; lia).
        assert (Hepsum3 : epSum (p3z 0 :: p3z 0 :: p3z 0 :: ls) = epSum ls)
          by (rewrite (epSum_p3z_even_cons 0 (p3z 0 :: p3z 0 :: ls) eq_refl), (epSum_p3z_even_cons 0 (p3z 0 :: ls) eq_refl), (epSum_p3z_even_cons 0 ls eq_refl); clear; lia).
        split.
        -- cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb isHeadP5 isHeadP3z1 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
           rewrite Heven3, Hpref3, Hepw3, Hep3, Hepsum3; cbn [negb andb orb].
           assert (Hphiw3 : GoodPhiW (1 + (3 + epW ls)) [] false = true)
             by (unfold GoodPhiW; cbn [nat_list_eqb orb]; clear - Hepw2_ge; lia).
           rewrite Hphiw3, orb_true_r; cbn [negb].
           change (0 + 0 <=? 2 * 1 + 4) with true; cbn [andb negb].
           change (MustDrain (p3z 0 :: p3z 0 :: p3z 0 :: ls)) with (MustDrain ls).
           rewrite Hmd0; cbn [andb negb].
           change (hasOdd (p3z 0 :: p3z 0 :: p3z 0 :: ls)) with (hasOdd ls).
           change (hasP5 (p3z 0 :: p3z 0 :: p3z 0 :: ls)) with (hasP5 ls).
           destruct (hasOdd ls && (0 + epSum ls <=? 2 * 1 + 4)) eqn:Eoc; [| reflexivity].
           assert (Hepw_ge3 : 3 <= epW ls).
           { destruct (epW ls =? 2) eqn:Ee2; [| clear - Hepw2_ge Ee2; lia].
             cbn [checkDs1Phi1 nat_list_eqb Nat.eqb negb] in Hds1.
             rewrite Ee2 in Hds1; cbn [negb] in Hds1.
             apply andb_true_iff in Hds1 as [_ Hds1_r].
             apply andb_true_iff in Eoc as [_ Eoc_r].
             clear - Hds1_r Eoc_r; lia. }
           assert (Hp5_t : hasP5 ls = true).
           { destruct (hasP5 ls) eqn:Ep; [reflexivity |].
             rewrite (Hodd_imp_p5 eq_refl) in Eoc; discriminate. }
           assert (Hgp : GoodPsi (1 + (3 + ep ls)) [] = true)
             by (unfold GoodPsi, GoodDs, GoodDsAux, GoodDs1; clear - Hepw_ge3 Hep_ge_epw; lia).
           rewrite Hgp, Hp5_t; cbn [negb orb andb]; try rewrite !orb_false_r; try rewrite !andb_false_r; cbn [negb orb andb]; try rewrite !orb_true_l; reflexivity.
        -- intro fuel. pose proof (Hch_step fuel) as Hf.
           Local Transparent checkChainAux.
           cbn [checkChainAux] in Hf.
           Local Opaque checkChainAux.
           rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf; cbn [isDrainRstDs isRank0 andb orb negb nat_list_eqb Nat.eqb] in Hf.
           try (change (8 <=? 0) with false in Hf; change (0 <=? 2) with true in Hf);
           try (change (8 <=? 1) with false in Hf; change (1 <=? 2) with true in Hf);
           try (change (8 <=? 2) with false in Hf; change (2 <=? 2) with true in Hf);
           cbn [andb orb negb] in Hf.
           rw_if_neg_in Hf ltac:(clear - Hepw2_ge; lia).
           fold tail_b2 in Hf. rewrite Hz_ls3 in Hf.
           cbn [invChain nat_list_eqb isHeadP3z1 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
           exact Hf.
      * (* d = 2 *)
        destruct ds' as [|d2 ds'']; [| exfalso; pose proof (GoodDs_pair_ge3 _ _ _ Hgd); clear - H; lia].
        cbn [nextState].
        unfold GoodPhiW in Hphiw; cbn [nat_list_eqb Nat.eqb andb] in Hphiw.
        assert (Hepw5 : epW ls = 5) by (clear - Hphiw; lia).
        assert (Hvp5' : ValidP5Chain (p3z 0 :: p3z 0 :: ls) = true) by exact Hvp5.
        assert (Hz0_2 : z0 (p3z 0 :: p3z 0 :: ls) = 2 + z0 ls)
          by (change (1 + (1 + z0 ls) = 2 + z0 ls); clear; lia).
        split.
        -- cbn [invCore checkDs2 checkDs1Phi1 nat_list_eqb isDGe25One isOddDrainDs isOddDrain1 isHeadP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
           change (GoodDs [0]) with true; cbn [negb orb andb].
           rewrite Hvp5', Hz0_2; cbn [negb andb orb].
           rw_if_neg ltac:(clear; lia).
           rw_if_neg ltac:(clear; lia).
           try rewrite !orb_false_r.
           destruct (6 <=? z0 ls) eqn:Ez6.
           ++ replace (17 <=? 1 + 2 * (2 + z0 ls)) with true by (clear - Ez6; lia).
              rewrite !orb_true_r; cbn [andb]; clear - Hepw5 Hz0_ge; lia.
           ++ replace (9 <=? 1 + (2 + z0 ls)) with false by (clear - Ez6; lia).
              cbn [negb orb andb]; clear - Hepw5 Hz0_ge; lia.
        -- intro fuel. pose proof (Hch_step fuel) as Hf.
           Local Transparent checkChainAux.
           cbn [checkChainAux] in Hf.
           Local Opaque checkChainAux.
           rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf; cbn [isDrainRstDs isRank0 andb orb negb nat_list_eqb Nat.eqb] in Hf.
           try (change (8 <=? 0) with false in Hf; change (0 <=? 2) with true in Hf);
           try (change (8 <=? 1) with false in Hf; change (1 <=? 2) with true in Hf);
           try (change (8 <=? 2) with false in Hf; change (2 <=? 2) with true in Hf);
           cbn [andb orb negb] in Hf.
           rw_if_neg_in Hf ltac:(clear - Hepw5; lia).
           fold tail_b2 in Hf. rewrite Hz_ls2 in Hf.
           cbn [invChain nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
           exact Hf.
      * (* d = S (S (S m'')) = m'' + 3 *)
        replace (S (S (S m''))) with (m'' + 3) in * by (clear; lia).
        destruct ds' as [|d2 ds''].
        -- (* ds = [m'' + 3] *)
           replace (m'' + 3) with (S (S (S m''))) by (clear; lia); cbn [nextState];
             replace (S (S (S m''))) with (m'' + 3) by (clear; lia).
           pose proof (GoodDs_d1_valid (d := m'' + 3) ltac:(clear; lia) Hgd) as Hd8.
           unfold GoodPhiW in Hphiw; cbn [nat_list_eqb isDGe25One] in Hphiw.
           replace (m'' + 3 =? 2) with false in Hphiw by (clear; lia).
           replace (m'' + 3 =? 0) with false in Hphiw by (clear; lia).
           replace (m'' + 3 =? 1) with false in Hphiw by (clear; lia).
           cbn [andb] in Hphiw.
           assert (Hepw_req : (if isOddDrainDs [m'' + 3] then 18 else 16) <= epW ls)
             by (destruct (isOddDrainDs [m'' + 3]); clear - Hphiw; lia).
           assert (Hepw16 : 16 <= epW ls)
             by (destruct (isOddDrainDs [m'' + 3]); clear - Hepw_req; lia).
           assert (Hz0_2 : z0 (p3z 0 :: p3z 0 :: ls) = 2 + z0 ls)
             by (change (1 + (1 + z0 ls) = 2 + z0 ls); clear; lia).
           split.
           ++ cbn [invCore isHeadP5 drop1L ValidEvenLs ValidP5Chain]. rewrite Hz0_2, Hvp5.
              clear - Hd8 Hepw16 Hz0_ge; lia.
           ++ intro fuel. pose proof (Hch_step fuel) as Hf.
              Local Transparent checkChainAux.
              cbn [checkChainAux] in Hf.
              Local Opaque checkChainAux.
              rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf; cbn [andb orb negb] in Hf.
              replace (isDrainRstDs [m'' + 3]) with true in Hf
                by (cbn [isDrainRstDs]; clear - Hd8; lia).
              replace (0 + epW ls <? (if isOddDrainDs [m'' + 3] then 18 else 16)) with false in Hf
                by (destruct (isOddDrainDs [m'' + 3]); clear - Hepw_req; lia).
              fold tail_b2 in Hf. rewrite Hz_ls2 in Hf.
              cbn [headNat invChain drop1L] in Hf |- *.
              replace (m'' + 3 - 7) with (m'' - 4) in Hf by (clear; lia).
              exact Hf.
        -- destruct d2 as [|c'].
           ++ (* ds = (m'' + 3) :: 0 :: ds'' *)
              destruct (GoodDs_pair_d2_cases Hgd) as [[_ [-> Hd8]] | [[Habs _] | [Habs _]]];
                [| discriminate | clear - Habs; lia].
              assert (Hm''2 : 2 <= m'') by (clear - Hd8; lia).
              destruct m'' as [|[|m4]]; try (clear - Hm''2; lia).
              replace (S (S m4) + 3) with (m4 + 5) in * by (clear; lia).
              replace (m4 + 5) with (S (S (S (S (S m4))))) by (clear; lia); cbn [nextState];
                replace (S (S (S (S (S m4))))) with (m4 + 5) by (clear; lia).
              unfold GoodPhiW in Hphiw; cbn [nat_list_eqb isDGe25One] in Hphiw.
              rewrite !andb_false_r in Hphiw.
              assert (Hepw_req : (if isOddDrainDs [m4 + 5; 0] then 18 else 16) <= epW ls)
                by (destruct (isOddDrainDs [m4 + 5; 0]); clear - Hphiw; lia).
              assert (Hepw16 : 16 <= epW ls)
                by (destruct (isOddDrainDs [m4 + 5; 0]); clear - Hepw_req; lia).
              assert (Hz0_2 : z0 (p3z 0 :: p3z 0 :: ls) = 2 + z0 ls)
                by (change (1 + (1 + z0 ls) = 2 + z0 ls); clear; lia).
              assert (Heven_new : ValidEvenLs (p5 :: p3z 0 :: p3z 0 :: ls) = true)
                by (cbn [ValidEvenLs ValidP5Chain]; rewrite Hz0_2, Hvp5; clear - Hepw16 Hz0_ge; lia).
              split.
              ** cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb isHeadP5 andb orb negb].
                 rewrite Heven_new; cbn [negb].
                 rw_if_pos ltac:(clear - Hd8; lia).
                 clear - Hd8; lia.
              ** intro fuel. pose proof (Hch_step fuel) as Hf.
                 Local Transparent checkChainAux.
                 cbn [checkChainAux] in Hf.
                 Local Opaque checkChainAux.
                 rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf; cbn [andb orb negb] in Hf.
                 replace (isDrainRstDs [m4 + 5; 0]) with true in Hf
                   by (cbn [isDrainRstDs]; clear - Hd8; lia).
                 replace (0 + epW ls <? (if isOddDrainDs [m4 + 5; 0] then 18 else 16)) with false in Hf
                   by (destruct (isOddDrainDs [m4 + 5; 0]); clear - Hepw_req; lia).
                 fold tail_b2 in Hf. rewrite Hz_ls2 in Hf.
                 cbn [headNat invChain drop1L] in Hf |- *.
                 rw_if_pos ltac:(clear - Hd8; lia).
                 replace (m4 + 5 - 7) with (m4 + 1 - 3) in Hf by (clear; lia).
                 exact Hf.
           ++ (* ds = (m'' + 3) :: S c' :: ds'' *)
              replace (m'' + 3) with (S (S (S m''))) by (clear; lia); cbn [nextState];
                replace (S (S (S m''))) with (m'' + 3) by (clear; lia).
              replace (S c') with (c' + 1) in * by (clear; lia).
              assert (Hm_f : isDrainRstDs ((m'' + 3) :: (c' + 1) :: ds'') = false)
                by (cbn [isDrainRstDs]; destruct (c' + 1) eqn:Ec1; [clear - Ec1; lia | reflexivity]).
              unfold GoodPhiW in Hphiw; cbn [nat_list_eqb] in Hphiw; rewrite !andb_false_r in Hphiw.
              assert (Hepw16 : 16 <= epW ls)
                by (destruct (isDGe25One ((m'' + 3) :: (c' + 1) :: ds'')), (isOddDrainDs ((m'' + 3) :: (c' + 1) :: ds'')); clear - Hphiw; lia).
              assert (Hz0_2 : z0 (p3z 0 :: p3z 0 :: ls) = 2 + z0 ls)
                by (change (1 + (1 + z0 ls) = 2 + z0 ls); clear; lia).
              assert (Heven_new : ValidEvenLs (p5 :: p3z 0 :: p3z 0 :: ls) = true)
                by (cbn [ValidEvenLs ValidP5Chain]; rewrite Hz0_2, Hvp5; clear - Hepw16 Hz0_ge; lia).
              destruct (GoodDs_pair_d2_cases Hgd) as [[Habs _] | [[Hc'0 [-> Hd_or]] | [Hc'2 [Hd17 [Hgd_tail [Hsub1 Hsub2]]]]]];
                [clear - Habs; lia | |].
              ** (* d2 = 1, ds'' = [] *)
                 assert (c' = 0) by (clear - Hc'0; lia); subst c'.
                 change (0 + 1) with 1 in *.
                 destruct Hd_or as [Hm''0 | Hd25].
                 --- assert (m'' = 0) by (clear - Hm''0; lia); subst m''.
                     split.
                     +++ cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb isHeadP5 MustDrain hasOdd Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
                         rewrite Heven_new; cbn [negb andb orb]; clear; lia.
                     +++ intro fuel. pose proof (Hch_step fuel) as Hf.
                         Local Transparent checkChainAux.
                         cbn [checkChainAux] in Hf.
                         Local Opaque checkChainAux.
                         rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf.
                         change (0 + 3) with 3 in Hf.
                         cbn [isDrainRstDs isRank0 nat_list_eqb GoodDs GoodDsAux GoodDs1 Nat.leb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb] in Hf.
                         rw_if_neg_in Hf ltac:(clear - Hepw16; lia).
                         fold tail_b2 in Hf. rewrite Hz_ls0 in Hf.
                         cbn [invChain isHeadP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.mul Nat.add andb orb negb].
                         exact Hf.
                 --- assert (Hm''22 : 22 <= m'') by (clear - Hd25; lia).
                     assert (Hepw36 : 36 <= epW ls).
                     { cbn [isDGe25One] in Hphiw. rw_if_pos_in Hphiw ltac:(clear - Hd25; lia).
                       clear - Hphiw; lia. }
                     assert (Hz38 : 38 <= z0 (p3z 0 :: p3z 0 :: ls)) by (clear - Hepw36 Hz0_ge Hz0_2; lia).
                     split.
                     +++ cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb].
                         cbn [andb orb negb].
                         destruct (m'' mod 2 =? 0) eqn:Em_ev.
                         *** rewrite Heven_new; cbn [negb isHeadP5 p5Suf MustDrain hasOdd Nat.eqb nat_list_eqb andb].
                             rw_if_neg ltac:(clear - Hm''22 Hz38; lia); reflexivity.
                         *** assert (Hm''23 : 23 <= m'') by (clear - Hm''22 Em_ev; lia).
                             assert (Heven_odd : ValidEvenLs (p3z m'' :: p5 :: p3z 0 :: p3z 0 :: ls) = true)
                               by (cbn [ValidEvenLs]; rewrite Em_ev; cbn [ValidAfterOdd ValidP5Chain]; rewrite Hz0_2, Hvp5; clear - Hepw16 Hz0_ge; lia).
                             cbn [Nat.eqb nat_list_eqb isHeadP5 p5Suf andb].
                             rw_if_neg ltac:(clear - Hm''23 Hz38; lia).
                             rewrite Heven_odd; cbn [negb].
                             assert (Hmd_f : MustDrain (p3z m'' :: p5 :: p3z 0 :: p3z 0 :: ls) = false)
                               by (cbn [MustDrain]; destruct (m'' mod 2 =? 1); reflexivity).
                             rewrite Hmd_f; cbn [andb].
                             rw_if_neg ltac:(clear - Hm''23; lia); cbn [negb].
                             rw_if_neg ltac:(clear - Hm''23; lia); reflexivity.
                     +++ intro fuel. pose proof (Hch_step fuel) as Hf.
                         Local Transparent checkChainAux.
                         cbn [checkChainAux] in Hf.
                         Local Opaque checkChainAux.
                         rewrite Hdec_0_2, Hnp5, !andb_false_r in Hf.
                         replace (isRank0 [m'' + 3; 1]) with false in Hf
                            by (destruct (m'' + 3) as [|[|[|?]]] eqn:E; [clear - E; lia | clear - E; lia | clear - E; lia | reflexivity]).
                         cbn [isDrainRstDs nat_list_eqb GoodDs GoodDsAux GoodDs1 Nat.eqb andb orb negb] in Hf.
                         replace (3 <=? m'' + 3) with true in Hf by (clear; lia).
                         replace (1 <=? 1) with true in Hf by reflexivity.
                         cbn [andb] in Hf.
                         rw_if_neg_in Hf ltac:(clear - Hepw16; lia).
                         fold tail_b2 in Hf. rewrite Hz_ls0 in Hf.
                         rw_if_pos_in Hf ltac:(clear - Hd25; lia).
                         pose proof (checkChainAux_B_ge3_c0_ok_ge22 fuel m'' (p3z 0 :: p3z 0 :: ls) Hm''22) as Hok_t.
                         cbn [invChain isHeadP5 drop1L Nat.eqb nat_list_eqb Nat.mul Nat.add].
                         replace (m'' - 8) with (m'' + 3 - 11) by (clear; lia).
                         destruct (m'' mod 2 =? 0) eqn:Em_ev; cbn [andb].
                         *** rw_if_pos ltac:(clear - Hm''22; lia). rewrite Hok_t; exact Hf.
                         *** rw_if_neg ltac:(clear; lia). rewrite Hok_t; exact Hf.
              ** (* d2 = c' + 1 >= 3 *)
                 destruct (GoodDs_tail_any Hgd_tail) as [Hgd_ds'' Hds''_ne2].
                 assert (Hds2' : checkDs2 (ModeB_ge3 (p5 :: p3z 0 :: p3z 0 :: ls) m'' c' ds'') = true).
                 { cbn [checkDs2]. destruct (nat_list_eqb ds'' [2]) eqn:E2; [| reflexivity].
                   apply nat_list_eqb_true in E2; contradiction. }
                 assert (Hds1' : checkDs1Phi1 (ModeB_ge3 (p5 :: p3z 0 :: p3z 0 :: ls) m'' c' ds'') = true).
                 { cbn [checkDs1Phi1]. destruct (nat_list_eqb ds'' [1]) eqn:E1; cbn [negb]; [| reflexivity].
                   apply nat_list_eqb_true in E1; subst ds''.
                   destruct (GoodDs_pair_d2_cases Hgd_tail) as [[Habs _] | [[_ [_ Hd_c_or]] | [Habs _]]];
                     [clear - Habs; lia | | clear - Habs; lia].
                   destruct Hd_c_or as [Hc'2_eq | Hc'24].
                   - assert (c' = 2) by (clear - Hc'2_eq; lia); subst c'.
                     cbn [Nat.add] in Hgd. pose proof (GoodDs_d31 Hgd) as Hd19.
                     assert (Hmd_f0 : MustDrain (p3z m'' :: p5 :: p3z 0 :: p3z 0 :: ls) = false)
                       by (cbn [MustDrain]; destruct (m'' mod 2 =? 1); reflexivity).
                     destruct (m'' mod 2 =? 0) eqn:Em_ev;
                       rewrite Hmd_f0; cbn [isHeadP5 hasP5 epSum Nat.sub Nat.add Nat.mul Nat.eqb negb andb].
                     + clear - Hd19; lia.
                     + clear - Em_ev Hd19; lia.
                   - destruct (m'' mod 2 =? 0); cbn [isHeadP5].
                     + rw_if_pos ltac:(clear - Hc'24; lia); reflexivity.
                     + rw_if_pos ltac:(clear - Hc'24; lia); reflexivity. }
                 assert (Hphiw_c' : GoodPhiW (c' - 1) ds'' false = true).
                 { replace (c' - 1) with (c' + 1 - 2) by (clear; lia).
                   exact (GoodPhiW_of_GoodDs_sub2 Hc'2 Hgd_tail). }
                 split.
                 --- cbn [invCore].
                     apply if_false_true; [rewrite Hgd_ds'', Hds2', Hds1'; reflexivity |].
                     destruct (m'' mod 2 =? 0) eqn:Em_ev.
                     +++ apply if_negb_false_true; [exact Heven_new |].
                         cbn [isHeadP5 negb].
                         rw_if_neg ltac:(clear - Hc'2; lia).
                         rewrite Hphiw_c'; reflexivity.
                     +++ rw_if_neg ltac:(clear - Hc'2; lia).
                         assert (Heven_odd : ValidEvenLs (p3z m'' :: p5 :: p3z 0 :: p3z 0 :: ls) = true)
                           by (cbn [ValidEvenLs]; rewrite Em_ev; cbn [ValidAfterOdd ValidP5Chain]; rewrite Hz0_2, Hvp5; clear - Hepw16 Hz0_ge; lia).
                         apply if_negb_false_true; [exact Heven_odd |].
                         assert (Hrst_f : ((m'' =? 1) && (c' =? 1) && nat_list_eqb ds'' []) = false) by (clear - Hc'2; lia).
                         assert (Hmd_f : MustDrain (p3z m'' :: p5 :: p3z 0 :: p3z 0 :: ls) = false)
                           by (cbn [MustDrain]; destruct (m'' mod 2 =? 1); reflexivity).
                         apply if_negb_false_true.
                         { rw_if_pos ltac:(clear - Hc'2; lia). rewrite Hrst_f; cbn [negb].
                           rewrite Hphiw_c', orb_true_r; reflexivity. }
                         rewrite Hmd_f; cbn [andb].
                         destruct (m'' <=? 2 * c' + 3) eqn:Ele; [| reflexivity].
                         rewrite Hrst_f.
                         assert (Hgp : GoodPsi (c' - 1) ds'' = true).
                         { unfold GoodPsi. replace (c' - 1 + 1) with (c' + 1 - 1) by (clear - Hc'2; lia).
                           apply Hsub1. clear - Em_ev Ele; lia. }
                         rewrite Hgp; cbn [hasP5 negb orb andb]; rewrite !andb_false_r; cbn [negb orb andb].
                         destruct (nat_list_eqb ds'' [1] && (24 <=? c' - 1)) eqn:Eds1; cbn [negb orb andb]; [| reflexivity].
                         apply andb_true_iff in Eds1 as [Eds1 Hc'24].
                         apply nat_list_eqb_true in Eds1; subst ds''.
                         pose proof (GoodDs_d_ge25_1 (d := m'' + 3) (d2 := c' + 1) ltac:(clear - Hc'24; lia) Hgd) as Hd39.
                         clear - Em_ev Hd39; lia.
                 --- intro fuel. pose proof (Hch_step fuel) as Hf.
                     Local Transparent checkChainAux.
                     cbn [checkChainAux] in Hf.
                     Local Opaque checkChainAux.
                     rewrite Hdec_0_2, Hnp5, !andb_false_r, Hm_f in Hf.
                     replace (isRank0 ((m'' + 3) :: (c' + 1) :: ds'')) with false in Hf
                        by (destruct (m'' + 3) as [|[|[|?]]] eqn:E; [clear - E; lia | clear - E; lia | clear - E; lia | reflexivity]).
                     cbn [nat_list_eqb andb orb negb] in Hf.
                     rw_if_pos_in Hf ltac:(clear - Hc'2; lia).
                     rw_if_neg_in Hf ltac:(destruct (((m'' + 3) mod 2 =? 0) && (m'' + 3 <=? 2 * (c' + 1) + 4)) eqn:Ec1; [rewrite (Hsub1 ltac:(clear - Ec1; lia)); reflexivity | reflexivity]).
                     rw_if_neg_in Hf ltac:(destruct (((m'' + 3) mod 2 =? 0) && (m'' + 3 + 14 <=? 2 * (c' + 1))) eqn:Ec2; [rewrite (Hsub2 ltac:(clear - Ec2; lia)); reflexivity | reflexivity]).
                     rw_if_neg_in Hf ltac:(clear - Hepw16; lia).
                     fold tail_b2 in Hf. rewrite Hz_ls0 in Hf.
                     rw_if_neg_in Hf ltac:(clear - Hc'2; lia).
                     replace (m'' + 3 - 3) with m'' in Hf by (clear; lia).
                     replace (c' + 1 - 1) with c' in Hf by (clear; lia).
                     replace (2 * (c' + 1)) with (2 * c' + 2) in Hf by (clear; lia).
                     cbn [invChain isHeadP5].
                     destruct (m'' mod 2 =? 0).
                     +++ rw_if_neg ltac:(clear - Hc'2; lia); exact Hf.
                     +++ rw_if_neg ltac:(clear - Hc'2; lia).
                         rw_if_neg ltac:(clear - Hc'2; lia); exact Hf.
Qed.

Lemma step_Inv_ModeB_b2 (ls : list LTok) (m : nat) (ds : list nat) :
  Inv (ModeB_b2 ls m ds) -> Inv (nextState (ModeB_b2 ls m ds)).
Proof.
  destruct m as [|[|m'']].
  - exact (step_Inv_ModeB_b2_m0 ls ds).
  - exact (step_Inv_ModeB_b2_m1 ls ds).
  - replace (S (S m'')) with (m'' + 2) by (clear; lia).
    exact (step_Inv_ModeB_b2_mge2 ls m'' ds).
Qed.

Lemma prefSumW_of_ValidP5Chain (ls : list LTok) :
  ValidP5Chain ls = true -> prefSumW ls = 0.
Proof.
  induction ls as [|[m | ] rest IH]; intro H; [reflexivity | | reflexivity].
  destruct m as [|m'].
  - cbn [ValidP5Chain] in H. cbn [prefSumW].
    destruct rest as [|[|] ?]; [reflexivity | exact (IH H) | reflexivity].
  - destruct rest as [|[|] ?]; try discriminate.
    cbn [prefSumW]; destruct (S m' mod 2 =? 1); reflexivity.
Qed.

Lemma MustDrain_of_ValidP5Chain (ls : list LTok) :
  ValidP5Chain ls = true -> MustDrain ls = false.
Proof.
  induction ls as [|[m | ] rest IH]; intro H; [reflexivity | | reflexivity].
  destruct m as [|m'].
  - cbn [ValidP5Chain] in H. exact (IH H).
  - destruct rest as [|[|] ?]; try discriminate.
    cbn [MustDrain]; destruct (S m' mod 2 =? 1); reflexivity.
Qed.

Lemma ep_ge_z0 (ls : list LTok) : z0 ls <= ep ls.
Proof.
  induction ls as [|[m | ] rest IH]; [cbn; lia | | cbn; lia].
  destruct m as [|?]; [cbn [z0 ep Nat.modulo Nat.divmod Nat.sub snd Nat.eqb]; lia | cbn [z0]; lia].
Qed.

Lemma epW_add1_ge_z0 (ls : list LTok) : z0 ls <= epW ls + 1.
Proof.
  induction ls as [|[m | ] rest IH]; [cbn; lia | | cbn; lia].
  destruct m as [|?]; [| cbn [z0]; lia].
  destruct rest as [|[m2 | ] s2]; [cbn; lia | | cbn; lia].
  change (epW (p3z 0 :: p3z m2 :: s2)) with (1 + epW (p3z m2 :: s2)).
  change (z0 (p3z 0 :: p3z m2 :: s2)) with (1 + z0 (p3z m2 :: s2)).
  lia.
Qed.

Lemma isHeadP5_false_of_z0_pos {ls : list LTok} : 1 <= z0 ls -> isHeadP5 ls = false.
Proof.
  destruct ls as [|[|] ?]; cbn [z0 isHeadP5]; [lia | reflexivity | lia].
Qed.

Lemma isHeadP3z1_false_of_z0_pos {ls : list LTok} : 1 <= z0 ls -> isHeadP3z1 ls = false.
Proof.
  destruct ls as [|[[|?] | ] ?]; cbn [z0 isHeadP3z1]; try lia; reflexivity.
Qed.

Lemma hasP5_of_ValidP5Chain_hasOdd (ls : list LTok) :
  ValidP5Chain ls = true -> hasOdd ls = true -> hasP5 ls = true.
Proof.
  induction ls as [|[m | ] rest IH]; intros Hv Ho; [discriminate | | reflexivity].
  destruct m as [|m'].
  - exact (IH Hv Ho).
  - destruct rest as [|[|] ?]; [discriminate | discriminate | reflexivity].
Qed.

Lemma ds_ne_two_of_checkDs2_ModeE_ge2 {ls : list LTok} {k c : nat} {ds : list nat} :
  checkDs2 (ModeE_ge2 ls k c ds) = true ->
  (hasP5 ls = false \/ MustDrain ls = true \/ k mod 2 = 1 \/ isHeadP5 ls = true \/ k + epSum ls < 2 * c + 6) ->
  ds <> [2].
Proof.
  intros H Himp ->. cbn [checkDs2 nat_list_eqb Nat.eqb andb negb] in H.
  destruct Himp as [Hp | [Hm | [Hk | [Hip | Hlt]]]].
  - rewrite Hp in H; discriminate.
  - rewrite Hm in H; cbn [negb] in H; repeat (rewrite ?andb_false_l, ?andb_false_r in H); discriminate.
  - replace (k mod 2 =? 0) with false in H by (clear - Hk; lia).
    repeat (rewrite ?andb_false_l, ?andb_false_r in H); discriminate.
  - rewrite Hip in H; cbn [negb] in H; repeat (rewrite ?andb_false_l, ?andb_false_r in H); discriminate.
  - replace (2 * c + 6 <=? k + epSum ls) with false in H by (clear - Hlt; lia).
    repeat (rewrite ?andb_false_l, ?andb_false_r in H); discriminate.
Qed.

Lemma d25_check_of_ge36 (cz : nat) (ds : list nat) :
  (forall d, ds = [d; 1] -> 25 <= d -> 36 <= cz) ->
  negb (isDGe25One ds) || (36 <=? cz) = true.
Proof.
  intro H. destruct ds as [|d [|d2 ds2]]; try reflexivity.
  destruct d2 as [|[|?]]; try reflexivity.
  destruct ds2 as [|? ?]; try reflexivity.
  unfold isDGe25One.
  destruct (25 <=? d) eqn:Ed; [| reflexivity].
  cbn [negb orb]. pose proof (H d eq_refl ltac:(clear - Ed; lia)); clear - H0; lia.
Qed.

Lemma d25_ge36_of_check {c : nat} {ds : list nat} :
  negb (isDGe25One ds) || (36 <=? c) = true ->
  forall d, ds = [d; 1] -> 25 <= d -> 36 <= c.
Proof.
  intros H d -> Hd. cbn [isDGe25One] in H.
  replace (25 <=? d) with true in H by (clear - Hd; lia).
  cbn [negb orb] in H; clear - H; lia.
Qed.

Lemma GoodPhiW_d25_ge35 {phiW d : nat} :
  25 <= d -> GoodPhiW phiW [d; 1] false = true -> 35 <= phiW.
Proof.
  intros Hd H. unfold GoodPhiW in H.
  cbn [nat_list_eqb isDGe25One orb] in H. rewrite !andb_false_r in H.
  replace (25 <=? d) with true in H by (clear - Hd; lia).
  clear - H; lia.
Qed.

Lemma prefSumW_p3z_m2_bound (m2 : nat) (ls' : list LTok) (k c : nat) :
  k <= 2 * c + 4 -> k + prefSumW (p3z (m2 + 2) :: ls') <= 2 * c + 6 ->
  k + prefSumW (p3z m2 :: ls') <= 2 * c + 4.
Proof.
  intros Hk1 Hk2.
  destruct (m2 mod 2 =? 1) eqn:Em.
  - cbn [prefSumW]; rewrite Em; clear - Hk1; lia.
  - destruct (isHeadP5 ls') eqn:Ep5.
    + destruct ls' as [|[|] ?]; try discriminate.
      cbn [prefSumW]; rewrite Em; clear - Hk1; lia.
    + pose proof (prefSumW_p3z_add2 m2 ls' ltac:(clear - Em; lia) Ep5).
      clear - Hk2 H; lia.
Qed.

Lemma ValidP5Chain_p3z_succ {m : nat} {ls' : list LTok} :
  ValidP5Chain (p3z (m + 1) :: ls') = true ->
  exists suf, ls' = p5 :: suf /\ 18 <= z0 suf /\ ValidP5Chain suf = true.
Proof.
  replace (m + 1) with (S m) by (clear; lia).
  intro H. destruct ls' as [|[|] suf]; try discriminate.
  cbn [ValidP5Chain] in H. apply andb_true_iff in H as [H1 H2].
  exists suf. repeat split; [clear - H1; lia | exact H2].
Qed.

Lemma GoodPhiW_of_ge17_and_d25 (phiW : nat) (ds : list nat) :
  ds <> [2] -> 17 <= phiW ->
  (forall d, ds = [d; 1] -> 25 <= d -> 35 <= phiW) ->
  GoodPhiW phiW ds false = true.
Proof.
  intros Hne2 H17 Hd25. unfold GoodPhiW; cbn [orb].
  replace (nat_list_eqb ds [2]) with false
    by (destruct (nat_list_eqb ds [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]).
  destruct (nat_list_eqb ds [0]); [clear - H17; lia |].
  destruct (nat_list_eqb ds [1]); [clear - H17; lia |].
  destruct (nat_list_eqb ds []); [clear - H17; lia |].
  destruct (isDGe25One ds) eqn:E25.
  - unfold isDGe25One in E25.
    destruct ds as [|d [|d2 ds2]]; try discriminate.
    destruct d2 as [|[|?]]; try discriminate.
    destruct ds2 as [|? ?]; try discriminate.
    pose proof (Hd25 d eq_refl ltac:(clear - E25; lia)); clear - H; lia.
  - destruct (isOddDrainDs ds); clear - H17; lia.
Qed.


#[local] Opaque checkChainAux.

(* ========================================================================== *)
(* Section 4 Part B2: ModeE_ge2 and Master Invariant Preservation step_Inv    *)
(* ========================================================================== *)

Lemma step_Inv_ModeE_ge2_nil (k c : nat) (ds : list nat) :
  Inv (ModeE_ge2 [] k c ds) -> Inv (ModeB_ge3 [] k c ds).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn [negb orb] in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeE_ge2 [] k c ds) = true) by (destruct (checkDs2 (ModeE_ge2 [] k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeE_ge2 [] k c ds) = true) by (destruct (checkDs1Phi1 (ModeE_ge2 [] k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  pose proof (ds_ne_two_of_checkDs2_ModeE_ge2 Hds2 (or_introl eq_refl)) as Hne2.
  assert (Hds2' : checkDs2 (ModeB_ge3 [] k c ds) = true).
  { cbn [checkDs2]. destruct (nat_list_eqb ds [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]. }
  destruct (k mod 2 =? 0) eqn:Ek; try cbv iota in Hc.
  - (* k even *)
    assert (Hk : k mod 2 = 0) by (clear - Ek; lia).
    apply unpack_if_negb_false in Hc as [_ Hc].
    apply unpack_if_negb_false in Hc as [Hk_le Hc].
    apply unpack_if_negb_false in Hc as [Hok_phi _].
    cbn [prefSumW] in Hk_le.
    assert (Hk_le1 : k <= 2 * c + 4) by (clear - Hk_le; lia).
    cbn [isHeadP5 isHeadP3z1 epW MustDrain hasP5 negb andb orb Nat.add] in Hok_phi; rewrite !Nat.add_0_r in Hok_phi; repeat (rewrite ?andb_false_l, ?andb_false_r in Hok_phi); cbn [orb] in Hok_phi.
    assert (Hds1' : checkDs1Phi1 (ModeB_ge3 [] k c ds) = true).
    { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
      rewrite Ek in Hds1 |- *. cbn [isHeadP5 epW hasP5 Nat.add] in Hds1 |- *; rewrite !Nat.add_0_r in Hds1. rewrite !Nat.add_0_r.
      destruct (c =? 1); [discriminate | reflexivity]. }
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      assert (Hepw1 : epW [p3z k] = 1) by (cbn [epW]; rw_if_neg ltac:(clear - Hk; lia); reflexivity).
      rewrite Ek, Hepw1; cbn [ValidEvenLs negb isHeadP5 prefSumW epW hasP5 MustDrain hasOdd Nat.leb orb andb].
      rewrite !Nat.add_0_r, orb_true_r; repeat (rewrite ?andb_false_l, ?andb_false_r); cbn [orb andb negb]; rewrite Hok_phi; cbn [orb andb negb].
      replace (k <=? 2 * c + 4) with true by (clear - Hk_le1; lia); reflexivity.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain] in Hch |- *. rewrite Ek in Hch |- *.
      cbn [isHeadP3z1 isHeadP5 andb] in Hch |- *; rewrite andb_false_r in Hch.
      rewrite <- (checkChainAux_true_E_ge2_to_B_ge3_nil fuel k c ds Hk).
      exact Hch.
  - (* k odd *)
    assert (Hm1 : k mod 2 = 1) by (clear - Ek; lia).
    apply unpack_if_negb_false in Hc as [_ Hc].
    apply unpack_if_negb_false in Hc as [Hck Hc].
    cbn [isP3zP5 dropZ0 z0 Nat.add Nat.mul andb] in Hc.
    rewrite !andb_false_r, !Nat.add_0_r in Hc; cbn [andb] in Hc.
    apply andb_true_iff in Hc as [Hc _]; apply andb_true_iff in Hc as [Hc Hc_1]; apply andb_true_iff in Hc as [Hc_base Hc_9].
    assert (Hck_8_15 : 8 <= c /\ 15 <= k).
    { clear - Hc_base. destruct ds as [|d ?]; [| destruct (3 <=? d)]; lia. }
    destruct Hck_8_15 as [Hc8 Hk15].
    assert (Hc_le : k <= 2 * c + 3) by (clear - Hck; lia).
    pose proof (Hch 1) as Hf1.
    cbn [invChain] in Hf1; rewrite Ek in Hf1.
    cbn [isP3zP5 dropZ0 z0 andb] in Hf1; rewrite !andb_false_r in Hf1; cbn [andb] in Hf1.
    Local Transparent checkChainAux.
    cbn [checkChainAux z0 dropZ0 isHeadP5 Nat.add Nat.mul negb andb] in Hf1.
    Local Opaque checkChainAux.
    rewrite Nat.add_0_r in Hf1.
    apply unpack_if_negb_false in Hf1 as [Hphiw_f Hf1].
    apply andb_true_iff in Hf1 as [Hgp _].
    assert (Hds1' : checkDs1Phi1 (ModeB_ge3 [] k c ds) = true).
    { cbn [checkDs1Phi1]. destruct (nat_list_eqb ds [1]); cbn [negb]; [| reflexivity].
      rewrite Ek. replace (c =? 2) with false by (clear - Hc8; lia); reflexivity. }
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      rewrite Ek.
      rw_if_neg ltac:(clear - Hc8; lia).
      assert (Heven_k : ValidEvenLs [p3z k] = true) by (cbn [ValidEvenLs]; rewrite Ek; reflexivity).
      apply if_negb_false_true; [exact Heven_k |].
      assert (Hrst_f : ((k =? 1) && (c =? 1) && nat_list_eqb ds []) = false) by (replace (c =? 1) with false by (clear - Hc8; lia); rewrite !andb_false_r; reflexivity).
      apply if_negb_false_true.
      { rw_if_pos ltac:(clear - Hc8; lia). rewrite Hrst_f; cbn [negb].
        rewrite Hphiw_f, orb_true_r; reflexivity. }
      assert (Hmd_t : MustDrain [p3z k] = true) by (cbn [MustDrain]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
      rewrite Hmd_t.
      apply if_false_true; [clear - Hc_le; lia |].
      rw_if_pos ltac:(clear - Hc_le; lia).
      rewrite Hrst_f, Hgp; cbn [hasP5 negb orb andb].
      assert (Hds1_ok : negb (nat_list_eqb ds [1] && (24 <=? c - 1)) || (37 <=? k) = true)
        by (destruct (nat_list_eqb ds [1]); [cbn [negb orb] in Hc_1; rewrite Hc_1, orb_true_r; reflexivity | reflexivity]).
      assert (Hds0_ok : negb ((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (8 <=? c - 1)) || (17 <=? k) = true)
        by (destruct (nat_list_eqb ds [] || nat_list_eqb ds [0]); cbn [andb orb negb] in *;
            [destruct (9 <=? c) eqn:Ec9; cbn [andb orb negb] in Hc_9;
             [rewrite Hc_9, orb_true_r; reflexivity | replace (8 <=? c - 1) with false by (clear - Ec9; lia); reflexivity]
            | reflexivity]).
      rewrite andb_true_r, Hds1_ok, Hds0_ok; clear - Hc8 Hk15; lia.
    + intros [|fuel'].
      * cbn [invChain]. rewrite Ek.
        rw_if_neg ltac:(clear - Hc8; lia).
        rw_if_neg ltac:(clear - Hc8; lia); reflexivity.
      * specialize (Hch (S fuel')).
        cbn [invChain] in Hch |- *; rewrite Ek in Hch |- *.
        cbn [isP3zP5 dropZ0 z0 andb] in Hch; rewrite !andb_false_r in Hch; cbn [andb] in Hch.
        rw_if_neg ltac:(clear - Hc8; lia).
        rw_if_neg ltac:(clear - Hc8; lia).
        Local Transparent checkChainAux.
        cbn [checkChainAux z0 dropZ0 isHeadP5 Nat.add Nat.mul negb andb] in Hch.
        cbn [checkChainAux].
        Local Opaque checkChainAux.
        rewrite Nat.add_0_r, Hphiw_f, Hgp in Hch; cbn [negb andb] in Hch.
        assert (Hodd_k : hasOdd [p3z k] = true) by (cbn [hasOdd]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
        assert (Hepsum_k : epSum [p3z k] = k - 1) by (cbn [epSum]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
        assert (Hep_k : ep [p3z k] = 0) by (cbn [ep]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
        assert (Hmd_k : MustDrain [p3z k] = true) by (cbn [MustDrain]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
        rewrite Hodd_k, Hepsum_k, Hep_k, Hmd_k; cbn [hasP5 p5Suf andb negb Nat.add Nat.mul].
        rw_if_pos ltac:(clear - Hc_le; lia).
        rewrite !Nat.add_0_r in Hch. rewrite !Nat.add_0_r. replace (k - 1 + 3) with (k + 2) by (clear - Hk15; lia).
        replace (k - 1 + 2) with (k + 1) by (clear - Hk15; lia).
        exact Hch.
Qed.

Lemma step_Inv_ModeE_ge2_p3z0 (ls' : list LTok) (k c : nat) (ds : list nat) :
  Inv (ModeE_ge2 (p3z 0 :: ls') k c ds) -> Inv (ModeE_ge2 ls' (k + 2) (c + 1) ds).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn [negb orb] in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeE_ge2 (p3z 0 :: ls') k c ds) = true) by (destruct (checkDs2 (ModeE_ge2 (p3z 0 :: ls') k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeE_ge2 (p3z 0 :: ls') k c ds) = true) by (destruct (checkDs1Phi1 (ModeE_ge2 (p3z 0 :: ls') k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  destruct (k mod 2 =? 0) eqn:Ek; try cbv iota in Hc.
  - (* k even *)
    assert (Hk : k mod 2 = 0) by (clear - Ek; lia).
    assert (Hk2 : (k + 2) mod 2 = 0) by (clear - Hk; lia).
    apply unpack_if_negb_false in Hc as [Heven Hc].
    rewrite (ValidEvenLs_p3z_even_cons 0 ls' eq_refl) in Heven.
    apply unpack_if_negb_false in Hc as [Hk_le Hc].
    apply unpack_if_negb_false in Hc as [Hok_phi Hc].
    apply unpack_if_false in Hc as [Hmd_bound Hc].
    apply unpack_if_negb_false in Hc as [_ Hodd_branch].
    pose proof (epSum_p3z_even_cons 0 ls' eq_refl) as Hepsum_eq.
    pose proof (ep_p3z_even_cons 0 ls' eq_refl) as Hep_eq.
    pose proof (hasOdd_p3z_even_cons 0 ls' eq_refl) as Hodd_eq.
    pose proof (MustDrain_p3z_even_cons 0 ls' eq_refl) as Hmd_eq.
    destruct (isHeadP5 ls') eqn:Ep5.
    + destruct ls' as [|[|] suf]; try discriminate.
      assert (Hk_le1 : k <= 2 * c + 4) by (clear - Hk_le; lia).
      assert (Hne2 : ds <> [2]).
      { apply (ds_ne_two_of_checkDs2_ModeE_ge2 Hds2).
        right; right; right; right. rewrite Hepsum_eq; cbn [epSum]; clear - Hk_le1; lia. }
      assert (Hds2' : checkDs2 (ModeE_ge2 (p5 :: suf) (k + 2) (c + 1) ds) = true).
      { cbn [checkDs2]. destruct (nat_list_eqb ds [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]. }
      assert (Hds1' : checkDs1Phi1 (ModeE_ge2 (p5 :: suf) (k + 2) (c + 1) ds) = true).
      { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
        rewrite Ek in Hds1. rw_if_pos ltac:(clear - Hk2; lia).
        cbn [isHeadP5 epW Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add] in Hds1 |- *.
        replace (c + 1 - 1) with c by (clear; lia).
        destruct (c =? 1) eqn:Ec1; cbn [negb] in *; [| reflexivity].
        assert (c = 1) by (clear - Ec1; lia); subst c.
        cbn [hasP5 MustDrain isHeadP5 epSum Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul negb andb] in Hds1.
        clear - Hds1 Hk_le1; lia. }
      cbn [isHeadP5 isHeadP3z1 epW MustDrain Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add negb andb orb] in Hok_phi; rewrite !Nat.add_0_r in Hok_phi; repeat (rewrite ?andb_false_l, ?andb_false_r in Hok_phi); cbn [orb] in Hok_phi.
      split.
      * cbn [invCore].
        apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
        rw_if_pos ltac:(clear - Hk2; lia).
        apply if_negb_false_true; [exact Heven |].
        cbn [prefSumW Nat.add].
        apply if_negb_false_true; [clear - Hk_le1; lia |].
        cbn [isHeadP5 negb].
        replace (c + 1 - 1) with c by (clear; lia).
        replace (1 <=? c + 1) with true by (clear; lia).
        rewrite Hok_phi, orb_true_r; cbn [negb MustDrain isHeadP3z1 hasOdd andb]; rewrite !andb_false_r; reflexivity.
      * intro fuel. specialize (Hch fuel).
        cbn [invChain] in Hch |- *.
        rewrite Ek in Hch. cbn [isHeadP3z1] in Hch |- *.
        rewrite !andb_false_r in Hch; cbv iota in Hch.
        rw_if_pos ltac:(clear - Hk2; lia).
        rewrite !andb_false_r; cbv iota.
        replace (2 * (c + 1) + 4) with (2 * c + 4 + 2) by (clear; lia).
        assert (Hcond_p5 : isHeadP5 (p5 :: suf) = false \/ k + epSum (p5 :: suf) <= 2 * c + 4)
          by (right; cbn [epSum]; clear - Hk_le1; lia).
        rewrite (checkChainAux_true_p3z0 fuel (p5 :: suf) (c + 1) k (2 * c + 4) ds Hcond_p5) in Hch.
        exact Hch.
    + pose proof (epW_p3z_even_cons 0 ls' eq_refl Ep5) as Hepw_eq.
      pose proof (prefSumW_p3z_even_cons 0 ls' eq_refl Ep5) as Hpref_eq.
      pose proof (preP5Val_p3z_cons_of_not_headP5 0 ls' Ep5) as Hpre_eq.
      assert (Hds2' : checkDs2 (ModeE_ge2 ls' (k + 2) (c + 1) ds) = true).
      { cbn [checkDs2] in Hds2 |- *. destruct (nat_list_eqb ds [2]); cbn [negb] in *; [| reflexivity].
        rewrite Ek, Hmd_eq, Hepsum_eq in Hds2; cbn [isHeadP5 hasP5 p5Suf Nat.add] in Hds2.
        rewrite Ep5; replace ((k + 2) mod 2 =? 0) with true by (clear - Hk2; lia); replace (2 * (c + 1) + 6 <=? k + 2 + epSum ls') with (2 * c + 6 <=? k + epSum ls') by (clear; lia); exact Hds2. }
      assert (Hds1' : checkDs1Phi1 (ModeE_ge2 ls' (k + 2) (c + 1) ds) = true).
      { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
        rewrite Ek in Hds1. rw_if_pos ltac:(clear - Hk2; lia).
        cbn [isHeadP5] in Hds1; rewrite Hepw_eq in Hds1; rewrite !Ep5.
        replace (c + 1 + epW ls') with (c + (1 + epW ls')) by (clear; lia).
        destruct (c + (1 + epW ls') =? 1); cbn [negb] in *; [| reflexivity].
        rewrite Hmd_eq, Hepsum_eq in Hds1; cbn [hasP5 isHeadP5 Nat.add] in Hds1.
        replace (2 * (c + 1) + 14 <=? k + 2 + epSum ls') with (2 * c + 14 <=? k + epSum ls') by (clear; lia); exact Hds1. }
      split.
      * cbn [invCore].
        apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
        rw_if_pos ltac:(clear - Hk2; lia).
        apply if_negb_false_true; [exact Heven |].
        rewrite Hpref_eq, Nat.add_0_l in Hk_le.
        apply if_negb_false_true; [clear - Hk_le; lia |].
        cbn [isHeadP5 isHeadP3z1 negb andb] in Hok_phi.
        apply if_negb_false_true.
        { rewrite Ep5; cbn [negb].
          replace (k + 2 =? 0) with false by (clear; lia); cbn [andb].
          rewrite andb_false_r.
          replace (c + 1 + epW ls') with (c + epW (p3z 0 :: ls')) by (clear - Hepw_eq; lia).
          replace (c + 1 + ep ls') with (c + ep (p3z 0 :: ls')) by (clear - Hep_eq; lia).
          replace (k + 2 + epSum ls' + 2 * ep ls')
            with (k + epSum (p3z 0 :: ls') + 2 * ep (p3z 0 :: ls')) by (clear - Hepsum_eq Hep_eq; lia).
          rewrite <- Hmd_eq, <- Hpre_eq.
          exact Hok_phi. }
        apply if_false_true; [rewrite Hmd_eq, Hepsum_eq in Hmd_bound; replace (2 * (c + 1) + 4 <? k + 2 + epSum ls') with (2 * c + 4 <? k + epSum ls') by (clear; lia); exact Hmd_bound |].
        replace (k + 2 =? 0) with false by (clear; lia); cbn [andb].
        cbn [negb].
        cbn [isHeadP3z1] in Hodd_branch; rewrite andb_false_r in Hodd_branch.
        rewrite Hodd_eq, Hepsum_eq, Nat.add_0_l in Hodd_branch.
        replace (k + 2 + epSum ls' <=? 2 * (c + 1) + 4) with (k + epSum ls' <=? 2 * c + 4) by (clear; lia).
        destruct (hasOdd ls' && (k + epSum ls' <=? 2 * c + 4)); [| reflexivity].
        replace (c + 1 + ep ls') with (c + ep (p3z 0 :: ls')) by (clear - Hep_eq; lia).
        replace (k + 2 + epSum ls' + 2 * ep ls') with (k + epSum ls' + 2 * ep (p3z 0 :: ls')) by (clear - Hep_eq; lia).
        rewrite <- Hmd_eq, <- Hpre_eq.
        exact Hodd_branch.
      * intro fuel. specialize (Hch fuel).
        cbn [invChain] in Hch |- *.
        rewrite Ek in Hch. cbn [isHeadP3z1] in Hch; rewrite andb_false_r in Hch.
        rw_if_pos ltac:(clear - Hk2; lia).
        replace (k + 2 =? 0) with false by (clear; lia); cbn [andb].
        replace (2 * (c + 1) + 4) with (2 * c + 4 + 2) by (clear; lia).
        rewrite (checkChainAux_true_p3z0 fuel ls' (c + 1) k (2 * c + 4) ds (or_introl Ep5)) in Hch.
        exact Hch.
  - (* k odd *)
    assert (Hm1 : k mod 2 = 1) by (clear - Ek; lia).
    assert (Hk2 : (k + 2) mod 2 = 1) by (clear - Hm1; lia).
    pose proof (ds_ne_two_of_checkDs2_ModeE_ge2 Hds2 (or_intror (or_intror (or_introl Hm1)))) as Hne2.
    assert (Hds2' : checkDs2 (ModeE_ge2 ls' (k + 2) (c + 1) ds) = true).
    { cbn [checkDs2]. destruct (nat_list_eqb ds [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]. }
    assert (Hds1' : checkDs1Phi1 (ModeE_ge2 ls' (k + 2) (c + 1) ds) = true).
    { cbn [checkDs1Phi1]. destruct (nat_list_eqb ds [1]); cbn [negb]; [| reflexivity].
      rw_if_neg ltac:(clear - Hk2; lia); reflexivity. }
    apply unpack_if_negb_false in Hc as [Hvp5 Hc].
    cbn [ValidP5Chain] in Hvp5.
    apply unpack_if_negb_false in Hc as [Hck Hc].
    cbn [headP3zVal andb] in Hc; rewrite andb_false_r in Hc.
    assert (Hz_eq : c + 1 + z0 ls' = c + z0 (p3z 0 :: ls')) by (cbn [z0]; clear; lia).
    assert (Hk_eq : k + 2 + 2 * z0 ls' = k + 2 * z0 (p3z 0 :: ls')) by (cbn [z0]; clear; lia).
    assert (Hb2_eq :
      (nat_list_eqb ds [] && (((k + 2 =? 1) && (c + 1 =? 1) && (z0 ls' =? 1)) || ((k + 2 =? 3) && (c + 1 =? 2) && (z0 ls' =? 0))) &&
       isP3zP5 (dropZ0 ls') && (18 <=? headP3zVal (dropZ0 ls')) && (38 <=? z0 (p5Suf ls'))) =
      (nat_list_eqb ds [] && (((k =? 1) && (c =? 1) && (z0 (p3z 0 :: ls') =? 1)) || ((k =? 3) && (c =? 2) && (z0 (p3z 0 :: ls') =? 0))) &&
       isP3zP5 (dropZ0 (p3z 0 :: ls')) && (18 <=? headP3zVal (dropZ0 (p3z 0 :: ls'))) && (38 <=? z0 (p5Suf (p3z 0 :: ls'))))).
    { cbn [z0 dropZ0 p5Suf].
      replace (k + 2 =? 1) with false by (clear; lia).
      replace (k + 2 =? 3) with (k =? 1) by (clear; lia).
      replace (c + 1 =? 2) with (c =? 1) by (clear; lia).
      replace (S (z0 ls') =? 1) with (z0 ls' =? 0) by (clear; lia).
      replace (S (z0 ls') =? 0) with false by (clear; lia).
      rewrite !andb_false_l, !andb_false_r, orb_false_l, orb_false_r; reflexivity. }
    assert (Hb1_f : nat_list_eqb ds [] && (k + 2 =? 1) && (c + 1 =? 1) && isP3zP5 ls' && (3 <=? headP3zVal ls') = false)
      by (replace (k + 2 =? 1) with false by (clear; lia); rewrite !andb_false_r; reflexivity).
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      rw_if_neg ltac:(clear - Hk2; lia).
      apply if_negb_false_true; [exact Hvp5 |].
      apply if_negb_false_true; [clear - Hck; lia |].
      rewrite Hb1_f; cbv iota.
      rewrite Hb2_eq, Hz_eq, Hk_eq.
      exact Hc.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain] in Hch |- *.
      rewrite Ek in Hch.
      cbn [headP3zVal] in Hch; rewrite andb_false_r in Hch; cbv iota in Hch.
      rw_if_neg ltac:(clear - Hk2; lia).
      rewrite Hb1_f; cbv iota.
      rewrite Hb2_eq.
      destruct (nat_list_eqb ds [] &&
        (((k =? 1) && (c =? 1) && (z0 (p3z 0 :: ls') =? 1)) || ((k =? 3) && (c =? 2) && (z0 (p3z 0 :: ls') =? 0))) &&
        isP3zP5 (dropZ0 (p3z 0 :: ls')) && (18 <=? headP3zVal (dropZ0 (p3z 0 :: ls'))) && (38 <=? z0 (p5Suf (p3z 0 :: ls'))));
        [exact Hch |].
      rewrite (checkChainAux_false_p3z0 fuel ls' c k 0 ds) in Hch.
      exact Hch.
Qed.

Lemma step_Inv_ModeE_ge2_p5 (ls' : list LTok) (k c : nat) (ds : list nat) :
  Inv (ModeE_ge2 (p5 :: ls') k c ds) -> Inv (ModeE_ge2 ls' (k + 3) (c + 2) ds).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn [negb orb] in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeE_ge2 (p5 :: ls') k c ds) = true) by (destruct (checkDs2 (ModeE_ge2 (p5 :: ls') k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeE_ge2 (p5 :: ls') k c ds) = true) by (destruct (checkDs1Phi1 (ModeE_ge2 (p5 :: ls') k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  pose proof (ds_ne_two_of_checkDs2_ModeE_ge2 Hds2 (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Hne2.
  assert (Hds2' : checkDs2 (ModeE_ge2 ls' (k + 3) (c + 2) ds) = true).
  { cbn [checkDs2]. destruct (nat_list_eqb ds [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]. }
  destruct (k mod 2 =? 0) eqn:Ek; try cbv iota in Hc.
  - (* k even *)
    assert (Hk : k mod 2 = 0) by (clear - Ek; lia).
    assert (Hk3 : (k + 3) mod 2 = 1) by (clear - Hk; lia).
    assert (Hds1' : checkDs1Phi1 (ModeE_ge2 ls' (k + 3) (c + 2) ds) = true).
    { cbn [checkDs1Phi1]. destruct (nat_list_eqb ds [1]); cbn [negb]; [| reflexivity].
      rw_if_neg ltac:(clear - Hk3; lia); reflexivity. }
    apply unpack_if_negb_false in Hc as [Heven Hc].
    cbn [ValidEvenLs] in Heven. apply andb_true_iff in Heven as [Hz18_b Hvp5].
    assert (Hz18 : 18 <= z0 ls') by (clear - Hz18_b; lia).
    apply unpack_if_negb_false in Hc as [Hk_le Hc].
    apply unpack_if_negb_false in Hc as [Hok_phi _].
    cbn [isHeadP5 negb] in Hok_phi.
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      rw_if_neg ltac:(clear - Hk3; lia).
      apply if_negb_false_true; [exact Hvp5 |].
      apply if_negb_false_true; [clear - Hk_le; lia |].
      replace (k + 3 =? 1) with false by (clear; lia); replace (z0 ls' =? 1) with false by (clear - Hz18; lia); replace (z0 ls' =? 0) with false by (clear - Hz18; lia); repeat (rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l); cbv iota.
      assert (Hbase : (if match ds with | d :: _ => 3 <=? d | [] => false end
        then (20 <=? c + 2 + z0 ls') && (15 <=? k + 3 + 2 * z0 ls')
        else (8 <=? c + 2 + z0 ls') && (15 <=? k + 3 + 2 * z0 ls')) = true)
        by (destruct ds as [|d ?]; [| destruct (3 <=? d)]; clear - Hz18; lia).
      rewrite Hbase.
      replace (17 <=? k + 3 + 2 * z0 ls') with true by (clear - Hz18; lia).
      replace (37 <=? k + 3 + 2 * z0 ls') with true by (clear - Hz18; lia).
      rewrite ?orb_true_r; cbn [andb].
      apply d25_check_of_ge36.
      intros d -> Hd25.
      cbn [nat_list_eqb isHeadP3z1 MustDrain andb orb] in Hok_phi; repeat (rewrite ?andb_false_r, ?andb_false_l, ?orb_false_l in Hok_phi).
      apply andb_true_iff in Hok_phi as [_ Hphiw].
      pose proof (GoodPhiW_d25_ge35 Hd25 Hphiw); clear - H; lia.
    + intro fuel. specialize (Hch (S fuel)).
      cbn [invChain] in Hch |- *.
      rewrite Ek in Hch; cbn [isHeadP3z1] in Hch; rewrite andb_false_r in Hch.
      rw_if_neg ltac:(clear - Hk3; lia).
      replace (k + 3 =? 1) with false by (clear; lia); replace (z0 ls' =? 1) with false by (clear - Hz18; lia); replace (z0 ls' =? 0) with false by (clear - Hz18; lia); repeat (rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l); cbv iota.
      Local Transparent checkChainAux.
      cbn [checkChainAux hasOdd hasP5 isHeadP5 p5Suf ep epSum andb orb negb Nat.add Nat.mul] in Hch.
      Local Opaque checkChainAux.
      rewrite !Nat.add_0_r in Hch; replace (c + 1 + 1) with (c + 2) in Hch by (clear; lia).
      exact Hch.
  - (* k odd *)
    assert (Hm1 : k mod 2 = 1) by (clear - Ek; lia).
    assert (Hk3 : (k + 3) mod 2 = 0) by (clear - Hm1; lia).
    apply unpack_if_negb_false in Hc as [Hvp5_p5 Hc].
    cbn [ValidP5Chain] in Hvp5_p5; apply andb_true_iff in Hvp5_p5 as [Hz18_b Hvp5].
    assert (Hz18 : 18 <= z0 ls') by (clear - Hz18_b; lia).
    pose proof (ValidP5Chain_imp_ValidEvenLs ls' Hvp5) as Heven'.
    pose proof (prefSumW_of_ValidP5Chain ls' Hvp5) as Hpref0.
    pose proof (MustDrain_of_ValidP5Chain ls' Hvp5) as Hmd0.
    pose proof (isHeadP5_false_of_z0_pos (ls := ls') ltac:(clear - Hz18; lia)) as Hnp5.
    pose proof (isHeadP3z1_false_of_z0_pos (ls := ls') ltac:(clear - Hz18; lia)) as Hnp3z1.
    assert (Hepw17 : 17 <= epW ls') by (pose proof (epW_add1_ge_z0 ls'); clear - Hz18 H; lia).
    assert (Hep18 : 18 <= ep ls') by (pose proof (ep_ge_z0 ls'); clear - Hz18 H; lia).
    apply unpack_if_negb_false in Hc as [Hck Hc].
    cbn [isP3zP5 dropZ0 z0 Nat.add Nat.mul andb] in Hc; rewrite !andb_false_r in Hc; cbn [andb] in Hc.
    apply andb_true_iff in Hc as [Hc Hc_25]; apply andb_true_iff in Hc as [Hc _]; apply andb_true_iff in Hc as [Hc_base _].
    assert (Hck_8_15 : 8 <= c /\ 15 <= k).
    { clear - Hc_base. destruct ds as [|d ?]; [| destruct (3 <=? d)]; lia. }
    destruct Hck_8_15 as [Hc8 Hk15].
    assert (Hds1' : checkDs1Phi1 (ModeE_ge2 ls' (k + 3) (c + 2) ds) = true).
    { cbn [checkDs1Phi1]. destruct (nat_list_eqb ds [1]); cbn [negb]; [| reflexivity].
      rw_if_pos ltac:(clear - Hk3; lia). rewrite Hnp5.
      replace (c + 2 + epW ls' =? 1) with false by (clear - Hepw17; lia); reflexivity. }
    assert (Hphiw' : GoodPhiW (c + 2 + epW ls') ds false = true).
    { apply GoodPhiW_of_ge17_and_d25; [exact Hne2 | clear - Hepw17; lia |].
      intros d Hd_eq Hd25.
      pose proof (d25_ge36_of_check Hc_25 d Hd_eq Hd25); clear - H; lia. }
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      rw_if_pos ltac:(clear - Hk3; lia).
      apply if_negb_false_true; [exact Heven' |].
      rewrite Hpref0, Nat.add_0_r.
      apply if_negb_false_true; [clear - Hck; lia |].
      apply if_negb_false_true.
      { rewrite Hnp5; cbn [negb]. rewrite (GoodPhiW_mono _ _ _ Hphiw'), orb_true_r; reflexivity. }
      rewrite Hmd0, Hnp3z1, andb_false_r; cbn [andb negb].
      destruct (hasOdd ls' && (k + 3 + epSum ls' <=? 2 * (c + 2) + 4)) eqn:Econd; [| reflexivity].
      apply andb_true_iff in Econd as [Hodd_t Hdec_m].
      pose proof (hasP5_of_ValidP5Chain_hasOdd ls' Hvp5 Hodd_t) as Hp5_t.
      pose proof (Hch 2) as Hf2.
      cbn [invChain] in Hf2; rewrite Ek in Hf2.
      cbn [isP3zP5 dropZ0 z0 andb] in Hf2; rewrite !andb_false_r in Hf2; cbn [andb] in Hf2.
      Local Transparent checkChainAux.
      cbn [checkChainAux z0 dropZ0 isHeadP5 Nat.add Nat.mul negb andb] in Hf2.
      Local Opaque checkChainAux.
      rewrite !Nat.add_0_r, Hodd_t, Hnp5, Hmd0, Hp5_t in Hf2.
      rw_if_pos_in Hf2 ltac:(clear - Hdec_m; lia).
      rewrite ?andb_true_r in Hf2; cbn [orb negb andb GoodPsi] in Hf2; replace (c + 3 + ep ls' - 1 + 1) with (c + 3 + ep ls') in Hf2 by (clear; lia).
      assert (Hgp : GoodPsi (c + 2 + ep ls') ds = true).
      { unfold GoodPsi. replace (c + 2 + ep ls' + 1) with (c + 3 + ep ls') by (clear; lia). exact Hf2. }
      rewrite Hgp; cbn [negb orb andb].
      replace (36 <=? k + 3 + epSum ls' + 2 * ep ls') with true by (clear - Hep18; lia).
      replace (16 <=? k + 3 + epSum ls' + 2 * ep ls') with true by (clear - Hep18; lia).
      rewrite !orb_true_r; reflexivity.
    + intro fuel. specialize (Hch (S fuel)).
      cbn [invChain] in Hch |- *.
      rewrite Ek in Hch; cbn [isP3zP5 dropZ0 z0 andb] in Hch; rewrite !andb_false_r in Hch; cbn [andb] in Hch.
      rw_if_pos ltac:(clear - Hk3; lia).
      rewrite Hnp3z1, andb_false_r; cbv iota.
      Local Transparent checkChainAux.
      cbn [checkChainAux z0 dropZ0 isHeadP5 negb andb] in Hch.
      Local Opaque checkChainAux.
      rewrite ?Nat.mul_0_r, ?Nat.add_0_r in Hch; replace (c + 3) with (c + 2 + 1) in Hch by (clear; lia).
      exact Hch.
Qed.

Lemma step_Inv_ModeE_ge2_p3z_ge2 (m2 : nat) (ls' : list LTok) (k c : nat) (ds : list nat) :
  Inv (ModeE_ge2 (p3z (m2 + 2) :: ls') k c ds) -> Inv (ModeB_ge3 (p3z m2 :: ls') k c ds).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hgd : GoodDs ds = true) by (destruct (GoodDs ds); cbn [negb orb] in Hg; [reflexivity | discriminate]).
  assert (Hds2 : checkDs2 (ModeE_ge2 (p3z (m2 + 2) :: ls') k c ds) = true) by (destruct (checkDs2 (ModeE_ge2 (p3z (m2 + 2) :: ls') k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  assert (Hds1 : checkDs1Phi1 (ModeE_ge2 (p3z (m2 + 2) :: ls') k c ds) = true) by (destruct (checkDs1Phi1 (ModeE_ge2 (p3z (m2 + 2) :: ls') k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite !orb_true_r in Hg; discriminate]).
  destruct (k mod 2 =? 0) eqn:Ek; try cbv iota in Hc.
  - (* k even *)
    assert (Hk : k mod 2 = 0) by (clear - Ek; lia).
    apply unpack_if_negb_false in Hc as [Heven Hc].
    rewrite ValidEvenLs_p3z_add2 in Heven.
    apply unpack_if_negb_false in Hc as [Hk_le Hc].
    apply unpack_if_negb_false in Hc as [Hok_phi Hc].
    apply unpack_if_false in Hc as [Hmd_bound Hc].
    apply unpack_if_negb_false in Hc as [_ Hodd_branch].
    pose proof (MustDrain_p3z_add2 m2 ls') as Hmd_eq.
    pose proof (epSum_p3z_add2 m2 ls') as Hepsum_eq.
    pose proof (ep_p3z_add2 m2 ls') as Hep_eq.
    pose proof (epW_p3z_add2 m2 ls') as Hepw_eq.
    pose proof (hasOdd_p3z_add2 m2 ls') as Hodd_eq.
    assert (Hds2' : checkDs2 (ModeB_ge3 (p3z m2 :: ls') k c ds) = true).
    { cbn [checkDs2] in Hds2 |- *. destruct (nat_list_eqb ds [2]); cbn [negb] in *; [| reflexivity].
      rewrite Ek, Hmd_eq, Hepsum_eq in Hds2; rewrite Ek.
      cbn [isHeadP5 hasP5 p5Suf] in Hds2 |- *; replace (2 * c + 4 <=? k + epSum (p3z m2 :: ls')) with (2 * c + 6 <=? k + (epSum (p3z m2 :: ls') + 2)) by (clear; lia); exact Hds2. }
    assert (Hds1' : checkDs1Phi1 (ModeB_ge3 (p3z m2 :: ls') k c ds) = true).
    { cbn [checkDs1Phi1] in Hds1 |- *. destruct (nat_list_eqb ds [1]); cbn [negb] in *; [| reflexivity].
      rewrite Ek in Hds1 |- *; cbn [isHeadP5] in Hds1 |- *.
      rewrite Hepw_eq in Hds1.
      destruct (c + epW (p3z m2 :: ls') =? 1); cbn [negb] in *; [| reflexivity].
      rewrite Hmd_eq, Hepsum_eq in Hds1.
      rewrite (MustDrain_p3z_even_cons k (p3z m2 :: ls') Hk).
      cbn [hasP5 isHeadP5] in Hds1 |- *; replace (2 * c + 12 <=? k + epSum (p3z m2 :: ls')) with (2 * c + 14 <=? k + (epSum (p3z m2 :: ls') + 2)) by (clear; lia); exact Hds1. }
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
      rewrite Ek.
      apply if_negb_false_true; [exact Heven |].
      assert (Hstart0 : isHeadP3z1 (p3z (m2 + 2) :: ls') = false) by (replace (m2 + 2) with (S (S m2)) by (clear; lia); reflexivity).
      cbn [isHeadP5 negb] in Hok_phi; rewrite Hstart0, andb_false_l in Hok_phi.
      cbn [isHeadP5] in Hk_le; apply andb_true_iff in Hk_le as [Hk_le1 Hk_le2].
      pose proof (prefSumW_p3z_m2_bound m2 ls' k c ltac:(clear - Hk_le1; lia) ltac:(clear - Hk_le2; lia)) as Hpref_m2.
      assert (Hepw_ge1 : 1 <= epW (p3z k :: p3z m2 :: ls'))
        by (rewrite (epW_p3z_even_cons k (p3z m2 :: ls') Hk eq_refl); clear; lia).
      apply if_negb_false_true.
      { cbn [isHeadP5 negb].
        replace (k + prefSumW (p3z m2 :: ls') <=? 2 * c + 4) with true by (clear - Hpref_m2; lia).
        replace (1 <=? epW (p3z k :: p3z m2 :: ls')) with true by (clear - Hepw_ge1; lia).
        rewrite orb_true_r, andb_true_r, andb_true_l.
        rewrite Hepw_eq, Hmd_eq, Hep_eq, Hepsum_eq in Hok_phi.
        replace (k + (epSum (p3z m2 :: ls') + 2) + 2 * ep (p3z m2 :: ls'))
          with (k + epSum (p3z m2 :: ls') + 2 * ep (p3z m2 :: ls') + 2) in Hok_phi by (clear; lia).
        cbn [hasP5 p5Suf] in Hok_phi |- *.
        destruct (MustDrain (p3z m2 :: ls')) eqn:Emd; [| repeat (rewrite ?andb_false_r, ?andb_false_l, ?orb_false_l in Hok_phi); repeat (rewrite ?andb_false_r, ?andb_false_l, ?orb_false_l); exact Hok_phi].
        rewrite (preP5Val_p3z_add2_of_not_headP5 m2 ls' (not_isHeadP5_of_MustDrain_p3z m2 ls' Emd)) in Hok_phi.
        exact Hok_phi. }
      apply if_false_true; [rewrite Hmd_eq, Hepsum_eq in Hmd_bound; replace (2 * c + 2 <? k + epSum (p3z m2 :: ls')) with (2 * c + 4 <? k + (epSum (p3z m2 :: ls') + 2)) by (clear; lia); exact Hmd_bound |].
      rewrite Hstart0, andb_false_r in Hodd_branch; cbn [negb] in Hodd_branch.
      rewrite Hodd_eq, Hepsum_eq in Hodd_branch.
      replace (k + epSum (p3z m2 :: ls') <=? 2 * c + 2)
        with (k + (epSum (p3z m2 :: ls') + 2) <=? 2 * c + 4) by (clear; lia).
      destruct (hasOdd (p3z m2 :: ls') && (k + (epSum (p3z m2 :: ls') + 2) <=? 2 * c + 4)); [| reflexivity].
      rewrite Hep_eq, Hmd_eq in Hodd_branch.
      replace (k + (epSum (p3z m2 :: ls') + 2) + 2 * ep (p3z m2 :: ls'))
        with (k + epSum (p3z m2 :: ls') + 2 * ep (p3z m2 :: ls') + 2) in Hodd_branch by (clear; lia).
      cbn [hasP5 p5Suf] in Hodd_branch |- *.
      destruct (MustDrain (p3z m2 :: ls')) eqn:Emd; [| cbn [negb] in Hodd_branch |- *; repeat (rewrite ?orb_true_l, ?orb_true_r in Hodd_branch); repeat (rewrite ?orb_true_l, ?orb_true_r); exact Hodd_branch].
      rewrite (preP5Val_p3z_add2_of_not_headP5 m2 ls' (not_isHeadP5_of_MustDrain_p3z m2 ls' Emd)) in Hodd_branch.
      exact Hodd_branch.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain] in Hch |- *. rewrite Ek in Hch |- *.
      assert (Hstart0 : isHeadP3z1 (p3z (m2 + 2) :: ls') = false) by (replace (m2 + 2) with (S (S m2)) by (clear; lia); reflexivity).
      rewrite Hstart0, andb_false_r in Hch.
      cbn [isHeadP5 andb].
      rewrite (checkChainAux_true_E_ge2_to_B_ge3_even fuel m2 ls' k c ds Hk) in Hch.
      exact Hch.
  - (* k odd *)
    assert (Hm1 : k mod 2 = 1) by (clear - Ek; lia).
    pose proof (ds_ne_two_of_checkDs2_ModeE_ge2 Hds2 (or_intror (or_intror (or_introl Hm1)))) as Hne2.
    assert (Hds2' : checkDs2 (ModeB_ge3 (p3z m2 :: ls') k c ds) = true).
    { cbn [checkDs2]. destruct (nat_list_eqb ds [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]. }
    apply unpack_if_negb_false in Hc as [Hvp5_0 Hc].
    replace (m2 + 2) with (m2 + 1 + 1) in Hvp5_0 by (clear; lia).
    destruct (ValidP5Chain_p3z_succ Hvp5_0) as [suf [-> [Hz18 Hvp5]]].
    apply unpack_if_negb_false in Hc as [Hck Hc].
    set (nls := p3z k :: p3z m2 :: p5 :: suf).
    assert (Heven_nls : ValidEvenLs nls = true)
      by (cbn [nls ValidEvenLs ValidAfterOdd]; rewrite Ek, Hvp5; clear - Hz18; lia).
    assert (Hmd_nls : MustDrain nls = true)
      by (cbn [nls MustDrain]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
    assert (Hz0_eq : z0 (p3z (m2 + 2) :: p5 :: suf) = 0)
      by (replace (m2 + 2) with (S (S m2)) by (clear; lia); reflexivity).
    assert (Hdz0_eq : dropZ0 (p3z (m2 + 2) :: p5 :: suf) = p3z (m2 + 2) :: p5 :: suf)
      by (replace (m2 + 2) with (S (S m2)) by (clear; lia); reflexivity).
    destruct (nat_list_eqb ds [] && (k =? 1) && (c =? 1) &&
      isP3zP5 (p3z (m2 + 2) :: p5 :: suf) && (3 <=? headP3zVal (p3z (m2 + 2) :: p5 :: suf))) eqn:Eb1.
    + assert (ds = [] /\ k = 1 /\ c = 1 /\ 1 <= m2) as [-> [-> [-> Hm2_1]]].
      { cbn [headP3zVal isP3zP5] in Eb1. destruct (nat_list_eqb ds []) eqn:Eds0; [| discriminate]. cbn [andb] in Eb1.
        repeat split; [exact (proj1 (nat_list_eqb_true _ _) Eds0) | clear - Eb1; lia | clear - Eb1; lia | clear - Eb1; lia]. }
      destruct m2 as [|m2']; [clear - Hm2_1; lia |].
      split.
      * cbn [invCore GoodDs checkDs2 checkDs1Phi1 nat_list_eqb isP3zGe1P5 MustDrain Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul andb orb negb].
        fold nls. rewrite Heven_nls; reflexivity.
      * intro fuel. specialize (Hch fuel).
        cbn [invChain nat_list_eqb isP3zP5 headP3zVal drop2L Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb] in Hch |- *.
        rw_if_pos_in Hch ltac:(clear; lia).
        replace (S m2' + 2 - 2) with (S m2') in Hch by (clear; lia).
        exact Hch.
    + destruct (nat_list_eqb ds [] &&
        (((k =? 1) && (c =? 1) && (z0 (p3z (m2 + 2) :: p5 :: suf) =? 1)) ||
         ((k =? 3) && (c =? 2) && (z0 (p3z (m2 + 2) :: p5 :: suf) =? 0))) &&
        isP3zP5 (dropZ0 (p3z (m2 + 2) :: p5 :: suf)) &&
        (18 <=? headP3zVal (dropZ0 (p3z (m2 + 2) :: p5 :: suf))) &&
        (38 <=? z0 (p5Suf (p3z (m2 + 2) :: p5 :: suf)))) eqn:Eb2.
      * pose proof Eb2 as Eb2_orig.
        rewrite Hz0_eq, Hdz0_eq in Eb2; cbn [headP3zVal p5Suf isP3zP5] in Eb2.
        assert (ds = [] /\ k = 3 /\ c = 2 /\ 16 <= m2 /\ 38 <= z0 suf) as [-> [-> [-> [Hm2_16 Hz38]]]].
        { destruct (nat_list_eqb ds []) eqn:Eds0; [| discriminate]. cbn [andb] in Eb2.
          repeat split; [exact (proj1 (nat_list_eqb_true _ _) Eds0) | clear - Eb2; lia | clear - Eb2; lia | clear - Eb2; lia | clear - Eb2; lia]. }
        split.
        -- unfold nls in *; cbn [invCore GoodDs GoodDsAux GoodDs1 checkDs2 checkDs1Phi1 isHeadP5 prefSumW epW hasOdd epSum ep hasP5 preP5Val p5Suf GoodPhiW GoodPsi isDGe25One isOddDrainDs nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul andb orb negb] in *.
           rewrite Heven_nls, Hmd_nls.
           replace (16 <=? m2) with true by (clear - Hm2_16; lia).
           replace (38 <=? z0 suf) with true by (clear - Hz38; lia).
           reflexivity.
        -- intros [|fuel'].
           ++ cbn [invChain Nat.modulo Nat.divmod Nat.sub snd Nat.eqb nat_list_eqb andb]. reflexivity.
           ++ specialize (Hch fuel').
              cbn [invChain] in Hch |- *.
              change (3 mod 2 =? 0) with false in Hch |- *; cbn [andb orb negb] in Hch |- *.
              rewrite Eb1, Eb2_orig, Hdz0_eq in Hch; cbn [headP3zVal drop2L] in Hch.
              cbn [Nat.eqb nat_list_eqb andb].
              Local Transparent checkChainAux.
              cbn [checkChainAux].
              Local Opaque checkChainAux.
              fold nls.
              change (hasOdd nls) with true.
              change (epSum nls) with 2.
              change (ep nls) with 0.
              change (hasP5 nls) with true.
              change (preP5Val nls) with m2.
              change (p5Suf nls) with suf.
              rewrite Hmd_nls; cbn [Nat.add Nat.mul nat_list_eqb andb orb negb].
              change (2 <=? 6) with true; cbv iota.
              rw_if_neg ltac:(clear - Hm2_16; lia).
              rw_if_neg ltac:(clear - Hm2_16; lia).
              replace (m2 + 2 - 4) with (m2 - 2) in Hch by (clear; lia).
              exact Hch.
      * cbv iota in Hc.
        rewrite Hz0_eq, !Nat.add_0_r in Hc.
        apply andb_true_iff in Hc as [Hc _]; apply andb_true_iff in Hc as [Hc Hc_1]; apply andb_true_iff in Hc as [Hc_base Hc_9].
        assert (Hck_8_15 : 8 <= c /\ 15 <= k).
        { clear - Hc_base. destruct ds as [|d ?]; [| destruct (3 <=? d)]; lia. }
        destruct Hck_8_15 as [Hc8 Hk15].
        assert (Hc_le : k <= 2 * c + 3) by (clear - Hck; lia).
        pose proof (Hch 1) as Hf1.
        cbn [invChain] in Hf1; rewrite Ek, Eb1, Eb2 in Hf1.
        Local Transparent checkChainAux.
        cbn [checkChainAux] in Hf1.
        Local Opaque checkChainAux.
        rewrite Hz0_eq, Hdz0_eq, !Nat.add_0_r in Hf1.
        cbn [isHeadP5 drop1L negb andb] in Hf1.
        apply unpack_if_negb_false in Hf1 as [Hphiw_f Hf1].
        rw_if_neg_in Hf1 ltac:(clear; lia).
        apply unpack_if_negb_false in Hf1 as [Hgp _].
        assert (Hds1' : checkDs1Phi1 (ModeB_ge3 (p3z m2 :: p5 :: suf) k c ds) = true).
        { cbn [checkDs1Phi1]. destruct (nat_list_eqb ds [1]); cbn [negb]; [| reflexivity].
          rewrite Ek. replace (c =? 2) with false by (clear - Hc8; lia); reflexivity. }
        split.
        -- cbn [invCore].
           apply if_false_true; [rewrite Hgd, Hds2', Hds1'; reflexivity |].
           rewrite Ek.
           rw_if_neg ltac:(clear - Hc8; lia).
           fold nls.
           apply if_negb_false_true; [exact Heven_nls |].
           assert (Hrst_f : ((k =? 1) && (c =? 1) && nat_list_eqb ds []) = false) by (replace (c =? 1) with false by (clear - Hc8; lia); rewrite !andb_false_r; reflexivity).
           apply if_negb_false_true.
           { rw_if_pos ltac:(clear - Hc8; lia). rewrite Hrst_f; cbn [negb].
             rewrite Hphiw_f, orb_true_r; reflexivity. }
           rewrite Hmd_nls.
           apply if_false_true; [clear - Hc_le; lia |].
           rw_if_pos ltac:(clear - Hc_le; lia).
           rewrite Hrst_f, Hgp; cbn [hasP5 negb orb andb].
           assert (Hds1_ok : negb (nat_list_eqb ds [1] && (24 <=? c - 1)) || (37 <=? k) = true)
             by (destruct (nat_list_eqb ds [1]); [cbn [negb orb] in Hc_1; rewrite Hc_1, orb_true_r; reflexivity | reflexivity]).
           assert (Hds0_ok : negb ((nat_list_eqb ds [] || nat_list_eqb ds [0]) && (8 <=? c - 1)) || (17 <=? k) = true)
             by (destruct (nat_list_eqb ds [] || nat_list_eqb ds [0]); cbn [andb orb negb] in *;
                 [destruct (9 <=? c) eqn:Ec9; cbn [andb orb negb] in Hc_9;
                  [rewrite Hc_9, orb_true_r; reflexivity | replace (8 <=? c - 1) with false by (clear - Ec9; lia); reflexivity]
                 | reflexivity]).
           rewrite andb_true_r, Hds1_ok, Hds0_ok; clear - Hc8 Hk15; lia.
        -- intros [|fuel'].
           ++ cbn [invChain]. rewrite Ek.
              rw_if_neg ltac:(clear - Hc8; lia).
              rw_if_neg ltac:(clear - Hc8; lia); reflexivity.
           ++ specialize (Hch (S fuel')).
              cbn [invChain] in Hch |- *; rewrite Ek in Hch |- *.
              rewrite Eb1, Eb2 in Hch.
              rw_if_neg ltac:(clear - Hc8; lia).
              rw_if_neg ltac:(clear - Hc8; lia).
              Local Transparent checkChainAux.
              cbn [checkChainAux] in Hch |- *.
              Local Opaque checkChainAux.
              rewrite Hz0_eq, Hdz0_eq, !Nat.add_0_r in Hch.
              cbn [isHeadP5 drop1L negb andb] in Hch.
              rewrite Hphiw_f, Hgp in Hch; cbn [negb andb] in Hch.
              rw_if_neg_in Hch ltac:(clear; lia).
              fold nls.
              assert (Hodd_k : hasOdd nls = true) by (cbn [nls hasOdd]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
              assert (Hepsum_k : epSum nls = k - 1) by (cbn [nls epSum]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
              assert (Hep_k : ep nls = 0) by (cbn [nls ep]; rw_if_pos ltac:(clear - Hm1; lia); reflexivity).
              rewrite Hodd_k, Hepsum_k, Hep_k, Hmd_nls; cbn [nls hasP5 preP5Val p5Suf andb negb].
              rw_if_pos ltac:(clear - Hc_le; lia).
              rewrite !Nat.mul_0_r, !Nat.add_0_l, !Nat.add_0_r.
              replace (k - 1 + 5) with (k + 4) by (clear - Hk15; lia).
              replace (k - 1 + 3) with (k + 2) by (clear - Hk15; lia).
              replace (k - 1 + 2) with (k + 1) by (clear - Hk15; lia).
              replace (m2 + 2 - 4) with (m2 - 2) in Hch by (clear; lia).
              replace (m2 + 2 + 1) with (m2 + 3) in Hch by (clear; lia).
              replace (m2 + 2 - 1) with (m2 + 1) in Hch by (clear; lia).
              replace ((m2 mod 2 =? 0) && (m2 <=? 2 * (k - 1) + 10))
                with (((m2 + 2) mod 2 =? 0) && (m2 + 2 <=? 2 * k + 10)) by (clear - Hk15; lia).
              replace ((m2 mod 2 =? 1) && (m2 <=? 2 * (k - 1) + 11))
                with (((m2 + 2) mod 2 =? 1) && (m2 + 2 <=? 2 * k + 11)) by (clear - Hk15; lia).
              exact Hch.
Qed.

Lemma isOddDrainDs_cons_imp {d : nat} {ds : list nat} :
  isOddDrainDs (d :: ds) = true -> (ds = [] \/ ds = [0]) /\ 9 <= d.
Proof.
  destruct ds as [|[|?] [|? ?]]; intro H; try discriminate.
  - unfold isOddDrainDs, isOddDrain1 in H. split; [left; reflexivity | clear - H; lia].
  - unfold isOddDrainDs, isOddDrain1 in H. split; [right; reflexivity | clear - H; lia].
Qed.

Lemma GoodPhiW_push_ge8 (phiW c : nat) (ds : list nat) :
  7 <= c -> 15 <= phiW ->
  (ds = [1] -> 24 <= c -> 35 <= phiW) ->
  (ds = [] \/ ds = [0] -> 8 <= c -> 17 <= phiW) ->
  GoodPhiW phiW ((c + 1) :: ds) false = true.
Proof.
  intros Hc H15 Hd25 Hod. unfold GoodPhiW; cbn [nat_list_eqb].
  replace (c + 1 =? 2) with false by (clear - Hc; lia).
  replace (c + 1 =? 0) with false by (clear - Hc; lia).
  replace (c + 1 =? 1) with false by (clear - Hc; lia).
  cbn [andb].
  destruct (isDGe25One ((c + 1) :: ds)) eqn:E25.
  - destruct ds as [|[|[|?]] [|? ?]]; try discriminate.
    cbn [isDGe25One] in E25. pose proof (Hd25 eq_refl ltac:(clear - E25; lia)); clear - H; lia.
  - destruct (isOddDrainDs ((c + 1) :: ds)) eqn:Eod.
    + destruct (isOddDrainDs_cons_imp Eod) as [Hds Hc9].
      pose proof (Hod Hds ltac:(clear - Hc9; lia)); clear - H; lia.
    + clear - H15; lia.
Qed.

Lemma GoodPhiW_c_pos {c : nat} {ds : list nat} :
  ds <> [2] -> GoodPhiW c ds false = true -> 1 <= c.
Proof.
  intros Hne2 H. destruct c as [|c']; [| clear; lia].
  unfold GoodPhiW in H.
  replace (nat_list_eqb ds [2]) with false in H
    by (destruct (nat_list_eqb ds [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]).
  destruct (nat_list_eqb ds [0]); [discriminate |].
  destruct (nat_list_eqb ds [1]); [discriminate |].
  destruct (nat_list_eqb ds []); [discriminate |].
  destruct (isDGe25One ds); [discriminate |].
  destruct (isOddDrainDs ds); discriminate.
Qed.

Lemma GoodPhiW_nil_ge6 {c : nat} : GoodPhiW c [] false = true -> 6 <= c.
Proof.
  cbn [GoodPhiW nat_list_eqb orb]; intro H; clear - H; lia.
Qed.

Lemma ValidAfterOdd_cases {ls' : list LTok} :
  ValidAfterOdd ls' = true ->
  ls' = [] \/
  (exists suf, ls' = p5 :: suf /\ 18 <= z0 suf /\ ValidP5Chain suf = true) \/
  (exists m suf, ls' = p3z m :: p5 :: suf /\ 18 <= z0 suf /\ ValidP5Chain suf = true).
Proof.
  destruct ls' as [|[m | ] rest]; intro H.
  - left; reflexivity.
  - destruct rest as [|[|] suf]; try discriminate.
    cbn [ValidAfterOdd] in H; apply andb_true_iff in H as [H1 H2].
    right; right; exists m, suf; repeat split; [clear - H1; lia | exact H2].
  - cbn [ValidAfterOdd] in H; apply andb_true_iff in H as [H1 H2].
    right; left; exists rest; repeat split; [clear - H1; lia | exact H2].
Qed.

Lemma epSum_p3z_p5_ge14 {m2 : nat} {suf : list LTok} :
  14 <= m2 -> 14 <= epSum (p3z m2 :: p5 :: suf).
Proof.
  intro Hm. cbn [epSum]. destruct (m2 mod 2 =? 1) eqn:E; clear - Hm E; lia.
Qed.

Lemma step_Inv_ModeE_ge2_p3z1_odd (ls' : list LTok) (k c : nat) (ds : list nat) :
  k mod 2 <> 0 ->
  Inv (ModeE_ge2 (p3z 1 :: ls') k c ds) ->
  Inv (nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)).
Proof.
  intros Hk [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [_ Hc].
  rw_if_neg_in Hc ltac:(clear - Hk; lia).
  apply unpack_if_negb_false in Hc as [Hvp5_0 Hc].
  destruct (ValidP5Chain_p3z_succ (m := 0) Hvp5_0) as [suf [-> [Hz18 Hvp5]]].
  apply unpack_if_negb_false in Hc as [Hck Hc].
  cbn [headP3zVal z0 dropZ0 andb Nat.add Nat.mul] in Hc.
  rewrite !andb_false_r, !Nat.add_0_r in Hc; cbn [andb] in Hc.
  apply andb_true_iff in Hc as [Hc _]; apply andb_true_iff in Hc as [Hc _]; apply andb_true_iff in Hc as [Hc_base _].
  assert (Hck_8_15 : 8 <= c /\ 15 <= k).
  { clear - Hc_base. destruct ds as [|d ?]; [| destruct (3 <=? d)]; lia. }
  destruct Hck_8_15 as [Hc8 Hk15].
  pose proof (Hch 1) as Hf1.
  cbn [invChain] in Hf1. rw_if_neg_in Hf1 ltac:(clear - Hk; lia).
  cbn [headP3zVal z0 dropZ0 andb] in Hf1; rewrite !andb_false_r in Hf1; cbn [andb] in Hf1.
  Local Transparent checkChainAux.
  cbn [checkChainAux z0 dropZ0 isHeadP5 drop1L Nat.eqb Nat.add Nat.mul negb andb] in Hf1.
  Local Opaque checkChainAux.
  rewrite !Nat.add_0_r in Hf1.
  apply unpack_if_negb_false in Hf1 as [_ Hf1].
  apply andb_true_iff in Hf1 as [Hgd' _]; unfold GoodPsi in Hgd'.
  cbn [nextModeE_p3z1]; replace (k + 2 + 2) with (k + 4) by (clear; lia).
  assert (Hds2' : checkDs2 (ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true)
    by (cbn [checkDs2 nat_list_eqb]; replace (c + 1 =? 2) with false by (clear - Hc8; lia); reflexivity).
  assert (Hds1' : checkDs1Phi1 (ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true)
    by (cbn [checkDs1Phi1 nat_list_eqb]; replace (c + 1 =? 1) with false by (clear - Hc8; lia); reflexivity).
  split.
  - cbn [invCore].
    apply if_false_true; [rewrite Hgd', Hds2', Hds1'; reflexivity |].
    change (1 mod 2 =? 0) with false; cbn [andb orb negb].
    apply if_negb_false_true; [exact Hvp5 |].
    apply if_negb_false_true; [clear; lia |].
    cbn [nat_list_eqb andb].
    assert (Hbase : (if 3 <=? c + 1
      then (20 <=? k + 4 + z0 suf) && (15 <=? 1 + 2 * z0 suf)
      else (8 <=? k + 4 + z0 suf) && (15 <=? 1 + 2 * z0 suf)) = true)
      by (destruct (3 <=? c + 1); clear - Hz18 Hk15; lia).
    rewrite Hbase.
    replace (17 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
    replace (37 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
    rewrite !orb_true_r; cbn [andb].
    apply d25_check_of_ge36; intros _ _ _; clear - Hz18 Hk15; lia.
  - intro fuel. specialize (Hch (S fuel)).
    cbn [invChain] in Hch |- *.
    rw_if_neg_in Hch ltac:(clear - Hk; lia).
    cbn [headP3zVal z0 dropZ0 andb] in Hch; rewrite !andb_false_r in Hch; cbn [andb] in Hch.
    cbn [nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb].
    Local Transparent checkChainAux.
    cbn [checkChainAux z0 dropZ0 isHeadP5 drop1L Nat.eqb Nat.add Nat.mul negb andb] in Hch.
    Local Opaque checkChainAux.
    rewrite !Nat.add_0_r in Hch.
    apply unpack_if_negb_false in Hch as [_ Hch].
    apply andb_true_iff in Hch as [_ Hch]; exact Hch.
Qed.

Lemma step_Inv_ModeE_ge2_p3z1_reset (ls' : list LTok) :
  Inv (ModeE_ge2 (p3z 1 :: ls') 0 0 []) ->
  Inv (nextModeE_p3z1 ls' 2 [1]).
Proof.
  intros [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [_ Hc].
  change (0 mod 2 =? 0) with true in Hc; cbn [andb orb negb] in Hc.
  apply unpack_if_negb_false in Hc as [Heven Hc].
  cbn [ValidEvenLs Nat.modulo Nat.divmod Nat.sub snd Nat.eqb] in Heven.
  apply unpack_if_negb_false in Hc as [_ Hc].
  apply unpack_if_negb_false in Hc as [_ Hc].
  apply unpack_if_false in Hc as [_ Hc].
  apply unpack_if_negb_false in Hc as [Hok_rst _].
  cbn [isHeadP3z1 drop1L nat_list_eqb Nat.eqb andb] in Hok_rst.
  destruct (ValidAfterOdd_cases Heven) as [-> | [[suf [-> _]] | [m [suf [-> [Hz18 Hvp5]]]]]].
  - (* ls' = [] *)
    split.
    + reflexivity.
    + intro fuel. specialize (Hch fuel).
      cbn [invChain nextModeE_p3z1 isHeadP3z1 drop1L nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb] in Hch |- *.
      exact Hch.
  - discriminate.
  - destruct m as [|[|m2]].
    + discriminate.
    + (* m = 1 *)
      cbn [nextModeE_p3z1]; change (0 + 2) with 2; change (2 + 1) with 3.
      split.
      * cbn [invCore GoodDs GoodDsAux GoodDs2 checkDs2 checkDs1Phi1 nat_list_eqb isDGe25One isOddDrainDs Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
        rewrite Hvp5; cbn [negb andb]; cbv iota.
        apply if_negb_false_true; [reflexivity |].
        change (3 <=? 3) with true; change (25 <=? 3) with false; cbn [negb orb andb]; cbv iota.
        replace (20 <=? 2 + z0 suf) with true by (clear - Hz18; lia).
        replace (15 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
        replace (17 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
        replace (37 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
        rewrite ?orb_true_r; reflexivity.
      * intro fuel. specialize (Hch fuel).
        cbn [invChain isHeadP3z1 drop1L headP3zVal drop2L checkResetSufAux nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb] in Hch |- *.
        exact Hch.
    + (* m = S (S m2) *)
      cbn [nextModeE_p3z1].
      assert (Heven_m2 : ValidEvenLs (p3z m2 :: p5 :: suf) = true)
        by (cbn [ValidEvenLs ValidAfterOdd]; destruct (m2 mod 2 =? 0); rewrite Hvp5; clear - Hz18; lia).
      assert (Hepw0 : epW (p3z m2 :: p5 :: suf) = 0)
        by (cbn [epW]; destruct (m2 mod 2 =? 1); reflexivity).
      assert (Hpref0 : prefSumW (p3z m2 :: p5 :: suf) = 0)
        by (cbn [prefSumW]; destruct (m2 mod 2 =? 1); reflexivity).
      assert (Hmd0 : MustDrain (p3z m2 :: p5 :: suf) = false)
        by (cbn [MustDrain]; destruct (m2 mod 2 =? 1); reflexivity).
      assert (Hds1' : checkDs1Phi1 (ModeE_ge2 (p3z m2 :: p5 :: suf) 0 2 [1]) = true)
        by (cbn [checkDs1Phi1 isHeadP5 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb negb andb]; rewrite Hepw0; reflexivity).
      split.
      * cbn [invCore GoodDs GoodDsAux checkDs2 nat_list_eqb isHeadP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
        unfold GoodDs1; rewrite Hds1', Heven_m2, Hpref0, Hepw0, Hmd0; cbn [GoodPhiW nat_list_eqb Nat.eqb Nat.add Nat.mul andb orb negb].
        change (1 <=? 2) with true; change (8 <=? 1) with false; change (0 <=? 8) with true; change (0 <=? 10) with true; cbn [negb orb andb]; cbv iota.
        destruct (hasOdd (p3z m2 :: p5 :: suf) && (epSum (p3z m2 :: p5 :: suf) <=? 8)) eqn:Econd; [| reflexivity].
        assert (Hm2_odd : m2 mod 2 = 1)
          by (cbn [hasOdd] in Econd; destruct (m2 mod 2 =? 1) eqn:Em; [clear - Em; lia | discriminate]).
        assert (Hep0 : ep (p3z m2 :: p5 :: suf) = 0)
          by (cbn [ep]; rw_if_pos ltac:(clear - Hm2_odd; lia); reflexivity).
        rewrite Hep0; reflexivity.
      * intro fuel. specialize (Hch fuel).
        cbn [invChain isHeadP3z1 drop1L headP3zVal drop2L checkResetSufAux nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add Nat.mul andb] in Hch |- *.
        rewrite Nat.sub_0_r in Hch.
        exact Hch.
Qed.

Lemma step_Inv_ModeE_ge2_p3z1_even_nonreset (ls' : list LTok) (k c : nat) (ds : list nat) :
  k mod 2 = 0 ->
  ~ (k = 0 /\ c = 0 /\ ds = []) ->
  Inv (ModeE_ge2 (p3z 1 :: ls') k c ds) ->
  Inv (nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)).
Proof.
  intros Hk Hrst [Hc Hch]. cbn [invCore] in Hc.
  apply unpack_if_false in Hc as [Hg Hc].
  assert (Hds2 : checkDs2 (ModeE_ge2 (p3z 1 :: ls') k c ds) = true)
    by (destruct (checkDs2 (ModeE_ge2 (p3z 1 :: ls') k c ds)); cbn [negb orb] in Hg; [reflexivity | rewrite orb_true_r in Hg; discriminate]).
  rw_if_pos_in Hc ltac:(clear - Hk; lia).
  apply unpack_if_negb_false in Hc as [Heven Hc].
  cbn [ValidEvenLs Nat.modulo Nat.divmod Nat.sub snd Nat.eqb] in Heven.
  apply unpack_if_negb_false in Hc as [Hk_le Hc].
  cbn [prefSumW Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add] in Hk_le.
  assert (Hk_le1 : k <= 2 * c + 4) by (clear - Hk_le; lia).
  assert (Hne2 : ds <> [2]).
  { apply (ds_ne_two_of_checkDs2_ModeE_ge2 Hds2).
    right; right; right; right. cbn [epSum Nat.modulo Nat.divmod Nat.sub snd Nat.eqb]; clear - Hk_le1; lia. }
  apply unpack_if_negb_false in Hc as [Hok_phi Hc].
  apply unpack_if_false in Hc as [_ Hc].
  assert (Hrst_f : ((k =? 0) && (c =? 0) && nat_list_eqb ds []) = false).
  { destruct ((k =? 0) && (c =? 0) && nat_list_eqb ds []) eqn:Er; [| reflexivity].
    apply andb_true_iff in Er as [Er Eds0]; apply andb_true_iff in Er as [Ek0 Ec0].
    exfalso; apply Hrst. repeat split; [clear - Ek0; lia | clear - Ec0; lia | exact (proj1 (nat_list_eqb_true _ _) Eds0)]. }
  rewrite Hrst_f in Hc; cbn [andb negb] in Hc; cbv iota in Hc; cbn [andb negb] in Hc; cbv iota in Hc.
  change (hasOdd (p3z 1 :: ls')) with true in Hc.
  change (epSum (p3z 1 :: ls')) with 0 in Hc.
  change (ep (p3z 1 :: ls')) with 0 in Hc.
  rewrite !Nat.add_0_r, andb_true_l in Hc.
  rw_if_pos_in Hc ltac:(clear - Hk_le1; lia).
  apply andb_true_iff in Hc as [Hc_l Hc]; apply andb_true_iff in Hc_l as [Hc_l Hc_od]; apply andb_true_iff in Hc_l as [Hgp_c Hc_d1].
  assert (Hgd' : GoodDs ((c + 1) :: ds) = true) by exact Hgp_c.
  assert (Hd25_imp : ds = [1] -> 24 <= c -> 36 <= k).
  { intros -> Hc24. cbn [nat_list_eqb Nat.eqb andb] in Hc_d1. clear - Hc_d1 Hc24; lia. }
  destruct (ValidAfterOdd_cases Heven) as [-> | [[suf [-> [Hz18 Hvp5]]] | [m [suf [-> [Hz18 Hvp5]]]]]].
  - (* ls' = [] *)
    cbn [nextModeE_p3z1].
    cbn [MustDrain hasP5 preP5Val p5Suf z0 negb andb orb] in Hc; change (16 <=? 0) with false in Hc; change (38 <=? 0) with false in Hc; repeat (rewrite ?andb_false_l, ?andb_false_r, ?orb_false_l, ?orb_false_r in Hc).
    assert (Hc7_k14 : 14 <= k /\ 7 <= c) by (clear - Hc; lia).
    destruct Hc7_k14 as [Hk14 Hc7].
    assert (Hod_imp : ds = [] \/ ds = [0] -> 8 <= c -> 16 <= k).
    { intros [-> | ->] Hc8; cbn [nat_list_eqb MustDrain hasP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb] in Hc_od; clear - Hc_od Hc8; lia. }
    pose proof (GoodPhiW_push_ge8 (k + 2) c ds Hc7 ltac:(clear - Hk14; lia)
      (fun h1 hc24 => ltac:(pose proof (Hd25_imp h1 hc24); clear - H; lia))
      (fun h0 hc8 => ltac:(pose proof (Hod_imp h0 hc8); clear - H; lia))) as Hphiw'.
    assert (Hds2' : checkDs2 (ModeE_ge2 [] 0 (k + 2) ((c + 1) :: ds)) = true)
      by (cbn [checkDs2 nat_list_eqb]; replace (c + 1 =? 2) with false by (clear - Hc7; lia); reflexivity).
    assert (Hds1' : checkDs1Phi1 (ModeE_ge2 [] 0 (k + 2) ((c + 1) :: ds)) = true)
      by (cbn [checkDs1Phi1 nat_list_eqb]; replace (c + 1 =? 1) with false by (clear - Hc7; lia); reflexivity).
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd', Hds2', Hds1'; reflexivity |].
      cbn [ValidEvenLs prefSumW isHeadP5 epW isHeadP3z1 MustDrain hasOdd nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add andb orb negb].
      repeat match goal with |- context [0 <=? ?x] => change (0 <=? x) with true end; cbn [negb orb andb]; cbv iota.
      rewrite ?Nat.add_0_r, Hphiw'; rewrite ?andb_false_r; reflexivity.
    + intro fuel. specialize (Hch (S fuel)).
      cbn [invChain] in Hch |- *.
      rw_if_pos_in Hch ltac:(clear - Hk; lia).
      rewrite Hrst_f in Hch; cbn [andb isHeadP3z1 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb] in Hch |- *.
      rewrite andb_false_r.
      Local Transparent checkChainAux.
      cbn [checkChainAux hasOdd epSum ep MustDrain hasP5 isHeadP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add negb andb] in Hch.
      Local Opaque checkChainAux.
      rewrite !Nat.mul_0_r, !Nat.add_0_r in Hch.
      rw_if_pos_in Hch ltac:(clear - Hk_le1; lia).
      replace (k + 2 + 1) with (k + 3) by (clear; lia).
      exact Hch.
  - (* ls' = p5 :: suf *)
    cbn [nextModeE_p3z1]; replace (k + 2 + 2) with (k + 4) by (clear; lia).
    cbn [isHeadP5 isHeadP3z1 MustDrain epW Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add negb] in Hok_phi.
    rewrite Hrst_f, !andb_false_r, orb_false_l in Hok_phi.
    pose proof (GoodPhiW_c_pos Hne2 Hok_phi) as Hc_pos.
    assert (Hne2' : (c + 1) :: ds <> [2]).
    { intro Heq; injection Heq as Hc1 ->.
      pose proof (GoodPhiW_nil_ge6 Hok_phi); clear - Hc1 H; lia. }
    assert (Hds2' : checkDs2 (ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true).
    { cbn [checkDs2]. destruct (nat_list_eqb ((c + 1) :: ds) [2]) eqn:E; [apply nat_list_eqb_true in E; contradiction | reflexivity]. }
    assert (Hds1' : checkDs1Phi1 (ModeE_ge2 suf 1 (k + 4) ((c + 1) :: ds)) = true)
      by (cbn [checkDs1Phi1 nat_list_eqb]; replace (c + 1 =? 1) with false by (clear - Hc_pos; lia); reflexivity).
    split.
    + cbn [invCore].
      apply if_false_true; [rewrite Hgd', Hds2', Hds1'; reflexivity |].
      cbn [nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb].
      apply if_negb_false_true; [exact Hvp5 |].
      apply if_negb_false_true; [clear; lia |].
      assert (Hbase : (if 3 <=? c + 1
        then (20 <=? k + 4 + z0 suf) && (15 <=? 1 + 2 * z0 suf)
        else (8 <=? k + 4 + z0 suf) && (15 <=? 1 + 2 * z0 suf)) = true)
        by (destruct (3 <=? c + 1); clear - Hz18; lia).
      rewrite Hbase.
      replace (17 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
      replace (37 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
      rewrite ?orb_true_r; cbn [andb].
      apply d25_check_of_ge36.
      intros d Hd_eq Hd25. injection Hd_eq as <- Hds_eq.
      pose proof (Hd25_imp Hds_eq ltac:(clear - Hd25; lia)); clear - H; lia.
    + intro fuel. specialize (Hch (S fuel)).
      cbn [invChain] in Hch |- *.
      rw_if_pos_in Hch ltac:(clear - Hk; lia).
      rewrite Hrst_f in Hch; cbn [andb nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb] in Hch |- *.
      Local Transparent checkChainAux.
      cbn [checkChainAux hasOdd epSum ep MustDrain hasP5 p5Suf isHeadP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add negb andb] in Hch.
      Local Opaque checkChainAux.
      rewrite !Nat.mul_0_r, !Nat.add_0_r in Hch.
      rw_if_pos_in Hch ltac:(clear - Hk_le1; lia).
      apply andb_true_iff in Hch as [_ Hch]; exact Hch.
  - (* ls' = p3z m :: p5 :: suf *)
    cbn [MustDrain hasP5 preP5Val p5Suf Nat.modulo Nat.divmod Nat.sub snd Nat.eqb negb orb] in Hc.
    assert (Hod_imp : ds = [] \/ ds = [0] -> 8 <= c -> 16 <= k).
    { intros [-> | ->] Hc8; cbn [nat_list_eqb MustDrain hasP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb] in Hc_od; clear - Hc_od Hc8; lia. }
    assert (Hch_unfold : forall fuel',
      checkChainAux (S fuel') true (p3z 1 :: p3z m :: p5 :: suf) (c + 1) k (2 * c + 4) ds =
      (if (m mod 2 =? 0) && (m <=? 2 * k + 10) then
         checkChainAux fuel' false suf (k + 5) (m + 3) 0 ((c + 1) :: ds)
       else if (m mod 2 =? 1) && (m <=? 2 * k + 11) then
         GoodDs ((k + 3) :: (c + 1) :: ds) && checkChainAux fuel' false suf (m + 1) 1 0 ((k + 3) :: (c + 1) :: ds)
       else
         checkChainAux fuel' true (p3z (m - 2) :: p5 :: suf) (k + 3) 0 (2 * (k + 2) + 4) ((c + 1) :: ds))).
    { intro fuel'.
      Local Transparent checkChainAux.
      cbn [checkChainAux hasOdd epSum ep MustDrain hasP5 preP5Val p5Suf isHeadP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add negb andb].
      Local Opaque checkChainAux.
      rewrite !Nat.mul_0_r, !Nat.add_0_r.
      rw_if_pos ltac:(clear - Hk_le1; lia).
      reflexivity. }
    destruct m as [|[|m2]].
    + (* m = 0 *)
      cbn [nextModeE_p3z1]; replace (k + 2 + 1) with (k + 3) by (clear; lia).
      change (16 <=? 0) with false in Hc; repeat (rewrite ?andb_false_l, ?andb_false_r, ?orb_false_l, ?orb_false_r in Hc).
      assert (Hc7_k14 : 14 <= k /\ 7 <= c) by (clear - Hc; lia).
      destruct Hc7_k14 as [Hk14 Hc7].
      pose proof (GoodPhiW_push_ge8 (k + 2) c ds Hc7 ltac:(clear - Hk14; lia)
        (fun h1 hc24 => ltac:(pose proof (Hd25_imp h1 hc24); clear - H; lia))
        (fun h0 hc8 => ltac:(pose proof (Hod_imp h0 hc8); clear - H; lia))) as Hphiw'.
      assert (Hds2' : checkDs2 (ModeE_ge2 (p5 :: suf) 0 (k + 3) ((c + 1) :: ds)) = true)
        by (cbn [checkDs2 nat_list_eqb]; replace (c + 1 =? 2) with false by (clear - Hc7; lia); reflexivity).
      assert (Hds1' : checkDs1Phi1 (ModeE_ge2 (p5 :: suf) 0 (k + 3) ((c + 1) :: ds)) = true)
        by (cbn [checkDs1Phi1 nat_list_eqb]; replace (c + 1 =? 1) with false by (clear - Hc7; lia); reflexivity).
      assert (Heven_p5 : ValidEvenLs (p5 :: suf) = true)
        by (cbn [ValidEvenLs]; rewrite Hvp5; clear - Hz18; lia).
      split.
      * cbn [invCore].
        apply if_false_true; [rewrite Hgd', Hds2', Hds1'; reflexivity |].
        cbn [prefSumW isHeadP5 isHeadP3z1 MustDrain hasOdd nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.add andb orb negb].
        rewrite Heven_p5; repeat match goal with |- context [0 <=? ?x] => change (0 <=? x) with true end; cbn [negb orb andb]; cbv iota.
        replace (k + 3 - 1) with (k + 2) by (clear; lia).
        replace (1 <=? k + 3) with true by (clear; lia).
        rewrite ?Nat.add_0_r, Hphiw'; rewrite ?andb_false_r; reflexivity.
      * intros [|fuel'].
        -- Local Transparent checkChainAux.
           cbn [invChain checkChainAux isHeadP3z1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb].
           Local Opaque checkChainAux.
           rewrite !andb_false_r; reflexivity.
        -- specialize (Hch (S fuel')).
           cbn [invChain] in Hch |- *.
           rw_if_pos_in Hch ltac:(clear - Hk; lia).
           rewrite Hrst_f in Hch; cbn [andb isHeadP3z1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb] in Hch |- *.
           rewrite !andb_false_r.
           rewrite (Hch_unfold fuel') in Hch.
           cbn [Nat.modulo Nat.divmod Nat.sub snd Nat.eqb Nat.leb Nat.add andb] in Hch.
           Local Transparent checkChainAux.
           cbn [checkChainAux hasOdd hasP5 isHeadP5 p5Suf ep epSum Nat.add andb orb negb].
           Local Opaque checkChainAux.
           rewrite !Nat.mul_0_r, !Nat.add_0_r.
           replace (k + 3 + 1 + 1) with (k + 5) by (clear; lia).
           exact Hch.
    + (* m = 1 *)
      cbn [nextModeE_p3z1]; change (0 + 2) with 2.
      change (16 <=? 1) with false in Hc; repeat (rewrite ?andb_false_l, ?andb_false_r, ?orb_false_l, ?orb_false_r in Hc).
      assert (Hc7_k14 : 14 <= k /\ 7 <= c) by (clear - Hc; lia).
      destruct Hc7_k14 as [Hk14 Hc7].
      pose proof (Hch 1) as Hf1.
      cbn [invChain] in Hf1; rw_if_pos_in Hf1 ltac:(clear - Hk; lia); rewrite Hrst_f in Hf1; cbn [andb isHeadP3z1] in Hf1.
      rewrite (Hch_unfold 0) in Hf1; rw_if_neg_in Hf1 ltac:(clear; lia); rw_if_pos_in Hf1 ltac:(clear; lia).
      apply andb_true_iff in Hf1 as [Hf1_gd _].
      assert (Hgd'' : GoodDs ((k + 2 + 1) :: (c + 1) :: ds) = true)
        by (replace (k + 2 + 1) with (k + 3) by (clear; lia); exact Hf1_gd).
      split.
      * cbn [invCore checkDs2 checkDs1Phi1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
        rewrite Hgd'', Hvp5, !andb_false_r; cbn [negb andb orb]; cbv iota.
        apply if_negb_false_true; [reflexivity |].
        assert (Hbase : (if 3 <=? k + 2 + 1
          then (20 <=? 2 + z0 suf) && (15 <=? 1 + 2 * z0 suf)
          else (8 <=? 2 + z0 suf) && (15 <=? 1 + 2 * z0 suf)) = true)
          by (destruct (3 <=? k + 2 + 1); clear - Hz18; lia).
        rewrite Hbase.
        replace (17 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
        replace (37 <=? 1 + 2 * z0 suf) with true by (clear - Hz18; lia).
        rewrite ?orb_true_r; cbn [andb].
        apply d25_check_of_ge36.
        intros d Hd_eq _. injection Hd_eq as _ Hc1_eq; clear - Hc7 Hc1_eq; lia.
      * intro fuel. specialize (Hch (S fuel)).
        cbn [invChain] in Hch |- *.
        rw_if_pos_in Hch ltac:(clear - Hk; lia); rewrite Hrst_f in Hch; cbn [andb isHeadP3z1] in Hch.
        rewrite (Hch_unfold fuel) in Hch; rw_if_neg_in Hch ltac:(clear; lia); rw_if_pos_in Hch ltac:(clear; lia).
        cbn [nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb]; rewrite ?andb_false_r, ?andb_false_l; cbv iota.
        replace (k + 2 + 1) with (k + 3) by (clear; lia).
        apply andb_true_iff in Hch as [_ Hch]; exact Hch.
    + (* m = S (S m2) = m2 + 2 *)
      cbn [nextModeE_p3z1].
      replace (S (S m2)) with (m2 + 2) in * by (clear; lia).
      assert (Heven_m2 : ValidEvenLs (p3z m2 :: p5 :: suf) = true)
        by (cbn [ValidEvenLs ValidAfterOdd]; destruct (m2 mod 2 =? 0); rewrite Hvp5; clear - Hz18; lia).
      assert (Hpref0 : prefSumW (p3z m2 :: p5 :: suf) = 0)
        by (cbn [prefSumW]; destruct (m2 mod 2 =? 1); reflexivity).
      assert (Hepw0_m2 : epW (p3z m2 :: p5 :: suf) = 0)
        by (cbn [epW]; destruct (m2 mod 2 =? 1); reflexivity).
      assert (Hmd0_m2 : MustDrain (p3z m2 :: p5 :: suf) = false)
        by (cbn [MustDrain]; destruct (m2 mod 2 =? 1); reflexivity).
      assert (Hmd_or : (14 <= k /\ 7 <= c) \/ (ds = [] /\ c = 1 /\ k = 2 /\ 14 <= m2 /\ 38 <= z0 suf)).
      { destruct (nat_list_eqb ds [] && (c =? 1) && (k =? 2) && (16 <=? m2 + 2) && (38 <=? z0 suf)) eqn:Ep1.
        - right. destruct (nat_list_eqb ds []) eqn:Eds0; [| discriminate]. cbn [andb] in Ep1.
          repeat split; [exact (proj1 (nat_list_eqb_true _ _) Eds0) | clear - Ep1; lia | clear - Ep1; lia | clear - Ep1; lia | clear - Ep1; lia].
        - left; rewrite ?orb_false_r in Hc; clear - Hc; lia. }
      destruct Hmd_or as [[Hk14 Hc7] | [-> [-> [-> [Hm2_14 Hz38]]]]].
      * (* 14 <= k /\ 7 <= c *)
        pose proof (GoodPhiW_push_ge8 (k + 2) c ds Hc7 ltac:(clear - Hk14; lia)
          (fun h1 hc24 => ltac:(pose proof (Hd25_imp h1 hc24); clear - H; lia))
          (fun h0 hc8 => ltac:(pose proof (Hod_imp h0 hc8); clear - H; lia))) as Hphiw'.
        assert (Hds2' : checkDs2 (ModeE_ge2 (p3z m2 :: p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) = true)
          by (cbn [checkDs2 nat_list_eqb]; replace (c + 1 =? 2) with false by (clear - Hc7; lia); reflexivity).
        assert (Hds1' : checkDs1Phi1 (ModeE_ge2 (p3z m2 :: p5 :: suf) 0 (k + 2) ((c + 1) :: ds)) = true)
          by (cbn [checkDs1Phi1 nat_list_eqb]; replace (c + 1 =? 1) with false by (clear - Hc7; lia); reflexivity).
        split.
        -- cbn [invCore].
           apply if_false_true; [rewrite Hgd', Hds2', Hds1'; reflexivity |].
           change (0 mod 2 =? 0) with true; cbn [andb orb negb].
           apply if_negb_false_true; [exact Heven_m2 |].
           rewrite Hpref0; apply if_negb_false_true; [clear; lia |].
           apply if_negb_false_true.
           { cbn [isHeadP5 negb]; cbv iota; rewrite Hepw0_m2, Nat.add_0_r; rewrite GoodPhiW_mono by exact Hphiw'; rewrite ?orb_true_r; reflexivity. }
           rewrite Hmd0_m2, andb_false_l; cbv iota.
           cbn [nat_list_eqb isHeadP3z1 andb]; rewrite !andb_false_r, andb_false_l; cbv iota; cbn [negb Nat.add].
           destruct (hasOdd (p3z m2 :: p5 :: suf) && (epSum (p3z m2 :: p5 :: suf) <=? 2 * (k + 2) + 4)) eqn:Econd; [| reflexivity].
           assert (Hm2_odd : m2 mod 2 = 1)
             by (cbn [hasOdd] in Econd; destruct (m2 mod 2 =? 1) eqn:Em; [clear - Em; lia | discriminate]).
           assert (Hep0_m2 : ep (p3z m2 :: p5 :: suf) = 0)
             by (cbn [ep]; rw_if_pos ltac:(clear - Hm2_odd; lia); reflexivity).
           assert (Hepsum_m2 : epSum (p3z m2 :: p5 :: suf) = m2 - 1)
             by (cbn [epSum]; rw_if_pos ltac:(clear - Hm2_odd; lia); reflexivity).
           rewrite Hepsum_m2 in Econd.
           pose proof (Hch 1) as Hf1.
           cbn [invChain] in Hf1; rw_if_pos_in Hf1 ltac:(clear - Hk; lia); rewrite Hrst_f in Hf1; cbn [andb] in Hf1.
           rewrite (Hch_unfold 0) in Hf1.
           rw_if_neg_in Hf1 ltac:(clear - Hm2_odd; lia).
           rw_if_pos_in Hf1 ltac:(clear - Hm2_odd Econd; lia).
           apply andb_true_iff in Hf1 as [Hgp' _].
           rewrite Hep0_m2, !Nat.mul_0_r, !Nat.add_0_r, ?Hmd0_m2; unfold GoodPsi.
           replace (k + 2 + 1) with (k + 3) by (clear; lia); rewrite Hgp'.
           cbn [nat_list_eqb hasP5 negb orb andb].
           replace (c + 1 =? 1) with false by (clear - Hc7; lia).
           replace (c + 1 =? 0) with false by (clear - Hc7; lia).
           reflexivity.
        -- intro fuel.
           destruct (((m2 + 2) mod 2 =? 0) && (m2 + 2 <=? 2 * k + 10)) eqn:Ec1.
           ++ destruct fuel as [|fuel'].
              { Local Transparent checkChainAux.
                cbn [invChain checkChainAux isHeadP3z1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb].
                Local Opaque checkChainAux.
                rewrite !andb_false_r, ?andb_false_l; reflexivity. }
              specialize (Hch (S fuel')).
              cbn [invChain] in Hch |- *.
              rw_if_pos_in Hch ltac:(clear - Hk; lia); rewrite Hrst_f in Hch; cbn [andb isHeadP3z1] in Hch; cbv iota in Hch.
              cbn [isHeadP3z1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb]; rewrite !andb_false_r, ?andb_false_l; cbv iota.
              rewrite (Hch_unfold fuel') in Hch; cbv iota in Hch.
              assert (Hm2_ev : m2 mod 2 = 0) by (clear - Ec1; lia).
              Local Transparent checkChainAux.
              cbn [checkChainAux].
              Local Opaque checkChainAux.
              assert (Hodd_m2 : hasOdd (p3z m2 :: p5 :: suf) = false)
                by (cbn [hasOdd]; rw_if_neg ltac:(clear - Hm2_ev; lia); reflexivity).
              assert (Hepsum_m2 : epSum (p3z m2 :: p5 :: suf) = m2)
                by (cbn [epSum]; rw_if_neg ltac:(clear - Hm2_ev; lia); clear; lia).
              assert (Hep_m2 : ep (p3z m2 :: p5 :: suf) = 1)
                by (cbn [ep]; rw_if_neg ltac:(clear - Hm2_ev; lia); reflexivity).
              rewrite Hodd_m2, Hepsum_m2, Hep_m2; cbn [hasP5 isHeadP5 p5Suf Nat.add Nat.mul andb orb negb].
              rw_if_pos ltac:(clear - Ec1; lia).
              replace (k + 2 + 1 + 1 + 1) with (k + 5) by (clear; lia).
              replace (m2 + (1 + (1 + 0)) + 3) with (m2 + 2 + 3) by (clear; lia).
              exact Hch.
           ++ destruct (((m2 + 2) mod 2 =? 1) && (m2 + 2 <=? 2 * k + 11)) eqn:Ec2.
              ** destruct fuel as [|fuel'].
                 { Local Transparent checkChainAux.
                   cbn [invChain checkChainAux isHeadP3z1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb].
                   Local Opaque checkChainAux.
                   rewrite !andb_false_r, ?andb_false_l; reflexivity. }
                 specialize (Hch (S fuel')).
                 cbn [invChain] in Hch |- *.
                 rw_if_pos_in Hch ltac:(clear - Hk; lia); rewrite Hrst_f in Hch; cbn [andb isHeadP3z1] in Hch; cbv iota in Hch.
                 cbn [isHeadP3z1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb]; rewrite !andb_false_r, ?andb_false_l; cbv iota.
                 rewrite (Hch_unfold fuel') in Hch; cbv iota in Hch.
                 assert (Hm2_odd : m2 mod 2 = 1) by (clear - Ec2; lia).
                 Local Transparent checkChainAux.
                 cbn [checkChainAux].
                 Local Opaque checkChainAux.
                 assert (Hodd_m2 : hasOdd (p3z m2 :: p5 :: suf) = true)
                   by (cbn [hasOdd]; rw_if_pos ltac:(clear - Hm2_odd; lia); reflexivity).
                 assert (Hepsum_m2 : epSum (p3z m2 :: p5 :: suf) = m2 - 1)
                   by (cbn [epSum]; rw_if_pos ltac:(clear - Hm2_odd; lia); clear; lia).
                 assert (Hep_m2 : ep (p3z m2 :: p5 :: suf) = 0)
                   by (cbn [ep]; rw_if_pos ltac:(clear - Hm2_odd; lia); reflexivity).
                 rewrite Hodd_m2, Hepsum_m2, Hep_m2, Hmd0_m2; cbn [hasP5 p5Suf Nat.add Nat.mul andb orb negb].
                 rw_if_pos ltac:(clear - Ec2; lia).
                 rewrite !Nat.add_0_r.
                 replace (k + 2 + 1) with (k + 3) by (clear; lia).
                 replace (m2 - 1 + 4) with (m2 + 2 + 1) by (clear - Hm2_odd; lia).
                 exact Hch.
              ** specialize (Hch (S fuel)).
                 cbn [invChain] in Hch |- *.
                 rw_if_pos_in Hch ltac:(clear - Hk; lia); rewrite Hrst_f in Hch; cbn [andb isHeadP3z1] in Hch; cbv iota in Hch.
                 cbn [isHeadP3z1 nat_list_eqb Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb]; rewrite !andb_false_r, ?andb_false_l; cbv iota.
                 rewrite (Hch_unfold fuel) in Hch; cbv iota in Hch.
                 replace (m2 + 2 - 2) with m2 in Hch by (clear; lia).
                 replace (k + 2 + 1) with (k + 3) by (clear; lia).
                 exact Hch.
      * (* ds = [], c = 1, k = 2, 14 <= m2, 38 <= z0 suf *)
        change (2 + 2) with 4; change (1 + 1) with 2.
        pose proof (epSum_p3z_p5_ge14 (suf := suf) Hm2_14) as Hepsum_14.
        assert (Hds2' : checkDs2 (ModeE_ge2 (p3z m2 :: p5 :: suf) 0 4 [2]) = true).
        { cbn [checkDs2 nat_list_eqb isHeadP5 hasP5 p5Suf Nat.modulo Nat.divmod Nat.sub snd Nat.eqb negb andb].
          rewrite Hmd0_m2; cbn [negb andb Nat.add Nat.mul].
          clear - Hepsum_14 Hz38; lia. }
        split.
        -- cbn [invCore GoodDs GoodDsAux checkDs1Phi1 nat_list_eqb isHeadP5 Nat.modulo Nat.divmod Nat.sub snd Nat.eqb andb orb negb].
           unfold GoodDs1; rewrite Hds2', Heven_m2, Hpref0, Hepw0_m2, Hmd0_m2.
           cbn [GoodPhiW nat_list_eqb Nat.eqb Nat.add Nat.mul andb orb negb].
           change (2 <=? 2) with true; change (0 <=? 12) with true; change (0 <=? 14) with true; cbn [negb orb andb]; cbv iota.
           replace (epSum (p3z m2 :: p5 :: suf) <=? 12) with false by (clear - Hepsum_14; lia).
           rewrite andb_false_r; reflexivity.
        -- intro fuel. specialize (Hch (S fuel)).
           cbn [invChain isHeadP3z1 nat_list_eqb Nat.eqb andb] in Hch |- *.
           change (2 mod 2 =? 0) with true in Hch; change (0 mod 2 =? 0) with true.
           cbn [andb] in Hch |- *; cbv iota in Hch |- *.
           rewrite (Hch_unfold fuel) in Hch.
           rw_if_neg_in Hch ltac:(clear - Hm2_14; lia).
           rw_if_neg_in Hch ltac:(clear - Hm2_14; lia).
           cbn [Nat.add Nat.mul] in Hch |- *.
           replace (m2 + 2 - 2) with m2 in Hch by (clear; lia).
           exact Hch.
Qed.

Lemma step_Inv_ModeE_ge2_p3z1 (ls' : list LTok) (k c : nat) (ds : list nat) :
  Inv (ModeE_ge2 (p3z 1 :: ls') k c ds) ->
  Inv (nextModeE_p3z1 ls' (k + 2) ((c + 1) :: ds)).
Proof.
  destruct (k mod 2 =? 0) eqn:Ek; try cbv iota in Hc.
  - destruct ((k =? 0) && (c =? 0) && nat_list_eqb ds []) eqn:Erst.
    + assert (k = 0 /\ c = 0 /\ ds = []) as [-> [-> ->]].
      { destruct (nat_list_eqb ds []) eqn:Eds0; [rewrite andb_true_r in Erst | rewrite andb_false_r in Erst; discriminate].
        repeat split; [clear - Erst; lia | clear - Erst; lia | exact (proj1 (nat_list_eqb_true _ _) Eds0)]. }
      exact (step_Inv_ModeE_ge2_p3z1_reset ls').
    + apply step_Inv_ModeE_ge2_p3z1_even_nonreset.
      * clear - Ek; lia.
      * intros [-> [-> ->]]; discriminate.
  - apply step_Inv_ModeE_ge2_p3z1_odd. clear - Ek; lia.
Qed.

Lemma step_Inv_ModeE_ge2 (ls : list LTok) (k c : nat) (ds : list nat) :
  Inv (ModeE_ge2 ls k c ds) -> Inv (nextState (ModeE_ge2 ls k c ds)).
Proof.
  destruct ls as [|[m | ] ls'].
  - exact (step_Inv_ModeE_ge2_nil k c ds).
  - destruct m as [|[|m2]].
    + exact (step_Inv_ModeE_ge2_p3z0 ls' k c ds).
    + exact (step_Inv_ModeE_ge2_p3z1 ls' k c ds).
    + cbn [nextState]. replace (S (S m2)) with (m2 + 2) by (clear; lia).
      exact (step_Inv_ModeE_ge2_p3z_ge2 m2 ls' k c ds).
  - exact (step_Inv_ModeE_ge2_p5 ls' k c ds).
Qed.

Lemma step_Inv (s : State270) : Inv s -> Inv (nextState s).
Proof.
  destruct s as [ls k ds | ls k c ds | ls a c ds | ls m ds | ls a].
  - exact (step_Inv_ModeE_c1 ls k ds).
  - exact (step_Inv_ModeE_ge2 ls k c ds).
  - destruct c as [|c'].
    + exact (step_Inv_ModeB_ge3_c0 ls a ds).
    + exact (step_Inv_ModeB_ge3_cpos ls a c' ds).
  - exact (step_Inv_ModeB_b2 ls m ds).
  - exact (step_Inv_ModeB_blank ls a).
Qed.


#[local] Transparent checkChainAux.

(* ========================================================================== *)
(* Section 5g.1: Normalized Segment Representation & 1-Step Chain Equivalence *)
(* ========================================================================== *)

Record SegState := mkSeg {
  st_b : bool;
  st_segs : list (nat * nat);
  st_zl : nat;
  st_cp1 : nat;
  st_kb : nat;
  st_mrg : nat;
  st_ds : list nat
}.

Definition normSeg (z m : nat) : nat * nat :=
  if m =? 0 then (z + 1, 0) else (z, m).

Definition pushSeg (has_p5 : bool) (z_new m_rem : nat) (rest : list (nat * nat)) (zl : nat)
    : list (nat * nat) * nat :=
  if has_p5 then (normSeg z_new m_rem :: rest, zl) else ([], z_new).

Fixpoint encSegs (segs : list (nat * nat)) (zl : nat) : list LTok :=
  match segs with
  | [] => z0Rep zl []
  | (z, 0) :: rest => z0Rep z (p5 :: encSegs rest zl)
  | (z, S m') :: rest => z0Rep z (p3z (S m') :: p5 :: encSegs rest zl)
  end.

Lemma z0Rep_succ_right_sym (n : nat) (rest : list LTok) :
  z0Rep (n + 1) rest = z0Rep n (p3z 0 :: rest).
Proof.
  induction n as [|n IH]; [reflexivity |].
  cbn [Nat.add z0Rep]. rewrite IH. reflexivity.
Qed.

Lemma encSegs_normSeg (z m : nat) (rest : list (nat * nat)) (zl : nat) :
  encSegs (normSeg z m :: rest) zl = z0Rep z (p3z m :: p5 :: encSegs rest zl).
Proof.
  destruct m as [|m']; [cbn [normSeg Nat.eqb encSegs]; exact (z0Rep_succ_right_sym z (p5 :: encSegs rest zl)) | reflexivity].
Qed.

Lemma encSegs_pushSeg (hp : bool) (z_new m_rem : nat) (rest : list (nat * nat)) (zl : nat) :
  encSegs (fst (pushSeg hp z_new m_rem rest zl)) (snd (pushSeg hp z_new m_rem rest zl)) =
    z0Rep z_new (if hp then p3z m_rem :: p5 :: encSegs rest zl else []).
Proof.
  destruct hp; [exact (encSegs_normSeg z_new m_rem rest zl) | reflexivity].
Qed.

Lemma z0_z0Rep_of_zero {rest : list LTok} (H : z0 rest = 0) (n : nat) :
  z0 (z0Rep n rest) = n.
Proof. rewrite z0_z0Rep, H; lia. Qed.

Lemma dropZ0_z0Rep_of_nonz0 {rest : list LTok} (H : dropZ0 rest = rest) (n : nat) :
  dropZ0 (z0Rep n rest) = rest.
Proof. induction n as [|n IH]; [exact H | cbn [z0Rep dropZ0]; exact IH]. Qed.

Lemma epW_z0Rep_nil (n : nat) : epW (z0Rep n []) = n.
Proof.
  induction n as [|n IH]; [reflexivity |].
  destruct n as [|n']; [reflexivity |].
  change (epW (z0Rep (S (S n')) [])) with (if 0 mod 2 =? 1 then 0 else 1 + epW (z0Rep (S n') [])).
  change (0 mod 2 =? 1) with false. rewrite IH; lia.
Qed.

Lemma epW_z0Rep_p3z (n m : nat) (suf : list LTok) :
  epW (z0Rep n (p3z m :: p5 :: suf)) = n.
Proof.
  induction n as [|n IH].
  - cbn [z0Rep epW]. destruct (m mod 2 =? 1); reflexivity.
  - destruct n as [|n'].
    + change (epW (z0Rep 1 (p3z m :: p5 :: suf))) with (1 + epW (p3z m :: p5 :: suf)).
      change (z0Rep 0 (p3z m :: p5 :: suf)) with (p3z m :: p5 :: suf) in IH.
      rewrite IH; reflexivity.
    + change (epW (z0Rep (S (S n')) (p3z m :: p5 :: suf)))
        with (1 + epW (z0Rep (S n') (p3z m :: p5 :: suf))).
      rewrite IH; lia.
Qed.

Lemma isHeadP5_z0Rep_p3z (n m : nat) (suf : list LTok) :
  isHeadP5 (z0Rep n (p3z m :: suf)) = false.
Proof. destruct n; reflexivity. Qed.

Lemma isRank0_iff (ds : list nat) :
  isRank0 ds = true <-> (ds = [] \/ ds = [0] \/ ds = [1] \/ ds = [2]).
Proof.
  destruct ds as [|d [|d2 ds2]].
  - cbn [isRank0]; tauto.
  - destruct d as [|[|[|d3]]]; cbn [isRank0 Nat.leb]; split; intro H;
      try reflexivity; try discriminate; try tauto;
      (destruct H as [H|[H|[H|H]]]; congruence).
  - destruct d as [|[|[|d3]]]; cbn [isRank0]; (split; [discriminate | intros [H|[H|[H|H]]]; congruence]).
Qed.

Definition drainPopGuards (phiWp1 : nat) (ds : list nat) : bool :=
  if isDrainRstDs ds then
    (if isOddDrainDs ds then 18 else 16) <=? phiWp1
  else if isRank0 ds then
    2 <=? phiWp1
  else
    match ds with
    | d :: d2 :: ds2 =>
        (3 <=? d) && (1 <=? d2) &&
        (negb ((d mod 2 =? 0) && (d <=? 2 * d2 + 4)) || GoodDs ((d2 - 1) :: ds2)) &&
        (negb ((d mod 2 =? 0) && (d + 14 <=? 2 * d2)) || GoodDs ((d2 - 2) :: ds2)) &&
        (16 <=? phiWp1)
    | _ => false
    end.

Definition drainPopStep (has_p5 : bool) (phiWp1 m_rem : nat) (rest : list (nat * nat)) (zl : nat)
    (ds : list nat) : SegState :=
  if isDrainRstDs ds then
    let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl in
    let m_rst := headNat ds - 7 in
    if m_rst =? 1 then
      mkSeg false (fst p) (snd p) 2 1 0 [3; 1]
    else
      mkSeg true (normSeg 0 (m_rst - 2) :: fst p) (snd p) 3 0 8 [1]
  else if isRank0 ds then
    if nat_list_eqb ds [] then
      let p := pushSeg has_p5 (phiWp1 + 1) m_rem rest zl in
      mkSeg false (fst p) (snd p) 1 1 0 []
    else if nat_list_eqb ds [0] then
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl in
      mkSeg true (fst p) (snd p) 2 2 6 []
    else if nat_list_eqb ds [1] then
      let p := pushSeg has_p5 (phiWp1 + 3) m_rem rest zl in
      mkSeg true (fst p) (snd p) 2 0 6 []
    else
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl in
      mkSeg false (fst p) (snd p) 1 1 0 [0]
  else
    match ds with
    | d :: d2 :: ds2 =>
        let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl in
        if (d2 =? 1) && nat_list_eqb ds2 [] && (25 <=? d) then
          mkSeg true (normSeg 0 (d - 11) :: fst p) (snd p) 5 0 12 [2]
        else
          mkSeg true (normSeg 0 (d - 3) :: fst p) (snd p) (d2 - 1) 0 (2 * d2) ds2
    | _ => mkSeg true [] 0 0 0 0 []
    end.

Definition stepGuards (s : SegState) : bool :=
  match st_b s with
  | false =>
      let c := st_cp1 s in
      let k := st_kb s in
      match st_segs s with
      | [] =>
          let cz := c + st_zl s in
          GoodPhiW (cz - 1) (st_ds s) false && GoodPsi (cz - 1) (st_ds s)
      | (_, 0) :: _ => true
      | (z_0, S m') :: _ =>
          let m0 := S m' in
          let cz := c + z_0 in
          let kz := k + 2 * z_0 in
          GoodPhiW (cz - 1) (st_ds s) false &&
          if m0 =? 1 then GoodPsi cz (st_ds s)
          else
            GoodPsi (cz - 1) (st_ds s) &&
            if (m0 mod 2 =? 0) && (m0 <=? 2 * kz + 10) then true
            else if (m0 mod 2 =? 1) && (m0 <=? 2 * kz + 11) then GoodDs ((kz + 2) :: cz :: st_ds s)
            else true
      end
  | true =>
      match st_segs s with
      | [] => drainPopGuards (st_cp1 s + st_zl s) (st_ds s)
      | (_, 0) :: _ => st_kb s <=? st_mrg s
      | (z_0, S m') :: _ =>
          let m0 := S m' in
          if m0 mod 2 =? 1 then
            if st_kb s + m' <=? st_mrg s then GoodDs ((st_cp1 s + z_0) :: st_ds s)
            else drainPopGuards (st_cp1 s + z_0) (st_ds s)
          else
            if st_kb s + m0 <=? st_mrg s then true
            else drainPopGuards (st_cp1 s + z_0) (st_ds s)
      end
  end.

Definition stepSegs (s : SegState) : SegState :=
  match st_b s with
  | false =>
      let c := st_cp1 s in
      let k := st_kb s in
      match st_segs s with
      | [] =>
          let cz := c + st_zl s in
          let kz := k + 2 * st_zl s in
          mkSeg true [] 0 (kz + 2) 0 (2 * kz + 6) (cz :: st_ds s)
      | (z_0, 0) :: rest =>
          let cz := c + z_0 in
          let kz := k + 2 * z_0 in
          mkSeg true rest (st_zl s) (cz + 3) (kz + 3) (2 * cz + 8) (st_ds s)
      | (z_0, S m') :: rest =>
          let m0 := S m' in
          let cz := c + z_0 in
          let kz := k + 2 * z_0 in
          if m0 =? 1 then
            mkSeg false rest (st_zl s) (kz + 4) 1 0 ((cz + 1) :: st_ds s)
          else if (m0 mod 2 =? 0) && (m0 <=? 2 * kz + 10) then
            mkSeg false rest (st_zl s) (kz + 4) (m0 + 1) 0 (cz :: st_ds s)
          else if (m0 mod 2 =? 1) && (m0 <=? 2 * kz + 11) then
            mkSeg false rest (st_zl s) (m0 - 1) 1 0 ((kz + 2) :: cz :: st_ds s)
          else
            mkSeg true (normSeg 0 (m0 - 4) :: rest) (st_zl s) (kz + 2) 0 (2 * kz + 6) (cz :: st_ds s)
      end
  | true =>
      match st_segs s with
      | [] => drainPopStep false (st_cp1 s + st_zl s) 0 [] (st_zl s) (st_ds s)
      | (z_0, 0) :: rest =>
          mkSeg false rest (st_zl s) (st_cp1 s + z_0 + 1) (st_kb s + 2 * z_0 + 3) 0 (st_ds s)
      | (z_0, S m') :: rest =>
          let m0 := S m' in
          if m0 mod 2 =? 1 then
            if st_kb s + m' <=? st_mrg s then
              mkSeg false rest (st_zl s) (st_kb s + m' + 2 * z_0 + 4) 1 0 ((st_cp1 s + z_0) :: st_ds s)
            else
              drainPopStep true (st_cp1 s + z_0) (st_kb s + m0 - (st_mrg s + 2)) rest (st_zl s) (st_ds s)
          else
            if st_kb s + m0 <=? st_mrg s then
              mkSeg false rest (st_zl s) (st_cp1 s + z_0 + 2) (st_kb s + m0 + 2 * z_0 + 5) 0 (st_ds s)
            else
              drainPopStep true (st_cp1 s + z_0) (st_kb s + m0 - (st_mrg s + 2)) rest (st_zl s) (st_ds s)
      end
  end.

Lemma z0Rep_add2 (n : nat) (rest : list LTok) :
  z0Rep (n + 2) rest = p3z 0 :: p3z 0 :: z0Rep n rest.
Proof. replace (n + 2) with (S (S n)) by lia; reflexivity. Qed.

Lemma drainPop_eq_checkChain (fuel : nat) (ls : list LTok) (cp1 kb mrg : nat) (ds : list nat)
    (has_p5 : bool) (m_rem_arg : nat) (rest : list (nat * nat)) (zl : nat)
    (H1 : hasOdd ls && (kb + epSum ls <=? mrg) = false)
    (H2 : negb (hasOdd ls) && hasP5 ls && (isHeadP5 ls || (kb + epSum ls <=? mrg)) = false)
    (Hp5 : hasP5 ls = has_p5)
    (Hsuf : has_p5 = true -> p5Suf ls = encSegs rest zl)
    (Hmrem : has_p5 = true -> kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2) = m_rem_arg)
    (Hg : drainPopGuards (cp1 + epW ls) ds = true) :
  checkChainAux (S fuel) true ls cp1 kb mrg ds =
    let s' := drainPopStep has_p5 (cp1 + epW ls) m_rem_arg rest zl ds in
    checkChainAux fuel (st_b s') (encSegs (st_segs s') (st_zl s')) (st_cp1 s') (st_kb s') (st_mrg s') (st_ds s').
Proof.
  cbn [checkChainAux]. rewrite H1, H2.
  assert (Htail : (if hasP5 ls then p3z (kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2)) :: p5 :: p5Suf ls else []) =
                  (if has_p5 then p3z m_rem_arg :: p5 :: encSegs rest zl else [])).
  { destruct has_p5.
    - rewrite Hp5, (Hsuf eq_refl), (Hmrem eq_refl); reflexivity.
    - rewrite Hp5; reflexivity. }
  unfold drainPopGuards, drainPopStep in *.
  destruct (isDrainRstDs ds) eqn:Erst.
  - assert (Hlt : (cp1 + epW ls <? (if isOddDrainDs ds then 18 else 16)) = false)
      by (clear - Hg; destruct (isOddDrainDs ds); lia).
    rewrite Hlt.
    destruct (headNat ds - 7 =? 1) eqn:Em1; cbn [st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    + rewrite encSegs_pushSeg, Htail; reflexivity.
    + rewrite encSegs_normSeg; cbn [z0Rep]; rewrite encSegs_pushSeg, Htail; reflexivity.
  - destruct (isRank0 ds) eqn:Er0.
    + assert (Hlt : (cp1 + epW ls <? 2) = false) by (clear - Hg; lia).
      rewrite Hlt.
      destruct (nat_list_eqb ds []); [| destruct (nat_list_eqb ds [0]); [| destruct (nat_list_eqb ds [1])]];
        cbn [st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite encSegs_pushSeg, Htail; reflexivity.
    + destruct ds as [|d [|d2 ds2]]; try discriminate.
      assert (Hd32 : (3 <=? d) && (1 <=? d2) = true) by (clear - Hg; lia).
      rewrite Hd32.
      assert (Hc1 : (d mod 2 =? 0) && (d <=? 2 * d2 + 4) && negb (GoodDs ((d2 - 1) :: ds2)) = false)
        by (clear - Hg; lia).
      assert (Hc2 : (d mod 2 =? 0) && (d + 14 <=? 2 * d2) && negb (GoodDs ((d2 - 2) :: ds2)) = false)
        by (clear - Hg; lia).
      assert (Hc3 : (cp1 + epW ls <? 16) = false) by (clear - Hg; lia).
      rewrite Hc1, Hc2, Hc3.
      destruct ((d2 =? 1) && nat_list_eqb ds2 [] && (25 <=? d));
        cbn [st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds];
        rewrite encSegs_normSeg; cbn [z0Rep]; rewrite encSegs_pushSeg, z0Rep_add2, Htail; reflexivity.
Qed.

Lemma checkChainAux_eq_of_guards (fuel : nat) (s : SegState) (Hg : stepGuards s = true) :
  checkChainAux (S fuel) (st_b s) (encSegs (st_segs s) (st_zl s)) (st_cp1 s) (st_kb s) (st_mrg s) (st_ds s) =
    let s' := stepSegs s in
    checkChainAux fuel (st_b s') (encSegs (st_segs s') (st_zl s')) (st_cp1 s') (st_kb s') (st_mrg s') (st_ds s').
Proof.
  destruct s as [[|] segs zl cp1 kb mrg ds].
  - (* st_b = true *)
    destruct segs as [|[z [|m']] rest].
    + cbn [stepGuards stepSegs encSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds] in Hg |- *.
      pose proof (epW_z0Rep_nil zl) as Hepw.
      assert (H1 : hasOdd (z0Rep zl []) && (kb + epSum (z0Rep zl []) <=? mrg) = false)
        by (rewrite hasOdd_z0Rep; reflexivity).
      assert (H2 : negb (hasOdd (z0Rep zl [])) && hasP5 (z0Rep zl []) &&
                   (isHeadP5 (z0Rep zl []) || (kb + epSum (z0Rep zl []) <=? mrg)) = false)
        by (rewrite hasP5_z0Rep; cbn [hasP5]; rewrite !andb_false_r; reflexivity).
      pose proof (drainPop_eq_checkChain fuel (z0Rep zl []) cp1 kb mrg ds false 0 [] zl
        H1 H2 (hasP5_z0Rep zl []) ltac:(discriminate) ltac:(discriminate)
        ltac:(rewrite Hepw; exact Hg)) as Heq.
      rewrite Hepw in Heq; exact Heq.
    + cbn [stepGuards stepSegs encSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds] in Hg |- *.
      cbn [checkChainAux].
      rewrite hasOdd_z0Rep, hasP5_z0Rep, epSum_z0Rep, ep_z0Rep, p5Suf_z0Rep.
      cbn [hasOdd hasP5 epSum ep negb andb].
      replace (kb + 0 <=? mrg) with true by lia.
      rewrite orb_true_r; cbn [Nat.add].
      replace (kb + 2 * z + 3) with (kb + (2 * z + 3)) by lia.
      f_equal; lia.
    + cbn [stepGuards stepSegs encSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds] in Hg |- *.
      set (ls := z0Rep z (p3z (S m') :: p5 :: encSegs rest zl)).
      assert (Hp5 : hasP5 ls = true) by (unfold ls; rewrite hasP5_z0Rep; reflexivity).
      assert (Hsuf : p5Suf ls = encSegs rest zl) by (unfold ls; rewrite p5Suf_z0Rep; reflexivity).
      assert (Hhd : isHeadP5 ls = false) by (unfold ls; exact (isHeadP5_z0Rep_p3z z (S m') _)).
      assert (Hepw : epW ls = z) by (unfold ls; exact (epW_z0Rep_p3z z (S m') _)).
      destruct (S m' mod 2 =? 1) eqn:Eodd.
      * assert (Hodd : hasOdd ls = true) by (unfold ls; rewrite hasOdd_z0Rep; cbn [hasOdd]; rewrite Eodd; reflexivity).
        assert (Hmd : MustDrain ls = false) by (unfold ls; rewrite MustDrain_z0Rep; cbn [MustDrain]; rewrite Eodd; reflexivity).
        assert (Hep : ep ls = z) by (unfold ls; rewrite ep_z0Rep; cbn [ep]; rewrite Eodd; lia).
        assert (Heps : epSum ls = m') by (unfold ls; rewrite epSum_z0Rep; cbn [epSum]; rewrite Eodd; lia).
        destruct (kb + m' <=? mrg) eqn:Emrg.
        -- cbn [checkChainAux]. rewrite Hodd, Heps, Emrg; cbn [andb].
           rewrite Hmd, Hp5, Hsuf, Hep; cbn [negb].
           rewrite Hg; reflexivity.
        -- assert (H1 : hasOdd ls && (kb + epSum ls <=? mrg) = false) by (rewrite Hodd, Heps, Emrg; reflexivity).
           assert (H2 : negb (hasOdd ls) && hasP5 ls && (isHeadP5 ls || (kb + epSum ls <=? mrg)) = false)
             by (rewrite Hodd; reflexivity).
           pose proof (drainPop_eq_checkChain fuel ls cp1 kb mrg ds true (kb + S m' - (mrg + 2)) rest zl
             H1 H2 Hp5 (fun _ => Hsuf) (fun _ => ltac:(rewrite Heps, Hodd; f_equal; lia))
             ltac:(rewrite Hepw; exact Hg)) as Heq.
           rewrite Hepw in Heq; exact Heq.
      * assert (Hodd : hasOdd ls = false) by (unfold ls; rewrite hasOdd_z0Rep; cbn [hasOdd]; rewrite Eodd; reflexivity).
        assert (Hep : ep ls = z + 1) by (unfold ls; rewrite ep_z0Rep; cbn [ep]; rewrite Eodd; lia).
        assert (Heps : epSum ls = S m') by (unfold ls; rewrite epSum_z0Rep; cbn [epSum]; rewrite Eodd; lia).
        destruct (kb + S m' <=? mrg) eqn:Emrg.
        -- cbn [checkChainAux]. rewrite Hodd, Hp5, Hhd, Heps, Emrg, Hsuf, Hep; cbn [negb andb orb].
           cbn [st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
           f_equal; lia.
        -- assert (H1 : hasOdd ls && (kb + epSum ls <=? mrg) = false) by (rewrite Hodd; reflexivity).
           assert (H2 : negb (hasOdd ls) && hasP5 ls && (isHeadP5 ls || (kb + epSum ls <=? mrg)) = false)
             by (rewrite Hodd, Hp5, Hhd, Heps, Emrg; reflexivity).
           pose proof (drainPop_eq_checkChain fuel ls cp1 kb mrg ds true (kb + S m' - (mrg + 2)) rest zl
             H1 H2 Hp5 (fun _ => Hsuf) (fun _ => ltac:(rewrite Heps, Hodd; lia))
             ltac:(rewrite Hepw; exact Hg)) as Heq.
           rewrite Hepw in Heq; exact Heq.
  - (* st_b = false *)
    destruct segs as [|[z [|m']] rest].
    + cbn [stepGuards stepSegs encSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds] in Hg |- *.
      apply andb_true_iff in Hg as [Hphi Hpsi].
      cbn [checkChainAux].
      rewrite (z0_z0Rep_of_zero (rest := []) eq_refl zl), (dropZ0_z0Rep_of_nonz0 (rest := []) eq_refl zl).
      cbn [isHeadP5 negb]. rewrite Hphi, Hpsi; cbn [negb andb z0Rep].
      f_equal; lia.
    + cbn [stepGuards stepSegs encSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds] in Hg |- *.
      cbn [checkChainAux].
      rewrite (z0_z0Rep_of_zero (rest := p5 :: encSegs rest zl) eq_refl z),
              (dropZ0_z0Rep_of_nonz0 (rest := p5 :: encSegs rest zl) eq_refl z).
      cbn [isHeadP5 negb andb]. f_equal; lia.
    + cbn [stepGuards stepSegs encSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds] in Hg |- *.
      apply andb_true_iff in Hg as [Hphi Hg_rest].
      cbn [checkChainAux].
      rewrite (z0_z0Rep_of_zero (rest := p3z (S m') :: p5 :: encSegs rest zl) eq_refl z),
              (dropZ0_z0Rep_of_nonz0 (rest := p3z (S m') :: p5 :: encSegs rest zl) eq_refl z).
      cbn [isHeadP5 drop1L negb]. rewrite Hphi; cbn [negb andb].
      destruct (S m' =? 1) eqn:Em1.
      * rewrite Hg_rest; reflexivity.
      * apply andb_true_iff in Hg_rest as [Hpsi Hg_sub].
        rewrite Hpsi; cbn [negb].
        destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (kb + 2 * z) + 10)) eqn:Eev.
        -- reflexivity.
        -- destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (kb + 2 * z) + 11)) eqn:Eod.
           ++ rewrite Hg_sub; reflexivity.
           ++ cbn [st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
              rewrite encSegs_normSeg; cbn [z0Rep]. f_equal; lia.
Qed.

Fixpoint iterGuards (n : nat) (s : SegState) : bool :=
  match n with
  | 0 => true
  | S n' => stepGuards s && iterGuards n' (stepSegs s)
  end.

Fixpoint iterStep (n : nat) (s : SegState) : SegState :=
  match n with
  | 0 => s
  | S n' => iterStep n' (stepSegs s)
  end.

Lemma checkChainAux_of_iter (k : nat) :
  forall fuel s, iterGuards k s = true ->
    (forall f, checkChainAux f (st_b (iterStep k s)) (encSegs (st_segs (iterStep k s)) (st_zl (iterStep k s)))
      (st_cp1 (iterStep k s)) (st_kb (iterStep k s)) (st_mrg (iterStep k s)) (st_ds (iterStep k s)) = true) ->
    checkChainAux fuel (st_b s) (encSegs (st_segs s) (st_zl s)) (st_cp1 s) (st_kb s) (st_mrg s) (st_ds s) = true.
Proof.
  induction k as [|k IH]; intros fuel s Hg H.
  - exact (H fuel).
  - destruct fuel as [|f]; [reflexivity |].
    cbn [iterGuards] in Hg. apply andb_true_iff in Hg as [Hg1 Hg2].
    rewrite (checkChainAux_eq_of_guards f s Hg1).
    exact (IH f (stepSegs s) Hg2 H).
Qed.

(* Concrete 28-step validation of stepGuards & stepSegs! *)
Example hg28_check : iterGuards 28 (mkSeg true [] 0 3 0 8 [1]) = true :=
  ltac:(vm_compute; reflexivity).

Example hs28_check : iterStep 28 (mkSeg true [] 0 3 0 8 [1]) = mkSeg false [(56, 223)] 489 10 21 0 [] :=
  ltac:(vm_compute; reflexivity).


(* ========================================================================== *)
(* Section 5g.2: Fuel-Bounded LeadsUpTo Framework & Stack-Polymorphic Excursion *)
(* ========================================================================== *)

Lemma nat_strong_ind (P : nat -> Prop) (IH : forall n, (forall m, m < n -> P m) -> P n) :
  forall n, P n.
Proof.
  assert (Hbound : forall b n, n <= b -> P n).
  { induction b as [|b IHb]; intros n Hle.
    - assert (n = 0) by lia; subst n; apply IH; intros m Hm; lia.
    - destruct (Nat.eq_dec n (S b)) as [-> | Hne].
      + apply IH; intros m Hm; apply IHb; lia.
      + apply IHb; lia. }
  intro n; exact (Hbound n n (Nat.le_refl n)).
Qed.

Definition FailsIn (s : SegState) (n : nat) : Prop :=
  checkChainAux n (st_b s) (encSegs (st_segs s) (st_zl s)) (st_cp1 s) (st_kb s) (st_mrg s) (st_ds s) = false.

Definition ChainLeadsUpTo (N : nat) (s : SegState) (P : SegState -> Prop) : Prop :=
  forall n, n <= N -> FailsIn s n -> exists m s', m <= n /\ P s' /\ FailsIn s' m.

Definition ChainLeads (s : SegState) (P : SegState -> Prop) : Prop :=
  forall N, ChainLeadsUpTo N s P.

Definition ChainAdvances (s : SegState) (P : SegState -> Prop) : Prop :=
  stepGuards s = true /\ ChainLeads (stepSegs s) P.

Lemma not_failsIn_zero (s : SegState) : ~ FailsIn s 0.
Proof. unfold FailsIn; cbn [checkChainAux]; discriminate. Qed.

Lemma chainLeadsUpTo_here {N : nat} {s : SegState} {P : SegState -> Prop} (Hp : P s) :
  ChainLeadsUpTo N s P.
Proof. intros n _ Hf; exists n, s; exact (conj (Nat.le_refl n) (conj Hp Hf)). Qed.

Lemma chainLeadsUpTo_mono {M N : nat} (Hle : M <= N) {s : SegState} {P : SegState -> Prop}
    (H : ChainLeadsUpTo N s P) : ChainLeadsUpTo M s P.
Proof. intros n Hn Hf; exact (H n (Nat.le_trans _ _ _ Hn Hle) Hf). Qed.

Lemma chainLeadsUpTo_imp {N : nat} {s : SegState} {P Q : SegState -> Prop}
    (H : ChainLeadsUpTo N s P) (Himp : forall s', P s' -> Q s') : ChainLeadsUpTo N s Q.
Proof.
  intros n Hn Hf.
  destruct (H n Hn Hf) as [m [s' [Hm [Hp Hfm]]]].
  exists m, s'; exact (conj Hm (conj (Himp s' Hp) Hfm)).
Qed.

Lemma chainLeadsUpTo_trans {N : nat} {s : SegState} {P Q : SegState -> Prop}
    (H1 : ChainLeadsUpTo N s P)
    (H2 : forall m s', m <= N -> P s' -> ChainLeadsUpTo m s' Q) :
  ChainLeadsUpTo N s Q.
Proof.
  intros n Hn Hf.
  destruct (H1 n Hn Hf) as [m [s' [Hm [Hp Hfm]]]].
  destruct (H2 m s' (Nat.le_trans _ _ _ Hm Hn) Hp m (Nat.le_refl m) Hfm) as [k [s'' [Hk [Hq Hfk]]]].
  exists k, s''; exact (conj (Nat.le_trans _ _ _ Hk Hm) (conj Hq Hfk)).
Qed.

Lemma chainLeadsUpTo_step {N : nat} {s : SegState} {P : SegState -> Prop}
    (Hg : stepGuards s = true)
    (Hnext : forall m, m < N -> ChainLeadsUpTo m (stepSegs s) P) :
  ChainLeadsUpTo N s P.
Proof.
  intros [|m] Hn Hf.
  - exfalso; exact (not_failsIn_zero s Hf).
  - unfold FailsIn in Hf.
    rewrite (checkChainAux_eq_of_guards m s Hg) in Hf.
    destruct (Hnext m ltac:(lia) m (Nat.le_refl m) Hf) as [k [s' [Hk [Hp Hfk]]]].
    exists k, s'; split; [lia | exact (conj Hp Hfk)].
Qed.

Lemma chainLeadsUpTo_step1 {N : nat} {s : SegState} {P : SegState -> Prop}
    (Hg : stepGuards s = true)
    (Hnext : ChainLeadsUpTo N (stepSegs s) P) :
  ChainLeadsUpTo N s P.
Proof.
  apply (chainLeadsUpTo_step Hg); intros m Hm.
  apply (chainLeadsUpTo_mono (M := m) (N := N)); [lia | exact Hnext].
Qed.

Lemma checkChainAux_true_of_advances {P : SegState -> Prop}
    (Hadv : forall s, P s -> ChainAdvances s P) :
  forall fuel s, P s ->
    checkChainAux fuel (st_b s) (encSegs (st_segs s) (st_zl s)) (st_cp1 s) (st_kb s) (st_mrg s) (st_ds s) = true.
Proof.
  apply (nat_strong_ind (fun fuel => forall s, P s ->
    checkChainAux fuel (st_b s) (encSegs (st_segs s) (st_zl s)) (st_cp1 s) (st_kb s) (st_mrg s) (st_ds s) = true)).
  intros [|m] IH s Hp; [reflexivity |].
  destruct (Hadv s Hp) as [Hg Hleads].
  destruct (checkChainAux (S m) (st_b s) (encSegs (st_segs s) (st_zl s)) (st_cp1 s) (st_kb s) (st_mrg s) (st_ds s)) eqn:Hval; [reflexivity |].
  rewrite (checkChainAux_eq_of_guards m s Hg) in Hval.
  destruct (Hleads m m (Nat.le_refl m) Hval) as [k [s' [Hk [Hps' Hfk]]]].
  unfold FailsIn in Hfk.
  rewrite (IH k ltac:(lia) s' Hps') in Hfk.
  discriminate.
Qed.

#[local] Opaque checkChainAux FailsIn ChainLeadsUpTo.

(* ========================================================================== *)
(* Segment Validity, SafeStack, and Standalone Arithmetic Lemmas              *)
(* ========================================================================== *)

Definition ValidSegs40 (segs : list (nat * nat)) (zl : nat) : Prop :=
  (forall p, In p segs -> 40 <= fst p) /\ 230 <= zl.

Definition ValidTail40 (segs : list (nat * nat)) (zl : nat) : Prop :=
  match segs with
  | [] => 230 <= zl
  | _ :: rest => ValidSegs40 rest zl
  end.

Definition fzOf (segs : list (nat * nat)) (zl : nat) : nat :=
  match segs with
  | [] => zl
  | (z, _) :: _ => z
  end.

Lemma fzOf_ge_40 {segs : list (nat * nat)} {zl : nat} (Hv : ValidSegs40 segs zl) :
  40 <= fzOf segs zl.
Proof.
  destruct Hv as [Hall Hzl].
  destruct segs as [|[z m] rest]; [cbn [fzOf]; lia |].
  exact (Hall (z, m) (or_introl eq_refl)).
Qed.

Lemma validTail40_of_validSegs40 {segs : list (nat * nat)} {zl : nat}
    (Hv : ValidSegs40 segs zl) : ValidTail40 segs zl.
Proof.
  destruct Hv as [Hall Hzl].
  destruct segs as [|p rest]; [exact Hzl |].
  split; [intros q Hq; exact (Hall q (or_intror Hq)) | exact Hzl].
Qed.

Lemma validSegs40_tail {p : nat * nat} {rest : list (nat * nat)} {zl : nat}
    (Hv : ValidSegs40 (p :: rest) zl) : ValidSegs40 rest zl.
Proof. exact (validTail40_of_validSegs40 Hv). Qed.

Lemma normSeg_fst_ge (z m : nat) : z <= fst (normSeg z m).
Proof. unfold normSeg; destruct (m =? 0); cbn [fst]; lia. Qed.

Lemma validSegs40_pushSeg (hp : bool) {z m : nat} {rest : list (nat * nat)} {zl : nat}
    (Hz : 40 <= z) (Hv : hp = true -> ValidSegs40 rest zl) (Hzl : hp = false -> 230 <= z) :
  ValidSegs40 (fst (pushSeg hp z m rest zl)) (snd (pushSeg hp z m rest zl)).
Proof.
  destruct hp; cbn [pushSeg fst snd].
  - destruct (Hv eq_refl) as [Hall Hzl'].
    split; [| exact Hzl'].
    intros q [<- | Hq].
    + pose proof (normSeg_fst_ge z m); lia.
    + exact (Hall q Hq).
  - split; [intros _ [] | exact (Hzl eq_refl)].
Qed.

Lemma validTail40_pushSeg (hp : bool) {z m : nat} {rest : list (nat * nat)} {zl : nat}
    (Hv : hp = true -> ValidSegs40 rest zl) (Hzl : hp = false -> 230 <= z) :
  ValidTail40 (fst (pushSeg hp z m rest zl)) (snd (pushSeg hp z m rest zl)).
Proof. destruct hp; [exact (Hv eq_refl) | exact (Hzl eq_refl)]. Qed.

Lemma fzOf_pushSeg_ge (hp : bool) (z m : nat) (rest : list (nat * nat)) (zl : nat) :
  z <= fzOf (fst (pushSeg hp z m rest zl)) (snd (pushSeg hp z m rest zl)).
Proof.
  destruct hp; cbn [pushSeg fst snd fzOf].
  - unfold normSeg; destruct (m =? 0); lia.
  - lia.
Qed.

Lemma goodPhiW_of_ge35 {phiW : nat} {ds : list nat} (Hne2 : ds <> [2]) (H35 : 35 <= phiW) :
  GoodPhiW phiW ds false = true.
Proof.
  unfold GoodPhiW.
  assert (E2 : nat_list_eqb ds [2] = false) by (apply nat_list_eqb_false; exact Hne2).
  rewrite E2.
  destruct (nat_list_eqb ds [0]); [lia |].
  destruct (nat_list_eqb ds [1]); [lia |].
  destruct (nat_list_eqb ds []); [cbn [orb]; lia |].
  destruct (isDGe25One ds); [lia |].
  destruct (isOddDrainDs ds); lia.
Qed.

Definition SafeStack (m : nat) (S_ds : list nat) : Prop :=
  S_ds <> [2] /\ GoodDs S_ds = true /\ forall u, m <= u -> GoodDs (u :: S_ds) = true.

Lemma safeStack_mono {m1 m2 : nat} {S_ds : list nat} (Hle : m1 <= m2) (Hs : SafeStack m1 S_ds) :
  SafeStack m2 S_ds.
Proof.
  destruct Hs as [H1 [H2 H3]].
  exact (conj H1 (conj H2 (fun u Hu => H3 u (Nat.le_trans _ _ _ Hle Hu)))).
Qed.

Lemma isOddDrain1_eq_false_of_ge18 {x : nat} (Hx : 18 <= x) : isOddDrain1 x = false.
Proof. unfold isOddDrain1; lia. Qed.

Lemma GoodDs_cons2 (u x : nat) : GoodDs [u; x] = GoodDs2 u x.
Proof. reflexivity. Qed.

Lemma GoodDs_cons3 (u d2 d3 : nat) (ds3 : list nat) :
  GoodDs (u :: d2 :: d3 :: ds3) =
    if d2 <? 3 then false
    else if (d2 =? 3) && (d3 =? 1) && nat_list_eqb ds3 [] && (u <? 19) then false
    else if isOddDrainDs (d2 :: d3 :: ds3) && (u <? 19) then false
    else if (25 <=? d2) && (d3 =? 1) && nat_list_eqb ds3 [] && (u <? 39) then false
    else if (u <? 17) || negb (GoodDs (d2 :: d3 :: ds3)) then false
    else if ((u mod 2 =? 0) && (u <=? 2 * d2 + 4)) && negb (GoodDs ((d2 - 1) :: d3 :: ds3)) then false
    else if ((u mod 2 =? 0) && (u + 14 <=? 2 * d2)) && negb (GoodDs ((d2 - 2) :: d3 :: ds3)) then false
    else true.
Proof. reflexivity. Qed.

Lemma safeStack_cons {m x : nat} {S_ds : list nat}
    (Hs : SafeStack m S_ds) (Hx18 : 18 <= x) (Hxm : m + 2 <= x) :
  SafeStack 39 (x :: S_ds).
Proof.
  destruct Hs as [Hne2 [HgS HallS]].
  split; [intro H; inversion H; lia |].
  split; [exact (HallS x ltac:(lia)) |].
  intros u Hu.
  destruct S_ds as [|d3 ds3].
  - rewrite GoodDs_cons2; unfold GoodDs2, GoodDs1.
    rewrite (isOddDrain1_eq_false_of_ge18 Hx18).
    rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
    cbn [andb]. rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). reflexivity.
  - rewrite GoodDs_cons3.
    rewrite (HallS x ltac:(lia)), (HallS (x - 1) ltac:(lia)), (HallS (x - 2) ltac:(lia)).
    cbn [negb]; rewrite !andb_false_r, !orb_false_r.
    rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
    reflexivity.
Qed.

Lemma safeStack_cons_ne1 {m x : nat} {S_ds : list nat}
    (Hne1 : S_ds <> [1]) (Hs : SafeStack m S_ds) (Hx18 : 18 <= x) (Hxm : m + 2 <= x) :
  SafeStack 19 (x :: S_ds).
Proof.
  destruct Hs as [Hne2 [HgS HallS]].
  split; [intro H; inversion H; lia |].
  split; [exact (HallS x ltac:(lia)) |].
  intros u Hu.
  destruct S_ds as [|d3 ds3].
  - rewrite GoodDs_cons2; unfold GoodDs2, GoodDs1.
    rewrite (isOddDrain1_eq_false_of_ge18 Hx18).
    rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
    cbn [andb]. rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). reflexivity.
  - rewrite GoodDs_cons3.
    rewrite (HallS x ltac:(lia)), (HallS (x - 1) ltac:(lia)), (HallS (x - 2) ltac:(lia)).
    cbn [negb]; rewrite !andb_false_r, !orb_false_r.
    assert (Hd25 : ((25 <=? x) && (d3 =? 1) && nat_list_eqb ds3 [] && (u <? 39)) = false).
    { destruct (d3 =? 1) eqn:Ed3; [| rewrite !andb_false_r; cbn [andb]; lia].
      destruct (nat_list_eqb ds3 []) eqn:Eds3; [| rewrite !andb_false_r; cbn [andb]; lia].
      exfalso; apply Hne1.
      assert (d3 = 1) by lia. apply nat_list_eqb_true in Eds3. subst; reflexivity. }
    rewrite Hd25.
    rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
    reflexivity.
Qed.

Definition ox (kz cz : nat) : nat := cz - (3 * cz - kz) / 30 - 2.
Definition odw (kz cz : nat) : nat := ox kz cz - 1.
Definition oxw (kz cz : nat) : nat := cz + kz / 20 + 36.

Lemma ox_spec_lt {kz cz : nat} (H : kz < 3 * cz) :
  exists q r, r < 30 /\ 30 * q + r + kz = 3 * cz /\
    (q + 2 <= cz -> ox kz cz = cz - q - 2).
Proof.
  exists ((3 * cz - kz) / 30), ((3 * cz - kz) mod 30).
  unfold ox; lia.
Qed.

Lemma oxw_spec (kz cz : nat) :
  exists q r, r < 20 /\ kz = 20 * q + r /\ oxw kz cz = cz + q + 36.
Proof.
  exists (kz / 20), (kz mod 20).
  unfold oxw; lia.
Qed.

Lemma div10_spec (n : nat) :
  exists q r, r < 10 /\ n = 10 * q + r /\ n / 10 = q.
Proof.
  exists (n / 10), (n mod 10); lia.
Qed.

Lemma ox_bounds_relaxed {c k fz : nat}
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz : 35 <= fz) (Hcz : 42 <= c + fz) (Hkz : 73 <= k + 2 * fz) :
  39 <= ox (k + 2 * fz) (c + fz) /\ ox (k + 2 * fz) (c + fz) + 3 <= c + fz.
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q [r [Hr [Heq Hox]]]].
  rewrite (Hox ltac:(lia)); lia.
Qed.

Lemma ox_ge41_of_c5 {c k fz : nat}
    (Hc : 5 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz) :
  41 <= ox (k + 2 * fz) (c + fz).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q [r [Hr [Heq Hox]]]].
  rewrite (Hox ltac:(lia)); lia.
Qed.

Lemma arith_fb_t0 {c k z_0 z_1 fz2 : nat}
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz0 : 35 <= z_0) (Hcz : 42 <= c + z_0) (Hkz : 73 <= k + 2 * z_0)
    (Hz1 : 40 <= z_1) (Hfz2 : 40 <= fz2) :
  ox (k + 2 * z_0) (c + z_0) <= ox (k + 2 * z_0 + 3 + 2 * z_1 + 3 + 2 * fz2) (c + z_0 + 3 + z_1 + 1 + fz2) /\
  odw (k + 2 * z_0) (c + z_0) <= odw (k + 2 * z_0 + 3 + 2 * z_1 + 3 + 2 * fz2) (c + z_0 + 3 + z_1 + 1 + fz2) /\
  oxw (k + 2 * z_0) (c + z_0) <= oxw (k + 2 * z_0 + 3 + 2 * z_1 + 3 + 2 * fz2) (c + z_0 + 3 + z_1 + 1 + fz2).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * z_0) (cz := c + z_0) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (ox_spec_lt (kz := k + 2 * z_0 + 3 + 2 * z_1 + 3 + 2 * fz2) (cz := c + z_0 + 3 + z_1 + 1 + fz2) ltac:(lia)) as [q2 [r2 [Hr2 [Heq2 Hox2]]]].
  destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  destruct (oxw_spec (k + 2 * z_0 + 3 + 2 * z_1 + 3 + 2 * fz2) (c + z_0 + 3 + z_1 + 1 + fz2)) as [qw2 [rw2 [Hrw2 [Hkw2 Hoxw2]]]].
  unfold odw; rewrite (Hox1 ltac:(lia)), (Hox2 ltac:(lia)), Hoxw1, Hoxw2; lia.
Qed.

Lemma arith_fb_to {c k z_0 z_1 m1' fz2 : nat}
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz0 : 35 <= z_0) (Hcz : 42 <= c + z_0) (Hkz : 73 <= k + 2 * z_0)
    (Hz1 : 40 <= z_1) (Hfz2 : 40 <= fz2) :
  ox (k + 2 * z_0) (c + z_0) <= c + z_0 + 3 + z_1 /\
  30 * ox (k + 2 * z_0) (c + z_0) <= (k + 2 * z_0 + 3 + m1' + 2 * z_1 + 4 + fz2) + 27 * (c + z_0 + 3 + z_1) + 900 /\
  60 * ox (k + 2 * z_0) (c + z_0) + 120 <= 2 * (k + 2 * z_0 + 3 + m1' + 2 * z_1 + 4 + fz2) + 55 * (c + z_0 + 3 + z_1) /\
  10 * oxw (k + 2 * z_0) (c + z_0) + 40 <= 9 * (k + 2 * z_0 + 3 + m1' + 2 * z_1 + 4 + fz2) + 10 * (c + z_0 + 3 + z_1) /\
  20 * oxw (k + 2 * z_0) (c + z_0) <= (k + 2 * z_0 + 3 + m1' + 2 * z_1 + 4 + fz2) + 20 * (c + z_0 + 3 + z_1) + 800.
Proof.
  destruct (ox_spec_lt (kz := k + 2 * z_0) (cz := c + z_0) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  rewrite (Hox1 ltac:(lia)), Hoxw1; lia.
Qed.

Lemma arith_fb_te {c k z_0 z_1 m1' fz2 : nat}
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz0 : 35 <= z_0) (Hcz : 42 <= c + z_0) (Hkz : 73 <= k + 2 * z_0)
    (Hz1 : 40 <= z_1) (Hfz2 : 40 <= fz2)
    (Hmrg : (k + 2 * z_0 + 3) + (m1' + 1) <= 2 * (c + z_0) + 8) :
  ox (k + 2 * z_0) (c + z_0) <= ox ((k + 2 * z_0 + 3) + (m1' + 1) + 2 * z_1 + 5 + 2 * fz2) (c + z_0 + 3 + z_1 + 2 + fz2) /\
  odw (k + 2 * z_0) (c + z_0) <= odw ((k + 2 * z_0 + 3) + (m1' + 1) + 2 * z_1 + 5 + 2 * fz2) (c + z_0 + 3 + z_1 + 2 + fz2) /\
  oxw (k + 2 * z_0) (c + z_0) <= oxw ((k + 2 * z_0 + 3) + (m1' + 1) + 2 * z_1 + 5 + 2 * fz2) (c + z_0 + 3 + z_1 + 2 + fz2).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * z_0) (cz := c + z_0) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (ox_spec_lt (kz := (k + 2 * z_0 + 3) + (m1' + 1) + 2 * z_1 + 5 + 2 * fz2) (cz := c + z_0 + 3 + z_1 + 2 + fz2) ltac:(lia)) as [q2 [r2 [Hr2 [Heq2 Hox2]]]].
  destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  destruct (oxw_spec ((k + 2 * z_0 + 3) + (m1' + 1) + 2 * z_1 + 5 + 2 * fz2) (c + z_0 + 3 + z_1 + 2 + fz2)) as [qw2 [rw2 [Hrw2 [Hkw2 Hoxw2]]]].
  unfold odw; rewrite (Hox1 ltac:(lia)), (Hox2 ltac:(lia)), Hoxw1, Hoxw2; lia.
Qed.

Lemma arith_fb_m1_ev {c k z_0 fz1 dx : nat}
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz0 : 35 <= z_0) (Hcz : 42 <= c + z_0) (Hkz : 73 <= k + 2 * z_0)
    (Hfz1 : 40 <= fz1) (Hdx : dx <= 1) :
  ox (k + 2 * z_0) (c + z_0) <= c + z_0 + dx /\
  30 * ox (k + 2 * z_0) (c + z_0) <= (k + 2 * z_0 + 4 + fz1) + 27 * (c + z_0 + dx) + 900 /\
  60 * ox (k + 2 * z_0) (c + z_0) + 120 <= 2 * (k + 2 * z_0 + 4 + fz1) + 55 * (c + z_0 + dx) /\
  10 * oxw (k + 2 * z_0) (c + z_0) + 40 <= 9 * (k + 2 * z_0 + 4 + fz1) + 10 * (c + z_0 + dx) /\
  20 * oxw (k + 2 * z_0) (c + z_0) <= (k + 2 * z_0 + 4 + fz1) + 20 * (c + z_0 + dx) + 800.
Proof.
  destruct (ox_spec_lt (kz := k + 2 * z_0) (cz := c + z_0) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  rewrite (Hox1 ltac:(lia)), Hoxw1; lia.
Qed.

Lemma arith_fb_os_r10 {c k z_0 y1 phi1 fz4 : nat}
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz0 : 35 <= z_0) (Hcz : 42 <= c + z_0) (Hkz : 73 <= k + 2 * z_0)
    (Hy1_lo : 9 * ((k + 2 * z_0) / 10) - 2 <= y1)
    (Hy1_hi : y1 <= 2 * (c + z_0) + 3)
    (Hphi1 : 38 <= phi1)
    (Hyw : k + 2 * z_0 + 35 <= y1 + phi1)
    (Hfz4 : phi1 + 2 <= fz4) :
  ox (k + 2 * z_0) (c + z_0) <= ox (y1 + 2 + 2 * fz4) (c + z_0 + 1 + fz4) /\
  odw (k + 2 * z_0) (c + z_0) <= odw (y1 + 2 + 2 * fz4) (c + z_0 + 1 + fz4) /\
  oxw (k + 2 * z_0) (c + z_0) <= oxw (y1 + 2 + 2 * fz4) (c + z_0 + 1 + fz4).
Proof.
  destruct (div10_spec (k + 2 * z_0)) as [qd [rd [Hrd [Hkd Hdiv10]]]].
  rewrite Hdiv10 in Hy1_lo.
  destruct (ox_spec_lt (kz := k + 2 * z_0) (cz := c + z_0) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (ox_spec_lt (kz := y1 + 2 + 2 * fz4) (cz := c + z_0 + 1 + fz4) ltac:(lia)) as [q2 [r2 [Hr2 [Heq2 Hox2]]]].
  destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  destruct (oxw_spec (y1 + 2 + 2 * fz4) (c + z_0 + 1 + fz4)) as [qw2 [rw2 [Hrw2 [Hkw2 Hoxw2]]]].
  unfold odw; rewrite (Hox1 ltac:(lia)), (Hox2 ltac:(lia)), Hoxw1, Hoxw2; lia.
Qed.

Lemma arith_fb_os_r11 {c k z_0 y1 phi1 fz4 : nat}
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz0 : 35 <= z_0) (Hcz : 42 <= c + z_0) (Hkz : 73 <= k + 2 * z_0)
    (Hyw : k + 2 * z_0 + 35 <= y1 + phi1)
    (Hfz4 : phi1 + 2 <= fz4) :
  ox (k + 2 * z_0) (c + z_0) <= c + z_0 - 1 /\
  30 * ox (k + 2 * z_0) (c + z_0) <= (y1 + fz4) + 27 * (c + z_0 - 1) + 900 /\
  60 * ox (k + 2 * z_0) (c + z_0) + 120 <= 2 * (y1 + fz4) + 55 * (c + z_0 - 1) /\
  10 * oxw (k + 2 * z_0) (c + z_0) + 40 <= 9 * (y1 + fz4) + 10 * (c + z_0 - 1) /\
  20 * oxw (k + 2 * z_0) (c + z_0) <= (y1 + fz4) + 20 * (c + z_0 - 1) + 800.
Proof.
  destruct (ox_spec_lt (kz := k + 2 * z_0) (cz := c + z_0) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  rewrite (Hox1 ltac:(lia)), Hoxw1; lia.
Qed.

Lemma arith_lb_r10 {c k fz x tx txw y phi fz3 : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz)
    (Htx21 : 21 <= tx) (Htx_x : tx <= x)
    (Hi1 : 30 * tx <= (c + fz) + 27 * x + 900)
    (Hi2 : 60 * tx + 120 <= 2 * (c + fz) + 55 * x)
    (Hi3 : 10 * txw + 40 <= 9 * (c + fz) + 10 * x)
    (Hi4 : 20 * txw <= (c + fz) + 20 * x + 800)
    (Hy_lo : ox (k + 2 * fz) (c + fz) <= y)
    (Hy_hi : y <= 2 * x + 3)
    (Hphi38 : 38 <= phi)
    (Hyw : oxw (k + 2 * fz) (c + fz) <= y + phi)
    (Hfz3 : phi + 2 <= fz3) :
  tx <= ox (y + 2 + 2 * fz3) (x + 1 + fz3) /\
  tx - 1 <= odw (y + 2 + 2 * fz3) (x + 1 + fz3) /\
  txw <= oxw (y + 2 + 2 * fz3) (x + 1 + fz3).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * fz) (c + fz)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  rewrite (Hox1 ltac:(lia)) in Hy_lo; rewrite Hoxw1 in Hyw.
  destruct (ox_spec_lt (kz := y + 2 + 2 * fz3) (cz := x + 1 + fz3) ltac:(lia)) as [q2 [r2 [Hr2 [Heq2 Hox2]]]].
  destruct (oxw_spec (y + 2 + 2 * fz3) (x + 1 + fz3)) as [qw2 [rw2 [Hrw2 [Hkw2 Hoxw2]]]].
  unfold odw; rewrite (Hox2 ltac:(lia)), Hoxw2; lia.
Qed.

Lemma arith_lb_r11 {c k fz x tx txw y phi fz3 : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz)
    (Htx21 : 21 <= tx) (Htx_x : tx <= x)
    (Hi1 : 30 * tx <= (c + fz) + 27 * x + 900)
    (Hi2 : 60 * tx + 120 <= 2 * (c + fz) + 55 * x)
    (Hi3 : 10 * txw + 40 <= 9 * (c + fz) + 10 * x)
    (Hi4 : 20 * txw <= (c + fz) + 20 * x + 800)
    (Hy_lo : ox (k + 2 * fz) (c + fz) <= y)
    (Hy_hi : y <= 2 * x + 4)
    (Hphi38 : 38 <= phi)
    (Hyw : oxw (k + 2 * fz) (c + fz) <= y + phi)
    (Hfz3 : phi + 2 <= fz3) :
  5 <= y /\
  tx <= x - 1 /\
  30 * tx <= (y + fz3) + 27 * (x - 1) + 900 /\
  60 * tx + 120 <= 2 * (y + fz3) + 55 * (x - 1) /\
  10 * txw + 40 <= 9 * (y + fz3) + 10 * (x - 1) /\
  20 * txw <= (y + fz3) + 20 * (x - 1) + 800.
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * fz) (c + fz)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  rewrite (Hox1 ltac:(lia)) in Hy_lo; rewrite Hoxw1 in Hyw; lia.
Qed.

(* ========================================================================== *)
(* Pre-Pop Bounce Predicate & R9/R10/R11 Pop Dispatcher                       *)
(* ========================================================================== *)

Inductive IsBounce : nat -> list nat -> SegState -> Prop :=
| IsBounce_nil (zl cp1 kb mrg : nat) (ds : list nat) :
    230 <= cp1 + zl ->
    IsBounce (cp1 + zl) ds (mkSeg true [] zl cp1 kb mrg ds)
| IsBounce_cons (z_0 m zl cp1 kb mrg : nat) (rest : list (nat * nat)) (ds : list nat) :
    ValidSegs40 rest zl ->
    16 <= cp1 + z_0 ->
    (if S m mod 2 =? 1 then mrg < kb + m else mrg < kb + S m) ->
    IsBounce (cp1 + z_0) ds (mkSeg true ((z_0, S m) :: rest) zl cp1 kb mrg ds).

Lemma isBounce_step {phi : nat} {ds : list nat} {s : SegState}
    (Hb : IsBounce phi ds s) (Hg_pop : drainPopGuards phi ds = true) :
  stepGuards s = true /\ 16 <= phi /\
    exists hp m_rem rest zl,
      (hp = true -> ValidSegs40 rest zl) /\
      (hp = false -> 230 <= phi) /\
      stepSegs s = drainPopStep hp phi m_rem rest zl ds.
Proof.
  destruct Hb as [zl cp1 kb mrg ds Hphi | z_0 m zl cp1 kb mrg rest ds Hv Hphi Hnm].
  - split; [exact Hg_pop | split; [lia |]].
    exists false, 0, (@nil (nat * nat)), zl.
    split; [discriminate | split; [intros _; exact Hphi | reflexivity]].
  - split; [| split; [exact Hphi |]].
    + cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
      destruct (S m mod 2 =? 1); rw_if_neg ltac:(lia); exact Hg_pop.
    + exists true, (kb + S m - (mrg + 2)), rest, zl.
      split; [intros _; exact Hv | split; [discriminate |]].
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
      destruct (S m mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity.
Qed.

Definition Exit270 (tx tdw txw : nat) (S_ds : list nat) (s : SegState) : Prop :=
  (exists phi, tdw <= phi /\ IsBounce phi S_ds s) \/
  (exists y phi, tx <= y /\ 38 <= phi /\ txw <= y + phi /\ IsBounce phi (y :: S_ds) s).

Lemma exit270_mono {tx1 tdw1 txw1 tx2 tdw2 txw2 : nat} {S_ds : list nat} {s : SegState}
    (He : Exit270 tx2 tdw2 txw2 S_ds s)
    (H1 : tx1 <= tx2) (H2 : tdw1 <= tdw2) (H3 : txw1 <= txw2) :
  Exit270 tx1 tdw1 txw1 S_ds s.
Proof.
  destruct He as [[phi [Hp Hb]] | [y [phi [Hy [Hp38 [Hyw Hb]]]]]].
  - left; exists phi; split; [lia | exact Hb].
  - right; exists y, phi; split; [lia | split; [exact Hp38 | split; [lia | exact Hb]]].
Qed.

Lemma drainPop_two (hp : bool) (phi m_rem zl y x : nat) (rest : list (nat * nat)) (S_ds : list nat)
    (Hy : 19 <= y) (Hx : 19 <= x) (Hphi : 16 <= phi)
    (Hg1 : GoodDs ((x - 1) :: S_ds) = true)
    (Hg2 : y mod 2 = 0 /\ y + 14 <= 2 * x -> GoodDs ((x - 2) :: S_ds) = true) :
  drainPopGuards phi (y :: x :: S_ds) = true /\
    drainPopStep hp phi m_rem rest zl (y :: x :: S_ds) =
      let p := pushSeg hp (phi + 2) m_rem rest zl in
      mkSeg true ((0, y - 3) :: fst p) (snd p) (x - 1) 0 (2 * x) S_ds.
Proof.
  assert (Hnrst : isDrainRstDs (y :: x :: S_ds) = false) by (destruct x; [lia | reflexivity]).
  assert (Hnr0 : isRank0 (y :: x :: S_ds) = false) by (destruct y as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  split.
  - unfold drainPopGuards. rewrite Hnrst, Hnr0, Hg1, orb_true_r.
    assert (Hc2 : negb ((y mod 2 =? 0) && (y + 14 <=? 2 * x)) || GoodDs ((x - 2) :: S_ds) = true).
    { destruct ((y mod 2 =? 0) && (y + 14 <=? 2 * x)) eqn:Ec.
      - rewrite (Hg2 ltac:(lia)), orb_true_r; reflexivity.
      - reflexivity. }
    rewrite Hc2; lia.
  - unfold drainPopStep. rewrite Hnrst, Hnr0.
    rw_if_neg ltac:(lia).
    replace (normSeg 0 (y - 3)) with (0, y - 3) by (unfold normSeg; rw_if_neg ltac:(lia); reflexivity).
    reflexivity.
Qed.

Lemma amega_pop_step {N x y phi : nat} {S_ds : list nat} {sb : SegState} {P : SegState -> Prop}
    (Hb : IsBounce phi (y :: x :: S_ds) sb)
    (Hphi38 : 38 <= phi) (Hy : 19 <= y) (Hx : 19 <= x)
    (Hg1 : GoodDs ((x - 1) :: S_ds) = true)
    (Hg2 : y mod 2 = 0 /\ y + 14 <= 2 * x -> GoodDs ((x - 2) :: S_ds) = true)
    (Hr9 : 2 * x + 5 <= y -> forall m, m < N -> forall p1 p2, ValidSegs40 p1 p2 -> phi + 2 <= fzOf p1 p2 ->
      ChainLeadsUpTo m (mkSeg true ((0, y - 3) :: p1) p2 (x - 1) 0 (2 * x) S_ds) P)
    (Hr10 : y <= 2 * x + 3 -> y mod 2 = 1 -> forall m, m < N -> forall p1 p2, ValidSegs40 p1 p2 -> phi + 2 <= fzOf p1 p2 ->
      ChainLeadsUpTo m (mkSeg false p1 p2 (x + 1) (y + 2) 0 S_ds) P)
    (Hr11 : y <= 2 * x + 4 -> y mod 2 = 0 -> forall m, m < N -> forall p1 p2, ValidSegs40 p1 p2 -> phi + 2 <= fzOf p1 p2 ->
      ChainLeadsUpTo m (mkSeg false p1 p2 y 1 0 ((x - 1) :: S_ds)) P) :
  ChainLeadsUpTo N sb P.
Proof.
  pose proof (proj1 (drainPop_two false phi 0 0 y x [] S_ds Hy Hx ltac:(lia) Hg1 Hg2)) as Hg_pop.
  destruct (isBounce_step Hb Hg_pop) as [Hg_sb [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep_sb]]]]]]]].
  rewrite (proj2 (drainPop_two hp phi m_rem zl y x rest S_ds Hy Hx ltac:(lia) Hg1 Hg2)) in Hstep_sb.
  set (p := pushSeg hp (phi + 2) m_rem rest zl) in *.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg (z := phi + 2) (m := m_rem) hp ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp.
  apply (chainLeadsUpTo_step Hg_sb); intros m Hm.
  rewrite Hstep_sb.
  destruct (2 * x + 5 <=? y) eqn:Ebig.
  - exact (Hr9 ltac:(lia) m Hm (fst p) (snd p) Hvp Hfzp).
  - assert (Hy_sub : y - 3 = S (y - 4)) by lia.
    destruct (y mod 2 =? 1) eqn:Eyodd.
    + assert (Hg_mid : stepGuards (mkSeg true ((0, y - 3) :: fst p) (snd p) (x - 1) 0 (2 * x) S_ds) = true).
      { rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
        rw_if_neg ltac:(lia). rw_if_pos ltac:(lia). reflexivity. }
      assert (Hs_mid : stepSegs (mkSeg true ((0, y - 3) :: fst p) (snd p) (x - 1) 0 (2 * x) S_ds) =
                       mkSeg false (fst p) (snd p) (x + 1) (y + 2) 0 S_ds).
      { rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
        rw_if_neg ltac:(lia). rw_if_pos ltac:(lia). f_equal; lia. }
      apply (chainLeadsUpTo_step1 Hg_mid); rewrite Hs_mid.
      exact (Hr10 ltac:(lia) ltac:(lia) m Hm (fst p) (snd p) Hvp Hfzp).
    + assert (Hg_mid : stepGuards (mkSeg true ((0, y - 3) :: fst p) (snd p) (x - 1) 0 (2 * x) S_ds) = true).
      { rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
        rw_if_pos ltac:(lia). rw_if_pos ltac:(lia). rewrite Nat.add_0_r; exact Hg1. }
      assert (Hs_mid : stepSegs (mkSeg true ((0, y - 3) :: fst p) (snd p) (x - 1) 0 (2 * x) S_ds) =
                       mkSeg false (fst p) (snd p) y 1 0 ((x - 1) :: S_ds)).
      { rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
        rw_if_pos ltac:(lia). rw_if_pos ltac:(lia). f_equal; [lia | f_equal; lia]. }
      apply (chainLeadsUpTo_step1 Hg_mid); rewrite Hs_mid.
      exact (Hr11 ltac:(lia) ltac:(lia) m Hm (fst p) (snd p) Hvp Hfzp).
Qed.

Lemma isBounce_r9 {x y : nat} {p1 : list (nat * nat)} {p2 : nat} {S_ds : list nat}
    (Hx : 19 <= x) (Hbig : 2 * x + 5 <= y) (Hvp : ValidSegs40 p1 p2) :
  IsBounce (x - 1) S_ds (mkSeg true ((0, y - 3) :: p1) p2 (x - 1) 0 (2 * x) S_ds).
Proof.
  replace (y - 3) with (S (y - 4)) by lia.
  replace (x - 1) with ((x - 1) + 0) at 1 by lia.
  apply (IsBounce_cons 0 (y - 4) p2 (x - 1) 0 (2 * x) p1 S_ds Hvp ltac:(lia)).
  destruct (S (y - 4) mod 2 =? 1); lia.
Qed.

(* ========================================================================== *)
(* Main Fuel-Indexed Excursion Bundle (`FBound N /\ LoopBound N`)             *)
(* ========================================================================== *)

Definition FBound (N : nat) : Prop :=
  forall ms S_ds segs zl c k,
    19 <= ms -> SafeStack ms S_ds ->
    ValidTail40 segs zl ->
    1 <= c -> 1 <= k -> k <= 2 * c + 3 ->
    35 <= fzOf segs zl ->
    42 <= c + fzOf segs zl ->
    73 <= k + 2 * fzOf segs zl ->
    ms + 2 <= ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) ->
    ChainLeadsUpTo N (mkSeg false segs zl c k 0 S_ds)
      (Exit270 (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) S_ds).

Definition LoopBound (N : nat) : Prop :=
  forall ms S_ds segs zl c k x tx txw,
    19 <= ms -> SafeStack ms S_ds ->
    (S_ds <> [1] \/ 5 <= c) ->
    ValidSegs40 segs zl ->
    2 <= c -> 1 <= k -> k <= 2 * c + 3 ->
    ms + 2 <= tx -> tx <= x ->
    30 * tx <= (c + fzOf segs zl) + 27 * x + 900 ->
    60 * tx + 120 <= 2 * (c + fzOf segs zl) + 55 * x ->
    10 * txw + 40 <= 9 * (c + fzOf segs zl) + 10 * x ->
    20 * txw <= (c + fzOf segs zl) + 20 * x + 800 ->
    ChainLeadsUpTo N (mkSeg false segs zl c k 0 (x :: S_ds))
      (Exit270 tx (tx - 1) txw S_ds).

Lemma or_c5 (S_ds : list nat) (c : nat) (H : 5 <= c) : S_ds <> [1] \/ 5 <= c.
Proof. right; exact H. Qed.

Lemma excursion270_bundle (N : nat) : FBound N /\ LoopBound N.
Proof.
  revert N; apply (nat_strong_ind (fun N => FBound N /\ LoopBound N)); intros N IH.
  cbv delta [FBound LoopBound] in IH.
  assert (HFB : FBound N).
  { intros ms S_ds segs zl c k Hms19 HS Hvt Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hms_ox.
    destruct (ox_bounds_relaxed Hc Hk1 Hkc Hfz35 Hcz42 Hkz73) as [Hox39 Hox_cz3].
    destruct HS as [HS_ne2 [HS_gd HS_all]].
    assert (HS : SafeStack ms S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
    destruct segs as [|[z_0 m0] rest].
    - cbn [fzOf ValidTail40] in *.
      assert (Hg : stepGuards (mkSeg false [] zl c k 0 S_ds) = true).
      { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
        rewrite (goodPhiW_of_ge35 (phiW := c + zl - 1) HS_ne2 ltac:(lia)); cbn [andb]; unfold GoodPsi.
        replace (c + zl - 1 + 1) with (c + zl) by lia.
        exact (HS_all (c + zl) ltac:(lia)). }
      apply (chainLeadsUpTo_step1 Hg); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      apply chainLeadsUpTo_here; right.
      destruct (oxw_spec (k + 2 * zl) (c + zl)) as [qw [rw_ [Hrw [Hkw Hoxw]]]].
      exists (c + zl), (k + 2 * zl + 2).
      split; [lia | split; [lia | split; [rewrite Hoxw; lia |]]].
      replace (k + 2 * zl + 2) with ((k + 2 * zl + 2) + 0) at 1 by lia.
      exact (IsBounce_nil 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) ((c + zl) :: S_ds) ltac:(lia)).
    - cbn [fzOf ValidTail40] in *.
      assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
      destruct m0 as [|m'].
      + assert (Hg1 : stepGuards (mkSeg false ((z_0, 0) :: rest) zl c k 0 S_ds) = true) by reflexivity.
        apply (chainLeadsUpTo_step Hg1); intros m1 Hm1.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct rest as [|[z_1 [|m1']] rest2].
        * pose proof (proj2 Hv_rest) as Hzl230.
          apply chainLeadsUpTo_here; left.
          exists (c + z_0 + 3 + zl); split; [unfold odw; lia | exact (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds ltac:(lia))].
        * pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
          pose proof (validSegs40_tail Hv_rest) as Hv_rest2.
          pose proof (fzOf_ge_40 Hv_rest2) as Hfz2_40.
          assert (Hg2 : stepGuards (mkSeg true ((z_1, 0) :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true)
            by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
          apply (chainLeadsUpTo_step Hg2); intros m2 Hm2.
          cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
          destruct (arith_fb_t0 Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hz1_40 Hfz2_40) as [Hm_ox [Hm_odw Hm_oxw]].
          exact (chainLeadsUpTo_imp
            (proj1 (IH m2 ltac:(lia)) ms S_ds rest2 zl (c + z_0 + 3 + z_1 + 1) (k + 2 * z_0 + 3 + 2 * z_1 + 3)
              Hms19 HS (validTail40_of_validSegs40 Hv_rest2)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
            (fun s' He => exit270_mono He Hm_ox Hm_odw Hm_oxw)).
        * pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
          pose proof (validSegs40_tail Hv_rest) as Hv_rest2.
          pose proof (fzOf_ge_40 Hv_rest2) as Hfz2_40.
          destruct (S m1' mod 2 =? 1) eqn:Em1_odd.
          -- destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
             ++ assert (Hg2 : stepGuards (mkSeg true ((z_1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                  rewrite Em1_odd, Emrg. exact (HS_all (c + z_0 + 3 + z_1) ltac:(lia)). }
                apply (chainLeadsUpTo_step Hg2); intros m2 Hm2.
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
                rewrite Em1_odd, Emrg.
                destruct (arith_fb_to (m1' := m1') Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hz1_40 Hfz2_40)
                  as [Hi0 [Hi1 [Hi2 [Hi3 Hi4]]]].
                exact (proj2 (IH m2 ltac:(lia)) ms S_ds rest2 zl
                  ((k + 2 * z_0 + 3) + m1' + 2 * z_1 + 4) 1 (c + z_0 + 3 + z_1)
                  (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
                  Hms19 HS (or_c5 S_ds ((k + 2 * z_0 + 3) + m1' + 2 * z_1 + 4) ltac:(lia)) Hv_rest2
                  ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi0 Hi1 Hi2 Hi3 Hi4).
             ++ apply chainLeadsUpTo_here; left.
                exists (c + z_0 + 3 + z_1); split; [unfold odw; lia |].
                apply (IsBounce_cons z_1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 S_ds Hv_rest2 ltac:(lia)).
                rewrite Em1_odd; lia.
          -- destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
             ++ assert (Hg2 : stepGuards (mkSeg true ((z_1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                  rewrite Em1_odd, Emrg; reflexivity. }
                apply (chainLeadsUpTo_step Hg2); intros m2 Hm2.
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
                rewrite Em1_odd, Emrg.
                replace (S m1') with (m1' + 1) by lia.
                destruct (arith_fb_te (m1' := m1') Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hz1_40 Hfz2_40 ltac:(lia))
                  as [Hm_ox [Hm_odw Hm_oxw]].
                exact (chainLeadsUpTo_imp
                  (proj1 (IH m2 ltac:(lia)) ms S_ds rest2 zl (c + z_0 + 3 + z_1 + 2) ((k + 2 * z_0 + 3) + (m1' + 1) + 2 * z_1 + 5)
                    Hms19 HS (validTail40_of_validSegs40 Hv_rest2)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                  (fun s' He => exit270_mono He Hm_ox Hm_odw Hm_oxw)).
             ++ apply chainLeadsUpTo_here; left.
                exists (c + z_0 + 3 + z_1); split; [unfold odw; lia |].
                apply (IsBounce_cons z_1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 S_ds Hv_rest2 ltac:(lia)).
                rewrite Em1_odd; lia.
      + pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
        pose proof (goodPhiW_of_ge35 (phiW := c + z_0 - 1) HS_ne2 ltac:(lia)) as Hphiw.
        destruct (S m' =? 1) eqn:Em1.
        * assert (m' = 0) by lia; subst m'.
          assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 S_ds) = true).
          { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
            rewrite Hphiw; cbn [andb]; unfold GoodPsi.
            exact (HS_all (c + z_0 + 1) ltac:(lia)). }
          apply (chainLeadsUpTo_step Hg); intros m1 Hm1.
          cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
          destruct (arith_fb_m1_ev (dx := 1) Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hfz1_40 ltac:(lia))
            as [Hi0 [Hi1 [Hi2 [Hi3 Hi4]]]].
          exact (proj2 (IH m1 Hm1) ms S_ds rest zl (k + 2 * z_0 + 4) 1 (c + z_0 + 1)
            (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
            Hms19 HS (or_c5 S_ds (k + 2 * z_0 + 4) ltac:(lia)) Hv_rest
            ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi0 Hi1 Hi2 Hi3 Hi4).
        * assert (Hpsi_cz : GoodPsi (c + z_0 - 1) S_ds = true).
          { unfold GoodPsi; replace (c + z_0 - 1 + 1) with (c + z_0) by lia.
            exact (HS_all (c + z_0) ltac:(lia)). }
          destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
          -- assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true).
             { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
               rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity. }
             apply (chainLeadsUpTo_step Hg); intros m1 Hm1.
             cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
             rewrite Em1, Eev_sm.
             destruct (arith_fb_m1_ev (dx := 0) Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hfz1_40 ltac:(lia))
               as [Hi0 [Hi1 [Hi2 [Hi3 Hi4]]]].
             rewrite Nat.add_0_r in Hi0, Hi1, Hi2, Hi3, Hi4.
             exact (proj2 (IH m1 Hm1) ms S_ds rest zl (k + 2 * z_0 + 4) (S m' + 1) (c + z_0)
               (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
               Hms19 HS (or_c5 S_ds (k + 2 * z_0 + 4) ltac:(lia)) Hv_rest
               ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi0 Hi1 Hi2 Hi3 Hi4).
          -- destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
             ++ pose proof (safeStack_cons (x := c + z_0) HS ltac:(lia) ltac:(lia)) as HS_cz.
                assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                  rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                  exact (proj2 (proj2 HS_cz) (k + 2 * z_0 + 2) ltac:(lia)). }
                apply (chainLeadsUpTo_step Hg); intros m1 Hm1.
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
                rewrite Em1, Eev_sm, Eod_sm.
                replace (S m' - 1) with m' by lia.
                destruct (div10_spec (k + 2 * z_0)) as [q10 [r10 [Hr10 [Hkz10 Hdw10]]]].
                assert (Hne1_cz : ((c + z_0) :: S_ds) <> [1]) by (intro H; inversion H; lia).
                pose proof (proj2 (IH m1 Hm1) 39 ((c + z_0) :: S_ds) rest zl m' 1
                  (k + 2 * z_0 + 2) (9 * q10 - 2) (k + 2 * z_0 + 35)
                  ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_rest
                  ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia)) as H_loop1.
                apply (chainLeadsUpTo_trans H_loop1).
                intros m2 s_mid Hm2 [[phi1 [Hphi1 Hb1]] | [y1 [phi1 [Hy1_tx1 [Hphi1_38 [Hyw1 Hb1]]]]]].
                ** apply chainLeadsUpTo_here; right.
                   destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw [rw_ [Hrw [Hkw Hoxw]]]].
                   exists (c + z_0), phi1.
                   split; [lia | split; [lia | split; [rewrite Hoxw; lia | exact Hb1]]].
                ** apply (amega_pop_step Hb1 Hphi1_38 ltac:(lia) ltac:(lia)
                     (HS_all (c + z_0 - 1) ltac:(lia))
                     (fun _ => HS_all (c + z_0 - 2) ltac:(lia))).
                   --- intros Hbig m3 _ p1 p2 Hvp _.
                       apply chainLeadsUpTo_here; left.
                       exists (c + z_0 - 1); split; [unfold odw; lia | exact (isBounce_r9 (x := c + z_0) ltac:(lia) Hbig Hvp)].
                   --- intros Hy1_le _ m3 Hm3 p1 p2 Hvp Hfzp.
                       assert (Hy1_lo : 9 * ((k + 2 * z_0) / 10) - 2 <= y1) by (rewrite Hdw10; exact Hy1_tx1).
                       destruct (arith_fb_os_r10 Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hy1_lo Hy1_le Hphi1_38 Hyw1 Hfzp)
                         as [Hm_ox [Hm_odw Hm_oxw]].
                       exact (chainLeadsUpTo_imp
                         (proj1 (IH m3 ltac:(lia)) ms S_ds p1 p2 (c + z_0 + 1) (y1 + 2) Hms19 HS
                           (validTail40_of_validSegs40 Hvp)
                           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                         (fun s' He => exit270_mono He Hm_ox Hm_odw Hm_oxw)).
                   --- intros Hy1_le _ m3 Hm3 p1 p2 Hvp Hfzp.
                       destruct (arith_fb_os_r11 Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hyw1 Hfzp)
                         as [Hi0 [Hi1 [Hi2 [Hi3 Hi4]]]].
                       exact (proj2 (IH m3 ltac:(lia)) ms S_ds p1 p2 y1 1 (c + z_0 - 1)
                         (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
                         Hms19 HS (or_c5 S_ds y1 ltac:(lia)) Hvp
                         ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi0 Hi1 Hi2 Hi3 Hi4).
             ++ assert (Hm0_big : 2 * (k + 2 * z_0) + 12 <= S m')
                  by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
                assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                  rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity. }
                apply (chainLeadsUpTo_step1 Hg).
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
                rewrite Em1, Eev_sm, Eod_sm.
                replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                  by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
                apply chainLeadsUpTo_here; right.
                destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw [rw_ [Hrw [Hkw Hoxw]]]].
                exists (c + z_0), (k + 2 * z_0 + 2).
                split; [lia | split; [lia | split; [rewrite Hoxw; lia |]]].
                replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
                apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest ((c + z_0) :: S_ds) Hv_rest ltac:(lia)).
                destruct (S (m' - 4) mod 2 =? 1); lia. }
  split; [exact HFB |].
  intros ms S_ds segs zl c k x tx txw Hms19 HS HSc5 Hv Hc Hk1 Hkc Hms_tx Htx_x Hi1 Hi2 Hi3 Hi4.
  pose proof (fzOf_ge_40 Hv) as Hfz40.
  pose proof (proj1 (ox_bounds_relaxed (c := c) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia))) as Hox39.
  destruct HS as [HS_ne2 [HS_gd HS_all]].
  assert (HS : SafeStack ms S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
  assert (Hfb : ChainLeadsUpTo N (mkSeg false segs zl c k 0 (x :: S_ds))
    (Exit270 (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
      (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
      (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) (x :: S_ds))).
  { destruct HSc5 as [Hne1 | Hc5].
    - exact (HFB 19 (x :: S_ds) segs zl c k ltac:(lia)
        (safeStack_cons_ne1 (x := x) Hne1 HS ltac:(lia) ltac:(lia))
        (validTail40_of_validSegs40 Hv)
        ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (HFB 39 (x :: S_ds) segs zl c k ltac:(lia)
        (safeStack_cons (x := x) HS ltac:(lia) ltac:(lia))
        (validTail40_of_validSegs40 Hv)
        ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) (ox_ge41_of_c5 Hc5 Hk1 Hkc Hfz40)). }
  apply (chainLeadsUpTo_trans Hfb).
  intros m1 s_mid Hm1 [[phi [Hphi_odw Hb]] | [y [phi [Hy_ox [Hphi38 [Hyw Hb]]]]]].
  - apply chainLeadsUpTo_here; right.
    destruct (ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
    exists x, phi.
    unfold odw in Hphi_odw; rewrite (Hox1 ltac:(lia)) in Hphi_odw.
    split; [exact Htx_x | split; [lia | split; [lia | exact Hb]]].
  - apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
      (HS_all (x - 1) ltac:(lia)) (fun _ => HS_all (x - 2) ltac:(lia))).
    + intros Hbig m3 _ p1 p2 Hvp _.
      apply chainLeadsUpTo_here; left.
      exists (x - 1); split; [lia | exact (isBounce_r9 (x := x) ltac:(lia) Hbig Hvp)].
    + intros Hy_le _ m2 Hm2 p1 p2 Hvp Hfzp.
      destruct (arith_lb_r10 (tx := tx) Hc Hk1 Hkc Hfz40 ltac:(lia) Htx_x Hi1 Hi2 Hi3 Hi4 Hy_ox Hy_le Hphi38 Hyw Hfzp)
        as [Hm_ox [Hm_odw Hm_oxw]].
      exact (chainLeadsUpTo_imp
        (proj1 (IH m2 ltac:(lia)) ms S_ds p1 p2 (x + 1) (y + 2) Hms19 HS
          (validTail40_of_validSegs40 Hvp)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        (fun s' He => exit270_mono He Hm_ox Hm_odw Hm_oxw)).
    + intros Hy_le _ m2 Hm2 p1 p2 Hvp Hfzp.
      destruct (arith_lb_r11 (tx := tx) Hc Hk1 Hkc Hfz40 ltac:(lia) Htx_x Hi1 Hi2 Hi3 Hi4 Hy_ox Hy_le Hphi38 Hyw Hfzp)
        as [Hy5 [Htx_x1 [Hi1' [Hi2' [Hi3' Hi4']]]]].
      exact (proj2 (IH m2 ltac:(lia)) ms S_ds p1 p2 y 1 (x - 1) tx txw
        Hms19 HS (or_intror Hy5) Hvp
        ltac:(lia) ltac:(lia) ltac:(lia) Hms_tx Htx_x1 Hi1' Hi2' Hi3' Hi4').
Qed.


(* ========================================================================== *)
(* Section 5g.3a: SafeStack Bases & High-Excursion Bundle (`FHigh`, `LoopHigh`, `LoopOS`) *)
(* ========================================================================== *)

Lemma safeStack_nil : SafeStack 19 [].
Proof.
  split; [discriminate | split; [reflexivity |]].
  intros u Hu; unfold GoodDs, GoodDsAux, GoodDs1; lia.
Qed.

Lemma safeStack_zero : SafeStack 19 [0].
Proof.
  split; [intro H; inversion H | split; [reflexivity |]].
  intros u Hu; unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia.
Qed.

Lemma safeStack_one : SafeStack 25 [1].
Proof.
  split; [intro H; inversion H | split; [reflexivity |]].
  intros u Hu; unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia.
Qed.

Lemma safeStack_31 : SafeStack 19 [3; 1].
Proof.
  split; [intro H; inversion H | split; [reflexivity |]].
  intros u Hu; rewrite GoodDs_cons3.
  change (GoodDs [3; 1]) with true.
  change (isOddDrainDs [3; 1]) with false.
  rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). cbn [andb].
  rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
  rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). reflexivity.
Qed.

Lemma safeStack_x_31 {x : nat} (Hx20 : 20 <= x) (Hx22 : x <= 22) :
  SafeStack 39 [x; 3; 1].
Proof.
  pose proof (proj2 (proj2 safeStack_31) x ltac:(lia)) as Hgx.
  pose proof (proj2 (proj2 safeStack_31) (x - 1) ltac:(lia)) as Hgx1.
  split; [intro H; inversion H | split; [exact Hgx |]].
  intros u Hu; rewrite GoodDs_cons3.
  rewrite Hgx, Hgx1; change (isOddDrainDs [x; 3; 1]) with false.
  cbn [andb negb orb]; rewrite !andb_false_r; cbn [andb negb orb].
  repeat (rw_if_neg ltac:(lia)); reflexivity.
Qed.

Lemma safeStack_d {d : nat} (Hd8 : 8 <= d) : SafeStack 21 [d].
Proof.
  split; [intro H; inversion H; lia |].
  split; [unfold GoodDs, GoodDsAux, GoodDs1; lia |].
  intros u Hu; rewrite GoodDs_cons2; unfold GoodDs2, GoodDs1.
  rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
  assert (Ho : isOddDrain1 d && (u <? 19) = false) by (destruct (isOddDrain1 d); lia).
  rewrite Ho. rw_if_neg ltac:(lia).
  destruct (Nat.eq_dec d 8) as [-> | Hd9]; [rw_if_neg ltac:(lia); rw_if_neg ltac:(lia); reflexivity |].
  rw_if_neg ltac:(lia).
  destruct (Nat.eq_dec d 9) as [-> | Hd10]; rw_if_neg ltac:(lia); reflexivity.
Qed.

Lemma safeStack_d0 {d : nat} (Hd8 : 8 <= d) : SafeStack 21 [d; 0].
Proof.
  split; [intro H; inversion H; lia |].
  split; [unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia |].
  intros u Hu; rewrite GoodDs_cons3.
  assert (Hgd : GoodDs [d; 0] = true) by (unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia).
  rewrite Hgd; cbn [negb orb].
  rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
  assert (Ho : isOddDrainDs [d; 0] && (u <? 19) = false) by (destruct (isOddDrainDs [d; 0]); lia).
  rewrite Ho. rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
  destruct (Nat.eq_dec d 8) as [-> | Hd9]; [rw_if_neg ltac:(lia); rw_if_neg ltac:(lia); reflexivity |].
  assert (Hg1 : GoodDs [d - 1; 0] = true) by (unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia).
  rewrite Hg1, andb_false_r.
  destruct (Nat.eq_dec d 9) as [-> | Hd10]; [rw_if_neg ltac:(lia); reflexivity |].
  assert (Hg2 : GoodDs [d - 2; 0] = true) by (unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia).
  rewrite Hg2, andb_false_r; reflexivity.
Qed.

Lemma safeStack_d1 {d : nat} (Hd26 : 26 <= d) : SafeStack 39 [d; 1].
Proof.
  pose proof (proj2 (proj2 safeStack_one) d ltac:(lia)) as Hgd.
  pose proof (proj2 (proj2 safeStack_one) (d - 1) ltac:(lia)) as Hg1.
  split; [intro H; inversion H | split; [exact Hgd |]].
  intros u Hu; rewrite GoodDs_cons3.
  rewrite Hgd, Hg1; change (isOddDrainDs [d; 1]) with false.
  cbn [negb orb andb]; rewrite !andb_false_r; cbn [negb orb andb].
  destruct (Nat.eq_dec d 26) as [-> | Hd27]; [repeat (rw_if_neg ltac:(lia)); reflexivity |].
  rewrite (proj2 (proj2 safeStack_one) (d - 2) ltac:(lia)); cbn [negb orb andb]; rewrite !andb_false_r.
  repeat (rw_if_neg ltac:(lia)); reflexivity.
Qed.

Lemma safeStack_of_gt2d2 {m d2 d3 : nat} {ds3 : list nat}
    (Hm39 : 39 <= m) (Hm_gt : 2 * d2 + 5 <= m) (Hd2 : 17 <= d2)
    (Hg : GoodDs (d2 :: d3 :: ds3) = true) :
  SafeStack m (d2 :: d3 :: ds3).
Proof.
  split; [intro H; inversion H | split; [exact Hg |]].
  intros u Hu; rewrite GoodDs_cons3, Hg; cbn [negb orb].
  rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
  assert (Ho : isOddDrainDs (d2 :: d3 :: ds3) && (u <? 19) = false)
    by (destruct (isOddDrainDs (d2 :: d3 :: ds3)); lia).
  rewrite Ho. rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
  rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). reflexivity.
Qed.

Lemma safeStack_25_1 : SafeStack 55 [25; 1].
Proof. apply safeStack_of_gt2d2; try lia; exact eq_refl. Qed.

Lemma safeStack_17_8_0 : SafeStack 39 [17; 8; 0].
Proof. apply safeStack_of_gt2d2; try lia; exact eq_refl. Qed.

Lemma safeStack_20_3_1 : SafeStack 27 [20; 3; 1].
Proof.
  split; [intro H; inversion H | split; [reflexivity |]].
  intros u Hu; rewrite GoodDs_cons3.
  change (GoodDs [20; 3; 1]) with true.
  change (GoodDs [20 - 1; 3; 1]) with true.
  change (isOddDrainDs [20; 3; 1]) with false.
  cbn [negb orb andb]; rewrite !andb_false_r; cbn [negb orb andb].
  repeat (rw_if_neg ltac:(lia)); reflexivity.
Qed.

Lemma safeStack_19_9 : SafeStack 43 [19; 9].
Proof. apply safeStack_of_gt2d2; try lia; exact eq_refl. Qed.

Lemma safeStack_19_9_0 : SafeStack 43 [19; 9; 0].
Proof. apply safeStack_of_gt2d2; try lia; exact eq_refl. Qed.

Lemma safeStack_47_25_1 : SafeStack 99 [47; 25; 1].
Proof. apply safeStack_of_gt2d2; try lia; exact eq_refl. Qed.

(* ========================================================================== *)
(* High-Excursion Arithmetic Lemmas & Bundle (`FHigh`, `LoopHigh`, `LoopOS`)  *)
(* ========================================================================== *)

Definition ExitHigh (S_ds : list nat) (s : SegState) : Prop :=
  (exists phi, 48 <= phi /\ IsBounce phi S_ds s) \/
  (exists y phi, 49 <= y /\ ((53 <= y /\ 90 <= phi) \/ 100 <= phi) /\ IsBounce phi (y :: S_ds) s).

Lemma arith_lh_bounds {c k fz : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz) (Hcz : 131 <= c + fz) :
  119 <= ox (k + 2 * fz) (c + fz) /\ 118 <= odw (k + 2 * fz) (c + fz).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  unfold odw; rewrite (Hox1 ltac:(lia)); lia.
Qed.

Lemma arith_los_r11 {c k fz x y phi fz3 : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz)
    (Hx : 91 <= x) (Hpot : 2220 <= (c + fz) + 22 * x)
    (Hy_lo : ox (k + 2 * fz) (c + fz) <= y) (Hy_hi : y <= 2 * x + 4)
    (Hphi38 : 38 <= phi) (Hyw : oxw (k + 2 * fz) (c + fz) <= y + phi)
    (Hfz3 : phi + 2 <= fz3) :
  39 <= y /\ 91 <= x - 1 /\ 2220 <= (y + fz3) + 22 * (x - 1).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * fz) (c + fz)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  rewrite (Hox1 ltac:(lia)) in Hy_lo; rewrite Hoxw1 in Hyw; lia.
Qed.

Lemma odw_def (kz cz : nat) : odw kz cz = ox kz cz - 1.
Proof. reflexivity. Qed.

#[local] Opaque ox odw oxw.

Definition FHigh (N : nat) : Prop :=
  forall S_ds segs zl c k,
    S_ds <> [1] -> SafeStack 43 S_ds ->
    ValidSegs40 segs zl ->
    2 <= c -> 1 <= k -> k <= 2 * c + 3 ->
    53 <= c + fzOf segs zl ->
    97 <= k + 2 * fzOf segs zl ->
    ChainLeadsUpTo N (mkSeg false segs zl c k 0 S_ds) (ExitHigh S_ds).

Definition LoopHigh (N : nat) : Prop :=
  forall S_ds segs zl c k x,
    S_ds <> [1] -> SafeStack 43 S_ds ->
    ValidSegs40 segs zl ->
    2 <= c -> 1 <= k -> k <= 2 * c + 3 ->
    49 <= x ->
    131 <= c + fzOf segs zl ->
    ChainLeadsUpTo N (mkSeg false segs zl c k 0 (x :: S_ds)) (ExitHigh S_ds).

Definition LoopOS (N : nat) : Prop :=
  forall S_ds segs zl c k x cz_out,
    S_ds <> [1] -> SafeStack 43 S_ds ->
    ValidSegs40 segs zl ->
    2 <= c -> 1 <= k -> k <= 2 * c + 3 ->
    53 <= cz_out ->
    91 <= x ->
    2220 <= (c + fzOf segs zl) + 22 * x ->
    ChainLeadsUpTo N (mkSeg false segs zl c k 0 (x :: cz_out :: S_ds)) (ExitHigh S_ds).

Lemma fhigh_bundle (N : nat) : FHigh N /\ LoopHigh N /\ LoopOS N.
Proof.
  revert N; apply (nat_strong_ind (fun N => FHigh N /\ LoopHigh N /\ LoopOS N)); intros N IH.
  cbv delta [FHigh LoopHigh LoopOS] in IH.
  assert (HFH : FHigh N).
  { intros S_ds segs zl c k Hne1 HS Hv Hc Hk1 Hkc Hcz53 Hkz97.
    destruct HS as [HS_ne2 [HS_gd HS_all]].
    assert (HS : SafeStack 43 S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
    destruct segs as [|[z_0 m0] rest].
    - cbn [fzOf] in Hcz53, Hkz97.
      pose proof (proj2 Hv) as Hzl230.
      assert (Hg : stepGuards (mkSeg false [] zl c k 0 S_ds) = true).
      { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
        rewrite (goodPhiW_of_ge35 (phiW := c + zl - 1) HS_ne2 ltac:(lia)); cbn [andb]; unfold GoodPsi.
        replace (c + zl - 1 + 1) with (c + zl) by lia.
        exact (HS_all (c + zl) ltac:(lia)). }
      apply (chainLeadsUpTo_step1 Hg); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      apply chainLeadsUpTo_here; right.
      exists (c + zl), (k + 2 * zl + 2).
      split; [lia | split; [right; lia |]].
      replace (k + 2 * zl + 2) with ((k + 2 * zl + 2) + 0) at 1 by lia.
      exact (IsBounce_nil 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) ((c + zl) :: S_ds) ltac:(lia)).
    - pose proof (fzOf_ge_40 Hv) as Hz0_40; cbn [fzOf] in Hz0_40, Hcz53, Hkz97.
      pose proof (validSegs40_tail Hv) as Hv_rest.
      destruct m0 as [|m'].
      + assert (Hg1 : stepGuards (mkSeg false ((z_0, 0) :: rest) zl c k 0 S_ds) = true) by reflexivity.
        apply (chainLeadsUpTo_step Hg1); intros m1 Hm1.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct rest as [|[z_1 [|m1']] rest2].
        * pose proof (proj2 Hv_rest) as Hzl230.
          apply chainLeadsUpTo_here; left.
          exists (c + z_0 + 3 + zl); split; [lia | exact (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds ltac:(lia))].
        * pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
          pose proof (validSegs40_tail Hv_rest) as Hv_rest2.
          pose proof (fzOf_ge_40 Hv_rest2) as Hfz2_40.
          assert (Hg2 : stepGuards (mkSeg true ((z_1, 0) :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true)
            by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
          apply (chainLeadsUpTo_step Hg2); intros m2 Hm2.
          cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
          exact (proj1 (IH m2 ltac:(lia)) S_ds rest2 zl (c + z_0 + 3 + z_1 + 1) (k + 2 * z_0 + 3 + 2 * z_1 + 3)
            Hne1 HS Hv_rest2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        * pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
          pose proof (validSegs40_tail Hv_rest) as Hv_rest2.
          pose proof (fzOf_ge_40 Hv_rest2) as Hfz2_40.
          destruct (S m1' mod 2 =? 1) eqn:Em1_odd.
          -- destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
             ++ assert (Hg2 : stepGuards (mkSeg true ((z_1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                  rewrite Em1_odd, Emrg; exact (HS_all (c + z_0 + 3 + z_1) ltac:(lia)). }
                apply (chainLeadsUpTo_step Hg2); intros m2 Hm2.
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
                rewrite Em1_odd, Emrg.
                exact (proj1 (proj2 (IH m2 ltac:(lia))) S_ds rest2 zl ((k + 2 * z_0 + 3) + m1' + 2 * z_1 + 4) 1
                  (c + z_0 + 3 + z_1) Hne1 HS Hv_rest2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
             ++ apply chainLeadsUpTo_here; left.
                exists (c + z_0 + 3 + z_1); split; [lia |].
                apply (IsBounce_cons z_1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 S_ds Hv_rest2 ltac:(lia)).
                rewrite Em1_odd; lia.
          -- destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
             ++ assert (Hg2 : stepGuards (mkSeg true ((z_1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                  rewrite Em1_odd, Emrg; reflexivity. }
                apply (chainLeadsUpTo_step Hg2); intros m2 Hm2.
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
                rewrite Em1_odd, Emrg.
                exact (proj1 (IH m2 ltac:(lia)) S_ds rest2 zl (c + z_0 + 3 + z_1 + 2)
                  ((k + 2 * z_0 + 3) + S m1' + 2 * z_1 + 5)
                  Hne1 HS Hv_rest2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
             ++ apply chainLeadsUpTo_here; left.
                exists (c + z_0 + 3 + z_1); split; [lia |].
                apply (IsBounce_cons z_1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 S_ds Hv_rest2 ltac:(lia)).
                rewrite Em1_odd; lia.
      + pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
        pose proof (goodPhiW_of_ge35 (phiW := c + z_0 - 1) HS_ne2 ltac:(lia)) as Hphiw.
        destruct (S m' =? 1) eqn:Em1.
        * assert (m' = 0) by lia; subst m'.
          assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 S_ds) = true).
          { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
            rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (HS_all (c + z_0 + 1) ltac:(lia)). }
          apply (chainLeadsUpTo_step Hg); intros m1 Hm1.
          cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
          exact (proj1 (proj2 (IH m1 Hm1)) S_ds rest zl (k + 2 * z_0 + 4) 1 (c + z_0 + 1)
            Hne1 HS Hv_rest ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        * assert (Hpsi_cz : GoodPsi (c + z_0 - 1) S_ds = true).
          { unfold GoodPsi; replace (c + z_0 - 1 + 1) with (c + z_0) by lia.
            exact (HS_all (c + z_0) ltac:(lia)). }
          destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
          -- assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true).
             { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
               rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity. }
             apply (chainLeadsUpTo_step Hg); intros m1 Hm1.
             cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
             rewrite Em1, Eev_sm.
             exact (proj1 (proj2 (IH m1 Hm1)) S_ds rest zl (k + 2 * z_0 + 4) (S m' + 1) (c + z_0)
               Hne1 HS Hv_rest ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
          -- destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
             ++ pose proof (safeStack_cons_ne1 (x := c + z_0) Hne1 HS ltac:(lia) ltac:(lia)) as HS_cz.
                assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                  rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                  exact (proj2 (proj2 HS_cz) (k + 2 * z_0 + 2) ltac:(lia)). }
                apply (chainLeadsUpTo_step Hg); intros m1 Hm1.
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
                rewrite Em1, Eev_sm, Eod_sm.
                replace (S m' - 1) with m' by lia.
                exact (proj2 (proj2 (IH m1 Hm1)) S_ds rest zl m' 1 (k + 2 * z_0 + 2) (c + z_0)
                  Hne1 HS Hv_rest ltac:(lia) ltac:(lia) ltac:(lia) Hcz53 ltac:(lia) ltac:(lia)).
             ++ assert (Hm0_big : 2 * (k + 2 * z_0) + 12 <= S m')
                  by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
                assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true).
                { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                  rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity. }
                apply (chainLeadsUpTo_step1 Hg).
                cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
                rewrite Em1, Eev_sm, Eod_sm.
                replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                  by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
                apply chainLeadsUpTo_here; right.
                exists (c + z_0), (k + 2 * z_0 + 2).
                split; [lia | split; [left; split; [exact Hcz53 | lia] |]].
                replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
                apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest ((c + z_0) :: S_ds) Hv_rest ltac:(lia)).
                destruct (S (m' - 4) mod 2 =? 1); lia. }
  assert (HLH : LoopHigh N).
  { intros S_ds segs zl c k x Hne1 HS Hv Hc Hk1 Hkc Hx49 Hcz131.
    pose proof (fzOf_ge_40 Hv) as Hfz40.
    destruct (arith_lh_bounds Hc Hk1 Hkc Hfz40 Hcz131) as [Hox119 Hodw118].
    destruct HS as [HS_ne2 [HS_gd HS_all]].
    assert (HS : SafeStack 43 S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
    pose proof (safeStack_cons_ne1 (x := x) Hne1 HS ltac:(lia) ltac:(lia)) as HSx.
    pose proof (proj1 (excursion270_bundle N) 19 (x :: S_ds) segs zl c k ltac:(lia) HSx
      (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
    apply (chainLeadsUpTo_trans Hfb).
    intros m1 s_mid Hm1 [[phi [Hphi_odw Hb]] | [y [phi [Hy_ox [Hphi38 [_ Hb]]]]]].
    - apply chainLeadsUpTo_here; right.
      exists x, phi; split; [exact Hx49 | split; [right; lia | exact Hb]].
    - apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
        (HS_all (x - 1) ltac:(lia)) (fun _ => HS_all (x - 2) ltac:(lia))).
      + intros Hbig m3 _ p1 p2 Hvp _.
        apply chainLeadsUpTo_here; left; exists (x - 1); split; [lia | exact (isBounce_r9 (x := x) ltac:(lia) Hbig Hvp)].
      + intros Hy_le _ m2 Hm2 p1 p2 Hvp _.
        pose proof (fzOf_ge_40 Hvp) as Hfp40.
        exact (proj1 (IH m2 ltac:(lia)) S_ds p1 p2 (x + 1) (y + 2) Hne1 HS Hvp
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      + intros Hy_le _ m2 Hm2 p1 p2 Hvp _.
        pose proof (fzOf_ge_40 Hvp) as Hfp40.
        exact (proj1 (proj2 (IH m2 ltac:(lia))) S_ds p1 p2 y 1 (x - 1) Hne1 HS Hvp
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  split; [exact HFH | split; [exact HLH |]].
  intros S_ds segs zl c k x cz_out Hne1 HS Hv Hc Hk1 Hkc Hcz_out Hx91 Hpot.
  pose proof (fzOf_ge_40 Hv) as Hfz40.
  pose proof (proj1 (ox_bounds_relaxed (c := c) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia))) as Hox39.
  destruct HS as [HS_ne2 [HS_gd HS_all]].
  assert (HS : SafeStack 43 S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
  pose proof (safeStack_cons_ne1 (x := cz_out) Hne1 HS ltac:(lia) ltac:(lia)) as HS_cz.
  assert (Hne1_cz : (cz_out :: S_ds) <> [1]) by (intro H; inversion H; lia).
  pose proof (safeStack_cons_ne1 (x := x) Hne1_cz HS_cz ltac:(lia) ltac:(lia)) as HS_xcz.
  pose proof (proj1 (excursion270_bundle N) 19 (x :: cz_out :: S_ds) segs zl c k ltac:(lia) HS_xcz
    (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
  apply (chainLeadsUpTo_trans Hfb).
  intros m1 s_mid Hm1 [[phi [Hphi_odw Hb]] | [y [phi [Hy_ox [Hphi38 [Hyw Hb]]]]]].
  - assert (Hphi38 : 38 <= phi) by (rewrite odw_def in Hphi_odw; lia).
    apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
      (HS_all (cz_out - 1) ltac:(lia)) (fun _ => HS_all (cz_out - 2) ltac:(lia))).
    + intros Hbig m3 _ p1 p2 Hvp _.
      apply chainLeadsUpTo_here; left; exists (cz_out - 1); split; [lia | exact (isBounce_r9 (x := cz_out) ltac:(lia) Hbig Hvp)].
    + intros Hx_le _ m2 Hm2 p1 p2 Hvp _.
      pose proof (fzOf_ge_40 Hvp) as Hfp40.
      exact (proj1 (IH m2 ltac:(lia)) S_ds p1 p2 (cz_out + 1) (x + 2) Hne1 HS Hvp
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros Hx_le _ m2 Hm2 p1 p2 Hvp _.
      pose proof (fzOf_ge_40 Hvp) as Hfp40.
      exact (proj1 (proj2 (IH m2 ltac:(lia))) S_ds p1 p2 x 1 (cz_out - 1) Hne1 HS Hvp
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
      (proj2 (proj2 HS_cz) (x - 1) ltac:(lia)) (fun _ => proj2 (proj2 HS_cz) (x - 2) ltac:(lia))).
    + intros Hbig m3 _ p1 p2 Hvp _.
      apply chainLeadsUpTo_here; right.
      exists cz_out, (x - 1); split; [lia | split; [left; split; [exact Hcz_out | lia] | exact (isBounce_r9 (x := x) ltac:(lia) Hbig Hvp)]].
    + intros Hy_le _ m2 Hm2 p1 p2 Hvp _.
      pose proof (fzOf_ge_40 Hvp) as Hfp40.
      exact (proj1 (proj2 (IH m2 ltac:(lia))) S_ds p1 p2 (x + 1) (y + 2)
        cz_out Hne1 HS Hvp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros Hy_le _ m2 Hm2 p1 p2 Hvp Hfzp.
      destruct (arith_los_r11 Hc Hk1 Hkc Hfz40 Hx91 Hpot Hy_ox Hy_le Hphi38 Hyw Hfzp) as [Hy39 [Hx91' Hpot']].
      exact (proj2 (proj2 (IH m2 ltac:(lia))) S_ds p1 p2 y 1 (x - 1) cz_out Hne1 HS Hvp
        ltac:(lia) ltac:(lia) ltac:(lia) Hcz_out Hx91' Hpot').
Qed.



(* ========================================================================== *)
(* Section 5g.3b: Forced-R9, k=1 Boost, Odd-cz53 High Excursion & RootInv270  *)
(* ========================================================================== *)

Lemma chainLeads_trans {s : SegState} {P Q : SegState -> Prop}
    (H1 : ChainLeads s P) (H2 : forall s', P s' -> ChainLeads s' Q) :
  ChainLeads s Q.
Proof.
  intro N; exact (chainLeadsUpTo_trans (H1 N) (fun m s' _ Hp => H2 s' Hp m)).
Qed.

Lemma fbound_force_r9 {N x d3 : nat} {ds3 : list nat} {segs : list (nat * nat)} {zl c k : nat}
    {P : SegState -> Prop}
    (Hx19 : 19 <= x)
    (Hgx : GoodDs (x :: d3 :: ds3) = true)
    (Hg_pop1 : GoodDs ((x - 1) :: d3 :: ds3) = true)
    (Hv : ValidSegs40 segs zl)
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hcz42 : 42 <= c + fzOf segs zl)
    (Hox : 2 * x + 7 <= ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
    (Hcont1 : forall m phi, m <= N -> 2 * x + 6 <= phi -> forall s',
      IsBounce phi (x :: d3 :: ds3) s' -> ChainLeadsUpTo m s' P)
    (Hcont2 : forall m, m < N -> forall s',
      IsBounce (x - 1) (d3 :: ds3) s' -> ChainLeadsUpTo m s' P) :
  ChainLeadsUpTo N (mkSeg false segs zl c k 0 (x :: d3 :: ds3)) P.
Proof.
  pose proof (fzOf_ge_40 Hv) as Hfz40.
  pose proof (safeStack_of_gt2d2 (m := 2 * x + 5) (d2 := x) (d3 := d3) (ds3 := ds3) ltac:(lia) (Nat.le_refl _) ltac:(lia) Hgx) as HS.
  pose proof (proj1 (excursion270_bundle N) (2 * x + 5) (x :: d3 :: ds3) segs zl c k
    ltac:(lia) HS (validTail40_of_validSegs40 Hv) Hc Hk1 Hkc
    ltac:(lia) Hcz42 ltac:(lia) ltac:(lia)) as Hfb.
  apply (chainLeadsUpTo_trans Hfb).
  intros m1 s_mid Hm1 [[phi [Hphi_odw Hb]] | [y [phi [Hy_ox [Hphi38 [_ Hb]]]]]].
  - assert (Hphi_ge : 2 * x + 6 <= phi) by (rewrite odw_def in Hphi_odw; lia).
    exact (Hcont1 m1 phi Hm1 Hphi_ge s_mid Hb).
  - apply (amega_pop_step Hb Hphi38 ltac:(lia) Hx19 Hg_pop1 (fun H => ltac:(lia))).
    + intros Hbig m2 Hm2 p1 p2 Hvp ?.
      exact (Hcont2 m2 ltac:(lia) _ (isBounce_r9 (x := x) (y := y) Hx19 Hbig Hvp)).
    + intros Hle; exfalso; lia.
    + intros Hle; exfalso; lia.
Qed.

Local Transparent ox odw oxw.
Lemma arith_boost_c85 {c k fz : nat}
    (Hc : 85 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz) :
  114 <= ox (k + 2 * fz) (c + fz) /\ 113 <= odw (k + 2 * fz) (c + fz) /\
  165 <= oxw (k + 2 * fz) (c + fz).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * fz) (c + fz)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  unfold odw; rewrite (Hox1 ltac:(lia)), Hoxw1; lia.
Qed.

Lemma arith_boost_r10 {c k fz : nat}
    (Hc : 43 <= c) (Hk : 72 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz) :
  73 <= ox (k + 2 * fz) (c + fz) /\ 72 <= odw (k + 2 * fz) (c + fz) /\
  126 <= oxw (k + 2 * fz) (c + fz).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * fz) (c + fz)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  unfold odw; rewrite (Hox1 ltac:(lia)), Hoxw1; lia.
Qed.

Lemma arith_boost_cz {c fz cz_lo ox_lo : nat}
    (Hc : 2 <= c) (Hfz : 40 <= fz) (Hcz : cz_lo <= c + fz)
    (H : (cz_lo = 109 /\ ox_lo = 99) \/ (cz_lo = 118 /\ ox_lo = 107) \/
         (cz_lo = 148 /\ ox_lo = 134) \/ (cz_lo = 154 /\ ox_lo = 140)) :
  ox_lo <= ox (1 + 2 * fz) (c + fz).
Proof.
  destruct (ox_spec_lt (kz := 1 + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  rewrite (Hox1 ltac:(lia)); lia.
Qed.
Local Opaque ox odw oxw.

Lemma fbound_k1_boost {N d2 : nat} {ds2 : list nat} {segs : list (nat * nat)} {zl c1 : nat}
    (Hne1 : (d2 :: ds2) <> [1]) (HS1 : SafeStack 19 (d2 :: ds2))
    (Hv : ValidSegs40 segs zl) (Hc1 : 2 <= c1) :
  ChainLeadsUpTo N (mkSeg false segs zl c1 1 0 (d2 :: ds2)) (Exit270 39 38 107 (d2 :: ds2)).
Proof.
  destruct HS1 as [HS1_ne2 [HS1_gd HS1_all]].
  assert (HS1 : SafeStack 19 (d2 :: ds2)) by exact (conj HS1_ne2 (conj HS1_gd HS1_all)).
  destruct segs as [|[z1 m1] rest1].
  - pose proof (proj2 Hv) as Hzl230.
    assert (Hg : stepGuards (mkSeg false [] zl c1 1 0 (d2 :: ds2)) = true).
    { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
      rewrite (goodPhiW_of_ge35 (phiW := c1 + zl - 1) HS1_ne2 ltac:(lia)); cbn [andb]; unfold GoodPsi.
      replace (c1 + zl - 1 + 1) with (c1 + zl) by lia.
      exact (HS1_all (c1 + zl) ltac:(lia)). }
    apply (chainLeadsUpTo_step1 Hg); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    apply chainLeadsUpTo_here; right.
    exists (c1 + zl), (1 + 2 * zl + 2).
    split; [lia | split; [lia | split; [lia |]]].
    replace (1 + 2 * zl + 2) with ((1 + 2 * zl + 2) + 0) at 1 by lia.
    exact (IsBounce_nil 0 (1 + 2 * zl + 2) 0 (2 * (1 + 2 * zl) + 6) ((c1 + zl) :: d2 :: ds2) ltac:(lia)).
  - pose proof (fzOf_ge_40 Hv) as Hz1_40; cbn [fzOf] in Hz1_40.
    pose proof (validSegs40_tail Hv) as Hv_r1.
    destruct m1 as [|m'].
    + assert (Hg1 : stepGuards (mkSeg false ((z1, 0) :: rest1) zl c1 1 0 (d2 :: ds2)) = true) by reflexivity.
      apply (chainLeadsUpTo_step Hg1); intros m_a Hm_a.
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      destruct rest1 as [|[z2 [|m2']] rest2].
      * pose proof (proj2 Hv_r1) as Hzl230.
        apply chainLeadsUpTo_here; left.
        exists (c1 + z1 + 3 + zl); split; [lia | exact (IsBounce_nil zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) (d2 :: ds2) ltac:(lia))].
      * pose proof (fzOf_ge_40 Hv_r1) as Hz2_40; cbn [fzOf] in Hz2_40.
        pose proof (validSegs40_tail Hv_r1) as Hv_r2.
        pose proof (fzOf_ge_40 Hv_r2) as Hfz3_40.
        assert (Hg2 : stepGuards (mkSeg true ((z2, 0) :: rest2) zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) (d2 :: ds2)) = true)
          by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
        apply (chainLeadsUpTo_step Hg2); intros m_b Hm_b.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct (arith_boost_c85 (c := c1 + z1 + 3 + z2 + 1) (k := 1 + 2 * z1 + 3 + 2 * z2 + 3)
          (fz := fzOf rest2 zl) ltac:(lia) ltac:(lia) ltac:(lia) Hfz3_40) as [Hb1 [Hb2 Hb3]].
        exact (chainLeadsUpTo_imp
          (proj1 (excursion270_bundle m_b) 19 (d2 :: ds2) rest2 zl
            (c1 + z1 + 3 + z2 + 1) (1 + 2 * z1 + 3 + 2 * z2 + 3) ltac:(lia) HS1
            (validTail40_of_validSegs40 Hv_r2) ltac:(lia) ltac:(lia) ltac:(lia)
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          (fun _ He => exit270_mono (tx1 := 39) (tdw1 := 38) (txw1 := 107) He ltac:(lia) ltac:(lia) ltac:(lia))).
      * pose proof (fzOf_ge_40 Hv_r1) as Hz2_40; cbn [fzOf] in Hz2_40.
        pose proof (validSegs40_tail Hv_r1) as Hv_r2.
        pose proof (fzOf_ge_40 Hv_r2) as Hfz3_40.
        destruct (S m2' mod 2 =? 1) eqn:Em2_od.
        -- destruct ((1 + 2 * z1 + 3) + m2' <=? 2 * (c1 + z1) + 8) eqn:Emrg.
           ++ assert (Hg2 : stepGuards (mkSeg true ((z2, S m2') :: rest2) zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) (d2 :: ds2)) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                rewrite Em2_od, Emrg; exact (HS1_all (c1 + z1 + 3 + z2) ltac:(lia)). }
              apply (chainLeadsUpTo_step Hg2); intros m_b Hm_b.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
              rewrite Em2_od, Emrg.
              exact (proj2 (excursion270_bundle m_b) 19 (d2 :: ds2) rest2 zl
                ((1 + 2 * z1 + 3) + m2' + 2 * z2 + 4) 1 (c1 + z1 + 3 + z2) 39 107
                ltac:(lia) HS1 (or_introl Hne1) Hv_r2
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
           ++ apply chainLeadsUpTo_here; left.
              exists (c1 + z1 + 3 + z2); split; [lia |].
              apply (IsBounce_cons z2 m2' zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) rest2 (d2 :: ds2) Hv_r2 ltac:(lia)).
              rewrite Em2_od; lia.
        -- destruct ((1 + 2 * z1 + 3) + S m2' <=? 2 * (c1 + z1) + 8) eqn:Emrg.
           ++ assert (Hg2 : stepGuards (mkSeg true ((z2, S m2') :: rest2) zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) (d2 :: ds2)) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                rewrite Em2_od, Emrg; reflexivity. }
              apply (chainLeadsUpTo_step Hg2); intros m_b Hm_b.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
              rewrite Em2_od, Emrg.
              destruct (arith_boost_c85 (c := c1 + z1 + 3 + z2 + 2)
                (k := (1 + 2 * z1 + 3) + S m2' + 2 * z2 + 5)
                (fz := fzOf rest2 zl) ltac:(lia) ltac:(lia) ltac:(lia) Hfz3_40) as [Hb1 [Hb2 Hb3]].
              exact (chainLeadsUpTo_imp
                (proj1 (excursion270_bundle m_b) 19 (d2 :: ds2) rest2 zl
                  (c1 + z1 + 3 + z2 + 2) ((1 + 2 * z1 + 3) + S m2' + 2 * z2 + 5)
                  ltac:(lia) HS1 (validTail40_of_validSegs40 Hv_r2)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                (fun _ He => exit270_mono (tx1 := 39) (tdw1 := 38) (txw1 := 107) He ltac:(lia) ltac:(lia) ltac:(lia))).
           ++ apply chainLeadsUpTo_here; left.
              exists (c1 + z1 + 3 + z2); split; [lia |].
              apply (IsBounce_cons z2 m2' zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) rest2 (d2 :: ds2) Hv_r2 ltac:(lia)).
              rewrite Em2_od; lia.
    + pose proof (fzOf_ge_40 Hv_r1) as Hfz2_40.
      pose proof (goodPhiW_of_ge35 (phiW := c1 + z1 - 1) HS1_ne2 ltac:(lia)) as Hphiw.
      assert (H_push85 : forall m_b x0 k', 42 <= x0 -> 1 <= k' -> k' <= 2 * (1 + 2 * z1 + 4) + 3 ->
        ChainLeadsUpTo m_b (mkSeg false rest1 zl (1 + 2 * z1 + 4) k' 0 (x0 :: d2 :: ds2))
          (Exit270 39 38 107 (d2 :: ds2))).
      { intros m_b x0 k' Hx0 Hk'1 Hk'c.
        destruct (67 <=? x0) eqn:Ex67.
        - exact (proj2 (excursion270_bundle m_b) 19 (d2 :: ds2) rest1 zl (1 + 2 * z1 + 4) k' x0 39 107
            ltac:(lia) HS1 (or_introl Hne1) Hv_r1 ltac:(lia) Hk'1 Hk'c ltac:(lia) ltac:(lia)
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        - destruct (arith_boost_c85 (c := 1 + 2 * z1 + 4) (k := k') (fz := fzOf rest1 zl)
            ltac:(lia) Hk'1 Hk'c Hfz2_40) as [Hb1 [Hb2 Hb3]].
          pose proof (safeStack_cons_ne1 (x := x0) Hne1 HS1 ltac:(lia) ltac:(lia)) as HSx0.
          pose proof (proj1 (excursion270_bundle m_b) 19 (x0 :: d2 :: ds2) rest1 zl
            (1 + 2 * z1 + 4) k' ltac:(lia) HSx0 (validTail40_of_validSegs40 Hv_r1)
            ltac:(lia) Hk'1 Hk'c ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb1.
          apply (chainLeadsUpTo_trans Hfb1).
          intros m_c s_mid Hm_c [[phi [Hphi Hb]] | [y [phi [Hy_ox [Hphi38 [Hyw Hb]]]]]].
          + apply chainLeadsUpTo_here; right.
            exists x0, phi; split; [lia | split; [lia | split; [lia | exact Hb]]].
          + apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
              (HS1_all (x0 - 1) ltac:(lia)) (fun _ => HS1_all (x0 - 2) ltac:(lia))).
            * intros Hbig m_d ? p1 p2 Hvp ?.
              apply chainLeadsUpTo_here; left; exists (x0 - 1); split; [lia | exact (isBounce_r9 (x := x0) (y := y) ltac:(lia) Hbig Hvp)].
            * intros ? ? m_d Hm_d p1 p2 Hvp ?.
              pose proof (fzOf_ge_40 Hvp) as Hfp.
              destruct (arith_boost_r10 (c := x0 + 1) (k := y + 2) (fz := fzOf p1 p2)
                ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hr1 [Hr2 Hr3]].
              exact (chainLeadsUpTo_imp
                (proj1 (excursion270_bundle m_d) 19 (d2 :: ds2) p1 p2 (x0 + 1) (y + 2)
                  ltac:(lia) HS1 (validTail40_of_validSegs40 Hvp)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                (fun _ He => exit270_mono (tx1 := 39) (tdw1 := 38) (txw1 := 107) He ltac:(lia) ltac:(lia) ltac:(lia))).
            * intros Hy_le ? m_d Hm_d p1 p2 Hvp ?.
              pose proof (fzOf_ge_40 Hvp) as Hfp.
              pose proof (arith_boost_cz (c := y) (fz := fzOf p1 p2) (cz_lo := 154) (ox_lo := 140)
                ltac:(lia) Hfp ltac:(lia) ltac:(right; right; right; split; reflexivity)) as Hox140.
              apply (fbound_force_r9 (x := x0 - 1) (d3 := d2) (ds3 := ds2) (c := y) (k := 1) ltac:(lia)
                (HS1_all (x0 - 1) ltac:(lia)) (HS1_all (x0 - 1 - 1) ltac:(lia)) Hvp
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
              -- intros m_e phi2 ? Hphi2 s_e Hbc2.
                 apply chainLeadsUpTo_here; right; exists (x0 - 1), phi2; split; [lia | split; [lia | split; [lia | exact Hbc2]]].
              -- intros m_e ? s_e Hbc2.
                 replace (x0 - 1 - 1) with (x0 - 2) in Hbc2 by lia.
                 apply chainLeadsUpTo_here; left; exists (x0 - 2); split; [lia | exact Hbc2]. }
      destruct (S m' =? 1) eqn:Em1.
      * assert (m' = 0) by lia; subst m'.
        assert (Hg : stepGuards (mkSeg false ((z1, 1) :: rest1) zl c1 1 0 (d2 :: ds2)) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
          rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (HS1_all (c1 + z1 + 1) ltac:(lia)). }
        apply (chainLeadsUpTo_step Hg); intros m_b Hm_b.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
        exact (H_push85 m_b (c1 + z1 + 1) 1 ltac:(lia) ltac:(lia) ltac:(lia)).
      * assert (Hpsi_cz : GoodPsi (c1 + z1 - 1) (d2 :: ds2) = true).
        { unfold GoodPsi; replace (c1 + z1 - 1 + 1) with (c1 + z1) by lia.
          exact (HS1_all (c1 + z1) ltac:(lia)). }
        destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (1 + 2 * z1) + 10)) eqn:Eev_sm.
        -- assert (Hg : stepGuards (mkSeg false ((z1, S m') :: rest1) zl c1 1 0 (d2 :: ds2)) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
             rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity. }
           apply (chainLeadsUpTo_step Hg); intros m_b Hm_b.
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
           rewrite Em1, Eev_sm.
           exact (H_push85 m_b (c1 + z1) (S m' + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
        -- destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (1 + 2 * z1) + 11)) eqn:Eod_sm.
           ++ pose proof (safeStack_cons_ne1 (x := c1 + z1) Hne1 HS1 ltac:(lia) ltac:(lia)) as HS_cz.
              assert (Hg : stepGuards (mkSeg false ((z1, S m') :: rest1) zl c1 1 0 (d2 :: ds2)) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                exact (proj2 (proj2 HS_cz) (1 + 2 * z1 + 2) ltac:(lia)). }
              apply (chainLeadsUpTo_step Hg); intros m_b Hm_b.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
              rewrite Em1, Eev_sm, Eod_sm.
              assert (Hm'1 : 1 <= m') by (clear - Em1; lia).
              assert (Hm'_od_le : S m' mod 2 = 1 /\ S m' <= 2 * (1 + 2 * z1) + 11) by (clear - Eod_sm; lia).
              clear Hg Hphiw Hpsi_cz Em1 Eev_sm Eod_sm.
              replace (S m' - 1) with m' by lia.
              destruct (div10_spec (1 + 2 * z1)) as [q10 [r10 [Hr10 [Hkz10 Hdw10]]]].
              assert (Hne1_cz : ((c1 + z1) :: d2 :: ds2) <> [1]) by (intro H; inversion H; lia).
              pose proof (proj2 (excursion270_bundle m_b) 19 ((c1 + z1) :: d2 :: ds2) rest1 zl
                m' 1 (1 + 2 * z1 + 2) (9 * q10 - 2) (1 + 2 * z1 + 35)
                ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_r1
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as Hl1; clear Hdw10.
              apply (chainLeadsUpTo_trans Hl1).
              intros m_c s_mid Hm_c [[phi0 [Hphi0 Hb0]] | [y0 [phi0 [Hy0 [Hphi0_38 [Hyw0 Hb0]]]]]].
              ** apply chainLeadsUpTo_here; right.
                 exists (c1 + z1), phi0; split; [lia | split; [lia | split; [lia | exact Hb0]]].
              ** apply (amega_pop_step Hb0 Hphi0_38 ltac:(lia) ltac:(lia)
                   (HS1_all (c1 + z1 - 1) ltac:(lia)) (fun _ => HS1_all (c1 + z1 - 2) ltac:(lia))).
                 --- intros Hbig m_d ? p1 p2 Hvp ?.
                     apply chainLeadsUpTo_here; left; exists (c1 + z1 - 1); split; [lia | exact (isBounce_r9 (x := c1 + z1) (y := y0) ltac:(lia) Hbig Hvp)].
                 --- intros ? ? m_d Hm_d p1 p2 Hvp ?.
                     pose proof (fzOf_ge_40 Hvp) as Hfp.
                     destruct (arith_boost_r10 (c := c1 + z1 + 1) (k := y0 + 2) (fz := fzOf p1 p2)
                       ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hr1 [Hr2 Hr3]].
                     exact (chainLeadsUpTo_imp
                       (proj1 (excursion270_bundle m_d) 19 (d2 :: ds2) p1 p2 (c1 + z1 + 1) (y0 + 2)
                         ltac:(lia) HS1 (validTail40_of_validSegs40 Hvp)
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                       (fun _ He => exit270_mono (tx1 := 39) (tdw1 := 38) (txw1 := 107) He ltac:(lia) ltac:(lia) ltac:(lia))).
                 --- intros Hy0_le ? m_d Hm_d p1 p2 Hvp Hfzp.
                     pose proof (fzOf_ge_40 Hvp) as Hfp.
                     destruct (62 <=? c1 + z1 - 1) eqn:Ex62.
                     +++ exact (proj2 (excursion270_bundle m_d) 19 (d2 :: ds2) p1 p2 y0 1 (c1 + z1 - 1) 39 107
                           ltac:(lia) HS1 (or_introl Hne1) Hvp
                           ltac:(lia) ltac:(lia) ltac:(lia)
                           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
                     +++ set (x0 := c1 + z1 - 3).
                         replace (c1 + z1 - 1) with (x0 + 2) in * by (unfold x0; lia).
                         assert (Hx0_lo : 39 <= x0) by (unfold x0; lia).
                         assert (Hx0_hi : x0 <= 59) by lia.
                         pose proof (arith_boost_cz (c := y0) (fz := fzOf p1 p2)
                           (cz_lo := 118) (ox_lo := 107) ltac:(lia) Hfp
                           ltac:(lia) ltac:(right; left; split; reflexivity)) as Hox107.
                         pose proof (safeStack_cons_ne1 (x := x0 + 2) Hne1 HS1 ltac:(lia) ltac:(lia)) as HSx'.
                         pose proof (proj1 (excursion270_bundle m_d) 19 ((x0 + 2) :: d2 :: ds2)
                           p1 p2 y0 1 ltac:(lia) HSx' (validTail40_of_validSegs40 Hvp)
                           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb2.
                         apply (chainLeadsUpTo_trans Hfb2).
                         intros m_e s_m2 Hm_e [[phi2 [Hphi2 Hb2]] | [y2 [phi2 [Hy2_ox [Hphi2_38 [_ Hb2]]]]]].
                         *** assert (Hphi2_106 : 106 <= phi2) by (rewrite odw_def in Hphi2; lia).
                             apply chainLeadsUpTo_here; right.
                             exists (x0 + 2), phi2; split; [lia | split; [lia | split; [lia | exact Hb2]]].
                         *** apply (amega_pop_step Hb2 Hphi2_38 ltac:(lia) ltac:(lia)
                               (HS1_all (x0 + 2 - 1) ltac:(lia)) (fun _ => HS1_all (x0 + 2 - 2) ltac:(lia))).
                             ---- intros Hbig m_f ? q1 q2 Hvq ?.
                                  apply chainLeadsUpTo_here; left; exists (x0 + 1); split; [lia |].
                                  replace (x0 + 1) with (x0 + 2 - 1) by lia.
                                  exact (isBounce_r9 (x := x0 + 2) (y := y2) ltac:(lia) Hbig Hvq).
                             ---- intros ? ? m_f Hm_f q1 q2 Hvq ?.
                                  pose proof (fzOf_ge_40 Hvq) as Hfq.
                                  destruct (arith_boost_r10 (c := x0 + 2 + 1) (k := y2 + 2) (fz := fzOf q1 q2)
                                    ltac:(lia) ltac:(lia) ltac:(lia) Hfq) as [Hr1 [Hr2 Hr3]].
                                  exact (chainLeadsUpTo_imp
                                    (proj1 (excursion270_bundle m_f) 19 (d2 :: ds2) q1 q2 (x0 + 2 + 1) (y2 + 2)
                                      ltac:(lia) HS1 (validTail40_of_validSegs40 Hvq)
                                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                                    (fun _ He => exit270_mono (tx1 := 39) (tdw1 := 38) (txw1 := 107) He ltac:(lia) ltac:(lia) ltac:(lia))).
                             ---- intros Hy2_le ? m_f Hm_f q1 q2 Hvq ?.
                                  replace (x0 + 2 - 1) with (x0 + 1) by lia.
                                  pose proof (fzOf_ge_40 Hvq) as Hfq.
                                  pose proof (arith_boost_cz (c := y2) (fz := fzOf q1 q2)
                                    (cz_lo := 148) (ox_lo := 134) ltac:(lia) Hfq ltac:(lia)
                                    ltac:(right; right; left; split; reflexivity)) as Hox134.
                                  apply (fbound_force_r9 (x := x0 + 1) (d3 := d2) (ds3 := ds2) (c := y2) (k := 1) ltac:(lia)
                                    (HS1_all (x0 + 1) ltac:(lia)) (HS1_all (x0 + 1 - 1) ltac:(lia)) Hvq
                                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
                                  ++++ intros m_g phi3 ? Hphi3 s_g Hb3.
                                       apply chainLeadsUpTo_here; right; exists (x0 + 1), phi3; split; [lia | split; [lia | split; [lia | exact Hb3]]].
                                  ++++ intros m_g ? s_g Hb3.
                                       replace (x0 + 1 - 1) with x0 in Hb3 by lia.
                                       apply chainLeadsUpTo_here; left; exists x0; split; [lia | exact Hb3].
           ++ assert (Hm1_big : 2 * (1 + 2 * z1) + 12 <= S m')
                by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
              assert (Hg : stepGuards (mkSeg false ((z1, S m') :: rest1) zl c1 1 0 (d2 :: ds2)) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity. }
              apply (chainLeadsUpTo_step1 Hg).
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
              rewrite Em1, Eev_sm, Eod_sm.
              replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
              apply chainLeadsUpTo_here; right.
              exists (c1 + z1), (1 + 2 * z1 + 2).
              split; [lia | split; [lia | split; [lia |]]].
              replace (1 + 2 * z1 + 2) with ((1 + 2 * z1 + 2) + 0) at 1 by lia.
              apply (IsBounce_cons 0 (m' - 4) zl (1 + 2 * z1 + 2) 0 (2 * (1 + 2 * z1) + 6) rest1 ((c1 + z1) :: d2 :: ds2) Hv_r1 ltac:(lia)).
              destruct (S (m' - 4) mod 2 =? 1); lia.
Qed.

Lemma loop_k1_le47 {N x1 d3 : nat} {ds3 : list nat} {segs : list (nat * nat)} {zl c1 : nat}
    {P : SegState -> Prop}
    (Hne1_0 : (d3 :: ds3) <> [1])
    (HS0 : SafeStack 21 (d3 :: ds3))
    (Hx_lo : 23 <= x1 \/ (x1 = 21 /\ SafeStack 19 (d3 :: ds3)))
    (Hx_hi : x1 <= 47)
    (Hv : ValidSegs40 segs zl) (Hc1 : 2 <= c1)
    (H_top : forall m z phi, m <= N -> (z = x1 \/ z = x1 - 1) -> 38 <= phi -> forall s',
      IsBounce phi (z :: d3 :: ds3) s' -> ChainLeadsUpTo m s' P)
    (H_b1 : forall m, m < N -> forall s', IsBounce (x1 - 1) (d3 :: ds3) s' -> ChainLeadsUpTo m s' P)
    (H_b2 : forall m, m < N -> forall s', IsBounce (x1 - 2) (d3 :: ds3) s' -> ChainLeadsUpTo m s' P)
    (H_r10 : forall m c' k' p1 p2, m < N -> c' = x1 + 1 -> 41 <= k' -> k' <= 2 * c' + 3 ->
      ValidSegs40 p1 p2 -> ChainLeadsUpTo m (mkSeg false p1 p2 c' k' 0 (d3 :: ds3)) P) :
  ChainLeadsUpTo N (mkSeg false segs zl c1 1 0 (x1 :: d3 :: ds3)) P.
Proof.
  assert (Hx21 : 21 <= x1) by (destruct Hx_lo as [? | [-> _]]; lia).
  assert (HS1 : SafeStack 19 (x1 :: d3 :: ds3)).
  { destruct Hx_lo as [H23 | [-> H19]];
      [exact (safeStack_cons_ne1 (x := x1) Hne1_0 HS0 ltac:(lia) ltac:(lia))
      |exact (safeStack_cons_ne1 (x := 21) Hne1_0 H19 ltac:(lia) ltac:(lia))]. }
  assert (Hg_x1_1 : GoodDs ((x1 - 1) :: d3 :: ds3) = true).
  { destruct Hx_lo as [H23 | [-> H19]];
      [exact (proj2 (proj2 HS0) (x1 - 1) ltac:(lia))
      |exact (proj2 (proj2 H19) 20 ltac:(lia))]. }
  assert (Hg_x1_2 : GoodDs ((x1 - 2) :: d3 :: ds3) = true).
  { destruct Hx_lo as [H23 | [-> H19]];
      [exact (proj2 (proj2 HS0) (x1 - 2) ltac:(lia))
      |exact (proj2 (proj2 H19) 19 ltac:(lia))]. }
  assert (Hne1_1 : (x1 :: d3 :: ds3) <> [1]) by (intro H; inversion H).
  pose proof (fbound_k1_boost (N := N) Hne1_1 HS1 Hv Hc1) as Hb.
  apply (chainLeadsUpTo_trans Hb).
  intros m1 s_mid Hm1 [[phi [Hphi38 Hsb]] | [y1 [phi1 [Hy1_39 [Hphi1_38 [Hyw1 Hsb]]]]]].
  - exact (H_top m1 x1 phi Hm1 (or_introl eq_refl) Hphi38 s_mid Hsb).
  - apply (amega_pop_step Hsb Hphi1_38 ltac:(lia) ltac:(lia) Hg_x1_1 (fun _ => Hg_x1_2)).
    + intros Hbig m2 Hm2 p1 p2 Hvp ?.
      exact (H_b1 m2 ltac:(lia) _ (isBounce_r9 (x := x1) (y := y1) ltac:(lia) Hbig Hvp)).
    + intros ? ? m2 Hm2 p1 p2 Hvp ?.
      exact (H_r10 m2 (x1 + 1) (y1 + 2) p1 p2 ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Hvp).
    + intros Hy1_le ? m2 Hm2 p1 p2 Hvp Hfzp.
      pose proof (fzOf_ge_40 Hvp) as Hfp.
      pose proof (arith_boost_cz (c := y1) (fz := fzOf p1 p2) (cz_lo := 109) (ox_lo := 99)
        ltac:(lia) Hfp ltac:(lia) ltac:(left; split; reflexivity)) as Hox99.
      assert (Hg_x1_11 : GoodDs ((x1 - 1 - 1) :: d3 :: ds3) = true)
        by (replace (x1 - 1 - 1) with (x1 - 2) by lia; exact Hg_x1_2).
      apply (fbound_force_r9 (x := x1 - 1) (d3 := d3) (ds3 := ds3) (c := y1) (k := 1) ltac:(lia)
        Hg_x1_1 Hg_x1_11 Hvp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      * intros m3 phi2 Hm3 Hphi2 s' Hb2.
        exact (H_top m3 (x1 - 1) phi2 ltac:(lia) (or_intror eq_refl) ltac:(lia) s' Hb2).
      * intros m3 Hm3 s' Hb2.
        replace (x1 - 1 - 1) with (x1 - 2) in Hb2 by lia.
        exact (H_b2 m3 ltac:(lia) s' Hb2).
Qed.

(* ========================================================================== *)
(* Odd-cz53 High Excursion Extension (`ExitHighExt`, `loopOS_odd`, `fhigh_ext`) *)
(* ========================================================================== *)

Definition ExitHighExt (S_ds : list nat) (s : SegState) : Prop :=
  ExitHigh S_ds s \/ (exists y phi, 53 <= y /\ y mod 2 = 1 /\ 88 <= phi /\ IsBounce phi (y :: S_ds) s).

Lemma arith_los_odd_r11 {c k fz x y phi fz3 : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz)
    (Hx : 89 <= x) (Hpot : 2079 <= (c + fz) + 21 * x)
    (Hy_lo : ox (k + 2 * fz) (c + fz) <= y) (Hy_hi : y <= 2 * x + 4)
    (Hphi38 : 38 <= phi) (Hyw : oxw (k + 2 * fz) (c + fz) <= y + phi)
    (Hfz3 : phi + 2 <= fz3) :
  39 <= y /\ 89 <= x - 1 /\ 2079 <= (y + fz3) + 21 * (x - 1).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
  destruct (oxw_spec (k + 2 * fz) (c + fz)) as [qw1 [rw1 [Hrw1 [Hkw1 Hoxw1]]]].
  rewrite (Hox1 ltac:(lia)) in Hy_lo; rewrite Hoxw1 in Hyw; lia.
Qed.

Lemma loopOS_odd (N : nat) :
  forall S_ds segs zl c k x cz_out,
    S_ds <> [1] -> SafeStack 43 S_ds -> ValidSegs40 segs zl ->
    2 <= c -> 1 <= k -> k <= 2 * c + 3 ->
    53 <= cz_out -> cz_out mod 2 = 1 ->
    89 <= x -> 2079 <= (c + fzOf segs zl) + 21 * x ->
    ChainLeadsUpTo N (mkSeg false segs zl c k 0 (x :: cz_out :: S_ds)) (ExitHighExt S_ds).
Proof.
  revert N; apply (nat_strong_ind (fun N =>
    forall S_ds segs zl c k x cz_out,
      S_ds <> [1] -> SafeStack 43 S_ds -> ValidSegs40 segs zl ->
      2 <= c -> 1 <= k -> k <= 2 * c + 3 ->
      53 <= cz_out -> cz_out mod 2 = 1 ->
      89 <= x -> 2079 <= (c + fzOf segs zl) + 21 * x ->
      ChainLeadsUpTo N (mkSeg false segs zl c k 0 (x :: cz_out :: S_ds)) (ExitHighExt S_ds))).
  intros N IH S_ds segs zl c k x cz_out Hne1 HS Hv Hc Hk1 Hkc Hcz_out Hcz_odd Hx89 Hpot.
  pose proof (fzOf_ge_40 Hv) as Hfz40.
  pose proof (proj1 (ox_bounds_relaxed (c := c) (k := k) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia))) as Hox39.
  destruct HS as [HS_ne2 [HS_gd HS_all]].
  assert (HS : SafeStack 43 S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
  pose proof (safeStack_cons_ne1 (x := cz_out) Hne1 HS ltac:(lia) ltac:(lia)) as HS_cz.
  assert (Hne1_cz : (cz_out :: S_ds) <> [1]) by (intro H; inversion H; lia).
  pose proof (safeStack_cons_ne1 (x := x) Hne1_cz HS_cz ltac:(lia) ltac:(lia)) as HS_xcz.
  pose proof (proj1 (excursion270_bundle N) 19 (x :: cz_out :: S_ds) segs zl c k ltac:(lia) HS_xcz
    (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
  apply (chainLeadsUpTo_trans Hfb).
  intros m1 s_mid Hm1 [[phi [Hphi_odw Hb]] | [y [phi [Hy_ox [Hphi38 [Hyw Hb]]]]]].
  - destruct (ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) ltac:(lia))
      as [q0 [r0 [Hr0 [Heq0 Hox0]]]].
    rewrite odw_def, (Hox0 ltac:(lia)) in Hphi_odw.
    assert (Hphi38 : 38 <= phi) by lia.
    apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
      (HS_all (cz_out - 1) ltac:(lia)) (fun _ => HS_all (cz_out - 2) ltac:(lia))).
    + intros Hbig m2 ? p1 p2 Hvp ?.
      apply chainLeadsUpTo_here; left; left; exists (cz_out - 1); split; [lia | exact (isBounce_r9 (x := cz_out) (y := x) ltac:(lia) Hbig Hvp)].
    + intros ? ? m2 Hm2 p1 p2 Hvp ?.
      pose proof (fzOf_ge_40 Hvp) as Hfp.
      exact (chainLeadsUpTo_imp
        (proj1 (fhigh_bundle m2) S_ds p1 p2 (cz_out + 1) (x + 2) Hne1 HS Hvp
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        (fun _ He => or_introl He)).
    + intros ? ? m2 Hm2 p1 p2 Hvp Hfzp.
      pose proof (fzOf_ge_40 Hvp) as Hfp.
      exact (chainLeadsUpTo_imp
        (proj1 (proj2 (fhigh_bundle m2)) S_ds p1 p2 x 1 (cz_out - 1) Hne1 HS Hvp
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        (fun _ He => or_introl He)).
  - apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
      (proj2 (proj2 HS_cz) (x - 1) ltac:(lia)) (fun _ => proj2 (proj2 HS_cz) (x - 2) ltac:(lia))).
    + intros Hbig m2 ? p1 p2 Hvp ?.
      apply chainLeadsUpTo_here; right.
      exists cz_out, (x - 1); split; [exact Hcz_out | split; [exact Hcz_odd | split; [lia | exact (isBounce_r9 (x := x) (y := y) ltac:(lia) Hbig Hvp)]]].
    + intros Hy_hi ? m2 Hm2 p1 p2 Hvp ?.
      pose proof (fzOf_ge_40 Hvp) as Hfp.
      assert (Hc_ge : 131 <= (x + 1) + fzOf p1 p2).
      { destruct (ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) ltac:(lia)) as [q1 [r1 [Hr1 [Heq1 Hox1]]]].
        rewrite (Hox1 ltac:(lia)) in Hy_ox; lia. }
      exact (chainLeadsUpTo_imp
        (proj1 (proj2 (fhigh_bundle m2)) S_ds p1 p2 (x + 1) (y + 2) cz_out Hne1 HS Hvp
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc_ge)
        (fun _ He => or_introl He)).
    + intros Hy_le ? m2 Hm2 p1 p2 Hvp Hfzp.
      destruct (arith_los_odd_r11 Hc Hk1 Hkc Hfz40 Hx89 Hpot Hy_ox Hy_le Hphi38 Hyw Hfzp)
        as [Hy39 [Hx89' Hpot']].
      exact (IH m2 ltac:(lia) S_ds p1 p2 y 1 (x - 1) cz_out Hne1 HS Hvp
        ltac:(lia) ltac:(lia) ltac:(lia) Hcz_out Hcz_odd Hx89' Hpot').
Qed.

Lemma fhigh_ext {N : nat} {S_ds : list nat} {segs : list (nat * nat)} {zl c : nat}
    (Hne1 : S_ds <> [1]) (HS : SafeStack 43 S_ds) (Hv : ValidSegs40 segs zl)
    (Hc : 2 <= c) (Hcz53 : 53 <= c + fzOf segs zl)
    (Hkz95 : 95 <= 1 + 2 * fzOf segs zl)
    (Hodd : 1 + 2 * fzOf segs zl < 97 -> (c + fzOf segs zl) mod 2 = 1) :
  ChainLeadsUpTo N (mkSeg false segs zl c 1 0 S_ds) (ExitHighExt S_ds).
Proof.
  destruct (97 <=? 1 + 2 * fzOf segs zl) eqn:E97.
  - exact (chainLeadsUpTo_imp
      (proj1 (fhigh_bundle N) S_ds segs zl c 1 Hne1 HS Hv Hc ltac:(lia) ltac:(lia) Hcz53 ltac:(lia))
      (fun _ He => or_introl He)).
  - assert (Hcz_odd : (c + fzOf segs zl) mod 2 = 1) by (apply Hodd; lia).
    destruct HS as [HS_ne2 [HS_gd HS_all]].
    assert (HS : SafeStack 43 S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
    destruct segs as [|[z_0 m0] rest].
    + cbn [fzOf] in E97; pose proof (proj2 Hv); lia.
    + cbn [fzOf] in Hcz53, Hkz95, E97, Hcz_odd.
      assert (z_0 = 47) by lia; subst z_0.
      pose proof (validSegs40_tail Hv) as Hv_rest.
      destruct m0 as [|m'].
      * assert (Hg1 : stepGuards (mkSeg false ((47, 0) :: rest) zl c 1 0 S_ds) = true) by reflexivity.
        apply (chainLeadsUpTo_step Hg1); intros m1 Hm1.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct rest as [|[z1 [|m1']] rest2].
        -- pose proof (proj2 Hv_rest) as Hzl230.
           apply chainLeadsUpTo_here; left; left.
           exists (c + 47 + 3 + zl); split; [lia | exact (IsBounce_nil zl (c + 47 + 3) (1 + 2 * 47 + 3) (2 * (c + 47) + 8) S_ds ltac:(lia))].
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: rest2) zl (c + 47 + 3) (1 + 2 * 47 + 3) (2 * (c + 47) + 8) S_ds) = true)
             by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
           apply (chainLeadsUpTo_step Hg2); intros m2 ?.
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
           exact (chainLeadsUpTo_imp
             (proj1 (fhigh_bundle m2) S_ds rest2 zl (c + 47 + 3 + z1 + 1) (1 + 2 * 47 + 3 + 2 * z1 + 3)
               Hne1 HS Hv_r2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
             (fun _ He => or_introl He)).
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           destruct (S m1' mod 2 =? 1) eqn:Em1_od.
           ++ destruct ((1 + 2 * 47 + 3) + m1' <=? 2 * (c + 47) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + 47 + 3) (1 + 2 * 47 + 3) (2 * (c + 47) + 8) S_ds) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                   rewrite Em1_od, Emrg; exact (HS_all (c + 47 + 3 + z1) ltac:(lia)). }
                 apply (chainLeadsUpTo_step Hg2); intros m2 ?.
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
                 rewrite Em1_od, Emrg.
                 exact (chainLeadsUpTo_imp
                   (proj1 (proj2 (fhigh_bundle m2)) S_ds rest2 zl ((1 + 2 * 47 + 3) + m1' + 2 * z1 + 4) 1 (c + 47 + 3 + z1)
                     Hne1 HS Hv_r2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ He => or_introl He)).
              ** apply chainLeadsUpTo_here; left; left.
                 exists (c + 47 + 3 + z1); split; [lia |].
                 apply (IsBounce_cons z1 m1' zl (c + 47 + 3) (1 + 2 * 47 + 3) (2 * (c + 47) + 8) rest2 S_ds Hv_r2 ltac:(lia)).
                 rewrite Em1_od; lia.
           ++ destruct ((1 + 2 * 47 + 3) + S m1' <=? 2 * (c + 47) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + 47 + 3) (1 + 2 * 47 + 3) (2 * (c + 47) + 8) S_ds) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
                   rewrite Em1_od, Emrg; reflexivity. }
                 apply (chainLeadsUpTo_step Hg2); intros m2 ?.
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
                 rewrite Em1_od, Emrg.
                 exact (chainLeadsUpTo_imp
                   (proj1 (fhigh_bundle m2) S_ds rest2 zl (c + 47 + 3 + z1 + 2) ((1 + 2 * 47 + 3) + S m1' + 2 * z1 + 5)
                     Hne1 HS Hv_r2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ He => or_introl He)).
              ** apply chainLeadsUpTo_here; left; left.
                 exists (c + 47 + 3 + z1); split; [lia |].
                 apply (IsBounce_cons z1 m1' zl (c + 47 + 3) (1 + 2 * 47 + 3) (2 * (c + 47) + 8) rest2 S_ds Hv_r2 ltac:(lia)).
                 rewrite Em1_od; lia.
      * pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
        pose proof (goodPhiW_of_ge35 (phiW := c + 47 - 1) HS_ne2 ltac:(lia)) as Hphiw.
        destruct (S m' =? 1) eqn:Em1.
        -- assert (m' = 0) by lia; subst m'.
           assert (Hg : stepGuards (mkSeg false ((47, 1) :: rest) zl c 1 0 S_ds) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
             rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (HS_all (c + 47 + 1) ltac:(lia)). }
           apply (chainLeadsUpTo_step Hg); intros m1 ?.
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
           exact (chainLeadsUpTo_imp
             (proj1 (proj2 (fhigh_bundle m1)) S_ds rest zl (1 + 2 * 47 + 4) 1 (c + 47 + 1)
               Hne1 HS Hv_rest ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
             (fun _ He => or_introl He)).
        -- assert (Hpsi_cz : GoodPsi (c + 47 - 1) S_ds = true).
           { unfold GoodPsi; replace (c + 47 - 1 + 1) with (c + 47) by lia.
             exact (HS_all (c + 47) ltac:(lia)). }
           destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (1 + 2 * 47) + 10)) eqn:Eev_sm.
           ++ assert (Hg : stepGuards (mkSeg false ((47, S m') :: rest) zl c 1 0 S_ds) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity. }
              apply (chainLeadsUpTo_step Hg); intros m1 ?.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
              rewrite Em1, Eev_sm.
              exact (chainLeadsUpTo_imp
                (proj1 (proj2 (fhigh_bundle m1)) S_ds rest zl (1 + 2 * 47 + 4) (S m' + 1) (c + 47)
                  Hne1 HS Hv_rest ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                (fun _ He => or_introl He)).
           ++ destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (1 + 2 * 47) + 11)) eqn:Eod_sm.
              ** pose proof (safeStack_cons_ne1 (x := c + 47) Hne1 HS ltac:(lia) ltac:(lia)) as HS_cz.
                 assert (Hg : stepGuards (mkSeg false ((47, S m') :: rest) zl c 1 0 S_ds) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                   rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                   exact (proj2 (proj2 HS_cz) (1 + 2 * 47 + 2) ltac:(lia)). }
                 apply (chainLeadsUpTo_step Hg); intros m1 ?.
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
                 rewrite Em1, Eev_sm, Eod_sm.
                 replace (S m' - 1) with m' by lia.
                 exact (loopOS_odd m1 S_ds rest zl m' 1 (1 + 2 * 47 + 2) (c + 47) Hne1 HS Hv_rest
                   ltac:(lia) ltac:(lia) ltac:(lia) Hcz53 Hcz_odd ltac:(lia) ltac:(lia)).
              ** assert (Hm_big : 202 <= S m')
                   by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
                 assert (Hg : stepGuards (mkSeg false ((47, S m') :: rest) zl c 1 0 S_ds) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds].
                   rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity. }
                 apply (chainLeadsUpTo_step1 Hg).
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
                 rewrite Em1, Eev_sm, Eod_sm.
                 replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                   by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
                 apply chainLeadsUpTo_here; left; right.
                 exists (c + 47), (1 + 2 * 47 + 2).
                 split; [lia | split; [left; split; [exact Hcz53 | lia] |]].
                 replace (1 + 2 * 47 + 2) with ((1 + 2 * 47 + 2) + 0) at 1 by lia.
                 apply (IsBounce_cons 0 (m' - 4) zl (1 + 2 * 47 + 2) 0 (2 * (1 + 2 * 47) + 6) rest ((c + 47) :: S_ds) Hv_rest ltac:(lia)).
                 destruct (S (m' - 4) mod 2 =? 1); lia.
Qed.

(* ========================================================================== *)
(* Root Invariant (`Root0`, `Root1`, `Root31`, `RootD`, `RootD1`, `RootInv270`) *)
(* ========================================================================== *)

Definition Root0A (s : SegState) : Prop :=
  st_ds s = [] /\ st_cp1 s = 1 /\ st_kb s = 1 /\
  exists z1 m0 m1 rest,
    st_segs s = (8, m0) :: (z1, m1) :: rest /\
    (m0 = 1 \/ m0 = 2) /\ 36 <= z1 /\ ValidSegs40 rest (st_zl s).

Definition Root0B (s : SegState) : Prop :=
  (st_ds s = [] \/ st_ds s = [0]) /\
  ValidTail40 (st_segs s) (st_zl s) /\
  1 <= st_cp1 s /\ 1 <= st_kb s /\ st_kb s <= 2 * st_cp1 s + 3 /\
  7 <= fzOf (st_segs s) (st_zl s) /\ 8 <= st_cp1 s + fzOf (st_segs s) (st_zl s) /\
  (st_cp1 s + fzOf (st_segs s) (st_zl s) = 8 -> exists m0 rest,
    st_segs s = (7, m0) :: rest /\ st_cp1 s = 1 /\ st_kb s = 1 /\ st_ds s = [0] /\ 44 <= fzOf rest (st_zl s)) /\
  (fzOf (st_segs s) (st_zl s) < 39 ->
    (st_cp1 s = 1 /\ st_kb s = 1) \/ (st_cp1 s = 2 /\ st_kb s = 5 /\ 20 <= fzOf (st_segs s) (st_zl s))) /\
  (forall z_0 m0 rest, st_segs s = (z_0, m0) :: rest -> st_cp1 s + fzOf (st_segs s) (st_zl s) = 9 ->
    3 <= m0 -> m0 mod 2 = 1 ->
      53 <= (m0 - 1) + fzOf rest (st_zl s) /\ 95 <= 1 + 2 * fzOf rest (st_zl s) /\
      (1 + 2 * fzOf rest (st_zl s) < 97 -> ((m0 - 1) + fzOf rest (st_zl s)) mod 2 = 1)).

Definition Root0 (s : SegState) : Prop := Root0A s \/ Root0B s.

Definition Root1 (s : SegState) : Prop :=
  st_ds s = [1] /\
  ValidTail40 (st_segs s) (st_zl s) /\
  5 <= st_cp1 s /\ 1 <= st_kb s /\ st_kb s <= 2 * st_cp1 s + 3 /\
  20 <= fzOf (st_segs s) (st_zl s) /\ 45 <= st_kb s + 2 * fzOf (st_segs s) (st_zl s) /\
  (st_cp1 s + fzOf (st_segs s) (st_zl s) = 25 -> exists m0 rest,
    st_segs s = (20, m0) :: rest /\ st_cp1 s = 5 /\ st_kb s = 5 /\ 6 <= m0 /\
    (m0 mod 2 = 1 -> 102 <= (m0 - 1) + fzOf rest (st_zl s) /\ 185 <= 1 + 2 * fzOf rest (st_zl s))) /\
  (26 <= st_cp1 s + fzOf (st_segs s) (st_zl s) -> 47 <= st_kb s + 2 * fzOf (st_segs s) (st_zl s)).

Definition Root31A (s : SegState) : Prop :=
  st_ds s = [3; 1] /\ ValidTail40 (st_segs s) (st_zl s) /\
  st_cp1 s = 2 /\ st_kb s = 1 /\
  (fzOf (st_segs s) (st_zl s) = 18 \/ fzOf (st_segs s) (st_zl s) = 19 \/ exists rest, st_segs s = (20, 0) :: rest).

Definition Root31B (s : SegState) : Prop :=
  st_ds s = [3; 1] /\
  ValidTail40 (st_segs s) (st_zl s) /\
  2 <= st_cp1 s /\ 1 <= st_kb s /\ st_kb s <= 2 * st_cp1 s + 3 /\
  21 <= fzOf (st_segs s) (st_zl s) /\ 25 <= st_cp1 s + fzOf (st_segs s) (st_zl s) /\ 43 <= st_kb s + 2 * fzOf (st_segs s) (st_zl s) /\
  (forall z_0 m0 rest, st_segs s = (z_0, m0) :: rest -> (st_cp1 s + z_0) mod 2 = 0 -> 3 <= m0 -> m0 mod 2 = 1 ->
    (st_cp1 s = 4 /\ st_kb s = 1 /\ z_0 = 22) \/ 47 <= st_kb s + 2 * z_0).

Definition Root31 (s : SegState) : Prop := Root31A s \/ Root31B s.

Definition RootD (s : SegState) : Prop :=
  (exists d, 8 <= d /\ (st_ds s = [d] \/ st_ds s = [d; 0])) /\
  ValidTail40 (st_segs s) (st_zl s) /\
  1 <= st_cp1 s /\ 1 <= st_kb s /\ st_kb s <= 2 * st_cp1 s + 3 /\
  35 <= fzOf (st_segs s) (st_zl s) /\ 42 <= st_cp1 s + fzOf (st_segs s) (st_zl s) /\ 73 <= st_kb s + 2 * fzOf (st_segs s) (st_zl s).

Definition RootD1 (s : SegState) : Prop :=
  (exists d, 25 <= d /\ st_ds s = [d; 1]) /\
  ValidTail40 (st_segs s) (st_zl s) /\
  2 <= st_cp1 s /\ 1 <= st_kb s /\ st_kb s <= 2 * st_cp1 s + 3 /\
  40 <= fzOf (st_segs s) (st_zl s) /\ 62 <= st_cp1 s + fzOf (st_segs s) (st_zl s) /\ 81 <= st_kb s + 2 * fzOf (st_segs s) (st_zl s).

Definition RootInv270 (s : SegState) : Prop :=
  st_b s = false /\ st_mrg s = 0 /\ (Root0 s \/ Root1 s \/ Root31 s \/ RootD s \/ RootD1 s).

Lemma rootInv_of_0A {z1 m0 m1 zl : nat} {rest : list (nat * nat)}
    (Hm0 : m0 = 1 \/ m0 = 2) (Hz1 : 36 <= z1) (Hv : ValidSegs40 rest zl) :
  RootInv270 (mkSeg false ((8, m0) :: (z1, m1) :: rest) zl 1 1 0 []).
Proof.
  refine (conj eq_refl (conj eq_refl (or_introl (or_introl _)))).
  refine (conj eq_refl (conj eq_refl (conj eq_refl _))).
  exists z1, m0, m1, rest; exact (conj eq_refl (conj Hm0 (conj Hz1 Hv))).
Qed.

Lemma rootInv_of_0B {segs : list (nat * nat)} {zl c k : nat} {ds : list nat}
    (Hds : ds = [] \/ ds = [0]) (Hvt : ValidTail40 segs zl)
    (Hc : 1 <= c) (Hk : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz : 7 <= fzOf segs zl) (Hcz : 8 <= c + fzOf segs zl)
    (H8 : c + fzOf segs zl = 8 -> exists m0 rest,
      segs = (7, m0) :: rest /\ c = 1 /\ k = 1 /\ ds = [0] /\ 44 <= fzOf rest zl)
    (H39 : fzOf segs zl < 39 -> (c = 1 /\ k = 1) \/ (c = 2 /\ k = 5 /\ 20 <= fzOf segs zl))
    (H9 : forall z_0 m0 rest, segs = (z_0, m0) :: rest -> c + fzOf segs zl = 9 ->
      3 <= m0 -> m0 mod 2 = 1 ->
        53 <= (m0 - 1) + fzOf rest zl /\ 95 <= 1 + 2 * fzOf rest zl /\
        (1 + 2 * fzOf rest zl < 97 -> ((m0 - 1) + fzOf rest zl) mod 2 = 1)) :
  RootInv270 (mkSeg false segs zl c k 0 ds).
Proof.
  exact (conj eq_refl (conj eq_refl (or_introl (or_intror
    (conj Hds (conj Hvt (conj Hc (conj Hk (conj Hkc (conj Hfz (conj Hcz (conj H8 (conj H39 H9))))))))))))).
Qed.

Lemma rootInv_of_1 {segs : list (nat * nat)} {zl c k : nat}
    (Hvt : ValidTail40 segs zl)
    (Hc : 5 <= c) (Hk : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz : 20 <= fzOf segs zl) (Hkz : 45 <= k + 2 * fzOf segs zl)
    (H25 : c + fzOf segs zl = 25 -> exists m0 rest,
      segs = (20, m0) :: rest /\ c = 5 /\ k = 5 /\ 6 <= m0 /\
      (m0 mod 2 = 1 -> 102 <= (m0 - 1) + fzOf rest zl /\ 185 <= 1 + 2 * fzOf rest zl))
    (H26 : 26 <= c + fzOf segs zl -> 47 <= k + 2 * fzOf segs zl) :
  RootInv270 (mkSeg false segs zl c k 0 [1]).
Proof.
  exact (conj eq_refl (conj eq_refl (or_intror (or_introl
    (conj eq_refl (conj Hvt (conj Hc (conj Hk (conj Hkc (conj Hfz (conj Hkz (conj H25 H26)))))))))))).
Qed.

Lemma rootInv_of_31A {segs : list (nat * nat)} {zl : nat}
    (Hvt : ValidTail40 segs zl)
    (Hfz : fzOf segs zl = 18 \/ fzOf segs zl = 19 \/ exists rest, segs = (20, 0) :: rest) :
  RootInv270 (mkSeg false segs zl 2 1 0 [3; 1]).
Proof.
  exact (conj eq_refl (conj eq_refl (or_intror (or_intror (or_introl (or_introl
    (conj eq_refl (conj Hvt (conj eq_refl (conj eq_refl Hfz)))))))))).
Qed.

Lemma rootInv_of_31B {segs : list (nat * nat)} {zl c k : nat} {ds : list nat}
    (Hds : ds = [3; 1]) (Hvt : ValidTail40 segs zl)
    (Hc : 2 <= c) (Hk : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz : 21 <= fzOf segs zl) (Hcz : 25 <= c + fzOf segs zl) (Hkz : 43 <= k + 2 * fzOf segs zl)
    (Hod : forall z_0 m0 rest, segs = (z_0, m0) :: rest -> (c + z_0) mod 2 = 0 -> 3 <= m0 -> m0 mod 2 = 1 ->
      (c = 4 /\ k = 1 /\ z_0 = 22) \/ 47 <= k + 2 * z_0) :
  RootInv270 (mkSeg false segs zl c k 0 ds).
Proof.
  exact (conj eq_refl (conj eq_refl (or_intror (or_intror (or_introl (or_intror
    (conj Hds (conj Hvt (conj Hc (conj Hk (conj Hkc (conj Hfz (conj Hcz (conj Hkz Hod)))))))))))))).
Qed.

Lemma rootInv_of_D {segs : list (nat * nat)} {zl c k d : nat} {ds : list nat}
    (Hd : 8 <= d) (Hds : ds = [d] \/ ds = [d; 0]) (Hvt : ValidTail40 segs zl)
    (Hc : 1 <= c) (Hk : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz : 35 <= fzOf segs zl) (Hcz : 42 <= c + fzOf segs zl) (Hkz : 73 <= k + 2 * fzOf segs zl) :
  RootInv270 (mkSeg false segs zl c k 0 ds).
Proof.
  refine (conj eq_refl (conj eq_refl (or_intror (or_intror (or_intror (or_introl _)))))).
  refine (conj _ (conj Hvt (conj Hc (conj Hk (conj Hkc (conj Hfz (conj Hcz Hkz))))))).
  exists d; exact (conj Hd Hds).
Qed.

Lemma rootInv_of_D1 {segs : list (nat * nat)} {zl c k d : nat}
    (Hd : 25 <= d) (Hvt : ValidTail40 segs zl)
    (Hc : 2 <= c) (Hk : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz : 40 <= fzOf segs zl) (Hcz : 62 <= c + fzOf segs zl) (Hkz : 81 <= k + 2 * fzOf segs zl) :
  RootInv270 (mkSeg false segs zl c k 0 [d; 1]).
Proof.
  refine (conj eq_refl (conj eq_refl (or_intror (or_intror (or_intror (or_intror _)))))).
  refine (conj _ (conj Hvt (conj Hc (conj Hk (conj Hkc (conj Hfz (conj Hcz Hkz))))))).
  exists d; exact (conj Hd eq_refl).
Qed.

Arguments chainLeadsUpTo_here {N s P} & _.
Arguments rootInv_of_0B {segs zl c k ds} & _ _ _ _ _ _ _ _ _ _.
Arguments rootInv_of_1 {segs zl c k} & _ _ _ _ _ _ _ _.
Arguments rootInv_of_31A {segs zl} & _ _.
Arguments rootInv_of_31B {segs zl c k ds} & _ _ _ _ _ _ _ _ _.
Arguments rootInv_of_D {segs zl c k d ds} & _ _ _ _ _ _ _ _ _.
Arguments rootInv_of_D1 {segs zl c k d} & _ _ _ _ _ _ _ _.


Ltac find_top_if term ::=
  lazymatch term with
  | if ?c then _ else _ => c
  | ?f ?a =>
      lazymatch f with
      | context [if _ then _ else _] => find_top_if f
      | _ => find_top_if a
      end
  end.
#[local] Arguments or_introl {A B} & _.
#[local] Arguments or_intror {A B} & _.
#[local] Arguments conj {A B} & _ _.
(* ========================================================================== *)
(* Drain-Pop Closure Lemmas (`IsBounce phi ds s -> ChainLeadsUpTo N s RootInv270`) *)
(* ========================================================================== *)

Lemma bounce_nil_leads {N phi : nat} {s : SegState}
    (Hb : IsBounce phi [] s) (Hphi : 9 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi [] = true) by (unfold drainPopGuards; cbn [isDrainRstDs isRank0]; lia).
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  apply (chainLeadsUpTo_step1 Hg_s); rewrite Hstep.
  set (p := pushSeg hp (phi + 1) m_rem rest zl).
  change (drainPopStep hp phi m_rem rest zl []) with (mkSeg false (fst p) (snd p) 1 1 0 []).
  assert (Hvt : ValidTail40 (fst p) (snd p))
    by (apply (validTail40_pushSeg hp (z := phi + 1) (m := m_rem) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 1) m_rem rest zl) as Hfzp; fold p in Hfzp.
  apply chainLeadsUpTo_here.
  exact (rootInv_of_0B (or_introl eq_refl) Hvt ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun _ => or_introl (conj eq_refl eq_refl))
    (fun _ _ _ _ Hcz9 => ltac:(lia))).
Qed.

Lemma bounce_zero_leads {N phi : nat} {s : SegState}
    (Hb : IsBounce phi [0] s) (Hphi : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi [0] = true) by (change (drainPopGuards phi [0]) with (2 <=? phi) || change (drainPopGuards phi [1]) with (2 <=? phi); lia).
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?.
  rewrite Hstep.
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  change (drainPopStep hp phi m_rem rest zl [0]) with (mkSeg true (fst p) (snd p) 2 2 6 []).
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  destruct (fst p) as [|[z1 [|m1']] r2] eqn:Ep1.
  - pose proof (proj2 Hvp) as Hzl230.
    exact (bounce_nil_leads (IsBounce_nil (snd p) 2 2 6 [] ltac:(lia)) ltac:(lia)).
  - pose proof (fzOf_ge_40 Hvp) as Hz1_40; cbn [fzOf] in Hz1_40.
    pose proof (validSegs40_tail Hvp) as Hv_r2.
    pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
    assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: r2) (snd p) 2 2 6 []) = true) by reflexivity.
    apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    apply chainLeadsUpTo_here.
    exact (rootInv_of_0B (or_introl eq_refl) (validTail40_of_validSegs40 Hv_r2)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia))).
  - pose proof (fzOf_ge_40 Hvp) as Hz1_40; cbn [fzOf] in Hz1_40.
    pose proof (validSegs40_tail Hvp) as Hv_r2.
    pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
    destruct (S m1' mod 2 =? 1) eqn:Eod.
    + destruct (2 + m1' <=? 6) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: r2) (snd p) 2 2 6 []) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
          exact (proj2 (proj2 safeStack_nil) (2 + z1) ltac:(lia)). }
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
        apply chainLeadsUpTo_here.
        exact (rootInv_of_D (d := 2 + z1) ltac:(lia) (or_introl eq_refl)
          (validTail40_of_validSegs40 Hv_r2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      * apply (bounce_nil_leads (phi := 2 + z1)); [| lia].
        apply (IsBounce_cons z1 m1' (snd p) 2 2 6 r2 [] Hv_r2 ltac:(lia)).
        rewrite Eod; lia.
    + destruct (2 + S m1' <=? 6) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: r2) (snd p) 2 2 6 []) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg; reflexivity. }
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
        apply chainLeadsUpTo_here.
        exact (rootInv_of_0B (or_introl eq_refl) (validTail40_of_validSegs40 Hv_r2)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
          (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia))).
      * apply (bounce_nil_leads (phi := 2 + z1)); [| lia].
        apply (IsBounce_cons z1 m1' (snd p) 2 2 6 r2 [] Hv_r2 ltac:(lia)).
        rewrite Eod; lia.
Qed.

Lemma bounce_one_leads {N phi : nat} {s : SegState}
    (Hb : IsBounce phi [1] s) (Hphi : 24 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi [1] = true) by (change (drainPopGuards phi [0]) with (2 <=? phi) || change (drainPopGuards phi [1]) with (2 <=? phi); lia).
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?.
  rewrite Hstep.
  change (drainPopStep hp phi m_rem rest zl [1])
    with (mkSeg true (fst (pushSeg hp (phi + 3) m_rem rest zl)) (snd (pushSeg hp (phi + 3) m_rem rest zl)) 2 0 6 []).
  destruct hp.
  - pose proof (Hv_rest eq_refl) as Hv_r.
    pose proof (fzOf_ge_40 Hv_r) as Hfz_r.
    cbn [pushSeg fst snd].
    destruct m_rem as [|mr'].
    + cbn [normSeg Nat.eqb].
      assert (Hg2 : stepGuards (mkSeg true ((phi + 3 + 1, 0) :: rest) zl 2 0 6 []) = true) by reflexivity.
      apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      apply chainLeadsUpTo_here.
      exact (rootInv_of_0B (or_introl eq_refl) (validTail40_of_validSegs40 Hv_r)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia))).
    + cbn [normSeg Nat.eqb].
      destruct (S mr' mod 2 =? 1) eqn:Eod.
      * destruct (0 + mr' <=? 6) eqn:Emrg.
        -- assert (Hg2 : stepGuards (mkSeg true ((phi + 3, S mr') :: rest) zl 2 0 6 []) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
             exact (proj2 (proj2 safeStack_nil) (2 + (phi + 3)) ltac:(lia)). }
           apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
           apply chainLeadsUpTo_here.
           exact (rootInv_of_D (d := 2 + (phi + 3)) ltac:(lia) (or_introl eq_refl)
             (validTail40_of_validSegs40 Hv_r) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        -- apply (bounce_nil_leads (phi := 2 + (phi + 3))); [| lia].
           apply (IsBounce_cons (phi + 3) mr' zl 2 0 6 rest [] Hv_r ltac:(lia)).
           rewrite Eod; lia.
      * destruct (0 + S mr' <=? 6) eqn:Emrg.
        -- assert (Hg2 : stepGuards (mkSeg true ((phi + 3, S mr') :: rest) zl 2 0 6 []) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg; reflexivity. }
           apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
           apply chainLeadsUpTo_here.
           exact (rootInv_of_0B (or_introl eq_refl) (validTail40_of_validSegs40 Hv_r)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia))).
        -- apply (bounce_nil_leads (phi := 2 + (phi + 3))); [| lia].
           apply (IsBounce_cons (phi + 3) mr' zl 2 0 6 rest [] Hv_r ltac:(lia)).
           rewrite Eod; lia.
  - pose proof (Hzl_false eq_refl) as Hzl230.
    cbn [pushSeg fst snd].
    exact (bounce_nil_leads (IsBounce_nil (phi + 3) 2 0 6 [] ltac:(lia)) ltac:(lia)).
Qed.

Lemma bounce_31_leads {N phi : nat} {s : SegState}
    (Hb : IsBounce phi [3; 1] s) (Hphi : 18 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi [3; 1] = true)
    by (change (drainPopGuards phi [3; 1]) with (true && true && true && (16 <=? phi)); cbn [andb]; lia).
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?.
  rewrite Hstep.
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  change (drainPopStep hp phi m_rem rest zl [3; 1]) with (mkSeg true ((1, 0) :: fst p) (snd p) 0 0 2 []).
  assert (Hvt : ValidTail40 (fst p) (snd p))
    by (apply (validTail40_pushSeg hp (z := phi + 2) (m := m_rem) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp; fold p in Hfzp.
  assert (Hg2 : stepGuards (mkSeg true ((1, 0) :: fst p) (snd p) 0 0 2 []) = true) by reflexivity.
  apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
  apply chainLeadsUpTo_here.
  exact (rootInv_of_0B (or_introl eq_refl) Hvt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (fun H => ltac:(lia)) (fun _ => or_intror (conj eq_refl (conj eq_refl ltac:(lia))))
    (fun _ _ _ _ Hcz9 => ltac:(lia))).
Qed.

Lemma bounce_cz_31_leads {N cz phi : nat} {s : SegState}
    (Hb : IsBounce phi [cz; 3; 1] s)
    (Hcases : ((cz = 20 \/ cz = 21) /\ 34 <= phi) \/
              (22 <= cz /\ cz mod 2 = 1 /\ 38 <= phi) \/
              (26 <= cz /\ cz mod 2 = 0 /\ (46 <= phi \/ (cz = 26 /\ phi = 45)))) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hcz20 : 20 <= cz) by lia.
  assert (Hphi34 : 34 <= phi) by lia.
  assert (Hnrst : isDrainRstDs [cz; 3; 1] = false) by reflexivity.
  assert (Hnr0 : isRank0 [cz; 3; 1] = false) by (destruct cz as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop' : drainPopGuards phi [cz; 3; 1] = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? cz) && (1 <=? 3)) with true by lia.
    replace ((cz mod 2 =? 0) && (cz <=? 2 * 3 + 4)) with false by lia.
    replace ((cz mod 2 =? 0) && (cz + 14 <=? 2 * 3)) with false by lia.
    cbn [negb orb andb]; lia. }
  destruct (isBounce_step Hb Hg_pop') as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl [cz; 3; 1] =
                mkSeg true ((0, cz - 3) :: fst p) (snd p) 2 0 6 [1]).
  { unfold drainPopStep; rewrite Hnrst, Hnr0; cbn [Nat.eqb nat_list_eqb andb].
    replace (normSeg 0 (cz - 3)) with (0, cz - 3) by (unfold normSeg; rw_if_neg ltac:(lia); reflexivity).
    reflexivity. }
  rewrite Hdp in Hstep.
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp; fold p in Hfzp.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hg_b1 : stepGuards (mkSeg true ((0, cz - 3) :: fst p) (snd p) 2 0 6 [1]) = true).
  { replace (cz - 3) with (S (cz - 4)) by lia.
    cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 4) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
  assert (Hs_b1 : stepSegs (mkSeg true ((0, cz - 3) :: fst p) (snd p) 2 0 6 [1]) =
                  mkSeg true ((5, cz - 11) :: fst p) (snd p) 2 0 6 []).
  { set (p1 := fst p); set (p2 := snd p); clearbody p1 p2.
    replace (cz - 3) with (S (cz - 4)) by lia.
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 4) mod 2 =? 1); rw_if_neg ltac:(lia);
      cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb]; f_equal; f_equal; unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia. }
  apply (chainLeadsUpTo_step Hg_b1); intros m2 ?; rewrite Hs_b1.
  assert (Hg_b2 : stepGuards (mkSeg true ((5, cz - 11) :: fst p) (snd p) 2 0 6 []) = true).
  { replace (cz - 11) with (S (cz - 12)) by lia.
    cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 12) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
  assert (Hs_b2 : stepSegs (mkSeg true ((5, cz - 11) :: fst p) (snd p) 2 0 6 []) =
                  mkSeg false ((8, cz - 19) :: fst p) (snd p) 1 1 0 []).
  { set (p1 := fst p); set (p2 := snd p); clearbody p1 p2.
    replace (cz - 11) with (S (cz - 12)) by lia.
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 12) mod 2 =? 1); rw_if_neg ltac:(lia);
      cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb]; f_equal; f_equal; unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia. }
  apply (chainLeadsUpTo_step1 Hg_b2); rewrite Hs_b2; apply chainLeadsUpTo_here.
  destruct Hcases as [[Hcz2021 _] | [[Hcz22 [Hcz_od Hphi38]] | [Hcz26 [Hcz_ev Hphi_ev]]]].
  - destruct hp.
    + pose proof (Hv_rest eq_refl) as Hvr.
      pose proof (normSeg_fst_ge (phi + 2) m_rem) as Hnf.
      unfold p; cbn [pushSeg fst snd].
      destruct (normSeg (phi + 2) m_rem) as [z1_seg m1_seg]; cbn [fst] in Hnf.
      exact (rootInv_of_0A (z1 := z1_seg) (m0 := cz - 19) (m1 := m1_seg) ltac:(lia) ltac:(lia) Hvr).
    + pose proof (Hzl_false eq_refl) as Hzl230.
      assert (Hvp : ValidSegs40 (fst p) (snd p))
        by (unfold p; apply (validSegs40_pushSeg false (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intros ?; lia).
      clearbody p.
      refine (rootInv_of_0B (or_introl eq_refl) Hvp ltac:(lia) ltac:(lia) ltac:(lia)
        (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
        (fun H => ltac:(cbn [fzOf] in H; lia)) (fun _ => or_introl (conj eq_refl eq_refl)) _).
      intros z_0 m0 r Hseg ?; inversion Hseg; subst; lia.
  - assert (Hvp : ValidSegs40 (fst p) (snd p))
      by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
    clearbody p.
    refine (rootInv_of_0B (or_introl eq_refl) Hvp ltac:(lia) ltac:(lia) ltac:(lia)
      (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
      (fun H => ltac:(cbn [fzOf] in H; lia)) (fun _ => or_introl (conj eq_refl eq_refl)) _).
    intros z_0 m0 r Hseg ? ? Hm0_od; inversion Hseg; subst; lia.
  - assert (Hphi45 : 45 <= phi) by lia.
    assert (Hvp : ValidSegs40 (fst p) (snd p))
      by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
    clearbody p.
    refine (rootInv_of_0B (or_introl eq_refl) Hvp ltac:(lia) ltac:(lia) ltac:(lia)
      (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
      (fun H => ltac:(cbn [fzOf] in H; lia)) (fun _ => or_introl (conj eq_refl eq_refl)) _).
    intros z_0 m0 r Hseg ? ? ?; inversion Hseg; subst.
    destruct Hphi_ev as [Hphi46 | [-> ->]]; [split; [lia | split; [lia | intro; lia]] | split; [lia | split; [lia | intro; lia]]].
Qed.

Lemma bounce_d1_leads {N d phi : nat} {s : SegState}
    (Hb : IsBounce phi [d; 1] s) (Hd25 : 25 <= d) (Hphi42 : 42 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hnrst : isDrainRstDs [d; 1] = false) by reflexivity.
  assert (Hnr0 : isRank0 [d; 1] = false) by (destruct d as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop : drainPopGuards phi [d; 1] = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? d) && (1 <=? 1)) with true by lia.
    replace ((d mod 2 =? 0) && (d <=? 2 * 1 + 4)) with false by lia.
    replace ((d mod 2 =? 0) && (d + 14 <=? 2 * 1)) with false by lia.
    cbn [negb orb andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl [d; 1] =
                mkSeg true (normSeg 0 (d - 11) :: fst p) (snd p) 5 0 12 [2]).
  { unfold drainPopStep; rewrite Hnrst, Hnr0.
    replace ((1 =? 1) && nat_list_eqb [] [] && (25 <=? d)) with true
      by (cbn [Nat.eqb nat_list_eqb andb]; lia).
    reflexivity. }
  rewrite Hdp.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp; fold p in Hfzp; clearbody p.
  replace (normSeg 0 (d - 11)) with (0, S (d - 12))
    by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
  assert (Hg2 : stepGuards (mkSeg true ((0, S (d - 12)) :: fst p) (snd p) 5 0 12 [2]) = true).
  { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (d - 12) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
  assert (Hs2 : stepSegs (mkSeg true ((0, S (d - 12)) :: fst p) (snd p) 5 0 12 [2]) =
                mkSeg false (normSeg 7 (d - 25) :: fst p) (snd p) 1 1 0 [0]).
  { cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (d - 12) mod 2 =? 1); rw_if_neg ltac:(lia);
      cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb];
      f_equal; f_equal; f_equal; lia. }
  apply (chainLeadsUpTo_step1 Hg2); rewrite Hs2; apply chainLeadsUpTo_here.
  destruct (Nat.eq_dec d 25) as [-> | Hd26].
  - change (normSeg 7 (25 - 25)) with (8, 0).
    refine (rootInv_of_0B (or_intror eq_refl) Hvp ltac:(lia) ltac:(lia) ltac:(lia)
      (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
      (fun H => ltac:(cbn [fzOf] in H; lia)) (fun _ => or_introl (conj eq_refl eq_refl)) _).
    intros z_0 m0 r Hseg ? H3; inversion Hseg; subst; lia.
  - replace (normSeg 7 (d - 25)) with (7, d - 25) by (unfold normSeg; rw_if_neg ltac:(lia); reflexivity).
    refine (rootInv_of_0B (or_intror eq_refl) Hvp ltac:(lia) ltac:(lia) ltac:(lia)
      (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
      (fun _ => ltac:(exists (d - 25), (fst p); repeat split; lia))
      (fun _ => or_introl (conj eq_refl eq_refl))
      (fun _ _ _ _ Hcz9 => ltac:(cbn [fzOf] in Hcz9; lia))).
Qed.

Lemma bounce_d_leads {N d phi : nat} {ds : list nat} {s : SegState}
    (Hb : IsBounce phi ds s)
    (Hds : ds = [d] \/ ds = [d; 0])
    (Hcases : (d = 8 /\ (phi = 16 \/ phi = 17 \/ 38 <= phi)) \/
              (d = 9 /\ 19 <= phi) \/
              (10 <= d /\ d <= 18 /\ 19 <= phi /\ (12 <= d -> d mod 2 = 0 -> 23 <= phi)) \/
              (d = 19 /\ 37 <= phi) \/
              (20 <= d /\ 38 <= phi)) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hd8 : 8 <= d) by lia.
  assert (Hrst : isDrainRstDs ds = true) by (destruct Hds as [-> | ->]; unfold isDrainRstDs; lia).
  assert (Hhd_ds : headNat ds = d) by (destruct Hds as [-> | ->]; reflexivity).
  assert (Hg_pop : drainPopGuards phi ds = true).
  { unfold drainPopGuards; rewrite Hrst.
    destruct Hcases as [[-> H16] | [[_ H19] | [[_ [_ [H19 _]]] | [[_ H19] | [_ H19]]]]].
    - destruct Hds as [-> | ->]; [change (isOddDrainDs [8]) with false | change (isOddDrainDs [8; 0]) with false]; cbv iota; lia.
    - destruct (isOddDrainDs ds); lia.
    - destruct (isOddDrainDs ds); lia.
    - destruct (isOddDrainDs ds); lia.
    - destruct (isOddDrainDs ds); lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  unfold drainPopStep; rewrite Hrst, Hhd_ds.
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hvt : ValidTail40 (fst p) (snd p))
    by (unfold p; apply (validTail40_pushSeg hp (z := phi + 2) (m := m_rem) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp; fold p in Hfzp.
  destruct Hcases as [[-> Hphi_d8] | [[-> Hphi19] | [[Hd10 [Hd18 [Hphi19 Hd_ev23]]] | [[-> Hphi37] | [Hd20 Hphi38]]]]].
  - change (8 - 7 =? 1) with true; cbv iota.
    apply chainLeadsUpTo_here.
    destruct Hphi_d8 as [-> | [-> | Hphi38]].
    + apply (rootInv_of_31A Hvt).
      destruct hp; [| pose proof (Hzl_false eq_refl); lia].
      destruct m_rem; [right; left; reflexivity | left; reflexivity].
    + apply (rootInv_of_31A Hvt).
      destruct hp; [| pose proof (Hzl_false eq_refl); lia].
      destruct m_rem; [right; right; exists rest; reflexivity | right; left; reflexivity].
    + refine (rootInv_of_31B eq_refl Hvt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _).
      intros z_0 m0 r Hseg ? ? ?; assert (fzOf (fst p) (snd p) = z_0) by (rewrite Hseg; reflexivity); right; lia.
  - change (9 - 7 =? 1) with false; cbv iota.
    change (normSeg 0 (9 - 7 - 2)) with (1, 0).
    assert (Hg2 : stepGuards (mkSeg true ((1, 0) :: fst p) (snd p) 3 0 8 [1]) = true) by reflexivity.
    apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    exact (chainLeadsUpTo_here (rootInv_of_1 Hvt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      (fun H => ltac:(lia)) (fun _ => ltac:(lia)))).
  - rw_if_neg ltac:(lia).
    replace (normSeg 0 (d - 7 - 2)) with (0, S (d - 10))
      by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
    destruct (S (d - 10) mod 2 =? 1) eqn:Eod.
    + assert (Hmrg : (0 + (d - 10) <=? 8) = true) by lia.
      assert (Hg2 : stepGuards (mkSeg true ((0, S (d - 10)) :: fst p) (snd p) 3 0 8 [1]) = true)
        by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Hmrg; reflexivity).
      apply (chainLeadsUpTo_step1 Hg2).
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Hmrg; cbn [andb Nat.eqb].
      apply chainLeadsUpTo_here.
      refine (rootInv_of_31B eq_refl Hvt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _).
      intros z_0 m0 r Hseg Hpar ? ?.
      assert (Hz0 : fzOf (fst p) (snd p) = z_0) by (rewrite Hseg; reflexivity).
      destruct (Nat.eq_dec d 10) as [-> | Hd12]; [lia |].
      pose proof (Hd_ev23 ltac:(lia) ltac:(lia)); right; lia.
    + assert (Hmrg : (0 + S (d - 10) <=? 8) = true) by lia.
      assert (Hg2 : stepGuards (mkSeg true ((0, S (d - 10)) :: fst p) (snd p) 3 0 8 [1]) = true)
        by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Hmrg; reflexivity).
      apply (chainLeadsUpTo_step1 Hg2).
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Hmrg; cbn [andb Nat.eqb].
      exact (chainLeadsUpTo_here (rootInv_of_1 Hvt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        (fun H => ltac:(lia)) (fun _ => ltac:(lia)))).
  - change (19 - 7 =? 1) with false; cbv iota.
    change (normSeg 0 (19 - 7 - 2)) with (0, 10).
    assert (Hg2 : stepGuards (mkSeg true ((0, 10) :: fst p) (snd p) 3 0 8 [1]) = true) by reflexivity.
    assert (Hs2 : stepSegs (mkSeg true ((0, 10) :: fst p) (snd p) 3 0 8 [1]) =
                  mkSeg true ((7, 0) :: fst p) (snd p) 2 0 6 []) by reflexivity.
    apply (chainLeadsUpTo_step Hg2); intros m2 ?; rewrite Hs2.
    assert (Hg3 : stepGuards (mkSeg true ((7, 0) :: fst p) (snd p) 2 0 6 []) = true) by reflexivity.
    apply (chainLeadsUpTo_step1 Hg3); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvt ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
  - rw_if_neg ltac:(lia).
    assert (Hvp : ValidSegs40 (fst p) (snd p))
      by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
    pose proof (fzOf_ge_40 Hvp) as Hfzp40; clearbody p.
    replace (normSeg 0 (d - 7 - 2)) with (0, S (d - 10))
      by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
    assert (Hg2 : stepGuards (mkSeg true ((0, S (d - 10)) :: fst p) (snd p) 3 0 8 [1]) = true).
    { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
      destruct (S (d - 10) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
    assert (Hs2 : stepSegs (mkSeg true ((0, S (d - 10)) :: fst p) (snd p) 3 0 8 [1]) =
                  mkSeg true ((6, S (d - 20)) :: fst p) (snd p) 2 0 6 []).
    { cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
      destruct (S (d - 10) mod 2 =? 1); rw_if_neg ltac:(lia);
        cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb]; f_equal; f_equal; unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia. }
    apply (chainLeadsUpTo_step Hg2); intros m2 ?; rewrite Hs2.
    destruct (S (d - 20) mod 2 =? 1) eqn:Eod2.
    + destruct (0 + (d - 20) <=? 6) eqn:Emrg2.
      * assert (Hg3 : stepGuards (mkSeg true ((6, S (d - 20)) :: fst p) (snd p) 2 0 6 []) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2; reflexivity).
        apply (chainLeadsUpTo_step1 Hg3).
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2; cbn [andb Nat.eqb].
        exact (chainLeadsUpTo_here (rootInv_of_D (d := 8) ltac:(lia) (or_introl eq_refl)
          (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      * assert (Hg3 : stepGuards (mkSeg true ((6, S (d - 20)) :: fst p) (snd p) 2 0 6 []) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2; reflexivity).
        apply (chainLeadsUpTo_step1 Hg3).
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2.
        set (q := pushSeg true 9 (0 + S (d - 20) - (6 + 2)) (fst p) (snd p)).
        change (drainPopStep true (2 + 6) (0 + S (d - 20) - (6 + 2)) (fst p) (snd p) [])
          with (mkSeg false (fst q) (snd q) 1 1 0 []).
        assert (Hvtq : ValidTail40 (fst q) (snd q))
          by (unfold q; apply (validTail40_pushSeg true (z := 9) (m := 0 + S (d - 20) - (6 + 2)) (fun _ => Hvp)); discriminate).
        pose proof (fzOf_pushSeg_ge true 9 (0 + S (d - 20) - (6 + 2)) (fst p) (snd p)) as Hfzq; fold q in Hfzq; clearbody q.
        exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvtq ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun _ => or_introl (conj eq_refl eq_refl)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
    + destruct (0 + S (d - 20) <=? 6) eqn:Emrg2.
      * assert (Hg3 : stepGuards (mkSeg true ((6, S (d - 20)) :: fst p) (snd p) 2 0 6 []) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2; reflexivity).
        apply (chainLeadsUpTo_step1 Hg3).
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2; cbn [andb Nat.eqb].
        exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) (validTail40_of_validSegs40 Hvp)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
          (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
      * assert (Hg3 : stepGuards (mkSeg true ((6, S (d - 20)) :: fst p) (snd p) 2 0 6 []) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2; reflexivity).
        apply (chainLeadsUpTo_step1 Hg3).
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod2, Emrg2.
        set (q := pushSeg true 9 (0 + S (d - 20) - (6 + 2)) (fst p) (snd p)).
        change (drainPopStep true (2 + 6) (0 + S (d - 20) - (6 + 2)) (fst p) (snd p) [])
          with (mkSeg false (fst q) (snd q) 1 1 0 []).
        assert (Hvtq : ValidTail40 (fst q) (snd q))
          by (unfold q; apply (validTail40_pushSeg true (z := 9) (m := 0 + S (d - 20) - (6 + 2)) (fun _ => Hvp)); discriminate).
        pose proof (fzOf_pushSeg_ge true 9 (0 + S (d - 20) - (6 + 2)) (fst p) (snd p)) as Hfzq; fold q in Hfzq; clearbody q.
        exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvtq ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun _ => or_introl (conj eq_refl eq_refl)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
Qed.

(* ========================================================================== *)
(* Section 5g.3c: RootD, RootD1, and Root1 Advancement Closures               *)
(* ========================================================================== *)


Arguments bounce_nil_leads {N phi s} & _ _.
Arguments bounce_zero_leads {N phi s} & _ _.
Arguments bounce_one_leads {N phi s} & _ _.
Arguments bounce_31_leads {N phi s} & _ _.
Arguments bounce_cz_31_leads {N cz phi s} & _ _.
Arguments bounce_d1_leads {N d phi s} & _ _ _.
Arguments bounce_d_leads {N d phi ds s} & _ _ _.


(* ========================================================================== *)
Lemma chainAdvances_trans {s : SegState} {P Q : SegState -> Prop}
    (H1 : ChainAdvances s P) (H2 : forall s', P s' -> ChainLeads s' Q) :
  ChainAdvances s Q.
Proof.
  exact (conj (proj1 H1) (chainLeads_trans (proj2 H1) H2)).
Qed.
Arguments chainAdvances_trans {s P Q} & _ _.

Lemma fbound_advances {ms : nat} {S_ds : list nat} {segs : list (nat * nat)} {zl c k : nat}
    (Hms19 : 19 <= ms) (HS : SafeStack ms S_ds)
    (Hvt : ValidTail40 segs zl)
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3)
    (Hfz35 : 35 <= fzOf segs zl) (Hcz42 : 42 <= c + fzOf segs zl)
    (Hkz73 : 73 <= k + 2 * fzOf segs zl)
    (Hms_ox : ms + 2 <= ox (k + 2 * fzOf segs zl) (c + fzOf segs zl)) :
  ChainAdvances (mkSeg false segs zl c k 0 S_ds)
    (Exit270 (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
      (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
      (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) S_ds).
Proof.
  destruct (ox_bounds_relaxed (c := c) (k := k) (fz := fzOf segs zl) Hc Hk1 Hkc Hfz35 Hcz42 Hkz73) as [Hox39 Hox_cz3].
  destruct HS as [HS_ne2 [HS_gd HS_all]].
  assert (HS : SafeStack ms S_ds) by exact (conj HS_ne2 (conj HS_gd HS_all)).
  destruct segs as [|[z_0 m0] rest].
  - cbn [fzOf ValidTail40] in Hvt, Hfz35, Hcz42, Hkz73, Hms_ox, Hox39, Hox_cz3 |- *.
    assert (Hg : stepGuards (mkSeg false [] zl c k 0 S_ds) = true).
    { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
      rewrite (goodPhiW_of_ge35 (phiW := c + zl - 1) HS_ne2 ltac:(lia)); cbn [andb]; unfold GoodPsi.
      replace (c + zl - 1 + 1) with (c + zl) by lia.
      exact (HS_all (c + zl) ltac:(lia)). }
    split; [exact Hg | intro N].
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    apply chainLeadsUpTo_here; right.
    destruct (oxw_spec (k + 2 * zl) (c + zl)) as [qw [rw [Hrw [Hkw Hoxw]]]].
    exists (c + zl), (k + 2 * zl + 2).
    split; [lia | split; [lia | split; [rewrite Hoxw; lia |]]].
    replace (k + 2 * zl + 2) with ((k + 2 * zl + 2) + 0) at 1 by lia.
    exact (IsBounce_nil 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) ((c + zl) :: S_ds) ltac:(lia)).
  - cbn [fzOf ValidTail40] in Hvt, Hfz35, Hcz42, Hkz73, Hms_ox, Hox39, Hox_cz3 |- *.
    assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
    destruct m0 as [|m'].
    + split; [reflexivity | intro N].
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      destruct rest as [|[z1 [|m1']] rest2].
      * pose proof (proj2 Hv_rest) as Hzl230.
        apply chainLeadsUpTo_here; left.
        exists (c + z_0 + 3 + zl); split; [rewrite odw_def; lia | exact (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds ltac:(lia))].
      * pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
        pose proof (validSegs40_tail Hv_rest) as Hv_rest2.
        pose proof (fzOf_ge_40 Hv_rest2) as Hfz2_40.
        assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true)
          by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
        apply (chainLeadsUpTo_step Hg2); intros m2 ?.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct (arith_fb_t0 (c := c) (k := k) (z_0 := z_0) (z_1 := z1) (fz2 := fzOf rest2 zl)
          Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hz1_40 Hfz2_40) as [Hm1 [Hm2 Hm3]].
        exact (chainLeadsUpTo_imp
          (proj1 (excursion270_bundle m2) ms S_ds rest2 zl (c + z_0 + 3 + z1 + 1)
            (k + 2 * z_0 + 3 + 2 * z1 + 3) Hms19 HS (validTail40_of_validSegs40 Hv_rest2)
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
            (Nat.le_trans _ _ _ Hms_ox Hm1))
          (fun _ He => exit270_mono He Hm1 Hm2 Hm3)).
      * pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
        pose proof (validSegs40_tail Hv_rest) as Hv_rest2.
        pose proof (fzOf_ge_40 Hv_rest2) as Hfz2_40.
        destruct (S m1' mod 2 =? 1) eqn:Em1_od.
        -- destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
           ++ assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                exact (HS_all (c + z_0 + 3 + z1) ltac:(lia)). }
              apply (chainLeadsUpTo_step Hg2); intros m2 ?.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
              destruct (arith_fb_to (c := c) (k := k) (z_0 := z_0) (z_1 := z1) (m1' := m1') (fz2 := fzOf rest2 zl)
                Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hz1_40 Hfz2_40) as [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]].
              exact (proj2 (excursion270_bundle m2) ms S_ds rest2 zl
                ((k + 2 * z_0 + 3) + m1' + 2 * z1 + 4) 1 (c + z_0 + 3 + z1)
                (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
                Hms19 HS (or_intror ltac:(lia)) Hv_rest2
                ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi1 Hi2 Hi3 Hi4 Hi5).
           ++ apply chainLeadsUpTo_here; left.
              exists (c + z_0 + 3 + z1); split; [rewrite odw_def; lia |].
              apply (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 S_ds Hv_rest2 ltac:(lia)).
              rewrite Em1_od; lia.
        -- destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
           ++ assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) S_ds) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg; reflexivity).
              apply (chainLeadsUpTo_step Hg2); intros m2 ?.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
              replace (S m1') with (m1' + 1) in * by lia.
              destruct (arith_fb_te (c := c) (k := k) (z_0 := z_0) (z_1 := z1) (m1' := m1') (fz2 := fzOf rest2 zl)
                Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hz1_40 Hfz2_40 ltac:(lia)) as [Hm1 [Hm2 Hm3]].
              exact (chainLeadsUpTo_imp
                (proj1 (excursion270_bundle m2) ms S_ds rest2 zl (c + z_0 + 3 + z1 + 2)
                  ((k + 2 * z_0 + 3) + (m1' + 1) + 2 * z1 + 5)
                  Hms19 HS (validTail40_of_validSegs40 Hv_rest2)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  (Nat.le_trans _ _ _ Hms_ox Hm1))
                (fun _ He => exit270_mono He Hm1 Hm2 Hm3)).
           ++ apply chainLeadsUpTo_here; left.
              exists (c + z_0 + 3 + z1); split; [rewrite odw_def; lia |].
              apply (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 S_ds Hv_rest2 ltac:(lia)).
              rewrite Em1_od; lia.
    + pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
      pose proof (goodPhiW_of_ge35 (phiW := c + z_0 - 1) HS_ne2 ltac:(lia)) as Hphiw.
      destruct (S m' =? 1) eqn:Em1.
      * assert (m' = 0) by lia; subst m'.
        assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 S_ds) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
          rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (HS_all (c + z_0 + 1) ltac:(lia)). }
        split; [exact Hg | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
        destruct (arith_fb_m1_ev (c := c) (k := k) (z_0 := z_0) (fz1 := fzOf rest zl) (dx := 1)
          Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hfz1_40 ltac:(lia)) as [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]].
        exact (proj2 (excursion270_bundle N) ms S_ds rest zl (k + 2 * z_0 + 4) 1 (c + z_0 + 1)
          (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
          Hms19 HS (or_intror ltac:(lia)) Hv_rest
          ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi1 Hi2 Hi3 Hi4 Hi5).
      * assert (Hpsi_cz : GoodPsi (c + z_0 - 1) S_ds = true).
        { unfold GoodPsi; replace (c + z_0 - 1 + 1) with (c + z_0) by lia.
          exact (HS_all (c + z_0) ltac:(lia)). }
        destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
        -- assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true)
             by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
           split; [exact Hg | intro N].
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
           destruct (arith_fb_m1_ev (c := c) (k := k) (z_0 := z_0) (fz1 := fzOf rest zl) (dx := 0)
             Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hfz1_40 ltac:(lia)) as [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]].
           rewrite !Nat.add_0_r in Hi1, Hi2, Hi3, Hi4, Hi5.
           exact (proj2 (excursion270_bundle N) ms S_ds rest zl (k + 2 * z_0 + 4) (S m' + 1) (c + z_0)
             (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
             Hms19 HS (or_intror ltac:(lia)) Hv_rest
             ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi1 Hi2 Hi3 Hi4 Hi5).
        -- destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
           ++ pose proof (safeStack_cons (x := c + z_0) HS ltac:(lia) ltac:(lia)) as HS_cz.
              assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                exact (proj2 (proj2 HS_cz) (k + 2 * z_0 + 2) ltac:(lia)). }
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
              replace (S m' - 1) with m' by lia.
              destruct (div10_spec (k + 2 * z_0)) as [q10 [r10 [Hr10 [Hkz10 Hdw10]]]].
              assert (Hne1_cz : ((c + z_0) :: S_ds) <> [1]) by (intro H; inversion H; lia).
              pose proof (proj2 (excursion270_bundle N) 39 ((c + z_0) :: S_ds) rest zl m' 1
                (k + 2 * z_0 + 2) (9 * q10 - 2) (k + 2 * z_0 + 35)
                ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_rest
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H_loop1.
              apply (chainLeadsUpTo_trans H_loop1).
              intros m2 s_mid Hm2 [[phi1 [Hphi1 Hb1]] | [y1 [phi1 [Hy1_tx1 [Hphi1_38 [Hyw1 Hb1]]]]]].
              ** apply chainLeadsUpTo_here; right.
                 destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw [rw [Hrw [Hkw Hoxw]]]].
                 exists (c + z_0), phi1; split; [lia | split; [lia | split; [rewrite Hoxw; lia | exact Hb1]]].
              ** apply (amega_pop_step Hb1 Hphi1_38 ltac:(lia) ltac:(lia)
                   (HS_all (c + z_0 - 1) ltac:(lia)) (fun _ => HS_all (c + z_0 - 2) ltac:(lia))).
                 --- intros Hbig m3 ? p1 p2 Hvp ?.
                     apply chainLeadsUpTo_here; left; exists (c + z_0 - 1).
                     split; [rewrite odw_def; lia | exact (isBounce_r9 (x := c + z_0) (y := y1) ltac:(lia) Hbig Hvp)].
                 --- intros Hy1_le ? m3 ? p1 p2 Hvp Hfzp.
                     assert (Hy1_lo : 9 * ((k + 2 * z_0) / 10) - 2 <= y1) by (rewrite Hdw10; exact Hy1_tx1).
                     destruct (arith_fb_os_r10 (c := c) (k := k) (z_0 := z_0) (y1 := y1) (phi1 := phi1) (fz4 := fzOf p1 p2)
                       Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hy1_lo Hy1_le Hphi1_38 Hyw1 Hfzp) as [Hmo1 [Hmo2 Hmo3]].
                     exact (chainLeadsUpTo_imp
                       (proj1 (excursion270_bundle m3) ms S_ds p1 p2 (c + z_0 + 1) (y1 + 2) Hms19 HS
                         (validTail40_of_validSegs40 Hvp)
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                         (Nat.le_trans _ _ _ Hms_ox Hmo1))
                       (fun _ He => exit270_mono He Hmo1 Hmo2 Hmo3)).
                 --- intros ? ? m3 ? p1 p2 Hvp Hfzp.
                     destruct (arith_fb_os_r11 (c := c) (k := k) (z_0 := z_0) (y1 := y1) (phi1 := phi1) (fz4 := fzOf p1 p2)
                       Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 Hyw1 Hfzp) as [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]].
                     exact (proj2 (excursion270_bundle m3) ms S_ds p1 p2 y1 1 (c + z_0 - 1)
                       (ox (k + 2 * z_0) (c + z_0)) (oxw (k + 2 * z_0) (c + z_0))
                       Hms19 HS (or_intror ltac:(lia)) Hvp
                       ltac:(lia) ltac:(lia) ltac:(lia) Hms_ox Hi1 Hi2 Hi3 Hi4 Hi5).
           ++ assert (Hm_big : 2 * (k + 2 * z_0) + 12 <= S m')
                by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
              assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 S_ds) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
              replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
              apply chainLeadsUpTo_here; right.
              destruct (oxw_spec (k + 2 * z_0) (c + z_0)) as [qw [rw [Hrw [Hkw Hoxw]]]].
              exists (c + z_0), (k + 2 * z_0 + 2).
              split; [lia | split; [lia | split; [rewrite Hoxw; lia |]]].
              replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
              apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest ((c + z_0) :: S_ds) Hv_rest ltac:(lia)).
              destruct (S (m' - 4) mod 2 =? 1); lia.
Qed.
Arguments fbound_advances {ms S_ds segs zl c k} & _ _ _ _ _ _ _ _ _ _.

Lemma ox_ge_of_c {c k fz : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz) :
  c + 38 - (c + 13) / 10 <= ox (k + 2 * fz) (c + fz) /\
  c + 37 - (c + 13) / 10 <= odw (k + 2 * fz) (c + fz).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q [r [Hr [Heq Hox]]]].
  rewrite odw_def, (Hox ltac:(lia)); lia.
Qed.

Lemma ox_ge57_of_cz62 {c k fz : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz)
    (Hcz : 62 <= c + fz) (Hkz : 81 <= k + 2 * fz) :
  57 <= ox (k + 2 * fz) (c + fz) /\ 56 <= odw (k + 2 * fz) (c + fz).
Proof.
  destruct (ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) ltac:(lia)) as [q [r [Hr [Heq Hox]]]].
  rewrite odw_def, (Hox ltac:(lia)); lia.
Qed.

Lemma r9_pop_step {N x y phi : nat} {S_ds : list nat} {sb : SegState} {P : SegState -> Prop}
    (Hb : IsBounce phi (y :: x :: S_ds) sb)
    (Hphi38 : 38 <= phi) (Hx19 : 19 <= x) (Hbig : 2 * x + 5 <= y)
    (Hcont : forall m, m < N -> forall p1 p2, ValidSegs40 p1 p2 -> phi + 2 <= fzOf p1 p2 ->
      ChainLeadsUpTo m (mkSeg true ((0, y - 3) :: p1) p2 (x - 1) 0 (2 * x) S_ds) P) :
  ChainLeadsUpTo N sb P.
Proof.
  assert (Hnrst : isDrainRstDs (y :: x :: S_ds) = false) by (destruct x; [lia | reflexivity]).
  assert (Hnr0 : isRank0 (y :: x :: S_ds) = false) by (destruct y as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop : drainPopGuards phi (y :: x :: S_ds) = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? y) && (1 <=? x)) with true by lia.
    replace ((y mod 2 =? 0) && (y <=? 2 * x + 4)) with false by lia.
    replace ((y mod 2 =? 0) && (y + 14 <=? 2 * x)) with false by lia.
    cbn [negb orb andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_sb [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl (y :: x :: S_ds) =
                mkSeg true ((0, y - 3) :: fst p) (snd p) (x - 1) 0 (2 * x) S_ds).
  { unfold drainPopStep; rewrite Hnrst, Hnr0.
    rw_if_neg ltac:(lia).
    replace (normSeg 0 (y - 3)) with (0, y - 3) by (unfold normSeg; rw_if_neg ltac:(lia); reflexivity).
    reflexivity. }
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp; fold p in Hfzp; clearbody p.
  apply (chainLeadsUpTo_step Hg_sb); intros m Hm; rewrite Hstep, Hdp.
  exact (Hcont m Hm (fst p) (snd p) Hvp Hfzp).
Qed.

Lemma bounce_r9_zero_leads {N d y : nat} {p1 : list (nat * nat)} {p2 : nat}
    (Hd8 : 8 <= d) (Hbig : 2 * d + 5 <= y) (Hvp : ValidSegs40 p1 p2) :
  ChainLeadsUpTo N (mkSeg true ((0, y - 3) :: p1) p2 (d - 1) 0 (2 * d) [0]) RootInv270.
Proof.
  assert (Hy_sub : y - 3 = S (y - 4)) by lia.
  assert (Hpop0 : drainPopGuards (d - 1 + 0) [0] = true)
    by (change (drainPopGuards (d - 1 + 0) [0]) with (2 <=? d - 1 + 0); lia).
  assert (Hg1 : stepGuards (mkSeg true ((0, y - 3) :: p1) p2 (d - 1) 0 (2 * d) [0]) = true).
  { rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia); exact Hpop0. }
  assert (Hs1 : stepSegs (mkSeg true ((0, y - 3) :: p1) p2 (d - 1) 0 (2 * d) [0]) =
                mkSeg true (normSeg (d + 1) (y - 2 * d - 5) :: p1) p2 2 2 6 []).
  { rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia);
      cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb];
      f_equal; f_equal; f_equal; lia. }
  apply (chainLeadsUpTo_step Hg1); intros m1 ?; rewrite Hs1.
  pose proof (fzOf_ge_40 Hvp) as Hfp40.
  destruct (y - 2 * d - 5) as [|mr'] eqn:Emr.
  - cbn [normSeg Nat.eqb].
    assert (Hg2 : stepGuards (mkSeg true ((d + 1 + 1, 0) :: p1) p2 2 2 6 []) = true) by reflexivity.
    apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) (validTail40_of_validSegs40 Hvp)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
  - cbn [normSeg Nat.eqb].
    destruct (S mr' mod 2 =? 1) eqn:Eod.
    + destruct (2 + mr' <=? 6) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((d + 1, S mr') :: p1) p2 2 2 6 []) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
          exact (proj1 (proj2 (safeStack_d (d := 2 + (d + 1)) ltac:(lia)))). }
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
        exact (chainLeadsUpTo_here (rootInv_of_D (d := 2 + (d + 1)) ltac:(lia) (or_introl eq_refl)
          (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      * assert (Hg2 : stepGuards (mkSeg true ((d + 1, S mr') :: p1) p2 2 2 6 []) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg; change (drainPopGuards (2 + (d + 1)) []) with (2 <=? 2 + (d + 1)); lia).
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
        set (q := pushSeg true (2 + (d + 1) + 1) (2 + S mr' - (6 + 2)) p1 p2).
        change (drainPopStep true (2 + (d + 1)) (2 + S mr' - (6 + 2)) p1 p2 [])
          with (mkSeg false (fst q) (snd q) 1 1 0 []).
        assert (Hvtq : ValidTail40 (fst q) (snd q))
          by (unfold q; apply (validTail40_pushSeg true (z := 2 + (d + 1) + 1) (m := 2 + S mr' - (6 + 2)) (fun _ => Hvp)); discriminate).
        pose proof (fzOf_pushSeg_ge true (2 + (d + 1) + 1) (2 + S mr' - (6 + 2)) p1 p2) as Hfzq; fold q in Hfzq; clearbody q.
        exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvtq ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun _ => or_introl (conj eq_refl eq_refl)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
    + destruct (2 + S mr' <=? 6) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((d + 1, S mr') :: p1) p2 2 2 6 []) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg; reflexivity).
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
        exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) (validTail40_of_validSegs40 Hvp)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
          (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
      * assert (Hg2 : stepGuards (mkSeg true ((d + 1, S mr') :: p1) p2 2 2 6 []) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg; change (drainPopGuards (2 + (d + 1)) []) with (2 <=? 2 + (d + 1)); lia).
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Eod, Emrg.
        set (q := pushSeg true (2 + (d + 1) + 1) (2 + S mr' - (6 + 2)) p1 p2).
        change (drainPopStep true (2 + (d + 1)) (2 + S mr' - (6 + 2)) p1 p2 [])
          with (mkSeg false (fst q) (snd q) 1 1 0 []).
        assert (Hvtq : ValidTail40 (fst q) (snd q))
          by (unfold q; apply (validTail40_pushSeg true (z := 2 + (d + 1) + 1) (m := 2 + S mr' - (6 + 2)) (fun _ => Hvp)); discriminate).
        pose proof (fzOf_pushSeg_ge true (2 + (d + 1) + 1) (2 + S mr' - (6 + 2)) p1 p2) as Hfzq; fold q in Hfzq; clearbody q.
        exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvtq ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun _ => or_introl (conj eq_refl eq_refl)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
Qed.
Arguments bounce_r9_zero_leads {N d y p1 p2} & _ _ _.

Lemma bounce_y_8_ge46_leads {N y phi : nat} {s : SegState}
    (Hb : IsBounce phi [y; 8] s) (Hy28 : 28 <= y) (Hphi46 : 46 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hnrst : isDrainRstDs [y; 8] = false) by reflexivity.
  assert (Hnr0 : isRank0 [y; 8] = false) by (destruct y as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop : drainPopGuards phi [y; 8] = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? y) && (1 <=? 8)) with true by lia.
    replace ((y mod 2 =? 0) && (y <=? 2 * 8 + 4)) with false by lia.
    replace ((y mod 2 =? 0) && (y + 14 <=? 2 * 8)) with false by lia.
    cbn [negb orb andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl [y; 8] =
                mkSeg true ((0, S (y - 4)) :: fst p) (snd p) 7 0 16 []).
  { unfold drainPopStep; rewrite Hnrst, Hnr0; cbn [Nat.eqb nat_list_eqb andb].
    replace (normSeg 0 (y - 3)) with (0, S (y - 4)) by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
    reflexivity. }
  rewrite Hdp in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp; fold p in Hfzp; clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hg2 : stepGuards (mkSeg true ((0, S (y - 4)) :: fst p) (snd p) 7 0 16 []) = true).
  { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
  assert (Hs2 : stepSegs (mkSeg true ((0, S (y - 4)) :: fst p) (snd p) 7 0 16 []) =
                mkSeg false ((8, y - 21) :: fst p) (snd p) 1 1 0 []).
  { cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia);
      cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb]; f_equal; f_equal; unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia. }
  apply (chainLeadsUpTo_step1 Hg2); rewrite Hs2; apply chainLeadsUpTo_here.
  refine (rootInv_of_0B (or_introl eq_refl) Hvp ltac:(lia) ltac:(lia) ltac:(lia)
    (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
    (fun H => ltac:(cbn [fzOf] in H; lia)) (fun _ => or_introl (conj eq_refl eq_refl)) _).
  intros z_0 m0 r Hseg ? ? ?; inversion Hseg; subst.
  split; [lia | split; [lia | intro; lia]].
Qed.

Lemma bounce_y_d_small_leads {N d y phi : nat} {tl : list nat} {s : SegState}
    (Hb : IsBounce phi (y :: d :: tl) s)
    (Hd_lo : 8 <= d) (Hd_hi : d <= 18)
    (Htl : tl = [] \/ tl = [0])
    (H8_tl : d = 8 -> tl = [0])
    (Hy39 : 39 <= y) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg1 : 9 <= d -> GoodDs ((d - 1) :: tl) = true).
  { intro Hd9; destruct Htl as [-> | ->].
    - exact (proj1 (proj2 (safeStack_d (d := d - 1) ltac:(lia)))).
    - exact (proj1 (proj2 (safeStack_d0 (d := d - 1) ltac:(lia)))). }
  assert (Hnrst : isDrainRstDs (y :: d :: tl) = false) by (destruct d; [lia | reflexivity]).
  assert (Hnr0 : isRank0 (y :: d :: tl) = false) by (destruct y as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop : drainPopGuards phi (y :: d :: tl) = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? y) && (1 <=? d)) with true by lia.
    assert (Hc2 : (negb ((y mod 2 =? 0) && (y <=? 2 * d + 4)) || GoodDs ((d - 1) :: tl)) = true).
    { destruct (Nat.eq_dec d 8) as [-> | Hd9].
      - replace ((y mod 2 =? 0) && (y <=? 2 * 8 + 4)) with false by lia; reflexivity.
      - rewrite (Hg1 ltac:(lia)), orb_true_r; reflexivity. }
    rewrite Hc2.
    replace ((y mod 2 =? 0) && (y + 14 <=? 2 * d)) with false by lia.
    cbn [negb orb andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl (y :: d :: tl) =
                mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) tl).
  { unfold drainPopStep; rewrite Hnrst, Hnr0.
    rw_if_neg ltac:(lia).
    replace (normSeg 0 (y - 3)) with (0, y - 3) by (unfold normSeg; rw_if_neg ltac:(lia); reflexivity).
    reflexivity. }
  rewrite Hdp in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_ge_40 Hvp) as Hfzp40; clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  destruct (2 * d + 5 <=? y) eqn:Ebig.
  - destruct Htl as [-> | ->].
    + assert (Hd9 : 9 <= d) by (destruct (Nat.eq_dec d 8) as [Heq8 | ?]; [pose proof (H8_tl Heq8); discriminate | lia]).
      assert (Hy_sub : y - 3 = S (y - 4)) by lia.
      assert (Hpop_nil : drainPopGuards (d - 1 + 0) [] = true)
        by (change (drainPopGuards (d - 1 + 0) []) with (2 <=? d - 1 + 0); lia).
      assert (Hg2 : stepGuards (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) []) = true).
      { rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
        destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia); exact Hpop_nil. }
      apply (chainLeadsUpTo_step1 Hg2).
      set (q := pushSeg true (d - 1 + 0 + 1) (0 + S (y - 4) - (2 * d + 2)) (fst p) (snd p)).
      assert (Hs2 : stepSegs (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) []) =
                    mkSeg false (fst q) (snd q) 1 1 0 []).
      { rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
        destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
      rewrite Hs2.
      assert (Hvtq : ValidTail40 (fst q) (snd q))
        by (unfold q; apply (validTail40_pushSeg true (z := d - 1 + 0 + 1) (m := 0 + S (y - 4) - (2 * d + 2)) (fun _ => Hvp)); discriminate).
      pose proof (fzOf_pushSeg_ge true (d - 1 + 0 + 1) (0 + S (y - 4) - (2 * d + 2)) (fst p) (snd p)) as Hfzq; fold q in Hfzq; clearbody q.
      exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvtq ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun _ => or_introl (conj eq_refl eq_refl)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
    + exact (bounce_r9_zero_leads (d := d) (y := y) Hd_lo ltac:(lia) Hvp).
  - assert (d = 18) by lia; subst d.
    destruct (Nat.eq_dec y 39) as [-> | Hy40].
    + assert (Hg2 : stepGuards (mkSeg true ((0, 39 - 3) :: fst p) (snd p) (18 - 1) 0 (2 * 18) tl) = true) by reflexivity.
      apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
      exact (chainLeadsUpTo_here (rootInv_of_0B Htl (validTail40_of_validSegs40 Hvp)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
    + assert (y = 40) by lia; subst y.
      assert (Hg2 : stepGuards (mkSeg true ((0, 40 - 3) :: fst p) (snd p) (18 - 1) 0 (2 * 18) tl) = true)
        by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; exact (Hg1 ltac:(lia))).
      apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
      assert (Hds17 : (17 :: tl) = [17] \/ (17 :: tl) = [17; 0])
        by (destruct Htl as [-> | ->]; [left; reflexivity | right; reflexivity]).
      exact (chainLeadsUpTo_here (rootInv_of_D (d := 17) ltac:(lia) Hds17
        (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.



Arguments bounce_y_8_ge46_leads {N y phi s} & _ _ _.
Arguments bounce_y_d_small_leads {N d y phi tl s} & _ _ _ _ _ _ _.



(* ========================================================================== *)
(* 1. `rootD_advances` (`RootD s -> ChainAdvances s RootInv270`)              *)
(* ========================================================================== *)

Lemma x_8_high_leads {N x zl c k : nat} {segs : list (nat * nat)}
    (Hx41 : 41 <= x) (Hv : ValidSegs40 segs zl)
    (Hc : (66 <= c /\ k = 1) \/ (77 <= c /\ 1 <= k /\ k <= 2 * c + 3)) :
  ChainLeadsUpTo N (mkSeg false segs zl c k 0 [x; 8]) RootInv270.
Proof.
  assert (Hc66 : 66 <= c) by lia.
  assert (Hk1 : 1 <= k) by lia.
  assert (Hkc : k <= 2 * c + 3) by lia.
  pose proof (fzOf_ge_40 Hv) as Hfz40.
  destruct (ox_ge_of_c (c := c) (k := k) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc Hfz40) as [Hox_c Hodw_c].
  assert (Hox97 : 97 <= ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) /\
                  96 <= odw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) by lia.
  pose proof (safeStack_d (d := 8) ltac:(lia)) as HS8_21.
  pose proof (safeStack_mono (m1 := 21) (m2 := 43) ltac:(lia) HS8_21) as HS8.
  assert (Hne1_8 : ([8] : list nat) <> [1]) by (intro H; inversion H).
  pose proof (safeStack_cons_ne1 (x := x) Hne1_8 HS8_21 ltac:(lia) ltac:(lia)) as HSx8.
  pose proof (proj1 (excursion270_bundle N) 19 [x; 8] segs zl c k ltac:(lia) HSx8
    (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
  apply (chainLeadsUpTo_trans Hfb).
  intros m1 s_mid Hm1 [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
  - exact (bounce_y_8_ge46_leads Hb ltac:(lia) ltac:(lia)).
  - apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
      (proj2 (proj2 HS8_21) (x - 1) ltac:(lia))
      (fun _ => proj2 (proj2 HS8_21) (x - 2) ltac:(lia))).
    + intros Hbig ? ? p1 p2 Hvp ?.
      exact (bounce_d_leads (d := 8) (isBounce_r9 (x := x) (y := y) ltac:(lia) Hbig Hvp)
        (or_introl eq_refl) (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
    + intros ? ? ? ? p1 p2 Hvp ?.
      pose proof (fzOf_ge_40 Hvp) as Hfp.
      exact (chainLeadsUpTo_here (rootInv_of_D (d := 8) ltac:(lia) (or_introl eq_refl)
        (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia) ltac:(lia))).
    + intros Hy_le ? m2 ? p1 p2 Hvp ?.
      pose proof (fzOf_ge_40 Hvp) as Hfp.
      destruct (ox_ge_of_c (c := y) (k := 1) (fz := fzOf p1 p2) ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hox_p Hodw_p].
      assert (Hox124 : 124 <= ox (1 + 2 * fzOf p1 p2) (y + fzOf p1 p2) /\
                       123 <= odw (1 + 2 * fzOf p1 p2) (y + fzOf p1 p2)) by lia.
      pose proof (safeStack_cons_ne1 (x := x - 1) Hne1_8 HS8_21 ltac:(lia) ltac:(lia)) as HSx1.
      pose proof (proj1 (excursion270_bundle m2) 19 [x - 1; 8] p1 p2 y 1 ltac:(lia) HSx1
        (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb2.
      apply (chainLeadsUpTo_trans Hfb2).
      intros m3 s_m2 ? [[phi2 [Hphi2 Hb2]] | [y2 [phi2 [Hy2 [Hphi2_38 [_ Hb2]]]]]].
      * exact (bounce_y_8_ge46_leads Hb2 ltac:(lia) ltac:(lia)).
      * apply (amega_pop_step Hb2 Hphi2_38 ltac:(lia) ltac:(lia)
          (proj2 (proj2 HS8_21) (x - 1 - 1) ltac:(lia))
          (fun _ => proj2 (proj2 HS8_21) (x - 1 - 2) ltac:(lia))).
        -- intros Hbig ? ? q1 q2 Hvq ?.
           exact (bounce_d_leads (d := 8) (isBounce_r9 (x := x - 1) (y := y2) ltac:(lia) Hbig Hvq)
             (or_introl eq_refl) (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
        -- intros ? ? ? ? q1 q2 Hvq ?.
           pose proof (fzOf_ge_40 Hvq) as Hfq.
           exact (chainLeadsUpTo_here (rootInv_of_D (d := 8) ltac:(lia) (or_introl eq_refl)
             (validTail40_of_validSegs40 Hvq) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(lia) ltac:(lia) ltac:(lia))).
        -- intros Hy2_le ? m4 ? q1 q2 Hvq ?.
           pose proof (fzOf_ge_40 Hvq) as Hfq.
           pose proof (proj1 (proj2 (fhigh_bundle m4)) [8] q1 q2 y2 1 (x - 1 - 1)
             Hne1_8 HS8 Hvq ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hlh.
           apply (chainLeadsUpTo_trans Hlh).
           intros m5 s_eh ? [[phi3 [Hphi3 Hb3]] | [y3 [phi3 [Hy3 [Hphi3 Hb3]]]]].
           ++ exact (bounce_d_leads (d := 8) Hb3 (or_introl eq_refl)
                (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
           ++ exact (bounce_y_8_ge46_leads Hb3 ltac:(lia) ltac:(lia)).
Qed.
Arguments x_8_high_leads {N x zl c k segs} & _ _ _.

Lemma exitHigh_8_leads {N : nat} {s : SegState} (Heh : ExitHigh [8] s) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  destruct Heh as [[phi [Hphi Hb]] | [y [phi [Hy [Hphi Hb]]]]].
  - exact (bounce_d_leads (d := 8) Hb (or_introl eq_refl)
      (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
  - exact (bounce_y_8_ge46_leads Hb ltac:(lia) ltac:(lia)).
Qed.
Arguments exitHigh_8_leads {N s} & _.

Lemma rootD_advances {s : SegState} (Hb0 : st_b s = false) (Hm0_z : st_mrg s = 0) (Hr : RootD s) :
  ChainAdvances s RootInv270.
Proof.
  destruct s as [b segs zl c k mrg ds]; cbn [st_b st_mrg] in Hb0, Hm0_z; subst b mrg.
  destruct Hr as [[d [Hd8 Hds]] [Hvt [Hc [Hk1 [Hkc [Hfz35 [Hcz42 Hkz73]]]]]]].
  cbn [st_segs st_zl st_cp1 st_kb st_ds] in *.
  destruct (nat_list_eqb ds [8]) eqn:Eds8.
  - apply nat_list_eqb_true in Eds8; subst ds.
    pose proof (safeStack_d (d := 8) ltac:(lia)) as HS8_21.
    pose proof (safeStack_mono (m1 := 21) (m2 := 43) ltac:(lia) HS8_21) as HS8_43.
    assert (Hne1_8 : ([8] : list nat) <> [1]) by (intro H; inversion H).
    destruct segs as [|[z_0 m0] rest].
    + cbn [fzOf ValidTail40] in Hvt, Hfz35, Hcz42, Hkz73.
      assert (Hg : stepGuards (mkSeg false [] zl c k 0 [8]) = true).
      { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
        rewrite (goodPhiW_of_ge35 (phiW := c + zl - 1) (proj1 HS8_21) ltac:(lia)); cbn [andb]; unfold GoodPsi.
        replace (c + zl - 1 + 1) with (c + zl) by lia.
        exact (proj2 (proj2 HS8_21) (c + zl) ltac:(lia)). }
      split; [exact Hg | intro N].
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      assert (Hbc : IsBounce (k + 2 * zl + 2) [c + zl; 8]
                      (mkSeg true [] 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 8])).
      { replace (k + 2 * zl + 2) with ((k + 2 * zl + 2) + 0) at 1 by lia.
        exact (IsBounce_nil 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 8] ltac:(lia)). }
      exact (bounce_y_8_ge46_leads Hbc ltac:(lia) ltac:(lia)).
    + cbn [fzOf ValidTail40] in Hvt, Hfz35, Hcz42, Hkz73.
      assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
      destruct m0 as [|m'].
      * split; [reflexivity | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct rest as [|[z1 [|m1']] rest2].
        -- pose proof (proj2 Hv_rest) as Hzl230.
           exact (bounce_d_leads (d := 8) (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [8] ltac:(lia))
             (or_introl eq_refl) (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [8]) = true)
             by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
           apply (chainLeadsUpTo_step Hg2); intros m2 ?.
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
           exact (chainLeadsUpTo_trans
             (proj1 (fhigh_bundle m2) [8] rest2 zl (c + z_0 + 3 + z1 + 1) (k + 2 * z_0 + 3 + 2 * z1 + 3)
               Hne1_8 HS8_43 Hv_r2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
             (fun _ _ _ Heh => exitHigh_8_leads Heh)).
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           destruct (S m1' mod 2 =? 1) eqn:Em1_od.
           ++ destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [8]) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                   exact (proj2 (proj2 HS8_21) (c + z_0 + 3 + z1) ltac:(lia)). }
                 apply (chainLeadsUpTo_step Hg2); intros m2 ?.
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                 exact (chainLeadsUpTo_trans
                   (proj1 (proj2 (fhigh_bundle m2)) [8] rest2 zl ((k + 2 * z_0 + 3) + m1' + 2 * z1 + 4) 1
                     (c + z_0 + 3 + z1) Hne1_8 HS8_43 Hv_r2
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ _ _ Heh => exitHigh_8_leads Heh)).
              ** apply (bounce_d_leads (d := 8) (phi := c + z_0 + 3 + z1)
                   (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 [8] Hv_r2 ltac:(lia)
                     (ltac:(rewrite Em1_od; lia)))
                   (or_introl eq_refl) (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
           ++ destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [8]) = true)
                   by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg; reflexivity).
                 apply (chainLeadsUpTo_step Hg2); intros m2 ?.
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                 exact (chainLeadsUpTo_trans
                   (proj1 (fhigh_bundle m2) [8] rest2 zl (c + z_0 + 3 + z1 + 2)
                     ((k + 2 * z_0 + 3) + S m1' + 2 * z1 + 5)
                     Hne1_8 HS8_43 Hv_r2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ _ _ Heh => exitHigh_8_leads Heh)).
              ** apply (bounce_d_leads (d := 8) (phi := c + z_0 + 3 + z1)
                   (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 [8] Hv_r2 ltac:(lia)
                     (ltac:(rewrite Em1_od; lia)))
                   (or_introl eq_refl) (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
      * pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
        pose proof (goodPhiW_of_ge35 (phiW := c + z_0 - 1) (proj1 HS8_21) ltac:(lia)) as Hphiw.
        destruct (S m' =? 1) eqn:Em1.
        -- assert (m' = 0) by lia; subst m'.
           assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 [8]) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
             rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (proj2 (proj2 HS8_21) (c + z_0 + 1) ltac:(lia)). }
           split; [exact Hg | intro N].
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
           exact (x_8_high_leads ltac:(lia) Hv_rest (or_intror (conj ltac:(lia) (conj ltac:(lia) ltac:(lia))))).
        -- assert (Hpsi_cz : GoodPsi (c + z_0 - 1) [8] = true).
           { unfold GoodPsi; replace (c + z_0 - 1 + 1) with (c + z_0) by lia.
             exact (proj2 (proj2 HS8_21) (c + z_0) ltac:(lia)). }
           destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
           ++ assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [8]) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
              exact (x_8_high_leads ltac:(lia) Hv_rest (or_intror (conj ltac:(lia) (conj ltac:(lia) ltac:(lia))))).
           ++ destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
              ** pose proof (safeStack_cons_ne1 (x := c + z_0) Hne1_8 HS8_21 ltac:(lia) ltac:(lia)) as HS_cz.
                 assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [8]) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                   exact (proj2 (proj2 HS_cz) (k + 2 * z_0 + 2) ltac:(lia)). }
                 split; [exact Hg | intro N].
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                 assert (Hm'1 : 1 <= m') by (clear - Em1; lia).
                 assert (Hm'_od_le : S m' mod 2 = 1 /\ S m' <= 2 * (k + 2 * z_0) + 11) by (clear - Eod_sm; lia).
                 clear Hg Hphiw Hpsi_cz Em1 Eev_sm Eod_sm.
                 replace (S m' - 1) with m' by lia.
                 assert (Hne1_cz : ([c + z_0; 8] : list nat) <> [1]) by (intro H; inversion H).
                 pose proof (proj2 (excursion270_bundle N) 19 [c + z_0; 8] rest zl m' 1
                   (k + 2 * z_0 + 2) 65 0 ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_rest
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hlb.
                 apply (chainLeadsUpTo_trans Hlb).
                 intros m1 s_mid ? [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
                 --- exact (bounce_y_8_ge46_leads Hb ltac:(lia) ltac:(lia)).
                 --- apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
                       (proj2 (proj2 HS8_21) (c + z_0 - 1) ltac:(lia))
                       (fun _ => proj2 (proj2 HS8_21) (c + z_0 - 2) ltac:(lia))).
                     +++ intros Hbig ? ? p1 p2 Hvp ?.
                         exact (bounce_d_leads (d := 8) (isBounce_r9 (x := c + z_0) (y := y) ltac:(lia) Hbig Hvp)
                           (or_introl eq_refl) (or_introl (conj eq_refl (or_intror (or_intror ltac:(lia)))))).
                     +++ intros ? ? ? ? p1 p2 Hvp ?.
                         pose proof (fzOf_ge_40 Hvp) as Hfp.
                         exact (chainLeadsUpTo_here (rootInv_of_D (d := 8) ltac:(lia) (or_introl eq_refl)
                           (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia)
                           ltac:(lia) ltac:(lia) ltac:(lia))).
                     +++ intros ? ? m2 ? p1 p2 Hvp ?.
                         exact (x_8_high_leads ltac:(lia) Hvp (or_introl (conj ltac:(lia) eq_refl))).
              ** assert (Hm_big : 2 * (k + 2 * z_0) + 12 <= S m')
                   by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
                 assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [8]) = true)
                   by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
                 split; [exact Hg | intro N].
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                 replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                   by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
                 assert (Hbc : IsBounce (k + 2 * z_0 + 2) [c + z_0; 8]
                                 (mkSeg true ((0, S (m' - 4)) :: rest) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) [c + z_0; 8])).
                 { replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
                   apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest [c + z_0; 8] Hv_rest ltac:(lia)).
                   destruct (S (m' - 4) mod 2 =? 1); lia. }
                 exact (bounce_y_8_ge46_leads Hbc ltac:(lia) ltac:(lia)).
  - assert (Hnot8 : ds <> [8]) by (intro H; subst ds; discriminate Eds8).
    assert (HS : SafeStack 21 ds)
      by (destruct Hds as [-> | ->]; [exact (safeStack_d Hd8) | exact (safeStack_d0 Hd8)]).
    destruct (ox_bounds_relaxed (c := c) (k := k) (fz := fzOf segs zl) Hc Hk1 Hkc Hfz35 Hcz42 Hkz73) as [Hox39 _].
    pose proof (fbound_advances (ms := 21) ltac:(lia) HS Hvt Hc Hk1 Hkc Hfz35 Hcz42 Hkz73 ltac:(lia)) as Hadv.
    apply (chainAdvances_trans Hadv); intros s' Hex N.
    destruct Hex as [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
    + assert (Hphi38 : 38 <= phi) by (rewrite odw_def in Hphi; lia).
      apply (bounce_d_leads (d := d) Hb Hds).
      destruct (Nat.eq_dec d 8) as [-> | Hd9]; [left; split; [reflexivity | right; right; exact Hphi38] |].
      destruct (Nat.eq_dec d 9) as [-> | Hd10]; [right; left; split; [reflexivity | lia] |].
      destruct (d <=? 18) eqn:Ed18; [right; right; left; split; [lia | split; [lia | split; [lia | intros ? ?; lia]]] |].
      destruct (Nat.eq_dec d 19) as [-> | Hd20]; [right; right; right; left; split; [reflexivity | lia] |].
      right; right; right; right; split; [lia | exact Hphi38].
    + assert (Htl_ex : exists tl : list nat, ds = d :: tl /\ (tl = [] \/ tl = [0]) /\ (d = 8 -> tl = [0])).
      { destruct Hds as [-> | ->].
        - exists ([] : list nat); split; [reflexivity | split; [left; reflexivity | intro Hd; exfalso; apply Hnot8; subst; reflexivity]].
        - exists [0]; split; [reflexivity | split; [right; reflexivity | intro; reflexivity]]. }
      destruct Htl_ex as [tl [Hds_eq [Htl H8_tl]]].
      rewrite Hds_eq in Hb.
      destruct (d <=? 18) eqn:Ed18.
      * exact (bounce_y_d_small_leads Hb Hd8 ltac:(lia) Htl H8_tl ltac:(lia) Hphi38).
      * assert (Hg1 : GoodDs ((d - 1) :: tl) = true)
          by (destruct Htl as [-> | ->]; [exact (proj1 (proj2 (safeStack_d (d := d - 1) ltac:(lia))))
                                         |exact (proj1 (proj2 (safeStack_d0 (d := d - 1) ltac:(lia))))]).
        assert (Hg2 : GoodDs ((d - 2) :: tl) = true)
          by (destruct Htl as [-> | ->]; [exact (proj1 (proj2 (safeStack_d (d := d - 2) ltac:(lia))))
                                         |exact (proj1 (proj2 (safeStack_d0 (d := d - 2) ltac:(lia))))]).
        apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia) Hg1 (fun _ => Hg2)).
        -- intros Hbig ? ? p1 p2 Hvp ?.
           destruct Htl as [-> | ->].
           ++ exact (bounce_nil_leads (isBounce_r9 (x := d) (y := y) ltac:(lia) Hbig Hvp) ltac:(lia)).
           ++ exact (bounce_r9_zero_leads (d := d) (y := y) ltac:(lia) Hbig Hvp).
        -- intros ? ? ? ? p1 p2 Hvp ?.
           pose proof (fzOf_ge_40 Hvp) as Hfp.
           exact (chainLeadsUpTo_here (rootInv_of_0B Htl (validTail40_of_validSegs40 Hvp)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
        -- intros ? ? ? ? p1 p2 Hvp ?.
           pose proof (fzOf_ge_40 Hvp) as Hfp.
           assert (Hds_d1 : ((d - 1) :: tl) = [d - 1] \/ ((d - 1) :: tl) = [d - 1; 0])
             by (destruct Htl as [-> | ->]; [left; reflexivity | right; reflexivity]).
           exact (chainLeadsUpTo_here (rootInv_of_D (d := d - 1) ltac:(lia) Hds_d1
             (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

(* ========================================================================== *)
(* 2. `rootD1_advances` (`RootD1 s -> ChainAdvances s RootInv270`)            *)
(* ========================================================================== *)

Lemma exit270_d1_leads {N d tx tdw txw : nat} {s : SegState}
    (Hex : Exit270 tx tdw txw [d; 1] s)
    (Hd25 : 25 <= d) (Htx : 43 <= tx) (Htdw : 42 <= tdw)
    (H25_tx : d = 25 -> 57 <= tx) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  destruct Hex as [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
  - exact (bounce_d1_leads (d := d) Hb Hd25 ltac:(lia)).
  - destruct (Nat.eq_dec d 25) as [-> | Hd26].
    + pose proof (H25_tx eq_refl) as H57.
      apply (r9_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)).
      intros ? ? p1 p2 Hvp ?.
      exact (bounce_one_leads (isBounce_r9 (x := 25) (y := y) ltac:(lia) ltac:(lia) Hvp) ltac:(lia)).
    + apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
        (proj2 (proj2 safeStack_one) (d - 1) ltac:(lia))
        (fun _ => proj2 (proj2 safeStack_one) (d - 2) ltac:(lia))).
      * intros Hbig ? ? p1 p2 Hvp ?.
        exact (bounce_one_leads (isBounce_r9 (x := d) (y := y) ltac:(lia) Hbig Hvp) ltac:(lia)).
      * intros ? ? ? ? p1 p2 Hvp ?.
        pose proof (fzOf_ge_40 Hvp) as Hfp.
        exact (chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 Hvp)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
          (fun H => ltac:(lia)) (fun _ => ltac:(lia)))).
      * intros ? ? ? ? p1 p2 Hvp ?.
        pose proof (fzOf_ge_40 Hvp) as Hfp.
        exact (chainLeadsUpTo_here (rootInv_of_D1 (d := d - 1) ltac:(lia) (validTail40_of_validSegs40 Hvp)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.
Arguments exit270_d1_leads {N d tx tdw txw s} & _ _ _ _ _.

Lemma rootD1_advances {s : SegState} (Hb0 : st_b s = false) (Hm0_z : st_mrg s = 0) (Hr : RootD1 s) :
  ChainAdvances s RootInv270.
Proof.
  destruct s as [b segs zl c k mrg ds]; cbn [st_b st_mrg] in Hb0, Hm0_z; subst b mrg.
  destruct Hr as [[d [Hd25 Hds]] [Hvt [Hc [Hk1 [Hkc [Hfz40 [Hcz62 Hkz81]]]]]]].
  cbn [st_segs st_zl st_cp1 st_kb st_ds] in *; subst ds.
  destruct (Nat.eq_dec d 25) as [-> | Hd26].
  - pose proof safeStack_25_1 as HS55.
    assert (Hne1 : ([25; 1] : list nat) <> [1]) by (intro H; inversion H).
    destruct segs as [|[z_0 m0] rest].
    + cbn [fzOf ValidTail40] in Hvt, Hfz40, Hcz62, Hkz81.
      assert (Hg : stepGuards (mkSeg false [] zl c k 0 [25; 1]) = true).
      { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
        rewrite (goodPhiW_of_ge35 (phiW := c + zl - 1) (proj1 HS55) ltac:(lia)); cbn [andb]; unfold GoodPsi.
        replace (c + zl - 1 + 1) with (c + zl) by lia.
        exact (proj2 (proj2 HS55) (c + zl) ltac:(lia)). }
      split; [exact Hg | intro N].
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      assert (Hbc : IsBounce (k + 2 * zl + 2) [c + zl; 25; 1]
                      (mkSeg true [] 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 25; 1])).
      { replace (k + 2 * zl + 2) with ((k + 2 * zl + 2) + 0) at 1 by lia.
        exact (IsBounce_nil 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 25; 1] ltac:(lia)). }
      exact (exit270_d1_leads (d := 25) (tx := 57) (tdw := 42) (txw := 0)
        ltac:(right; exists (c + zl), (k + 2 * zl + 2); repeat split; [lia | lia | lia | exact Hbc]) ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia))).
    + cbn [fzOf ValidTail40] in Hvt, Hfz40, Hcz62, Hkz81.
      assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
      destruct m0 as [|m'].
      * split; [reflexivity | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct rest as [|[z1 [|m1']] rest2].
        -- pose proof (proj2 Hv_rest) as Hzl230.
           exact (bounce_d1_leads (d := 25) (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [25; 1] ltac:(lia))
             ltac:(lia) ltac:(lia)).
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [25; 1]) = true)
             by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
           apply (chainLeadsUpTo_step Hg2); intros m2 ?.
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
           destruct (ox_ge_of_c (c := c + z_0 + 3 + z1 + 1) (k := k + 2 * z_0 + 3 + 2 * z1 + 3)
             (fz := fzOf rest2 zl) ltac:(lia) ltac:(lia) ltac:(lia) Hfz2_40) as [Hox Hodw].
           exact (chainLeadsUpTo_trans
             (proj1 (excursion270_bundle m2) 55 [25; 1] rest2 zl (c + z_0 + 3 + z1 + 1)
               (k + 2 * z_0 + 3 + 2 * z1 + 3) ltac:(lia) HS55 (validTail40_of_validSegs40 Hv_r2)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
             (fun _ _ _ Hex => exit270_d1_leads Hex ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           destruct (S m1' mod 2 =? 1) eqn:Em1_od.
           ++ destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [25; 1]) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                   exact (proj2 (proj2 HS55) (c + z_0 + 3 + z1) ltac:(lia)). }
                 apply (chainLeadsUpTo_step Hg2); intros m2 ?.
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                 exact (chainLeadsUpTo_trans
                   (proj2 (excursion270_bundle m2) 55 [25; 1] rest2 zl
                     ((k + 2 * z_0 + 3) + m1' + 2 * z1 + 4) 1 (c + z_0 + 3 + z1) 57 0
                     ltac:(lia) HS55 (or_introl Hne1) Hv_r2
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ _ _ Hex => exit270_d1_leads Hex ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
              ** exact (bounce_d1_leads (d := 25)
                   (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 [25; 1] Hv_r2 ltac:(lia)
                     (ltac:(rewrite Em1_od; lia)))
                   ltac:(lia) ltac:(lia)).
           ++ destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [25; 1]) = true)
                   by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg; reflexivity).
                 apply (chainLeadsUpTo_step Hg2); intros m2 ?.
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                 destruct (ox_ge_of_c (c := c + z_0 + 3 + z1 + 2)
                   (k := (k + 2 * z_0 + 3) + S m1' + 2 * z1 + 5)
                   (fz := fzOf rest2 zl) ltac:(lia) ltac:(lia) ltac:(lia) Hfz2_40) as [Hox Hodw].
                 exact (chainLeadsUpTo_trans
                   (proj1 (excursion270_bundle m2) 55 [25; 1] rest2 zl (c + z_0 + 3 + z1 + 2)
                     ((k + 2 * z_0 + 3) + S m1' + 2 * z1 + 5)
                     ltac:(lia) HS55 (validTail40_of_validSegs40 Hv_r2)
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ _ _ Hex => exit270_d1_leads Hex ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
              ** exact (bounce_d1_leads (d := 25)
                   (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 [25; 1] Hv_r2 ltac:(lia)
                     (ltac:(rewrite Em1_od; lia)))
                   ltac:(lia) ltac:(lia)).
      * pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
        pose proof (goodPhiW_of_ge35 (phiW := c + z_0 - 1) (proj1 HS55) ltac:(lia)) as Hphiw.
        destruct (S m' =? 1) eqn:Em1.
        -- assert (m' = 0) by lia; subst m'.
           assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 [25; 1]) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
             rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (proj2 (proj2 HS55) (c + z_0 + 1) ltac:(lia)). }
           split; [exact Hg | intro N].
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
           exact (chainLeadsUpTo_trans
             (proj2 (excursion270_bundle N) 55 [25; 1] rest zl (k + 2 * z_0 + 4) 1 (c + z_0 + 1) 57 0
               ltac:(lia) HS55 (or_introl Hne1) Hv_rest
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
             (fun _ _ _ Hex => exit270_d1_leads Hex ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
        -- assert (Hpsi_cz : GoodPsi (c + z_0 - 1) [25; 1] = true).
           { unfold GoodPsi; replace (c + z_0 - 1 + 1) with (c + z_0) by lia.
             exact (proj2 (proj2 HS55) (c + z_0) ltac:(lia)). }
           destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
           ++ assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [25; 1]) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
              exact (chainLeadsUpTo_trans
                (proj2 (excursion270_bundle N) 55 [25; 1] rest zl (k + 2 * z_0 + 4) (S m' + 1) (c + z_0) 57 0
                  ltac:(lia) HS55 (or_introl Hne1) Hv_rest
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                (fun _ _ _ Hex => exit270_d1_leads Hex ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
           ++ destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
              ** pose proof (safeStack_cons_ne1 (x := c + z_0) Hne1 HS55 ltac:(lia) ltac:(lia)) as HS_cz.
                 assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [25; 1]) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                   exact (proj2 (proj2 HS_cz) (k + 2 * z_0 + 2) ltac:(lia)). }
                 split; [exact Hg | intro N].
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                 assert (Hm'1 : 1 <= m') by (clear - Em1; lia).
                 assert (Hm'_od_le : S m' mod 2 = 1 /\ S m' <= 2 * (k + 2 * z_0) + 11) by (clear - Eod_sm; lia).
                 clear Hg Hphiw Hpsi_cz Em1 Eev_sm Eod_sm.
                 replace (S m' - 1) with m' by lia.
                 assert (Hne1_cz : ([c + z_0; 25; 1] : list nat) <> [1]) by (intro H; inversion H).
                 pose proof (proj2 (excursion270_bundle N) 19 [c + z_0; 25; 1] rest zl m' 1
                   (k + 2 * z_0 + 2) 65 0 ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_rest
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hlb.
                 apply (chainLeadsUpTo_trans Hlb).
                 intros m1 s_mid ? [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
                 --- exact (exit270_d1_leads (d := 25) (tx := 57) (tdw := 42) (txw := 0)
                       ltac:(right; exists (c + z_0), phi; repeat split; [lia | lia | lia | exact Hb]) ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia))).
                 --- apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
                       (proj2 (proj2 HS55) (c + z_0 - 1) ltac:(lia))
                       (fun _ => proj2 (proj2 HS55) (c + z_0 - 2) ltac:(lia))).
                     +++ intros Hbig ? ? p1 p2 Hvp ?.
                         exact (bounce_d1_leads (d := 25) (isBounce_r9 (x := c + z_0) (y := y) ltac:(lia) Hbig Hvp)
                           ltac:(lia) ltac:(lia)).
                     +++ intros ? ? m2 ? p1 p2 Hvp ?.
                         pose proof (fzOf_ge_40 Hvp) as Hfp.
                         destruct (ox_ge_of_c (c := c + z_0 + 1) (k := y + 2) (fz := fzOf p1 p2)
                           ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hox Hodw].
                         exact (chainLeadsUpTo_trans
                           (proj1 (excursion270_bundle m2) 55 [25; 1] p1 p2 (c + z_0 + 1) (y + 2)
                             ltac:(lia) HS55 (validTail40_of_validSegs40 Hvp)
                             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                           (fun _ _ _ Hex2 => exit270_d1_leads Hex2 ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
                     +++ intros ? ? m2 ? p1 p2 Hvp ?.
                         pose proof (fzOf_ge_40 Hvp) as Hfp.
                         exact (chainLeadsUpTo_trans
                           (proj2 (excursion270_bundle m2) 55 [25; 1] p1 p2 y 1 (c + z_0 - 1) 57 0
                             ltac:(lia) HS55 (or_introl Hne1) Hvp
                             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                           (fun _ _ _ Hex2 => exit270_d1_leads Hex2 ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
              ** assert (Hm_big : 2 * (k + 2 * z_0) + 12 <= S m')
                   by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
                 assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [25; 1]) = true)
                   by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
                 split; [exact Hg | intro N].
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                 replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                   by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
                 assert (Hbc : IsBounce (k + 2 * z_0 + 2) [c + z_0; 25; 1]
                                 (mkSeg true ((0, S (m' - 4)) :: rest) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) [c + z_0; 25; 1])).
                 { replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
                   apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest [c + z_0; 25; 1] Hv_rest ltac:(lia)).
                   destruct (S (m' - 4) mod 2 =? 1); lia. }
                 exact (exit270_d1_leads (d := 25) (tx := 57) (tdw := 42) (txw := 0)
                   ltac:(right; exists (c + z_0), (k + 2 * z_0 + 2); repeat split; [lia | lia | lia | exact Hbc]) ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia))).
  - pose proof (safeStack_d1 (d := d) ltac:(lia)) as HS.
    destruct (ox_ge57_of_cz62 (c := c) (k := k) (fz := fzOf segs zl) Hc Hk1 Hkc Hfz40 Hcz62 Hkz81) as [Hox57 Hodw56].
    pose proof (fbound_advances (ms := 39) (c := c) (k := k) ltac:(lia) HS Hvt ltac:(lia) Hk1 Hkc
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hadv.
    exact (chainAdvances_trans Hadv
      (fun _ Hex _ => exit270_d1_leads Hex Hd25 ltac:(lia) ltac:(lia) (fun H25 => False_ind _ (Hd26 H25)))).
Qed.

(* ========================================================================== *)
(* 3. `root1_advances` (`Root1 s -> ChainAdvances s RootInv270`)              *)
(* ========================================================================== *)



Lemma ox_ge_lin {c k fz : nat}
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hfz : 40 <= fz) :
  9 * c + 367 <= 10 * ox (k + 2 * fz) (c + fz) /\
  9 * c + 357 <= 10 * odw (k + 2 * fz) (c + fz).
Proof.
  pose proof (ox_ge_of_c Hc Hk1 Hkc Hfz) as H.
  lia.
Qed.

Lemma pop_47_25_1_leads {N phi : nat} {s : SegState}
    (Hb : IsBounce phi [47; 25; 1] s) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi [47; 25; 1] = true)
    by (change (drainPopGuards phi [47; 25; 1]) with (true && true && true && (16 <=? phi)); cbn [andb]; lia).
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  change (drainPopStep hp phi m_rem rest zl [47; 25; 1])
    with (mkSeg true ((0, 44) :: fst p) (snd p) 24 0 50 [1]) in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_ge_40 Hvp) as Hfp; clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hg2 : stepGuards (mkSeg true ((0, 44) :: fst p) (snd p) 24 0 50 [1]) = true) by reflexivity.
  apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
  exact (chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 Hvp)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (fun H => ltac:(lia)) (fun _ => ltac:(lia)))).
Qed.
Arguments pop_47_25_1_leads {N phi s} & _ _.

Lemma exit_47_25_1_leads {N tx tdw txw : nat} {s : SegState}
    (Hex : Exit270 tx tdw txw [47; 25; 1] s)
    (Htx99 : 99 <= tx) (Htdw38 : 38 <= tdw) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  destruct Hex as [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
  - exact (pop_47_25_1_leads Hb ltac:(lia)).
  - apply (r9_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)).
    intros ? ? p1 p2 Hvp ?.
    exact (bounce_d1_leads (d := 25) (isBounce_r9 (x := 47) (y := y) ltac:(lia) ltac:(lia) Hvp) ltac:(lia) ltac:(lia)).
Qed.
Arguments exit_47_25_1_leads {N tx tdw txw s} & _ _ _.

Lemma x_47_25_1_high_leads {N x zl c k : nat} {segs : list (nat * nat)}
    (Hx101 : 101 <= x) (Hv : ValidSegs40 segs zl)
    (Hc : (170 <= c /\ k = 1) \/ (189 <= c /\ 1 <= k /\ k <= 2 * c + 3)) :
  ChainLeadsUpTo N (mkSeg false segs zl c k 0 [x; 47; 25; 1]) RootInv270.
Proof.
  assert (Hc170 : 170 <= c) by lia.
  assert (Hk1 : 1 <= k) by lia.
  assert (Hkc : k <= 2 * c + 3) by lia.
  pose proof (fzOf_ge_40 Hv) as Hfz40.
  pose proof safeStack_47_25_1 as HS47.
  assert (Hne1 : ([47; 25; 1] : list nat) <> [1]) by discriminate.
  destruct (105 <=? x) eqn:Ex105.
  - exact (chainLeadsUpTo_trans
      (proj2 (excursion270_bundle N) 99 [47; 25; 1] segs zl c k x 101 0
        ltac:(lia) HS47 (or_introl Hne1) Hv
        ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      (fun _ _ _ Hex => exit_47_25_1_leads Hex ltac:(lia) ltac:(lia))).
  - destruct (ox_ge_lin (c := c) (k := k) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc Hfz40) as [Hox190 Hodw190].
    pose proof (safeStack_cons_ne1 (x := x) Hne1 HS47 ltac:(lia) ltac:(lia)) as HSx.
    pose proof (proj1 (excursion270_bundle N) 19 [x; 47; 25; 1] segs zl c k ltac:(lia) HSx
      (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
    apply (chainLeadsUpTo_trans Hfb).
    intros m1 s_mid ? [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
    + exact (exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0)
        ltac:(right; exists x, phi; repeat split; [lia | lia | lia | exact Hb]) ltac:(lia) ltac:(lia)).
    + apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
        (proj2 (proj2 HS47) (x - 1) ltac:(lia))
        (fun _ => proj2 (proj2 HS47) (x - 2) ltac:(lia))).
      * intros Hbig ? ? p1 p2 Hvp ?.
        exact (pop_47_25_1_leads (isBounce_r9 (x := x) (y := y) ltac:(lia) Hbig Hvp) ltac:(lia)).
      * intros ? ? m2 ? p1 p2 Hvp ?.
        pose proof (fzOf_ge_40 Hvp) as Hfp.
        destruct (ox_ge_lin (c := x + 1) (k := y + 2) (fz := fzOf p1 p2) ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hox129 Hodw129].
        exact (chainLeadsUpTo_trans
          (proj1 (excursion270_bundle m2) 99 [47; 25; 1] p1 p2 (x + 1) (y + 2)
            ltac:(lia) HS47 (validTail40_of_validSegs40 Hvp)
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          (fun _ _ _ Hex2 => exit_47_25_1_leads Hex2 ltac:(lia) ltac:(lia))).
      * intros ? ? m2 ? p1 p2 Hvp ?.
        pose proof (fzOf_ge_40 Hvp) as Hfp.
        destruct (ox_ge_lin (c := y) (k := 1) (fz := fzOf p1 p2) ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hox208 Hodw208].
        destruct (Nat.eq_dec x 101) as [-> | Hx102].
        -- change (101 - 1) with 100.
           apply (fbound_force_r9 (x := 100) (d3 := 47) (ds3 := [25; 1]) (c := y) (k := 1) ltac:(lia)
             (proj2 (proj2 HS47) 100 ltac:(lia)) (proj2 (proj2 HS47) 99 ltac:(lia)) Hvp
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
           ++ intros ? phi2 ? Hphi2 ? Hb2.
              exact (exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0)
                ltac:(right; exists 100, phi2; repeat split; [lia | lia | lia | exact Hb2]) ltac:(lia) ltac:(lia)).
           ++ intros ? ? ? Hb2.
              exact (pop_47_25_1_leads Hb2 ltac:(lia)).
        -- pose proof (safeStack_cons_ne1 (x := x - 1) Hne1 HS47 ltac:(lia) ltac:(lia)) as HSx1.
           pose proof (proj1 (excursion270_bundle m2) 19 [x - 1; 47; 25; 1] p1 p2 y 1
             ltac:(lia) HSx1 (validTail40_of_validSegs40 Hvp)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb2.
           apply (chainLeadsUpTo_trans Hfb2).
           intros m3 s_m2 ? [[phi2 [Hphi2 Hb2]] | [y2 [phi2 [Hy2 [Hphi2_38 [_ Hb2]]]]]].
           ++ exact (exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0)
                ltac:(right; exists (x - 1), phi2; repeat split; [lia | lia | lia | exact Hb2]) ltac:(lia) ltac:(lia)).
           ++ apply (amega_pop_step Hb2 Hphi2_38 ltac:(lia) ltac:(lia)
                (proj2 (proj2 HS47) (x - 1 - 1) ltac:(lia))
                (fun _ => proj2 (proj2 HS47) (x - 1 - 2) ltac:(lia))).
              ** intros Hbig ? ? q1 q2 Hvq ?.
                 exact (pop_47_25_1_leads (isBounce_r9 (x := x - 1) (y := y2) ltac:(lia) Hbig Hvq) ltac:(lia)).
              ** intros ? ? m4 ? q1 q2 Hvq ?.
                 pose proof (fzOf_ge_40 Hvq) as Hfq.
                 destruct (ox_ge_lin (c := x - 1 + 1) (k := y2 + 2) (fz := fzOf q1 q2)
                   ltac:(lia) ltac:(lia) ltac:(lia) Hfq) as [Hox129 Hodw129].
                 exact (chainLeadsUpTo_trans
                   (proj1 (excursion270_bundle m4) 99 [47; 25; 1] q1 q2 (x - 1 + 1) (y2 + 2)
                     ltac:(lia) HS47 (validTail40_of_validSegs40 Hvq)
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ _ _ Hex3 => exit_47_25_1_leads Hex3 ltac:(lia) ltac:(lia))).
              ** intros ? ? ? ? q1 q2 Hvq ?.
                 pose proof (fzOf_ge_40 Hvq) as Hfq.
                 destruct (ox_ge_lin (c := y2) (k := 1) (fz := fzOf q1 q2) ltac:(lia) ltac:(lia) ltac:(lia) Hfq) as [Hox224 Hodw224].
                 apply (fbound_force_r9 (x := x - 1 - 1) (d3 := 47) (ds3 := [25; 1]) (c := y2) (k := 1) ltac:(lia)
                   (proj2 (proj2 HS47) (x - 1 - 1) ltac:(lia)) (proj2 (proj2 HS47) (x - 1 - 1 - 1) ltac:(lia)) Hvq
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
                 --- intros ? phi3 ? Hphi3 ? Hb3.
                     exact (exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0)
                       ltac:(right; exists (x - 1 - 1), phi3; repeat split; [lia | lia | lia | exact Hb3]) ltac:(lia) ltac:(lia)).
                 --- intros ? ? ? Hb3.
                     exact (pop_47_25_1_leads Hb3 ltac:(lia)).
Qed.
Arguments x_47_25_1_high_leads {N x zl c k segs} & _ _ _.

Lemma stack_47_25_1_leads {N zl c1 : nat} {segs : list (nat * nat)}
    (Hv : ValidSegs40 segs zl) (Hc1 : 6 <= c1)
    (Hcz102 : 102 <= c1 + fzOf segs zl) (Hkz185 : 185 <= 1 + 2 * fzOf segs zl) :
  ChainLeadsUpTo N (mkSeg false segs zl c1 1 0 [47; 25; 1]) RootInv270.
Proof.
  pose proof safeStack_47_25_1 as HS47.
  assert (Hne1 : ([47; 25; 1] : list nat) <> [1]) by discriminate.
  destruct segs as [|[z1 m1] rest].
  - pose proof (proj2 Hv) as Hzl230.
    assert (Hg : stepGuards (mkSeg false [] zl c1 1 0 [47; 25; 1]) = true).
    { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
      rewrite (goodPhiW_of_ge35 (phiW := c1 + zl - 1) (proj1 HS47) ltac:(lia)); cbn [andb]; unfold GoodPsi.
      replace (c1 + zl - 1 + 1) with (c1 + zl) by lia.
      exact (proj2 (proj2 HS47) (c1 + zl) ltac:(lia)). }
    apply (chainLeadsUpTo_step1 Hg); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    assert (Hbc : IsBounce (1 + 2 * zl + 2) [c1 + zl; 47; 25; 1]
                    (mkSeg true [] 0 (1 + 2 * zl + 2) 0 (2 * (1 + 2 * zl) + 6) [c1 + zl; 47; 25; 1])).
    { replace (1 + 2 * zl + 2) with ((1 + 2 * zl + 2) + 0) at 1 by lia.
      exact (IsBounce_nil 0 (1 + 2 * zl + 2) 0 (2 * (1 + 2 * zl) + 6) [c1 + zl; 47; 25; 1] ltac:(lia)). }
    exact (exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0)
      ltac:(right; exists (c1 + zl), (1 + 2 * zl + 2); repeat split; [lia | lia | lia | exact Hbc]) ltac:(lia) ltac:(lia)).
  - cbn [fzOf] in Hcz102, Hkz185.
    pose proof (validSegs40_tail Hv) as Hv_rest.
    destruct m1 as [|m'].
    + assert (Hg1 : stepGuards (mkSeg false ((z1, 0) :: rest) zl c1 1 0 [47; 25; 1]) = true) by reflexivity.
      apply (chainLeadsUpTo_step Hg1); intros m_a ?.
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      destruct rest as [|[z2 [|m2']] rest2].
      * pose proof (proj2 Hv_rest) as Hzl230.
        exact (pop_47_25_1_leads (IsBounce_nil zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) [47; 25; 1] ltac:(lia)) ltac:(lia)).
      * pose proof (fzOf_ge_40 Hv_rest) as Hz2_40; cbn [fzOf] in Hz2_40.
        pose proof (validSegs40_tail Hv_rest) as Hv_r2.
        pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
        assert (Hg2 : stepGuards (mkSeg true ((z2, 0) :: rest2) zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) [47; 25; 1]) = true)
          by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
        apply (chainLeadsUpTo_step Hg2); intros m_b ?.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct (ox_ge_lin (c := c1 + z1 + 3 + z2 + 1) (k := 1 + 2 * z1 + 3 + 2 * z2 + 3)
          (fz := fzOf rest2 zl) ltac:(lia) ltac:(lia) ltac:(lia) Hfz2_40) as [Hox Hodw].
        exact (chainLeadsUpTo_trans
          (proj1 (excursion270_bundle m_b) 99 [47; 25; 1] rest2 zl (c1 + z1 + 3 + z2 + 1)
            (1 + 2 * z1 + 3 + 2 * z2 + 3) ltac:(lia) HS47 (validTail40_of_validSegs40 Hv_r2)
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          (fun _ _ _ Hex => exit_47_25_1_leads Hex ltac:(lia) ltac:(lia))).
      * pose proof (fzOf_ge_40 Hv_rest) as Hz2_40; cbn [fzOf] in Hz2_40.
        pose proof (validSegs40_tail Hv_rest) as Hv_r2.
        pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
        destruct (S m2' mod 2 =? 1) eqn:Em2_od.
        -- destruct ((1 + 2 * z1 + 3) + m2' <=? 2 * (c1 + z1) + 8) eqn:Emrg.
           ++ assert (Hg2 : stepGuards (mkSeg true ((z2, S m2') :: rest2) zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) [47; 25; 1]) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em2_od, Emrg.
                exact (proj2 (proj2 HS47) (c1 + z1 + 3 + z2) ltac:(lia)). }
              apply (chainLeadsUpTo_step Hg2); intros m_b ?.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em2_od, Emrg.
              exact (x_47_25_1_high_leads ltac:(lia) Hv_r2 (or_introl (conj ltac:(lia) eq_refl))).
           ++ exact (pop_47_25_1_leads
                (IsBounce_cons z2 m2' zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) rest2 [47; 25; 1] Hv_r2 ltac:(lia)
                  (ltac:(rewrite Em2_od; lia)))
                ltac:(lia)).
        -- destruct ((1 + 2 * z1 + 3) + S m2' <=? 2 * (c1 + z1) + 8) eqn:Emrg.
           ++ assert (Hg2 : stepGuards (mkSeg true ((z2, S m2') :: rest2) zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) [47; 25; 1]) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em2_od, Emrg; reflexivity).
              apply (chainLeadsUpTo_step Hg2); intros m_b ?.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em2_od, Emrg.
              destruct (ox_ge_lin (c := c1 + z1 + 3 + z2 + 2)
                (k := (1 + 2 * z1 + 3) + S m2' + 2 * z2 + 5)
                (fz := fzOf rest2 zl) ltac:(lia) ltac:(lia) ltac:(lia) Hfz2_40) as [Hox Hodw].
              exact (chainLeadsUpTo_trans
                (proj1 (excursion270_bundle m_b) 99 [47; 25; 1] rest2 zl (c1 + z1 + 3 + z2 + 2)
                  ((1 + 2 * z1 + 3) + S m2' + 2 * z2 + 5)
                  ltac:(lia) HS47 (validTail40_of_validSegs40 Hv_r2)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                (fun _ _ _ Hex => exit_47_25_1_leads Hex ltac:(lia) ltac:(lia))).
           ++ exact (pop_47_25_1_leads
                (IsBounce_cons z2 m2' zl (c1 + z1 + 3) (1 + 2 * z1 + 3) (2 * (c1 + z1) + 8) rest2 [47; 25; 1] Hv_r2 ltac:(lia)
                  (ltac:(rewrite Em2_od; lia)))
                ltac:(lia)).
    + pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
      pose proof (goodPhiW_of_ge35 (phiW := c1 + z1 - 1) (proj1 HS47) ltac:(lia)) as Hphiw.
      destruct (S m' =? 1) eqn:Em1.
      * assert (m' = 0) by lia; subst m'.
        assert (Hg : stepGuards (mkSeg false ((z1, 1) :: rest) zl c1 1 0 [47; 25; 1]) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
          rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (proj2 (proj2 HS47) (c1 + z1 + 1) ltac:(lia)). }
        apply (chainLeadsUpTo_step Hg); intros m_a ?.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
        exact (x_47_25_1_high_leads ltac:(lia) Hv_rest (or_introl (conj ltac:(lia) eq_refl))).
      * assert (Hpsi_cz : GoodPsi (c1 + z1 - 1) [47; 25; 1] = true).
        { unfold GoodPsi; replace (c1 + z1 - 1 + 1) with (c1 + z1) by lia.
          exact (proj2 (proj2 HS47) (c1 + z1) ltac:(lia)). }
        destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (1 + 2 * z1) + 10)) eqn:Eev_sm.
        -- assert (Hg : stepGuards (mkSeg false ((z1, S m') :: rest) zl c1 1 0 [47; 25; 1]) = true)
             by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
           apply (chainLeadsUpTo_step Hg); intros m_a ?.
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
           exact (x_47_25_1_high_leads ltac:(lia) Hv_rest (or_intror (conj ltac:(lia) (conj ltac:(lia) ltac:(lia))))).
        -- destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (1 + 2 * z1) + 11)) eqn:Eod_sm.
           ++ pose proof (safeStack_cons_ne1 (x := c1 + z1) Hne1 HS47 ltac:(lia) ltac:(lia)) as HS_cz.
              assert (Hg : stepGuards (mkSeg false ((z1, S m') :: rest) zl c1 1 0 [47; 25; 1]) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                exact (proj2 (proj2 HS_cz) (1 + 2 * z1 + 2) ltac:(lia)). }
              apply (chainLeadsUpTo_step Hg); intros m_a ?.
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
              assert (Hm'1 : 1 <= m') by (clear - Em1; lia).
              assert (Hm'_od_le : S m' mod 2 = 1 /\ S m' <= 2 * (1 + 2 * z1) + 11) by (clear - Eod_sm; lia).
              clear Hg Hphiw Hpsi_cz Em1 Eev_sm Eod_sm.
              replace (S m' - 1) with m' by lia.
              assert (Hne1_cz : ([c1 + z1; 47; 25; 1] : list nat) <> [1]) by discriminate.
              pose proof (proj2 (excursion270_bundle m_a) 19 [c1 + z1; 47; 25; 1] rest zl m' 1
                (1 + 2 * z1 + 2) 170 0 ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_rest
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hlb.
              apply (chainLeadsUpTo_trans Hlb).
              intros m_b s_mid ? [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
              ** exact (exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0)
                   ltac:(right; exists (c1 + z1), phi; repeat split; [lia | lia | lia | exact Hb]) ltac:(lia) ltac:(lia)).
              ** apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
                   (proj2 (proj2 HS47) (c1 + z1 - 1) ltac:(lia))
                   (fun _ => proj2 (proj2 HS47) (c1 + z1 - 2) ltac:(lia))).
                 --- intros Hbig ? ? p1 p2 Hvp ?.
                     exact (pop_47_25_1_leads (isBounce_r9 (x := c1 + z1) (y := y) ltac:(lia) Hbig Hvp) ltac:(lia)).
                 --- intros ? ? m_c ? p1 p2 Hvp ?.
                     pose proof (fzOf_ge_40 Hvp) as Hfp.
                     destruct (ox_ge_lin (c := c1 + z1 + 1) (k := y + 2) (fz := fzOf p1 p2)
                       ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hox Hodw].
                     exact (chainLeadsUpTo_trans
                       (proj1 (excursion270_bundle m_c) 99 [47; 25; 1] p1 p2 (c1 + z1 + 1) (y + 2)
                         ltac:(lia) HS47 (validTail40_of_validSegs40 Hvp)
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                       (fun _ _ _ Hex2 => exit_47_25_1_leads Hex2 ltac:(lia) ltac:(lia))).
                 --- intros ? ? ? ? p1 p2 Hvp ?.
                     exact (x_47_25_1_high_leads ltac:(lia) Hvp (or_introl (conj ltac:(lia) eq_refl))).
           ++ assert (Hm_big : 2 * (1 + 2 * z1) + 12 <= S m')
                by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
              assert (Hg : stepGuards (mkSeg false ((z1, S m') :: rest) zl c1 1 0 [47; 25; 1]) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
              apply (chainLeadsUpTo_step1 Hg).
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
              replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
              assert (Hbc : IsBounce (1 + 2 * z1 + 2) [c1 + z1; 47; 25; 1]
                              (mkSeg true ((0, S (m' - 4)) :: rest) zl (1 + 2 * z1 + 2) 0 (2 * (1 + 2 * z1) + 6) [c1 + z1; 47; 25; 1])).
              { replace (1 + 2 * z1 + 2) with ((1 + 2 * z1 + 2) + 0) at 1 by lia.
                apply (IsBounce_cons 0 (m' - 4) zl (1 + 2 * z1 + 2) 0 (2 * (1 + 2 * z1) + 6) rest [c1 + z1; 47; 25; 1] Hv_rest ltac:(lia)).
                destruct (S (m' - 4) mod 2 =? 1); lia. }
              exact (exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0)
                ltac:(right; exists (c1 + z1), (1 + 2 * z1 + 2); repeat split; [lia | lia | lia | exact Hbc]) ltac:(lia) ltac:(lia)).
Qed.
Arguments stack_47_25_1_leads {N zl c1 segs} & _ _ _ _.

Lemma root1_advances {s : SegState} (Hb0 : st_b s = false) (Hm0_z : st_mrg s = 0) (Hr : Root1 s) :
  ChainAdvances s RootInv270.
Proof.
  destruct s as [b segs zl c k mrg ds]; cbn [st_b st_mrg] in Hb0, Hm0_z; subst b mrg.
  destruct Hr as [Hds [Hvt [Hc5 [Hk1 [Hkc [Hfz20 [Hkz45 [H25 H26]]]]]]]].
  cbn [st_segs st_zl st_cp1 st_kb st_ds] in *; subst ds.
  pose proof safeStack_one as HS1.
  destruct (Nat.eq_dec (c + fzOf segs zl) 25) as [Hcz25 | Hcz_ne25].
  - destruct (H25 Hcz25) as [m0 [rest [Hseg [-> [-> [Hm0_6 Hm0_odd]]]]]]; subst segs.
    cbn [ValidTail40] in Hvt.
    assert (Hm'_ex : exists m', m0 = S m') by (exists (m0 - 1); lia).
    destruct Hm'_ex as [m' ->].
    assert (Em1 : (S m' =? 1) = false) by lia.
    assert (Hphiw : GoodPhiW (5 + 20 - 1) [1] false = true) by reflexivity.
    assert (Hpsi_cz : GoodPsi (5 + 20 - 1) [1] = true) by reflexivity.
    destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (5 + 2 * 20) + 10)) eqn:Eev_sm.
    + assert (Hg : stepGuards (mkSeg false ((20, S m') :: rest) zl 5 5 0 [1]) = true)
        by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
      split; [exact Hg | intro N].
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
      pose proof (fzOf_ge_40 Hvt) as Hfz1_40.
      destruct (ox_ge_lin (c := 5 + 2 * 20 + 4) (k := S m' + 1) (fz := fzOf rest zl)
        ltac:(lia) ltac:(lia) ltac:(lia) Hfz1_40) as [Hox Hodw].
      exact (chainLeadsUpTo_trans
        (proj1 (excursion270_bundle N) 55 [25; 1] rest zl (5 + 2 * 20 + 4) (S m' + 1)
          ltac:(lia) safeStack_25_1 (validTail40_of_validSegs40 Hvt)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        (fun _ _ _ Hex => exit270_d1_leads Hex ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => ltac:(lia)))).
    + destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (5 + 2 * 20) + 11)) eqn:Eod_sm.
      * assert (Hg : stepGuards (mkSeg false ((20, S m') :: rest) zl 5 5 0 [1]) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
        split; [exact Hg | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
        assert (Hod1 : S m' mod 2 = 1) by (clear - Eod_sm; lia).
        destruct (Hm0_odd Hod1) as [H102 H185].
        replace (S m' - 1) with m' in * by lia.
        exact (stack_47_25_1_leads Hvt ltac:(lia) H102 H185).
      * assert (Hm_big : 2 * (5 + 2 * 20) + 12 <= S m')
          by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
        assert (Hg : stepGuards (mkSeg false ((20, S m') :: rest) zl 5 5 0 [1]) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
        split; [exact Hg | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
        replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
          by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
        assert (Hbc : IsBounce 47 [25; 1] (mkSeg true ((0, S (m' - 4)) :: rest) zl 47 0 96 [25; 1])).
        { change 47 with (47 + 0) at 1.
          apply (IsBounce_cons 0 (m' - 4) zl 47 0 96 rest [25; 1] Hvt ltac:(lia)).
          destruct (S (m' - 4) mod 2 =? 1); lia. }
        exact (bounce_d1_leads (d := 25) Hbc ltac:(lia) ltac:(lia)).
  - assert (Hcz26 : 26 <= c + fzOf segs zl) by lia.
    pose proof (H26 Hcz26) as Hkz47.
    destruct segs as [|[z_0 m0] rest].
    + cbn [fzOf ValidTail40] in Hvt, Hfz20, Hcz26, Hkz47.
      assert (Hg : stepGuards (mkSeg false [] zl c k 0 [1]) = true).
      { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
        assert (Hpw : GoodPhiW (c + zl - 1) [1] false = true)
          by (change (GoodPhiW (c + zl - 1) [1] false) with (1 <=? c + zl - 1); lia).
        rewrite Hpw; cbn [andb]; unfold GoodPsi.
        replace (c + zl - 1 + 1) with (c + zl) by lia.
        exact (proj2 (proj2 HS1) (c + zl) ltac:(lia)). }
      split; [exact Hg | intro N].
      cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
      assert (Hbc : IsBounce (k + 2 * zl + 2) [c + zl; 1]
                      (mkSeg true [] 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 1])).
      { replace (k + 2 * zl + 2) with ((k + 2 * zl + 2) + 0) at 1 by lia.
        exact (IsBounce_nil 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 1] ltac:(lia)). }
      exact (bounce_d1_leads (d := c + zl) Hbc ltac:(lia) ltac:(lia)).
    + cbn [fzOf ValidTail40] in Hvt, Hfz20, Hcz26, Hkz47.
      assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
      destruct m0 as [|m'].
      * split; [reflexivity | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
        destruct rest as [|[z1 [|m1']] rest2].
        -- pose proof (proj2 Hv_rest) as Hzl230.
           exact (bounce_one_leads (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [1] ltac:(lia)) ltac:(lia)).
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [1]) = true)
             by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
           apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
           exact (chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 Hv_r2)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             (fun H => ltac:(lia)) (fun _ => ltac:(lia)))).
        -- pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
           pose proof (validSegs40_tail Hv_rest) as Hv_r2.
           pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
           destruct (S m1' mod 2 =? 1) eqn:Em1_od.
           ++ destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [1]) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                   exact (proj2 (proj2 HS1) (c + z_0 + 3 + z1) ltac:(lia)). }
                 apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                 exact (chainLeadsUpTo_here (rootInv_of_D1 (d := c + z_0 + 3 + z1) ltac:(lia)
                   (validTail40_of_validSegs40 Hv_r2)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
              ** exact (bounce_one_leads
                   (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 [1] Hv_r2 ltac:(lia)
                     (ltac:(rewrite Em1_od; lia)))
                   ltac:(lia)).
           ++ destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
              ** assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: rest2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [1]) = true)
                   by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg; reflexivity).
                 apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
                 exact (chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 Hv_r2)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                   (fun H => ltac:(lia)) (fun _ => ltac:(lia)))).
              ** exact (bounce_one_leads
                   (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) rest2 [1] Hv_r2 ltac:(lia)
                     (ltac:(rewrite Em1_od; lia)))
                   ltac:(lia)).
      * pose proof (fzOf_ge_40 Hv_rest) as Hfz1_40.
        assert (Hphiw : GoodPhiW (c + z_0 - 1) [1] false = true)
          by (change (GoodPhiW (c + z_0 - 1) [1] false) with (1 <=? c + z_0 - 1); lia).
        destruct (S m' =? 1) eqn:Em1.
        -- assert (m' = 0) by lia; subst m'.
           assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 [1]) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
             rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (proj2 (proj2 HS1) (c + z_0 + 1) ltac:(lia)). }
           split; [exact Hg | intro N].
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
           exact (chainLeadsUpTo_here (rootInv_of_D1 (d := c + z_0 + 1) ltac:(lia)
             (validTail40_of_validSegs40 Hv_rest)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
        -- assert (Hpsi_cz : GoodPsi (c + z_0 - 1) [1] = true).
           { unfold GoodPsi; replace (c + z_0 - 1 + 1) with (c + z_0) by lia.
             exact (proj2 (proj2 HS1) (c + z_0) ltac:(lia)). }
           destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
           ++ assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [1]) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
              exact (chainLeadsUpTo_here (rootInv_of_D1 (d := c + z_0) ltac:(lia)
                (validTail40_of_validSegs40 Hv_rest)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
           ++ destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
              ** pose proof (safeStack_d1 (d := c + z_0) ltac:(lia)) as HS_cz.
                 assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [1]) = true).
                 { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                   exact (proj2 (proj2 HS_cz) (k + 2 * z_0 + 2) ltac:(lia)). }
                 split; [exact Hg | intro N].
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                 assert (Hm'1 : 1 <= m') by (clear - Em1; lia).
                 assert (Hm'_od_le : S m' mod 2 = 1 /\ S m' <= 2 * (k + 2 * z_0) + 11) by (clear - Eod_sm; lia).
                 clear Hg Hphiw Hpsi_cz Em1 Eev_sm Eod_sm.
                 replace (S m' - 1) with m' by lia.
                 assert (Hne1_cz : ([c + z_0; 1] : list nat) <> [1]) by discriminate.
                 exact (chainLeadsUpTo_trans
                   (proj2 (excursion270_bundle N) 39 [c + z_0; 1] rest zl m' 1
                     (k + 2 * z_0 + 2) 43 0 ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_rest
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                   (fun _ _ _ Hex => exit270_d1_leads Hex ltac:(lia) ltac:(lia) ltac:(lia)
                     (fun H25 => False_ind _ (ltac:(lia))))).
              ** assert (Hm_big : 2 * (k + 2 * z_0) + 12 <= S m')
                   by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
                 assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [1]) = true)
                   by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
                 split; [exact Hg | intro N].
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                 replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                   by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
                 assert (Hbc : IsBounce (k + 2 * z_0 + 2) [c + z_0; 1]
                                 (mkSeg true ((0, S (m' - 4)) :: rest) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) [c + z_0; 1])).
                 { replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
                   apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest [c + z_0; 1] Hv_rest ltac:(lia)).
                   destruct (S (m' - 4) mod 2 =? 1); lia. }
                 exact (bounce_d1_leads (d := c + z_0) Hbc ltac:(lia) ltac:(lia)).
Qed.

(* ========================================================================== *)
(* 4. `root31_advances` (`Root31 s -> ChainAdvances s RootInv270`)            *)
(* ========================================================================== *)

Lemma goodPhiW_31 {w : nat} (Hw : 15 <= w) : GoodPhiW w [3; 1] false = true.
Proof.
  change (GoodPhiW w [3; 1] false) with (15 <=? w); lia.
Qed.

Lemma bounce_19_31_leads {N phi : nat} {s : SegState}
    (Hb : IsBounce phi [19; 3; 1] s) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi [19; 3; 1] = true)
    by (change (drainPopGuards phi [19; 3; 1]) with (true && true && true && (16 <=? phi)); cbn [andb]; lia).
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  change (drainPopStep hp phi m_rem rest zl [19; 3; 1])
    with (mkSeg true ((0, 16) :: fst p) (snd p) 2 0 6 [1]) in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hg_b1 : stepGuards (mkSeg true ((0, 16) :: fst p) (snd p) 2 0 6 [1]) = true) by reflexivity.
  assert (Hs_b1 : stepSegs (mkSeg true ((0, 16) :: fst p) (snd p) 2 0 6 [1]) =
                  mkSeg true ((5, 8) :: fst p) (snd p) 2 0 6 []) by reflexivity.
  apply (chainLeadsUpTo_step Hg_b1); intros m2 ?; rewrite Hs_b1.
  assert (Hg_b2 : stepGuards (mkSeg true ((5, 8) :: fst p) (snd p) 2 0 6 []) = true) by reflexivity.
  assert (Hs_b2 : stepSegs (mkSeg true ((5, 8) :: fst p) (snd p) 2 0 6 []) =
                  mkSeg false ((9, 0) :: fst p) (snd p) 1 1 0 []) by reflexivity.
  apply (chainLeadsUpTo_step1 Hg_b2); rewrite Hs_b2.
  exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvp
    ltac:(lia) ltac:(lia) ltac:(lia) (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
    (fun H => ltac:(cbn [fzOf] in H; lia)) (fun _ => or_introl (conj eq_refl eq_refl))
    (fun _ _ _ _ Hcz9 => ltac:(cbn [fzOf] in Hcz9; lia)))).
Qed.
Arguments bounce_19_31_leads {N phi s} & _ _.

Lemma bounce_cz_31_even_extra {N cz phi : nat} {s : SegState}
    (Hb : IsBounce phi [cz; 3; 1] s)
    (Hcases : (22 <= cz /\ cz mod 2 = 0 /\ 49 <= phi) \/
              (26 <= cz /\ cz mod 2 = 0 /\ 45 <= phi)) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hcz22 : 22 <= cz) by lia.
  assert (Hphi45 : 45 <= phi) by lia.
  assert (Hnrst : isDrainRstDs [cz; 3; 1] = false) by reflexivity.
  assert (Hnr0 : isRank0 [cz; 3; 1] = false) by (destruct cz as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop : drainPopGuards phi [cz; 3; 1] = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? cz) && (1 <=? 3)) with true by lia.
    replace ((cz mod 2 =? 0) && (cz <=? 2 * 3 + 4)) with false by lia.
    replace ((cz mod 2 =? 0) && (cz + 14 <=? 2 * 3)) with false by lia.
    cbn [negb orb andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl [cz; 3; 1] =
                mkSeg true ((0, cz - 3) :: fst p) (snd p) 2 0 6 [1]).
  { unfold drainPopStep; rewrite Hnrst, Hnr0; cbn [Nat.eqb nat_list_eqb andb].
    replace (normSeg 0 (cz - 3)) with (0, cz - 3) by (unfold normSeg; rw_if_neg ltac:(lia); reflexivity).
    reflexivity. }
  rewrite Hdp in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl) as Hfzp; fold p in Hfzp; clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hg_b1 : stepGuards (mkSeg true ((0, cz - 3) :: fst p) (snd p) 2 0 6 [1]) = true).
  { replace (cz - 3) with (S (cz - 4)) by lia.
    cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 4) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
  assert (Hs_b1 : stepSegs (mkSeg true ((0, cz - 3) :: fst p) (snd p) 2 0 6 [1]) =
                  mkSeg true ((5, cz - 11) :: fst p) (snd p) 2 0 6 []).
  { replace (cz - 3) with (S (cz - 4)) by lia.
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 4) mod 2 =? 1); rw_if_neg ltac:(lia);
      cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb]; f_equal; f_equal; unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia. }
  apply (chainLeadsUpTo_step Hg_b1); intros m2 ?; rewrite Hs_b1.
  assert (Hg_b2 : stepGuards (mkSeg true ((5, cz - 11) :: fst p) (snd p) 2 0 6 []) = true).
  { replace (cz - 11) with (S (cz - 12)) by lia.
    cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 12) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
  assert (Hs_b2 : stepSegs (mkSeg true ((5, cz - 11) :: fst p) (snd p) 2 0 6 []) =
                  mkSeg false ((8, cz - 19) :: fst p) (snd p) 1 1 0 []).
  { replace (cz - 11) with (S (cz - 12)) by lia.
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (cz - 12) mod 2 =? 1); rw_if_neg ltac:(lia);
      cbn [drainPopStep isDrainRstDs isRank0 nat_list_eqb pushSeg fst snd Nat.leb Nat.eqb andb orb]; f_equal; f_equal; unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia. }
  apply (chainLeadsUpTo_step1 Hg_b2); rewrite Hs_b2; apply chainLeadsUpTo_here.
  refine (rootInv_of_0B (or_introl eq_refl) Hvp ltac:(lia) ltac:(lia) ltac:(lia)
    (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
    (fun H => ltac:(cbn [fzOf] in H; lia)) (fun _ => or_introl (conj eq_refl eq_refl)) _).
  intros z_0 m0 r Hseg ? ? ?; inversion Hseg; subst.
  destruct Hcases as [[_ [_ Hphi49]] | [Hcz26 [Hcz_ev _]]];
    [split; [lia | split; [lia | intro; lia]] | split; [lia | split; [lia | intro; lia]]].
Qed.
Arguments bounce_cz_31_even_extra {N cz phi s} & _ _.

Lemma bounce_cz_31_ge25_leads {N cz phi : nat} {s : SegState}
    (Hb : IsBounce phi [cz; 3; 1] s) (Hcz25 : 25 <= cz) (Hphi45 : 45 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  destruct (cz mod 2 =? 1) eqn:Eod.
  - exact (bounce_cz_31_leads Hb (or_intror (or_introl (conj ltac:(lia) (conj ltac:(lia) ltac:(lia)))))).
  - exact (bounce_cz_31_even_extra Hb (or_intror (conj ltac:(lia) (conj ltac:(lia) Hphi45)))).
Qed.
Arguments bounce_cz_31_ge25_leads {N cz phi s} & _ _ _.

Lemma x_31_high_aux (d : nat) :
  forall N x segs zl c k,
    23 <= x -> x - 23 <= d ->
    ValidSegs40 segs zl ->
    40 <= c -> 1 <= k -> k <= 2 * c + 3 ->
    ChainLeadsUpTo N (mkSeg false segs zl c k 0 [x; 3; 1]) RootInv270.
Proof.
  assert (Hne1_31 : ([3; 1] : list nat) <> [1]) by discriminate.
  induction d as [|d IH]; intros N x segs zl c k Hx23 Hxd Hv Hc40 Hk1 Hkc.
  - assert (x = 23) by lia; subst x.
    pose proof (fzOf_ge_40 Hv) as Hfz40.
    destruct (ox_ge_lin (c := c) (k := k) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc Hfz40) as [Hox Hodw].
    pose proof (safeStack_cons_ne1 (x := 23) Hne1_31 safeStack_31 ltac:(lia) ltac:(lia)) as HS.
    pose proof (proj1 (excursion270_bundle N) 19 [23; 3; 1] segs zl c k ltac:(lia) HS
      (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
    apply (chainLeadsUpTo_trans Hfb).
    intros m1 s_mid Hm1 [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
    + exact (bounce_cz_31_leads Hb (or_intror (or_introl (conj ltac:(lia) (conj eq_refl ltac:(lia)))))).
    + apply (r9_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)).
      intros m2 ? p1 p2 Hvp ?.
      exact (bounce_31_leads (isBounce_r9 (x := 23) (y := y) ltac:(lia) ltac:(lia) Hvp) ltac:(lia)).
  - pose proof (fzOf_ge_40 Hv) as Hfz40.
    destruct (ox_ge_lin (c := c) (k := k) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc Hfz40) as [Hox Hodw].
    pose proof (safeStack_cons_ne1 (x := x) Hne1_31 safeStack_31 ltac:(lia) ltac:(lia)) as HS.
    pose proof (proj1 (excursion270_bundle N) 19 [x; 3; 1] segs zl c k ltac:(lia) HS
      (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
    apply (chainLeadsUpTo_trans Hfb).
    intros m1 s_mid Hm1 [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
    + destruct (x mod 2 =? 1) eqn:Eod.
      * exact (bounce_cz_31_leads Hb (or_intror (or_introl (conj ltac:(lia) (conj ltac:(lia) ltac:(lia)))))).
      * exact (bounce_cz_31_even_extra Hb (or_introl (conj ltac:(lia) (conj ltac:(lia) ltac:(lia))))).
    + apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
        (proj2 (proj2 safeStack_31) (x - 1) ltac:(lia))
        (fun _ => proj2 (proj2 safeStack_31) (x - 2) ltac:(lia))).
      * intros Hbig ? ? p1 p2 Hvp ?.
        exact (bounce_31_leads (isBounce_r9 (x := x) (y := y) ltac:(lia) Hbig Hvp) ltac:(lia)).
      * intros Hy_le ? ? ? p1 p2 Hvp ?.
        pose proof (fzOf_ge_40 Hvp) as Hfp.
        refine (chainLeadsUpTo_here (rootInv_of_31B eq_refl (validTail40_of_validSegs40 Hvp)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _)).
        intros z_0 m0 r Hseg ? ? ?.
        assert (Hz0 : fzOf p1 p2 = z_0) by (rewrite Hseg; reflexivity).
        right; lia.
      * intros Hy_le ? m2 ? p1 p2 Hvp ?.
        exact (IH m2 (x - 1) p1 p2 y 1 ltac:(lia) ltac:(lia) Hvp ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma x_31_high_leads {N x : nat} {segs : list (nat * nat)} {zl c k : nat}
    (Hx20 : 20 <= x) (Hv : ValidSegs40 segs zl)
    (Hc40 : 40 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) :
  ChainLeadsUpTo N (mkSeg false segs zl c k 0 [x; 3; 1]) RootInv270.
Proof.
  destruct (x <=? 22) eqn:Ex22.
  - pose proof (fzOf_ge_40 Hv) as Hfz40.
    destruct (ox_ge_lin (c := c) (k := k) (fz := fzOf segs zl) ltac:(lia) Hk1 Hkc Hfz40) as [Hox Hodw].
    pose proof (safeStack_x_31 Hx20 ltac:(lia)) as HS.
    pose proof (proj1 (excursion270_bundle N) 39 [x; 3; 1] segs zl c k ltac:(lia) HS
      (validTail40_of_validSegs40 Hv) ltac:(lia) Hk1 Hkc
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
    apply (chainLeadsUpTo_trans Hfb).
    intros m1 s_mid Hm1 [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
    + destruct (Nat.eq_dec x 22) as [-> | Hx2021].
      * exact (bounce_cz_31_even_extra Hb (or_introl (conj ltac:(lia) (conj eq_refl ltac:(lia))))).
      * exact (bounce_cz_31_leads Hb (or_introl (conj ltac:(lia) ltac:(lia)))).
    + apply (r9_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)).
      intros ? ? p1 p2 Hvp ?.
      exact (bounce_31_leads (isBounce_r9 (x := x) (y := y) ltac:(lia) ltac:(lia) Hvp) ltac:(lia)).
  - exact (x_31_high_aux (x - 23) N x segs zl c k ltac:(lia) (Nat.le_refl _) Hv Hc40 Hk1 Hkc).
Qed.
Arguments x_31_high_leads {N x segs zl c k} & _ _ _ _ _.

Lemma pop_z_cz_31_leads {N z cz phi : nat} {s : SegState}
    (Hb : IsBounce phi [z; cz; 3; 1] s)
    (Hz44 : 44 <= z) (Hcz25 : 25 <= cz) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  apply (amega_pop_step Hb Hphi38 ltac:(lia) ltac:(lia)
    (proj2 (proj2 safeStack_31) (cz - 1) ltac:(lia))
    (fun _ => proj2 (proj2 safeStack_31) (cz - 2) ltac:(lia))).
  - intros Hbig ? ? p1 p2 Hvp ?.
    exact (bounce_31_leads (isBounce_r9 (x := cz) (y := z) ltac:(lia) Hbig Hvp) ltac:(lia)).
  - intros ? ? ? ? p1 p2 Hvp ?.
    pose proof (fzOf_ge_40 Hvp) as Hfp.
    refine (chainLeadsUpTo_here (rootInv_of_31B eq_refl (validTail40_of_validSegs40 Hvp)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _)).
    intros z_0 m0 r Hseg ? ? ?.
    assert (Hz0 : fzOf p1 p2 = z_0) by (rewrite Hseg; reflexivity).
    right; lia.
  - intros ? ? m2 ? p1 p2 Hvp ?.
    exact (x_31_high_leads ltac:(lia) Hvp ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Arguments pop_z_cz_31_leads {N z cz phi s} & _ _ _ _ _.



Lemma loop_k1_gen {N x1 d3 : nat} {ds3 : list nat} {segs : list (nat * nat)} {zl c1 : nat}
    {P : SegState -> Prop}
    (Hx_lo : 21 <= x1) (Hx_hi : x1 <= 47)
    (HS1 : SafeStack 19 (x1 :: d3 :: ds3))
    (Hg_x1_1 : GoodDs ((x1 - 1) :: d3 :: ds3) = true)
    (Hg_x1_2 : GoodDs ((x1 - 2) :: d3 :: ds3) = true)
    (Hv : ValidSegs40 segs zl) (Hc1 : 2 <= c1)
    (H_top : forall m z phi, m <= N -> (z = x1 \/ z = x1 - 1) -> 38 <= phi -> forall s',
      IsBounce phi (z :: d3 :: ds3) s' -> ChainLeadsUpTo m s' P)
    (H_b1 : forall m, m < N -> forall s', IsBounce (x1 - 1) (d3 :: ds3) s' -> ChainLeadsUpTo m s' P)
    (H_b2 : forall m, m < N -> forall s', IsBounce (x1 - 2) (d3 :: ds3) s' -> ChainLeadsUpTo m s' P)
    (H_r10 : forall m c' k' p1 p2, m < N -> c' = x1 + 1 -> 41 <= k' -> k' <= 2 * c' + 3 ->
      ValidSegs40 p1 p2 -> ChainLeadsUpTo m (mkSeg false p1 p2 c' k' 0 (d3 :: ds3)) P) :
  ChainLeadsUpTo N (mkSeg false segs zl c1 1 0 (x1 :: d3 :: ds3)) P.
Proof.
  assert (Hne1_1 : (x1 :: d3 :: ds3) <> [1]) by discriminate.
  pose proof (fbound_k1_boost (N := N) Hne1_1 HS1 Hv Hc1) as Hb.
  apply (chainLeadsUpTo_trans Hb).
  intros m1 s_mid Hm1 [[phi [Hphi38 Hsb]] | [y1 [phi1 [Hy1_39 [Hphi1_38 [Hyw1 Hsb]]]]]].
  - exact (H_top m1 x1 phi Hm1 (or_introl eq_refl) Hphi38 s_mid Hsb).
  - apply (amega_pop_step Hsb Hphi1_38 ltac:(lia) ltac:(lia) Hg_x1_1 (fun _ => Hg_x1_2)).
    + intros Hbig m2 Hm2 p1 p2 Hvp ?.
      exact (H_b1 m2 ltac:(lia) _ (isBounce_r9 (x := x1) (y := y1) ltac:(lia) Hbig Hvp)).
    + intros ? ? m2 Hm2 p1 p2 Hvp ?.
      exact (H_r10 m2 (x1 + 1) (y1 + 2) p1 p2 ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Hvp).
    + intros Hy1_le ? m2 Hm2 p1 p2 Hvp Hfzp.
      pose proof (fzOf_ge_40 Hvp) as Hfp.
      pose proof (arith_boost_cz (c := y1) (fz := fzOf p1 p2) (cz_lo := 109) (ox_lo := 99)
        ltac:(lia) Hfp ltac:(lia) (or_introl (conj eq_refl eq_refl))) as Hox99.
      assert (Hg_x1_11 : GoodDs ((x1 - 1 - 1) :: d3 :: ds3) = true)
        by (replace (x1 - 1 - 1) with (x1 - 2) by lia; exact Hg_x1_2).
      apply (fbound_force_r9 (x := x1 - 1) (d3 := d3) (ds3 := ds3) (c := y1) (k := 1) ltac:(lia)
        Hg_x1_1 Hg_x1_11 Hvp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      * intros m3 phi2 Hm3 Hphi2 s' Hb2.
        exact (H_top m3 (x1 - 1) phi2 ltac:(lia) (or_intror eq_refl) ltac:(lia) s' Hb2).
      * intros m3 Hm3 s' Hb2.
        replace (x1 - 1 - 1) with (x1 - 2) in Hb2 by lia.
        exact (H_b2 m3 ltac:(lia) s' Hb2).
Qed.

Lemma step_m0_zero_31_advances {z_0 zl c k : nat} {rest : list (nat * nat)}
    (Hv_rest : ValidSegs40 rest zl)
    (Hc : 2 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hcz20 : 20 <= c + z_0) :
  ChainAdvances (mkSeg false ((z_0, 0) :: rest) zl c k 0 [3; 1]) RootInv270.
Proof.
  split; [reflexivity | intro N].
  cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
  destruct rest as [|[z1 [|m1']] r2].
  - pose proof (proj2 Hv_rest) as Hzl230.
    exact (bounce_31_leads (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [3; 1] ltac:(lia)) ltac:(lia)).
  - pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
    pose proof (validSegs40_tail Hv_rest) as Hv_r2.
    pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
    assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: r2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [3; 1]) = true)
      by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
    apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    refine (chainLeadsUpTo_here (rootInv_of_31B eq_refl (validTail40_of_validSegs40 Hv_r2)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _)).
    intros z2 m2 r3 Hseg ? ? ?.
    assert (Hz2 : fzOf r2 zl = z2) by (rewrite Hseg; reflexivity).
    right; lia.
  - pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
    pose proof (validSegs40_tail Hv_rest) as Hv_r2.
    pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
    destruct (S m1' mod 2 =? 1) eqn:Em1_od.
    + destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: r2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [3; 1]) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
          exact (proj2 (proj2 safeStack_31) (c + z_0 + 3 + z1) ltac:(lia)). }
        apply (chainLeadsUpTo_step Hg2); intros m2 ?.
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
        exact (x_31_high_leads ltac:(lia) Hv_r2 ltac:(lia) ltac:(lia) ltac:(lia)).
      * exact (bounce_31_leads
          (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) r2 [3; 1] Hv_r2 ltac:(lia)
            (ltac:(rewrite Em1_od; lia)))
          ltac:(lia)).
    + destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: r2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) [3; 1]) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg; reflexivity).
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
        refine (chainLeadsUpTo_here (rootInv_of_31B eq_refl (validTail40_of_validSegs40 Hv_r2)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _)).
        intros z2 m2 r3 Hseg ? ? ?.
        assert (Hz2 : fzOf r2 zl = z2) by (rewrite Hseg; reflexivity).
        right; lia.
      * exact (bounce_31_leads
          (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) r2 [3; 1] Hv_r2 ltac:(lia)
            (ltac:(rewrite Em1_od; lia)))
          ltac:(lia)).
Qed.
Arguments step_m0_zero_31_advances {z_0 zl c k rest} & _ _ _ _ _.

Lemma root31A_advances {s : SegState}
    (Hb : st_b s = false) (Hmrg : st_mrg s = 0) (Hr : Root31A s) :
  ChainAdvances s RootInv270.
Proof.
  destruct s as [b segs zl cp1 kb mrg ds]; cbn [st_b st_mrg] in Hb, Hmrg; subst b mrg.
  destruct Hr as [Hds [Hvt [Hc [Hk Hcases]]]]; cbn [st_segs st_zl st_cp1 st_kb st_ds] in *; subst ds cp1 kb.
  assert (H1819 : fzOf segs zl = 18 \/ fzOf segs zl = 19 ->
                  ChainAdvances (mkSeg false segs zl 2 1 0 [3; 1]) RootInv270).
  { intro Hfz.
    destruct segs as [|[z_0 m0] rest]; [cbn [fzOf ValidTail40] in Hvt, Hfz; lia |].
    cbn [fzOf ValidTail40] in Hvt, Hfz.
    assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
    destruct m0 as [|m'].
    - exact (step_m0_zero_31_advances Hv_rest ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - pose proof (goodPhiW_31 (w := 2 + z_0 - 1) ltac:(lia)) as Hphiw.
      destruct (S m' =? 1) eqn:Em1.
      + assert (m' = 0) by lia; subst m'.
        assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl 2 1 0 [3; 1]) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
          rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (proj2 (proj2 safeStack_31) (2 + z_0 + 1) ltac:(lia)). }
        split; [exact Hg | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
        exact (x_31_high_leads ltac:(lia) Hv_rest ltac:(lia) ltac:(lia) ltac:(lia)).
      + assert (Hpsi_cz : GoodPsi (2 + z_0 - 1) [3; 1] = true).
        { unfold GoodPsi; replace (2 + z_0 - 1 + 1) with (2 + z_0) by lia.
          exact (proj2 (proj2 safeStack_31) (2 + z_0) ltac:(lia)). }
        destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (1 + 2 * z_0) + 10)) eqn:Eev_sm.
        * assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl 2 1 0 [3; 1]) = true)
            by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
          split; [exact Hg | intro N].
          cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
          exact (x_31_high_leads ltac:(lia) Hv_rest ltac:(lia) ltac:(lia) ltac:(lia)).
        * destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (1 + 2 * z_0) + 11)) eqn:Eod_sm.
          -- assert (HS_cz : SafeStack 27 [2 + z_0; 3; 1]).
             { destruct (Nat.eq_dec z_0 18) as [-> | Hz19]; [exact safeStack_20_3_1 |].
               assert (z_0 = 19) by lia; subst z_0.
               assert (Hne1_31 : ([3; 1] : list nat) <> [1]) by discriminate.
               exact (safeStack_mono (m1 := 19) (m2 := 27) ltac:(lia) (safeStack_cons_ne1 (x := 21) Hne1_31 safeStack_31 ltac:(lia) ltac:(lia))). }
             assert (Hne1_cz : ([2 + z_0; 3; 1] : list nat) <> [1]) by discriminate.
             pose proof (safeStack_cons_ne1 (x := 1 + 2 * z_0 + 2) Hne1_cz HS_cz ltac:(lia) ltac:(lia)) as HS1.
             assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl 2 1 0 [3; 1]) = true).
             { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
               exact (proj2 (proj2 HS_cz) (1 + 2 * z_0 + 2) ltac:(lia)). }
             split; [exact Hg | intro N].
             cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
             assert (Hm'1 : 1 <= m') by (clear - Em1; lia).
             assert (Hm'_od_le : S m' mod 2 = 1 /\ S m' <= 2 * (1 + 2 * z_0) + 11) by (clear - Eod_sm; lia).
             clear Hg Hphiw Hpsi_cz Em1 Eev_sm Eod_sm.
             replace (S m' - 1) with m' by lia.
             apply (loop_k1_gen (x1 := 1 + 2 * z_0 + 2) (d3 := 2 + z_0) (ds3 := [3; 1]) (c1 := m')
               ltac:(lia) ltac:(lia) HS1
               (proj2 (proj2 HS_cz) (1 + 2 * z_0 + 2 - 1) ltac:(lia))
               (proj2 (proj2 HS_cz) (1 + 2 * z_0 + 2 - 2) ltac:(lia))
               Hv_rest ltac:(lia)).
             ++ intros m1 z phi ? Hz Hphi38 s' Hbz.
                apply (amega_pop_step Hbz Hphi38 ltac:(lia) ltac:(lia)
                  (proj2 (proj2 safeStack_31) (2 + z_0 - 1) ltac:(lia))
                  (fun Hbad => ltac:(lia))).
                ** intro Hbig; exfalso; lia.
                ** intros ? ? ? ? p1 p2 Hvp ?.
                   pose proof (fzOf_ge_40 Hvp) as Hfp.
                   refine (chainLeadsUpTo_here (rootInv_of_31B eq_refl (validTail40_of_validSegs40 Hvp)
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _)).
                   intros z2 m2 r3 Hseg ? ? ?.
                   assert (Hz2 : fzOf p1 p2 = z2) by (rewrite Hseg; reflexivity).
                   right; lia.
                ** intros ? ? m2 ? p1 p2 Hvp ?.
                   pose proof (fzOf_ge_40 Hvp) as Hfp.
                   destruct (ox_ge_lin (c := z) (k := 1) (fz := fzOf p1 p2) ltac:(lia) ltac:(lia) ltac:(lia) Hfp) as [Hox Hodw].
                   pose proof (safeStack_of_gt2d2 (m := 45) (d2 := 2 + z_0 - 1) (d3 := 3) (ds3 := [1])
                     ltac:(lia) ltac:(lia) ltac:(lia) (proj2 (proj2 safeStack_31) (2 + z_0 - 1) ltac:(lia))) as HS45.
                   pose proof (proj1 (excursion270_bundle m2) 45 [2 + z_0 - 1; 3; 1] p1 p2 z 1
                     ltac:(lia) HS45 (validTail40_of_validSegs40 Hvp)
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
                   apply (chainLeadsUpTo_trans Hfb).
                   intros m3 s_m3 ? [[phi2 [Hphi2 Hb2]] | [y2 [phi2 [Hy2 [Hphi2_38 [_ Hb2]]]]]].
                   --- destruct (Nat.eq_dec (2 + z_0 - 1) 19) as [H19 | H20].
                       +++ rewrite H19 in Hb2; exact (bounce_19_31_leads Hb2 ltac:(lia)).
                       +++ exact (bounce_cz_31_leads Hb2 (or_introl (conj ltac:(lia) ltac:(lia)))).
                   --- apply (r9_pop_step Hb2 Hphi2_38 ltac:(lia) ltac:(lia)).
                       intros ? ? q1 q2 Hvq ?.
                       exact (bounce_31_leads (isBounce_r9 (x := 2 + z_0 - 1) (y := y2) ltac:(lia) ltac:(lia) Hvq) ltac:(lia)).
             ++ intros m1 ? s' Hb1.
                exact (bounce_cz_31_leads Hb1 (or_introl (conj ltac:(lia) ltac:(lia)))).
             ++ intros m1 ? s' Hb2.
                exact (bounce_cz_31_leads Hb2 (or_introl (conj ltac:(lia) ltac:(lia)))).
             ++ intros m1 c' k' p1 p2 ? -> Hk'41 Hk'c Hvp.
                exact (x_31_high_leads ltac:(lia) Hvp ltac:(lia) ltac:(lia) Hk'c).
          -- assert (Hm_big : 2 * (1 + 2 * z_0) + 12 <= S m')
               by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
             assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl 2 1 0 [3; 1]) = true)
               by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
             split; [exact Hg | intro N].
             cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
             replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
               by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
             assert (Hbc : IsBounce (1 + 2 * z_0 + 2) [2 + z_0; 3; 1]
                             (mkSeg true ((0, S (m' - 4)) :: rest) zl (1 + 2 * z_0 + 2) 0 (2 * (1 + 2 * z_0) + 6) [2 + z_0; 3; 1])).
             { replace (1 + 2 * z_0 + 2) with ((1 + 2 * z_0 + 2) + 0) at 1 by lia.
               apply (IsBounce_cons 0 (m' - 4) zl (1 + 2 * z_0 + 2) 0 (2 * (1 + 2 * z_0) + 6) rest [2 + z_0; 3; 1] Hv_rest ltac:(lia)).
               destruct (S (m' - 4) mod 2 =? 1); lia. }
             exact (bounce_cz_31_leads Hbc (or_introl (conj ltac:(lia) ltac:(lia)))). }
  destruct Hcases as [Hfz18 | [Hfz19 | [rest ->]]].
  - exact (H1819 (or_introl Hfz18)).
  - exact (H1819 (or_intror Hfz19)).
  - exact (step_m0_zero_31_advances Hvt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma root31B_advances {s : SegState}
    (Hb : st_b s = false) (Hmrg : st_mrg s = 0) (Hr : Root31B s) :
  ChainAdvances s RootInv270.
Proof.
  destruct s as [b segs zl c k mrg ds]; cbn [st_b st_mrg] in Hb, Hmrg; subst b mrg.
  destruct Hr as [Hds [Hvt [Hc [Hk1 [Hkc [Hfz21 [Hcz25 [Hkz43 Hod_inv]]]]]]]].
  cbn [st_segs st_zl st_cp1 st_kb st_ds] in *; subst ds.
  assert (Hne1_31 : ([3; 1] : list nat) <> [1]) by discriminate.
  destruct segs as [|[z_0 m0] rest].
  - cbn [fzOf ValidTail40] in Hvt, Hfz21, Hcz25, Hkz43.
    assert (Hg : stepGuards (mkSeg false [] zl c k 0 [3; 1]) = true).
    { cbn [stepGuards st_b st_segs st_zl st_cp1 st_kb st_ds].
      rewrite (goodPhiW_31 (w := c + zl - 1) ltac:(lia)); cbn [andb]; unfold GoodPsi.
      replace (c + zl - 1 + 1) with (c + zl) by lia.
      exact (proj2 (proj2 safeStack_31) (c + zl) ltac:(lia)). }
    split; [exact Hg | intro N].
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    assert (Hbc : IsBounce (k + 2 * zl + 2) [c + zl; 3; 1]
                    (mkSeg true [] 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 3; 1])).
    { replace (k + 2 * zl + 2) with ((k + 2 * zl + 2) + 0) at 1 by lia.
      exact (IsBounce_nil 0 (k + 2 * zl + 2) 0 (2 * (k + 2 * zl) + 6) [c + zl; 3; 1] ltac:(lia)). }
    exact (bounce_cz_31_ge25_leads Hbc ltac:(lia) ltac:(lia)).
  - cbn [fzOf ValidTail40] in Hvt, Hfz21, Hcz25, Hkz43.
    assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
    destruct m0 as [|m'].
    + exact (step_m0_zero_31_advances Hv_rest Hc Hk1 Hkc ltac:(lia)).
    + pose proof (goodPhiW_31 (w := c + z_0 - 1) ltac:(lia)) as Hphiw.
      destruct (S m' =? 1) eqn:Em1.
      * assert (m' = 0) by lia; subst m'.
        assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 [3; 1]) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
          rewrite Hphiw; cbn [andb]; unfold GoodPsi; exact (proj2 (proj2 safeStack_31) (c + z_0 + 1) ltac:(lia)). }
        split; [exact Hg | intro N].
        cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
        exact (x_31_high_leads ltac:(lia) Hv_rest ltac:(lia) ltac:(lia) ltac:(lia)).
      * assert (Hpsi_cz : GoodPsi (c + z_0 - 1) [3; 1] = true).
        { unfold GoodPsi; replace (c + z_0 - 1 + 1) with (c + z_0) by lia.
          exact (proj2 (proj2 safeStack_31) (c + z_0) ltac:(lia)). }
        destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
        -- assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [3; 1]) = true)
             by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
           split; [exact Hg | intro N].
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
           exact (x_31_high_leads ltac:(lia) Hv_rest ltac:(lia) ltac:(lia) ltac:(lia)).
        -- destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
           ++ pose proof (safeStack_cons_ne1 (x := c + z_0) Hne1_31 safeStack_31 ltac:(lia) ltac:(lia)) as HS_cz.
              assert (Hne1_cz : ([c + z_0; 3; 1] : list nat) <> [1]) by discriminate.
              assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [3; 1]) = true).
              { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                exact (proj2 (proj2 HS_cz) (k + 2 * z_0 + 2) ltac:(lia)). }
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
              assert (Hm'1 : 1 <= m') by (clear - Em1; lia).
              assert (Hm'_od_le : S m' mod 2 = 1 /\ S m' <= 2 * (k + 2 * z_0) + 11) by (clear - Eod_sm; lia).
              clear Hg Hphiw Hpsi_cz Em1 Eev_sm Eod_sm.
              replace (S m' - 1) with m' by lia.
              set (x1 := k + 2 * z_0 + 2).
              destruct (x1 <=? 47) eqn:Ex47.
              ** apply (loop_k1_le47 (x1 := x1) (d3 := c + z_0) (ds3 := [3; 1]) (c1 := m') Hne1_cz
                   (safeStack_mono (m1 := 19) (m2 := 21) ltac:(lia) HS_cz)
                   (or_introl ltac:(unfold x1; lia)) ltac:(lia) Hv_rest ltac:(lia)).
                 --- intros m1 z phi ? Hz Hphi38 ? Hbz.
                     exact (pop_z_cz_31_leads Hbz ltac:(unfold x1 in *; lia) Hcz25 Hphi38).
                 --- intros m1 ? s' Hb1.
                     destruct ((c + z_0) mod 2 =? 1) eqn:Ecz_od.
                     +++ exact (bounce_cz_31_leads Hb1 (or_intror (or_introl (conj ltac:(lia) (conj ltac:(lia) ltac:(unfold x1 in *; lia)))))).
                     +++ destruct (Hod_inv z_0 (S m') rest eq_refl ltac:(lia) ltac:(lia) (proj1 Hm'_od_le)) as [[-> [-> ->]] | H47].
                         *** exact (bounce_cz_31_even_extra Hb1 (or_intror (conj ltac:(lia) (conj eq_refl ltac:(unfold x1 in *; lia))))).
                         *** unfold x1 in *; lia.
                 --- intros m1 ? s' Hb2.
                     destruct ((c + z_0) mod 2 =? 1) eqn:Ecz_od.
                     +++ exact (bounce_cz_31_leads Hb2 (or_intror (or_introl (conj ltac:(lia) (conj ltac:(lia) ltac:(unfold x1 in *; lia)))))).
                     +++ destruct (Hod_inv z_0 (S m') rest eq_refl ltac:(lia) ltac:(lia) (proj1 Hm'_od_le)) as [[-> [-> ->]] | H47].
                         *** exact (bounce_cz_31_even_extra Hb2 (or_intror (conj ltac:(lia) (conj eq_refl ltac:(unfold x1 in *; lia))))).
                         *** unfold x1 in *; lia.
                 --- intros m1 c' k' p1 p2 ? -> Hk'41 Hk'c Hvp.
                     exact (x_31_high_leads ltac:(lia) Hvp ltac:(unfold x1 in *; lia) ltac:(lia) Hk'c).
              ** destruct (x1 <=? 50) eqn:Ex50.
                 --- pose proof (safeStack_cons_ne1 (x := x1) Hne1_cz HS_cz ltac:(unfold x1 in *; lia) ltac:(unfold x1 in *; lia)) as HS_x1.
                     assert (Hne1_x1 : ([x1; c + z_0; 3; 1] : list nat) <> [1]) by discriminate.
                     apply (chainLeadsUpTo_trans (fbound_k1_boost (N := N) (c1 := m') Hne1_x1 HS_x1 Hv_rest ltac:(lia))).
                     intros m1 s_m1 Hm1 [[phi1 [Hphi1 Hb1]] | [y1 [phi1 [Hy1 [Hphi1_38 [Hyw1 Hb1]]]]]].
                     +++ exact (pop_z_cz_31_leads Hb1 ltac:(lia) Hcz25 Hphi1).
                     +++ apply (amega_pop_step Hb1 Hphi1_38 ltac:(lia) ltac:(lia)
                           (proj2 (proj2 HS_cz) (x1 - 1) ltac:(lia))
                           (fun _ => proj2 (proj2 HS_cz) (x1 - 2) ltac:(lia))).
                         *** intros Hbig ? ? p1 p2 Hvp ?.
                             exact (bounce_cz_31_ge25_leads (isBounce_r9 (x := x1) (y := y1) ltac:(lia) Hbig Hvp) Hcz25 ltac:(lia)).
                         *** intros ? ? ? ? p1 p2 Hvp ?.
                             exact (x_31_high_leads ltac:(lia) Hvp ltac:(lia) ltac:(lia) ltac:(lia)).
                         *** intros Hy1_le ? m2 ? p1 p2 Hvp Hfzp.
                             pose proof (fzOf_ge_40 Hvp) as Hfp.
                             pose proof (arith_boost_cz (c := y1) (fz := fzOf p1 p2)
                               (cz_lo := 109) (ox_lo := 99) ltac:(lia) Hfp ltac:(lia) (or_introl (conj eq_refl eq_refl))) as Hox99.
                             pose proof (safeStack_cons_ne1 (x := x1 - 1) Hne1_cz HS_cz ltac:(lia) ltac:(lia)) as HS_x1'.
                             pose proof (proj1 (excursion270_bundle m2) 19 [x1 - 1; c + z_0; 3; 1] p1 p2 y1 1
                               ltac:(lia) HS_x1' (validTail40_of_validSegs40 Hvp)
                               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb2.
                             apply (chainLeadsUpTo_trans Hfb2).
                             intros m3 s_m3 ? [[phi2 [Hphi2 Hb2]] | [y2 [phi2 [Hy2 [Hphi2_38 [_ Hb2]]]]]].
                             ---- assert (Hp2 : 38 <= phi2) by (rewrite odw_def in Hphi2; lia).
                                  exact (pop_z_cz_31_leads Hb2 ltac:(lia) Hcz25 Hp2).
                             ---- apply (amega_pop_step Hb2 Hphi2_38 ltac:(lia) ltac:(lia)
                                    (proj2 (proj2 HS_cz) (x1 - 1 - 1) ltac:(lia))
                                    (fun _ => proj2 (proj2 HS_cz) (x1 - 1 - 2) ltac:(lia))).
                                  ++++ intros Hbig ? ? q1 q2 Hvq ?.
                                       exact (bounce_cz_31_ge25_leads (isBounce_r9 (x := x1 - 1) (y := y2) ltac:(lia) Hbig Hvq) Hcz25 ltac:(lia)).
                                  ++++ intros ? ? ? ? q1 q2 Hvq ?.
                                       exact (x_31_high_leads ltac:(lia) Hvq ltac:(lia) ltac:(lia) ltac:(lia)).
                                  ++++ intros Hy2_le ? m4 ? q1 q2 Hvq ?.
                                       pose proof (fzOf_ge_40 Hvq) as Hfq.
                                       destruct (ox_ge_lin (c := y2) (k := 1) (fz := fzOf q1 q2)
                                         ltac:(lia) ltac:(lia) ltac:(lia) Hfq) as [Hox_q _].
                                       apply (fbound_force_r9 (x := x1 - 1 - 1) (d3 := c + z_0) (ds3 := [3; 1])
                                         (c := y2) (k := 1) ltac:(lia)
                                         (proj2 (proj2 HS_cz) (x1 - 1 - 1) ltac:(lia))
                                         (proj2 (proj2 HS_cz) (x1 - 1 - 1 - 1) ltac:(lia)) Hvq
                                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
                                       **** intros ? phi3 ? Hphi3 ? Hb3.
                                            exact (pop_z_cz_31_leads Hb3 ltac:(lia) Hcz25 ltac:(lia)).
                                       **** intros ? ? ? Hb3.
                                            exact (bounce_cz_31_ge25_leads Hb3 Hcz25 ltac:(lia)).
                 --- pose proof (fzOf_ge_40 Hv_rest) as Hfz_r.
                     apply (chainLeadsUpTo_trans
                       (proj2 (excursion270_bundle N) 19 [c + z_0; 3; 1] rest zl m' 1 x1 46 0
                         ltac:(lia) HS_cz (or_introl Hne1_cz) Hv_rest
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
                     intros ? ? ? [[phi [Hphi Hb0]] | [z [phi [Hz [Hphi38 [_ Hb0]]]]]].
                     +++ exact (bounce_cz_31_ge25_leads Hb0 Hcz25 Hphi).
                     +++ exact (pop_z_cz_31_leads Hb0 ltac:(lia) Hcz25 Hphi38).
           ++ assert (Hm_big : 2 * (k + 2 * z_0) + 12 <= S m')
                by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
              assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 [3; 1]) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
              replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
              assert (Hbc : IsBounce (k + 2 * z_0 + 2) [c + z_0; 3; 1]
                              (mkSeg true ((0, S (m' - 4)) :: rest) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) [c + z_0; 3; 1])).
              { replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
                apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest [c + z_0; 3; 1] Hv_rest ltac:(lia)).
                destruct (S (m' - 4) mod 2 =? 1); lia. }
              exact (bounce_cz_31_ge25_leads Hbc Hcz25 ltac:(lia)).
Qed.

Lemma root31_advances {s : SegState}
    (Hb : st_b s = false) (Hmrg : st_mrg s = 0) (Hr : Root31 s) :
  ChainAdvances s RootInv270.
Proof.
  destruct Hr as [Ha | Hb31].
  - exact (root31A_advances Hb Hmrg Ha).
  - exact (root31B_advances Hb Hmrg Hb31).
Qed.



(* ========================================================================== *)
(* 5. `root0_advances` (`Root0 s -> ChainAdvances s RootInv270`)              *)
(* ========================================================================== *)

Lemma goodPhiW_0 {w : nat} {ds : list nat} (Hds : ds = [] \/ ds = [0]) (Hw : 6 <= w) :
  GoodPhiW w ds false = true.
Proof.
  destruct Hds as [-> | ->].
  - change (GoodPhiW w [] false) with (false || (6 <=? w)); cbn [orb]; lia.
  - change (GoodPhiW w [0] false) with (6 <=? w); lia.
Qed.
Arguments goodPhiW_0 {w ds} & _ _.

Lemma goodPsi_0 {w : nat} {ds : list nat} (Hds : ds = [] \/ ds = [0]) (Hw : 7 <= w) :
  GoodPsi w ds = true.
Proof.
  destruct Hds as [-> | ->].
  - change (GoodPsi w []) with ((w + 1 <=? 2) || (8 <=? w + 1)); lia.
  - change (GoodPsi w [0]) with (8 <=? w + 1); lia.
Qed.
Arguments goodPsi_0 {w ds} & _ _.

Lemma safeStack_0 {ds : list nat} (Hds : ds = [] \/ ds = [0]) : SafeStack 19 ds.
Proof.
  destruct Hds as [-> | ->]; [exact safeStack_nil | exact safeStack_zero].
Qed.

Lemma safeStack19_d_ds {d : nat} {ds : list nat} (Hd10 : 10 <= d) (Hds : ds = [] \/ ds = [0]) :
  SafeStack 19 (d :: ds).
Proof.
  destruct Hds as [-> | ->].
  - refine (conj (fun H => ltac:(inversion H; lia)) (conj (proj1 (proj2 (safeStack_d (d := d) ltac:(lia)))) _)).
    intros u Hu; rewrite GoodDs_cons2; unfold GoodDs2, GoodDs1.
    rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
    assert (Ho : isOddDrain1 d && (u <? 19) = false) by (destruct (isOddDrain1 d); lia).
    rewrite Ho. rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). rw_if_neg ltac:(lia). reflexivity.
  - refine (conj (fun H => ltac:(inversion H)) (conj (proj1 (proj2 (safeStack_d0 (d := d) ltac:(lia)))) _)).
    intros u Hu; rewrite GoodDs_cons3.
    assert (Hgd : GoodDs [d; 0] = true) by (unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia).
    rewrite Hgd; cbn [negb orb].
    rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
    assert (Ho : isOddDrainDs [d; 0] && (u <? 19) = false) by (destruct (isOddDrainDs [d; 0]); lia).
    rewrite Ho. rw_if_neg ltac:(lia). rw_if_neg ltac:(lia).
    assert (Hg1 : GoodDs [d - 1; 0] = true) by (unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia).
    rewrite Hg1, andb_false_r.
    assert (Hg2 : GoodDs [d - 2; 0] = true) by (unfold GoodDs, GoodDsAux, GoodDs2; cbn [Nat.eqb]; lia).
    rewrite Hg2, andb_false_r; reflexivity.
Qed.

Lemma bounce_0_leads {N phi : nat} {ds : list nat} {s : SegState}
    (Hb : IsBounce phi ds s) (Hds : ds = [] \/ ds = [0]) (Hphi : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  destruct Hds as [-> | ->]; [exact (bounce_nil_leads Hb ltac:(lia)) | exact (bounce_zero_leads Hb Hphi)].
Qed.
Arguments bounce_0_leads {N phi ds s} & _ _ _.

Lemma step_m0_zero_0_advances {z_0 zl c k : nat} {rest : list (nat * nat)} {ds : list nat}
    (Hds : ds = [] \/ ds = [0]) (Hv_rest : ValidSegs40 rest zl)
    (Hc : 1 <= c) (Hk1 : 1 <= k) (Hkc : k <= 2 * c + 3) (Hcz8 : 8 <= c + z_0) :
  ChainAdvances (mkSeg false ((z_0, 0) :: rest) zl c k 0 ds) RootInv270.
Proof.
  split; [reflexivity | intro N].
  cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
  destruct rest as [|[z1 [|m1']] r2].
  - pose proof (proj2 Hv_rest) as Hzl230.
    exact (bounce_0_leads (IsBounce_nil zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) ds ltac:(lia)) Hds ltac:(lia)).
  - pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
    pose proof (validSegs40_tail Hv_rest) as Hv_r2.
    pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
    assert (Hg2 : stepGuards (mkSeg true ((z1, 0) :: r2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) ds) = true)
      by (cbn [stepGuards st_b st_segs st_kb st_mrg]; lia).
    apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds].
    exact (chainLeadsUpTo_here (rootInv_of_0B Hds (validTail40_of_validSegs40 Hv_r2)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
  - pose proof (fzOf_ge_40 Hv_rest) as Hz1_40; cbn [fzOf] in Hz1_40.
    pose proof (validSegs40_tail Hv_rest) as Hv_r2.
    pose proof (fzOf_ge_40 Hv_r2) as Hfz2_40.
    destruct (S m1' mod 2 =? 1) eqn:Em1_od.
    + destruct ((k + 2 * z_0 + 3) + m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: r2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) ds) = true).
        { cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
          exact (proj2 (proj2 (safeStack_0 Hds)) (c + z_0 + 3 + z1) ltac:(lia)). }
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
        assert (Hds_d : ((c + z_0 + 3 + z1) :: ds) = [c + z_0 + 3 + z1] \/ ((c + z_0 + 3 + z1) :: ds) = [c + z_0 + 3 + z1; 0])
          by (destruct Hds as [-> | ->]; [left; reflexivity | right; reflexivity]).
        exact (chainLeadsUpTo_here (rootInv_of_D (d := c + z_0 + 3 + z1) ltac:(lia) Hds_d
          (validTail40_of_validSegs40 Hv_r2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      * refine (bounce_0_leads (phi := c + z_0 + 3 + z1) _ Hds ltac:(lia)).
        apply (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) r2 ds Hv_r2 ltac:(lia)).
        rewrite Em1_od; lia.
    + destruct ((k + 2 * z_0 + 3) + S m1' <=? 2 * (c + z_0) + 8) eqn:Emrg.
      * assert (Hg2 : stepGuards (mkSeg true ((z1, S m1') :: r2) zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) ds) = true)
          by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg; reflexivity).
        apply (chainLeadsUpTo_step1 Hg2); cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Em1_od, Emrg.
        exact (chainLeadsUpTo_here (rootInv_of_0B Hds (validTail40_of_validSegs40 Hv_r2)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
          (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
      * refine (bounce_0_leads (phi := c + z_0 + 3 + z1) _ Hds ltac:(lia)).
        apply (IsBounce_cons z1 m1' zl (c + z_0 + 3) (k + 2 * z_0 + 3) (2 * (c + z_0) + 8) r2 ds Hv_r2 ltac:(lia)).
        rewrite Em1_od; lia.
Qed.

Lemma pop_17_8_0_leads {N phi : nat} {s : SegState}
    (Hb : IsBounce phi [17; 8; 0] s) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi [17; 8; 0] = true)
    by (change (drainPopGuards phi [17; 8; 0]) with (true && true && true && (16 <=? phi)); cbn [andb]; lia).
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl [17; 8; 0] =
                mkSeg true ((0, 14) :: fst p) (snd p) 7 0 16 [0]) by reflexivity.
  rewrite Hdp in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_ge_40 Hvp) as Hfp40; clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hg2 : stepGuards (mkSeg true ((0, 14) :: fst p) (snd p) 7 0 16 [0]) = true) by reflexivity.
  assert (Hs2 : stepSegs (mkSeg true ((0, 14) :: fst p) (snd p) 7 0 16 [0]) =
                mkSeg false (fst p) (snd p) 9 19 0 [0]) by reflexivity.
  apply (chainLeadsUpTo_step1 Hg2); rewrite Hs2.
  exact (chainLeadsUpTo_here (rootInv_of_0B (or_intror eq_refl) (validTail40_of_validSegs40 Hvp)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
Qed.
Arguments pop_17_8_0_leads {N phi s} & _ _.

Lemma pop_y_17_8_0_leads {N y phi : nat} {s : SegState}
    (Hb : IsBounce phi [y; 17; 8; 0] s) (Hy43 : 43 <= y) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hnrst : isDrainRstDs [y; 17; 8; 0] = false) by reflexivity.
  assert (Hnr0 : isRank0 [y; 17; 8; 0] = false) by (destruct y as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop : drainPopGuards phi [y; 17; 8; 0] = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? y) && (1 <=? 17)) with true by lia.
    replace ((y mod 2 =? 0) && (y <=? 2 * 17 + 4)) with false by lia.
    replace ((y mod 2 =? 0) && (y + 14 <=? 2 * 17)) with false by lia.
    cbn [negb orb andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl [y; 17; 8; 0] =
                mkSeg true ((0, S (y - 4)) :: fst p) (snd p) 16 0 34 [8; 0]).
  { unfold drainPopStep; rewrite Hnrst, Hnr0; cbn [Nat.eqb nat_list_eqb andb].
    replace (normSeg 0 (y - 3)) with (0, S (y - 4)) by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
    reflexivity. }
  rewrite Hdp in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hbc : IsBounce 16 [8; 0] (mkSeg true ((0, S (y - 4)) :: fst p) (snd p) 16 0 34 [8; 0])).
  { replace 16 with (16 + 0) at 1 by lia.
    apply (IsBounce_cons 0 (y - 4) (snd p) 16 0 34 (fst p) [8; 0] Hvp ltac:(lia)).
    destruct (S (y - 4) mod 2 =? 1); lia. }
  exact (bounce_d_leads (d := 8) Hbc (or_intror eq_refl) (or_introl (conj eq_refl (or_introl eq_refl)))).
Qed.
Arguments pop_y_17_8_0_leads {N y phi s} & _ _ _.

Lemma pop_19_9_leads {N phi : nat} {ds : list nat} {s : SegState}
    (Hb : IsBounce phi (19 :: 9 :: ds) s) (Hds : ds = [] \/ ds = [0]) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg_pop : drainPopGuards phi (19 :: 9 :: ds) = true).
  { destruct Hds as [-> | ->].
    - change (drainPopGuards phi [19; 9]) with (true && true && true && (16 <=? phi)); cbn [andb]; lia.
    - change (drainPopGuards phi [19; 9; 0]) with (true && true && true && (16 <=? phi)); cbn [andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl (19 :: 9 :: ds) =
                mkSeg true ((0, 16) :: fst p) (snd p) 8 0 18 ds)
    by (destruct Hds as [-> | ->]; reflexivity).
  rewrite Hdp in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_ge_40 Hvp) as Hfp40; clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  assert (Hg2 : stepGuards (mkSeg true ((0, 16) :: fst p) (snd p) 8 0 18 ds) = true) by reflexivity.
  assert (Hs2 : stepSegs (mkSeg true ((0, 16) :: fst p) (snd p) 8 0 18 ds) =
                mkSeg false (fst p) (snd p) 10 21 0 ds) by reflexivity.
  apply (chainLeadsUpTo_step1 Hg2); rewrite Hs2.
  exact (chainLeadsUpTo_here (rootInv_of_0B Hds (validTail40_of_validSegs40 Hvp)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
Qed.
Arguments pop_19_9_leads {N phi ds s} & _ _ _.

Lemma pop_y_19_9_leads {N y phi : nat} {ds : list nat} {s : SegState}
    (Hb : IsBounce phi (y :: 19 :: 9 :: ds) s)
    (Hds : ds = [] \/ ds = [0])
    (Hy49 : 49 <= y)
    (Hphi_cases : (53 <= y /\ 90 <= phi) \/ 100 <= phi \/ (53 <= y /\ y mod 2 = 1 /\ 88 <= phi)) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hphi88 : 88 <= phi) by lia.
  apply (r9_pop_step Hb ltac:(lia) ltac:(lia) ltac:(lia)).
  intros m1 ? p0_1 p0_2 Hvp0 Hfzp0.
  assert (Hy_sub : y - 3 = S (y - 4)) by (clear - Hy49; lia).
  assert (Hg_pop9 : drainPopGuards (18 + 0) (9 :: ds) = true)
    by (destruct Hds as [-> | ->]; reflexivity).
  assert (Hg2 : stepGuards (mkSeg true ((0, y - 3) :: p0_1) p0_2 18 0 38 (9 :: ds)) = true).
  { rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
    destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(clear - Hy49; lia); exact Hg_pop9. }
  assert (Hs2 : stepSegs (mkSeg true ((0, y - 3) :: p0_1) p0_2 18 0 38 (9 :: ds)) =
                mkSeg true ((1, 0) :: (20, y - 43) :: p0_1) p0_2 3 0 8 [1]).
  { assert (Hm_eq : 0 + S (y - 4) - (38 + 2) = y - 43) by (clear - Hy49; lia).
    assert (Hn20 : normSeg 20 (y - 43) = (20, y - 43))
      by (unfold normSeg; rw_if_neg ltac:(clear - Hy49; lia); reflexivity).
    assert (Hdp9 : drainPopStep true (18 + 0) (y - 43) p0_1 p0_2 (9 :: ds) =
                   mkSeg true ((1, 0) :: normSeg 20 (y - 43) :: p0_1) p0_2 3 0 8 [1])
      by (destruct Hds as [-> | ->]; reflexivity).
    rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
    destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(clear - Hy49; lia); rewrite Hm_eq, Hdp9, Hn20; reflexivity. }
  apply (chainLeadsUpTo_step Hg2); intros m2 ?; rewrite Hs2.
  assert (Hg3 : stepGuards (mkSeg true ((1, 0) :: (20, y - 43) :: p0_1) p0_2 3 0 8 [1]) = true) by reflexivity.
  assert (Hs3 : stepSegs (mkSeg true ((1, 0) :: (20, y - 43) :: p0_1) p0_2 3 0 8 [1]) =
                mkSeg false ((20, y - 43) :: p0_1) p0_2 5 5 0 [1]) by reflexivity.
  apply (chainLeadsUpTo_step1 Hg3); rewrite Hs3; apply chainLeadsUpTo_here.
  refine (rootInv_of_1 Hvp0 ltac:(lia) ltac:(lia) ltac:(lia)
    (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
    _ (fun H => ltac:(cbn [fzOf] in H; lia))).
  intros _; exists (y - 43), p0_1.
  refine (conj eq_refl (conj eq_refl (conj eq_refl (conj ltac:(lia) (fun Hm0_od => conj ltac:(lia) ltac:(lia)))))).
Qed.
Arguments pop_y_19_9_leads {N y phi ds s} & _ _ _ _.

Lemma pop_y_d_leads {N d y phi : nat} {ds : list nat} {s : SegState}
    (Hb : IsBounce phi (y :: d :: ds) s)
    (Hd10 : 10 <= d) (Hds : ds = [] \/ ds = [0])
    (Hy20 : 20 <= y) (Hphi38 : 38 <= phi) :
  ChainLeadsUpTo N s RootInv270.
Proof.
  assert (Hg1 : GoodDs ((d - 1) :: ds) = true)
    by (destruct Hds as [-> | ->]; [exact (proj1 (proj2 (safeStack_d (d := d - 1) ltac:(lia))))
                                   | exact (proj1 (proj2 (safeStack_d0 (d := d - 1) ltac:(lia))))]).
  assert (Hg2 : GoodDs ((d - 2) :: ds) = true)
    by (destruct Hds as [-> | ->]; [exact (proj1 (proj2 (safeStack_d (d := d - 2) ltac:(lia))))
                                   | exact (proj1 (proj2 (safeStack_d0 (d := d - 2) ltac:(lia))))]).
  assert (Hnrst : isDrainRstDs (y :: d :: ds) = false) by (destruct d; [lia | reflexivity]).
  assert (Hnr0 : isRank0 (y :: d :: ds) = false) by (destruct y as [|[|[|?]]]; [lia | lia | lia | reflexivity]).
  assert (Hg_pop : drainPopGuards phi (y :: d :: ds) = true).
  { unfold drainPopGuards; rewrite Hnrst, Hnr0.
    replace ((3 <=? y) && (1 <=? d)) with true by lia.
    rewrite Hg1, Hg2, !orb_true_r; cbn [andb]; lia. }
  destruct (isBounce_step Hb Hg_pop) as [Hg_s [_ [hp [m_rem [rest [zl [Hv_rest [Hzl_false Hstep]]]]]]]].
  set (p := pushSeg hp (phi + 2) m_rem rest zl).
  assert (Hdp : drainPopStep hp phi m_rem rest zl (y :: d :: ds) =
                mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) ds).
  { assert (Hd_ne1 : (d =? 1) = false) by (clear - Hd10; lia).
    assert (Hn0 : normSeg 0 (y - 3) = (0, y - 3))
      by (clear - Hy20; unfold normSeg; rw_if_neg ltac:(lia); reflexivity).
    unfold drainPopStep; rewrite Hnrst, Hnr0, Hd_ne1; cbn [andb]; rewrite Hn0; reflexivity. }
  rewrite Hdp in Hstep.
  assert (Hvp : ValidSegs40 (fst p) (snd p))
    by (unfold p; apply (validSegs40_pushSeg hp (z := phi + 2) (m := m_rem) ltac:(lia) Hv_rest); intro Hf; pose proof (Hzl_false Hf); lia).
  pose proof (fzOf_ge_40 Hvp) as Hfzp40; clearbody p.
  apply (chainLeadsUpTo_step Hg_s); intros m1 ?; rewrite Hstep.
  destruct (2 * d + 5 <=? y) eqn:Ebig.
  - destruct Hds as [-> | ->].
    + assert (Hy_sub : y - 3 = S (y - 4)) by lia.
      assert (Hpop_nil : drainPopGuards (d - 1 + 0) [] = true)
        by (change (drainPopGuards (d - 1 + 0) []) with (2 <=? d - 1 + 0); lia).
      assert (Hg_s2 : stepGuards (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) []) = true).
      { rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds].
        destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia); exact Hpop_nil. }
      apply (chainLeadsUpTo_step1 Hg_s2).
      set (q := pushSeg true (d - 1 + 0 + 1) (0 + S (y - 4) - (2 * d + 2)) (fst p) (snd p)).
      assert (Hs_s2 : stepSegs (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) []) =
                      mkSeg false (fst q) (snd q) 1 1 0 []).
      { rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds].
        destruct (S (y - 4) mod 2 =? 1); rw_if_neg ltac:(lia); reflexivity. }
      rewrite Hs_s2.
      assert (Hvtq : ValidTail40 (fst q) (snd q))
        by (unfold q; apply (validTail40_pushSeg true (z := d - 1 + 0 + 1) (m := 0 + S (y - 4) - (2 * d + 2)) (fun _ => Hvp)); discriminate).
      pose proof (fzOf_pushSeg_ge true (d - 1 + 0 + 1) (0 + S (y - 4) - (2 * d + 2)) (fst p) (snd p)) as Hfzq; fold q in Hfzq; clearbody q.
      exact (chainLeadsUpTo_here (rootInv_of_0B (or_introl eq_refl) Hvtq ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia) (fun H => ltac:(lia)) (fun _ => or_introl (conj eq_refl eq_refl)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
    + exact (bounce_r9_zero_leads (d := d) (y := y) ltac:(lia) ltac:(lia) Hvp).
  - assert (Hy_sub : y - 3 = S (y - 4)) by lia.
    destruct (y mod 2 =? 1) eqn:Ey_od.
    + assert (Hm_ev : (S (y - 4) mod 2 =? 1) = false) by lia.
      assert (Hmrg : (0 + S (y - 4) <=? 2 * d) = true) by lia.
      assert (Hg_mid : stepGuards (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) ds) = true)
        by (rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Hm_ev, Hmrg; reflexivity).
      assert (Hs_mid : stepSegs (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) ds) =
                       mkSeg false (fst p) (snd p) (d + 1) (y + 2) 0 ds)
        by (rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Hm_ev, Hmrg; f_equal; lia).
      apply (chainLeadsUpTo_step1 Hg_mid); rewrite Hs_mid.
      exact (chainLeadsUpTo_here (rootInv_of_0B Hds (validTail40_of_validSegs40 Hvp)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        (fun H => ltac:(lia)) (fun H => ltac:(lia)) (fun _ _ _ _ Hcz9 => ltac:(lia)))).
    + assert (Hm_od : (S (y - 4) mod 2 =? 1) = true) by lia.
      assert (Hmrg : (0 + (y - 4) <=? 2 * d) = true) by lia.
      assert (Hg_mid : stepGuards (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) ds) = true).
      { rewrite Hy_sub; cbn [stepGuards st_b st_segs st_cp1 st_kb st_mrg st_ds]; rewrite Hm_od, Hmrg.
        replace (d - 1 + 0) with (d - 1) by lia; exact Hg1. }
      assert (Hs_mid : stepSegs (mkSeg true ((0, y - 3) :: fst p) (snd p) (d - 1) 0 (2 * d) ds) =
                       mkSeg false (fst p) (snd p) y 1 0 ((d - 1) :: ds))
        by (rewrite Hy_sub; cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_mrg st_ds]; rewrite Hm_od, Hmrg; f_equal; [lia | f_equal; lia]).
      apply (chainLeadsUpTo_step1 Hg_mid); rewrite Hs_mid.
      assert (Hds_d1 : ((d - 1) :: ds) = [d - 1] \/ ((d - 1) :: ds) = [d - 1; 0])
        by (destruct Hds as [-> | ->]; [left; reflexivity | right; reflexivity]).
      exact (chainLeadsUpTo_here (rootInv_of_D (d := d - 1) ltac:(lia) Hds_d1
        (validTail40_of_validSegs40 Hvp) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.
Arguments pop_y_d_leads {N d y phi ds s} & _ _ _ _ _.

Lemma arith_root0_c8 {m' fz : nat} (Hm'2 : 2 <= m') (Hm'_hi : m' <= 40) (Hfz44 : 44 <= fz) :
  43 <= ox (1 + 2 * fz) (m' + fz) /\ 42 <= odw (1 + 2 * fz) (m' + fz).
Proof.
  destruct (ox_spec_lt (kz := 1 + 2 * fz) (cz := m' + fz) ltac:(lia)) as [q [r [Hr [Heq Hox]]]].
  rewrite odw_def, (Hox ltac:(lia)); lia.
Qed.




Lemma root0A_advances {s : SegState}
    (Hb0 : st_b s = false) (Hmrg : st_mrg s = 0) (Hr : Root0A s) :
  ChainAdvances s RootInv270.
Proof.
  destruct s as [b segs zl cp1 kb mrg ds]; cbn [st_b st_mrg] in Hb0, Hmrg; subst b mrg.
  destruct Hr as [Hds [Hc [Hk [z1 [m0 [m1 [rest [Hsegs [Hm0 [Hz1 Hv]]]]]]]]]].
  cbn [st_segs st_zl st_cp1 st_kb st_ds] in *; subst ds cp1 kb segs.
  destruct Hm0 as [-> | ->].
  - split; [reflexivity | intro N].
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
    exact (chainLeadsUpTo_here (rootInv_of_D (d := 10) ltac:(lia) (or_introl eq_refl) Hv
      ltac:(lia) ltac:(lia) ltac:(lia) (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia)))).
  - split; [reflexivity | intro N].
    cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
    exact (chainLeadsUpTo_here (rootInv_of_D (d := 9) ltac:(lia) (or_introl eq_refl) Hv
      ltac:(lia) ltac:(lia) ltac:(lia) (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia)))).
Qed.

Lemma root0B_advances {s : SegState}
    (Hb0 : st_b s = false) (Hmrg : st_mrg s = 0) (Hr : Root0B s) :
  ChainAdvances s RootInv270.
Proof.
  destruct s as [b segs zl c k mrg ds]; cbn [st_b st_mrg] in Hb0, Hmrg; subst b mrg.
  destruct Hr as [Hds [Hvt [Hc [Hk1 [Hkc [Hfz7 [Hcz8 [H8 [H39 H9]]]]]]]]].
  cbn [st_segs st_zl st_cp1 st_kb st_ds] in *.
  destruct ((39 <=? fzOf segs zl) && (42 <=? c + fzOf segs zl)) eqn:Ehi.
  - pose proof (safeStack_0 Hds) as HS0.
    destruct (ox_bounds_relaxed (c := c) (k := k) (fz := fzOf segs zl) Hc Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia)) as [Hox39 _].
    apply (chainAdvances_trans
      (fbound_advances (ms := 19) ltac:(lia) HS0 Hvt Hc Hk1 Hkc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    intros s' Hex N.
    destruct Hex as [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
    + exact (bounce_0_leads Hb Hds (ltac:(rewrite odw_def in Hphi; lia))).
    + assert (Hds_y : (y :: ds) = [y] \/ (y :: ds) = [y; 0])
        by (destruct Hds as [-> | ->]; [left; reflexivity | right; reflexivity]).
      exact (bounce_d_leads (d := y) Hb Hds_y (or_intror (or_intror (or_intror (or_intror (conj ltac:(lia) Hphi38)))))).
  - destruct segs as [|[z_0 m0] rest].
    + cbn [fzOf ValidTail40] in Hvt, Ehi; lia.
    + cbn [fzOf ValidTail40] in Hvt, Hfz7, Hcz8, H8, H39, H9, Ehi.
      assert (Hv_rest : ValidSegs40 rest zl) by exact Hvt.
      destruct m0 as [|m'].
      * exact (step_m0_zero_0_advances Hds Hv_rest Hc Hk1 Hkc Hcz8).
      * pose proof (goodPhiW_0 Hds (w := c + z_0 - 1) ltac:(lia)) as Hphiw.
        assert (Hds_cz : ((c + z_0) :: ds) = [c + z_0] \/ ((c + z_0) :: ds) = [c + z_0; 0])
          by (destruct Hds as [-> | ->]; [left; reflexivity | right; reflexivity]).
        assert (Hds_cz1 : ((c + z_0 + 1) :: ds) = [c + z_0 + 1] \/ ((c + z_0 + 1) :: ds) = [c + z_0 + 1; 0])
          by (destruct Hds as [-> | ->]; [left; reflexivity | right; reflexivity]).
        pose proof (fzOf_ge_40 Hv_rest) as Hfz_r.
        destruct (S m' =? 1) eqn:Em1.
        -- assert (m' = 0) by lia; subst m'.
           assert (Hg : stepGuards (mkSeg false ((z_0, 1) :: rest) zl c k 0 ds) = true).
           { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds Nat.eqb].
             rewrite Hphiw; cbn [andb]; exact (goodPsi_0 Hds ltac:(lia)). }
           split; [exact Hg | intro N].
           cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds Nat.eqb].
           exact (chainLeadsUpTo_here (rootInv_of_D (d := c + z_0 + 1) ltac:(lia) Hds_cz1
             (validTail40_of_validSegs40 Hv_rest) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
        -- pose proof (goodPsi_0 Hds (w := c + z_0 - 1) ltac:(lia)) as Hpsi_cz.
           destruct ((S m' mod 2 =? 0) && (S m' <=? 2 * (k + 2 * z_0) + 10)) eqn:Eev_sm.
           ++ assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 ds) = true)
                by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm; reflexivity).
              split; [exact Hg | intro N].
              cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm.
              exact (chainLeadsUpTo_here (rootInv_of_D (d := c + z_0) ltac:(lia) Hds_cz
                (validTail40_of_validSegs40 Hv_rest) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
           ++ assert (H_bounce_cz : 10 <= c + z_0 -> forall phi, k + 2 * z_0 <= phi ->
                        (c + z_0 = 8 /\ (phi = 16 \/ phi = 17 \/ 38 <= phi)) \/
                        (c + z_0 = 9 /\ 19 <= phi) \/
                        (10 <= c + z_0 /\ c + z_0 <= 18 /\ 19 <= phi /\ (12 <= c + z_0 -> (c + z_0) mod 2 = 0 -> 23 <= phi)) \/
                        (c + z_0 = 19 /\ 37 <= phi) \/
                        (20 <= c + z_0 /\ 38 <= phi)).
              { intros Hd10 phi Hphi_kz.
                destruct (39 <=? z_0) eqn:Ez39.
                - right; right; right; right; lia.
                - destruct (H39 ltac:(lia)) as [[-> ->] | [-> [-> Hz20]]].
                  + destruct (1 + z_0 <=? 18) eqn:E18; [right; right; left; split; [lia | split; [lia | split; [lia | intros; lia]]] |].
                    destruct (Nat.eq_dec (1 + z_0) 19) as [Heq19 | Hge20]; [right; right; right; left; lia | right; right; right; right; lia].
                  + right; right; right; right; lia. }
              destruct ((S m' mod 2 =? 1) && (S m' <=? 2 * (k + 2 * z_0) + 11)) eqn:Eod_sm.
              ** destruct (Nat.eq_dec (c + z_0) 8) as [Hcz_eq8 | Hcz_ge9].
                 --- destruct (H8 Hcz_eq8) as [m0_ [rest_ [Hseg_eq [-> [-> [-> Hfz44]]]]]].
                     inversion Hseg_eq; subst z_0 m0_ rest_; clear H8 H9 H39 Hseg_eq.
                     assert (Hg : stepGuards (mkSeg false ((7, S m') :: rest) zl 1 1 0 [0]) = true).
                     { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity. }
                     split; [exact Hg | intro N].
                     cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                     replace (S m' - 1) with m' by lia.
                     destruct (arith_root0_c8 (m' := m') (fz := fzOf rest zl) ltac:(lia) ltac:(lia) Hfz44) as [Hox43 Hodw42].
                     pose proof (proj1 (excursion270_bundle N) 39 [17; 8; 0] rest zl m' 1
                       ltac:(lia) safeStack_17_8_0 (validTail40_of_validSegs40 Hv_rest)
                       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfb.
                     apply (chainLeadsUpTo_trans Hfb).
                     intros m1 s_mid ? [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
                     +++ exact (pop_17_8_0_leads Hb ltac:(lia)).
                     +++ exact (pop_y_17_8_0_leads Hb ltac:(lia) Hphi38).
                 --- clear H8.
                     destruct (Nat.eq_dec (c + z_0) 9) as [Hcz_eq9 | Hcz_ge10].
                     +++ assert (Hck1 : c = 1 /\ k = 1)
                           by (destruct (H39 ltac:(lia)) as [H | [_ [_ ?]]]; [exact H | lia]).
                         destruct Hck1 as [-> ->]; clear H39.
                         assert (z_0 = 8) by lia; subst z_0.
                         assert (Hm'2 : 2 <= m') by lia.
                         pose proof (H9 8 (S m') rest eq_refl Hcz_eq9 ltac:(lia) ltac:(lia)) as H9_props; clear H9.
                         replace (S m' - 1) with m' in H9_props by lia.
                         destruct H9_props as [H9_1 [H9_2 H9_3]].
                         assert (HS_19 : SafeStack 43 (19 :: 9 :: ds))
                           by (destruct Hds as [-> | ->]; [exact safeStack_19_9 | exact safeStack_19_9_0]).
                         assert (Hg : stepGuards (mkSeg false ((8, S m') :: rest) zl 1 1 0 ds) = true).
                         { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                           exact (proj1 (proj2 HS_19)). }
                         split; [exact Hg | intro N].
                         cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                         replace (S m' - 1) with m' by lia.
                         assert (Hne1_19 : (19 :: 9 :: ds) <> [1]) by discriminate.
                         apply (chainLeadsUpTo_trans (fhigh_ext (N := N) (c := m') Hne1_19 HS_19 Hv_rest Hm'2 H9_1 H9_2 H9_3)).
                         intros m1 s_mid ? [[[phi [Hphi Hb]] | [y [phi [Hy49 [Hpc Hb]]]]] | [y [phi [Hy53 [Hy_od [Hphi88 Hb]]]]]].
                         *** exact (pop_19_9_leads Hb Hds ltac:(lia)).
                         *** apply (pop_y_19_9_leads Hb Hds Hy49); destruct Hpc as [H1 | H2]; [left; exact H1 | right; left; exact H2].
                         *** exact (pop_y_19_9_leads Hb Hds ltac:(lia) (or_intror (or_intror (conj Hy53 (conj Hy_od Hphi88))))).
                     +++ assert (Hd10 : 10 <= c + z_0) by lia.
                         pose proof (safeStack19_d_ds Hd10 Hds) as HS_d.
                         assert (Hne1_d : ((c + z_0) :: ds) <> [1]) by (intro Hne_abs; inversion Hne_abs; lia).
                         assert (Hx1_21 : 21 <= k + 2 * z_0 + 2)
                           by (destruct (39 <=? z_0) eqn:?; [lia | destruct (H39 ltac:(lia)) as [[-> ->] | [-> [-> _]]]; lia]).
                         assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 ds) = true).
                         { cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; cbn [andb].
                           exact (proj2 (proj2 HS_d) (k + 2 * z_0 + 2) ltac:(lia)). }
                         split; [exact Hg | intro N].
                         cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                         replace (S m' - 1) with m' by lia.
                         set (x1 := k + 2 * z_0 + 2).
                         destruct (x1 <=? 47) eqn:Ex47.
                         *** assert (Hx_lo : 23 <= x1 \/ (x1 = 21 /\ SafeStack 19 ((c + z_0) :: ds))).
                             { destruct (Nat.eq_dec x1 21) as [H21 | Hne21]; [right; exact (conj H21 HS_d) |].
                               left; unfold x1 in *; destruct (39 <=? z_0) eqn:?;
                                 [lia | destruct (H39 ltac:(lia)) as [[-> ->] | [-> [-> _]]]; lia]. }
                             apply (loop_k1_le47 (x1 := x1) (c1 := m') Hne1_d (safeStack_mono (m1 := 19) (m2 := 21) ltac:(lia) HS_d)
                               Hx_lo ltac:(lia) Hv_rest ltac:(lia)).
                             ---- intros m1 z phi ? Hz Hphi38 ? Hbz.
                                  exact (pop_y_d_leads Hbz Hd10 Hds ltac:(unfold x1 in *; lia) Hphi38).
                             ---- intros m1 ? ? Hb1.
                                  exact (bounce_d_leads (d := c + z_0) Hb1 Hds_cz (H_bounce_cz Hd10 (x1 - 1) ltac:(unfold x1; lia))).
                             ---- intros m1 ? ? Hb2.
                                  exact (bounce_d_leads (d := c + z_0) Hb2 Hds_cz (H_bounce_cz Hd10 (x1 - 2) ltac:(unfold x1; lia))).
                             ---- intros m1 c' k' p1 p2 ? -> Hk'41 Hk'c Hvp.
                                  pose proof (fzOf_ge_40 Hvp) as Hfp.
                                  exact (chainLeadsUpTo_here (rootInv_of_D (d := c + z_0) ltac:(lia) Hds_cz
                                    (validTail40_of_validSegs40 Hvp) ltac:(unfold x1; lia) ltac:(lia) Hk'c
                                    ltac:(lia) ltac:(unfold x1; lia) ltac:(lia))).
                         *** apply (chainLeadsUpTo_trans
                               (proj2 (excursion270_bundle N) 19 ((c + z_0) :: ds) rest zl m' 1 x1 39 0
                                 ltac:(lia) HS_d (or_introl Hne1_d) Hv_rest
                                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
                             intros m1 s_mid ? [[phi [Hphi Hb]] | [y [phi [Hy [Hphi38 [_ Hb]]]]]].
                             ---- apply (bounce_d_leads (d := c + z_0) Hb Hds_cz).
                                  destruct (c + z_0 <=? 18) eqn:E18; [right; right; left; split; [lia | split; [lia | split; [lia | intros; lia]]] |].
                                  destruct (Nat.eq_dec (c + z_0) 19) as [Heq19 | Hge20]; [right; right; right; left; lia | right; right; right; right; lia].
                             ---- exact (pop_y_d_leads Hb Hd10 Hds ltac:(lia) Hphi38).
              ** assert (Hm_big : 2 * (k + 2 * z_0) + 12 <= S m')
                   by (destruct (S m' mod 2 =? 0) eqn:?; destruct (S m' mod 2 =? 1) eqn:?; cbn [andb] in *; lia).
                 assert (Hg : stepGuards (mkSeg false ((z_0, S m') :: rest) zl c k 0 ds) = true)
                   by (cbn [stepGuards st_b st_segs st_cp1 st_kb st_ds]; rewrite Hphiw, Em1, Hpsi_cz, Eev_sm, Eod_sm; reflexivity).
                 split; [exact Hg | intro N].
                 cbn [stepSegs st_b st_segs st_zl st_cp1 st_kb st_ds]; rewrite Em1, Eev_sm, Eod_sm.
                 replace (normSeg 0 (S m' - 4)) with (0, S (m' - 4))
                   by (unfold normSeg; rw_if_neg ltac:(lia); f_equal; lia).
                 assert (Hbc : IsBounce (k + 2 * z_0 + 2) ((c + z_0) :: ds)
                                 (mkSeg true ((0, S (m' - 4)) :: rest) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) ((c + z_0) :: ds))).
                 { replace (k + 2 * z_0 + 2) with ((k + 2 * z_0 + 2) + 0) at 1 by lia.
                   apply (IsBounce_cons 0 (m' - 4) zl (k + 2 * z_0 + 2) 0 (2 * (k + 2 * z_0) + 6) rest ((c + z_0) :: ds) Hv_rest ltac:(lia)).
                   destruct (S (m' - 4) mod 2 =? 1); lia. }
                 destruct (Nat.eq_dec (c + z_0) 8) as [H_eq8 | H_ge9].
                 --- destruct (H8 H_eq8) as [m0_ [rest_ [Hseg_eq [-> [-> _]]]]].
                     inversion Hseg_eq; subst z_0 m0_ rest_.
                     exact (bounce_d_leads (d := 8) Hbc Hds_cz (or_introl (conj eq_refl (or_intror (or_introl eq_refl))))).
                 --- destruct (Nat.eq_dec (c + z_0) 9) as [H_eq9 | H_ge10].
                     +++ assert (Hck1 : c = 1 /\ k = 1)
                           by (destruct (H39 ltac:(lia)) as [H | [_ [_ ?]]]; [exact H | lia]).
                         destruct Hck1 as [-> ->].
                         exact (bounce_d_leads (d := 1 + z_0) Hbc Hds_cz (or_intror (or_introl (conj H_eq9 ltac:(lia))))).
                     +++ exact (bounce_d_leads (d := c + z_0) Hbc Hds_cz (H_bounce_cz ltac:(lia) (k + 2 * z_0 + 2) ltac:(lia))).
Qed.

Lemma root0_advances {s : SegState}
    (Hb0 : st_b s = false) (Hmrg : st_mrg s = 0) (Hr : Root0 s) :
  ChainAdvances s RootInv270.
Proof.
  destruct Hr as [Ha | Hb]; [exact (root0A_advances Hb0 Hmrg Ha) | exact (root0B_advances Hb0 Hmrg Hb)].
Qed.

(* ========================================================================== *)
(* Master Root Advancement & Unconditional Non-Halting Theorem (`nonhalt`)    *)
(* ========================================================================== *)

Lemma root_advances270 : forall s, RootInv270 s -> ChainAdvances s RootInv270.
Proof.
  intros s [Hb [Hmrg [H0 | [H1 | [H31 | [HD | HD1]]]]]].
  - exact (root0_advances Hb Hmrg H0).
  - exact (root1_advances Hb Hmrg H1).
  - exact (root31_advances Hb Hmrg H31).
  - exact (rootD_advances Hb Hmrg HD).
  - exact (rootD1_advances Hb Hmrg HD1).
Qed.

Local Transparent checkChainAux.
Theorem inv_s0 : Inv (ModeB_ge3 [] 1 1 []).
Proof.
  split; [reflexivity | intro fuel].
  change (checkChainAux fuel true (encSegs [] 0) 3 0 8 [1] = true).
  apply (checkChainAux_of_iter 28 fuel (mkSeg true [] 0 3 0 8 [1]) hg28_check); intro f.
  rewrite hs28_check.
  apply (checkChainAux_true_of_advances root_advances270 f (mkSeg false [(56, 223)] 489 10 21 0 [])).
  refine (rootInv_of_0B (or_introl eq_refl) (conj (fun _ H => False_ind _ H) ltac:(lia))
    ltac:(lia) ltac:(lia) ltac:(lia) (ltac:(cbn [fzOf]; lia)) (ltac:(cbn [fzOf]; lia))
    (fun H => ltac:(cbn [fzOf] in H; lia)) (fun H => ltac:(cbn [fzOf] in H; lia))
    (fun _ _ _ _ Hcz9 => ltac:(cbn [fzOf] in Hcz9; lia))).
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  apply (multistep_nonhalt tm c0 (toCfg (ModeB_ge3 [] 1 1 []))
           (progress_evstep tm c0 (toCfg (ModeB_ge3 [] 1 1 [])) init_to_s0)).
  apply (progress_nonhalt_cond tm State270 (ModeB_ge3 [] 1 1 []) toCfg Inv).
  - intros s hI. exists (nextState s). split; [exact (step_toCfg s hI) | exact (step_Inv s hI)].
  - exact inv_s0.
Qed.


