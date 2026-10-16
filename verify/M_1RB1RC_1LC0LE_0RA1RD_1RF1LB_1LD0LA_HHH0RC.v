(* 1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat PeanoNat String Lists.List.
Import ListNotations.

Open Scope list_scope.
Open Scope nat_scope.

Definition tm := Eval compute in
  (TM_from_str "1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC"%string).

Definition holdout_0311_tm : TM := tm.

(* ========================================================================== *)
(* Transition Combinators and Local Stepper                                   *)
(* ========================================================================== *)

Lemma stepPlus_stepStar {m c1 c2} (H : c1 -[ m ]->+ c2) : c1 -[ m ]->* c2.
Proof. exact (progress_evstep m c1 c2 H). Qed.

Lemma stepPlus_stepPlus_stepPlus {m c1 c2 c3}
  (H1 : c1 -[ m ]->+ c2) (H2 : c2 -[ m ]->+ c3) : c1 -[ m ]->+ c3.
Proof. exact (progress_trans m c1 c2 c3 H1 H2). Qed.

Lemma stepPlus_stepStar_stepPlus {m c1 c2 c3}
  (H1 : c1 -[ m ]->+ c2) (H2 : c2 -[ m ]->* c3) : c1 -[ m ]->+ c3.
Proof. exact (progress_evstep_trans m c1 c2 c3 H1 H2). Qed.

Lemma stepStar_stepPlus_stepPlus {m c1 c2 c3}
  (H1 : c1 -[ m ]->* c2) (H2 : c2 -[ m ]->+ c3) : c1 -[ m ]->+ c3.
Proof. exact (evstep_progress_trans m c1 c2 c3 H1 H2). Qed.

Lemma stepStar_trans {m c1 c2 c3}
  (H1 : c1 -[ m ]->* c2) (H2 : c2 -[ m ]->* c3) : c1 -[ m ]->* c3.
Proof. exact (evstep_trans m c1 c2 c3 H1 H2). Qed.

Definition cfg_of (q : Q) (d : dir) (l r : side) : Q * tape :=
  match d with
  | L => l <{{q}} r
  | R => l {{q}}> r
  end.

Record LocalState := mkLocalState {
  ls_l : list Sym;
  ls_r : list Sym;
  ls_q : Q;
  ls_d : dir
}.

Definition step_local (m : TM) (s : LocalState) : option LocalState :=
  match ls_d s with
  | L =>
    match ls_l s with
    | [] => None
    | b :: l =>
      match m (ls_q s, b) with
      | Some (b', L, q') => Some (mkLocalState l (b' :: ls_r s) q' L)
      | Some (b', R, q') => Some (mkLocalState (b' :: l) (ls_r s) q' R)
      | None => None
      end
    end
  | R =>
    match ls_r s with
    | [] => None
    | b :: r =>
      match m (ls_q s, b) with
      | Some (b', L, q') => Some (mkLocalState (ls_l s) (b' :: r) q' L)
      | Some (b', R, q') => Some (mkLocalState (b' :: ls_l s) r q' R)
      | None => None
      end
    end
  end.

Lemma step_local_spec (m : TM) (s1 s2 : LocalState) (L0 R0 : side) :
  step_local m s1 = Some s2 ->
  cfg_of (ls_q s1) (ls_d s1) (ls_l s1 *> L0) (ls_r s1 *> R0) -[ m ]->
  cfg_of (ls_q s2) (ls_d s2) (ls_l s2 *> L0) (ls_r s2 *> R0).
Proof.
  unfold step_local, cfg_of; destruct s1 as [l1 r1 q1 [|]], s2 as [l2 r2 q2 d2]; simpl.
  - destruct l1 as [|b l]; [discriminate|].
    destruct (m (q1, b)) as [[[b' [|]] q']|] eqn:Hm; intros H; inversion H; subst; clear H; simpl.
    + apply step_left; exact Hm.
    + apply step_right; exact Hm.
  - destruct r1 as [|b r]; [discriminate|].
    destruct (m (q1, b)) as [[[b' [|]] q']|] eqn:Hm; intros H; inversion H; subst; clear H; simpl.
    + apply step_left; exact Hm.
    + apply step_right; exact Hm.
Qed.

Fixpoint run_local (m : TM) (n : nat) (s : LocalState) : option LocalState :=
  match n with
  | O => Some s
  | S n' =>
    match step_local m s with
    | Some s' => run_local m n' s'
    | None => None
    end
  end.

Lemma run_local_spec (m : TM) (n : nat) (s1 s2 : LocalState) (L0 R0 : side) :
  run_local m n s1 = Some s2 ->
  cfg_of (ls_q s1) (ls_d s1) (ls_l s1 *> L0) (ls_r s1 *> R0) -[ m ]->*
  cfg_of (ls_q s2) (ls_d s2) (ls_l s2 *> L0) (ls_r s2 *> R0).
Proof.
  revert s1.
  induction n as [|n IH]; intros s1 H; simpl in H.
  - inversion H; subst; apply evstep_refl.
  - destruct (step_local m s1) as [sm|] eqn:Hs; [|discriminate].
    eapply evstep_step.
    + exact (step_local_spec m s1 sm L0 R0 Hs).
    + exact (IH sm H).
Qed.

Lemma run_local_plus_eq (m : TM) (n : nat) (s1 s2 : LocalState) (c1 c2 : Q * tape) (L0 R0 : side) :
  run_local m (S n) s1 = Some s2 ->
  cfg_of (ls_q s1) (ls_d s1) (ls_l s1 *> L0) (ls_r s1 *> R0) = c1 ->
  cfg_of (ls_q s2) (ls_d s2) (ls_l s2 *> L0) (ls_r s2 *> R0) = c2 ->
  c1 -[ m ]->+ c2.
Proof.
  intros H <- <-.
  simpl in H.
  destruct (step_local m s1) as [sm|] eqn:Hs; [|discriminate].
  eapply progress_intro.
  - exact (step_local_spec m s1 sm L0 R0 Hs).
  - exact (run_local_spec m n sm s2 L0 R0 H).
Qed.

(* ========================================================================== *)
(* Mode Configurations and Finite-Step Lemmas                                 *)
(* ========================================================================== *)

Definition cfg_modeC (l r : side) : Q * tape :=
  (S1 >> S0 >> l) {{C}}> r.

Definition cfg_modeE1 (l r : side) : Q * tape :=
  (S1 >> S0 >> l) <{{E}} (S0 >> S1 >> r).

Definition cfg_modeE0_first (l : side) : Q * tape :=
  (S0 >> S1 >> S0 >> l) <{{E}} (S0 >> S1 >> const S0).

Definition cfg_modeE0_loop (l r : side) : Q * tape :=
  (S0 >> l) <{{E}} (S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r).

Definition cfg_b101_mid (l : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) <{{E}} (S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> const S0).

Definition cfg_e0f_mid (l : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).

Definition cfg_e0l_mid (l r : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).

Definition cfg_transA_mid (l : side) : Q * tape :=
  (S1 >> S1 >> S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).

Definition cfg_transB_mid (l r : side) : Q * tape :=
  (S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> l) {{B}}> (S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).

Ltac norm_cfg :=
  unfold cfg_modeC, cfg_modeE1, cfg_modeE0_first, cfg_modeE0_loop,
         cfg_b101_mid, cfg_e0f_mid, cfg_e0l_mid, cfg_transA_mid, cfg_transB_mid,
         cfg_of, c0, tape0, q0, s0;
  cbn [ls_q ls_d ls_l ls_r Str_app hd tl];
  repeat rewrite <- const_unfold;
  reflexivity.

Ltac solve_local m n s1 L0 R0 :=
  eapply (run_local_plus_eq m n s1 _ _ _ L0 R0);
  [ cbv; reflexivity | norm_cfg | norm_cfg ].

Lemma init_reaches_modeC :
  c0 -[ holdout_0311_tm ]->+ cfg_modeC (S0 >> S1 >> const S0) (const S0).
Proof.
  solve_local holdout_0311_tm 9 (mkLocalState [S0; S0] [S0; S0] A R) (const S0) (const S0).
Qed.

Lemma step_modeC_nil (l : side) :
  cfg_modeC l (const S0) -[ holdout_0311_tm ]->+ cfg_modeE0_first l.
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S1; S0] [S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01 (l r : side) :
  cfg_modeC l (S0 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_modeC (S1 >> S0 >> l) r.
Proof.
  solve_local holdout_0311_tm 1 (mkLocalState [S1; S0] [S0; S1] C R) l r.
Qed.

Lemma step_modeC_b01_b10101 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) r.
Proof.
  solve_local holdout_0311_tm 6 (mkLocalState [S1; S0] [S0; S1; S1; S0; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeC_b11 (l r : side) :
  cfg_modeC l (S1 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_modeE1 l r.
Proof.
  solve_local holdout_0311_tm 2 (mkLocalState [S1; S0] [S1; S1] C R) l r.
Qed.

Lemma step_modeC_b01_b000 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S0 >> S0 >> S0 >> r) -[ holdout_0311_tm ]->+ cfg_modeE0_loop l r.
Proof.
  solve_local holdout_0311_tm 13 (mkLocalState [S1; S0] [S0; S1; S0; S0; S0] C R) l r.
Qed.

Lemma step_modeC_b01_b101_nil_1 (l : side) :
  cfg_modeC (S1 >> S0 >> l) (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+ cfg_b101_mid l.
Proof.
  solve_local holdout_0311_tm 33
    (mkLocalState [S1; S0; S1; S0] [S1; S0; S1; S0; S0; S0; S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01_b101_nil_2 (l : side) :
  cfg_b101_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 (S1 >> S0 >> l) (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).
Proof.
  solve_local holdout_0311_tm 32
    (mkLocalState [S1; S1; S1; S1; S0; S1; S0] [S0; S1; S0; S1; S0; S1] E L) l (const S0).
Qed.

Lemma step_modeC_b01_b1011101 (l r : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 16
    (mkLocalState [S1; S0] [S0; S1; S1; S0; S1; S1; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeE1_base (r : side) :
  cfg_modeE1 (S0 >> S1 >> const S0) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0) (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S1; S0; S0; S1; S0; S0; S0; S0] [S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE1_b10 (l r : side) :
  cfg_modeE1 (S1 >> S0 >> l) r -[ holdout_0311_tm ]->+ cfg_modeE1 l (S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S1; S0; S1; S0] [S0; S1] E L) l r.
Qed.

Lemma step_modeC_b01_b101_nil (l : side) :
  cfg_modeC l (S0 >> S1 >> S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01 l _)
    (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_1 l)
      (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_2 l) (step_modeE1_b10 l _)))).
Qed.

Lemma step_modeE1_b011_10_base (r : side) :
  cfg_modeE1 (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r))).
Proof.
  solve_local holdout_0311_tm 33
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S0; S1; S0; S0; S0; S0] [S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE1_b011_10_b10 (l r : side) :
  cfg_modeE1 (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 14
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1] E L) l r.
Qed.

Lemma step_modeE0_first_base :
  cfg_modeE0_first (S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S0; S1; S0; S0; S1; S0; S0; S0] [S0; S1] E L) (const S0) (const S0).
Qed.

Lemma step_modeE0_first_b10 (l : side) :
  cfg_modeE0_first (S1 >> S0 >> l) -[ holdout_0311_tm ]->+ cfg_modeE0_loop l (const S0).
Proof.
  solve_local holdout_0311_tm 5 (mkLocalState [S0; S1; S0; S1; S0] [S0; S1] E L) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_base_1 :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) -[ holdout_0311_tm ]->+
    cfg_modeE1 (S0 >> S1 >> const S0) (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 35
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S0; S1] [S0; S1] E L) (const S0) (const S0).
Qed.

Lemma step_modeE0_first_b011_10_base :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus step_modeE0_first_b011_10_base_1 (step_modeE1_base _)).
Qed.

Lemma step_modeE0_first_b011_10_b10_1 (l : side) :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) -[ holdout_0311_tm ]->+ cfg_e0f_mid l.
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1] E L) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_b10_2 (l : side) :
  cfg_e0f_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1] B R) l (const S0).
Qed.

Lemma step_modeE0_first_b011_10_b10 (l : side) :
  cfg_modeE0_first (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l)) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_first_b011_10_b10_1 l) (step_modeE0_first_b011_10_b10_2 l)).
Qed.

Lemma step_modeE0_loop_base (r : side) :
  cfg_modeE0_loop (S0 >> S1 >> const S0) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) (S0 >> S1 >> r).
Proof.
  solve_local holdout_0311_tm 26
    (mkLocalState [S0; S0; S1; S0; S0] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_base (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> const S0)) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> r))))).
Proof.
  solve_local holdout_0311_tm 24
    (mkLocalState [S0; S1; S0; S0; S1; S0; S0; S0] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_b10 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S1 >> S0 >> l)) r -[ holdout_0311_tm ]->+
    cfg_modeE0_loop l (S1 >> S1 >> (S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 5
    (mkLocalState [S0; S1; S0; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_base_1 (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0))) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (S0 >> S1 >> const S0)
      (S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 35
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S0; S1] [S0; S1; S1; S1; S0; S1] E L) (const S0) r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_base (r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0))) r -[ holdout_0311_tm ]->+
    cfg_modeC (S0 >> S1 >> const S0)
      (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_base_1 r) (step_modeE1_base _)).
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_1 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))) r -[ holdout_0311_tm ]->+
    cfg_e0l_mid l r.
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S0; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_2 (l r : side) :
  cfg_e0l_mid l r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  solve_local holdout_0311_tm 20
    (mkLocalState [S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1; S1; S1; S0; S1] B R) l r.
Qed.

Lemma step_modeE0_loop_b10_b011_10_b10 (l r : side) :
  cfg_modeE0_loop (S1 >> S0 >> (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_b10_1 l r) (step_modeE0_loop_b10_b011_10_b10_2 l r)).
Qed.

Lemma step_modeE0_loop_b011_10 (l r : side) :
  cfg_modeE0_loop (S0 >> S1 >> S1 >> S1 >> S0 >> l) r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  solve_local holdout_0311_tm 27
    (mkLocalState [S0; S0; S1; S1; S1; S0] [S0; S1; S1; S1; S0; S1] E L) l r.
Qed.

Lemma step_modeC_b01110_b10_b101_nil_1 (l : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+ cfg_transA_mid l.
Proof.
  solve_local holdout_0311_tm 40
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S1; S0; S1; S0; S0; S0; S0; S0; S0] C R) l (const S0).
Qed.

Lemma step_modeC_b01110_b10_b101_nil_2 (l : side) :
  cfg_transA_mid l -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof.
  solve_local holdout_0311_tm 40
    (mkLocalState [S1; S1; S1; S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S0; S0; S1; S0; S1] B R) l (const S0).
Qed.

Lemma step_modeC_b01110_b10_b101_nil (l : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b101_nil_1 l) (step_modeC_b01110_b10_b101_nil_2 l)).
Qed.

Lemma step_modeC_b01110_b10_b0000101_1 (l r : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+ cfg_transB_mid l r.
Proof.
  solve_local holdout_0311_tm 23
    (mkLocalState [S1; S0; S0; S1; S1; S1; S0; S1; S0] [S0; S0; S0; S0; S1; S0; S1] C R) l r.
Qed.

Lemma step_modeC_b01110_b10_b0000101_2 (l r : side) :
  cfg_transB_mid l r -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  solve_local holdout_0311_tm 23
    (mkLocalState [S1; S0; S1; S1; S0; S1; S0] [S1; S0; S1; S0; S1; S0; S1; S0; S1] B R) l r.
Qed.

Lemma step_modeC_b01110_b10_b0000101 (l r : side) :
  cfg_modeC (S0 >> S1 >> S1 >> S1 >> S0 >> (S1 >> S0 >> l))
    (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 l (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof.
  exact (stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b0000101_1 l r) (step_modeC_b01110_b10_b0000101_2 l r)).
Qed.

(* ========================================================================== *)
(* Parametric Left-Tape Encoding and Invariant                                *)
(* ========================================================================== *)

Fixpoint prepend10 (k : nat) (l : side) : side :=
  match k with
  | O => l
  | S k' => S1 >> S0 >> prepend10 k' l
  end.

Fixpoint encL_tail (ks : list nat) : side :=
  match ks with
  | [] => S0 >> S1 >> const S0
  | k :: ks' => S0 >> S1 >> S1 >> S1 >> S0 >> prepend10 k (encL_tail ks')
  end.

Definition encL (k0 : nat) (ks : list nat) : side :=
  prepend10 k0 (encL_tail ks).

Lemma encL_zero_nil : encL 0 [] = S0 >> S1 >> const S0.
Proof. reflexivity. Qed.

Lemma encL_S (k : nat) (ks : list nat) :
  encL (S k) ks = S1 >> S0 >> encL k ks.
Proof. reflexivity. Qed.

Lemma encL_succ (k : nat) (ks : list nat) :
  encL (k + 1) ks = S1 >> S0 >> encL k ks.
Proof. rewrite Nat.add_1_r. reflexivity. Qed.

Lemma encL_zero_cons (k : nat) (ks : list nat) :
  encL 0 (k :: ks) = S0 >> S1 >> S1 >> S1 >> S0 >> encL k ks.
Proof. reflexivity. Qed.

Lemma step_modeC_b01_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeC (encL k0 ks) (S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (encL (k0 + 1) ks) r.
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01 (encL k0 ks) r). Qed.

Lemma step_modeC_b01_b10101_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeC (encL k0 ks) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeC (encL 0 ((k0 + 1) :: ks)) r.
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01_b10101 (encL k0 ks) r). Qed.

Lemma step_modeE1_b10_encL (k0 : nat) (ks : list nat) (r : side) :
  cfg_modeE1 (encL (k0 + 1) ks) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL k0 ks) (S0 >> S1 >> r).
Proof. rewrite Nat.add_1_r. exact (step_modeE1_b10 (encL k0 ks) r). Qed.

Lemma step_modeE1_b011_10_b10_encL (k1 : nat) (ks : list nat) (r : side) :
  cfg_modeE1 (encL 0 ((k1 + 1) :: ks)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL k1 ks) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> r).
Proof. rewrite Nat.add_1_r. exact (step_modeE1_b011_10_b10 (encL k1 ks) r). Qed.

Lemma step_modeE0_first_b10_encL (x0 : nat) (ks : list nat) :
  cfg_modeE0_first (encL (x0 + 1) ks) -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL x0 ks) (const S0).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_first_b10 (encL x0 ks)). Qed.

Lemma step_modeE0_first_b011_10_b10_encL (x1 : nat) (ks : list nat) :
  cfg_modeE0_first (encL 0 ((x1 + 1) :: ks)) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL x1 ks) (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_first_b011_10_b10 (encL x1 ks)). Qed.

Lemma step_modeE0_loop_b10_b011_10_b10_encL (x1 : nat) (ks : list nat) (r : side) :
  cfg_modeE0_loop (encL 1 ((x1 + 1) :: ks)) r -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL x1 ks) (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> r)).
Proof. rewrite Nat.add_1_r. exact (step_modeE0_loop_b10_b011_10_b10 (encL x1 ks) r). Qed.

Lemma step_modeC_b01110_b10_b101_nil_encL (z1 : nat) (zs : list nat) :
  cfg_modeC (encL 0 ((z1 + 1) :: zs)) (S1 >> S0 >> S1 >> const S0) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL z1 zs) (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >>
      (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0)).
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01110_b10_b101_nil (encL z1 zs)). Qed.

Lemma step_modeC_b01110_b10_b0000101_encL (z1 : nat) (zs : list nat) (r : side) :
  cfg_modeC (encL 0 ((z1 + 1) :: zs)) (S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> r) -[ holdout_0311_tm ]->+
    cfg_modeE1 (encL z1 zs) (S0 >> S1 >> S0 >> S0 >> S0 >>
      (S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> r)))).
Proof. rewrite Nat.add_1_r. exact (step_modeC_b01110_b10_b0000101 (encL z1 zs) r). Qed.

Fixpoint prepend01 (k : nat) (r : side) : side :=
  match k with
  | O => r
  | S k' => S0 >> S1 >> prepend01 k' r
  end.

Lemma prepend01_add (a b : nat) (r : side) :
  prepend01 (a + b) r = prepend01 a (prepend01 b r).
Proof.
  induction a as [|a IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Fixpoint prepend11_01 (d : nat) (r : side) : side :=
  match d with
  | O => r
  | S d' => S1 >> S1 >> S0 >> S1 >> prepend11_01 d' r
  end.

Lemma prepend11_01_add (a b : nat) (r : side) :
  prepend11_01 (a + b) r = prepend11_01 a (prepend11_01 b r).
Proof.
  induction a as [|a IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Fixpoint add_last (ks : list nat) (c : nat) : list nat :=
  match ks with
  | [] => []
  | [x] => [x + c]
  | x :: ((_ :: _) as rest) => x :: add_last rest c
  end.

Lemma add_last_cons (x : nat) (ks : list nat) (c : nat) :
  ks <> [] -> add_last (x :: ks) c = x :: add_last ks c.
Proof.
  destruct ks as [|y rest]; [congruence | reflexivity].
Qed.

Lemma add_last_length (ks : list nat) (c : nat) :
  List.length (add_last ks c) = List.length ks.
Proof.
  induction ks as [|x [|y rest] IH]; simpl; [reflexivity | reflexivity | f_equal; exact IH].
Qed.

Lemma add_last_ne_nil (ks : list nat) (c : nat) :
  ks <> [] -> add_last ks c <> [].
Proof.
  destruct ks as [|x [|y rest]]; simpl; congruence.
Qed.

Lemma add_last_zero (ks : list nat) :
  add_last ks 0 = ks.
Proof.
  induction ks as [|x [|y rest] IH]; simpl; [reflexivity | f_equal; lia | f_equal; exact IH].
Qed.

Lemma add_last_add (ks : list nat) (a b : nat) :
  add_last (add_last ks a) b = add_last ks (a + b).
Proof.
  induction ks as [|x [|y rest] IH].
  - reflexivity.
  - simpl; f_equal; lia.
  - rewrite (add_last_cons x (y :: rest) a ltac:(discriminate)).
    rewrite (add_last_cons x (add_last (y :: rest) a) b (add_last_ne_nil (y :: rest) a ltac:(discriminate))).
    rewrite (add_last_cons x (y :: rest) (a + b) ltac:(discriminate)).
    f_equal; exact IH.
Qed.

Definition bump_enc (k0 : nat) (ks : list nat) : nat * list nat :=
  match ks with
  | [] => (k0 + 3, [])
  | k1 :: ks' => (k0, add_last (k1 :: ks') 3)
  end.

Definition bump_enc_twice (m0 : nat) (ms : list nat) : nat * list nat :=
  let p := bump_enc m0 ms in
  bump_enc (fst p) (snd p).

Lemma bump_enc_nonempty (k0 : nat) (ks : list nat) :
  ks <> [] -> bump_enc k0 ks = (k0, add_last ks 3).
Proof.
  destruct ks as [|k1 ks']; [congruence | reflexivity].
Qed.

Lemma bump_enc_twice_nonempty (m0 : nat) (ms : list nat) :
  ms <> [] -> bump_enc_twice m0 ms = (m0, add_last ms 6).
Proof.
  intros Hne. unfold bump_enc_twice.
  rewrite (bump_enc_nonempty m0 ms Hne); simpl.
  rewrite (bump_enc_nonempty m0 (add_last ms 3) (add_last_ne_nil ms 3 Hne)).
  rewrite add_last_add. reflexivity.
Qed.

Fixpoint ValidKS (ks : list nat) : Prop :=
  match ks with
  | [] => True
  | [_] => True
  | k :: ((_ :: _) as rest) => k >= 1 /\ ValidKS rest
  end.

Lemma ValidKS_add_last (ks : list nat) (c : nat) :
  ValidKS ks -> ValidKS (add_last ks c).
Proof.
  induction ks as [|k [|y rest] IH]; intros Hval; [exact I | exact I |].
  destruct Hval as [Hk Hrest].
  rewrite (add_last_cons k (y :: rest) c ltac:(discriminate)).
  pose proof (add_last_ne_nil (y :: rest) c ltac:(discriminate)) as Hne.
  pose proof (IH Hrest) as Hih.
  destruct (add_last (y :: rest) c) as [|z zs]; [congruence | exact (conj Hk Hih)].
Qed.

Fixpoint GoodKS (s : nat) (ks : list nat) : Prop :=
  match ks with
  | [] => True
  | k :: rest => s <= 35 * (k + 2) /\ GoodKS (s + 63 * (k + 2)) rest
  end.

Lemma GoodKS_mono (ks : list nat) :
  forall (s1 s2 : nat), s1 <= s2 -> GoodKS s2 ks -> GoodKS s1 ks.
Proof.
  induction ks as [|k rest IH]; simpl; intros s1 s2 Hle Hg; [exact I |].
  destruct Hg as [H1 H2].
  split; [lia | apply (IH _ (s2 + 63 * (k + 2))); [lia | exact H2]].
Qed.

Lemma GoodKS_add_last (ks : list nat) :
  forall (s c : nat), GoodKS s ks -> GoodKS s (add_last ks c).
Proof.
  induction ks as [|k [|y rest] IH]; simpl; intros s c Hg; [exact I | |].
  - destruct Hg as [H1 _]; split; [lia | exact I].
  - destruct Hg as [H1 H2]; split; [exact H1 | apply IH; exact H2].
Qed.

Lemma GoodKS_valid (ks : list nat) :
  forall (s : nat), s >= 71 -> GoodKS s ks -> ValidKS ks.
Proof.
  induction ks as [|k [|y rest] IH]; simpl; intros s Hs Hg; [exact I | exact I |].
  destruct Hg as [H1 H2].
  split; [lia | apply (IH (s + 63 * (k + 2))); [lia | exact H2]].
Qed.

Lemma GoodKS_succ_valid (s w : nat) (ws : list nat) :
  GoodKS s ((w + 1) :: ws) -> ValidKS ((w + 1) :: ws).
Proof.
  destruct ws as [|y rest]; simpl; intros Hg; [exact I |].
  destruct Hg as [H1 H2].
  split; [lia | apply (GoodKS_valid (y :: rest) (s + 63 * (w + 1 + 2))); [lia | exact H2]].
Qed.

Definition InvNil (k0 : nat) (ks : list nat) : Prop :=
  (ks = [] /\ k0 >= 5) \/
  (ks <> [] /\ GoodKS (if Nat.eqb k0 1 then 81 else 36 * (k0 + 2)) ks).

(* ========================================================================== *)
(* Macro Transitions (Mode C / E1 / E0_loop)                                  *)
(* ========================================================================== *)

Lemma modeC_prepend01_star (n : nat) :
  forall (k0 : nat) (ks : list nat) (r : side),
    cfg_modeC (encL k0 ks) (prepend01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + n) ks) r.
Proof.
  induction n as [|n IH]; intros k0 ks r; cbn [prepend01].
  - replace (k0 + 0) with k0 by lia. apply evstep_refl.
  - pose proof (step_modeC_b01_encL k0 ks (prepend01 n r)) as H1.
    pose proof (IH (k0 + 1) ks r) as H2.
    replace (k0 + 1 + n) with (k0 + S n) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma e0_loop_drain_pairs (d : nat) :
  forall (rem : nat) (xs : list nat) (r : side),
    cfg_modeE0_loop (encL (rem + 2 * d) xs) r -[ holdout_0311_tm ]->*
      cfg_modeE0_loop (encL rem xs) (prepend11_01 d r).
Proof.
  induction d as [|d IH]; intros rem xs r; cbn [prepend11_01].
  - replace (rem + 2 * 0) with rem by lia. apply evstep_refl.
  - replace (rem + 2 * S d) with (S (S (rem + 2 * d))) by lia.
    pose proof (step_modeE0_loop_b10_b10 (encL (rem + 2 * d) xs) r) as H1.
    change (S1 >> S1 >> (S0 >> S1 >> r)) with (prepend11_01 1 r) in H1.
    pose proof (IH rem xs (prepend11_01 1 r)) as H2.
    rewrite <- prepend11_01_add in H2.
    replace (d + 1) with (S d) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma modeE1_drain_k0 (k0 : nat) :
  forall (ks : list nat) (r : side),
    cfg_modeE1 (encL k0 ks) r -[ holdout_0311_tm ]->*
      cfg_modeE1 (encL 0 ks) (prepend01 k0 r).
Proof.
  induction k0 as [|k0 IH]; intros ks r.
  - apply evstep_refl.
  - pose proof (step_modeE1_b10 (encL k0 ks) r) as H1.
    change (S0 >> S1 >> r) with (prepend01 1 r) in H1.
    pose proof (IH ks (prepend01 1 r)) as H2.
    rewrite <- prepend01_add in H2.
    replace (k0 + 1) with (S k0) in H2 by lia.
    exact (stepPlus_stepStar (stepPlus_stepStar_stepPlus H1 H2)).
Qed.

Lemma modeE1_to_modeC (ks : list nat) :
  forall (k0 : nat) (r : side),
    ValidKS ks ->
    let b := bump_enc k0 ks in
    cfg_modeE1 (encL k0 ks) r -[ holdout_0311_tm ]->+ cfg_modeC (encL (fst b) (snd b)) r.
Proof.
  induction ks as [|k1 ks' IH]; intros k0 r Hval; simpl.
  - pose proof (modeE1_drain_k0 k0 [] r) as H1.
    pose proof (step_modeE1_base (prepend01 k0 r)) as H2.
    change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend01 k0 r)))
      with (prepend01 3 (prepend01 k0 r)) in H2.
    rewrite <- prepend01_add in H2.
    replace (3 + k0) with (k0 + 3) in H2 by lia.
    pose proof (modeC_prepend01_star (k0 + 3) 0 [] r) as H3; simpl in H3.
    exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 H3)).
  - destruct ks' as [|k2 ks''].
    + simpl.
      pose proof (modeE1_drain_k0 k0 [k1] r) as H1.
      destruct k1 as [|k1'].
      * pose proof (step_modeE1_b011_10_base (prepend01 k0 r)) as H2.
        pose proof (step_modeC_b01 (encL 0 [])
          (S0 >> S1 >> (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r))) as H3.
        pose proof (step_modeC_b01 (encL 1 [])
          (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r)) as H4.
        pose proof (step_modeC_b01_b10101_encL 2 [] (prepend01 k0 r)) as H5; simpl in H5.
        pose proof (modeC_prepend01_star k0 0 [3] r) as H6; simpl in H6.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepStar_stepPlus H5 H6))))).
      * pose proof (step_modeE1_b011_10_b10 (encL k1' []) (prepend01 k0 r)) as H2.
        pose proof (IH k1' (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r) I) as H3.
        simpl in H3.
        pose proof (step_modeC_b01_b10101_encL (k1' + 3) [] (prepend01 k0 r)) as H4.
        replace (k1' + 3 + 1) with (S k1' + 3) in H4 by lia.
        pose proof (modeC_prepend01_star k0 0 [S k1' + 3] r) as H5; simpl in H5.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepStar_stepPlus H4 H5)))).
    + simpl in Hval. destruct Hval as [Hk1 Hval'].
      destruct k1 as [|k1']; [lia|].
      simpl.
      pose proof (modeE1_drain_k0 k0 (S k1' :: k2 :: ks'') r) as H1.
      pose proof (step_modeE1_b011_10_b10 (encL k1' (k2 :: ks'')) (prepend01 k0 r)) as H2.
      pose proof (IH k1' (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> prepend01 k0 r) Hval') as H3.
      simpl in H3.
      pose proof (step_modeC_b01_b10101 (encL k1' (add_last (k2 :: ks'') 3)) (prepend01 k0 r)) as H4.
      pose proof (modeC_prepend01_star k0 0 (S k1' :: add_last (k2 :: ks'') 3) r) as H5; simpl in H5.
      exact (stepStar_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepPlus_stepPlus H3
            (stepPlus_stepStar_stepPlus H4 H5)))).
Qed.

Lemma modeC_consume_11_01_nil (n : nat) :
  forall (k0 : nat) (r : side),
    cfg_modeC (encL k0 []) (prepend11_01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + 4 * n) []) r.
Proof.
  induction n as [|n IH]; intros k0 r; cbn [prepend11_01].
  - replace (k0 + 4 * 0) with k0 by lia. apply evstep_refl.
  - pose proof (step_modeC_b11 (encL k0 []) (S0 >> S1 >> prepend11_01 n r)) as H1.
    pose proof (modeE1_to_modeC [] k0 (S0 >> S1 >> prepend11_01 n r) I) as H2; simpl in H2.
    pose proof (step_modeC_b01_encL (k0 + 3) [] (prepend11_01 n r)) as H3.
    replace (k0 + 3 + 1) with (k0 + 4) in H3 by lia.
    pose proof (IH (k0 + 4) r) as H4.
    replace (k0 + 4 + 4 * n) with (k0 + 4 * S n) in H4 by lia.
    exact (stepPlus_stepStar
      (stepPlus_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepStar_stepPlus H3 H4)))).
Qed.

Lemma modeC_consume_11_01_nonempty (n : nat) :
  forall (k0 : nat) (ks : list nat) (r : side),
    ks <> [] -> ValidKS ks ->
    cfg_modeC (encL k0 ks) (prepend11_01 n r) -[ holdout_0311_tm ]->*
      cfg_modeC (encL (k0 + n) (add_last ks (3 * n))) r.
Proof.
  induction n as [|n IH]; intros k0 ks r Hne Hval; cbn [prepend11_01].
  - replace (k0 + 0) with k0 by lia. replace (3 * 0) with 0 by lia.
    rewrite add_last_zero. apply evstep_refl.
  - pose proof (step_modeC_b11 (encL k0 ks) (S0 >> S1 >> prepend11_01 n r)) as H1.
    pose proof (modeE1_to_modeC ks k0 (S0 >> S1 >> prepend11_01 n r) Hval) as H2; simpl in H2.
    rewrite (bump_enc_nonempty k0 ks Hne) in H2; simpl in H2.
    pose proof (step_modeC_b01_encL k0 (add_last ks 3) (prepend11_01 n r)) as H3.
    pose proof (IH (k0 + 1) (add_last ks 3) r
      (add_last_ne_nil ks 3 Hne) (ValidKS_add_last ks 3 Hval)) as H4.
    rewrite add_last_add in H4.
    replace (k0 + 1 + n) with (k0 + S n) in H4 by lia.
    replace (3 + 3 * n) with (3 * S n) in H4 by lia.
    exact (stepPlus_stepStar
      (stepPlus_stepPlus_stepPlus H1
        (stepPlus_stepPlus_stepPlus H2
          (stepPlus_stepStar_stepPlus H3 H4)))).
Qed.

Lemma ValidKS_bump_enc (m0 : nat) (ms : list nat) :
  ValidKS ms -> ValidKS (snd (bump_enc m0 ms)).
Proof.
  destruct ms as [|x rest]; simpl; intros H; [exact I | exact (ValidKS_add_last (x :: rest) 3 H)].
Qed.

Lemma unwrap_11_01_1011101_step (m0 : nat) (ms : list nat) (R0 : side) :
  ValidKS ms ->
  let p := bump_enc_twice m0 ms in
  cfg_modeC (encL m0 ms)
    (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0)
    -[ holdout_0311_tm ]->+
    cfg_modeC (encL 0 ((fst p + 1) :: snd p)) R0.
Proof.
  intros Hval. simpl.
  set (p1 := bump_enc m0 ms).
  set (p2 := bump_enc (fst p1) (snd p1)).
  pose proof (step_modeC_b11 (encL m0 ms)
    (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0)) as H1.
  pose proof (modeE1_to_modeC ms m0
    (S0 >> S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R0) Hval) as H2.
  fold p1 in H2.
  pose proof (step_modeC_b01_b1011101 (encL (fst p1) (snd p1)) R0) as H3.
  pose proof (modeE1_to_modeC (snd p1) (fst p1)
    (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> R0)
    (ValidKS_bump_enc m0 ms Hval)) as H4.
  fold p2 in H4.
  pose proof (step_modeC_b01_b10101_encL (fst p2) (snd p2) R0) as H5.
  exact (stepPlus_stepPlus_stepPlus H1
    (stepPlus_stepPlus_stepPlus H2
      (stepPlus_stepPlus_stepPlus H3
        (stepPlus_stepPlus_stepPlus H4 H5)))).
Qed.

(* ========================================================================== *)
(* Master Lemma 1: e0_loop_leave1_goodks                                      *)
(* ========================================================================== *)

Lemma prepend11_01_split_last (d : nat) (R0 : side) :
  d >= 1 ->
  prepend11_01 d R0 = prepend11_01 (d - 1) (S1 >> S1 >> S0 >> S1 >> R0).
Proof.
  intros Hd.
  replace d with ((d - 1) + 1) at 1 by lia.
  rewrite prepend11_01_add. reflexivity.
Qed.

Lemma prepend11_01_S_split (d : nat) (R0 : side) :
  prepend11_01 (S d) R0 = prepend11_01 d (S1 >> S1 >> S0 >> S1 >> R0).
Proof.
  replace (S d) with (d + 1) by lia.
  rewrite prepend11_01_add. reflexivity.
Qed.

Lemma e0_loop_leave1_goodks (n : nat) :
  forall (x0 : nat) (xs : list nat) (S0_val : nat) (R0 : side),
    List.length xs = n ->
    S0_val >= 36 ->
    (xs = [] -> 2 * S0_val <= 35 * x0) ->
    (xs <> [] -> x0 >= 2 /\ 2 * S0_val <= 35 * (x0 + 3)) ->
    GoodKS (2 * S0_val + 63 * (x0 + 3)) xs ->
    exists m0 ms,
      (cfg_modeE0_loop (encL x0 xs) R0 -[ holdout_0311_tm ]->+
        cfg_modeC (encL m0 ms) (S1 >> S1 >> S0 >> S1 >> R0)) /\
      ValidKS ms /\
      (ms = [] -> m0 >= 7) /\
      (let p := bump_enc_twice m0 ms in GoodKS S0_val ((fst p + 1) :: snd p)) /\
      ((xs = [] -> x0 >= 10) -> S0_val = 81 ->
        let p1 := bump_enc m0 ms in GoodKS 81 ((fst p1 + 1) :: snd p1)).
Proof.
  induction n as [|n' IH]; intros x0 xs S0_val R0 Hlen HS Hnil Hcons Hgks.
  - destruct xs as [|x1 xs_rest]; [|simpl in Hlen; lia].
    pose proof (Hnil eq_refl) as Hx0.
    assert (Hx0_ge : x0 >= 3) by lia.
    set (d := x0 / 2).
    set (rem := x0 mod 2).
    assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
    assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
    destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      exists d, [3 * d - 3].
      split; [|split; [exact I | split; [discriminate | split]]].
      * assert (Hd_split : x0 = 0 + 2 * d) by lia.
        rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 0 [] R0) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty (d - 1) 1 [0]
          (S1 >> S1 >> S0 >> S1 >> R0) ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        rewrite <- (prepend11_01_split_last d R0 ltac:(lia)) in H4.
        replace (1 + (d - 1)) with d in H4 by lia.
        replace (0 + 3 * (d - 1)) with (3 * d - 3) in H4 by lia.
        exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 (stepPlus_stepStar_stepPlus H3 H4))).
      * unfold bump_enc_twice, bump_enc; cbn [fst snd add_last GoodKS].
        split; [lia | split; [lia | exact I]].
      * intros Hx10 HS81.
        pose proof (Hx10 eq_refl) as Hx10'.
        assert (Hd5 : d >= 5) by lia.
        unfold bump_enc; cbn [fst snd add_last GoodKS].
        split; [lia | split; [lia | exact I]].
    + assert (Hd : d >= 1) by lia.
      exists (4 * d + 3), (@nil nat).
      split; [|split; [exact I | split; [intros _; lia | split]]].
      * assert (Hd_split : x0 = 1 + 2 * d) by lia.
        rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 1 [] R0) as H1.
        pose proof (step_modeE0_loop_b10_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d R0)))))
          with (prepend01 3 (prepend11_01 (S d) R0)) in H2.
        pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nil d 3 (S1 >> S1 >> S0 >> S1 >> R0)) as H4.
        rewrite <- (prepend11_01_S_split d R0) in H4.
        replace (3 + 4 * d) with (4 * d + 3) in H4 by lia.
        exact (stepStar_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 H4))).
      * unfold bump_enc_twice, bump_enc; cbn [fst snd GoodKS].
        split; [lia | exact I].
      * intros _ _.
        unfold bump_enc; cbn [fst snd GoodKS].
        split; [lia | exact I].
  - destruct xs as [|x1 xs_rest]; [simpl in Hlen; lia|].
    assert (Hlen' : List.length xs_rest = n') by (simpl in Hlen; lia).
    destruct (Hcons ltac:(discriminate)) as [Hx0_ge Hx0_bound].
    cbn [GoodKS] in Hgks; destruct Hgks as [Hx1_bound Hgks_rest].
    assert (Hx1_ge : x1 >= 1) by lia.
    pose proof (GoodKS_valid xs_rest (2 * S0_val + 63 * (x0 + 3) + 63 * (x1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    set (d := x0 / 2).
    set (rem := x0 mod 2).
    assert (Hd : d >= 1) by (unfold d; lia).
    assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
    assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
    destruct Hrem as [Heven | Hodd].
    + assert (Hd_split : x0 = 0 + 2 * d) by lia.
      destruct xs_rest as [|x2 rest'].
      * exists (x1 + 4 * d + 3), (@nil nat).
        split; [|split; [exact I | split; [intros _; lia | split]]].
        -- rewrite Hd_split.
           pose proof (e0_loop_drain_pairs d 0 [x1] R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL x1 []) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC [] x1 (prepend01 4 (prepend11_01 d R0)) I) as H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 (x1 + 3) [] (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nil (d - 1) (x1 + 3 + 4) (S1 >> S1 >> S0 >> S1 >> R0)) as H5.
           rewrite <- (prepend11_01_split_last d R0 Hd) in H5.
           replace (x1 + 3 + 4 + 4 * (d - 1)) with (x1 + 4 * d + 3) in H5 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
        -- unfold bump_enc_twice, bump_enc; cbn [fst snd GoodKS].
           split; [lia | exact I].
        -- intros _ _.
           unfold bump_enc; cbn [fst snd GoodKS].
           split; [lia | exact I].
      * assert (Hne_rest : x2 :: rest' <> []) by discriminate.
        exists (x1 + d + 3), (add_last (x2 :: rest') (3 * d)).
        split; [|split; [exact (ValidKS_add_last (x2 :: rest') (3 * d) Hval_rest) |
                 split; [intros Hemp; exfalso; exact (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest Hemp) | split]]].
        -- rewrite Hd_split.
           pose proof (e0_loop_drain_pairs d 0 (x1 :: x2 :: rest') R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL x1 (x2 :: rest')) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC (x2 :: rest') x1 (prepend01 4 (prepend11_01 d R0)) Hval_rest) as H3.
           rewrite (bump_enc_nonempty x1 (x2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 x1 (add_last (x2 :: rest') 3) (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nonempty (d - 1) (x1 + 4) (add_last (x2 :: rest') 3)
             (S1 >> S1 >> S0 >> S1 >> R0)
             (add_last_ne_nil (x2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (x2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           rewrite <- (prepend11_01_split_last d R0 Hd) in H5.
           replace (x1 + 4 + (d - 1)) with (x1 + d + 3) in H5 by lia.
           replace (3 + 3 * (d - 1)) with (3 * d) in H5 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
        -- cbv zeta.
           rewrite (bump_enc_twice_nonempty (x1 + d + 3) (add_last (x2 :: rest') (3 * d))
             (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest)).
           rewrite add_last_add; cbn [fst snd GoodKS].
           split; [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest]; lia.
        -- intros _ HS81; subst S0_val. cbv zeta.
           rewrite (bump_enc_nonempty (x1 + d + 3) (add_last (x2 :: rest') (3 * d))
             (add_last_ne_nil (x2 :: rest') (3 * d) Hne_rest)).
           rewrite add_last_add; cbn [fst snd GoodKS].
           split; [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest]; lia.
    + assert (Hd_split : x0 = 1 + 2 * d) by lia.
      set (S_sub := S0_val + 63 * (d + 2)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (Hx1_ge10 : x1 >= 10) by lia.
      set (sub := bump_enc (x1 - 1) xs_rest).
      assert (Hsub_len : List.length (snd sub) = n').
      { unfold sub, bump_enc; destruct xs_rest; cbn [fst snd]; [exact Hlen' | rewrite add_last_length; exact Hlen']. }
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * S_sub + 63 * (x1 - 1 + 3)) with (2 * S0_val + 63 * (x0 + 3) + 63 * (x1 + 2)) by (unfold S_sub; lia).
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d R0).
      destruct (IH (fst sub) (snd sub) S_sub R_tail Hsub_len HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [Hys_emp [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists (d - 1), (add_last ks_mid (3 * (d - 1))).
      split; [|split; [exact (ValidKS_add_last ks_mid (3 * (d - 1)) Hval_mid) |
               split; [intros Hemp; exfalso; exact (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid Hemp) | split]]].
      * rewrite Hd_split.
        pose proof (e0_loop_drain_pairs d 1 (x1 :: xs_rest) R0) as H1.
        assert (Hx1_eq : x1 = (x1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (x1 - 1) xs_rest (prepend11_01 d R0)) as H2.
        rewrite <- Hx1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC xs_rest (x1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d R0) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty (d - 1) 0 ks_mid
          (S1 >> S1 >> S0 >> S1 >> R0) Hne_mid Hval_mid) as H6.
        rewrite <- (prepend11_01_split_last d R0 Hd) in H6.
        replace (0 + (d - 1)) with (d - 1) in H6 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepPlus_stepPlus Hstep_sub
                  (stepPlus_stepStar_stepPlus H5 H6)))))).
      * cbv zeta.
        rewrite (bump_enc_twice_nonempty (d - 1) (add_last ks_mid (3 * (d - 1)))
          (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid)).
        rewrite add_last_add; cbn [fst snd].
        replace (d - 1 + 1) with d by lia.
        cbn [GoodKS].
        split; [unfold S_sub; lia |].
        replace (S0_val + 63 * (d + 2)) with S_sub by reflexivity.
        exact (GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 6) Hgks_sub).
      * intros _ HS81; subst S0_val. cbv zeta.
        rewrite (bump_enc_nonempty (d - 1) (add_last ks_mid (3 * (d - 1)))
          (add_last_ne_nil ks_mid (3 * (d - 1)) Hne_mid)).
        rewrite add_last_add; cbn [fst snd].
        replace (d - 1 + 1) with d by lia.
        cbn [GoodKS].
        split; [unfold S_sub; lia |].
        replace (81 + 63 * (d + 2)) with S_sub by reflexivity.
        exact (GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 3) Hgks_sub).
Qed.

(* ========================================================================== *)
(* Master Lemma 2a: k0 >= 1 Transition (step_k0_pos)                          *)
(* ========================================================================== *)

Lemma step_k0_pos (k0 : nat) (ks : list nat) :
  k0 >= 1 ->
  InvNil k0 ks ->
  exists k0' ks',
    (cfg_modeC (encL k0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros Hk0 Hinv.
  set (x0 := k0 - 1).
  assert (Hk0_eq : k0 = x0 + 1) by lia.
  assert (Hto_e0 : cfg_modeC (encL k0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeE0_loop (encL x0 ks) (const S0)).
  { rewrite Hk0_eq.
    exact (stepPlus_stepPlus_stepPlus (step_modeC_nil (encL (x0 + 1) ks)) (step_modeE0_first_b10_encL x0 ks)). }
  set (d := x0 / 2).
  set (rem := x0 mod 2).
  assert (Hdiv : rem + 2 * d = x0) by (unfold d, rem; lia).
  assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
  destruct Hinv as [[-> Hk5] | [Hne Hgks]].
  - destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      assert (Hx_split : x0 = 0 + 2 * d) by lia.
      exists (d + 1), [3 * d].
      split.
      * rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 0 [] (const S0)) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d (const S0))) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d (const S0))) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty d 1 [0] (const S0) ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        replace (1 + d) with (d + 1) in H4 by lia.
        replace (0 + 3 * d) with (3 * d) in H4 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepStar_stepPlus H3 H4)))).
      * right; split; [discriminate |].
        destruct (Nat.eqb_spec (d + 1) 1); [lia |].
        cbn [GoodKS]; split; [lia | exact I].
    + assert (Hd : d >= 2) by lia.
      assert (Hx_split : x0 = 1 + 2 * d) by lia.
      exists (4 * d + 7), (@nil nat).
      split; [|left; split; [reflexivity | lia]].
      rewrite Hx_split in Hto_e0.
      pose proof (e0_loop_drain_pairs d 1 [] (const S0)) as H1.
      pose proof (step_modeE0_loop_b10_base (prepend11_01 d (const S0))) as H2.
      change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0))))))
        with (prepend01 3 (prepend11_01 (S d) (const S0))) in H2.
      pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) (const S0))) as H3; simpl in H3.
      pose proof (modeC_consume_11_01_nil (S d) 3 (const S0)) as H4.
      replace (3 + 4 * S d) with (4 * d + 7) in H4 by lia.
      exact (stepPlus_stepPlus_stepPlus Hto_e0
        (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 H4)))).
  - destruct ks as [|k1 ks_rest]; [congruence |].
    set (S_in := if Nat.eqb k0 1 then 81 else 36 * (k0 + 2)).
    fold S_in in Hgks.
    assert (HS_in_ge : S_in >= 81).
    { unfold S_in; destruct (Nat.eqb_spec k0 1); lia. }
    cbn [GoodKS] in Hgks; destruct Hgks as [Hk1_bound Hgks_rest].
    assert (Hk1_ge : k1 >= 1) by lia.
    pose proof (GoodKS_valid ks_rest (S_in + 63 * (k1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    destruct Hrem as [Heven | Hodd].
    + assert (Hx_split : x0 = 0 + 2 * d) by lia.
      destruct ks_rest as [|k2 rest'].
      * exists (k1 + 4 * d + 7), (@nil nat).
        split; [|left; split; [reflexivity | lia]].
        rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 0 [k1] (const S0)) as H1.
        pose proof (step_modeE0_loop_b011_10 (encL k1 []) (prepend11_01 d (const S0))) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0)))))
          with (prepend01 4 (prepend11_01 d (const S0))) in H2.
        pose proof (modeE1_to_modeC [] k1 (prepend01 4 (prepend11_01 d (const S0))) I) as H3; simpl in H3.
        pose proof (modeC_prepend01_star 4 (k1 + 3) [] (prepend11_01 d (const S0))) as H4.
        pose proof (modeC_consume_11_01_nil d (k1 + 3 + 4) (const S0)) as H5.
        replace (k1 + 3 + 4 + 4 * d) with (k1 + 4 * d + 7) in H5 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5))))).
      * assert (Hne_rest : k2 :: rest' <> []) by discriminate.
        exists (k1 + d + 4), (add_last (k2 :: rest') (3 * d + 3)).
        split.
        -- rewrite Hx_split in Hto_e0.
           pose proof (e0_loop_drain_pairs d 0 (k1 :: k2 :: rest') (const S0)) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL k1 (k2 :: rest')) (prepend11_01 d (const S0))) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d (const S0)))))
             with (prepend01 4 (prepend11_01 d (const S0))) in H2.
           pose proof (modeE1_to_modeC (k2 :: rest') k1 (prepend01 4 (prepend11_01 d (const S0))) Hval_rest) as H3.
           rewrite (bump_enc_nonempty k1 (k2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 k1 (add_last (k2 :: rest') 3) (prepend11_01 d (const S0))) as H4.
           pose proof (modeC_consume_11_01_nonempty d (k1 + 4) (add_last (k2 :: rest') 3) (const S0)
             (add_last_ne_nil (k2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (k2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           replace (k1 + 4 + d) with (k1 + d + 4) in H5 by lia.
           replace (3 + 3 * d) with (3 * d + 3) in H5 by lia.
           exact (stepPlus_stepPlus_stepPlus Hto_e0
             (stepStar_stepPlus_stepPlus H1
               (stepPlus_stepPlus_stepPlus H2
                 (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5))))).
        -- right; split; [exact (add_last_ne_nil (k2 :: rest') (3 * d + 3) Hne_rest) |].
           destruct (Nat.eqb_spec (k1 + d + 4) 1); [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest].
           unfold S_in; destruct (Nat.eqb_spec k0 1); lia.
    + assert (Hx_split : x0 = 1 + 2 * d) by lia.
      assert (Hk0_ne1 : k0 <> 1) by lia.
      assert (HS_in_eq : S_in = 72 * (d + 2)).
      { unfold S_in; destruct (Nat.eqb_spec k0 1); lia. }
      set (S_sub := 36 * (d + 2)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (Hk1_ge3 : k1 >= 3) by lia.
      set (sub := bump_enc (k1 - 1) ks_rest).
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * S_sub + 63 * (k1 - 1 + 3)) with (S_in + 63 * (k1 + 2)) by (unfold S_sub; lia).
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d (const S0)).
      destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) S_sub R_tail
        eq_refl HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [_ [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists d, (add_last ks_mid (3 * d)).
      split.
      * rewrite Hx_split in Hto_e0.
        pose proof (e0_loop_drain_pairs d 1 (k1 :: ks_rest) (const S0)) as H1.
        assert (Hk1_eq : k1 = (k1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (k1 - 1) ks_rest (prepend11_01 d (const S0))) as H2.
        rewrite <- Hk1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC ks_rest (k1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d (const S0)) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty d 0 ks_mid (const S0) Hne_mid Hval_mid) as H6.
        replace (0 + d) with d in H6 by lia.
        exact (stepPlus_stepPlus_stepPlus Hto_e0
          (stepStar_stepPlus_stepPlus H1
            (stepPlus_stepPlus_stepPlus H2
              (stepPlus_stepPlus_stepPlus H3
                (stepPlus_stepPlus_stepPlus H4
                  (stepPlus_stepPlus_stepPlus Hstep_sub
                    (stepPlus_stepStar_stepPlus H5 H6))))))).
      * right; split; [exact (add_last_ne_nil ks_mid (3 * d) Hne_mid) |].
        apply GoodKS_add_last.
        eapply GoodKS_mono; [|exact Hgks_sub].
        unfold S_sub; destruct (Nat.eqb_spec d 1); lia.
Qed.

(* ========================================================================== *)
(* Master Lemma 2b: Drain at R = 01 >> 01 >> const S0                         *)
(* ========================================================================== *)

Lemma e0_loop_drain_plus2 (w0 : nat) (ws : list nat) (S_w : nat) :
  (ws = [] -> w0 >= 4) ->
  36 <= S_w + 54 * (w0 / 2) ->
  GoodKS (S_w + 63 * (w0 + 3)) ws ->
  exists k0' ks',
    (cfg_modeE0_loop (encL w0 ws) (S0 >> S1 >> S0 >> S1 >> const S0)
      -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros Hempty Hsw Hgks.
  set (R0 := S0 >> S1 >> S0 >> S1 >> const S0).
  assert (HR0 : R0 = prepend01 2 (const S0)) by reflexivity.
  set (d := w0 / 2).
  set (rem := w0 mod 2).
  assert (Hdiv : rem + 2 * d = w0) by (unfold d, rem; lia).
  assert (Hrem : rem = 0 \/ rem = 1) by (unfold rem; lia).
  destruct ws as [|w1 ws_rest].
  - pose proof (Hempty eq_refl) as Hw4.
    destruct Hrem as [Heven | Hodd].
    + assert (Hd : d >= 2) by lia.
      assert (Hw_split : w0 = 0 + 2 * d) by lia.
      exists (d + 3), [3 * d].
      split.
      * rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 0 [] R0) as H1.
        pose proof (step_modeE0_loop_base (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in H2.
        pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 d R0)) as H3; simpl in H3.
        pose proof (modeC_consume_11_01_nonempty d 1 [0] R0 ltac:(discriminate) I) as H4.
        cbn [add_last] in H4.
        replace (0 + 3 * d) with (3 * d) in H4 by lia.
        rewrite HR0 in H4.
        pose proof (modeC_prepend01_star 2 (1 + d) [3 * d] (const S0)) as H5.
        replace (1 + d + 2) with (d + 3) in H5 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 H5)))).
      * right; split; [discriminate |].
        destruct (Nat.eqb_spec (d + 3) 1); [lia |].
        cbn [GoodKS]; split; [lia | exact I].
    + assert (Hd : d >= 1) by lia.
      assert (Hw_split : w0 = 1 + 2 * d) by lia.
      exists (4 * d + 9), (@nil nat).
      split; [|left; split; [reflexivity | lia]].
      rewrite Hw_split.
      pose proof (e0_loop_drain_pairs d 1 [] R0) as H1.
      pose proof (step_modeE0_loop_b10_base (prepend11_01 d R0)) as H2.
      change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S1 >> (S0 >> S1 >> prepend11_01 d R0)))))
        with (prepend01 3 (prepend11_01 (S d) R0)) in H2.
      pose proof (modeC_prepend01_star 3 0 [] (prepend11_01 (S d) R0)) as H3; simpl in H3.
      pose proof (modeC_consume_11_01_nil (S d) 3 R0) as H4.
      rewrite HR0 in H4.
      pose proof (modeC_prepend01_star 2 (3 + 4 * S d) [] (const S0)) as H5.
      replace (3 + 4 * S d + 2) with (4 * d + 9) in H5 by lia.
      exact (stepStar_stepPlus_stepPlus H1
        (stepPlus_stepStar_stepPlus H2 (stepStar_trans H3 (stepStar_trans H4 H5)))).
  - cbn [GoodKS] in Hgks; destruct Hgks as [Hw1_bound Hgks_rest].
    assert (Hw1_ge : w1 >= 4) by (unfold d in Hsw; lia).
    pose proof (GoodKS_valid ws_rest (S_w + 63 * (w0 + 3) + 63 * (w1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
    destruct Hrem as [Heven | Hodd].
    + assert (Hw_split : w0 = 0 + 2 * d) by lia.
      destruct ws_rest as [|w2 rest'].
      * exists (w1 + 4 * d + 9), (@nil nat).
        split; [|left; split; [reflexivity | lia]].
        rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 0 [w1] R0) as H1.
        pose proof (step_modeE0_loop_b011_10 (encL w1 []) (prepend11_01 d R0)) as H2.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
          with (prepend01 4 (prepend11_01 d R0)) in H2.
        pose proof (modeE1_to_modeC [] w1 (prepend01 4 (prepend11_01 d R0)) I) as H3; simpl in H3.
        pose proof (modeC_prepend01_star 4 (w1 + 3) [] (prepend11_01 d R0)) as H4.
        pose proof (modeC_consume_11_01_nil d (w1 + 3 + 4) R0) as H5.
        rewrite HR0 in H5.
        pose proof (modeC_prepend01_star 2 (w1 + 3 + 4 + 4 * d) [] (const S0)) as H6.
        replace (w1 + 3 + 4 + 4 * d + 2) with (w1 + 4 * d + 9) in H6 by lia.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 (stepStar_trans H5 H6))))).
      * assert (Hne_rest : w2 :: rest' <> []) by discriminate.
        exists (w1 + d + 6), (add_last (w2 :: rest') (3 * d + 3)).
        split.
        -- rewrite Hw_split.
           pose proof (e0_loop_drain_pairs d 0 (w1 :: w2 :: rest') R0) as H1.
           pose proof (step_modeE0_loop_b011_10 (encL w1 (w2 :: rest')) (prepend11_01 d R0)) as H2.
           change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> prepend11_01 d R0))))
             with (prepend01 4 (prepend11_01 d R0)) in H2.
           pose proof (modeE1_to_modeC (w2 :: rest') w1 (prepend01 4 (prepend11_01 d R0)) Hval_rest) as H3.
           rewrite (bump_enc_nonempty w1 (w2 :: rest') Hne_rest) in H3; simpl in H3.
           pose proof (modeC_prepend01_star 4 w1 (add_last (w2 :: rest') 3) (prepend11_01 d R0)) as H4.
           pose proof (modeC_consume_11_01_nonempty d (w1 + 4) (add_last (w2 :: rest') 3) R0
             (add_last_ne_nil (w2 :: rest') 3 Hne_rest)
             (ValidKS_add_last (w2 :: rest') 3 Hval_rest)) as H5.
           rewrite add_last_add in H5.
           replace (3 + 3 * d) with (3 * d + 3) in H5 by lia.
           rewrite HR0 in H5.
           pose proof (modeC_prepend01_star 2 (w1 + 4 + d) (add_last (w2 :: rest') (3 * d + 3)) (const S0)) as H6.
           replace (w1 + 4 + d + 2) with (w1 + d + 6) in H6 by lia.
           exact (stepStar_stepPlus_stepPlus H1
             (stepPlus_stepPlus_stepPlus H2
               (stepPlus_stepStar_stepPlus H3 (stepStar_trans H4 (stepStar_trans H5 H6))))).
        -- right; split; [exact (add_last_ne_nil (w2 :: rest') (3 * d + 3) Hne_rest) |].
           destruct (Nat.eqb_spec (w1 + d + 6) 1); [lia |].
           apply GoodKS_add_last.
           eapply GoodKS_mono; [|exact Hgks_rest].
           unfold d in Hsw; lia.
    + assert (Hw_split : w0 = 1 + 2 * d) by lia.
      set (S_sub := 36 * (d + 4)).
      assert (HS_sub : S_sub >= 36) by (unfold S_sub; lia).
      assert (H2S_le : 2 * S_sub <= S_w + 63 * (w0 + 3)) by (unfold S_sub; unfold d in Hsw; lia).
      set (sub := bump_enc (w1 - 1) ws_rest).
      assert (Hsub_nil : snd sub = [] -> 2 * S_sub <= 35 * fst sub).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [intros _; unfold S_sub; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * S_sub <= 35 * (fst sub + 3)).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; unfold S_sub; lia]. }
      assert (Hsub_gks : GoodKS (2 * S_sub + 63 * (fst sub + 3)) (snd sub)).
      { unfold sub, bump_enc; destruct ws_rest as [|y ys]; cbn [fst snd]; [exact I |].
        apply GoodKS_add_last.
        eapply GoodKS_mono; [|exact Hgks_rest]; lia. }
      set (R_tail := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> prepend11_01 d R0).
      destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) S_sub R_tail
        eq_refl HS_sub Hsub_nil Hsub_cons Hsub_gks)
        as [y0 [ys [Hstep_sub [Hval_ys [_ [Hgks_sub _]]]]]].
      set (py := bump_enc_twice y0 ys).
      set (ks_mid := (fst py + 1) :: snd py).
      assert (Hne_mid : ks_mid <> []) by discriminate.
      assert (Hval_mid : ValidKS ks_mid) by (apply (GoodKS_succ_valid S_sub (fst py) (snd py)); exact Hgks_sub).
      exists (d + 2), (add_last ks_mid (3 * d)).
      split.
      * rewrite Hw_split.
        pose proof (e0_loop_drain_pairs d 1 (w1 :: ws_rest) R0) as H1.
        assert (Hw1_eq : w1 = (w1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (w1 - 1) ws_rest (prepend11_01 d R0)) as H2.
        rewrite <- Hw1_eq in H2.
        fold R_tail in H2.
        pose proof (modeE1_to_modeC ws_rest (w1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_tail) Hval_rest) as H3.
        fold sub in H3.
        pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) R_tail) as H4.
        pose proof (unwrap_11_01_1011101_step y0 ys (prepend11_01 d R0) Hval_ys) as H5.
        fold py in H5; fold ks_mid in H5.
        pose proof (modeC_consume_11_01_nonempty d 0 ks_mid R0 Hne_mid Hval_mid) as H6.
        replace (0 + d) with d in H6 by lia.
        rewrite HR0 in H6.
        pose proof (modeC_prepend01_star 2 d (add_last ks_mid (3 * d)) (const S0)) as H7.
        exact (stepStar_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3
              (stepPlus_stepPlus_stepPlus H4
                (stepPlus_stepPlus_stepPlus Hstep_sub
                  (stepPlus_stepStar_stepPlus H5 (stepStar_trans H6 H7))))))).
      * right; split; [exact (add_last_ne_nil ks_mid (3 * d) Hne_mid) |].
        destruct (Nat.eqb_spec (d + 2) 1); [lia |].
        replace (36 * (d + 2 + 2)) with S_sub by (unfold S_sub; lia).
        exact (GoodKS_add_last ks_mid S_sub (3 * d) Hgks_sub).
Qed.

(* ========================================================================== *)
(* k0 = 0 Transition (Cases 0a, 0b, 0c)                                       *)
(* ========================================================================== *)

Lemma step_b01_b101_nil_to_e0_loop (p0 : nat) (ps : list nat) :
  ValidKS ps ->
  let w := bump_enc p0 ps in
  cfg_modeC (encL p0 ps) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)
    -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL (fst w) (snd w)) (S0 >> S1 >> S0 >> S1 >> const S0).
Proof.
  intros Hval; cbv zeta.
  set (w := bump_enc p0 ps).
  pose proof (step_modeC_b01_b101_nil (encL p0 ps)) as H1.
  pose proof (modeE1_to_modeC ps p0
    (S0 >> S1 >> S0 >> S0 >> S0 >> (S0 >> S1 >> (S0 >> S1 >> const S0))) Hval) as H2.
  fold w in H2.
  pose proof (step_modeC_b01_b000 (encL (fst w) (snd w)) (S0 >> S1 >> S0 >> S1 >> const S0)) as H3.
  exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 H3)).
Qed.

Lemma step_k0_zero (ks : list nat) :
  InvNil 0 ks ->
  exists k0' ks',
    (cfg_modeC (encL 0 ks) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL k0' ks') (const S0)) /\
    InvNil k0' ks'.
Proof.
  intros [[_ Hk5] | [Hne Hgks]]; [lia |].
  cbn [Nat.eqb] in Hgks.
  destruct ks as [|k1 ks_rest]; [congruence |].
  cbn [GoodKS] in Hgks; destruct Hgks as [Hk1_bound Hgks_rest].
  assert (Hk1_ge : k1 >= 1) by lia.
  replace (36 * (0 + 2)) with 72 in Hgks_rest by lia.
  pose proof (GoodKS_valid ks_rest (72 + 63 * (k1 + 2)) ltac:(lia) Hgks_rest) as Hval_rest.
  set (sub := bump_enc (k1 - 1) ks_rest).
  assert (Hto_sub : cfg_modeC (encL 0 (k1 :: ks_rest)) (const S0) -[ holdout_0311_tm ]->+
    cfg_modeE0_loop (encL (fst sub) (snd sub)) (S1 >> S0 >> S1 >> const S0)).
  { assert (Hk1_eq : k1 = (k1 - 1) + 1) by lia.
    pose proof (step_modeC_nil (encL 0 (k1 :: ks_rest))) as H1.
    pose proof (step_modeE0_first_b011_10_b10_encL (k1 - 1) ks_rest) as H2.
    rewrite <- Hk1_eq in H2.
    pose proof (modeE1_to_modeC ks_rest (k1 - 1)
      (S0 >> S1 >> S0 >> S0 >> S0 >> (S1 >> S0 >> S1 >> const S0)) Hval_rest) as H3.
    fold sub in H3.
    pose proof (step_modeC_b01_b000 (encL (fst sub) (snd sub)) (S1 >> S0 >> S1 >> const S0)) as H4.
    exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 (stepPlus_stepPlus_stepPlus H3 H4))). }
  assert (H0a_dec : (ks_rest = [] \/ k1 >= 3) \/ (ks_rest <> [] /\ k1 < 3)).
  { destruct ks_rest as [|y ys]; [left; left; reflexivity |].
    destruct (Nat.leb_spec 3 k1); [left; right; lia | right; split; [discriminate | lia]]. }
  destruct H0a_dec as [H0a | [Hne_rest Hk1_lt3]].
  - (* Case 0a *)
    assert (Hsub_nil : snd sub = [] -> 2 * 36 <= 35 * fst sub).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [intros _; lia |].
      intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
    assert (Hsub_cons : snd sub <> [] -> fst sub >= 2 /\ 2 * 36 <= 35 * (fst sub + 3)).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [congruence |].
      destruct H0a as [Hemp | Hk3]; [congruence | intros _; lia]. }
    assert (Hsub_gks : GoodKS (2 * 36 + 63 * (fst sub + 3)) (snd sub)).
    { unfold sub, bump_enc; destruct ks_rest as [|y ys]; cbn [fst snd]; [exact I |].
      replace (2 * 36 + 63 * (k1 - 1 + 3)) with (72 + 63 * (k1 + 2)) by lia.
      exact (GoodKS_add_last (y :: ys) _ 3 Hgks_rest). }
    destruct (e0_loop_leave1_goodks (List.length (snd sub)) (fst sub) (snd sub) 36
      (S1 >> S0 >> S1 >> const S0) eq_refl ltac:(lia) Hsub_nil Hsub_cons Hsub_gks)
      as [m0 [ms [Hstep_l1 [Hval_ms [Hms_emp [Hgks_w _]]]]]].
    set (p1 := bump_enc m0 ms).
    set (w := bump_enc_twice m0 ms).
    assert (Hw_eq : w = bump_enc (fst p1) (snd p1)) by reflexivity.
    assert (Hc11 : cfg_modeC (encL m0 ms)
      (S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> S1 >> const S0)
      -[ holdout_0311_tm ]->+
      cfg_modeC (encL (fst p1) (snd p1)) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)).
    { exact (stepPlus_stepPlus_stepPlus
        (step_modeC_b11 (encL m0 ms) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0))
        (modeE1_to_modeC ms m0 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0) Hval_ms)). }
    pose proof (step_b01_b101_nil_to_e0_loop (fst p1) (snd p1) (ValidKS_bump_enc m0 ms Hval_ms)) as Hto_w.
    cbv zeta in Hto_w; rewrite <- Hw_eq in Hto_w.
    assert (Hw_empty : snd w = [] -> fst w >= 4).
    { destruct ms as [|u us].
      - intros _; unfold w, bump_enc_twice, bump_enc; cbn [fst snd]; lia.
      - intros Hemp; unfold w in Hemp;
        rewrite (bump_enc_twice_nonempty m0 (u :: us) ltac:(discriminate)) in Hemp; cbn [snd] in Hemp;
        exfalso; exact (add_last_ne_nil (u :: us) 6 ltac:(discriminate) Hemp). }
    assert (Hgks_ws : GoodKS (36 + 63 * (fst w + 3)) (snd w)).
    { cbv zeta in Hgks_w; fold w in Hgks_w; cbn [GoodKS] in Hgks_w.
      destruct Hgks_w as [_ H2].
      replace (36 + 63 * (fst w + 3)) with (36 + 63 * (fst w + 1 + 2)) by lia.
      exact H2. }
    destruct (e0_loop_drain_plus2 (fst w) (snd w) 36 Hw_empty ltac:(lia) Hgks_ws)
      as [k0' [ks' [Hdrain Hinv']]].
    exists k0', ks'; split; [|exact Hinv'].
    exact (stepPlus_stepPlus_stepPlus Hto_sub
      (stepPlus_stepPlus_stepPlus Hstep_l1
        (stepPlus_stepPlus_stepPlus Hc11
          (stepPlus_stepPlus_stepPlus Hto_w Hdrain)))).
  - destruct ks_rest as [|k2 ks_tail]; [congruence |].
    assert (Hk1_cases : k1 = 1 \/ k1 = 2) by lia.
    destruct Hk1_cases as [-> | ->].
    + (* Case 0b: k1 = 1 *)
      assert (Hsub_eq : sub = (0, add_last (k2 :: ks_tail) 3)) by reflexivity.
      replace (72 + 63 * (1 + 2)) with 261 in Hgks_rest by lia.
      pose proof (GoodKS_add_last (k2 :: ks_tail) 261 3 Hgks_rest) as Hgks_sub.
      destruct (add_last (k2 :: ks_tail) 3) as [|x1 xs_rest] eqn:Hal;
        [exfalso; exact (add_last_ne_nil (k2 :: ks_tail) 3 ltac:(discriminate) Hal) |].
      cbn [GoodKS] in Hgks_sub; destruct Hgks_sub as [Hx1_bound Hgks_xs].
      assert (Hx1_ge6 : x1 >= 6) by lia.
      pose proof (GoodKS_valid xs_rest (261 + 63 * (x1 + 2)) ltac:(lia) Hgks_xs) as Hval_xs.
      set (xb := bump_enc x1 xs_rest).
      set (p1 := (fst xb + 3, snd xb)).
      set (w := bump_enc (fst p1) (snd p1)).
      assert (Hstep_0b : cfg_modeE0_loop (encL 0 (x1 :: xs_rest)) (S1 >> S0 >> S1 >> const S0)
        -[ holdout_0311_tm ]->+
        cfg_modeC (encL (fst p1) (snd p1)) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)).
      { pose proof (step_modeE0_loop_b011_10 (encL x1 xs_rest) (S1 >> S0 >> S1 >> const S0)) as H1.
        change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> (S1 >> S0 >> S1 >> const S0)))))
          with (prepend01 3 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) in H1.
        pose proof (modeE1_to_modeC xs_rest x1
          (prepend01 3 (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) Hval_xs) as H2.
        fold xb in H2.
        pose proof (modeC_prepend01_star 3 (fst xb) (snd xb) (S0 >> S1 >> S1 >> S0 >> S1 >> const S0)) as H3.
        exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepStar_stepPlus H2 H3)). }
      assert (Hval_p1 : ValidKS (snd p1)) by (unfold p1; exact (ValidKS_bump_enc x1 xs_rest Hval_xs)).
      pose proof (step_b01_b101_nil_to_e0_loop (fst p1) (snd p1) Hval_p1) as Hto_w.
      cbv zeta in Hto_w; fold w in Hto_w.
      assert (Hw1_ge9 : fst w >= 9).
      { destruct xs_rest as [|y ys].
        - unfold w, p1, xb, bump_enc; cbn [fst snd]; lia.
        - assert (Hw_cons : w = (x1 + 3, add_last (y :: ys) 6)).
          { unfold w, p1, xb; cbn [fst snd bump_enc].
            rewrite (bump_enc_nonempty (x1 + 3) (add_last (y :: ys) 3)
              (add_last_ne_nil (y :: ys) 3 ltac:(discriminate))).
            rewrite add_last_add; reflexivity. }
          rewrite Hw_cons; cbn [fst]; lia. }
      assert (Hw_empty : snd w = [] -> fst w >= 4) by (intros _; lia).
      assert (Hsw9 : 36 <= 9 + 54 * (fst w / 2)) by lia.
      assert (Hgks_ws : GoodKS (9 + 63 * (fst w + 3)) (snd w)).
      { destruct xs_rest as [|y ys].
        - unfold w, p1, xb, bump_enc; cbn [fst snd GoodKS]; exact I.
        - assert (Hw_cons : w = (x1 + 3, add_last (y :: ys) 6)).
          { unfold w, p1, xb; cbn [fst snd bump_enc].
            rewrite (bump_enc_nonempty (x1 + 3) (add_last (y :: ys) 3)
              (add_last_ne_nil (y :: ys) 3 ltac:(discriminate))).
            rewrite add_last_add; reflexivity. }
          rewrite Hw_cons; cbn [fst snd].
          replace (9 + 63 * (x1 + 3 + 3)) with (261 + 63 * (x1 + 2)) by lia.
          exact (GoodKS_add_last (y :: ys) _ 6 Hgks_xs). }
      destruct (e0_loop_drain_plus2 (fst w) (snd w) 9 Hw_empty Hsw9 Hgks_ws)
        as [k0' [ks' [Hdrain Hinv']]].
      rewrite Hsub_eq in Hto_sub; cbn [fst snd] in Hto_sub.
      exists k0', ks'; split; [|exact Hinv'].
      exact (stepPlus_stepPlus_stepPlus Hto_sub
        (stepPlus_stepPlus_stepPlus Hstep_0b
          (stepPlus_stepPlus_stepPlus Hto_w Hdrain))).
    + (* Case 0c: k1 = 2 *)
      assert (Hsub_eq : sub = (1, add_last (k2 :: ks_tail) 3)) by reflexivity.
      replace (72 + 63 * (2 + 2)) with 324 in Hgks_rest by lia.
      pose proof (GoodKS_add_last (k2 :: ks_tail) 324 3 Hgks_rest) as Hgks_sub.
      destruct (add_last (k2 :: ks_tail) 3) as [|x1 xs_rest] eqn:Hal;
        [exfalso; exact (add_last_ne_nil (k2 :: ks_tail) 3 ltac:(discriminate) Hal) |].
      cbn [GoodKS] in Hgks_sub; destruct Hgks_sub as [Hx1_bound Hgks_xs].
      assert (Hx1_ge8 : x1 >= 8) by lia.
      pose proof (GoodKS_valid xs_rest (324 + 63 * (x1 + 2)) ltac:(lia) Hgks_xs) as Hval_xs.
      set (sub2 := bump_enc (x1 - 1) xs_rest).
      set (R_101 := S1 >> S0 >> S1 >> const S0).
      set (R_1011101_101 := S1 >> S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> R_101).
      assert (Hstep1 : cfg_modeE0_loop (encL 1 (x1 :: xs_rest)) R_101 -[ holdout_0311_tm ]->+
        cfg_modeE0_loop (encL (fst sub2) (snd sub2)) R_1011101_101).
      { assert (Hx1_eq : x1 = (x1 - 1) + 1) by lia.
        pose proof (step_modeE0_loop_b10_b011_10_b10_encL (x1 - 1) xs_rest R_101) as H1.
        rewrite <- Hx1_eq in H1.
        fold R_1011101_101 in H1.
        pose proof (modeE1_to_modeC xs_rest (x1 - 1)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_1011101_101) Hval_xs) as H2.
        fold sub2 in H2.
        pose proof (step_modeC_b01_b000 (encL (fst sub2) (snd sub2)) R_1011101_101) as H3.
        exact (stepPlus_stepPlus_stepPlus H1 (stepPlus_stepPlus_stepPlus H2 H3)). }
      assert (Hsub2_nil : snd sub2 = [] -> 2 * 162 <= 35 * fst sub2).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [intros _; lia |].
        intros Hemp; exfalso; exact (add_last_ne_nil (y :: ys) 3 ltac:(discriminate) Hemp). }
      assert (Hsub2_cons : snd sub2 <> [] -> fst sub2 >= 2 /\ 2 * 162 <= 35 * (fst sub2 + 3)).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [congruence | intros _; lia]. }
      assert (Hsub2_gks : GoodKS (2 * 162 + 63 * (fst sub2 + 3)) (snd sub2)).
      { unfold sub2, bump_enc; destruct xs_rest as [|y ys]; cbn [fst snd]; [exact I |].
        replace (2 * 162 + 63 * (x1 - 1 + 3)) with (324 + 63 * (x1 + 2)) by lia.
        exact (GoodKS_add_last (y :: ys) _ 3 Hgks_xs). }
      destruct (e0_loop_leave1_goodks (List.length (snd sub2)) (fst sub2) (snd sub2) 162 R_1011101_101
        eq_refl ltac:(lia) Hsub2_nil Hsub2_cons Hsub2_gks)
        as [y0 [ys [Hstep_l2 [Hval_ys [Hys_emp [Hgks_z _]]]]]].
      pose proof (unwrap_11_01_1011101_step y0 ys R_101 Hval_ys) as Hunwrap2.
      cbv zeta in Hunwrap2, Hgks_z.
      set (pz := bump_enc_twice y0 ys) in *.
      set (z1 := fst pz + 1) in *.
      set (zs := snd pz) in *.
      cbn [GoodKS] in Hgks_z; destruct Hgks_z as [Hz1_bound Hgks_zs].
      assert (Hz1_ge3 : z1 >= 3) by lia.
      assert (Hzs_emp_z1 : zs = [] -> z1 >= 14).
      { destruct ys as [|u us].
        - pose proof (Hys_emp eq_refl) as Hy7.
          intros _; unfold z1, pz, bump_enc_twice, bump_enc; cbn [fst snd]; lia.
        - intros Hemp; unfold zs, pz in Hemp.
          rewrite (bump_enc_twice_nonempty y0 (u :: us) ltac:(discriminate)) in Hemp; cbn [snd] in Hemp.
          exfalso; exact (add_last_ne_nil (u :: us) 6 ltac:(discriminate) Hemp). }
      pose proof (GoodKS_valid zs (162 + 63 * (z1 + 2)) ltac:(lia) Hgks_zs) as Hval_zs.
      set (zb := bump_enc (z1 - 1) zs).
      set (w := bump_enc (fst zb) (snd zb)).
      set (R_0000101 := S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).
      set (R_101_01_01 := S1 >> S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))).
      assert (Hstep34 : cfg_modeC (encL 0 (z1 :: zs)) R_101 -[ holdout_0311_tm ]->+
        cfg_modeE0_loop (encL (fst w) (snd w)) R_101_01_01).
      { assert (Hz1_eq : z1 = (z1 - 1) + 1) by lia.
        pose proof (step_modeC_b01110_b10_b101_nil_encL (z1 - 1) zs) as HA.
        rewrite <- Hz1_eq in HA.
        fold R_101 in HA; fold R_0000101 in HA.
        pose proof (modeE1_to_modeC zs (z1 - 1)
          (S0 >> S1 >> S1 >> S0 >> S1 >> S0 >> S1 >> R_0000101) Hval_zs) as HA2.
        fold zb in HA2.
        pose proof (step_modeC_b01_b10101_encL (fst zb) (snd zb) R_0000101) as HA3.
        pose proof (step_modeC_b01110_b10_b0000101_encL (fst zb) (snd zb) (const S0)) as HB.
        fold R_0000101 in HB; fold R_101_01_01 in HB.
        pose proof (modeE1_to_modeC (snd zb) (fst zb)
          (S0 >> S1 >> S0 >> S0 >> S0 >> R_101_01_01)
          (ValidKS_bump_enc (z1 - 1) zs Hval_zs)) as HB2.
        fold w in HB2.
        pose proof (step_modeC_b01_b000 (encL (fst w) (snd w)) R_101_01_01) as HB3.
        exact (stepPlus_stepPlus_stepPlus HA
          (stepPlus_stepPlus_stepPlus HA2
            (stepPlus_stepPlus_stepPlus HA3
              (stepPlus_stepPlus_stepPlus HB
                (stepPlus_stepPlus_stepPlus HB2 HB3))))). }
      assert (Hw_def : w = bump_enc_twice (z1 - 1) zs) by reflexivity.
      assert (Hw_nil : snd w = [] -> 2 * 81 <= 35 * fst w).
      { destruct zs as [|y ys'] eqn:Hzs.
        - pose proof (Hzs_emp_z1 eq_refl) as Hz14.
          assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [fst snd]; intros _; lia.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [snd]; intros Hemp;
          exfalso; exact (add_last_ne_nil (y :: ys') 6 ltac:(discriminate) Hemp). }
      assert (Hw_ge10 : snd w = [] -> fst w >= 10).
      { destruct zs as [|y ys'] eqn:Hzs.
        - pose proof (Hzs_emp_z1 eq_refl) as Hz14.
          assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [fst snd]; intros _; lia.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [snd]; intros Hemp;
          exfalso; exact (add_last_ne_nil (y :: ys') 6 ltac:(discriminate) Hemp). }
      assert (Hw_cons : snd w <> [] -> fst w >= 2 /\ 2 * 81 <= 35 * (fst w + 3)).
      { destruct zs as [|y ys'] eqn:Hzs.
        - assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [snd]; congruence.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [fst snd]; intros _; lia. }
      assert (Hw_gks : GoodKS (2 * 81 + 63 * (fst w + 3)) (snd w)).
      { destruct zs as [|y ys'] eqn:Hzs.
        - assert (Hw_nil_eq : w = (z1 - 1 + 3 + 3, (@nil nat))) by (rewrite Hw_def; reflexivity).
          rewrite Hw_nil_eq; cbn [snd GoodKS]; exact I.
        - assert (Hw_cons_eq : w = (z1 - 1, add_last (y :: ys') 6))
            by (rewrite Hw_def; exact (bump_enc_twice_nonempty (z1 - 1) (y :: ys') ltac:(discriminate))).
          rewrite Hw_cons_eq; cbn [fst snd].
          replace (2 * 81 + 63 * (z1 - 1 + 3)) with (162 + 63 * (z1 + 2)) by lia.
          exact (GoodKS_add_last (y :: ys') _ 6 Hgks_zs). }
      destruct (e0_loop_leave1_goodks (List.length (snd w)) (fst w) (snd w) 81 R_101_01_01
        eq_refl ltac:(lia) Hw_nil Hw_cons Hw_gks)
        as [m0 [ms [Hstep_l5 [Hval_ms [_ [_ Hgks_81_fn]]]]]].
      pose proof (Hgks_81_fn Hw_ge10 eq_refl) as Hgks_b1.
      cbv zeta in Hgks_b1.
      set (b1 := bump_enc m0 ms) in *.
      assert (Hstep6 : cfg_modeC (encL m0 ms)
        (S1 >> S1 >> S0 >> S1 >> R_101_01_01) -[ holdout_0311_tm ]->+
        cfg_modeC (encL 1 ((fst b1 + 1) :: snd b1)) (const S0)).
      { pose proof (step_modeC_b11 (encL m0 ms) (S0 >> S1 >> R_101_01_01)) as H1.
        pose proof (modeE1_to_modeC ms m0 (S0 >> S1 >> R_101_01_01) Hval_ms) as H2.
        fold b1 in H2.
        pose proof (step_modeC_b01_b10101_encL (fst b1) (snd b1)
          (S0 >> S1 >> const S0)) as H3.
        pose proof (step_modeC_b01_encL 0 ((fst b1 + 1) :: snd b1) (const S0)) as H4; simpl in H4.
        exact (stepPlus_stepPlus_stepPlus H1
          (stepPlus_stepPlus_stepPlus H2
            (stepPlus_stepPlus_stepPlus H3 H4))). }
      rewrite Hsub_eq in Hto_sub; cbn [fst snd] in Hto_sub.
      fold R_101 in Hto_sub.
      exists 1, ((fst b1 + 1) :: snd b1).
      split.
      * exact (stepPlus_stepPlus_stepPlus Hto_sub
          (stepPlus_stepPlus_stepPlus Hstep1
            (stepPlus_stepPlus_stepPlus Hstep_l2
              (stepPlus_stepPlus_stepPlus Hunwrap2
                (stepPlus_stepPlus_stepPlus Hstep34
                  (stepPlus_stepPlus_stepPlus Hstep_l5 Hstep6)))))).
      * right; split; [discriminate | exact Hgks_b1].
Qed.

(* ========================================================================== *)
(* Top-Level Invariant and Non-Halting Theorem                                *)
(* ========================================================================== *)

Definition Inv (c : Q * tape) : Prop :=
  exists k0 ks, c = cfg_modeC (encL k0 ks) (const S0) /\ InvNil k0 ks.

Lemma init_reaches_inv :
  exists c, (c0 -[ holdout_0311_tm ]->+ c) /\ Inv c.
Proof.
  pose proof init_reaches_modeC as H0.
  change (S0 >> S1 >> const S0) with (encL 0 []) in H0.
  assert (H1 : cfg_modeC (encL 0 []) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL 3 []) (const S0)).
  { pose proof (step_modeC_nil (encL 0 [])) as Ha.
    pose proof step_modeE0_first_base as Hb.
    change (S0 >> S1 >> const S0) with (encL 0 []) in Hb.
    change (S0 >> S1 >> (S0 >> S1 >> (S0 >> S1 >> const S0))) with (prepend01 3 (const S0)) in Hb.
    pose proof (modeC_prepend01_star 3 0 [] (const S0)) as Hc; simpl in Hc.
    exact (stepPlus_stepPlus_stepPlus Ha (stepPlus_stepStar_stepPlus Hb Hc)). }
  assert (H2 : cfg_modeC (encL 3 []) (const S0) -[ holdout_0311_tm ]->+ cfg_modeC (encL 2 [3]) (const S0)).
  { pose proof (step_modeC_nil (encL 3 [])) as Ha.
    pose proof (step_modeE0_first_b10 (encL 2 [])) as Hb.
    pose proof (step_modeE0_loop_b10_b10 (encL 0 []) (const S0)) as Hc.
    change (S1 >> S1 >> (S0 >> S1 >> const S0)) with (prepend11_01 1 (const S0)) in Hc.
    pose proof (step_modeE0_loop_base (prepend11_01 1 (const S0))) as Hd.
    change (S0 >> S1 >> S1 >> S1 >> S0 >> (S0 >> S1 >> const S0)) with (encL 0 [0]) in Hd.
    pose proof (step_modeC_b01_encL 0 [0] (prepend11_01 1 (const S0))) as He; simpl in He.
    pose proof (modeC_consume_11_01_nonempty 1 1 [0] (const S0) ltac:(discriminate) I) as Hf.
    cbn [add_last] in Hf; simpl in Hf.
    exact (stepPlus_stepPlus_stepPlus Ha
      (stepPlus_stepPlus_stepPlus Hb
        (stepPlus_stepPlus_stepPlus Hc
          (stepPlus_stepPlus_stepPlus Hd
            (stepPlus_stepStar_stepPlus He Hf))))). }
  assert (Hinv : InvNil 2 [3]).
  { right; split; [discriminate | cbn [Nat.eqb GoodKS]; split; [lia | exact I]]. }
  exists (cfg_modeC (encL 2 [3]) (const S0)).
  split.
  - exact (stepPlus_stepPlus_stepPlus H0 (stepPlus_stepPlus_stepPlus H1 H2)).
  - exists 2, [3]; exact (conj eq_refl Hinv).
Qed.

Lemma inv_step :
  forall c, Inv c -> exists c', Inv c' /\ (c -[ holdout_0311_tm ]->+ c').
Proof.
  intros c [k0 [ks [-> Hinv]]].
  destruct k0 as [|k0'].
  - destruct (step_k0_zero ks Hinv) as [k0' [ks' [Hstep Hinv']]].
    exists (cfg_modeC (encL k0' ks') (const S0)).
    split; [exists k0', ks'; exact (conj eq_refl Hinv') | exact Hstep].
  - destruct (step_k0_pos (S k0') ks ltac:(lia) Hinv) as [k0'' [ks'' [Hstep Hinv']]].
    exists (cfg_modeC (encL k0'' ks'') (const S0)).
    split; [exists k0'', ks''; exact (conj eq_refl Hinv') | exact Hstep].
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  destruct init_reaches_inv as [c [Hinit Hinv]].
  eapply multistep_nonhalt; [exact (stepPlus_stepStar Hinit) |].
  eapply progress_nonhalt; [exact inv_step | exact Hinv].
Qed.

Print Assumptions nonhalt.
