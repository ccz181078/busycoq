(* 1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC never halts. *)

From Coq Require Import Bool List Lists.Streams PeanoNat Lia ZifyNat QArith Lqa ZArith String.
From BusyCoq Require Import Individual62.
Import ListNotations.

Set Default Goal Selector "!".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := TM_from_str "1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC".
Arguments tm _ : simpl never.

Definition tm_core : TM := TM_from_str "1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF".
Arguments tm_core _ : simpl never.

Local Notation rat := QArith_base.Q.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (@const Sym S0).

(* ========================================================================== *)
(* State-Permutation Isomorphism (`tm_core` -> `tm`)                          *)
(* ========================================================================== *)

Definition isoPerm (q : Q) : Q :=
  match q with
  | A => C
  | B => D
  | C => E
  | D => F
  | E => B
  | F => A
  end.

Definition conjCfg (c : Q * tape) : Q * tape :=
  let '(q, t) := c in (isoPerm q, t).

Lemma step_conj (c c' : Q * tape) :
  c -[ tm_core ]-> c' ->
  conjCfg c -[ tm ]-> conjCfg c'.
Proof.
  destruct c as [q [[l s] r]], c' as [q2 t2].
  intro Hstep.
  inversion Hstep as [qa qb sa sb la ra Htr Heq1 Heq2 | qa qb sa sb la ra Htr Heq1 Heq2]; subst; clear Hstep.
  - destruct q, s; inversion Htr; subst; cbn [conjCfg isoPerm]; apply @step_left; reflexivity.
  - destruct q, s; inversion Htr; subst; cbn [conjCfg isoPerm]; apply @step_right; reflexivity.
Qed.

Lemma multistep_conj (n : nat) (c c' : Q * tape) :
  c -[ tm_core ]->> n / c' ->
  conjCfg c -[ tm ]->> n / conjCfg c'.
Proof.
  induction 1 as [c | n c c1 c2 H1 _ IH].
  - constructor.
  - econstructor; [exact (step_conj c c1 H1) | exact IH].
Qed.

(* ========================================================================== *)
(* Section 1: Token Words, Hub Configurations, Events & Parametric Micro-Rules *)
(* ========================================================================== *)

Definition w0 : list Sym := [S0; S0; S0; S0].
Definition w1 : list Sym := [S0; S1; S1].
Definition w2 : list Sym := [S0; S0; S1; S1].
Definition w3 : list Sym := [S0; S0; S0; S1].
Definition w4 : list Sym := [S0; S0; S1].
Definition wE : list Sym := [S1; S1].
Definition w5 : list Sym := [S0; S0; S0; S1; S1].

Definition l00 : list Sym := [S0; S0].
Definition l101 : list Sym := [S1; S0; S1].
Definition l1111 : list Sym := [S1; S1; S1; S1].
Definition l01111 : list Sym := [S0; S1; S1; S1; S1].

Definition hF (l r : side) : Q * tape := l {{F}}> r.
Definition hA (l r : side) : Q * tape := l <{{A}} r.

Lemma ptrans {c1 c2 c3 : Q * tape} :
  c1 -[ tm_core ]->+ c2 -> c2 -[ tm_core ]->+ c3 -> c1 -[ tm_core ]->+ c3.
Proof. apply progress_trans. Qed.

Lemma ps_trans {c1 c2 c3 : Q * tape} :
  c1 -[ tm_core ]->+ c2 -> c2 -[ tm_core ]->* c3 -> c1 -[ tm_core ]->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma sp_trans {c1 c2 c3 : Q * tape} :
  c1 -[ tm_core ]->* c2 -> c2 -[ tm_core ]->+ c3 -> c1 -[ tm_core ]->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} :
  c1 -[ tm_core ]->* c2 -> c2 -[ tm_core ]->* c3 -> c1 -[ tm_core ]->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : Q * tape} :
  c1 -[ tm_core ]->+ c2 -> c1 -[ tm_core ]->* c2.
Proof. apply progress_evstep. Qed.

Lemma zero_cons_0inf : S0 >> 0inf = 0inf.
Proof. symmetry. apply const_unfold. Qed.

Lemma w0_append_0inf : w0 *> 0inf = 0inf.
Proof.
  unfold w0; cbn [Str_app].
  repeat rewrite <- const_unfold.
  reflexivity.
Qed.

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

Ltac run_micro :=
  unfold hF, hA, w0, w1, w2, w3, w4, wE, w5, l00, l101, l1111, l01111;
  cbn [Str_app Streams.hd Streams.tl];
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

Lemma micro_R1 (l r : side) :
  hF l (wE *> r) -[ tm_core ]->+ hF (l00 *> l) r.
Proof. run_micro. Qed.

Lemma micro_R2 (l r : side) :
  hF l (w1 *> r) -[ tm_core ]->+ hF (l101 *> l) r.
Proof. run_micro. Qed.

Lemma micro_R3 (l r : side) :
  hF l (w3 *> r) -[ tm_core ]->+ hF (l1111 *> l) r.
Proof. run_micro. Qed.

Lemma micro_R4 (l r : side) :
  hF l (w2 *> r) -[ tm_core ]->+ hA l (w3 *> r).
Proof. run_micro. Qed.

Lemma micro_R5 (l r : side) :
  hF l (w4 *> (S0 >> r)) -[ tm_core ]->+ hA l (w0 *> r).
Proof. run_micro. Qed.

Lemma micro_R5_fuse (l r : side) :
  hF l (w4 *> wE *> r) -[ tm_core ]->+ hA l (w5 *> r).
Proof. run_micro. Qed.

Lemma micro_R6 (l r : side) :
  hF l (w0 *> r) -[ tm_core ]->+ hA l (w2 *> r).
Proof. run_micro. Qed.

Lemma micro_R7 (l r : side) :
  hA (l101 *> l) r -[ tm_core ]->+ hA l (w1 *> r).
Proof. run_micro. Qed.

Lemma micro_R8 (l r : side) :
  hA (l1111 *> l) r -[ tm_core ]->+ hA l (w0 *> r).
Proof. run_micro. Qed.

Lemma micro_R9 (l r : side) :
  hA (l00 *> l) (S0 >> r) -[ tm_core ]->+ hF (l101 *> l) r.
Proof. run_micro. Qed.

Lemma micro_R10 (r : side) :
  hA 0inf (S0 >> r) -[ tm_core ]->+ hF (l101 *> 0inf) r.
Proof. run_micro. Qed.

Lemma micro_5_fwd (l r : side) :
  hF l (w5 *> r) -[ tm_core ]->+ hF (l01111 *> l) r.
Proof. run_micro. Qed.

Lemma micro_5_ret (l r : side) :
  hA (l01111 *> l) (S0 >> r) -[ tm_core ]->+ hA l (w0 *> wE *> r).
Proof. run_micro. Qed.

Inductive Ev : Type :=
  | EvB
  | EvS.

Definition StepEv (e : Ev) (r r' : side) : Prop :=
  match e with
  | EvB => forall l : side, hF l r -[ tm_core ]->+ hA l r'
  | EvS => r = S0 >> r'
  end.

Inductive RunEv : list Ev -> side -> side -> Prop :=
  | RunEv_nil (r : side) : RunEv [] r r
  | RunEv_cons {e : Ev} {es : list Ev} {r1 r2 r3 : side} :
      StepEv e r1 r2 -> RunEv es r2 r3 -> RunEv (e :: es) r1 r3.

Fixpoint repB (n : nat) : list Ev :=
  match n with
  | 0 => []
  | S k => EvB :: repB k
  end.

Lemma repB_add (a b : nat) : repB (a + b) = repB a ++ repB b.
Proof.
  induction a as [| a IH]; [reflexivity |].
  cbn [Nat.add repB List.app]. rewrite IH. reflexivity.
Qed.

Lemma runEv_single {e : Ev} {r1 r2 : side} (h : StepEv e r1 r2) :
  RunEv [e] r1 r2.
Proof. exact (RunEv_cons h (RunEv_nil r2)). Qed.

Lemma runEv_append {xs ys : list Ev} {r1 r2 r3 : side}
    (hx : RunEv xs r1 r2) (hy : RunEv ys r2 r3) : RunEv (xs ++ ys) r1 r3.
Proof.
  induction hx as [r | e es ra rb rc hstep _ IH].
  - exact hy.
  - exact (RunEv_cons hstep (IH hy)).
Qed.

Lemma runEv_prefix {xs ys : list Ev} {r1 r3 : side}
    (h : RunEv (xs ++ ys) r1 r3) : exists r2, RunEv xs r1 r2 /\ RunEv ys r2 r3.
Proof.
  revert r1 h.
  induction xs as [| e es IH]; intros r1 h.
  - exists r1. split; [exact (RunEv_nil r1) | exact h].
  - inversion h as [| e' es' ra r_mid rc hstep hrest]; subst.
    destruct (IH r_mid hrest) as [r2 [hes hys]].
    exists r2. split; [exact (RunEv_cons hstep hes) | exact hys].
Qed.

Lemma stepEv_default_S : StepEv EvS 0inf 0inf.
Proof. cbn [StepEv]. symmetry. exact zero_cons_0inf. Qed.

Lemma stepEv_w0_B (r : side) : StepEv EvB (w0 *> r) (w2 *> r).
Proof. intro l. exact (micro_R6 l r). Qed.

Lemma stepEv_w2_B (r : side) : StepEv EvB (w2 *> r) (w3 *> r).
Proof. intro l. exact (micro_R4 l r). Qed.

Lemma stepEv_w3_B {r r' : side} (h : StepEv EvB r r') :
  StepEv EvB (w3 *> r) (w0 *> r').
Proof.
  intro l.
  exact (ptrans (micro_R3 l r) (ptrans (h (l1111 *> l)) (micro_R8 l r'))).
Qed.

Lemma stepEv_w1_B {r r' : side} (h : StepEv EvB r r') :
  StepEv EvB (w1 *> r) (w1 *> r').
Proof.
  intro l.
  exact (ptrans (micro_R2 l r) (ptrans (h (l101 *> l)) (micro_R7 l r'))).
Qed.

Lemma stepEv_w4_B {r r' : side} (h : StepEv EvS r r') :
  StepEv EvB (w4 *> r) (w0 *> r').
Proof.
  intro l. cbn [StepEv] in h. rewrite h. exact (micro_R5 l r').
Qed.

Lemma stepEv_w4_wE_B (r : side) :
  StepEv EvB (w4 *> wE *> r) (w5 *> r).
Proof. intro l. exact (micro_R5_fuse l r). Qed.

Lemma stepEv_wE_B {r r1 r2 r3 : side}
    (h1 : StepEv EvB r r1) (h2 : StepEv EvS r1 r2) (h3 : StepEv EvB r2 r3) :
  StepEv EvB (wE *> r) (w1 *> r3).
Proof.
  intro l.
  pose proof (micro_R1 l r) as s1.
  pose proof (h1 (l00 *> l)) as s2.
  cbn [StepEv] in h2. rewrite h2 in s2.
  pose proof (micro_R9 l r2) as s3.
  pose proof (h3 (l101 *> l)) as s4.
  pose proof (micro_R7 l r3) as s5.
  exact (ptrans s1 (ptrans s2 (ptrans s3 (ptrans s4 s5)))).
Qed.

Lemma stepEv_w5_B {r r1 r2 : side}
    (h1 : StepEv EvB r r1) (h2 : StepEv EvS r1 r2) :
  StepEv EvB (w5 *> r) (w0 *> wE *> r2).
Proof.
  intro l.
  pose proof (micro_5_fwd l r) as s1.
  pose proof (h1 (l01111 *> l)) as s2.
  cbn [StepEv] in h2. rewrite h2 in s2.
  pose proof (micro_5_ret l r2) as s3.
  exact (ptrans s1 (ptrans s2 s3)).
Qed.

Lemma stepEv_w0_S {r r' : side} (h : StepEv EvS r r') :
  StepEv EvS (w0 *> r) (w0 *> r').
Proof.
  cbn [StepEv] in *. rewrite h. reflexivity.
Qed.

Lemma stepEv_w1_S (r : side) : StepEv EvS (w1 *> r) (wE *> r).
Proof. reflexivity. Qed.

Lemma stepEv_w2_S (r : side) : StepEv EvS (w2 *> r) (w1 *> r).
Proof. reflexivity. Qed.

Lemma stepEv_w3_S (r : side) : StepEv EvS (w3 *> r) (w4 *> r).
Proof. reflexivity. Qed.

Lemma stepEv_w0_wE_S (r : side) : StepEv EvS (w0 *> wE *> r) (w5 *> r).
Proof. reflexivity. Qed.


(* ========================================================================== *)
(* Section 2: Initial Reachability (`c0 -->* conjCfg (eraCfg 18 (w2 *> 0inf))`) *)
(* ========================================================================== *)

Lemma init_reaches_era18 :
  c0 -[ tm ]->* (0inf <{{C}} (w1 ^^ 18 *> w0 *> wE *> w2 *> 0inf)).
Proof.
  unfold w1, w0, wE, w2; cbn [lpow List.app].
  rewrite c0_to_cconfig.
  repeat rewrite Str_cons_def.
  repeat rewrite <- Str_app_assoc.
  repeat rewrite simpl_directed_head_l.
  repeat rewrite simpl_directed_head_r.
  repeat rewrite l_const0_app_nil.
  repeat rewrite r_const0_app_nil.
  repeat rewrite config_to_cconfig.
  apply cconfig_evstep_dec_spec with (n := 18 * 400).
  vm_compute.
  reflexivity.
Qed.

(* ========================================================================== *)
(* Section 3: Era Loop (`era_step`)                                           *)
(* ========================================================================== *)

Definition xk (k : nat) : list Sym :=
  if Nat.eqb (k mod 3) 1 then w2 else w0.

Definition eraCfg (k : nat) (r : side) : Q * tape :=
  hA 0inf (w1 ^^ k *> xk k *> wE *> r).

Lemma lpow_succ_r_side (xs : list Sym) (n : nat) (s : side) :
  xs ^^ n *> xs *> s = xs ^^ (n + 1) *> s.
Proof.
  rewrite lpow_add. cbn [lpow List.app].
  rewrite Str_app_assoc, app_nil_r. reflexivity.
Qed.

Lemma lpow_succ_l_side (xs : list Sym) (n : nat) (s : side) :
  xs ^^ (n + 1) *> s = xs *> xs ^^ n *> s.
Proof.
  replace (n + 1) with (1 + n) by lia.
  rewrite lpow_add. cbn [lpow].
  rewrite app_nil_r, Str_app_assoc. reflexivity.
Qed.

Lemma lpow_1_side (xs : list Sym) (s : side) :
  xs ^^ 1 *> s = xs *> s.
Proof.
  cbn [lpow]. rewrite app_nil_r. reflexivity.
Qed.

Lemma sweep_R2 (n : nat) (l r : side) :
  hF l (w1 ^^ n *> r) -[ tm_core ]->* hF (l101 ^^ n *> l) r.
Proof.
  revert l.
  induction n as [| n IH]; intro l.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S n) with (n + 1) by lia.
    rewrite lpow_succ_l_side.
    pose proof (micro_R2 l (w1 ^^ n *> r)) as h1.
    pose proof (IH (l101 *> l)) as h2.
    rewrite lpow_succ_r_side in h2.
    exact (etrans (pev h1) h2).
Qed.

Lemma sweep_R7 (n : nat) (l r : side) :
  hA (l101 ^^ n *> l) r -[ tm_core ]->* hA l (w1 ^^ n *> r).
Proof.
  revert r.
  induction n as [| n IH]; intro r.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S n) with (n + 1) by lia.
    rewrite lpow_succ_l_side.
    pose proof (micro_R7 (l101 ^^ n *> l) r) as h1.
    pose proof (IH (w1 *> r)) as h2.
    rewrite lpow_succ_r_side in h2.
    exact (etrans (pev h1) h2).
Qed.

Lemma launch_era (k k' : nat) (t : side) :
  k = k' + 1 ->
  hA 0inf (w1 ^^ k *> t) -[ tm_core ]->+
    hF (l101 ^^ k' *> l00 *> l101 ^^ 1 *> 0inf) t.
Proof.
  intros ->.
  rewrite lpow_succ_l_side, lpow_1_side.
  pose proof (micro_R10 (wE *> w1 ^^ k' *> t)) as s1.
  change (S0 >> wE *> w1 ^^ k' *> t) with (w1 *> w1 ^^ k' *> t) in s1.
  pose proof (micro_R1 (l101 *> 0inf) (w1 ^^ k' *> t)) as s2.
  pose proof (sweep_R2 k' (l00 *> l101 *> 0inf) t) as s3.
  exact (ps_trans (ptrans s1 s2) s3).
Qed.

Lemma bounce_advance (a a' b b' : nat) (t : side) :
  b = b' + 1 -> a' = a + 1 ->
  hA (l101 ^^ b *> l00 *> l101 ^^ a *> 0inf) t -[ tm_core ]->+
    hF (l101 ^^ b' *> l00 *> l101 ^^ a' *> 0inf) t.
Proof.
  intros -> ->.
  pose proof (sweep_R7 (b' + 1) (l00 *> l101 ^^ a *> 0inf) t) as s1.
  pose proof (micro_R9 (l101 ^^ a *> 0inf) (wE *> w1 ^^ b' *> t)) as s2.
  change (S0 >> wE *> w1 ^^ b' *> t) with (w1 *> w1 ^^ b' *> t) in s2.
  rewrite <- lpow_succ_l_side in s2.
  rewrite <- (lpow_succ_l_side l101 a 0inf) in s2.
  pose proof (micro_R1 (l101 ^^ (a + 1) *> 0inf) (w1 ^^ b' *> t)) as s3.
  pose proof (sweep_R2 b' (l00 *> l101 ^^ (a + 1) *> 0inf) t) as s4.
  exact (sp_trans s1 (ps_trans (ptrans s2 s3) s4)).
Qed.

Lemma loop_3b_one (a b : nat) {r r' : side} (hB : StepEv EvB r r') :
  hA (l101 ^^ (b + 3) *> l00 *> l101 ^^ a *> 0inf) (w0 *> w1 *> r) -[ tm_core ]->+
    hA (l101 ^^ b *> l00 *> l101 ^^ (a + 3) *> 0inf) (w0 *> w1 *> r').
Proof.
  pose proof (bounce_advance a (a + 1) (b + 3) (b + 2) (w0 *> w1 *> r) ltac:(lia) ltac:(lia)) as s1.
  pose proof (micro_R6 (l101 ^^ (b + 2) *> l00 *> l101 ^^ (a + 1) *> 0inf) (w1 *> r)) as s2.
  pose proof (bounce_advance (a + 1) (a + 2) (b + 2) (b + 1) (w2 *> w1 *> r) ltac:(lia) ltac:(lia)) as s3.
  pose proof (micro_R4 (l101 ^^ (b + 1) *> l00 *> l101 ^^ (a + 2) *> 0inf) (w1 *> r)) as s4.
  pose proof (bounce_advance (a + 2) (a + 3) (b + 1) b (w3 *> w1 *> r) ltac:(lia) ltac:(lia)) as s5.
  pose proof (stepEv_w3_B (stepEv_w1_B hB) (l101 ^^ b *> l00 *> l101 ^^ (a + 3) *> 0inf)) as s6.
  exact (ptrans s1 (ptrans s2 (ptrans s3 (ptrans s4 (ptrans s5 s6))))).
Qed.

Lemma loop_3b (m a b : nat) {r r' : side}
    (hBs : RunEv (repB m) r r') :
  hA (l101 ^^ (b + 3 * m) *> l00 *> l101 ^^ a *> 0inf) (w0 *> w1 *> r) -[ tm_core ]->*
    hA (l101 ^^ b *> l00 *> l101 ^^ (a + 3 * m) *> 0inf) (w0 *> w1 *> r').
Proof.
  revert a r hBs.
  induction m as [| m IH]; intros a r hBs.
  - inversion hBs; subst.
    replace (b + 3 * 0) with b by lia.
    replace (a + 3 * 0) with a by lia.
    apply evstep_refl.
  - cbn [repB] in hBs.
    inversion hBs as [| e es ra r_mid rc hB hrest]; subst.
    pose proof (loop_3b_one a (b + 3 * m) hB) as s1.
    pose proof (IH (a + 3) r_mid hrest) as s2.
    replace (b + 3 * S m) with ((b + 3 * m) + 3) by lia.
    replace (a + 3 * S m) with ((a + 3) + 3 * m) by lia.
    exact (etrans (pev s1) s2).
Qed.

Lemma finish_b0 (a a' : nat) (r : side) :
  a' = a + 1 ->
  hA (l00 *> l101 ^^ a *> 0inf) (w0 *> w1 *> r) -[ tm_core ]->+
    hA 0inf (w1 ^^ a' *> w2 *> wE *> r).
Proof.
  intros ->.
  change (w0 *> w1 *> r) with (S0 >> (w0 *> wE *> r)).
  pose proof (micro_R9 (l101 ^^ a *> 0inf) (w0 *> wE *> r)) as s1.
  rewrite <- (lpow_succ_l_side l101 a 0inf) in s1.
  pose proof (micro_R6 (l101 ^^ (a + 1) *> 0inf) (wE *> r)) as s2.
  pose proof (sweep_R7 (a + 1) 0inf (w2 *> wE *> r)) as s3.
  exact (ps_trans (ptrans s1 s2) s3).
Qed.

Lemma finish_b2 (a a' : nat) (r : side) :
  a' = a + 3 ->
  hA (l101 ^^ 2 *> l00 *> l101 ^^ a *> 0inf) (w0 *> w1 *> r) -[ tm_core ]->+
    hA 0inf (w1 ^^ a' *> w0 *> wE *> r).
Proof.
  intros ->.
  pose proof (bounce_advance a (a + 1) 2 1 (w0 *> w1 *> r) ltac:(lia) ltac:(lia)) as s1.
  pose proof (micro_R6 (l101 ^^ 1 *> l00 *> l101 ^^ (a + 1) *> 0inf) (w1 *> r)) as s2.
  pose proof (bounce_advance (a + 1) (a + 2) 1 0 (w2 *> w1 *> r) ltac:(lia) ltac:(lia)) as s3.
  pose proof (micro_R4 (l101 ^^ 0 *> l00 *> l101 ^^ (a + 2) *> 0inf) (w1 *> r)) as s4.
  cbn [lpow Str_app] in s3, s4.
  pose proof (micro_R9 (l101 ^^ (a + 2) *> 0inf) (w4 *> w1 *> r)) as s5.
  change (S0 >> w4 *> w1 *> r) with (w3 *> w1 *> r) in s5.
  rewrite <- (lpow_succ_l_side l101 (a + 2) 0inf) in s5.
  replace ((a + 2) + 1) with (a + 3) in s5 by lia.
  pose proof (micro_R5 (l101 ^^ (a + 3) *> 0inf) (wE *> r)) as s6.
  change (w4 *> (S0 >> wE *> r)) with (w4 *> w1 *> r) in s6.
  pose proof (sweep_R7 (a + 3) 0inf (w0 *> wE *> r)) as s7.
  exact (ps_trans (ptrans s1 (ptrans s2 (ptrans s3 (ptrans s4 (ptrans s5 s6))))) s7).
Qed.

Definition eraEvents (k : nat) : list Ev := [EvB; EvS] ++ repB (k / 3).

Lemma era_step (k : nat) (hk : 3 <= k) {r r' : side}
    (hev : RunEv (eraEvents k) r r') :
  eraCfg k r -[ tm_core ]->+ eraCfg (k + 1) r'.
Proof.
  set (m := k / 3 - 1).
  assert (hm : k / 3 = S m) by (unfold m; lia).
  unfold eraEvents in hev.
  rewrite hm in hev. cbn [repB List.app] in hev.
  change (EvB :: EvS :: EvB :: repB m) with ([EvB; EvS; EvB] ++ repB m) in hev.
  destruct (runEv_prefix hev) as [r3 [hbsb hbm]].
  inversion hbsb as [| ? ? ? r1 ? hB1 hrest1]; subst.
  inversion hrest1 as [| ? ? ? r2 ? hS hrest2]; subst.
  inversion hrest2 as [| ? ? ? ? ? hB2 hnil]; subst.
  inversion hnil; subst.
  assert (hrem : k mod 3 = 0 \/ k mod 3 = 1 \/ k mod 3 = 2) by lia.
  destruct hrem as [hr0 | [hr1 | hr2]].
  - assert (hxk : xk k = w0) by (unfold xk; rewrite hr0; reflexivity).
    assert (hr1' : (k + 1) mod 3 = 1) by lia.
    assert (hxk1 : xk (k + 1) = w2) by (unfold xk; rewrite hr1'; reflexivity).
    unfold eraCfg. rewrite hxk, hxk1.
    pose proof (launch_era k (3 * m + 2) (w0 *> wE *> r) ltac:(lia)) as s1.
    pose proof (micro_R6 (l101 ^^ (3 * m + 2) *> l00 *> l101 ^^ 1 *> 0inf) (wE *> r)) as s2.
    pose proof (bounce_advance 1 2 (3 * m + 2) (3 * m + 1) (w2 *> wE *> r) ltac:(lia) ltac:(lia)) as s3.
    pose proof (micro_R4 (l101 ^^ (3 * m + 1) *> l00 *> l101 ^^ 2 *> 0inf) (wE *> r)) as s4.
    pose proof (bounce_advance 2 3 (3 * m + 1) (3 * m) (w3 *> wE *> r) ltac:(lia) ltac:(lia)) as s5.
    pose proof (stepEv_w3_B (stepEv_wE_B hB1 hS hB2)
      (l101 ^^ (3 * m) *> l00 *> l101 ^^ 3 *> 0inf)) as s6.
    pose proof (loop_3b m 3 0 hbm) as s7.
    cbn [Nat.add lpow Str_app] in s7.
    pose proof (finish_b0 (3 + 3 * m) (k + 1) r' ltac:(lia)) as s8.
    exact (ptrans s1 (ptrans s2 (ptrans s3 (ptrans s4 (ptrans s5
      (ps_trans s6 (etrans s7 (pev s8)))))))).
  - assert (hxk : xk k = w2) by (unfold xk; rewrite hr1; reflexivity).
    assert (hr2' : (k + 1) mod 3 = 2) by lia.
    assert (hxk1 : xk (k + 1) = w0) by (unfold xk; rewrite hr2'; reflexivity).
    unfold eraCfg. rewrite hxk, hxk1.
    pose proof (launch_era k (3 * m + 3) (w2 *> wE *> r) ltac:(lia)) as s1.
    pose proof (micro_R4 (l101 ^^ (3 * m + 3) *> l00 *> l101 ^^ 1 *> 0inf) (wE *> r)) as s2.
    pose proof (bounce_advance 1 2 (3 * m + 3) (3 * m + 2) (w3 *> wE *> r) ltac:(lia) ltac:(lia)) as s3.
    pose proof (stepEv_w3_B (stepEv_wE_B hB1 hS hB2)
      (l101 ^^ (3 * m + 2) *> l00 *> l101 ^^ 2 *> 0inf)) as s4.
    pose proof (loop_3b m 2 2 hbm) as s5.
    replace (2 + 3 * m) with (3 * m + 2) in s5 by lia.
    pose proof (finish_b2 (3 * m + 2) (k + 1) r' ltac:(lia)) as s6.
    exact (ptrans s1 (ptrans s2 (ptrans s3
      (ps_trans s4 (etrans s5 (pev s6)))))).
  - assert (hxk : xk k = w0) by (unfold xk; rewrite hr2; reflexivity).
    assert (hr0' : (k + 1) mod 3 = 0) by lia.
    assert (hxk1 : xk (k + 1) = w0) by (unfold xk; rewrite hr0'; reflexivity).
    unfold eraCfg. rewrite hxk, hxk1.
    pose proof (launch_era k (3 * m + 4) (w0 *> wE *> r) ltac:(lia)) as s1.
    pose proof (micro_R6 (l101 ^^ (3 * m + 4) *> l00 *> l101 ^^ 1 *> 0inf) (wE *> r)) as s2.
    pose proof (bounce_advance 1 2 (3 * m + 4) (3 * m + 3) (w2 *> wE *> r) ltac:(lia) ltac:(lia)) as s3.
    pose proof (micro_R4 (l101 ^^ (3 * m + 3) *> l00 *> l101 ^^ 2 *> 0inf) (wE *> r)) as s4.
    pose proof (bounce_advance 2 3 (3 * m + 3) (3 * m + 2) (w3 *> wE *> r) ltac:(lia) ltac:(lia)) as s5.
    pose proof (stepEv_w3_B (stepEv_wE_B hB1 hS hB2)
      (l101 ^^ (3 * m + 2) *> l00 *> l101 ^^ 3 *> 0inf)) as s6.
    pose proof (loop_3b m 3 2 hbm) as s7.
    replace (2 + 3 * m) with (3 * m + 2) in s7 by lia.
    pose proof (finish_b2 (3 + 3 * m) (k + 1) r' ltac:(lia)) as s8.
    exact (ptrans s1 (ptrans s2 (ptrans s3 (ptrans s4 (ptrans s5
      (ps_trans s6 (etrans s7 (pev s8)))))))).
Qed.

(* ========================================================================== *)
(* Section 4: Pure Rational `AdjGoodFrom`, Discreteness Lemma & Gap Events    *)
(* ========================================================================== *)

Definition Q_of_nat (n : nat) : rat := inject_Z (Z.of_nat n).

Lemma Q_of_nat_nonneg (n : nat) : (0 <= Q_of_nat n)%Q.
Proof.
  unfold Q_of_nat. change 0%Q with (inject_Z 0).
  rewrite <- Zle_Qle. lia.
Qed.

Lemma Q_of_nat_le (a b : nat) : a <= b -> (Q_of_nat a <= Q_of_nat b)%Q.
Proof.
  intro H. unfold Q_of_nat. rewrite <- Zle_Qle. lia.
Qed.

Lemma Q_of_nat_add (a b : nat) : (Q_of_nat (a + b) == Q_of_nat a + Q_of_nat b)%Q.
Proof.
  unfold Q_of_nat. rewrite Nat2Z.inj_add, inject_Z_plus. reflexivity.
Qed.

Lemma Q_of_nat_S (n : nat) : (Q_of_nat (S n) == Q_of_nat n + 1)%Q.
Proof.
  replace (S n) with (n + 1) by lia.
  rewrite Q_of_nat_add. reflexivity.
Qed.

Lemma Q_of_nat_mul3 (q : nat) : (Q_of_nat (3 * q) == 3 * Q_of_nat q)%Q.
Proof.
  unfold Q_of_nat. rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity.
Qed.

Lemma Q_of_nat_lin (a q r : nat) :
  a = 3 * q + r ->
  (Q_of_nat a == 3 * Q_of_nat q + Q_of_nat r)%Q.
Proof.
  intros ->. rewrite Q_of_nat_add, Q_of_nat_mul3. reflexivity.
Qed.

Ltac qlra :=
  change (Q_of_nat 0) with 0%Q in *;
  change (Q_of_nat 1) with 1%Q in *;
  change (Q_of_nat 2) with 2%Q in *;
  change (Q_of_nat 3) with 3%Q in *;
  change (Q_of_nat 4) with 4%Q in *;
  change (Q_of_nat 5) with 5%Q in *;
  change (Q_of_nat 6) with 6%Q in *;
  lra.

Definition nextP (p : rat) (g : nat) : rat :=
  (Q_of_nat g + p * (1 # 3))%Q.

Fixpoint endP (p : rat) (gs : list nat) : rat :=
  match gs with
  | [] => p
  | g :: gs' => endP (nextP p g) gs'
  end.

Fixpoint AdjGoodFrom (p : rat) (gs : list nat) : Prop :=
  match gs with
  | [] => True
  | g :: gs' => (2 * p <= 3 * Q_of_nat g + 3)%Q /\ AdjGoodFrom (nextP p g) gs'
  end.

Definition Good (gs : list nat) : Prop := AdjGoodFrom 0%Q gs.

Lemma nextP_mono (p1 p2 : rat) (g : nat) :
  (p1 <= p2)%Q -> (nextP p1 g <= nextP p2 g)%Q.
Proof. unfold nextP. intros. qlra. Qed.

Lemma adjGood_mono (p1 p2 : rat) (gs : list nat) :
  (p1 <= p2)%Q -> AdjGoodFrom p2 gs -> AdjGoodFrom p1 gs.
Proof.
  revert p1 p2.
  induction gs as [| g gs IH]; intros p1 p2 Hle Hag; [exact I |].
  destruct Hag as [Hb Hrest].
  split; [lra | eapply IH; [apply nextP_mono; exact Hle | exact Hrest]].
Qed.

Lemma endP_append (p : rat) (xs ys : list nat) :
  endP p (xs ++ ys) = endP (endP p xs) ys.
Proof.
  revert p.
  induction xs as [| x xs IH]; intro p; [reflexivity |].
  exact (IH (nextP p x)).
Qed.

Lemma adjGood_append {p : rat} {xs ys : list nat}
    (hx : AdjGoodFrom p xs) (hy : AdjGoodFrom (endP p xs) ys) :
  AdjGoodFrom p (xs ++ ys).
Proof.
  revert p hx hy.
  induction xs as [| x xs IH]; intros p hx hy; [exact hy |].
  destruct hx as [h1 hrest].
  exact (conj h1 (IH (nextP p x) hrest hy)).
Qed.

Lemma adjGood_implies_bound {p : rat} {gs : list nat} (h : AdjGoodFrom p gs) :
  forall x, In x gs -> (2 * p <= 3 * Q_of_nat x + 3)%Q.
Proof.
  revert p h.
  induction gs as [| g rest IH]; intros p h x hx.
  - inversion hx.
  - destruct h as [h1 hrest].
    destruct hx as [<- | hmem]; [exact h1 |].
    pose proof (IH (nextP p g) hrest x hmem) as hih.
    unfold nextP in hih.
    destruct (Nat.lt_ge_cases g (S x)) as [hle | hge].
    + pose proof (Q_of_nat_le g x ltac:(lia)) as hle'. qlra.
    + pose proof (Q_of_nat_le (S x) g hge) as hge'.
      pose proof (Q_of_nat_S x) as hsx. qlra.
Qed.

Lemma adjGood_no_zero_of_gt {p : rat} {gs : list nat}
    (h : AdjGoodFrom p gs) (hp : (3 < 2 * p)%Q) :
  forall x, In x gs -> 1 <= x.
Proof.
  intros x hx.
  pose proof (adjGood_implies_bound h x hx) as hb.
  destruct x as [| x']; [| lia].
  change (Q_of_nat 0) with 0%Q in hb.
  exfalso. qlra.
Qed.

Fixpoint sum_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => x + sum_list xs'
  end.

Lemma sum_list_app (xs ys : list nat) :
  sum_list (xs ++ ys) = sum_list xs + sum_list ys.
Proof.
  induction xs as [| x xs IH]; [reflexivity |].
  cbn [List.app sum_list]. lia.
Qed.

Definition gapEv (g : nat) : list Ev := repB g ++ [EvS].

Fixpoint gapsEv (gs : list nat) : list Ev :=
  match gs with
  | [] => []
  | g :: gs' => gapEv g ++ gapsEv gs'
  end.

Lemma gapsEv_append (xs ys : list nat) :
  gapsEv (xs ++ ys) = gapsEv xs ++ gapsEv ys.
Proof.
  induction xs as [| x xs IH]; [reflexivity |].
  cbn [List.app gapsEv]. rewrite IH, app_assoc. reflexivity.
Qed.

Fixpoint isAllPos (gs : list nat) : bool :=
  match gs with
  | [] => true
  | 0 :: _ => false
  | S _ :: gs' => isAllPos gs'
  end.

Lemma isAllPos_eq_true_iff {gs : list nat} :
  isAllPos gs = true <-> forall x, In x gs -> 1 <= x.
Proof.
  induction gs as [| g rest IH].
  - cbn [isAllPos In]. split; [intros _ x []; lia | intros _; reflexivity].
  - destruct g as [| n].
    + cbn [isAllPos In]. split; [discriminate |].
      intro H. specialize (H 0 (or_introl eq_refl)). lia.
    + cbn [isAllPos In]. rewrite IH. split.
      * intros H x [<- | Hx]; [lia | exact (H x Hx)].
      * intros H x Hx. exact (H x (or_intror Hx)).
Qed.

Fixpoint stripLZ (gs : list nat) : list nat :=
  match gs with
  | [] => []
  | 0 :: gs' => stripLZ gs'
  | S n :: gs' => S n :: gs'
  end.

Lemma stripLZ_zeros_append (zs gs : list nat) (hz : forall x, In x zs -> x = 0) :
  stripLZ (zs ++ gs) = stripLZ gs.
Proof.
  induction zs as [| z zs IH]; [reflexivity |].
  assert (h0 : z = 0) by (apply hz; left; reflexivity).
  subst z. cbn [List.app stripLZ].
  apply IH. intros x hx. apply hz. right. exact hx.
Qed.

Definition isSafeZero (gs : list nat) : bool :=
  match stripLZ gs with
  | [] => true
  | 1 :: 0 :: rest => isAllPos rest
  | rest => isAllPos rest
  end.

Lemma isSafeZero_of_allPos {gs : list nat} (h : forall x, In x gs -> 1 <= x) :
  isSafeZero gs = true.
Proof.
  destruct gs as [| g rest]; [reflexivity |].
  destruct g as [| n].
  - exfalso. specialize (h 0 (or_introl eq_refl)). lia.
  - assert (hpos : isAllPos rest = true).
    { apply isAllPos_eq_true_iff. intros x hx. exact (h x (or_intror hx)). }
    destruct n as [| n'].
    + destruct rest as [| r rs]; [reflexivity |].
      destruct r as [| m].
      * exfalso. specialize (h 0 (or_intror (or_introl eq_refl))). lia.
      * cbn [isSafeZero stripLZ isAllPos] in *. exact hpos.
    + cbn [isSafeZero stripLZ isAllPos]. exact hpos.
Qed.

Lemma isSafeZero_zeros_append {zs gs : list nat} (hz : forall x, In x zs -> x = 0)
    (h : isSafeZero gs = true) : isSafeZero (zs ++ gs) = true.
Proof.
  unfold isSafeZero. rewrite (stripLZ_zeros_append zs gs hz). exact h.
Qed.

Lemma runEv_w0_B3 {r r' : side} (h : StepEv EvB r r') :
  RunEv [EvB; EvB; EvB] (w0 *> r) (w0 *> r').
Proof.
  exact (RunEv_cons (stepEv_w0_B r)
    (RunEv_cons (stepEv_w2_B r)
      (RunEv_cons (stepEv_w3_B h) (RunEv_nil _)))).
Qed.

Lemma runEv_w0_B3q (q : nat) {r r' : side}
    (h : RunEv (repB q) r r') :
  RunEv (repB (3 * q)) (w0 *> r) (w0 *> r').
Proof.
  revert r h.
  induction q as [| q IH]; intros r h.
  - inversion h; subst. exact (RunEv_nil _).
  - cbn [repB] in h.
    inversion h as [| ? ? ? r_mid ? hB hrest]; subst.
    replace (3 * S q) with (3 + 3 * q) by lia.
    rewrite repB_add. cbn [repB].
    exact (runEv_append (runEv_w0_B3 hB) (IH r_mid hrest)).
Qed.

Lemma runEv_w1_Bk (k : nat) {r r' : side}
    (h : RunEv (repB k) r r') :
  RunEv (repB k) (w1 *> r) (w1 *> r').
Proof.
  revert r h.
  induction k as [| k IH]; intros r h.
  - inversion h; subst. exact (RunEv_nil _).
  - cbn [repB] in h |- *.
    inversion h as [| ? ? ? r_mid ? hB hrest]; subst.
    exact (RunEv_cons (stepEv_w1_B hB) (IH r_mid hrest)).
Qed.

Lemma run_B_only : forall t : nat, exists r', RunEv (repB t) 0inf r'.
Proof.
  induction t as [t IH] using strong_induction.
  destruct t as [| t']; [exists 0inf; exact (RunEv_nil 0inf) |].
  set (n := S t'). fold n.
  assert (hq_lt : n / 3 < n) by (unfold n; lia).
  destruct (IH (n / 3) hq_lt) as [r1 hr1].
  pose proof (runEv_w0_B3q (n / 3) hr1) as hmain.
  rewrite w0_append_0inf in hmain.
  assert (hrem : n mod 3 = 0 \/ n mod 3 = 1 \/ n mod 3 = 2) by lia.
  destruct hrem as [h0 | [h1 | h2]].
  - rewrite (ltac:(f_equal; lia) : repB n = repB (3 * (n / 3))).
    exists (w0 *> r1). exact hmain.
  - rewrite (ltac:(f_equal; lia) : repB n = repB (3 * (n / 3) + 1)).
    rewrite repB_add. cbn [repB].
    exists (w2 *> r1).
    exact (runEv_append hmain (runEv_single (stepEv_w0_B r1))).
  - rewrite (ltac:(f_equal; lia) : repB n = repB (3 * (n / 3) + 2)).
    rewrite repB_add. cbn [repB].
    exists (w3 *> r1).
    exact (runEv_append hmain
      (RunEv_cons (stepEv_w0_B r1) (runEv_single (stepEv_w2_B r1)))).
Qed.

(* ========================================================================== *)
(* Section 5: 1-Cell Peeling Transducer (`peel1`)                             *)
(* ========================================================================== *)

Inductive St1 : Type :=
  | s0
  | s4
  | s1
  | sE.

Definition tok1 (st : St1) : list Sym :=
  match st with
  | s0 => w0
  | s4 => w4
  | s1 => w1
  | sE => wE
  end.

Definition def1 (st : St1) : nat :=
  match st with
  | s0 => 0
  | s4 => 1
  | s1 => 1
  | sE => 2
  end.

Definition step1 (st : St1) (c g : nat) : St1 * (nat * list nat) :=
  match st with
  | s0 =>
    if Nat.eqb (g mod 3) 0 then (s0, (0, [c + g / 3]))
    else if Nat.eqb (g mod 3) 1 then (s1, (c + g / 3, []))
    else (s4, (c + g / 3, []))
  | s4 =>
    match g with
    | 0 => (s4, (c, []))
    | S g' =>
      if Nat.eqb (g' mod 3) 0 then (s0, (0, [c; g' / 3]))
      else if Nat.eqb (g' mod 3) 1 then (s1, (g' / 3, [c]))
      else (s4, (g' / 3, [c]))
    end
  | s1 => (sE, (c + g, []))
  | sE =>
    match g with
    | 0 => (sE, (c, []))
    | S g' => (sE, (S g', [c + 1]))
    end
  end.

Fixpoint run1Aux (st : St1) (c : nat) (gs : list nat) : St1 * (nat * list nat) :=
  match gs with
  | [] => (st, (c, []))
  | g :: gs' =>
    let r1 := step1 st c g in
    let r2 := run1Aux (fst r1) (fst (snd r1)) gs' in
    (fst r2, (fst (snd r2), snd (snd r1) ++ snd (snd r2)))
  end.

Definition step1Tail (st : St1) (c t : nat) : list nat * nat :=
  match st with
  | s0 => ([], c + t / 3)
  | s4 => match t with 0 => ([], c) | S t' => ([c], t' / 3) end
  | s1 => ([], c + t)
  | sE => match t with 0 => ([], c) | S t' => ([c + 1], S t') end
  end.

Definition run1Full (st : St1) (c : nat) (gs : list nat) (t : nat) : list nat * nat :=
  let r := run1Aux st c gs in
  let rt := step1Tail (fst r) (fst (snd r)) t in
  (snd (snd r) ++ fst rt, snd rt).

Definition step1Ev (st : St1) (g : nat) : list Ev :=
  match st with
  | s0 =>
    if Nat.eqb (g mod 3) 0 then repB (g / 3) ++ [EvS]
    else repB (g / 3)
  | s4 =>
    match g with
    | 0 => []
    | S g' =>
      EvS :: (if Nat.eqb (g' mod 3) 0 then repB (g' / 3) ++ [EvS]
              else repB (g' / 3))
    end
  | s1 => repB g
  | sE =>
    match g with
    | 0 => []
    | S g' => EvB :: EvS :: repB (S g')
    end
  end.

Definition step1TailEv (st : St1) (t : nat) : list Ev :=
  match st with
  | s0 => repB (t / 3)
  | s4 => match t with 0 => [] | S t' => EvS :: repB (t' / 3) end
  | s1 => repB t
  | sE => match t with 0 => [] | S t' => EvB :: EvS :: repB (S t') end
  end.

Fixpoint run1Evs (st : St1) (gs : list nat) (t : nat) : list Ev :=
  match gs with
  | [] => step1TailEv st t
  | g :: gs' => step1Ev st g ++ run1Evs (fst (step1 st 0 g)) gs' t
  end.

Lemma step1_next_indep_c (st : St1) (c g : nat) :
  fst (step1 st c g) = fst (step1 st 0 g).
Proof.
  destruct st; cbn [step1].
  - destruct (Nat.eqb (g mod 3) 0); [reflexivity |].
    destruct (Nat.eqb (g mod 3) 1); reflexivity.
  - destruct g as [| g']; [reflexivity |].
    destruct (Nat.eqb (g' mod 3) 0); [reflexivity |].
    destruct (Nat.eqb (g' mod 3) 1); reflexivity.
  - reflexivity.
  - destruct g; reflexivity.
Qed.

Lemma rep_B_step1Ev (st : St1) (c g : nat) (hg : st = s4 \/ st = sE -> 1 <= g) :
  repB c ++ step1Ev st g =
    gapsEv (snd (snd (step1 st c g))) ++ repB (fst (snd (step1 st c g))).
Proof.
  destruct st.
  - cbn [step1Ev step1].
    assert (hrem : g mod 3 = 0 \/ g mod 3 = 1 \/ g mod 3 = 2) by lia.
    destruct hrem as [h0 | [h1 | h2]]; rewrite ?h0, ?h1, ?h2;
      cbn [Nat.eqb fst snd gapsEv List.app]; unfold gapEv;
      rewrite ?repB_add; repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - destruct g as [| g'].
    + exfalso. specialize (hg (or_introl eq_refl)). lia.
    + cbn [step1Ev step1].
      assert (hrem : g' mod 3 = 0 \/ g' mod 3 = 1 \/ g' mod 3 = 2) by lia.
      destruct hrem as [h0 | [h1 | h2]]; rewrite ?h0, ?h1, ?h2;
        cbn [Nat.eqb fst snd gapsEv List.app]; unfold gapEv;
        repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - cbn [step1Ev step1 fst snd gapsEv List.app].
    rewrite repB_add. reflexivity.
  - destruct g as [| g'].
    + exfalso. specialize (hg (or_intror eq_refl)). lia.
    + cbn [step1Ev step1 fst snd gapsEv]; unfold gapEv.
      rewrite repB_add. cbn [repB List.app].
      repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
Qed.

Lemma rep_B_step1TailEv (st : St1) (c t : nat) :
  repB c ++ step1TailEv st t =
    gapsEv (fst (step1Tail st c t)) ++ repB (snd (step1Tail st c t)).
Proof.
  destruct st.
  - cbn [step1TailEv step1Tail fst snd gapsEv List.app].
    rewrite repB_add. reflexivity.
  - destruct t as [| t']; cbn [step1TailEv step1Tail fst snd gapsEv List.app]; unfold gapEv.
    + rewrite app_nil_r. reflexivity.
    + repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - cbn [step1TailEv step1Tail fst snd gapsEv List.app].
    rewrite repB_add. reflexivity.
  - destruct t as [| t']; cbn [step1TailEv step1Tail fst snd gapsEv List.app]; unfold gapEv.
    + rewrite app_nil_r. reflexivity.
    + rewrite repB_add; repeat rewrite app_nil_r; cbn [repB List.app];
      repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
Qed.

Fixpoint Safe1 (st : St1) (gs : list nat) : Prop :=
  match gs with
  | [] => True
  | g :: gs' => (st = s4 \/ st = sE -> 1 <= g) /\ Safe1 (fst (step1 st 0 g)) gs'
  end.

Lemma safe1_of_allPos (st : St1) (gs : list nat) (h : forall x, In x gs -> 1 <= x) :
  Safe1 st gs.
Proof.
  revert st.
  induction gs as [| g rest IH]; intro st; [exact I |].
  split.
  - intros _. exact (h g (or_introl eq_refl)).
  - apply IH. intros x hx. exact (h x (or_intror hx)).
Qed.

Lemma rep_B_run1Evs (st : St1) (c : nat) (gs : list nat) (t : nat) (hs : Safe1 st gs) :
  repB c ++ run1Evs st gs t =
    gapsEv (fst (run1Full st c gs t)) ++ repB (snd (run1Full st c gs t)).
Proof.
  revert st c hs.
  induction gs as [| g rest IH]; intros st c hs.
  - cbn [run1Evs run1Full run1Aux fst snd List.app].
    exact (rep_B_step1TailEv st c t).
  - destruct hs as [hg hrest].
    cbn [run1Evs run1Full run1Aux fst snd].
    rewrite app_assoc, (rep_B_step1Ev st c g hg), <- app_assoc.
    rewrite <- (step1_next_indep_c st c g) in hrest |- *.
    pose proof (IH (fst (step1 st c g)) (fst (snd (step1 st c g))) hrest) as hih.
    unfold run1Full in hih.
    rewrite hih, app_assoc, <- gapsEv_append, <- app_assoc.
    reflexivity.
Qed.

Lemma lift1_s0_step (g : nat) {r r' : side}
    (h : RunEv (step1Ev s0 g) r r') :
  RunEv (gapEv g) (w0 *> r) (tok1 (fst (step1 s0 0 g)) *> r').
Proof.
  assert (hrem : g mod 3 = 0 \/ g mod 3 = 1 \/ g mod 3 = 2) by lia.
  destruct hrem as [h0 | [h1 | h2]].
  - cbn [step1Ev step1] in h |- *. rewrite h0 in h |- *. cbn [Nat.eqb fst tok1] in h |- *.
    destruct (runEv_prefix h) as [r1 [hB hS]].
    inversion hS as [| ? ? ? ? ? hs hnil]; subst.
    inversion hnil; subst.
    unfold gapEv. rewrite (ltac:(f_equal; lia) : repB g = repB (3 * (g / 3))).
    exact (runEv_append (runEv_w0_B3q (g / 3) hB) (runEv_single (stepEv_w0_S hs))).
  - cbn [step1Ev step1] in h |- *. rewrite h1 in h |- *. cbn [Nat.eqb fst tok1] in h |- *.
    unfold gapEv. rewrite (ltac:(f_equal; lia) : repB g = repB (3 * (g / 3) + 1)).
    rewrite repB_add, <- app_assoc. cbn [repB List.app].
    exact (runEv_append (runEv_w0_B3q (g / 3) h)
      (RunEv_cons (stepEv_w0_B r') (runEv_single (stepEv_w2_S r')))).
  - cbn [step1Ev step1] in h |- *. rewrite h2 in h |- *. cbn [Nat.eqb fst tok1] in h |- *.
    unfold gapEv. rewrite (ltac:(f_equal; lia) : repB g = repB (3 * (g / 3) + 2)).
    rewrite repB_add, <- app_assoc. cbn [repB List.app].
    exact (runEv_append (runEv_w0_B3q (g / 3) h)
      (RunEv_cons (stepEv_w0_B r')
        (RunEv_cons (stepEv_w2_B r') (runEv_single (stepEv_w3_S r'))))).
Qed.

Lemma lift1_step (st : St1) (g : nat) (hg : st = s4 \/ st = sE -> 1 <= g)
    {r r' : side} (h : RunEv (step1Ev st g) r r') :
  RunEv (gapEv g) (tok1 st *> r) (tok1 (fst (step1 st 0 g)) *> r').
Proof.
  destruct st.
  - exact (lift1_s0_step g h).
  - destruct g as [| g'].
    + exfalso. specialize (hg (or_introl eq_refl)). lia.
    + cbn [step1Ev] in h.
      inversion h as [| ? ? ? r1 ? hS hrest]; subst.
      pose proof (stepEv_w4_B hS) as hs1.
      change (gapEv (S g')) with (EvB :: gapEv g').
      pose proof (lift1_s0_step g' hrest) as hlift.
      assert (heq_st : fst (step1 s4 0 (S g')) = fst (step1 s0 0 g')).
      { cbn [step1]. destruct (Nat.eqb (g' mod 3) 0); [reflexivity |].
        destruct (Nat.eqb (g' mod 3) 1); reflexivity. }
      rewrite heq_st. cbn [tok1].
      exact (RunEv_cons hs1 hlift).
  - cbn [step1Ev] in h. cbn [step1 fst tok1]. unfold gapEv.
    exact (runEv_append (runEv_w1_Bk g h) (runEv_single (stepEv_w1_S r'))).
  - destruct g as [| g'].
    + exfalso. specialize (hg (or_intror eq_refl)). lia.
    + cbn [step1Ev repB] in h.
      inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
      inversion h1 as [| ? ? ? r2 ? hS h2]; subst.
      inversion h2 as [| ? ? ? r3 ? hB2 hrest]; subst.
      pose proof (stepEv_wE_B hB1 hS hB2) as hs1.
      change (gapEv (S g')) with (EvB :: (repB g' ++ [EvS])).
      cbn [step1 fst tok1].
      exact (RunEv_cons hs1
        (runEv_append (runEv_w1_Bk g' hrest) (runEv_single (stepEv_w1_S r')))).
Qed.

Lemma lift1_tail (st : St1) (t : nat) {r r' : side}
    (h : RunEv (step1TailEv st t) r r') :
  exists r_out, RunEv (repB t) (tok1 st *> r) r_out.
Proof.
  destruct st; cbn [tok1].
  - cbn [step1TailEv] in h.
    assert (hrem : t mod 3 = 0 \/ t mod 3 = 1 \/ t mod 3 = 2) by lia.
    destruct hrem as [h0 | [h1 | h2]].
    + rewrite (ltac:(f_equal; lia) : repB t = repB (3 * (t / 3))).
      exists (w0 *> r'). exact (runEv_w0_B3q (t / 3) h).
    + rewrite (ltac:(f_equal; lia) : repB t = repB (3 * (t / 3) + 1)).
      rewrite repB_add. cbn [repB].
      exists (w2 *> r').
      exact (runEv_append (runEv_w0_B3q (t / 3) h) (runEv_single (stepEv_w0_B r'))).
    + rewrite (ltac:(f_equal; lia) : repB t = repB (3 * (t / 3) + 2)).
      rewrite repB_add. cbn [repB].
      exists (w3 *> r').
      exact (runEv_append (runEv_w0_B3q (t / 3) h)
        (RunEv_cons (stepEv_w0_B r') (runEv_single (stepEv_w2_B r')))).
  - destruct t as [| t']; [exists (w4 *> r); exact (RunEv_nil _) |].
    cbn [step1TailEv] in h.
    inversion h as [| ? ? ? r1 ? hS hrest]; subst.
    cbn [repB].
    assert (hrem : t' mod 3 = 0 \/ t' mod 3 = 1 \/ t' mod 3 = 2) by lia.
    destruct hrem as [h0 | [h1 | h2]].
    + rewrite (ltac:(f_equal; lia) : repB t' = repB (3 * (t' / 3))).
      exists (w0 *> r').
      exact (RunEv_cons (stepEv_w4_B hS) (runEv_w0_B3q (t' / 3) hrest)).
    + rewrite (ltac:(f_equal; lia) : repB t' = repB (3 * (t' / 3) + 1)).
      rewrite repB_add. cbn [repB].
      exists (w2 *> r').
      exact (RunEv_cons (stepEv_w4_B hS)
        (runEv_append (runEv_w0_B3q (t' / 3) hrest) (runEv_single (stepEv_w0_B r')))).
    + rewrite (ltac:(f_equal; lia) : repB t' = repB (3 * (t' / 3) + 2)).
      rewrite repB_add. cbn [repB].
      exists (w3 *> r').
      exact (RunEv_cons (stepEv_w4_B hS)
        (runEv_append (runEv_w0_B3q (t' / 3) hrest)
          (RunEv_cons (stepEv_w0_B r') (runEv_single (stepEv_w2_B r'))))).
  - cbn [step1TailEv] in h.
    exists (w1 *> r'). exact (runEv_w1_Bk t h).
  - destruct t as [| t']; [exists (wE *> r); exact (RunEv_nil _) |].
    cbn [step1TailEv repB] in h |- *.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS h2]; subst.
    inversion h2 as [| ? ? ? r3 ? hB2 hrest]; subst.
    exists (w1 *> r').
    exact (RunEv_cons (stepEv_wE_B hB1 hS hB2) (runEv_w1_Bk t' hrest)).
Qed.

Lemma lift1_run (st : St1) (gs : list nat) (t : nat) (hs : Safe1 st gs)
    {r r' : side} (h : RunEv (run1Evs st gs t) r r') :
  exists r_out, RunEv (gapsEv gs ++ repB t) (tok1 st *> r) r_out.
Proof.
  revert st r hs h.
  induction gs as [| g rest IH]; intros st r hs h.
  - cbn [gapsEv List.app]. exact (lift1_tail st t h).
  - destruct hs as [hg hrest].
    cbn [run1Evs] in h.
    destruct (runEv_prefix h) as [r1 [hstep htail]].
    pose proof (lift1_step st g hg hstep) as hl.
    destruct (IH (fst (step1 st 0 g)) r1 hrest htail) as [r_out hrest_run].
    exists r_out. cbn [gapsEv]. rewrite <- app_assoc.
    exact (runEv_append hl hrest_run).
Qed.

Definition Inv1 (st : St1) (c : nat) (po pi : rat) : Prop :=
  (0 <= po)%Q /\ (0 <= pi)%Q /\
  match st with
  | s0 => c = 0 /\ (3 * po <= pi)%Q
  | s4 => (2 <= pi)%Q /\ (3 * Q_of_nat c + po <= pi - 2)%Q /\ (2 * po <= 3 * Q_of_nat c + 3)%Q
  | s1 => (1 <= pi)%Q /\ (3 * Q_of_nat c + po <= pi - 1)%Q
  | sE => (3 * Q_of_nat c + po <= 3 * pi + (3 # 2))%Q /\ (2 * po <= 3 * Q_of_nat c + 6)%Q
  end.

Lemma inv1_step (st : St1) (c g : nat) (po pi : rat)
    (hinv : Inv1 st c po pi) (hgood : (2 * pi <= 3 * Q_of_nat g + 3)%Q)
    (hgE : st = sE -> 1 <= g) :
  (st = s4 \/ st = sE -> 1 <= g) /\
  AdjGoodFrom po (snd (snd (step1 st c g))) /\
  Inv1 (fst (step1 st c g)) (fst (snd (step1 st c g)))
    (endP po (snd (snd (step1 st c g)))) (nextP pi g).
Proof.
  destruct hinv as [hpo0 [hpi0 hst]].
  destruct st.
  - destruct hst as [-> hle].
    assert (hrem : g mod 3 = 0 \/ g mod 3 = 1 \/ g mod 3 = 2) by lia.
    pose proof (Q_of_nat_nonneg (g / 3)) as hq0.
    pose proof (Q_of_nat_nonneg g) as hg0.
    destruct hrem as [h0 | [h1 | h2]].
    + pose proof (Q_of_nat_lin g (g / 3) 0 ltac:(lia)) as hqQ.
      change (Q_of_nat 0) with 0%Q in hqQ.
      cbn [step1]; rewrite h0; cbn [Nat.eqb fst snd Nat.add endP AdjGoodFrom Inv1]; unfold nextP.
      repeat split; try (intros [H | H]; discriminate); try exact I; qlra.
    + pose proof (Q_of_nat_lin g (g / 3) 1 ltac:(lia)) as hqQ.
      change (Q_of_nat 1) with 1%Q in hqQ.
      cbn [step1]; rewrite h1; cbn [Nat.eqb fst snd Nat.add endP AdjGoodFrom Inv1]; unfold nextP.
      repeat split; try (intros [H | H]; discriminate); try exact I; qlra.
    + pose proof (Q_of_nat_lin g (g / 3) 2 ltac:(lia)) as hqQ.
      change (Q_of_nat 2) with 2%Q in hqQ.
      cbn [step1]; rewrite h2; cbn [Nat.eqb fst snd Nat.add endP AdjGoodFrom Inv1]; unfold nextP.
      repeat split; try (intros [H | H]; discriminate); try exact I; qlra.
  - destruct hst as [hpi2 [hcp hpo_adj]].
    destruct g as [| g'].
    + change (Q_of_nat 0) with 0%Q in hgood. exfalso. qlra.
    + pose proof (Q_of_nat_S g') as hgQ.
      pose proof (Q_of_nat_nonneg c) as hc0.
      pose proof (Q_of_nat_nonneg (g' / 3)) as hq0.
      assert (hrem : g' mod 3 = 0 \/ g' mod 3 = 1 \/ g' mod 3 = 2) by lia.
      destruct hrem as [h0 | [h1 | h2]].
      * pose proof (Q_of_nat_lin g' (g' / 3) 0 ltac:(lia)) as hqQ.
        change (Q_of_nat 0) with 0%Q in hqQ.
        cbn [step1]; rewrite h0; cbn [Nat.eqb fst snd endP AdjGoodFrom Inv1]; unfold nextP.
        repeat split; try (intros _; lia); try exact I; qlra.
      * pose proof (Q_of_nat_lin g' (g' / 3) 1 ltac:(lia)) as hqQ.
        change (Q_of_nat 1) with 1%Q in hqQ.
        cbn [step1]; rewrite h1; cbn [Nat.eqb fst snd endP AdjGoodFrom Inv1]; unfold nextP.
        repeat split; try (intros _; lia); try exact I; qlra.
      * pose proof (Q_of_nat_lin g' (g' / 3) 2 ltac:(lia)) as hqQ.
        change (Q_of_nat 2) with 2%Q in hqQ.
        cbn [step1]; rewrite h2; cbn [Nat.eqb fst snd endP AdjGoodFrom Inv1]; unfold nextP.
        repeat split; try (intros _; lia); try exact I; qlra.
  - destruct hst as [hpi1 hcp].
    pose proof (Q_of_nat_nonneg g) as hg0.
    pose proof (Q_of_nat_nonneg c) as hc0.
    pose proof (Q_of_nat_add c g) as hcg.
    cbn [step1 fst snd endP AdjGoodFrom Inv1]; unfold nextP.
    repeat split; try (intros [H | H]; discriminate); try exact I; qlra.
  - destruct hst as [hcp hpo_adj].
    destruct g as [| g'].
    + exfalso. specialize (hgE eq_refl). lia.
    + pose proof (Q_of_nat_S g') as hgQ.
      pose proof (Q_of_nat_nonneg g') as hg'0.
      pose proof (Q_of_nat_nonneg c) as hc0.
      pose proof (Q_of_nat_add c 1) as hc1.
      change (Q_of_nat 1) with 1%Q in hc1.
      cbn [step1 fst snd endP AdjGoodFrom Inv1]; unfold nextP.
      repeat split; try (intros _; lia); try exact I; qlra.
Qed.

Lemma inv1_run (st : St1) (c : nat) (gs : list nat) (po pi : rat)
    (hinv : Inv1 st c po pi) (hgood : AdjGoodFrom pi gs)
    (hsafeE : Safe1 st gs) :
  AdjGoodFrom po (snd (snd (run1Aux st c gs))) /\
  Inv1 (fst (run1Aux st c gs)) (fst (snd (run1Aux st c gs)))
    (endP po (snd (snd (run1Aux st c gs)))) (endP pi gs).
Proof.
  revert st c po pi hinv hgood hsafeE.
  induction gs as [| g rest IH]; intros st c po pi hinv hgood hsafeE.
  - cbn [run1Aux fst snd endP AdjGoodFrom]. exact (conj I hinv).
  - destruct hgood as [h1 hrest_g].
    destruct hsafeE as [hg_s hrest_s].
    destruct (inv1_step st c g po pi hinv h1 (fun heq => hg_s (or_intror heq)))
      as [_ [h_ag_em h_inv1]].
    cbn [run1Aux fst snd].
    rewrite <- (step1_next_indep_c st c g) in hrest_s.
    destruct (IH (fst (step1 st c g)) (fst (snd (step1 st c g)))
      (endP po (snd (snd (step1 st c g)))) (nextP pi g) h_inv1 hrest_g hrest_s)
      as [h_ag_r h_inv_r].
    split.
    + exact (adjGood_append h_ag_em h_ag_r).
    + rewrite endP_append. exact h_inv_r.
Qed.

Lemma inv1_tail (st : St1) (c t : nat) (po pi : rat) (hinv : Inv1 st c po pi) :
  AdjGoodFrom po (fst (step1Tail st c t)).
Proof.
  destruct hinv as [_ [_ hst]].
  destruct st.
  - exact I.
  - destruct t as [| t']; [exact I |].
    destruct hst as [_ [_ h_adj]]. exact (conj h_adj I).
  - exact I.
  - destruct t as [| t']; [exact I |].
    destruct hst as [_ h_adj].
    pose proof (Q_of_nat_add c 1) as hc1.
    change (Q_of_nat 1) with 1%Q in hc1.
    cbn [step1Tail fst AdjGoodFrom].
    split; [lra | exact I].
Qed.

Lemma inv1_full (st : St1) (c : nat) (gs : list nat) (t : nat) (po pi : rat)
    (hinv : Inv1 st c po pi) (hgood : AdjGoodFrom pi gs) (hsafe : Safe1 st gs) :
  AdjGoodFrom po (fst (run1Full st c gs t)).
Proof.
  destruct (inv1_run st c gs po pi hinv hgood hsafe) as [hag hinv'].
  unfold run1Full; cbn [fst].
  exact (adjGood_append hag (inv1_tail _ _ t _ _ hinv')).
Qed.

Lemma run1Aux_def_eq (st : St1) (c : nat) (gs : list nat) (hs : Safe1 st gs) :
  List.length (snd (snd (run1Aux st c gs))) + def1 (fst (run1Aux st c gs)) =
    List.length gs + def1 st.
Proof.
  revert st c hs.
  induction gs as [| g rest IH]; intros st c hs; [reflexivity |].
  destruct hs as [hg hrest].
  rewrite <- (step1_next_indep_c st c g) in hrest.
  pose proof (IH (fst (step1 st c g)) (fst (snd (step1 st c g))) hrest) as hih.
  cbn [run1Aux fst snd List.length]. rewrite length_app.
  assert (hstep : List.length (snd (snd (step1 st c g))) + def1 (fst (step1 st c g)) = 1 + def1 st).
  { destruct st.
    - cbn [step1 def1].
      destruct (Nat.eqb (g mod 3) 0); [reflexivity |].
      destruct (Nat.eqb (g mod 3) 1); reflexivity.
    - destruct g as [| g']; [exfalso; specialize (hg (or_introl eq_refl)); lia |].
      cbn [step1 def1].
      destruct (Nat.eqb (g' mod 3) 0); [reflexivity |].
      destruct (Nat.eqb (g' mod 3) 1); reflexivity.
    - reflexivity.
    - destruct g as [| g']; [exfalso; specialize (hg (or_intror eq_refl)); lia |].
      reflexivity. }
  lia.
Qed.

Lemma run1Aux_stay_base3_budget (st : St1) (c : nat) (gs : list nat) (hs : Safe1 st gs)
    (h_end : fst (run1Aux st c gs) = s0 \/ fst (run1Aux st c gs) = s4) :
  (st = s0 \/ st = s4) ->
  3 * (sum_list (snd (snd (run1Aux st c gs))) + fst (snd (run1Aux st c gs))) <=
    sum_list gs + 3 * c.
Proof.
  revert st c hs h_end.
  induction gs as [| g rest IH]; intros st c hs h_end hst0.
  - cbn [run1Aux fst snd sum_list]. lia.
  - destruct hs as [hg hrest].
    rewrite <- (step1_next_indep_c st c g) in hrest.
    assert (hnext_not_imm : forall st_cur c1, (st_cur = s1 \/ st_cur = sE) ->
      fst (run1Aux st_cur c1 rest) = s1 \/ fst (run1Aux st_cur c1 rest) = sE).
    { clear h_end IH hst0 hrest hg.
      induction rest as [| g2 rs2 IHr]; intros st_cur c1 hs1; [exact hs1 |].
      cbn [run1Aux fst]. apply IHr.
      destruct hs1 as [-> | ->]; [right; reflexivity | destruct g2; right; reflexivity]. }
    assert (hst1 : fst (step1 st c g) = s0 \/ fst (step1 st c g) = s4).
    { destruct (fst (step1 st c g)) eqn:hcase.
      - left; reflexivity.
      - right; reflexivity.
      - exfalso.
        pose proof (hnext_not_imm s1 (fst (snd (step1 st c g))) (or_introl eq_refl)) as hbad.
        cbn [run1Aux fst] in h_end. rewrite hcase in h_end.
        destruct h_end as [he | he]; destruct hbad as [hb | hb]; congruence.
      - exfalso.
        pose proof (hnext_not_imm sE (fst (snd (step1 st c g))) (or_intror eq_refl)) as hbad.
        cbn [run1Aux fst] in h_end. rewrite hcase in h_end.
        destruct h_end as [he | he]; destruct hbad as [hb | hb]; congruence. }
    cbn [run1Aux fst snd sum_list] in h_end |- *.
    pose proof (IH (fst (step1 st c g)) (fst (snd (step1 st c g))) hrest h_end hst1) as hih.
    rewrite sum_list_app.
    assert (hstep_b : 3 * (sum_list (snd (snd (step1 st c g))) + fst (snd (step1 st c g))) <= g + 3 * c).
    { destruct hst0 as [-> | ->].
      - cbn [step1].
        destruct (Nat.eqb (g mod 3) 0) eqn:e0; [cbn [fst snd sum_list]; lia |].
        destruct (Nat.eqb (g mod 3) 1) eqn:e1; cbn [fst snd sum_list]; lia.
      - destruct g as [| g']; [exfalso; specialize (hg (or_introl eq_refl)); lia |].
        cbn [step1].
        destruct (Nat.eqb (g' mod 3) 0) eqn:e0; [cbn [fst snd sum_list]; lia |].
        destruct (Nat.eqb (g' mod 3) 1) eqn:e1; cbn [fst snd sum_list]; lia. }
    lia.
Qed.

Lemma run1Full_from_s1_allPos (st : St1) (c : nat) (gs : list nat) (t : nat)
    (hst : st = s1 \/ st = sE) (hpos : forall x, In x gs -> 1 <= x) :
  forall x, In x (fst (run1Full st c gs t)) -> 1 <= x.
Proof.
  revert st c hst.
  induction gs as [| g rest IH]; intros st c hst x hx.
  - cbn [run1Full run1Aux fst snd List.app] in hx.
    destruct hst as [-> | ->].
    + inversion hx.
    + destruct t as [| t']; cbn [step1Tail fst In] in hx.
      * inversion hx.
      * destruct hx as [<- | []]; lia.
  - assert (hg : 1 <= g) by (apply hpos; left; reflexivity).
    assert (hrest_pos : forall y, In y rest -> 1 <= y) by (intros y hy; apply hpos; right; exact hy).
    unfold run1Full in hx; cbn [run1Aux fst snd] in hx.
    rewrite <- app_assoc in hx.
    destruct hst as [-> | ->].
    + cbn [step1 fst snd List.app] in hx.
      exact (IH hrest_pos sE (c + g) (or_intror eq_refl) x hx).
    + destruct g as [| g']; [lia |].
      cbn [step1 fst snd List.app In] in hx.
      destruct hx as [<- | hx']; [lia |].
      exact (IH hrest_pos sE (S g') (or_intror eq_refl) x hx').
Qed.

Lemma run1Full_from_s0_1_0_allPos (rest : list nat) (t : nat)
    (hpos : forall x, In x rest -> 1 <= x) :
  forall x, In x (fst (run1Full s0 0 (1 :: 0 :: rest) t)) -> 1 <= x.
Proof.
  assert (heq : run1Full s0 0 (1 :: 0 :: rest) t = run1Full sE 0 rest t).
  { reflexivity. }
  rewrite heq.
  exact (run1Full_from_s1_allPos sE 0 rest t (or_intror eq_refl) hpos).
Qed.

(* ========================================================================== *)
(* Section 6: 2-Cell Post-Entry Peeling Transducer (`peel2`)                  *)
(* ========================================================================== *)

Inductive St2 : Type :=
  | p01
  | p42
  | p0E
  | p41z
  | p41p
  | p5
  | p4E
  | p11
  | p1E
  | pE1.

Definition tok2 (st : St2) : list Sym :=
  match st with
  | p01 => w0 ++ w1
  | p42 => w4 ++ w2
  | p0E => w0 ++ wE
  | p41z => w4 ++ w1
  | p41p => w4 ++ w1
  | p5 => w5
  | p4E => w4 ++ wE
  | p11 => w1 ++ w1
  | p1E => w1 ++ wE
  | pE1 => wE ++ w1
  end.

Definition def2 (st : St2) : nat :=
  match st with
  | p01 => 1
  | p42 => 1
  | p0E => 2
  | p41z => 2
  | p41p => 2
  | p5 => 3
  | p4E => 3
  | p11 => 2
  | p1E => 3
  | pE1 => 3
  end.

Definition step2From0E (c g' : nat) : St2 * (nat * list nat) :=
  match g' with
  | 0 => (p5, (c, []))
  | 1 => (p1E, (c, []))
  | 2 => (p4E, (c, []))
  | _ =>
    if Nat.eqb (g' mod 3) 0 then (p0E, (g' / 3, [c + 1]))
    else if Nat.eqb (g' mod 3) 1 then (p11, (g' / 3, [c + 1]))
    else (p41p, (g' / 3, [c + 1]))
  end.

Definition step2From01 (c g' : nat) : St2 * (nat * list nat) :=
  if Nat.eqb (g' mod 3) 0 then (p0E, (c + g' / 3, []))
  else if Nat.eqb (g' mod 3) 1 then (p11, (c + g' / 3, []))
  else (p41z, (c + g' / 3, [])).

Definition step2 (st : St2) (c g : nat) : St2 * (nat * list nat) :=
  match st with
  | p01 => step2From01 c g
  | p42 =>
    match g with
    | 0 => (p42, (c, []))
    | S g' => step2From01 c g'
    end
  | p0E => step2From0E c g
  | p41z =>
    match g with
    | 0 => (p41z, (c, []))
    | S g' => step2From0E c g'
    end
  | p41p =>
    match g with
    | 0 => (p41p, (c, []))
    | S g' => step2From0E c g'
    end
  | p5 =>
    match g with
    | 0 => (p5, (c, []))
    | S g' =>
      let res := step2From0E 0 g' in
      (fst res, (fst (snd res), (c + 1) :: snd (snd res)))
    end
  | p4E =>
    match g with
    | 0 => (p4E, (c, []))
    | 1 => (p4E, (c, []))
    | S (S g') =>
      let res := step2From0E 0 g' in
      (fst res, (fst (snd res), (c + 1) :: snd (snd res)))
    end
  | p11 => (pE1, (c + g, []))
  | p1E =>
    match g with
    | 0 => (p1E, (c, []))
    | S g' => (pE1, (S g', [c + 1]))
    end
  | pE1 =>
    match g with
    | 0 => (pE1, (c, []))
    | S g' => (pE1, (S g', [c + 2]))
    end
  end.

Fixpoint run2Aux (st : St2) (c : nat) (gs : list nat) : St2 * (nat * list nat) :=
  match gs with
  | [] => (st, (c, []))
  | g :: gs' =>
    let r1 := step2 st c g in
    let r2 := run2Aux (fst r1) (fst (snd r1)) gs' in
    (fst r2, (fst (snd r2), snd (snd r1) ++ snd (snd r2)))
  end.

Definition step2Tail0E (c t : nat) : list nat * nat :=
  match t with
  | 0 | 1 | 2 => ([], c)
  | _ => ([c + 1], t / 3)
  end.

Definition step2Tail (st : St2) (c t : nat) : list nat * nat :=
  match st with
  | p01 => ([], c + t / 3)
  | p42 => match t with 0 => ([], c) | S t' => ([], c + t' / 3) end
  | p0E => step2Tail0E c t
  | p41z => match t with 0 => ([], c) | S t' => step2Tail0E c t' end
  | p41p => match t with 0 => ([], c) | S t' => step2Tail0E c t' end
  | p5 =>
    match t with
    | 0 => ([], c)
    | S t' =>
      let rt := step2Tail0E 0 t' in
      ((c + 1) :: fst rt, snd rt)
    end
  | p4E =>
    match t with
    | 0 | 1 => ([], c)
    | S (S t') =>
      let rt := step2Tail0E 0 t' in
      ((c + 1) :: fst rt, snd rt)
    end
  | p11 => ([], c + t)
  | p1E => match t with 0 => ([], c) | S t' => ([c + 1], S t') end
  | pE1 => match t with 0 => ([], c) | S t' => ([c + 2], S t') end
  end.

Definition run2Full (st : St2) (c : nat) (gs : list nat) (t : nat) : list nat * nat :=
  let r := run2Aux st c gs in
  let rt := step2Tail (fst r) (fst (snd r)) t in
  (snd (snd r) ++ fst rt, snd rt).

Definition step2From0EEv (g' : nat) : list Ev :=
  match g' with
  | 0 | 1 | 2 => []
  | _ => EvB :: EvS :: repB (g' / 3)
  end.

Definition step2Ev (st : St2) (g : nat) : list Ev :=
  match st with
  | p01 => repB (g / 3)
  | p42 => match g with 0 => [] | S g' => repB (g' / 3) end
  | p0E => step2From0EEv g
  | p41z => match g with 0 => [] | S g' => step2From0EEv g' end
  | p41p => match g with 0 => [] | S g' => step2From0EEv g' end
  | p5 => match g with 0 => [] | S g' => EvB :: EvS :: step2From0EEv g' end
  | p4E => match g with 0 | 1 => [] | S (S g') => EvB :: EvS :: step2From0EEv g' end
  | p11 => repB g
  | p1E => match g with 0 => [] | S g' => EvB :: EvS :: repB (S g') end
  | pE1 => match g with 0 => [] | S g' => EvB :: EvB :: EvS :: repB (S g') end
  end.

Definition step2Tail0EEv (t : nat) : list Ev :=
  match t with
  | 0 | 1 | 2 => []
  | _ => EvB :: EvS :: repB (t / 3)
  end.

Definition step2TailEv (st : St2) (t : nat) : list Ev :=
  match st with
  | p01 => repB (t / 3)
  | p42 => match t with 0 => [] | S t' => repB (t' / 3) end
  | p0E => step2Tail0EEv t
  | p41z => match t with 0 => [] | S t' => step2Tail0EEv t' end
  | p41p => match t with 0 => [] | S t' => step2Tail0EEv t' end
  | p5 => match t with 0 => [] | S t' => EvB :: EvS :: step2Tail0EEv t' end
  | p4E => match t with 0 | 1 => [] | S (S t') => EvB :: EvS :: step2Tail0EEv t' end
  | p11 => repB t
  | p1E => match t with 0 => [] | S t' => EvB :: EvS :: repB (S t') end
  | pE1 => match t with 0 => [] | S t' => EvB :: EvB :: EvS :: repB (S t') end
  end.

Fixpoint run2Evs (st : St2) (gs : list nat) (t : nat) : list Ev :=
  match gs with
  | [] => step2TailEv st t
  | g :: gs' => step2Ev st g ++ run2Evs (fst (step2 st 0 g)) gs' t
  end.

Lemma step2From01_next_indep (c g : nat) :
  fst (step2From01 c g) = fst (step2From01 0 g).
Proof.
  unfold step2From01.
  destruct (Nat.eqb (g mod 3) 0); [reflexivity |].
  destruct (Nat.eqb (g mod 3) 1); reflexivity.
Qed.

Lemma step2From0E_next_indep (c g : nat) :
  fst (step2From0E c g) = fst (step2From0E 0 g).
Proof.
  destruct g as [| [| [| g3]]]; [reflexivity | reflexivity | reflexivity |].
  cbn [step2From0E].
  destruct (Nat.eqb (S (S (S g3)) mod 3) 0); [reflexivity |].
  destruct (Nat.eqb (S (S (S g3)) mod 3) 1); reflexivity.
Qed.

Lemma step2_next_indep_c (st : St2) (c g : nat) :
  fst (step2 st c g) = fst (step2 st 0 g).
Proof.
  destruct st; cbn [step2].
  - exact (step2From01_next_indep c g).
  - destruct g as [| g']; [reflexivity | exact (step2From01_next_indep c g')].
  - exact (step2From0E_next_indep c g).
  - destruct g as [| g']; [reflexivity | exact (step2From0E_next_indep c g')].
  - destruct g as [| g']; [reflexivity | exact (step2From0E_next_indep c g')].
  - destruct g; reflexivity.
  - destruct g as [| [| g']]; reflexivity.
  - reflexivity.
  - destruct g; reflexivity.
  - destruct g; reflexivity.
Qed.

Lemma rep_B_step2From0E (c g' : nat) :
  repB c ++ step2From0EEv g' =
    gapsEv (snd (snd (step2From0E c g'))) ++ repB (fst (snd (step2From0E c g'))).
Proof.
  destruct g' as [| [| [| g'']]]; cbn [step2From0EEv step2From0E fst snd gapsEv List.app].
  - rewrite app_nil_r. reflexivity.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_nil_r. reflexivity.
  - destruct (Nat.eqb (S (S (S g'')) mod 3) 0);
    [| destruct (Nat.eqb (S (S (S g'')) mod 3) 1)];
    cbn [fst snd gapsEv List.app]; unfold gapEv;
    rewrite repB_add; cbn [repB List.app];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
Qed.

Lemma rep_B_step2From01 (c g' : nat) :
  repB c ++ repB (g' / 3) =
    gapsEv (snd (snd (step2From01 c g'))) ++ repB (fst (snd (step2From01 c g'))).
Proof.
  unfold step2From01.
  destruct (Nat.eqb (g' mod 3) 0);
  [| destruct (Nat.eqb (g' mod 3) 1)];
  cbn [fst snd gapsEv List.app]; rewrite repB_add; reflexivity.
Qed.

Lemma rep_B_step2Tail0E (c t : nat) :
  repB c ++ step2Tail0EEv t =
    gapsEv (fst (step2Tail0E c t)) ++ repB (snd (step2Tail0E c t)).
Proof.
  destruct t as [| [| [| t']]]; cbn [step2Tail0EEv step2Tail0E fst snd gapsEv List.app]; unfold gapEv.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_nil_r. reflexivity.
  - rewrite repB_add; cbn [repB List.app];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
Qed.

Definition minGap2 (st : St2) : nat :=
  match st with
  | p01 => 1
  | p42 => 3
  | p0E => 2
  | p41z => 1
  | p41p => 4
  | p5 => 1
  | p4E => 2
  | p11 => 1
  | p1E => 1
  | pE1 => 1
  end.

Lemma rep_B_step2Ev (st : St2) (c g : nat) (hg : minGap2 st <= g) :
  repB c ++ step2Ev st g =
    gapsEv (snd (snd (step2 st c g))) ++ repB (fst (snd (step2 st c g))).
Proof.
  destruct st.
  - exact (rep_B_step2From01 c g).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia | exact (rep_B_step2From01 c g')].
  - exact (rep_B_step2From0E c g).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia | exact (rep_B_step2From0E c g')].
  - destruct g as [| g']; [cbn [minGap2] in hg; lia | exact (rep_B_step2From0E c g')].
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [step2Ev step2 fst snd gapsEv]; unfold gapEv.
    pose proof (rep_B_step2From0E 0 g') as h0.
    cbn [repB List.app] in h0.
    rewrite repB_add; cbn [repB List.app].
    rewrite h0. repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - destruct g as [| [| g']]; [cbn [minGap2] in hg; lia | cbn [minGap2] in hg; lia |].
    cbn [step2Ev step2 fst snd gapsEv]; unfold gapEv.
    pose proof (rep_B_step2From0E 0 g') as h0.
    cbn [repB List.app] in h0.
    rewrite repB_add; cbn [repB List.app].
    rewrite h0. repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - cbn [step2Ev step2 fst snd gapsEv List.app]. rewrite repB_add. reflexivity.
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [step2Ev step2 fst snd gapsEv List.app]; unfold gapEv.
    rewrite repB_add; cbn [repB List.app];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [step2Ev step2 fst snd gapsEv List.app]; unfold gapEv.
    rewrite repB_add; cbn [repB List.app];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
Qed.

Lemma rep_B_step2TailEv (st : St2) (c t : nat) :
  repB c ++ step2TailEv st t =
    gapsEv (fst (step2Tail st c t)) ++ repB (snd (step2Tail st c t)).
Proof.
  destruct st.
  - cbn [step2TailEv step2Tail fst snd gapsEv List.app]. rewrite repB_add. reflexivity.
  - destruct t as [| t']; cbn [step2TailEv step2Tail fst snd gapsEv List.app].
    + rewrite app_nil_r. reflexivity.
    + rewrite repB_add. reflexivity.
  - exact (rep_B_step2Tail0E c t).
  - destruct t as [| t']; [cbn [step2TailEv step2Tail fst snd gapsEv]; rewrite app_nil_r; reflexivity |].
    exact (rep_B_step2Tail0E c t').
  - destruct t as [| t']; [cbn [step2TailEv step2Tail fst snd gapsEv]; rewrite app_nil_r; reflexivity |].
    exact (rep_B_step2Tail0E c t').
  - destruct t as [| t']; [cbn [step2TailEv step2Tail fst snd gapsEv]; rewrite app_nil_r; reflexivity |].
    cbn [step2TailEv step2Tail fst snd gapsEv]; unfold gapEv.
    pose proof (rep_B_step2Tail0E 0 t') as h0.
    cbn [repB List.app] in h0.
    rewrite repB_add; cbn [repB List.app].
    rewrite h0. repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - destruct t as [| [| t']];
    [cbn [step2TailEv step2Tail fst snd gapsEv]; rewrite app_nil_r; reflexivity
    | cbn [step2TailEv step2Tail fst snd gapsEv]; rewrite app_nil_r; reflexivity |].
    cbn [step2TailEv step2Tail fst snd gapsEv]; unfold gapEv.
    pose proof (rep_B_step2Tail0E 0 t') as h0.
    cbn [repB List.app] in h0.
    rewrite repB_add; cbn [repB List.app].
    rewrite h0. repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - cbn [step2TailEv step2Tail fst snd gapsEv List.app]. rewrite repB_add. reflexivity.
  - destruct t as [| t']; [cbn [step2TailEv step2Tail fst snd gapsEv]; rewrite app_nil_r; reflexivity |].
    cbn [step2TailEv step2Tail fst snd gapsEv List.app]; unfold gapEv.
    rewrite repB_add; cbn [repB List.app];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
  - destruct t as [| t']; [cbn [step2TailEv step2Tail fst snd gapsEv]; rewrite app_nil_r; reflexivity |].
    cbn [step2TailEv step2Tail fst snd gapsEv List.app]; unfold gapEv.
    rewrite repB_add; cbn [repB List.app];
    repeat rewrite app_nil_r; repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
Qed.

Fixpoint Safe2 (st : St2) (gs : list nat) : Prop :=
  match gs with
  | [] => True
  | g :: gs' => minGap2 st <= g /\ Safe2 (fst (step2 st 0 g)) gs'
  end.

Lemma rep_B_run2Evs (st : St2) (c : nat) (gs : list nat) (t : nat) (hs : Safe2 st gs) :
  repB c ++ run2Evs st gs t =
    gapsEv (fst (run2Full st c gs t)) ++ repB (snd (run2Full st c gs t)).
Proof.
  revert st c hs.
  induction gs as [| g rest IH]; intros st c hs.
  - cbn [run2Evs run2Full run2Aux fst snd List.app].
    exact (rep_B_step2TailEv st c t).
  - destruct hs as [hg hrest].
    cbn [run2Evs run2Full run2Aux fst snd].
    rewrite app_assoc, (rep_B_step2Ev st c g hg), <- app_assoc.
    rewrite <- (step2_next_indep_c st c g) in hrest |- *.
    pose proof (IH (fst (step2 st c g)) (fst (snd (step2 st c g))) hrest) as hih.
    unfold run2Full in hih.
    rewrite hih, app_assoc, <- gapsEv_append, <- app_assoc.
    reflexivity.
Qed.

Lemma lift2_01_step (g : nat) {r r' : side}
    (h : RunEv (repB (g / 3)) r r') :
  RunEv (gapEv g) (w0 *> w1 *> r) (tok2 (fst (step2From01 0 g)) *> r').
Proof.
  pose proof (runEv_w0_B3q (g / 3) (runEv_w1_Bk (g / 3) h)) as hb3.
  assert (hrem : g mod 3 = 0 \/ g mod 3 = 1 \/ g mod 3 = 2) by lia.
  destruct hrem as [h0 | [h1 | h2]]; unfold step2From01; rewrite ?h0, ?h1, ?h2;
    cbn [Nat.eqb fst tok2]; rewrite Str_app_assoc.
  - unfold gapEv. rewrite (ltac:(f_equal; lia) : repB g = repB (3 * (g / 3))).
    exact (runEv_append hb3 (runEv_single (stepEv_w0_S (stepEv_w1_S r')))).
  - unfold gapEv. rewrite (ltac:(f_equal; lia) : repB g = repB (3 * (g / 3) + 1)).
    rewrite repB_add, <- app_assoc. cbn [repB List.app].
    exact (runEv_append hb3 (RunEv_cons (stepEv_w0_B (w1 *> r'))
      (runEv_single (stepEv_w2_S (w1 *> r'))))).
  - unfold gapEv. rewrite (ltac:(f_equal; lia) : repB g = repB (3 * (g / 3) + 2)).
    rewrite repB_add, <- app_assoc. cbn [repB List.app].
    exact (runEv_append hb3
      (RunEv_cons (stepEv_w0_B (w1 *> r'))
        (RunEv_cons (stepEv_w2_B (w1 *> r')) (runEv_single (stepEv_w3_S (w1 *> r')))))).
Qed.

Lemma lift2_01_step_p (g : nat) {r r' : side}
    (h : RunEv (repB (g / 3)) r r') :
  RunEv (gapEv g) (w0 *> w1 *> r)
    (tok2 (if Nat.eqb (g mod 3) 0 then p0E else if Nat.eqb (g mod 3) 1 then p11 else p41p) *> r').
Proof.
  pose proof (lift2_01_step g h) as hb.
  assert (htok : tok2 (fst (step2From01 0 g)) =
    tok2 (if Nat.eqb (g mod 3) 0 then p0E else if Nat.eqb (g mod 3) 1 then p11 else p41p)).
  { unfold step2From01.
    destruct (Nat.eqb (g mod 3) 0); [reflexivity |].
    destruct (Nat.eqb (g mod 3) 1); reflexivity. }
  rewrite <- htok. exact hb.
Qed.

Lemma lift2_0E_step (g : nat) {r r' : side}
    (h : RunEv (step2From0EEv g) r r') :
  RunEv (gapEv g) (w0 *> wE *> r) (tok2 (fst (step2From0E 0 g)) *> r').
Proof.
  destruct g as [| [| [| g']]].
  - inversion h; subst. cbn [gapEv repB List.app step2From0E fst tok2].
    exact (runEv_single (stepEv_w0_wE_S _)).
  - inversion h; subst. cbn [gapEv repB List.app step2From0E fst tok2].
    rewrite Str_app_assoc.
    exact (RunEv_cons (stepEv_w0_B _) (runEv_single (stepEv_w2_S _))).
  - inversion h; subst. cbn [gapEv repB List.app step2From0E fst tok2].
    rewrite Str_app_assoc.
    exact (RunEv_cons (stepEv_w0_B _)
      (RunEv_cons (stepEv_w2_B _) (runEv_single (stepEv_w3_S _)))).
  - cbn [step2From0EEv] in h.
    rewrite (ltac:(f_equal; lia) : repB (S (S (S g')) / 3) = repB (S (g' / 3))) in h.
    cbn [repB] in h.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS h2]; subst.
    inversion h2 as [| ? ? ? r3 ? hB2 hrest]; subst.
    pose proof (RunEv_cons (stepEv_w0_B (wE *> r))
      (RunEv_cons (stepEv_w2_B (wE *> r))
        (runEv_single (stepEv_w3_B (stepEv_wE_B hB1 hS hB2))))) as hb3.
    change (gapEv (S (S (S g')))) with ([EvB; EvB; EvB] ++ gapEv g').
    pose proof (lift2_01_step_p g' hrest) as hlift.
    assert (hmod : S (S (S g')) mod 3 = g' mod 3) by lia.
    assert (hst_eq : fst (step2From0E 0 (S (S (S g')))) =
      (if Nat.eqb (g' mod 3) 0 then p0E else if Nat.eqb (g' mod 3) 1 then p11 else p41p)).
    { cbn [step2From0E]. rewrite hmod.
      destruct (Nat.eqb (g' mod 3) 0); [reflexivity |].
      destruct (Nat.eqb (g' mod 3) 1); reflexivity. }
    rewrite hst_eq.
    exact (runEv_append hb3 hlift).
Qed.

Lemma lift2_step (st : St2) (g : nat) (hg : minGap2 st <= g)
    {r r' : side} (h : RunEv (step2Ev st g) r r') :
  RunEv (gapEv g) (tok2 st *> r) (tok2 (fst (step2 st 0 g)) *> r').
Proof.
  destruct st.
  - cbn [tok2 step2 step2Ev] in *. rewrite Str_app_assoc. exact (lift2_01_step g h).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [tok2 step2 step2Ev] in *. rewrite Str_app_assoc.
    change (gapEv (S g')) with (EvB :: gapEv g').
    exact (RunEv_cons (stepEv_w4_B (stepEv_w2_S r)) (lift2_01_step g' h)).
  - cbn [tok2 step2 step2Ev] in *. rewrite Str_app_assoc. exact (lift2_0E_step g h).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [tok2 step2 step2Ev] in *. rewrite Str_app_assoc.
    change (gapEv (S g')) with (EvB :: gapEv g').
    exact (RunEv_cons (stepEv_w4_B (stepEv_w1_S r)) (lift2_0E_step g' h)).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [tok2 step2 step2Ev] in *. rewrite Str_app_assoc.
    change (gapEv (S g')) with (EvB :: gapEv g').
    exact (RunEv_cons (stepEv_w4_B (stepEv_w1_S r)) (lift2_0E_step g' h)).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [step2Ev] in h.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS hrest]; subst.
    cbn [tok2 step2 fst].
    change (gapEv (S g')) with (EvB :: gapEv g').
    exact (RunEv_cons (stepEv_w5_B hB1 hS) (lift2_0E_step g' hrest)).
  - destruct g as [| [| g']]; [cbn [minGap2] in hg; lia | cbn [minGap2] in hg; lia |].
    cbn [step2Ev] in h.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS hrest]; subst.
    cbn [tok2 step2 fst]. rewrite Str_app_assoc.
    change (gapEv (S (S g'))) with (EvB :: EvB :: gapEv g').
    exact (RunEv_cons (stepEv_w4_wE_B r)
      (RunEv_cons (stepEv_w5_B hB1 hS) (lift2_0E_step g' hrest))).
  - cbn [tok2 step2 step2Ev fst] in *. repeat rewrite Str_app_assoc. unfold gapEv.
    exact (runEv_append (runEv_w1_Bk g (runEv_w1_Bk g h)) (runEv_single (stepEv_w1_S (w1 *> r')))).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [step2Ev repB] in h.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS h2]; subst.
    inversion h2 as [| ? ? ? r3 ? hB2 hrest]; subst.
    cbn [tok2 step2 fst]. repeat rewrite Str_app_assoc.
    change (gapEv (S g')) with (EvB :: (repB g' ++ [EvS])).
    exact (RunEv_cons (stepEv_w1_B (stepEv_wE_B hB1 hS hB2))
      (runEv_append (runEv_w1_Bk g' (runEv_w1_Bk g' hrest))
        (runEv_single (stepEv_w1_S (w1 *> r'))))).
  - destruct g as [| g']; [cbn [minGap2] in hg; lia |].
    cbn [step2Ev repB] in h.
    inversion h as [| ? ? ? r1 ? hB0 h0]; subst.
    inversion h0 as [| ? ? ? r2 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r3 ? hS h2]; subst.
    inversion h2 as [| ? ? ? r4 ? hB2 hrest]; subst.
    cbn [tok2 step2 fst]. repeat rewrite Str_app_assoc.
    pose proof (stepEv_wE_B (stepEv_w1_B hB0) (stepEv_w1_S r1) (stepEv_wE_B hB1 hS hB2)) as hs1.
    change (gapEv (S g')) with (EvB :: (repB g' ++ [EvS])).
    exact (RunEv_cons hs1
      (runEv_append (runEv_w1_Bk g' (runEv_w1_Bk g' hrest))
        (runEv_single (stepEv_w1_S (w1 *> r'))))).
Qed.

Lemma lift2_01_tail (t : nat) {r r' : side}
    (h : RunEv (repB (t / 3)) r r') :
  exists r_out, RunEv (repB t) (w0 *> w1 *> r) r_out.
Proof.
  pose proof (runEv_w0_B3q (t / 3) (runEv_w1_Bk (t / 3) h)) as hb3.
  assert (hrem : t mod 3 = 0 \/ t mod 3 = 1 \/ t mod 3 = 2) by lia.
  destruct hrem as [h0 | [h1 | h2]].
  - rewrite (ltac:(f_equal; lia) : repB t = repB (3 * (t / 3))).
    exists (w0 *> w1 *> r'). exact hb3.
  - rewrite (ltac:(f_equal; lia) : repB t = repB (3 * (t / 3) + 1)).
    rewrite repB_add. cbn [repB].
    exists (w2 *> w1 *> r').
    exact (runEv_append hb3 (runEv_single (stepEv_w0_B (w1 *> r')))).
  - rewrite (ltac:(f_equal; lia) : repB t = repB (3 * (t / 3) + 2)).
    rewrite repB_add. cbn [repB].
    exists (w3 *> w1 *> r').
    exact (runEv_append hb3
      (RunEv_cons (stepEv_w0_B (w1 *> r')) (runEv_single (stepEv_w2_B (w1 *> r'))))).
Qed.

Lemma lift2_0E_tail (t : nat) {r r' : side}
    (h : RunEv (step2Tail0EEv t) r r') :
  exists r_out, RunEv (repB t) (w0 *> wE *> r) r_out.
Proof.
  destruct t as [| [| [| t']]].
  - exists (w0 *> wE *> r). exact (RunEv_nil _).
  - exists (w2 *> wE *> r). exact (runEv_single (stepEv_w0_B (wE *> r))).
  - exists (w3 *> wE *> r).
    exact (RunEv_cons (stepEv_w0_B (wE *> r)) (runEv_single (stepEv_w2_B (wE *> r)))).
  - cbn [step2Tail0EEv] in h.
    rewrite (ltac:(f_equal; lia) : repB (S (S (S t')) / 3) = repB (S (t' / 3))) in h.
    cbn [repB] in h.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS h2]; subst.
    inversion h2 as [| ? ? ? r3 ? hB2 hrest]; subst.
    pose proof (RunEv_cons (stepEv_w0_B (wE *> r))
      (RunEv_cons (stepEv_w2_B (wE *> r))
        (runEv_single (stepEv_w3_B (stepEv_wE_B hB1 hS hB2))))) as hb3.
    destruct (lift2_01_tail t' hrest) as [r_out hr_out].
    change (repB (S (S (S t')))) with ([EvB; EvB; EvB] ++ repB t').
    exists r_out. exact (runEv_append hb3 hr_out).
Qed.

Lemma lift2_tail (st : St2) (t : nat) {r r' : side}
    (h : RunEv (step2TailEv st t) r r') :
  exists r_out, RunEv (repB t) (tok2 st *> r) r_out.
Proof.
  destruct st.
  - cbn [tok2 step2TailEv] in *. rewrite Str_app_assoc. exact (lift2_01_tail t h).
  - destruct t as [| t']; [exists (tok2 p42 *> r); exact (RunEv_nil _) |].
    cbn [tok2 step2TailEv repB] in *. rewrite Str_app_assoc.
    destruct (lift2_01_tail t' h) as [r_out hr_out].
    exists r_out. exact (RunEv_cons (stepEv_w4_B (stepEv_w2_S r)) hr_out).
  - cbn [tok2 step2TailEv] in *. rewrite Str_app_assoc. exact (lift2_0E_tail t h).
  - destruct t as [| t']; [exists (tok2 p41z *> r); exact (RunEv_nil _) |].
    cbn [tok2 step2TailEv repB] in *. rewrite Str_app_assoc.
    destruct (lift2_0E_tail t' h) as [r_out hr_out].
    exists r_out. exact (RunEv_cons (stepEv_w4_B (stepEv_w1_S r)) hr_out).
  - destruct t as [| t']; [exists (tok2 p41p *> r); exact (RunEv_nil _) |].
    cbn [tok2 step2TailEv repB] in *. rewrite Str_app_assoc.
    destruct (lift2_0E_tail t' h) as [r_out hr_out].
    exists r_out. exact (RunEv_cons (stepEv_w4_B (stepEv_w1_S r)) hr_out).
  - destruct t as [| t']; [exists (tok2 p5 *> r); exact (RunEv_nil _) |].
    cbn [step2TailEv] in h.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS hrest]; subst.
    destruct (lift2_0E_tail t' hrest) as [r_out hr_out].
    cbn [tok2 repB].
    exists r_out. exact (RunEv_cons (stepEv_w5_B hB1 hS) hr_out).
  - destruct t as [| [| t']].
    + exists (tok2 p4E *> r). exact (RunEv_nil _).
    + cbn [tok2 repB]. rewrite Str_app_assoc.
      exists (w5 *> r). exact (runEv_single (stepEv_w4_wE_B r)).
    + cbn [step2TailEv] in h.
      inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
      inversion h1 as [| ? ? ? r2 ? hS hrest]; subst.
      destruct (lift2_0E_tail t' hrest) as [r_out hr_out].
      cbn [tok2 repB]. rewrite Str_app_assoc.
      exists r_out.
      exact (RunEv_cons (stepEv_w4_wE_B r) (RunEv_cons (stepEv_w5_B hB1 hS) hr_out)).
  - cbn [tok2 step2TailEv] in *. rewrite Str_app_assoc.
    exists (w1 *> w1 *> r'). exact (runEv_w1_Bk t (runEv_w1_Bk t h)).
  - destruct t as [| t']; [exists (tok2 p1E *> r); exact (RunEv_nil _) |].
    cbn [step2TailEv repB] in h |- *.
    inversion h as [| ? ? ? r1 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r2 ? hS h2]; subst.
    inversion h2 as [| ? ? ? r3 ? hB2 hrest]; subst.
    cbn [tok2]. rewrite Str_app_assoc.
    exists (w1 *> w1 *> r').
    exact (RunEv_cons (stepEv_w1_B (stepEv_wE_B hB1 hS hB2))
      (runEv_w1_Bk t' (runEv_w1_Bk t' hrest))).
  - destruct t as [| t']; [exists (tok2 pE1 *> r); exact (RunEv_nil _) |].
    cbn [step2TailEv repB] in h |- *.
    inversion h as [| ? ? ? r1 ? hB0 h0]; subst.
    inversion h0 as [| ? ? ? r2 ? hB1 h1]; subst.
    inversion h1 as [| ? ? ? r3 ? hS h2]; subst.
    inversion h2 as [| ? ? ? r4 ? hB2 hrest]; subst.
    cbn [tok2]. rewrite Str_app_assoc.
    pose proof (stepEv_wE_B (stepEv_w1_B hB0) (stepEv_w1_S r1) (stepEv_wE_B hB1 hS hB2)) as hs1.
    exists (w1 *> w1 *> r').
    exact (RunEv_cons hs1 (runEv_w1_Bk t' (runEv_w1_Bk t' hrest))).
Qed.

Lemma lift2_run (st : St2) (gs : list nat) (t : nat) (hs : Safe2 st gs)
    {r r' : side} (h : RunEv (run2Evs st gs t) r r') :
  exists r_out, RunEv (gapsEv gs ++ repB t) (tok2 st *> r) r_out.
Proof.
  revert st r hs h.
  induction gs as [| g rest IH]; intros st r hs h.
  - cbn [gapsEv List.app]. exact (lift2_tail st t h).
  - destruct hs as [hg hrest].
    cbn [run2Evs] in h.
    destruct (runEv_prefix h) as [r1 [hstep htail]].
    pose proof (lift2_step st g hg hstep) as hl.
    destruct (IH (fst (step2 st 0 g)) r1 hrest htail) as [r_out hrest_run].
    exists r_out. cbn [gapsEv]. rewrite <- app_assoc.
    exact (runEv_append hl hrest_run).
Qed.

Definition Inv2 (st : St2) (c : nat) (po pi : rat) : Prop :=
  (0 <= po)%Q /\ (0 <= pi)%Q /\
  match st with
  | p01 => c = 0 /\ (po == 0)%Q /\ (3 <= pi)%Q
  | p42 => c = 0 /\ (po == 0)%Q /\ (5 <= pi)%Q
  | p0E => 1 <= c /\ (3 * Q_of_nat c + po <= pi + (3 # 2))%Q /\
           (3 * Q_of_nat c + (1 # 3) <= pi)%Q /\ (2 * po <= 3 * Q_of_nat c + 6)%Q
  | p41z => (po == 0)%Q /\ (3 * Q_of_nat c + 3 <= pi)%Q
  | p41p => 1 <= c /\ (3 * Q_of_nat c + po <= pi - (1 # 2))%Q /\
            (3 * Q_of_nat c + (28 # 9) <= pi)%Q /\ (2 * po <= 3 * Q_of_nat c + 6)%Q
  | p5 => c = 0 /\ (po <= 3)%Q /\ (po <= pi)%Q /\ (1 <= pi)%Q
  | p4E => c <= 1 /\ (po <= 3)%Q /\ (3 * Q_of_nat c + po <= 6)%Q /\
           (3 * Q_of_nat c + po <= pi + (5 # 2))%Q /\ ((28 # 9) <= pi)%Q
  | p11 => (3 * Q_of_nat c + po <= pi + (1 # 2))%Q
  | p1E => c = 0 /\ (po <= 3)%Q /\ (po <= pi - 1)%Q
  | pE1 => (3 * Q_of_nat c + po <= 3 * pi + 3)%Q /\ (2 * po <= 3 * Q_of_nat c + 9)%Q
  end.

Ltac close_em_pos :=
  intros ? Hx; cbn [In] in Hx;
  repeat (destruct Hx as [<- | Hx]; [lia |]); contradiction.

Lemma step2From0E_ge3 (c g' : nat) :
  step2From0E c (S (S (S g'))) =
  (if Nat.eqb (S (S (S g')) mod 3) 0 then (p0E, (S (S (S g')) / 3, [c + 1]))
   else if Nat.eqb (S (S (S g')) mod 3) 1 then (p11, (S (S (S g')) / 3, [c + 1]))
   else (p41p, (S (S (S g')) / 3, [c + 1]))).
Proof. reflexivity. Qed.

Lemma inv2_step (st : St2) (c g : nat) (po pi : rat)
    (hinv : Inv2 st c po pi) (hgpos : 1 <= g) (hgood : (2 * pi <= 3 * Q_of_nat g + 3)%Q) :
  minGap2 st <= g /\
  (forall x, In x (snd (snd (step2 st c g))) -> 1 <= x) /\
  List.length (snd (snd (step2 st c g))) + def2 (fst (step2 st c g)) = 1 + def2 st /\
  AdjGoodFrom po (snd (snd (step2 st c g))) /\
  Inv2 (fst (step2 st c g)) (fst (snd (step2 st c g)))
    (endP po (snd (snd (step2 st c g)))) (nextP pi g).
Proof.
  destruct hinv as [hpo0 [hpi0 hst]].
  pose proof (Q_of_nat_nonneg g) as hgQ0.
  pose proof (Q_of_nat_nonneg c) as hcQ0.
  destruct st.
  - (* p01 *)
    destruct hst as [-> [hpo_eq hpi3]].
    assert (hrem : g mod 3 = 0 \/ g mod 3 = 1 \/ g mod 3 = 2) by lia.
    pose proof (Q_of_nat_nonneg (g / 3)) as hq0.
    destruct hrem as [h0 | [h1 | h2]].
    + assert (hq_pos : 1 <= g / 3) by lia.
      pose proof (Q_of_nat_lin g (g / 3) 0 ltac:(lia)) as hqQ.
      change (Q_of_nat 0) with 0%Q in hqQ.
      cbn [minGap2 step2]; unfold step2From01; rewrite h0;
        cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + pose proof (Q_of_nat_lin g (g / 3) 1 ltac:(lia)) as hqQ.
      change (Q_of_nat 1) with 1%Q in hqQ.
      cbn [minGap2 step2]; unfold step2From01; rewrite h1;
        cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + pose proof (Q_of_nat_lin g (g / 3) 2 ltac:(lia)) as hqQ.
      change (Q_of_nat 2) with 2%Q in hqQ.
      cbn [minGap2 step2]; unfold step2From01; rewrite h2;
        cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
  - (* p42 *)
    destruct hst as [-> [hpo_eq hpi5]].
    assert (hg3 : 3 <= g).
    { destruct (Nat.lt_ge_cases g 3) as [hlt | hge]; [| exact hge].
      exfalso. pose proof (Q_of_nat_le g 2 ltac:(lia)) as hle2.
      change (Q_of_nat 2) with 2%Q in hle2. qlra. }
    destruct g as [| g']; [lia |].
    pose proof (Q_of_nat_S g') as hgQ.
    pose proof (Q_of_nat_nonneg (g' / 3)) as hq0.
    assert (hrem : g' mod 3 = 0 \/ g' mod 3 = 1 \/ g' mod 3 = 2) by lia.
    destruct hrem as [h0 | [h1 | h2]].
    + assert (hq_pos : 1 <= g' / 3) by lia.
      pose proof (Q_of_nat_lin g' (g' / 3) 0 ltac:(lia)) as hqQ.
      change (Q_of_nat 0) with 0%Q in hqQ.
      cbn [minGap2 step2]; unfold step2From01; rewrite h0;
        cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + pose proof (Q_of_nat_lin g' (g' / 3) 1 ltac:(lia)) as hqQ.
      change (Q_of_nat 1) with 1%Q in hqQ.
      cbn [minGap2 step2]; unfold step2From01; rewrite h1;
        cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + pose proof (Q_of_nat_lin g' (g' / 3) 2 ltac:(lia)) as hqQ.
      change (Q_of_nat 2) with 2%Q in hqQ.
      cbn [minGap2 step2]; unfold step2From01; rewrite h2;
        cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
  - (* p0E *)
    destruct hst as [hc1 [hW [hpi_lb hpo_adj]]].
    pose proof (Q_of_nat_le 1 c hc1) as hc1Q.
    change (Q_of_nat 1) with 1%Q in hc1Q.
    assert (hg2 : 2 <= g).
    { destruct (Nat.lt_ge_cases g 2) as [hlt | hge]; [| exact hge].
      exfalso. pose proof (Q_of_nat_le g 1 ltac:(lia)) as hle1.
      change (Q_of_nat 1) with 1%Q in hle1. qlra. }
    destruct g as [| [| [| g']]]; [lia | lia | |].
    + (* g = 2 *)
      assert (hc_eq1 : c = 1).
      { destruct (Nat.lt_ge_cases c 2) as [hlt | hge]; [lia |].
        exfalso. pose proof (Q_of_nat_le 2 c hge) as hc2Q.
        change (Q_of_nat 2) with 2%Q in hc2Q, hgood. qlra. }
      subst c. change (Q_of_nat 1) with 1%Q in *. change (Q_of_nat 2) with 2%Q in *.
      cbn [minGap2 step2 step2From0E fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP;
        change (Q_of_nat 1) with 1%Q; change (Q_of_nat 2) with 2%Q.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + (* g = S (S (S g')) >= 3 *)
      cbn [minGap2 step2]; rewrite step2From0E_ge3.
      set (n := S (S (S g'))) in *.
      pose proof (Q_of_nat_add c 1) as hc1_eq.
      assert (hq_pos : 1 <= n / 3) by (unfold n; lia).
      pose proof (Q_of_nat_nonneg (n / 3)) as hq0.
      assert (hrem : n mod 3 = 0 \/ n mod 3 = 1 \/ n mod 3 = 2) by lia.
      destruct hrem as [h0 | [h1 | h2]].
      * pose proof (Q_of_nat_lin n (n / 3) 0 ltac:(lia)) as hqQ.
        rewrite h0; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold n; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin n (n / 3) 1 ltac:(lia)) as hqQ.
        rewrite h1; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold n; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin n (n / 3) 2 ltac:(lia)) as hqQ.
        rewrite h2; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold n; lia); try close_em_pos; try exact I; qlra.
  - (* p41z *)
    destruct hst as [hpo_eq hpi_lb].
    destruct g as [| [| [| [| g']]]]; [lia | | | |].
    + (* g = 1 *)
      assert (hc0 : c = 0).
      { destruct c as [| c']; [reflexivity |].
        exfalso. pose proof (Q_of_nat_le 1 (S c') ltac:(lia)) as hc1Q. qlra. }
      subst c.
      cbn [minGap2 step2 step2From0E fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + (* g = 2 *)
      assert (hc0 : c = 0).
      { destruct c as [| c']; [reflexivity |].
        exfalso. pose proof (Q_of_nat_le 1 (S c') ltac:(lia)) as hc1Q. qlra. }
      subst c.
      cbn [minGap2 step2 step2From0E fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + (* g = 3 *)
      assert (hc_le1 : c <= 1).
      { destruct (Nat.lt_ge_cases c 2) as [hlt | hge]; [lia |].
        exfalso. pose proof (Q_of_nat_le 2 c hge) as hc2Q. qlra. }
      pose proof (Q_of_nat_le c 1 hc_le1) as hcQ1.
      cbn [minGap2 step2 step2From0E fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + (* g = S m where m = S (S (S g')) *)
      cbn [minGap2 step2]; rewrite step2From0E_ge3.
      set (m := S (S (S g'))) in *.
      pose proof (Q_of_nat_S m) as hsmQ.
      pose proof (Q_of_nat_add c 1) as hc1_eq.
      assert (hq_pos : 1 <= m / 3) by (unfold m; lia).
      pose proof (Q_of_nat_nonneg (m / 3)) as hq0.
      assert (hrem : m mod 3 = 0 \/ m mod 3 = 1 \/ m mod 3 = 2) by lia.
      destruct hrem as [h0 | [h1 | h2]].
      * pose proof (Q_of_nat_lin m (m / 3) 0 ltac:(lia)) as hqQ.
        rewrite h0; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin m (m / 3) 1 ltac:(lia)) as hqQ.
        rewrite h1; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin m (m / 3) 2 ltac:(lia)) as hqQ.
        rewrite h2; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
  - (* p41p *)
    destruct hst as [hc1 [hW [hpi_lb hpo_adj]]].
    pose proof (Q_of_nat_le 1 c hc1) as hc1Q.
    assert (hg4 : 4 <= g).
    { destruct (Nat.lt_ge_cases g 4) as [hlt | hge]; [| exact hge].
      exfalso. pose proof (Q_of_nat_le g 3 ltac:(lia)) as hle3. qlra. }
    destruct g as [| [| [| [| g']]]]; [lia | lia | lia | lia |].
    cbn [minGap2 step2]; rewrite step2From0E_ge3.
    set (m := S (S (S g'))) in *.
    pose proof (Q_of_nat_S m) as hsmQ.
    pose proof (Q_of_nat_add c 1) as hc1_eq.
    assert (hq_pos : 1 <= m / 3) by (unfold m; lia).
    pose proof (Q_of_nat_nonneg (m / 3)) as hq0.
    assert (hrem : m mod 3 = 0 \/ m mod 3 = 1 \/ m mod 3 = 2) by lia.
    destruct hrem as [h0 | [h1 | h2]].
    + pose proof (Q_of_nat_lin m (m / 3) 0 ltac:(lia)) as hqQ.
      rewrite h0; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
    + pose proof (Q_of_nat_lin m (m / 3) 1 ltac:(lia)) as hqQ.
      rewrite h1; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
    + pose proof (Q_of_nat_lin m (m / 3) 2 ltac:(lia)) as hqQ.
      rewrite h2; cbn [Nat.eqb fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
      repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
  - (* p5 *)
    destruct hst as [-> [hpo3 [hW hpi1]]].
    destruct g as [| [| [| [| g']]]]; [lia | | | |].
    + cbn [minGap2 step2 step2From0E fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2];
        unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + cbn [minGap2 step2 step2From0E fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2];
        unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + cbn [minGap2 step2 step2From0E fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2];
        unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + cbn [minGap2 step2 Nat.add]; rewrite step2From0E_ge3.
      set (m := S (S (S g'))) in *.
      pose proof (Q_of_nat_S m) as hsmQ.
      assert (hq_pos : 1 <= m / 3) by (unfold m; lia).
      pose proof (Q_of_nat_le 1 (m / 3) hq_pos) as hq1Q.
      assert (hrem : m mod 3 = 0 \/ m mod 3 = 1 \/ m mod 3 = 2) by lia.
      destruct hrem as [h0 | [h1 | h2]].
      * pose proof (Q_of_nat_lin m (m / 3) 0 ltac:(lia)) as hqQ.
        rewrite h0; cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin m (m / 3) 1 ltac:(lia)) as hqQ.
        rewrite h1; cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin m (m / 3) 2 ltac:(lia)) as hqQ.
        rewrite h2; cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
  - (* p4E *)
    destruct hst as [hc_le1 [hpo3 [h3c6 [hW hpi_lb]]]].
    assert (hg2 : 2 <= g).
    { destruct (Nat.lt_ge_cases g 2) as [hlt | hge]; [| exact hge].
      exfalso. pose proof (Q_of_nat_le g 1 ltac:(lia)) as hle1. qlra. }
    pose proof (Q_of_nat_add c 1) as hc1_eq.
    pose proof (Q_of_nat_le c 1 hc_le1) as hcQ1.
    destruct g as [| [| [| [| [| g']]]]]; [lia | lia | | | |].
    + cbn [minGap2 step2 step2From0E fst snd List.length def2 endP AdjGoodFrom Inv2];
        unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + cbn [minGap2 step2 step2From0E fst snd List.length def2 endP AdjGoodFrom Inv2];
        unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + cbn [minGap2 step2 step2From0E fst snd List.length def2 endP AdjGoodFrom Inv2];
        unfold nextP.
      repeat split; try lia; try close_em_pos; try exact I; qlra.
    + cbn [minGap2 step2]; rewrite step2From0E_ge3.
      set (m := S (S (S g'))) in *.
      pose proof (Q_of_nat_S (S m)) as hssmQ.
      pose proof (Q_of_nat_S m) as hsmQ.
      assert (hq_pos : 1 <= m / 3) by (unfold m; lia).
      pose proof (Q_of_nat_le 1 (m / 3) hq_pos) as hq1Q.
      assert (hrem : m mod 3 = 0 \/ m mod 3 = 1 \/ m mod 3 = 2) by lia.
      destruct hrem as [h0 | [h1 | h2]].
      * pose proof (Q_of_nat_lin m (m / 3) 0 ltac:(lia)) as hqQ.
        rewrite h0; cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin m (m / 3) 1 ltac:(lia)) as hqQ.
        rewrite h1; cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
      * pose proof (Q_of_nat_lin m (m / 3) 2 ltac:(lia)) as hqQ.
        rewrite h2; cbn [Nat.eqb fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
        repeat split; try (unfold m; lia); try close_em_pos; try exact I; qlra.
  - (* p11 *)
    pose proof (Q_of_nat_add c g) as hcg.
    cbn [minGap2 step2 fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
    repeat split; try lia; try close_em_pos; try exact I; qlra.
  - (* p1E *)
    destruct hst as [-> [hpo3 hW]].
    destruct g as [| g']; [lia |].
    pose proof (Q_of_nat_S g') as hgQ.
    pose proof (Q_of_nat_nonneg g') as hg'0.
    cbn [minGap2 step2 fst snd Nat.add List.length def2 endP AdjGoodFrom Inv2]; unfold nextP;
      change (Q_of_nat 1) with 1%Q.
    repeat split; try lia; try close_em_pos; try exact I; qlra.
  - (* pE1 *)
    destruct hst as [hW hpo_adj].
    destruct g as [| g']; [lia |].
    pose proof (Q_of_nat_S g') as hgQ.
    pose proof (Q_of_nat_nonneg g') as hg'0.
    pose proof (Q_of_nat_add c 2) as hc2_eq.
    change (Q_of_nat 2) with 2%Q in hc2_eq.
    cbn [minGap2 step2 fst snd List.length def2 endP AdjGoodFrom Inv2]; unfold nextP.
    repeat split; try lia; try close_em_pos; try exact I; qlra.
Qed.

Lemma inv2_run (st : St2) (c : nat) (gs : list nat) (po pi : rat)
    (hinv : Inv2 st c po pi) (hpos : forall x, In x gs -> 1 <= x) (hgood : AdjGoodFrom pi gs) :
  Safe2 st gs /\
  (forall x, In x (snd (snd (run2Aux st c gs))) -> 1 <= x) /\
  List.length (snd (snd (run2Aux st c gs))) + def2 (fst (run2Aux st c gs)) =
    List.length gs + def2 st /\
  AdjGoodFrom po (snd (snd (run2Aux st c gs))) /\
  Inv2 (fst (run2Aux st c gs)) (fst (snd (run2Aux st c gs)))
    (endP po (snd (snd (run2Aux st c gs)))) (endP pi gs).
Proof.
  revert st c po pi hinv hpos hgood.
  induction gs as [| g rest IH]; intros st c po pi hinv hpos hgood.
  - cbn [Safe2 run2Aux fst snd List.length Nat.add endP AdjGoodFrom].
    refine (conj I (conj _ (conj eq_refl (conj I hinv)))).
    intros x [].
  - destruct hgood as [h1 hrest_g].
    assert (hg : 1 <= g) by (apply hpos; left; reflexivity).
    assert (hrest_pos : forall x, In x rest -> 1 <= x)
      by (intros x hx; apply hpos; right; exact hx).
    destruct (inv2_step st c g po pi hinv hg h1) as [hmin [hall1 [hlen1 [hag1 hinv1]]]].
    destruct (IH (fst (step2 st c g)) (fst (snd (step2 st c g)))
      (endP po (snd (snd (step2 st c g)))) (nextP pi g) hinv1 hrest_pos hrest_g)
      as [hsafe2 [hall2 [hlen2 [hag2 hinv2]]]].
    cbn [Safe2 run2Aux fst snd].
    rewrite <- (step2_next_indep_c st c g).
    split; [exact (conj hmin hsafe2) |].
    split.
    + intros x hx. apply in_app_iff in hx.
      destruct hx as [hx | hx]; [exact (hall1 x hx) | exact (hall2 x hx)].
    + split.
      * rewrite length_app. cbn [List.length]. lia.
      * split; [exact (adjGood_append hag1 hag2) | rewrite endP_append; exact hinv2].
Qed.

Lemma inv2_tail (st : St2) (c t : nat) (po pi : rat) (hinv : Inv2 st c po pi) :
  (forall x, In x (fst (step2Tail st c t)) -> 1 <= x) /\
  List.length (fst (step2Tail st c t)) + 1 <= def2 st /\
  AdjGoodFrom po (fst (step2Tail st c t)).
Proof.
  destruct hinv as [hpo0 [hpi0 hst]].
  pose proof (Q_of_nat_nonneg c) as hc0.
  pose proof (Q_of_nat_add c 1) as hc1_eq.
  pose proof (Q_of_nat_add c 2) as hc2_eq.
  change (Q_of_nat 1) with 1%Q in hc1_eq.
  change (Q_of_nat 2) with 2%Q in hc2_eq.
  destruct st.
  - cbn [step2Tail fst List.length def2 AdjGoodFrom]. repeat split; try close_em_pos; try lia; exact I.
  - destruct t; cbn [step2Tail fst List.length def2 AdjGoodFrom]; repeat split; try close_em_pos; try lia; exact I.
  - destruct hst as [_ [_ [_ hpo_adj]]].
    destruct t as [| [| [| t']]]; cbn [step2Tail step2Tail0E fst List.length def2 AdjGoodFrom];
      repeat split; try close_em_pos; try lia; try exact I; qlra.
  - destruct hst as [hpo_eq _].
    destruct t as [| [| [| [| t']]]]; cbn [step2Tail step2Tail0E fst List.length def2 AdjGoodFrom];
      repeat split; try close_em_pos; try lia; try exact I; qlra.
  - destruct hst as [_ [_ [_ hpo_adj]]].
    destruct t as [| [| [| [| t']]]]; cbn [step2Tail step2Tail0E fst List.length def2 AdjGoodFrom];
      repeat split; try close_em_pos; try lia; try exact I; qlra.
  - destruct hst as [-> [hpo3 _]].
    destruct t as [| [| [| [| t']]]]; cbn [step2Tail step2Tail0E fst Nat.add List.length def2 AdjGoodFrom];
      unfold nextP; change (Q_of_nat 1) with 1%Q;
      repeat split; try close_em_pos; try lia; try exact I; qlra.
  - destruct hst as [_ [hpo3 [h3c6 _]]].
    destruct t as [| [| [| [| [| t']]]]]; cbn [step2Tail step2Tail0E fst Nat.add List.length def2 AdjGoodFrom];
      unfold nextP; change (Q_of_nat 1) with 1%Q;
      repeat split; try close_em_pos; try lia; try exact I; qlra.
  - cbn [step2Tail fst List.length def2 AdjGoodFrom]. repeat split; try close_em_pos; try lia; exact I.
  - destruct hst as [-> [hpo3 _]].
    destruct t as [| t']; cbn [step2Tail fst Nat.add List.length def2 AdjGoodFrom];
      change (Q_of_nat 1) with 1%Q;
      repeat split; try close_em_pos; try lia; try exact I; qlra.
  - destruct hst as [_ hpo_adj].
    destruct t as [| t']; cbn [step2Tail fst List.length def2 AdjGoodFrom];
      repeat split; try close_em_pos; try lia; try exact I; qlra.
Qed.

(* ========================================================================== *)
(* Section 7: Phase-0 Split & Strong Induction (`main_stream`)                *)
(* ========================================================================== *)

Lemma phase0_00_2 :
  RunEv (gapEv 2) (w0 *> w0 *> 0inf) (w4 *> w0 *> 0inf).
Proof.
  cbn [gapEv repB List.app].
  exact (RunEv_cons (stepEv_w0_B _)
    (RunEv_cons (stepEv_w2_B _) (runEv_single (stepEv_w3_S _)))).
Qed.

Lemma phase0_00_3 :
  RunEv (gapEv 3) (w0 *> w0 *> 0inf) (tok2 p01 *> 0inf).
Proof.
  cbn [gapEv repB List.app tok2]. rewrite Str_app_assoc.
  exact (RunEv_cons (stepEv_w0_B _)
    (RunEv_cons (stepEv_w2_B _)
      (RunEv_cons (stepEv_w3_B (stepEv_w0_B 0inf))
        (runEv_single (stepEv_w0_S (stepEv_w2_S 0inf)))))).
Qed.

Lemma phase0_00_5 :
  RunEv (gapEv 5) (w0 *> w0 *> 0inf) (tok2 p42 *> 0inf).
Proof.
  cbn [gapEv repB List.app tok2]. rewrite Str_app_assoc.
  exact (RunEv_cons (stepEv_w0_B _)
    (RunEv_cons (stepEv_w2_B _)
      (RunEv_cons (stepEv_w3_B (stepEv_w0_B 0inf))
        (RunEv_cons (stepEv_w0_B _)
          (RunEv_cons (stepEv_w2_B _) (runEv_single (stepEv_w3_S _))))))).
Qed.

Lemma phase0_40_1 :
  RunEv (gapEv 1) (w4 *> w0 *> 0inf) (w0 *> w0 *> 0inf).
Proof.
  cbn [gapEv repB List.app].
  exact (RunEv_cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S))
    (runEv_single (stepEv_w0_S (stepEv_w0_S stepEv_default_S)))).
Qed.

Lemma phase0_40_3 :
  RunEv (gapEv 3) (w4 *> w0 *> 0inf) (w4 *> w0 *> 0inf).
Proof.
  change (gapEv 3) with (EvB :: gapEv 2).
  exact (RunEv_cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S)) phase0_00_2).
Qed.

Lemma phase0_40_4 :
  RunEv (gapEv 4) (w4 *> w0 *> 0inf) (tok2 p01 *> 0inf).
Proof.
  change (gapEv 4) with (EvB :: gapEv 3).
  exact (RunEv_cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S)) phase0_00_3).
Qed.

Lemma phase0_40_6 :
  RunEv (gapEv 6) (w4 *> w0 *> 0inf) (tok2 p42 *> 0inf).
Proof.
  change (gapEv 6) with (EvB :: gapEv 5).
  exact (RunEv_cons (stepEv_w4_B (stepEv_w0_S stepEv_default_S)) phase0_00_5).
Qed.

Lemma adjGood_from_nextP00 {xs : list nat} (h : AdjGoodFrom (nextP 0%Q 0) xs) :
  AdjGoodFrom 0%Q xs.
Proof.
  apply (adjGood_mono 0%Q (nextP 0%Q 0) xs).
  - unfold nextP. change (Q_of_nat 0) with 0%Q. qlra.
  - exact h.
Qed.

Lemma phase0_find_entry (st : St1) (gs : list nat) (t : nat) (pi : rat)
    (hst : st = s0 \/ st = s4)
    (hpi : (0 <= pi)%Q /\ (st = s4 -> (2 <= pi)%Q))
    (hpos : forall x, In x gs -> 1 <= x)
    (hgood : AdjGoodFrom pi gs)
    (hbad : isSafeZero (fst (run1Full st 0 gs t)) = false) :
  exists (pref suff : list nat) (st2 : St2) (pi2 : rat),
    gs = pref ++ suff /\
    List.length suff < List.length gs /\
    (st2 = p01 \/ st2 = p42) /\
    Inv2 st2 0 0%Q pi2 /\
    AdjGoodFrom pi2 suff /\
    RunEv (gapsEv pref) (tok1 st *> w0 *> 0inf) (tok2 st2 *> 0inf).
Proof.
  revert st pi hst hpi hpos hgood hbad.
  induction gs as [| g rest IH]; intros st pi hst hpi hpos hgood hbad.
  - destruct hst as [-> | ->].
    + discriminate hbad.
    + destruct t; discriminate hbad.
  - destruct hgood as [h1 hrest_g].
    assert (hg : 1 <= g) by (apply hpos; left; reflexivity).
    assert (hrest_pos : forall x, In x rest -> 1 <= x)
      by (intros x hx; apply hpos; right; exact hx).
    destruct hst as [-> | ->].
    + (* st = s0 *)
      destruct g as [| [| [| [| [| [| g']]]]]]; [lia | | | | | |].
      * (* g = 1 *)
        pose proof (run1Full_from_s1_allPos s1 0 rest t (or_introl eq_refl) hrest_pos) as hall.
        assert (hok : isSafeZero (fst (run1Full s0 0 (1 :: rest) t)) = true).
        { change (fst (run1Full s0 0 (1 :: rest) t)) with (fst (run1Full s1 0 rest t)).
          exact (isSafeZero_of_allPos hall). }
        rewrite hok in hbad. discriminate hbad.
      * (* g = 2 *)
        change (fst (run1Full s0 0 (2 :: rest) t)) with (fst (run1Full s4 0 rest t)) in hbad.
        assert (hpi' : (0 <= nextP pi 2)%Q /\ (s4 = s4 -> (2 <= nextP pi 2)%Q)).
        { destruct hpi as [hpi0 _]. unfold nextP; change (Q_of_nat 2) with 2%Q.
          split; [lra | intros _; lra]. }
        destruct (IH s4 (nextP pi 2) (or_intror eq_refl) hpi' hrest_pos hrest_g hbad)
          as [pref [suff [st2 [pi2 [heq [hlt [hst2 [hinv2 [hgsuff hrun]]]]]]]]].
        exists (2 :: pref), suff, st2, pi2.
        refine (conj _ (conj _ (conj hst2 (conj hinv2 (conj hgsuff _))))).
        -- rewrite heq. reflexivity.
        -- cbn [List.length]. lia.
        -- cbn [gapsEv tok1]. exact (runEv_append phase0_00_2 hrun).
      * (* g = 3 *)
        exists [3], rest, p01, (nextP pi 3).
        destruct hpi as [hpi0 _].
        refine (conj eq_refl (conj _ (conj (or_introl eq_refl) (conj _ (conj hrest_g _))))).
        -- cbn [List.length]. lia.
        -- cbn [Inv2]; unfold nextP; change (Q_of_nat 3) with 3%Q. repeat split; qlra.
        -- cbn [gapsEv List.app tok1]. rewrite app_nil_r. exact phase0_00_3.
      * (* g = 4 *)
        pose proof (run1Full_from_s1_allPos s1 1 rest t (or_introl eq_refl) hrest_pos) as hall.
        assert (hok : isSafeZero (fst (run1Full s0 0 (4 :: rest) t)) = true).
        { change (fst (run1Full s0 0 (4 :: rest) t)) with (fst (run1Full s1 1 rest t)).
          exact (isSafeZero_of_allPos hall). }
        rewrite hok in hbad. discriminate hbad.
      * (* g = 5 *)
        exists [5], rest, p42, (nextP pi 5).
        destruct hpi as [hpi0 _].
        refine (conj eq_refl (conj _ (conj (or_intror eq_refl) (conj _ (conj hrest_g _))))).
        -- cbn [List.length]. lia.
        -- cbn [Inv2]; unfold nextP; change (Q_of_nat 5) with 5%Q. repeat split; qlra.
        -- cbn [gapsEv List.app tok1]. rewrite app_nil_r. exact phase0_00_5.
      * (* g = S (S (S (S (S (S g'))))) >= 6 *)
        set (m := S (S (S (S (S (S g')))))). fold m in h1, hrest_g, hbad |- *.
        assert (hq2 : 2 <= m / 3) by (unfold m; lia).
        pose proof (Q_of_nat_le 2 (m / 3) hq2) as hq2Q.
        change (Q_of_nat 2) with 2%Q in hq2Q.
        destruct hpi as [hpi0 _].
        assert (hinv0 : Inv1 s0 0 0%Q pi) by (cbn [Inv1]; repeat split; lra).
        pose proof (inv1_full s0 0 (m :: rest) t 0%Q pi hinv0 (conj h1 hrest_g)
          (safe1_of_allPos s0 (m :: rest) hpos)) as hgood_all.
        assert (hrem : m mod 3 = 0 \/ m mod 3 = 1 \/ m mod 3 = 2) by lia.
        destruct hrem as [h0 | [h1m | h2m]].
        -- assert (heq_list : fst (run1Full s0 0 (m :: rest) t) =
             (m / 3) :: fst (run1Full s0 0 rest t)).
           { unfold run1Full; cbn [run1Aux step1]; rewrite h0; reflexivity. }
           rewrite heq_list in hgood_all, hbad.
           destruct hgood_all as [_ hrest_ag].
           assert (hp_gt : (3 < 2 * nextP 0%Q (m / 3))%Q) by (unfold nextP; lra).
           pose proof (adjGood_no_zero_of_gt hrest_ag hp_gt) as hall_rest.
           assert (hok : isSafeZero ((m / 3) :: fst (run1Full s0 0 rest t)) = true).
           { apply isSafeZero_of_allPos. intros x [<- | hx']; [lia | exact (hall_rest x hx')]. }
           rewrite hok in hbad. discriminate hbad.
        -- assert (heq_list : fst (run1Full s0 0 (m :: rest) t) =
             fst (run1Full s1 (m / 3) rest t)).
           { unfold run1Full; cbn [run1Aux step1]; rewrite h1m; reflexivity. }
           rewrite heq_list in hbad.
           pose proof (isSafeZero_of_allPos
             (run1Full_from_s1_allPos s1 (m / 3) rest t (or_introl eq_refl) hrest_pos)) as hok.
           rewrite hok in hbad. discriminate hbad.
        -- assert (heq_list : fst (run1Full s0 0 (m :: rest) t) =
             fst (run1Full s4 (m / 3) rest t)).
           { unfold run1Full; cbn [run1Aux step1]; rewrite h2m; reflexivity. }
           rewrite heq_list in hgood_all, hbad.
           destruct rest as [| g2 rest2].
           ++ destruct t as [| t']; [discriminate hbad |].
              assert (hok : isSafeZero (fst (run1Full s4 (m / 3) [] (S t'))) = true).
              { unfold run1Full; cbn [run1Aux step1Tail fst snd List.app].
                apply isSafeZero_of_allPos. intros x hx; cbn [In] in hx; destruct hx as [<- | []]; lia. }
              rewrite hok in hbad. discriminate hbad.
           ++ destruct g2 as [| g2']; [exfalso; specialize (hrest_pos 0 (or_introl eq_refl)); lia |].
              assert (hhead : exists tail_em, fst (run1Full s4 (m / 3) (S g2' :: rest2) t) =
                (m / 3) :: tail_em).
              { unfold run1Full; cbn [run1Aux step1].
                destruct (Nat.eqb (g2' mod 3) 0); [eexists; reflexivity |].
                destruct (Nat.eqb (g2' mod 3) 1); eexists; reflexivity. }
              destruct hhead as [tail_em hte].
              rewrite hte in hgood_all, hbad.
              destruct hgood_all as [_ hrest_ag].
              assert (hp_gt : (3 < 2 * nextP 0%Q (m / 3))%Q) by (unfold nextP; lra).
              pose proof (adjGood_no_zero_of_gt hrest_ag hp_gt) as hall_rest.
              assert (hok : isSafeZero ((m / 3) :: tail_em) = true).
              { apply isSafeZero_of_allPos. intros x [<- | hx']; [lia | exact (hall_rest x hx')]. }
              rewrite hok in hbad. discriminate hbad.
    + (* st = s4 *)
      destruct hpi as [hpi0 hpi2_fn].
      pose proof (hpi2_fn eq_refl) as hpi2.
      destruct g as [| [| [| [| [| [| [| g']]]]]]]; [lia | | | | | | |].
      * (* g = 1 *)
        assert (hbad' : isSafeZero (fst (run1Full s0 0 rest t)) = false).
        { change (fst (run1Full s4 0 (1 :: rest) t)) with (0 :: 0 :: fst (run1Full s0 0 rest t)) in hbad.
          cbn [isSafeZero stripLZ] in hbad. exact hbad. }
        assert (hpi' : (0 <= nextP pi 1)%Q /\ (s0 = s4 -> (2 <= nextP pi 1)%Q)).
        { unfold nextP; change (Q_of_nat 1) with 1%Q. split; [lra | intro H; discriminate H]. }
        destruct (IH s0 (nextP pi 1) (or_introl eq_refl) hpi' hrest_pos hrest_g hbad')
          as [pref [suff [st2 [pi2 [heq [hlt [hst2 [hinv2 [hgsuff hrun]]]]]]]]].
        exists (1 :: pref), suff, st2, pi2.
        refine (conj _ (conj _ (conj hst2 (conj hinv2 (conj hgsuff _))))).
        -- rewrite heq. reflexivity.
        -- cbn [List.length]. lia.
        -- cbn [gapsEv tok1]. exact (runEv_append phase0_40_1 hrun).
      * (* g = 2 *)
        pose proof (run1Full_from_s1_allPos s1 0 rest t (or_introl eq_refl) hrest_pos) as hall.
        assert (hok : isSafeZero (fst (run1Full s4 0 (2 :: rest) t)) = true).
        { change (isSafeZero (fst (run1Full s4 0 (2 :: rest) t))) with
            (isSafeZero (fst (run1Full s1 0 rest t))).
          exact (isSafeZero_of_allPos hall). }
        rewrite hok in hbad. discriminate hbad.
      * (* g = 3 *)
        assert (hbad' : isSafeZero (fst (run1Full s4 0 rest t)) = false).
        { change (fst (run1Full s4 0 (3 :: rest) t)) with (0 :: fst (run1Full s4 0 rest t)) in hbad.
          cbn [isSafeZero stripLZ] in hbad. exact hbad. }
        assert (hpi' : (0 <= nextP pi 3)%Q /\ (s4 = s4 -> (2 <= nextP pi 3)%Q)).
        { unfold nextP; change (Q_of_nat 3) with 3%Q. split; [lra | intros _; lra]. }
        destruct (IH s4 (nextP pi 3) (or_intror eq_refl) hpi' hrest_pos hrest_g hbad')
          as [pref [suff [st2 [pi2 [heq [hlt [hst2 [hinv2 [hgsuff hrun]]]]]]]]].
        exists (3 :: pref), suff, st2, pi2.
        refine (conj _ (conj _ (conj hst2 (conj hinv2 (conj hgsuff _))))).
        -- rewrite heq. reflexivity.
        -- cbn [List.length]. lia.
        -- cbn [gapsEv tok1]. exact (runEv_append phase0_40_3 hrun).
      * (* g = 4 *)
        exists [4], rest, p01, (nextP pi 4).
        refine (conj eq_refl (conj _ (conj (or_introl eq_refl) (conj _ (conj hrest_g _))))).
        -- cbn [List.length]. lia.
        -- cbn [Inv2]; unfold nextP; change (Q_of_nat 4) with 4%Q. repeat split; qlra.
        -- cbn [gapsEv List.app tok1]. rewrite app_nil_r. exact phase0_40_4.
      * (* g = 5 *)
        pose proof (run1Full_from_s1_allPos s1 1 rest t (or_introl eq_refl) hrest_pos) as hall.
        assert (hok : isSafeZero (fst (run1Full s4 0 (5 :: rest) t)) = true).
        { change (isSafeZero (fst (run1Full s4 0 (5 :: rest) t))) with
            (isSafeZero (fst (run1Full s1 1 rest t))).
          exact (isSafeZero_of_allPos hall). }
        rewrite hok in hbad. discriminate hbad.
      * (* g = 6 *)
        exists [6], rest, p42, (nextP pi 6).
        refine (conj eq_refl (conj _ (conj (or_intror eq_refl) (conj _ (conj hrest_g _))))).
        -- cbn [List.length]. lia.
        -- cbn [Inv2]; unfold nextP; change (Q_of_nat 6) with 6%Q. repeat split; qlra.
        -- cbn [gapsEv List.app tok1]. rewrite app_nil_r. exact phase0_40_6.
      * (* g = S m where m = S (S (S (S (S (S g'))))) >= 6 *)
        set (m := S (S (S (S (S (S g')))))) in *.
        assert (hq2 : 2 <= m / 3) by (unfold m; lia).
        pose proof (Q_of_nat_le 2 (m / 3) hq2) as hq2Q.
        change (Q_of_nat 2) with 2%Q in hq2Q.
        assert (hinv4 : Inv1 s4 0 0%Q pi)
          by (cbn [Inv1]; repeat split; qlra).
        pose proof (inv1_full s4 0 (S m :: rest) t 0%Q pi hinv4 (conj h1 hrest_g)
          (safe1_of_allPos s4 (S m :: rest) hpos)) as hgood_all.
        assert (hrem : m mod 3 = 0 \/ m mod 3 = 1 \/ m mod 3 = 2) by lia.
        destruct hrem as [h0 | [h1m | h2m]].
        -- assert (heq_list : fst (run1Full s4 0 (S m :: rest) t) =
             0 :: (m / 3) :: fst (run1Full s0 0 rest t)).
           { unfold run1Full; cbn [run1Aux step1]; rewrite h0; reflexivity. }
           rewrite heq_list in hgood_all, hbad.
           destruct hgood_all as [_ hrest_ag0].
           pose proof (adjGood_from_nextP00 hrest_ag0) as hrest_ag1.
           destruct hrest_ag1 as [_ hrest_ag].
           assert (hp_gt : (3 < 2 * nextP 0%Q (m / 3))%Q) by (unfold nextP; lra).
           pose proof (adjGood_no_zero_of_gt hrest_ag hp_gt) as hall_rest.
           assert (hok : isSafeZero (0 :: (m / 3) :: fst (run1Full s0 0 rest t)) = true).
           { change (isSafeZero (0 :: (m / 3) :: fst (run1Full s0 0 rest t))) with
               (isSafeZero ((m / 3) :: fst (run1Full s0 0 rest t))).
             apply isSafeZero_of_allPos. intros x [<- | hx']; [lia | exact (hall_rest x hx')]. }
           rewrite hok in hbad. discriminate hbad.
        -- assert (heq_list : fst (run1Full s4 0 (S m :: rest) t) =
             0 :: fst (run1Full s1 (m / 3) rest t)).
           { unfold run1Full; cbn [run1Aux step1]; rewrite h1m; reflexivity. }
           rewrite heq_list in hbad.
           assert (hok : isSafeZero (0 :: fst (run1Full s1 (m / 3) rest t)) = true).
           { change (isSafeZero (0 :: fst (run1Full s1 (m / 3) rest t))) with
               (isSafeZero (fst (run1Full s1 (m / 3) rest t))).
             exact (isSafeZero_of_allPos
               (run1Full_from_s1_allPos s1 (m / 3) rest t (or_introl eq_refl) hrest_pos)). }
           rewrite hok in hbad. discriminate hbad.
        -- assert (heq_list : fst (run1Full s4 0 (S m :: rest) t) =
             0 :: fst (run1Full s4 (m / 3) rest t)).
           { unfold run1Full; cbn [run1Aux step1]; rewrite h2m; reflexivity. }
           rewrite heq_list in hgood_all, hbad.
           destruct hgood_all as [_ hrest_ag0].
           pose proof (adjGood_from_nextP00 hrest_ag0) as hrest_ag1.
           destruct rest as [| g2 rest2].
           ++ destruct t as [| t']; [discriminate hbad |].
              assert (hok : isSafeZero (0 :: fst (run1Full s4 (m / 3) [] (S t'))) = true).
              { change (isSafeZero (0 :: fst (run1Full s4 (m / 3) [] (S t')))) with
                  (isSafeZero (fst (run1Full s4 (m / 3) [] (S t')))).
                unfold run1Full; cbn [run1Aux step1Tail fst snd List.app].
                apply isSafeZero_of_allPos. intros x hx; cbn [In] in hx; destruct hx as [<- | []]; lia. }
              rewrite hok in hbad. discriminate hbad.
           ++ destruct g2 as [| g2']; [exfalso; specialize (hrest_pos 0 (or_introl eq_refl)); lia |].
              assert (hhead : exists tail_em, fst (run1Full s4 (m / 3) (S g2' :: rest2) t) =
                (m / 3) :: tail_em).
              { unfold run1Full; cbn [run1Aux step1].
                destruct (Nat.eqb (g2' mod 3) 0); [eexists; reflexivity |].
                destruct (Nat.eqb (g2' mod 3) 1); eexists; reflexivity. }
              destruct hhead as [tail_em hte].
              rewrite hte in hrest_ag1, hbad.
              destruct hrest_ag1 as [_ hrest_ag].
              assert (hp_gt : (3 < 2 * nextP 0%Q (m / 3))%Q) by (unfold nextP; lra).
              pose proof (adjGood_no_zero_of_gt hrest_ag hp_gt) as hall_rest.
              assert (hok : isSafeZero (0 :: (m / 3) :: tail_em) = true).
              { change (isSafeZero (0 :: (m / 3) :: tail_em)) with
                  (isSafeZero ((m / 3) :: tail_em)).
                apply isSafeZero_of_allPos. intros x [<- | hx']; [lia | exact (hall_rest x hx')]. }
              rewrite hok in hbad. discriminate hbad.
Qed.

Theorem main_stream : forall (n : nat),
  forall (m : nat) (gs : list nat) (t : nat),
    List.length gs <= n -> sum_list gs + t <= m ->
    Good gs -> isSafeZero gs = true ->
    exists r', RunEv (gapsEv gs ++ repB t) 0inf r'.
Proof.
  induction n as [n ih_len] using strong_induction.
  induction m as [m ih_sum] using strong_induction.
  intros gs t hlen hsum hgood hsafe.
  destruct gs as [| g rest].
  - cbn [gapsEv List.app]. exact (run_B_only t).
  - destruct g as [| g0].
    + (* g = 0 *)
      destruct hgood as [_ hrest_g0].
      pose proof (adjGood_from_nextP00 hrest_g0) as hrest_g.
      cbn [isSafeZero stripLZ] in hsafe.
      cbn [List.length] in hlen.
      assert (hlt_n : n - 1 < n) by lia.
      assert (hlen' : List.length rest <= n - 1) by lia.
      destruct (ih_len (n - 1) hlt_n (sum_list rest + t) rest t hlen' (Nat.le_refl _) hrest_g hsafe)
        as [r' hr'].
      exists r'. cbn [gapsEv gapEv repB List.app].
      exact (RunEv_cons stepEv_default_S hr').
    + (* g = S g0 >= 1 *)
      set (gs0 := S g0 :: rest).
      fold gs0 in hlen, hsum, hgood, hsafe |- *.
      assert (hgs_sum_pos : 1 <= sum_list gs0) by (unfold gs0; cbn [sum_list]; lia).
      assert (hsplit : (exists rest', gs0 = 1 :: 0 :: rest' /\ (forall x, In x rest' -> 1 <= x)) \/
        (forall x, In x gs0 -> 1 <= x)).
      { unfold gs0 in hsafe |- *.
        destruct g0 as [| g0'].
        - destruct rest as [| r1 rs1].
          + right. intros x [<- | []]; lia.
          + destruct r1 as [| r1'].
            * left. exists rs1. split; [reflexivity |].
              cbn [isSafeZero stripLZ] in hsafe.
              exact (proj1 isAllPos_eq_true_iff hsafe).
            * right. cbn [isSafeZero stripLZ isAllPos] in hsafe.
              pose proof (proj1 isAllPos_eq_true_iff hsafe) as htail.
              intros x [<- | [<- | hx']]; [lia | lia | exact (htail x hx')].
        - right. cbn [isSafeZero stripLZ isAllPos] in hsafe.
          pose proof (proj1 isAllPos_eq_true_iff hsafe) as htail.
          intros x [<- | hx']; [lia | exact (htail x hx')]. }
      assert (hsafe1 : Safe1 s0 gs0).
      { destruct hsplit as [[rest' [heq hpos']] | hpos].
        - rewrite heq. cbn [Safe1 step1 Nat.modulo Nat.eqb fst].
          refine (conj (fun h => _) (conj (fun h => _) (safe1_of_allPos sE rest' hpos')));
            destruct h as [h | h]; discriminate h.
        - exact (safe1_of_allPos s0 gs0 hpos). }
      set (res1 := run1Full s0 0 gs0 t).
      assert (hinv0 : Inv1 s0 0 0%Q 0%Q) by (cbn [Inv1]; repeat split; qlra).
      pose proof (inv1_full s0 0 gs0 t 0%Q 0%Q hinv0 hgood hsafe1) as hgood1.
      fold res1 in hgood1.
      destruct (isSafeZero (fst res1)) eqn:hsf1.
      * (* 1-cell peel *)
        pose proof (run1Aux_def_eq s0 0 gs0 hsafe1) as hdef.
        assert (hrun_child : exists r1', RunEv (gapsEv (fst res1) ++ repB (snd res1)) 0inf r1').
        { destruct (fst (run1Aux s0 0 gs0)) eqn:hst_end.
          - (* s0 *)
            assert (hlen_le : List.length (fst res1) <= n).
            { unfold res1, run1Full; rewrite hst_end;
              cbn [step1Tail def1 fst List.app] in hdef |- *; rewrite app_nil_r; lia. }
            pose proof (run1Aux_stay_base3_budget s0 0 gs0 hsafe1 (or_introl hst_end) (or_introl eq_refl))
              as hbud.
            assert (hsum_lt : sum_list (fst res1) + snd res1 < m).
            { unfold res1, run1Full; rewrite hst_end; cbn [step1Tail fst snd]; rewrite app_nil_r; lia. }
            exact (ih_sum (sum_list (fst res1) + snd res1) hsum_lt (fst res1) (snd res1)
              hlen_le (Nat.le_refl _) hgood1 hsf1).
          - (* s4 *)
            destruct t as [| t'].
            + assert (hlt_len : List.length (fst res1) < List.length gs0).
              { unfold res1, run1Full; rewrite hst_end;
                cbn [step1Tail def1 fst] in hdef |- *; rewrite app_nil_r; lia. }
              assert (hlt_n : n - 1 < n) by (unfold gs0 in hlen; cbn [List.length] in hlen; lia).
              exact (ih_len (n - 1) hlt_n (sum_list (fst res1) + snd res1) (fst res1) (snd res1)
                ltac:(lia) (Nat.le_refl _) hgood1 hsf1).
            + assert (hlen_le : List.length (fst res1) <= n).
              { unfold res1, run1Full; rewrite hst_end;
                cbn [step1Tail def1 fst] in hdef |- *; rewrite length_app; cbn [List.length]; lia. }
              pose proof (run1Aux_stay_base3_budget s0 0 gs0 hsafe1 (or_intror hst_end) (or_introl eq_refl))
                as hbud.
              assert (hsum_lt : sum_list (fst res1) + snd res1 < m).
              { unfold res1, run1Full; rewrite hst_end; cbn [step1Tail fst snd];
                rewrite sum_list_app; cbn [sum_list]; lia. }
              exact (ih_sum (sum_list (fst res1) + snd res1) hsum_lt (fst res1) (snd res1)
                hlen_le (Nat.le_refl _) hgood1 hsf1).
          - (* s1 *)
            assert (hlt_len : List.length (fst res1) < List.length gs0).
            { unfold res1, run1Full; rewrite hst_end;
              cbn [step1Tail def1 fst] in hdef |- *; rewrite app_nil_r; lia. }
            assert (hlt_n : n - 1 < n) by (unfold gs0 in hlen; cbn [List.length] in hlen; lia).
            exact (ih_len (n - 1) hlt_n (sum_list (fst res1) + snd res1) (fst res1) (snd res1)
              ltac:(lia) (Nat.le_refl _) hgood1 hsf1).
          - (* sE *)
            assert (hlt_len : List.length (fst res1) < List.length gs0).
            { unfold res1, run1Full; rewrite hst_end;
              cbn [def1 fst] in hdef |- *; rewrite length_app;
              destruct t; cbn [step1Tail fst List.length]; lia. }
            assert (hlt_n : n - 1 < n) by (unfold gs0 in hlen; cbn [List.length] in hlen; lia).
            exact (ih_len (n - 1) hlt_n (sum_list (fst res1) + snd res1) (fst res1) (snd res1)
              ltac:(lia) (Nat.le_refl _) hgood1 hsf1). }
        destruct hrun_child as [r1' hr1'].
        pose proof (rep_B_run1Evs s0 0 gs0 t hsafe1) as hev_eq.
        cbn [repB List.app] in hev_eq. fold res1 in hev_eq.
        rewrite <- hev_eq in hr1'.
        destruct (lift1_run s0 gs0 t hsafe1 hr1') as [r_out hrun_out].
        cbn [tok1] in hrun_out. rewrite w0_append_0inf in hrun_out.
        exists r_out. exact hrun_out.
      * (* 2-cell peel *)
        assert (hpos_gs0 : forall x, In x gs0 -> 1 <= x).
        { destruct hsplit as [[rest' [heq hpos']] | hpos]; [| exact hpos].
          exfalso. pose proof (run1Full_from_s0_1_0_allPos rest' t hpos') as hall.
          rewrite <- heq in hall. fold res1 in hall.
          pose proof (isSafeZero_of_allPos hall) as hok.
          rewrite hok in hsf1. discriminate hsf1. }
        destruct (phase0_find_entry s0 gs0 t 0%Q (or_introl eq_refl)
          (conj (Qle_refl 0%Q) (fun h : s0 = s4 => ltac:(discriminate h))) hpos_gs0 hgood hsf1)
          as [pref [suff [st2 [pi2 [heq_gs [hlt_suff [hst2 [hinv2 [hgood_suff hrun_pref]]]]]]]]].
        assert (hpos_suff : forall x, In x suff -> 1 <= x).
        { intros x hx. apply hpos_gs0. rewrite heq_gs. apply in_app_iff. right. exact hx. }
        destruct (inv2_run st2 0 suff 0%Q pi2 hinv2 hpos_suff hgood_suff)
          as [hsafe2 [hall2_aux [hlen2_aux [hag2_aux hinv2_end]]]].
        destruct (inv2_tail (fst (run2Aux st2 0 suff)) (fst (snd (run2Aux st2 0 suff))) t
          (endP 0%Q (snd (snd (run2Aux st2 0 suff)))) (endP pi2 suff) hinv2_end)
          as [hall2_tail [hlen2_tail hag2_tail]].
        set (res2 := run2Full st2 0 suff t).
        assert (hgood2 : Good (fst res2)) by (unfold res2, run2Full; exact (adjGood_append hag2_aux hag2_tail)).
        assert (hall2 : forall x, In x (fst res2) -> 1 <= x).
        { intros x hx. unfold res2, run2Full in hx; cbn [fst] in hx.
          apply in_app_iff in hx. destruct hx as [hx | hx];
            [exact (hall2_aux x hx) | exact (hall2_tail x hx)]. }
        pose proof (isSafeZero_of_allPos hall2) as hsafe_res2.
        assert (hdef_st2 : def2 st2 = 1) by (destruct hst2 as [-> | ->]; reflexivity).
        assert (hlen2_lt : List.length (fst res2) < List.length gs0).
        { unfold res2, run2Full; cbn [fst]; rewrite length_app; lia. }
        assert (hlt_n : n - 1 < n) by (unfold gs0 in hlen; cbn [List.length] in hlen; lia).
        destruct (ih_len (n - 1) hlt_n (sum_list (fst res2) + snd res2) (fst res2) (snd res2)
          ltac:(lia) (Nat.le_refl _) hgood2 hsafe_res2) as [r2' hr2'].
        pose proof (rep_B_run2Evs st2 0 suff t hsafe2) as hev2_eq.
        cbn [repB List.app] in hev2_eq. fold res2 in hev2_eq.
        rewrite <- hev2_eq in hr2'.
        destruct (lift2_run st2 suff t hsafe2 hr2') as [r_out hrun_suff].
        cbn [tok1] in hrun_pref. do 2 rewrite w0_append_0inf in hrun_pref.
        exists r_out.
        rewrite heq_gs, gapsEv_append, <- app_assoc.
        exact (runEv_append hrun_pref hrun_suff).
Qed.


(* ========================================================================== *)
(* Section 8: Initial `w2` Cell Peel & Final Conjugated Non-Halting Proof     *)
(* ========================================================================== *)

Fixpoint eraStream18 (N : nat) : list Ev :=
  match N with
  | 0 => []
  | S N' => eraStream18 N' ++ eraEvents (18 + N')
  end.

Fixpoint tailSeq18 (N : nat) : list nat :=
  match N with
  | 0 => []
  | S N' => tailSeq18 N' ++ [(18 + N') / 3 + 1]
  end.

Lemma eraStream18_eq_gapsEv (N : nat) :
  eraStream18 N ++ [EvB; EvS] = gapsEv (1 :: tailSeq18 N).
Proof.
  induction N as [| N IH]; [reflexivity |].
  cbn [eraStream18].
  change (1 :: tailSeq18 (S N)) with ((1 :: tailSeq18 N) ++ [(18 + N) / 3 + 1]).
  rewrite gapsEv_append, <- IH.
  change (gapsEv [(18 + N) / 3 + 1]) with (gapEv ((18 + N) / 3 + 1) ++ []).
  rewrite app_nil_r.
  unfold eraEvents, gapEv.
  rewrite repB_add. cbn [repB].
  repeat rewrite <- app_assoc; cbn [List.app]; reflexivity.
Qed.

Lemma tailSeq18_allPos (N : nat) : forall x, In x (tailSeq18 N) -> 1 <= x.
Proof.
  induction N as [| N IH]; intros x hx.
  - inversion hx.
  - cbn [tailSeq18] in hx. apply in_app_iff in hx.
    destruct hx as [hx | [<- | []]]; [exact (IH x hx) | lia].
Qed.

Lemma tailSeq18_good_from_2 (N : nat) :
  AdjGoodFrom 2%Q (tailSeq18 N) /\
  (2 * endP 2%Q (tailSeq18 N) <= 3 * Q_of_nat ((18 + N) / 3 + 1))%Q.
Proof.
  induction N as [| N [hgN hendN]].
  - cbn. change (Q_of_nat 7) with 7%Q.
    split; [exact I | lra].
  - set (x := (18 + N) / 3 + 1). fold x in hendN.
    assert (hstep_ag : AdjGoodFrom (endP 2%Q (tailSeq18 N)) [x]).
    { cbn [AdjGoodFrom]. split; [qlra | exact I]. }
    pose proof (adjGood_append hgN hstep_ag) as hgood_succ.
    assert (hmono : x <= (18 + S N) / 3 + 1) by (unfold x; lia).
    pose proof (Q_of_nat_le x ((18 + S N) / 3 + 1) hmono) as hmonoQ.
    cbn [tailSeq18]; fold x. split; [exact hgood_succ |].
    rewrite endP_append. cbn [endP]; unfold nextP. qlra.
Qed.

Lemma tailSeq18_cons_prefix (N : nat) :
  (N = 0 /\ tailSeq18 N = []) \/
  (N = 1 /\ tailSeq18 N = [7]) \/
  (exists rest, tailSeq18 N = 7 :: 7 :: rest /\ forall x, In x rest -> 1 <= x).
Proof.
  destruct N as [| [| k]].
  - left. exact (conj eq_refl eq_refl).
  - right; left. exact (conj eq_refl eq_refl).
  - right; right.
    induction k as [| k [rest [hrest hpos]]].
    + exists ([] : list nat). split; [reflexivity | intros x []].
    + exists (rest ++ [(18 + S (S k)) / 3 + 1]). split.
      * change (tailSeq18 (S (S (S k)))) with (tailSeq18 (S (S k)) ++ [(18 + S (S k)) / 3 + 1]).
        rewrite hrest. reflexivity.
      * intros x hx. apply in_app_iff in hx.
        destruct hx as [hx | [<- | []]]; [exact (hpos x hx) | lia].
Qed.

Lemma run1_tailSeq18_safe (N : nat) :
  isSafeZero (fst (run1Full s4 0 (tailSeq18 N) 0)) = true.
Proof.
  destruct (tailSeq18_cons_prefix N) as [[_ h0] | [[_ h1] | [rest [hrest hpos]]]].
  - rewrite h0. reflexivity.
  - rewrite h1. reflexivity.
  - rewrite hrest.
    change (isSafeZero (fst (run1Full s4 0 (7 :: 7 :: rest) 0))) with
      (isSafeZero (2 :: fst (run1Full s1 2 rest 0))).
    pose proof (run1Full_from_s1_allPos s1 2 rest 0 (or_introl eq_refl) hpos) as hall.
    apply isSafeZero_of_allPos.
    intros x [<- | hx']; [lia | exact (hall x hx')].
Qed.

Lemma eraStream18_runs (N : nat) :
  exists r', RunEv (eraStream18 N) (w2 *> 0inf) r'.
Proof.
  pose proof (tailSeq18_allPos N) as hpos.
  pose proof (safe1_of_allPos s4 (tailSeq18 N) hpos) as hsafe1.
  assert (hinv4 : Inv1 s4 0 0%Q 2%Q) by (cbn [Inv1]; repeat split; qlra).
  pose proof (inv1_full s4 0 (tailSeq18 N) 0 0%Q 2%Q hinv4
    (proj1 (tailSeq18_good_from_2 N)) hsafe1) as hgood1.
  pose proof (run1_tailSeq18_safe N) as hsf1.
  set (res := run1Full s4 0 (tailSeq18 N) 0).
  fold res in hgood1, hsf1.
  destruct (main_stream (List.length (fst res)) (sum_list (fst res) + snd res)
    (fst res) (snd res) (Nat.le_refl _) (Nat.le_refl _) hgood1 hsf1) as [r1 hr1].
  pose proof (rep_B_run1Evs s4 0 (tailSeq18 N) 0 hsafe1) as hev_eq.
  cbn [repB List.app] in hev_eq. fold res in hev_eq.
  rewrite <- hev_eq in hr1.
  destruct (lift1_run s4 (tailSeq18 N) 0 hsafe1 hr1) as [r_end hrun_tail].
  cbn [repB tok1] in hrun_tail. rewrite app_nil_r in hrun_tail.
  assert (hstep1 : RunEv (gapEv 1) (w2 *> 0inf) (w4 *> 0inf)).
  { cbn [gapEv repB List.app].
    exact (RunEv_cons (stepEv_w2_B 0inf) (runEv_single (stepEv_w3_S 0inf))). }
  pose proof (runEv_append hstep1 hrun_tail) as hfull.
  change (gapEv 1 ++ gapsEv (tailSeq18 N)) with (gapsEv (1 :: tailSeq18 N)) in hfull.
  rewrite <- (eraStream18_eq_gapsEv N) in hfull.
  destruct (runEv_prefix hfull) as [r' [hr' _]].
  exists r'. exact hr'.
Qed.

Lemma multi_era18_reach (N : nat) {r r' : side}
    (h : RunEv (eraStream18 N) r r') :
  exists M, N <= M /\ eraCfg 18 r -[ tm_core ]->> M / eraCfg (18 + N) r'.
Proof.
  revert r' h.
  induction N as [| N IH]; intros r' h.
  - inversion h; subst. exists 0. split; [lia |].
    replace (18 + 0) with 18 by lia. constructor.
  - cbn [eraStream18] in h.
    destruct (runEv_prefix h) as [r_mid [hpre hlast]].
    destruct (IH r_mid hpre) as [M1 [hM1 hms1]].
    pose proof (era_step (18 + N) ltac:(lia) hlast) as hp2.
    destruct (progress_multistep _ _ _ hp2) as [d hms2].
    exists (M1 + S d). split; [lia |].
    replace (18 + S N) with ((18 + N) + 1) by lia.
    exact (multistep_trans _ _ _ _ _ _ hms1 hms2).
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact init_reaches_era18.
  - intros [k Hhalt].
    destruct (eraStream18_runs (S k)) as [r' hr'].
    destruct (multi_era18_reach (S k) hr') as [M [hM hms]].
    pose proof (multistep_conj M _ _ hms) as hconj.
    change (conjCfg (eraCfg 18 (w2 *> 0inf))) with
      (0inf <{{C}} (w1 ^^ 18 *> w0 *> wE *> w2 *> 0inf)) in hconj.
    exact (exceeds_halt tm _ _ M k Hhalt ltac:(lia) hconj).
Qed.
