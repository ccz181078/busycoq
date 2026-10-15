From Coq Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat NArith.NArith ZArith.ZArith QArith.QArith micromega.Lqa micromega.Lia.
From BusyCoq Require Import Individual62.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm : TM := Eval compute in (TM_from_str "1RB0RD_1RC---_1LD1LE_1LE0LC_1RF1LD_1RA0RF"%string).
Definition canon_tm : TM := Eval compute in (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1LF0LA_1RA1RB_1LE---"%string).

Fixpoint cconfig_steps (m : TM) (x : cconfig) (n : nat) : option cconfig :=
  match n with
  | O => Some x
  | S n0 =>
    match cconfig_step m x with
    | None => None
    | Some x0 => cconfig_steps m x0 n0
    end
  end.

Lemma cconfig_steps_spec (m : TM) (n : nat) : forall (x y : cconfig),
  cconfig_steps m x n = Some y ->
  cconfig_to_config x -[ m ]->* cconfig_to_config y.
Proof.
  induction n as [| n IH]; intros x y H; cbn in H.
  - inversion H; subst; finish.
  - pose proof (cconfig_step_spec m x) as Hstep.
    destruct (cconfig_step m x) as [x0 |] eqn:E; [| discriminate].
    eapply evstep_step; [exact Hstep | exact (IH x0 y H)].
Qed.

Fixpoint cconfig_steps_chunks (m : TM) (x : cconfig) (chunks chunk_size : nat) : option cconfig :=
  match chunks with
  | O => Some x
  | S k =>
    match cconfig_steps m x chunk_size with
    | None => None
    | Some x0 => cconfig_steps_chunks m x0 k chunk_size
    end
  end.

Lemma cconfig_steps_chunks_spec (m : TM) (chunks chunk_size : nat) : forall (x y : cconfig),
  cconfig_steps_chunks m x chunks chunk_size = Some y ->
  cconfig_to_config x -[ m ]->* cconfig_to_config y.
Proof.
  induction chunks as [| k IH]; intros x y H; cbn in H.
  - inversion H; subst; finish.
  - destruct (cconfig_steps m x chunk_size) as [x0 |] eqn:E; [| discriminate].
    eapply evstep_trans; [exact (cconfig_steps_spec m chunk_size x x0 E) | exact (IH x0 y H)].
Qed.

Definition cconfig_check_steps (m : TM) (x y : cconfig) (chunks chunk_size rem : nat) : bool :=
  match cconfig_steps_chunks m x chunks chunk_size with
  | None => false
  | Some x1 =>
    match cconfig_steps m x1 rem with
    | None => false
    | Some x2 => cconfig_eqb x2 y
    end
  end.

Lemma cconfig_check_steps_spec (m : TM) (x y : cconfig) (chunks chunk_size rem : nat) :
  cconfig_check_steps m x y chunks chunk_size rem = true ->
  cconfig_to_config x -[ m ]->* cconfig_to_config y.
Proof.
  unfold cconfig_check_steps; intros H.
  destruct (cconfig_steps_chunks m x chunks chunk_size) as [x1 |] eqn:E1; [| discriminate].
  destruct (cconfig_steps m x1 rem) as [x2 |] eqn:E2; [| discriminate].
  rewrite <- (cconfig_eqb_spec x2 y H).
  eapply evstep_trans; [exact (cconfig_steps_chunks_spec m chunks chunk_size x x1 E1) |].
  exact (cconfig_steps_spec m rem x1 x2 E2).
Qed.

Definition t : list sym := [1; 1; 0; 0].
Definition d0 : list sym := [0; 0].
Definition d1 : list sym := [1; 0].
Definition one : list sym := [1].
Definition lh : side := [1; 0; 1] *> 0inf.
Definition w_word : list sym := [0; 0; 0; 1; 1; 0; 1; 0].
Definition w_rest : list sym :=
  t ++ t ++ (t ++ d1) ++ t ++ (t ++ d0) ++ t ++ (t ++ d0) ++ t ++ t ++ d1 ++ (t ++ one).
Definition w_base : list sym := w_word ++ w_rest.

Lemma zDd : d0 *> 0inf = 0inf.
Proof. solve_const0_eq. Qed.

Inductive Call : Type := ch | cj | cp.

Definition zCs (c : Call) : Q :=
  match c with
  | ch => B
  | cj => A
  | cp => A
  end.

Definition zCw (c : Call) : list sym :=
  match c with
  | ch => [1]
  | cj => [1; 1]
  | cp => [1; 0]
  end.

Definition zCR (l : side) (c : Call) (r : side) : Q * tape :=
  (zCw c *> l) {{zCs c}}> r.

Definition zCL (l : side) (r : side) : Q * tape :=
  l <{{C}} ([0] *> r).

Definition zCf (r : side) : Q * tape :=
  zCL lh (w_base *> r).

Definition z04 (c : Call) (r1 r2 : side) : Prop :=
  forall l, zCR l c r1 -[ canon_tm ]->+ zCL l r2.

Inductive Side : list Call -> side -> side -> Prop :=
  | Side_nil (r : side) : Side [] r r
  | Side_cons {c : Call} {ls : list Call} {r1 r2 r3 : side} :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3.

Definition Seg (ls_in ls_out : list Call) (w1 w2 : list sym) : Prop :=
  forall r1 r2, Side ls_out r1 r2 -> Side ls_in (w1 *> r1) (w2 *> r2).

Lemma zLp' {X : Type} (l : list X) (n : nat) : l ^^ (1 + n) = l ++ l ^^ n.
Proof. reflexivity. Qed.

Lemma z06 {X : Type} (l : list X) : l ^^ 1 = l.
Proof. cbn; apply app_nil_r. Qed.

Lemma z07 {X : Type} (l : list X) (m n : nat) : l ^^ (m + n) = l ^^ m ++ l ^^ n.
Proof. apply lpow_add. Qed.

Lemma z08 {ls1 ls2 : list Call} {r1 r2 r3 : side}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3.
Proof.
  induction h1 as [| c ls r1' r_mid r2' hc _ IH].
  - exact h2.
  - exact (Side_cons hc (IH h2)).
Qed.

Lemma z09 {ls1 ls2 : list Call} {r1 r3 : side}
    (h : Side (ls1 ++ ls2) r1 r3) : exists r2, Side ls1 r1 r2 /\ Side ls2 r2 r3.
Proof.
  revert r1 h.
  induction ls1 as [| c ls1 IH]; intros r1 h.
  - exists r1; split; [exact (Side_nil r1) | exact h].
  - inversion h as [| c' ls' r1' r_mid r3' hc hrest]; subst.
    destruct (IH r_mid hrest) as [r2 [h1 h2]].
    exists r2; split; [exact (Side_cons hc h1) | exact h2].
Qed.

Lemma z0a (w : list sym) : Seg [] [] w w.
Proof.
  intros r1 r2 h; inversion h; subst; exact (Side_nil (w *> r2)).
Qed.

Lemma z0m_id (ls : list Call) : Seg ls ls [] [].
Proof.
  intros r1 r2 h; exact h.
Qed.

Lemma zSc {ls1 ls2 : list Call} {w1 w2 : list sym} {r1 r2 : side}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 *> r1) (w2 *> r2).
Proof. exact (h1 r1 r2 h2). Qed.

Lemma zSg {ls1 ls2 ls3 ls4 : list Call} {w1 w2 w3 : list sym}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3.
Proof.
  intros r1 r3 h.
  destruct (z09 h) as [r2 [ha hb]].
  exact (z08 (h1 r1 r2 ha) (h2 r2 r3 hb)).
Qed.

Lemma zS0 {ls1 ls2 ls3 : list Call} {w1 w2 v1 v2 : list sym}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2).
Proof.
  intros r1 r2 h.
  rewrite !Str_app_assoc.
  exact (h1 (v1 *> r1) (v2 *> r2) (h2 r1 r2 h)).
Qed.

Lemma zS4 {c : Call} {w1 w2 : list sym}
    (h1 : forall l r, zCR l c (w1 *> r) -[ canon_tm ]->+ zCL l (w2 *> r)) :
    Seg [c] [] w1 w2.
Proof.
  intros r1 r2 h; inversion h; subst.
  exact (Side_cons (fun l => h1 l r2) (Side_nil _)).
Qed.

Lemma zS2 (mid : list sym) {c_in c_out : Call} {w1 w2 : list sym}
    (h1 : forall l r, zCR l c_in (w1 *> r) -[ canon_tm ]->+ zCR (mid *> l) c_out r)
    (h2 : forall l r, zCL (mid *> l) r -[ canon_tm ]->+ zCL l (w2 *> r)) :
    Seg [c_in] [c_out] w1 w2.
Proof.
  intros r1 r2 h.
  inversion h as [| ? ? ? r_mid ? hc hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun l => _) (Side_nil _)).
  eapply progress_trans; [exact (h1 l r1) |].
  eapply progress_trans; [exact (hc (mid *> l)) | exact (h2 l r2)].
Qed.

Lemma zS5 (mid1 mid2 : list sym) {c_in c1 c2 : Call} {w1 w2 : list sym}
    (h1 : forall l r, zCR l c_in (w1 *> r) -[ canon_tm ]->+ zCR (mid1 *> l) c1 r)
    (h2 : forall l r, zCL (mid1 *> l) r -[ canon_tm ]->+ zCR (mid2 *> l) c2 r)
    (h3 : forall l r, zCL (mid2 *> l) r -[ canon_tm ]->+ zCL l (w2 *> r)) :
    Seg [c_in] [c1; c2] w1 w2.
Proof.
  intros r1 r3 h.
  inversion h as [| ? ? ? r_mid1 ? hc1 hrest]; subst.
  inversion hrest as [| ? ? ? r_mid2 ? hc2 hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun l => _) (Side_nil _)).
  eapply progress_trans; [exact (h1 l r1) |].
  eapply progress_trans; [exact (hc1 (mid1 *> l)) |].
  eapply progress_trans; [exact (h2 l r_mid1) |].
  eapply progress_trans; [exact (hc2 (mid2 *> l)) | exact (h3 l r3)].
Qed.

Lemma zS6 (mid1 mid2 mid3 : list sym) {c_in c1 c2 c3 : Call} {w1 w2 : list sym}
    (h1 : forall l r, zCR l c_in (w1 *> r) -[ canon_tm ]->+ zCR (mid1 *> l) c1 r)
    (h2 : forall l r, zCL (mid1 *> l) r -[ canon_tm ]->+ zCR (mid2 *> l) c2 r)
    (h3 : forall l r, zCL (mid2 *> l) r -[ canon_tm ]->+ zCR (mid3 *> l) c3 r)
    (h4 : forall l r, zCL (mid3 *> l) r -[ canon_tm ]->+ zCL l (w2 *> r)) :
    Seg [c_in] [c1; c2; c3] w1 w2.
Proof.
  intros r1 r4 h.
  inversion h as [| ? ? ? r_mid1 ? hc1 hrest]; subst.
  inversion hrest as [| ? ? ? r_mid2 ? hc2 hrest2]; subst.
  inversion hrest2 as [| ? ? ? r_mid3 ? hc3 hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun l => _) (Side_nil _)).
  eapply progress_trans; [exact (h1 l r1) |].
  eapply progress_trans; [exact (hc1 (mid1 *> l)) |].
  eapply progress_trans; [exact (h2 l r_mid1) |].
  eapply progress_trans; [exact (hc2 (mid2 *> l)) |].
  eapply progress_trans; [exact (h3 l r_mid2) |].
  eapply progress_trans; [exact (hc3 (mid3 *> l)) | exact (h4 l r4)].
Qed.

Ltac exec_canon :=
  intros; unfold zCR, zCL, zCw, zCs, t, d0, d1, one, lh, w_word;
  cbn [Str_app List.app hd tl];
  eapply progress_intro;
  [ (apply @step_left; reflexivity) || (apply @step_right; reflexivity)
  | repeat (
      try rewrite move_left_const; try rewrite move_right_const;
      cbn [move_left move_right hd tl Str_app List.app];
      repeat rewrite <- const_unfold;
      first
      [ apply evstep_refl'; reflexivity
      | eapply evstep_step;
        [ (apply @step_left; reflexivity) || (apply @step_right; reflexivity) | ] ]) ].

Lemma z0b : Seg [cp] [] t [1; 1; 0; 1; 0].
Proof. apply zS4; exec_canon. Qed.

Lemma z0c_p : Seg [ch] [cp; ch] [1; 1; 0; 1; 0] t.
Proof. apply (zS5 [1; 0; 1; 1] [1; 0; 1; 0]); exec_canon. Qed.

Lemma z0c : Seg [cj] [cp] t t.
Proof. apply (zS2 [1; 0; 1; 0]); exec_canon. Qed.

Lemma zH2 : Seg [ch] [cj; ch] (t ++ one) t.
Proof. apply (zS5 [1; 0; 1; 1] [1; 0; 1; 0]); exec_canon. Qed.

Lemma z0d : Seg [ch] [ch; ch] t t.
Proof. apply (zS5 [1; 0; 1; 1] [1; 0; 1; 0]); exec_canon. Qed.

Lemma z0e : Seg [cp] [] (d1 ++ d0) (t ++ one).
Proof. apply zS4; exec_canon. Qed.

Lemma z0f : Seg [cj] [cj] (d1 ++ d0) t.
Proof. apply (zS2 [1; 0; 1; 0]); exec_canon. Qed.

Lemma z0g : Seg [cp] [cp] (d1 ++ d1) t.
Proof. apply (zS2 [1; 0; 1; 0]); exec_canon. Qed.

Lemma z0h : Seg [cj] [cp; ch] (d1 ++ d1) t.
Proof. apply (zS5 [1; 0; 1; 1] [1; 0; 1; 0]); exec_canon. Qed.

Lemma z0i : Seg [cj] [] d0 (d0 ++ one).
Proof. apply zS4; exec_canon. Qed.

Lemma zH1 : Seg [ch] [] (d0 ++ one) (d1 ++ one).
Proof. apply zS4; exec_canon. Qed.

Lemma zH3 : Seg [ch] [cj] (d1 ++ one) d0.
Proof. apply (zS2 [1; 1]); exec_canon. Qed.

Lemma z0j : Seg [cj] [cp] d1 d0.
Proof. apply (zS2 [1; 1]); exec_canon. Qed.

Lemma zH0 : Seg [ch] [] d0 d1.
Proof. apply zS4; exec_canon. Qed.

Lemma zH4 : Seg [ch] [ch] d1 d0.
Proof. apply (zS2 [1; 1]); exec_canon. Qed.

Lemma zC_base : Seg [cp] [ch; cp] [0; 1; 1; 1] t.
Proof. apply (zS5 [0; 1; 1; 1; 0] [1; 0; 1; 0]); exec_canon. Qed.

Lemma zO_head : Seg [cp] [] [1; 0; 0; 0] [1; 1; 0; 0; 1].
Proof. apply zS4; exec_canon. Qed.

Lemma zO_mid : Seg [ch] [ch; cp; ch] [1; 0; 1; 1; 1] t.
Proof. apply (zS6 [0; 1; 1; 1; 1] [1; 0; 1; 1] [1; 0; 1; 0]); exec_canon. Qed.

Lemma zO_b0 : Seg [cp] [ch] [1; 1] [1; 1; 0].
Proof. apply (zS2 [0; 1; 0]); exec_canon. Qed.

Lemma zO_b2 : Seg [ch] [cp] [1; 1; 0] d0.
Proof. apply (zS2 [1; 1]); exec_canon. Qed.

Lemma zE_head : Seg [cj] [] [0; 0; 1; 0; 0; 0] [0; 0; 1; 1; 0; 0; 0].
Proof. apply zS4; exec_canon. Qed.

Lemma zE_b0 : Seg [cj] [] [0; 0; 1; 1] [0; 0; 1; 1; 1].
Proof. apply zS4; exec_canon. Qed.

Lemma zW_td1a : Seg [cp] [] (t ++ d1) [1; 1; 0; 1; 0; 1; 0].
Proof. apply zS4; exec_canon. Qed.

Lemma zW_td1b : Seg [ch] [cp] [1; 1; 0; 1; 0; 1; 0] (d0 ++ t).
Proof. apply (zS2 [1; 0; 1; 0; 1; 1]); exec_canon. Qed.

Lemma zW_td0a : Seg [cp] [] (t ++ d0) [1; 1; 0; 1; 0; 0; 0].
Proof. apply zS4; exec_canon. Qed.

Lemma zW_td0b : Seg [ch] [] [1; 1; 0; 1; 0; 0; 0] (d0 ++ (t ++ one)).
Proof. apply zS4; exec_canon. Qed.

Lemma zS3 (n : nat) : Seg ([ch] ^^ n) ([ch] ^^ (n * 2)) t t.
Proof.
  induction n as [| n IH].
  - exact (z0a t).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite (lpow_S n [ch]), (z07 [ch] 2 (n * 2)).
    exact (zSg z0d IH).
Qed.

Lemma zT_pow (r : nat) : forall n, Seg ([ch] ^^ n) ([ch] ^^ (n * 2 ^ r)) (t ^^ r) (t ^^ r).
Proof.
  induction r as [| r IH]; intros n.
  - replace (n * 2 ^ 0) with n by (cbn; lia).
    exact (z0m_id _).
  - replace (n * 2 ^ S r) with ((n * 2) * 2 ^ r) by (cbn [Nat.pow]; lia).
    rewrite (lpow_S r t).
    exact (zS0 (zS3 n) (IH (n * 2))).
Qed.

Lemma zSa {w2 : list sym} (hw : Seg [ch; ch] [ch] w2 w2) (n : nat) :
    Seg ([ch] ^^ (n * 2)) ([ch] ^^ n) w2 w2.
Proof.
  induction n as [| n IH].
  - exact (z0a w2).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite (z07 [ch] 2 (n * 2)), (lpow_S n [ch]).
    exact (zSg hw IH).
Qed.

Lemma z0k : Seg [ch; ch] [ch] d0 d0.
Proof. exact (zSg zH0 zH4). Qed.

Lemma z0l : Seg [ch; ch] [ch] d1 d1.
Proof. exact (zSg zH4 zH0). Qed.

Lemma zH_d0_even (n : nat) : Seg ([ch] ^^ (n * 2)) ([ch] ^^ n) d0 d0.
Proof. exact (zSa z0k n). Qed.

Lemma zH_d0_odd (n : nat) : Seg ([ch] ^^ (1 + n * 2)) ([ch] ^^ n) d0 d1.
Proof.
  change ([ch] ^^ (1 + n * 2)) with ([ch] ++ [ch] ^^ (n * 2)).
  change ([ch] ^^ n) with ([] ++ [ch] ^^ n).
  exact (zSg zH0 (zSa z0l n)).
Qed.

Lemma zH_d1_even (n : nat) : Seg ([ch] ^^ (n * 2)) ([ch] ^^ n) d1 d1.
Proof. exact (zSa z0l n). Qed.

Lemma z0m (n : nat) : Seg ([cp] ++ [ch] ^^ (1 + n)) ([cp] ++ [ch] ^^ (1 + n * 2)) t t.
Proof.
  change ([cp] ++ [ch] ^^ (1 + n)) with (([cp] ++ [ch]) ++ [ch] ^^ n).
  change ([cp] ++ [ch] ^^ (1 + n * 2)) with (([cp; ch]) ++ [ch] ^^ (n * 2)).
  exact (zSg (zSg z0b z0c_p) (zS3 n)).
Qed.

Lemma z0n (n : nat) : Seg ([cj] ++ [ch] ^^ n) ([cp] ++ [ch] ^^ (n * 2)) t t.
Proof. exact (zSg z0c (zS3 n)). Qed.

Lemma z0o (n : nat) : Seg ([cp] ++ [ch] ^^ (1 + n)) ([cj] ++ [ch] ^^ (1 + n * 2)) (d1 ++ d0) t.
Proof.
  change ([cp] ++ [ch] ^^ (1 + n)) with (([cp] ++ [ch]) ++ [ch] ^^ n).
  change ([cj] ++ [ch] ^^ (1 + n * 2)) with (([cj; ch]) ++ [ch] ^^ (n * 2)).
  exact (zSg (zSg z0e zH2) (zS3 n)).
Qed.

Lemma z0p (n : nat) : Seg ([cj] ++ [ch] ^^ n) ([cj] ++ [ch] ^^ (n * 2)) (d1 ++ d0) t.
Proof. exact (zSg z0f (zS3 n)). Qed.

Lemma z0q (n : nat) : Seg ([cp] ++ [ch] ^^ n) ([cp] ++ [ch] ^^ (n * 2)) (d1 ++ d1) t.
Proof. exact (zSg z0g (zS3 n)). Qed.

Lemma z0r (n : nat) : Seg ([cj] ++ [ch] ^^ n) ([cp] ++ [ch] ^^ (1 + n * 2)) (d1 ++ d1) t.
Proof.
  change ([cp] ++ [ch] ^^ (1 + n * 2)) with ([cp; ch] ++ [ch] ^^ (n * 2)).
  exact (zSg z0h (zS3 n)).
Qed.

Lemma z0s (n : nat) : Seg ([cj] ++ [ch] ^^ (2 + n * 2)) ([cj] ++ [ch] ^^ n) d0 d0.
Proof.
  change ([cj] ++ [ch] ^^ (2 + n * 2)) with (([cj] ++ ([ch] ++ [ch])) ++ [ch] ^^ (n * 2)).
  exact (zSg (zSg z0i (zSg zH1 zH3)) (zSa z0k n)).
Qed.

Lemma z0t (n : nat) : Seg ([cj] ++ [ch] ^^ (n * 2)) ([cp] ++ [ch] ^^ n) d1 d0.
Proof. exact (zSg z0j (zSa z0k n)). Qed.

Lemma z0u : Seg [cj; ch] [] d0 (d1 ++ one).
Proof. exact (zSg z0i zH1). Qed.

Lemma z0v (n : nat) : Seg ([cj] ++ [ch] ^^ (3 + n * 2)) ([cj] ++ [ch] ^^ n) d0 d1.
Proof.
  change ([cj] ++ [ch] ^^ (3 + n * 2)) with (([cj] ++ ([ch] ++ ([ch] ++ [ch]))) ++ [ch] ^^ (n * 2)).
  exact (zSg (zSg z0i (zSg zH1 (zSg zH3 zH0))) (zSa z0l n)).
Qed.

Lemma z0w (n : nat) : Seg ([cj] ++ [ch] ^^ (1 + n * 2)) ([cp] ++ [ch] ^^ n) d1 d1.
Proof.
  change ([cj] ++ [ch] ^^ (1 + n * 2)) with (([cj] ++ [ch]) ++ [ch] ^^ (n * 2)).
  exact (zSg (zSg z0j zH0) (zSa z0l n)).
Qed.

Lemma zCp_step {r r_out : side} (h : Side [cp] ([0; 1] *> r) r_out) :
    Side [cp] ([0; 1; 1; 0; 0; 0] *> r) (t *> r_out).
Proof.
  inversion h as [| ? ? ? r_mid ? hcp hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun l => _) (Side_nil _)).
  assert (h1 : zCR l cp ([0; 1; 1; 0; 0; 0] *> r) -[ canon_tm ]->+ zCR ([1; 0; 1; 0] *> l) cp ([0; 1] *> r)) by exec_canon.
  assert (h2 : zCL ([1; 0; 1; 0] *> l) r_out -[ canon_tm ]->+ zCL l (t *> r_out)) by exec_canon.
  eapply progress_trans; [exact h1 |].
  eapply progress_trans; [exact (hcp ([1; 0; 1; 0] *> l)) | exact h2].
Qed.

Lemma zCp_chain (m : nat) :
    Seg [cp] [ch; cp] ([0; 1] ++ (d1 ++ d0) ^^ m ++ [1; 1]) (t ^^ (1 + m)).
Proof.
  induction m as [| m IH].
  - cbn [lpow app].
    change (t ++ []) with t.
    exact zC_base.
  - intros r1 r2 h.
    pose proof (IH r1 r2 h) as h_sub.
    assert (h_mid : ([0; 1] ++ (d1 ++ d0) ^^ m ++ [1; 1]) *> r1 =
        [0; 1] *> (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1)) by reflexivity.
    rewrite h_mid in h_sub.
    pose proof (zCp_step h_sub) as h_step.
    assert (h_in : ([0; 1] ++ (d1 ++ d0) ^^ S m ++ [1; 1]) *> r1 =
        [0; 1; 1; 0; 0; 0] *> (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1)) by reflexivity.
    rewrite <- h_in in h_step.
    assert (h_out : t *> (t ^^ (1 + m) *> r2) = t ^^ (1 + S m) *> r2).
    { change (t ^^ (1 + S m)) with (t ++ t ^^ (1 + m)).
      symmetry; apply Str_app_assoc. }
    rewrite <- h_out.
    exact h_step.
Qed.

Lemma zOdd_base (r : nat) :
    Seg [cp; ch] [ch; cp] ((d1 ++ d0) ^^ r ++ [1; 1]) (d0 ++ t ^^ r).
Proof.
  destruct r as [| m].
  - cbn [lpow app].
    change (d0 ++ []) with d0.
    exact (zSg zO_b0 zO_b2).
  - assert (h1 : Seg [cp] [] ([1; 0; 0; 0] ++ ((d1 ++ d0) ^^ m ++ [1; 1])) ([1; 1; 0; 0; 1] ++ ((d1 ++ d0) ^^ m ++ [1; 1])))
      by exact (zS0 zO_head (z0a _)).
    assert (h2 : Seg [ch] [ch; cp] ([1; 1; 0] ++ ([0; 1] ++ (d1 ++ d0) ^^ m ++ [1; 1])) (d0 ++ t ^^ (1 + m)))
      by exact (zS0 zO_b2 (zCp_chain m)).
    change ((d1 ++ d0) ^^ S m ++ [1; 1]) with ([1; 0; 0; 0] ++ ((d1 ++ d0) ^^ m ++ [1; 1])).
    change ([1; 1; 0; 0; 1] ++ ((d1 ++ d0) ^^ m ++ [1; 1])) with ([1; 1; 0] ++ ([0; 1] ++ (d1 ++ d0) ^^ m ++ [1; 1])) in h1.
    exact (zSg h1 h2).
Qed.

Lemma zEven_ch_step {r r_mid r_out : side}
    (h1 : Side [cp] ([0; 1] *> r) r_mid)
    (h2 : Side [ch] r_mid r_out) :
    Side [ch] ([1; 0; 1; 1; 0; 0; 0] *> r) (t *> r_out).
Proof.
  inversion h1 as [| ? ? ? ? ? hcp hnil1]; subst; inversion hnil1; subst.
  inversion h2 as [| ? ? ? ? ? hch hnil2]; subst; inversion hnil2; subst.
  refine (Side_cons (fun l => _) (Side_nil _)).
  assert (hs1 : zCR l ch ([1; 0; 1; 1; 0; 0; 0] *> r) -[ canon_tm ]->+ zCR ([1; 0; 1; 1] *> l) cp ([0; 1] *> r)) by exec_canon.
  assert (hs2 : zCL ([1; 0; 1; 1] *> l) r_mid -[ canon_tm ]->+ zCR ([1; 0; 1; 0] *> l) ch r_mid) by exec_canon.
  assert (hs3 : zCL ([1; 0; 1; 0] *> l) r_out -[ canon_tm ]->+ zCL l (t *> r_out)) by exec_canon.
  eapply progress_trans; [exact hs1 |].
  eapply progress_trans; [exact (hcp ([1; 0; 1; 1] *> l)) |].
  eapply progress_trans; [exact hs2 |].
  eapply progress_trans; [exact (hch ([1; 0; 1; 0] *> l)) | exact hs3].
Qed.

Lemma zEven_base (r : nat) :
    Seg [cj; ch; ch] ([ch; cp] ++ [ch] ^^ (2 ^ r)) (d0 ++ (d1 ++ d0) ^^ r ++ [1; 1]) (t ^^ (1 + r)).
Proof.
  destruct r as [| m].
  - assert (h1 : Seg [cj] [] [0; 0; 1; 1] [0; 0; 1; 1; 1]) by exact zE_b0.
    assert (h2 : Seg [ch] [] ([0; 0] ++ [1; 1; 1]) ([1; 0] ++ [1; 1; 1])) by exact (zS0 zH0 (z0a [1; 1; 1])).
    assert (h3 : Seg [ch] [ch; cp; ch] [1; 0; 1; 1; 1] t) by exact zO_mid.
    cbn [Nat.pow lpow app].
    change (t ++ []) with t.
    exact (zSg h1 (zSg h2 h3)).
  - intros r1 r2 h.
    replace (2 ^ S m) with (1 * 2 ^ (1 + m)) in h by (cbn [Nat.add Nat.mul]; lia).
    destruct (z09 h) as [r_mid [h_cp h_ch_pow]].
    pose proof (zCp_chain m r1 r_mid h_cp) as h_cp_seg.
    pose proof (zT_pow (1 + m) 1 r_mid r2 h_ch_pow) as h_ch_seg.
    cbn [lpow app] in h_ch_seg.
    assert (h_mid_eq : ([0; 1] ++ (d1 ++ d0) ^^ m ++ [1; 1]) *> r1 = [0; 1] *> (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1))
      by reflexivity.
    rewrite h_mid_eq in h_cp_seg.
    pose proof (zEven_ch_step h_cp_seg h_ch_seg) as h_step3.
    assert (h_step2 : Side [ch; ch] ([0; 0; 1; 1; 0; 0; 0] *> (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1)) (t *> (t ^^ (1 + m) *> r2))).
    { pose proof ((zS0 zH0 (z0a [1; 1; 0; 0; 0])) (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1) _ (Side_nil _)) as h_s2.
      exact (z08 h_s2 h_step3). }
    assert (h_step1 : Side [cj; ch; ch] ([0; 0; 1; 0; 0; 0] *> (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1)) (t *> (t ^^ (1 + m) *> r2))).
    { pose proof (zE_head (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1) _ (Side_nil _)) as h_s1.
      exact (z08 h_s1 h_step2). }
    assert (h_in : (d0 ++ (d1 ++ d0) ^^ S m ++ [1; 1]) *> r1 = [0; 0; 1; 0; 0; 0] *> (((d1 ++ d0) ^^ m ++ [1; 1]) *> r1))
      by reflexivity.
    assert (h_out : t ^^ (1 + S m) *> r2 = t *> (t ^^ (1 + m) *> r2)).
    { change (t ^^ (1 + S m)) with (t ++ t ^^ (1 + m)).
      apply Str_app_assoc. }
    rewrite h_in, h_out.
    exact h_step1.
Qed.

Lemma zW_turn {r r' : side} (h : Side [ch; cj; ch] r r') :
    zCL lh (w_word *> r) -[ canon_tm ]->+ zCL lh ((w_word ++ t ++ t ++ (t ++ d1)) *> r').
Proof.
  inversion h as [| ? ? ? r_mid1 ? hc1 hrest1]; subst.
  inversion hrest1 as [| ? ? ? r_mid2 ? hc2 hrest2]; subst.
  inversion hrest2 as [| ? ? ? ? ? hc3 hnil]; subst.
  inversion hnil; subst.
  assert (h1a : zCL lh (w_word *> r) -[ canon_tm ]->+
      ([1; 1; 0; 1; 1; 1; 1; 0; 1] *> 0inf) <{{C}} ([1; 1; 1; 0; 0; 0; 0; 1; 1; 1; 0; 1; 0] *> r)) by exec_canon.
  assert (h1b : ([1; 1; 0; 1; 1; 1; 1; 0; 1] *> 0inf) <{{C}} ([1; 1; 1; 0; 0; 0; 0; 1; 1; 1; 0; 1; 0] *> r) -[ canon_tm ]->+
      zCR ([1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) ch r) by exec_canon.
  assert (h2a : forall s1, zCL ([1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) s1 -[ canon_tm ]->+
      ([1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) {{A}}> ([1; 0; 1; 0; 0; 0; 0; 1] *> s1)) by exec_canon.
  assert (h2b : forall s1, ([1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) {{A}}> ([1; 0; 1; 0; 0; 0; 0; 1] *> s1) -[ canon_tm ]->+
      zCR ([1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) cj s1) by exec_canon.
  assert (h3 : forall s2, zCL ([1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) s2 -[ canon_tm ]->+
      zCR ([1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) ch s2) by exec_canon.
  assert (h4a : zCL ([1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) r' -[ canon_tm ]->+
      ([1; 0; 0; 1] *> 0inf) <{{D}} ([1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 0] *> r')) by exec_canon.
  assert (h4b : ([1; 0; 0; 1] *> 0inf) <{{D}} ([1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 0] *> r') -[ canon_tm ]->+
      zCL lh ((w_word ++ t ++ t ++ (t ++ d1)) *> r')) by exec_canon.
  eapply progress_trans; [eapply progress_trans; [exact h1a | exact h1b] |].
  eapply progress_trans; [exact (hc1 _) |].
  eapply progress_trans; [eapply progress_trans; [exact (h2a _) | exact (h2b _)] |].
  eapply progress_trans; [exact (hc2 _) |].
  eapply progress_trans; [exact (h3 _) |].
  eapply progress_trans; [exact (hc3 _) |].
  eapply progress_trans; [exact h4a | exact h4b].
Qed.

Lemma zW_s1 : Seg [ch; cj; ch] ([ch] ^^ 2 ++ [cp] ++ [ch] ^^ 2) t t.
Proof. exact (zSg z0d (zSg z0c z0d)). Qed.

Lemma zW_s2 : Seg ([ch] ^^ 2 ++ [cp] ++ [ch] ^^ 2) ([ch] ^^ 4 ++ [cp] ++ [ch] ^^ 3) t t.
Proof. exact (zSg (zS3 2) (z0m 1)). Qed.

Lemma zW_s3 : Seg ([ch] ^^ 4 ++ [cp] ++ [ch] ^^ 3) ([ch] ^^ 4 ++ [cp] ++ [ch] ^^ 2) (t ++ d1) (d0 ++ t).
Proof.
  assert (ha : Seg ([ch] ^^ 4) ([ch] ^^ 4) (t ++ d1) (t ++ d1)) by exact (zS0 (zS3 4) (zH_d1_even 4)).
  assert (hb1 : Seg [cp; ch] [cp] (t ++ d1) (d0 ++ t)) by exact (zSg zW_td1a zW_td1b).
  assert (hb2 : Seg ([ch] ^^ 2) ([ch] ^^ 2) (d0 ++ t) (d0 ++ t)) by exact (zS0 (zH_d0_even 1) (zS3 1)).
  assert (hb : Seg ([cp] ++ [ch] ^^ 3) ([cp] ++ [ch] ^^ 2) (t ++ d1) (d0 ++ t)) by exact (zSg hb1 hb2).
  exact (zSg ha hb).
Qed.

Lemma zW_s4 : Seg ([ch] ^^ 4 ++ [cp] ++ [ch] ^^ 2) ([ch] ^^ 8 ++ [cp] ++ [ch] ^^ 3) t t.
Proof. exact (zSg (zS3 4) (z0m 1)). Qed.

Lemma zW_s5 : Seg ([ch] ^^ 8 ++ [cp] ++ [ch] ^^ 3) ([ch] ^^ 8 ++ [cj; ch]) (t ++ d0) (d0 ++ t).
Proof.
  assert (ha : Seg ([ch] ^^ 8) ([ch] ^^ 8) (t ++ d0) (t ++ d0)) by exact (zS0 (zS3 8) (zH_d0_even 8)).
  assert (hb1 : Seg [cp; ch] [] (t ++ d0) (d0 ++ (t ++ one))) by exact (zSg zW_td0a zW_td0b).
  assert (hb2 : Seg [ch] [] (d0 ++ (t ++ one)) (d1 ++ (t ++ one))) by exact (zS0 zH0 (z0a (t ++ one))).
  assert (hb3 : Seg [ch] [cj; ch] (d1 ++ (t ++ one)) (d0 ++ t)) by exact (zS0 zH4 zH2).
  assert (hb : Seg ([cp] ++ [ch] ^^ 3) [cj; ch] (t ++ d0) (d0 ++ t)) by exact (zSg hb1 (zSg hb2 hb3)).
  exact (zSg ha hb).
Qed.

Lemma zW_s6 : Seg ([ch] ^^ 8 ++ [cj; ch]) ([ch] ^^ 16 ++ [cp] ++ [ch] ^^ 2) t t.
Proof. exact (zSg (zS3 8) (z0n 1)). Qed.

Lemma zW_s7 : Seg ([ch] ^^ 16 ++ [cp] ++ [ch] ^^ 2) ([ch] ^^ 16) (t ++ d0) (d1 ++ (t ++ one)).
Proof.
  assert (ha : Seg ([ch] ^^ 16) ([ch] ^^ 16) (t ++ d0) (t ++ d0)) by exact (zS0 (zS3 16) (zH_d0_even 16)).
  assert (hb1 : Seg [cp; ch] [] (t ++ d0) (d0 ++ (t ++ one))) by exact (zSg zW_td0a zW_td0b).
  assert (hb2 : Seg [ch] [] (d0 ++ (t ++ one)) (d1 ++ (t ++ one))) by exact (zS0 zH0 (z0a (t ++ one))).
  assert (hb : Seg ([cp] ++ [ch] ^^ 2) [] (t ++ d0) (d1 ++ (t ++ one))) by exact (zSg hb1 hb2).
  change ([ch] ^^ 16) with ([ch] ^^ 16 ++ []) at 2.
  exact (zSg ha hb).
Qed.

Lemma zW_s8 : Seg ([ch] ^^ 16) ([ch] ^^ 32) t t.
Proof. exact (zS3 16). Qed.

Lemma zW_s9 : Seg ([ch] ^^ 32) ([ch] ^^ 64) t t.
Proof. exact (zS3 32). Qed.

Lemma zW_s10 : Seg ([ch] ^^ 64) ([ch] ^^ 32) d1 d1.
Proof. exact (zH_d1_even 32). Qed.

Lemma zW_s11 : Seg ([ch] ^^ 32) ([cj] ++ [ch] ^^ 63) (t ++ one) t.
Proof.
  change ([ch] ^^ 32) with ([ch] ++ [ch] ^^ 31).
  change ([cj] ++ [ch] ^^ 63) with ([cj; ch] ++ [ch] ^^ (31 * 2)).
  exact (zSg zH2 (zS3 31)).
Qed.

Lemma zW_rest_seg :
    Seg [ch; cj; ch] ([cj] ++ [ch] ^^ 63) w_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one)) ++ t ++ t ++ d1 ++ t).
Proof.
  unfold w_rest.
  exact (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 zW_s1 zW_s2) zW_s3) zW_s4) zW_s5) zW_s6) zW_s7) zW_s8) zW_s9) zW_s10) zW_s11).
Qed.

Lemma zW_full {r r' : side} (h : Side ([cj] ++ [ch] ^^ 63) r r') :
    zCf r -[ canon_tm ]->+ zCf ((t ++ t ++ d1 ++ t) *> r').
Proof.
  pose proof (zW_rest_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  assert (h_in : w_word *> (w_rest *> r) = w_base *> r) by (unfold w_base; rewrite Str_app_assoc; reflexivity).
  assert (h_out : (w_word ++ t ++ t ++ (t ++ d1)) *>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one)) ++ t ++ t ++ d1 ++ t) *> r') =
      w_base *> ((t ++ t ++ d1 ++ t) *> r')) by reflexivity.
  unfold zCf.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

(* ---------- Words, zQK, zTs, BRIncs, Num, z2f ---------- *)

Inductive Word : Type := WV | WK | WQ.
Notation zW := (list Word).
Notation zR n x := (repeat x n).

Fixpoint zQK (r : nat) (u : zW) : zW :=
  match r with
  | O => u
  | S r' => WQ :: WK :: zQK r' u
  end.

Lemma zQK_append (r : nat) (u v : zW) :
  zQK r (u ++ v) = zQK r u ++ v.
Proof.
  induction r as [| r IH]; [reflexivity |].
  cbn [zQK app]; rewrite IH; reflexivity.
Qed.

Fixpoint zTs (u : zW) (r : side) : side :=
  match u with
  | [] => r
  | WV :: u' => t *> zTs u' r
  | WK :: u' => d0 *> zTs u' r
  | WQ :: u' => d1 *> zTs u' r
  end.

Lemma z0S (u v : zW) (r : side) :
  zTs (u ++ v) r = zTs u (zTs v r).
Proof.
  induction u as [| a u IH]; [reflexivity |].
  destruct a; cbn [app zTs]; rewrite IH; reflexivity.
Qed.

Lemma zTs_R (r_ch : nat) (r : side) :
  zTs (zR r_ch WV) r = (t ^^ r_ch) *> r.
Proof.
  induction r_ch as [| r_ch IH]; [reflexivity |].
  cbn [repeat zTs lpow]; rewrite IH, Str_app_assoc; reflexivity.
Qed.

Lemma zTs_QK (r_ch : nat) (r : side) :
  zTs (zQK r_ch [WV]) r = ((d1 ++ d0) ^^ r_ch ++ [1; 1]) *> (d0 *> r).
Proof.
  induction r_ch as [| r_ch IH]; [reflexivity |].
  cbn [zQK zTs lpow]; rewrite IH.
  change (d1 *> (d0 *> (((d1 ++ d0) ^^ r_ch ++ [1; 1]) *> (d0 *> r))))
    with (((d1 ++ d0) ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1])) *> (d0 *> r)).
  rewrite <- app_assoc; reflexivity.
Qed.

Inductive BRIncs : bool -> nat -> side -> side -> Prop :=
  | BRIncs_zero (r : side) : BRIncs false 0 r (one *> r)
  | BRIncs_T {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (2 + n) (t *> r) (t *> r')
  | BRIncs_pair0 {n : nat} {r r' : side} :
      BRIncs false (n * 2) r r' -> BRIncs false (1 + n) (d1 *> (d0 *> r)) (t *> r')
  | BRIncs_pair1 {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (1 + n) (d1 *> (d1 *> r)) (t *> r')
  | BRIncs_short00 {n : nat} {r r' : side} :
      BRIncs false (n * 2) r r' -> BRIncs false (2 + n * 4) (d0 *> r) (d0 *> r')
  | BRIncs_short01 {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (2 + n * 4) (d1 *> r) (d0 *> r')
  | BRIncs_short10 {n : nat} {r r' : side} :
      BRIncs false (n * 2) r r' -> BRIncs false (4 + n * 4) (d0 *> r) (d1 *> r')
  | BRIncs_short11 {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (4 + n * 4) (d1 *> r) (d1 *> r')
  | BRIncs_odd_chain0 (r_ch : nat) {m : nat} {r r' : side} :
      BRIncs true (1 + m * 2 ^ (1 + r_ch)) r r' ->
      BRIncs false (3 + m * 4) (zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR r_ch WV) r')
  | BRIncs_odd_chain1 (r_ch : nat) {m : nat} {r r' : side} :
      BRIncs true (1 + m * 2 ^ (1 + r_ch)) r r' ->
      BRIncs false (5 + m * 4) (zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR r_ch WV) r')
  | BRIncs_even_chain (r_ch : nat) {m : nat} {r r' : side} :
      BRIncs true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) r r' ->
      BRIncs false (6 + m * 2) (d0 *> zTs (zQK r_ch [WV]) r) (zTs (zR (1 + r_ch) WV) r')
  | BRIncs_shift_pair0 {n : nat} {r r' : side} :
      BRIncs false (n * 2) r r' -> BRIncs true (1 + n) (d0 *> r) (t *> r')
  | BRIncs_shift_pair1 {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs true (1 + n) (d1 *> r) (t *> r')
  | BRIncs_shift_chain0 (r_ch : nat) {m : nat} {r r' : side} :
      BRIncs true (1 + m * 2 ^ (2 + r_ch)) r r' ->
      BRIncs true (3 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR (1 + r_ch) WV) r')
  | BRIncs_shift_chain1 (r_ch : nat) {m : nat} {r r' : side} :
      BRIncs true (1 + m * 2 ^ (2 + r_ch)) r r' ->
      BRIncs true (5 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR (1 + r_ch) WV) r').

Inductive Num : bool -> nat -> list sym -> list Call -> Prop :=
  | Num_zero : Num false 0 one []
  | Num_odd (n : nat) : Num false (1 + n * 2) [] ([cp] ++ [ch] ^^ n)
  | Num_even (n : nat) : Num false (2 + n * 2) [] ([cj] ++ [ch] ^^ n)
  | Num_shift (n : nat) : Num true (1 + n * 2) d0 ([ch; cp] ++ [ch] ^^ n).

Definition z2f (s : bool) (k : nat) (r r' : side) : Prop :=
  forall w hs, Num s k w hs -> Side hs (w *> r) r'.

Lemma z2g {r r' : side} (h : z2f false 0 r r') :
  r' = one *> r.
Proof.
  pose proof (h one [] Num_zero) as h0.
  inversion h0; reflexivity.
Qed.

Lemma z2h {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f false (2 + n) (t *> r) (t *> r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (2 + n) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate; try lia.
  - destruct m as [| m]; [lia |].
    change (S m) with (1 + m) in *.
    apply (zSc (z0m m)).
    assert (hm : 1 + n * 2 = 1 + (1 + m * 2) * 2) by lia.
    pose proof (Num_odd (1 + m * 2)) as hN1.
    rewrite <- hm in hN1.
    exact (hI [] _ hN1).
  - apply (zSc (z0n m)).
    assert (hm : 1 + n * 2 = 1 + (m * 2) * 2) by lia.
    pose proof (Num_odd (m * 2)) as hN1.
    rewrite <- hm in hN1.
    exact (hI [] _ hN1).
Qed.

Lemma z2i_p0 {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f false (1 + n) (d1 *> (d0 *> r)) (t *> r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (1 + n) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate; try lia.
  - cbn [Str_app]; change (d1 *> (d0 *> r)) with ((d1 ++ d0) *> r).
    destruct m as [| m].
    + assert (hn0 : (n * 2 = 0)%nat) by lia.
      rewrite hn0 in hI.
      rewrite (z2g hI).
      change (t *> (one *> r)) with ((t ++ one) *> r).
      exact (zSc z0e (Side_nil r)).
    + change (S m) with (1 + m) in *.
      apply (zSc (z0o m)).
      assert (hm : n * 2 = 2 + (1 + m * 2) * 2) by lia.
      pose proof (Num_even (1 + m * 2)) as hN2.
      rewrite <- hm in hN2.
      exact (hI [] _ hN2).
  - cbn [Str_app]; change (d1 *> (d0 *> r)) with ((d1 ++ d0) *> r).
    apply (zSc (z0p m)).
    assert (hm : n * 2 = 2 + (m * 2) * 2) by lia.
    pose proof (Num_even (m * 2)) as hN2.
    rewrite <- hm in hN2.
    exact (hI [] _ hN2).
Qed.

Lemma z2j {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f false (1 + n) (d1 *> (d1 *> r)) (t *> r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (1 + n) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate; try lia.
  - cbn [Str_app]; change (d1 *> (d1 *> r)) with ((d1 ++ d1) *> r).
    apply (zSc (z0q m)).
    assert (hm : 1 + n * 2 = 1 + (m * 2) * 2) by lia.
    pose proof (Num_odd (m * 2)) as hN1.
    rewrite <- hm in hN1.
    exact (hI [] _ hN1).
  - cbn [Str_app]; change (d1 *> (d1 *> r)) with ((d1 ++ d1) *> r).
    apply (zSc (z0r m)).
    assert (hm : 1 + n * 2 = 1 + (1 + m * 2) * 2) by lia.
    pose proof (Num_odd (1 + m * 2)) as hN1.
    rewrite <- hm in hN1.
    exact (hI [] _ hN1).
Qed.

Lemma z2k {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f false (2 + n * 4) (d0 *> r) (d0 *> r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (2 + n * 4) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate; try lia.
  assert (hm : m = n * 2) by lia; subst m.
  destruct n as [| n].
  - rewrite (z2g hI).
    change (d0 *> (one *> r)) with ((d0 ++ one) *> r).
    exact (zSc z0i (Side_nil r)).
  - replace (S n * 2) with (2 + n * 2) by lia.
    apply (zSc (z0s n)).
    assert (heq : S n * 2 = 2 + n * 2) by lia.
    pose proof (Num_even n) as hN2.
    rewrite <- heq in hN2.
    exact (hI [] _ hN2).
Qed.

Lemma z2l {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f false (2 + n * 4) (d1 *> r) (d0 *> r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (2 + n * 4) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate; try lia.
  assert (hm : m = n * 2) by lia; subst m.
  apply (zSc (z0t n)).
  exact (hI [] _ (Num_odd n)).
Qed.

Lemma z2m {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f false (4 + n * 4) (d0 *> r) (d1 *> r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (4 + n * 4) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate; try lia.
  assert (hm : m = 1 + n * 2) by lia; subst m.
  destruct n as [| n].
  - rewrite (z2g hI).
    change (d1 *> (one *> r)) with ((d1 ++ one) *> r).
    exact (zSc z0u (Side_nil r)).
  - replace (1 + S n * 2) with (3 + n * 2) by lia.
    apply (zSc (z0v n)).
    assert (heq : S n * 2 = 2 + n * 2) by lia.
    pose proof (Num_even n) as hN2.
    rewrite <- heq in hN2.
    exact (hI [] _ hN2).
Qed.

Lemma z2n {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f false (4 + n * 4) (d1 *> r) (d1 *> r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (4 + n * 4) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate; try lia.
  assert (hm : m = 1 + n * 2) by lia; subst m.
  apply (zSc (z0w n)).
  exact (hI [] _ (Num_odd n)).
Qed.

Lemma zP2 (n : nat) : 2 ^ (1 + n) = 2 ^ n + 2 ^ n.
Proof. cbn [Nat.add Nat.pow]; lia. Qed.

Lemma z2_oc0 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
    z2f false (3 + m * 4) (zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR r_ch WV) r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (3 + m * 4) as k eqn:Hk.
  destruct hN as [| n | n | n]; try discriminate; try lia.
  assert (hn : n = 1 + m * 2) by lia; subst n.
  cbn [Str_app]; rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 (t ^^ r_ch) r').
  assert (h_seg : Seg ([cp] ++ [ch] ^^ (1 + m * 2)) ([ch; cp] ++ [ch] ^^ (m * 2 ^ r_ch))
      ((d1 ++ d0) ^^ r_ch ++ [1; 1]) (d0 ++ t ^^ r_ch)).
  { change ([cp] ++ [ch] ^^ (1 + m * 2)) with ([cp; ch] ++ [ch] ^^ (m * 2)).
    exact (zSg (zOdd_base r_ch) (zS0 (zH_d0_even m) (zT_pow r_ch m))). }
  apply (zSc h_seg).
  assert (heq : 1 + m * 2 ^ (1 + r_ch) = 1 + (m * 2 ^ r_ch) * 2) by (rewrite zP2; lia).
  pose proof (Num_shift (m * 2 ^ r_ch)) as h_num.
  rewrite <- heq in h_num.
  exact (hI d0 _ h_num).
Qed.

Lemma z2_oc1 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
    z2f false (5 + m * 4) (zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR r_ch WV) r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (5 + m * 4) as k eqn:Hk.
  destruct hN as [| n | n | n]; try discriminate; try lia.
  assert (hn : n = 1 + (1 + m * 2)) by lia; subst n.
  cbn [Str_app]; rewrite zTs_QK, zTs_R, <- (Str_app_assoc d1 (t ^^ r_ch) r').
  assert (h_seg : Seg ([cp] ++ [ch] ^^ (1 + (1 + m * 2))) ([ch; cp] ++ [ch] ^^ (m * 2 ^ r_ch))
      ((d1 ++ d0) ^^ r_ch ++ [1; 1]) (d1 ++ t ^^ r_ch)).
  { change ([cp] ++ [ch] ^^ (1 + (1 + m * 2))) with ([cp; ch] ++ [ch] ^^ (1 + m * 2)).
    exact (zSg (zOdd_base r_ch) (zS0 (zH_d0_odd m) (zT_pow r_ch m))). }
  apply (zSc h_seg).
  assert (heq : 1 + m * 2 ^ (1 + r_ch) = 1 + (m * 2 ^ r_ch) * 2) by (rewrite zP2; lia).
  pose proof (Num_shift (m * 2 ^ r_ch)) as h_num.
  rewrite <- heq in h_num.
  exact (hI d0 _ h_num).
Qed.

Lemma z2_ec (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) r r') :
    z2f false (6 + m * 2) (d0 *> zTs (zQK r_ch [WV]) r) (zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN.
  remember false as s0 eqn:Hs0; remember (6 + m * 2) as k eqn:Hk.
  destruct hN as [| n | n | n]; try discriminate; try lia.
  assert (hn : n = 1 + (1 + m)) by lia; subst n.
  cbn [Str_app]; rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 ((d1 ++ d0) ^^ r_ch ++ [1; 1]) (d0 *> r)).
  assert (h_seg : Seg ([cj] ++ [ch] ^^ (1 + (1 + m))) ([ch; cp] ++ [ch] ^^ ((1 + m * 2) * 2 ^ r_ch))
      (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1])) (t ^^ (1 + r_ch))).
  { pose proof (zSg (zEven_base r_ch) (zT_pow (1 + r_ch) m)) as h3.
    change ([cj; ch; ch] ++ [ch] ^^ m) with ([cj] ++ [ch] ^^ (1 + (1 + m))) in h3.
    rewrite <- app_assoc, <- z07 in h3.
    replace (2 ^ r_ch + m * 2 ^ (1 + r_ch)) with ((1 + m * 2) * 2 ^ r_ch) in h3
      by (rewrite zP2; lia).
    exact h3. }
  apply (zSc h_seg).
  assert (heq : 1 + (1 + m * 2) * 2 ^ (1 + r_ch) = 1 + ((1 + m * 2) * 2 ^ r_ch) * 2)
    by (rewrite zP2; lia).
  pose proof (Num_shift ((1 + m * 2) * 2 ^ r_ch)) as h_num.
  rewrite <- heq in h_num.
  exact (hI d0 _ h_num).
Qed.

Lemma z2_sp0 {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f true (1 + n) (d0 *> r) (t *> r').
Proof.
  intros w hs hN.
  remember true as s0 eqn:Hs0; remember (1 + n) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate.
  assert (hn : n = m * 2) by lia; subst n.
  rewrite <- Str_app_assoc.
  destruct m as [| m].
  - cbn [Nat.mul] in hI.
    rewrite (z2g hI), <- Str_app_assoc.
    assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ 0%nat) [] (d0 ++ d0) (t ++ one)).
    { cbn [lpow app]; exact (zSg (zS0 zH0 (z0a d0)) z0e). }
    exact (zSc h_seg (Side_nil r)).
  - change (S m) with (1 + m) in *.
    assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ (1 + m)) ([cj] ++ [ch] ^^ (1 + m * 2)) (d0 ++ d0) t).
    { change ([ch; cp] ++ [ch] ^^ (1 + m)) with ([ch] ++ ([cp] ++ [ch] ^^ (1 + m))).
      exact (zSg (zS0 zH0 (z0a d0)) (z0o m)). }
    apply (zSc h_seg).
    assert (hm : (1 + m) * 2 * 2 = 2 + (1 + m * 2) * 2) by lia.
    pose proof (Num_even (1 + m * 2)) as hN2.
    rewrite <- hm in hN2.
    exact (hI [] _ hN2).
Qed.

Lemma z2_sp1 {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f true (1 + n) (d1 *> r) (t *> r').
Proof.
  intros w hs hN.
  remember true as s0 eqn:Hs0; remember (1 + n) as k eqn:Hk.
  destruct hN as [| m | m | m]; try discriminate.
  assert (hn : n = m * 2) by lia; subst n.
  rewrite <- Str_app_assoc.
  assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ m) ([cp] ++ [ch] ^^ (m * 2)) (d0 ++ d1) t).
  { change ([ch; cp] ++ [ch] ^^ m) with ([ch] ++ ([cp] ++ [ch] ^^ m)).
    exact (zSg (zS0 zH0 (z0a d1)) (z0q m)). }
  apply (zSc h_seg).
  exact (hI [] _ (Num_odd (m * 2))).
Qed.

Lemma z2_sc0 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
    z2f true (3 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN.
  remember true as s0 eqn:Hs0; remember (3 + m * 4) as k eqn:Hk.
  destruct hN as [| n | n | n]; try discriminate; try lia.
  assert (hn : n = 1 + m * 2) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 (t ^^ (1 + r_ch)) r').
  assert (h_in : d0 *> (d0 *> (((d1 ++ d0) ^^ r_ch ++ [1; 1]) *> (d0 *> r))) =
      (d0 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))) *> (d0 *> r))
    by (rewrite !Str_app_assoc; reflexivity).
  rewrite h_in.
  assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ (1 + m * 2)) ([ch; cp] ++ [ch] ^^ (m * 2 ^ (1 + r_ch)))
      (d0 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))) (d0 ++ t ^^ (1 + r_ch))).
  { assert (h0 : Seg [ch] [] (d0 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))) ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1])).
    { change ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1]) with (d1 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))).
      exact (zS0 zH0 (z0a (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1])))). }
    pose proof (zSg h0 (zSg (zOdd_base (1 + r_ch)) (zS0 (zH_d0_even m) (zT_pow (1 + r_ch) m)))) as h_all.
    change ([ch] ++ ([cp; ch] ++ [ch] ^^ (m * 2))) with ([ch; cp] ++ [ch] ^^ (1 + m * 2)) in h_all.
    exact h_all. }
  apply (zSc h_seg).
  assert (heq : 1 + m * 2 ^ (2 + r_ch) = 1 + (m * 2 ^ (1 + r_ch)) * 2).
  { change (2 + r_ch) with (1 + (1 + r_ch)). rewrite zP2; lia. }
  pose proof (Num_shift (m * 2 ^ (1 + r_ch))) as h_num.
  rewrite <- heq in h_num.
  exact (hI d0 _ h_num).
Qed.

Lemma z2_sc1 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
    z2f true (5 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN.
  remember true as s0 eqn:Hs0; remember (5 + m * 4) as k eqn:Hk.
  destruct hN as [| n | n | n]; try discriminate; try lia.
  assert (hn : n = 1 + (1 + m * 2)) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d1 (t ^^ (1 + r_ch)) r').
  assert (h_in : d0 *> (d0 *> (((d1 ++ d0) ^^ r_ch ++ [1; 1]) *> (d0 *> r))) =
      (d0 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))) *> (d0 *> r))
    by (rewrite !Str_app_assoc; reflexivity).
  rewrite h_in.
  assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ (1 + (1 + m * 2))) ([ch; cp] ++ [ch] ^^ (m * 2 ^ (1 + r_ch)))
      (d0 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))) (d1 ++ t ^^ (1 + r_ch))).
  { assert (h0 : Seg [ch] [] (d0 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))) ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1])).
    { change ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1]) with (d1 ++ (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1]))).
      exact (zS0 zH0 (z0a (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1])))). }
    pose proof (zSg h0 (zSg (zOdd_base (1 + r_ch)) (zS0 (zH_d0_odd m) (zT_pow (1 + r_ch) m)))) as h_all.
    change ([ch] ++ ([cp; ch] ++ [ch] ^^ (1 + m * 2))) with ([ch; cp] ++ [ch] ^^ (1 + (1 + m * 2))) in h_all.
    exact h_all. }
  apply (zSc h_seg).
  assert (heq : 1 + m * 2 ^ (2 + r_ch) = 1 + (m * 2 ^ (1 + r_ch)) * 2).
  { change (2 + r_ch) with (1 + (1 + r_ch)). rewrite zP2; lia. }
  pose proof (Num_shift (m * 2 ^ (1 + r_ch))) as h_num.
  rewrite <- heq in h_num.
  exact (hI d0 _ h_num).
Qed.

Lemma z2o {s : bool} {k : nat} {r r' : side} (hI : BRIncs s k r r') :
  z2f s k r r'.
Proof.
  induction hI as [r
    | n r r' _ IH | n r r' _ IH | n r r' _ IH
    | n r r' _ IH | n r r' _ IH | n r r' _ IH | n r r' _ IH
    | r_ch m r r' _ IH | r_ch m r r' _ IH | r_ch m r r' _ IH
    | n r r' _ IH | n r r' _ IH | r_ch m r r' _ IH | r_ch m r r' _ IH].
  - intros w hs hN.
    remember false as s0 eqn:Hs0; remember 0%nat as k0 eqn:Hk0.
    destruct hN; try discriminate; try lia.
    exact (Side_nil (one *> r)).
  - exact (z2h IH).
  - exact (z2i_p0 IH).
  - exact (z2j IH).
  - exact (z2k IH).
  - exact (z2l IH).
  - exact (z2m IH).
  - exact (z2n IH).
  - exact (z2_oc0 r_ch IH).
  - exact (z2_oc1 r_ch IH).
  - exact (z2_ec r_ch IH).
  - exact (z2_sp0 IH).
  - exact (z2_sp1 IH).
  - exact (z2_sc0 r_ch IH).
  - exact (z2_sc1 r_ch IH).
Qed.

Lemma z2p {r r' : side} (hI : BRIncs false 128 r r') :
  zCf r -[ canon_tm ]->+ zCf (zTs [WV; WV; WQ; WV] r').
Proof.
  pose proof (z2o hI [] ([cj] ++ [ch] ^^ 63) (Num_even 63)) as hC.
  cbn [Str_app] in hC.
  pose proof (zW_full hC) as hW.
  assert (heq : (t ++ t ++ d1 ++ t) *> r' = zTs [WV; WV; WQ; WV] r') by reflexivity.
  rewrite <- heq; exact hW.
Qed.

(* ---------- Section 7A: Binary, Digits (zDg), Weights (z0Y..z11, z0W), z0L, zHn ---------- *)

Local Open Scope nat_scope.

Inductive Binary : nat -> nat -> side -> Prop :=
  | Binary_one : Binary 1 1 (d1 *> 0inf)
  | Binary_zero {n H : nat} {r : side} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 *> r)
  | Binary_two {n H : nat} {r : side} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 *> r).

Lemma zPp (n : nat) : 0 < 2 ^ n.
Proof.
  induction n as [| n IH]; cbn; lia.
Qed.

Lemma z0F (n : nat) : (exists a, n = a * 2) \/ (exists a, n = 1 + a * 2).
Proof.
  destruct (Nat.Even_or_Odd n) as [[a Ha] | [a Ha]].
  - left; exists a; lia.
  - right; exists a; lia.
Qed.

Lemma z0H {A H : nat} {r : side} (h : Binary A H r) :
  BRIncs false ((A - 1) * 2) 0inf r.
Proof.
  induction h as [| n H r _ IH | n H r _ IH].
  - cbn [Nat.sub Nat.mul].
    assert (hd : d1 *> 0inf = one *> 0inf) by solve_const0_eq.
    rewrite hd; exact (BRIncs_zero 0inf).
  - replace (1 + n - 1) with n in IH by lia.
    pose proof (BRIncs_short00 IH) as hs.
    rewrite zDd in hs.
    replace ((2 + n * 2 - 1) * 2) with (2 + n * 4) by lia.
    exact hs.
  - replace (1 + n - 1) with n in IH by lia.
    pose proof (BRIncs_short10 IH) as hs.
    rewrite zDd in hs.
    replace ((3 + n * 2 - 1) * 2) with (4 + n * 4) by lia.
    exact hs.
Qed.

Inductive zPr : bool -> zW -> Prop :=
  | zPr_nil (e : bool) : zPr e []
  | zPr_T (e : bool) {u : zW} : zPr true u -> zPr e (WV :: u)
  | zPr_short0 {u : zW} : zPr true u -> zPr true (WK :: u)
  | zPr_short1 {u : zW} : zPr false u -> zPr true (WQ :: u)
  | zPr_pair0 (e : bool) {u : zW} : zPr true u -> zPr e (WQ :: WK :: u)
  | zPr_pair1 (e : bool) {u : zW} : zPr false u -> zPr e (WQ :: WQ :: u).

Lemma z0I {u : zW} (h : zPr false u) : zPr true u.
Proof.
  inverts h; constructor; assumption.
Qed.

Lemma z0J (u : zW) : zPr true u /\ (zPr false u \/ zPr false (WQ :: u)).
Proof.
  induction u as [| w u [hI hJ]].
  - split; [exact (zPr_nil true) | left; exact (zPr_nil false)].
  - destruct w.
    + split; [exact (zPr_T true hI) | left; exact (zPr_T false hI)].
    + split; [exact (zPr_short0 hI) | right; exact (zPr_pair0 false hI)].
    + destruct hJ as [hJ | hJ].
      * split; [exact (zPr_short1 hJ) | right; exact (zPr_pair1 false hJ)].
      * split; [exact (z0I hJ) | left; exact hJ].
Qed.

Inductive zDg : nat -> nat -> zW -> Prop :=
  | zDg_nil : zDg 0 0 []
  | zDg_zero {A H : nat} {u : zW} : zDg A H u -> zDg (A * 2) (1 + H) (WK :: u)
  | zDg_one {A H : nat} {u : zW} : zDg A H u -> zDg (1 + A * 2) (1 + H) (WQ :: u).

Lemma z0K {A H : nat} {u : zW} (h : zDg A H (WV :: u)) : False.
Proof. inverts h. Qed.

Lemma zD0 {A H : nat} {u : zW} (h : zDg A H (WK :: u)) :
  exists A' H', zDg A' H' u /\ A = A' * 2 /\ H = 1 + H'.
Proof.
  inverts h as hD; exists A0, H0; repeat split; assumption || reflexivity.
Qed.

Lemma zD1 {A H : nat} {u : zW} (h : zDg A H (WQ :: u)) :
  exists A' H', zDg A' H' u /\ A = 1 + A' * 2 /\ H = 1 + H'.
Proof.
  inverts h as hD; exists A0, H0; repeat split; assumption || reflexivity.
Qed.

Lemma z0T (H : nat) : forall A, A < 2 ^ H -> exists u, zDg A H u.
Proof.
  induction H as [| H IH]; intros A HA.
  - cbn in HA. assert (A = 0) by lia. subst. exists (@nil Word); constructor.
  - change (S H) with (1 + H) in *.
    rewrite zP2 in HA.
    destruct (z0F A) as [[a ->] | [a ->]].
    + destruct (IH a ltac:(lia)) as [u Hu].
      exists (WK :: u); exact (zDg_zero Hu).
    + destruct (IH a ltac:(lia)) as [u Hu].
      exists (WQ :: u); exact (zDg_one Hu).
Qed.

Lemma z0U {A H : nat} {u : zW} (h1 : zDg A H u) :
  forall {B J : nat} {v : zW}, zDg B J v -> zDg (A + B * 2 ^ H) (H + J) (u ++ v).
Proof.
  induction h1 as [| A H u h1 IH | A H u h1 IH]; intros B0 J v h2.
  - cbn [Nat.add Nat.pow app].
    replace (B0 * 1) with B0 by lia. exact h2.
  - pose proof (zDg_zero (IH _ _ _ h2)) as h3.
    replace ((A + B0 * 2 ^ H) * 2) with (A * 2 + B0 * 2 ^ (1 + H)) in h3
      by (rewrite zP2; lia).
    exact h3.
  - pose proof (zDg_one (IH _ _ _ h2)) as h3.
    replace (1 + (A + B0 * 2 ^ H) * 2) with ((1 + A * 2) + B0 * 2 ^ (1 + H)) in h3
      by (rewrite zP2; lia).
    exact h3.
Qed.

Lemma z0W_lt {A H : nat} {u : zW} (h : zDg A H u) : A < 2 ^ H.
Proof.
  induction h; [cbn; lia | rewrite zP2; lia | rewrite zP2; lia].
Qed.

Lemma z0X_gen {A1 H1 : nat} {u : zW} (h1 : zDg A1 H1 u) :
  forall {A2 H2 : nat} {v : zW}, zDg A2 H2 v -> A1 = A2 -> H1 = H2 -> u = v.
Proof.
  induction h1 as [| A1 H1 u h1 IH | A1 H1 u h1 IH]; intros A2 H2 v h2 HA HH.
  - inverts h2; [reflexivity | lia | lia].
  - inverts h2 as hD; [lia | f_equal; eapply IH; [exact hD | lia | lia] | lia].
  - inverts h2 as hD; [lia | lia | f_equal; eapply IH; [exact hD | lia | lia]].
Qed.

Lemma z0X {A H : nat} {u v : zW} (h1 : zDg A H u) (h2 : zDg A H v) : u = v.
Proof. exact (z0X_gen h1 h2 eq_refl eq_refl). Qed.

Fixpoint z0L (u : zW) : bool :=
  match u with
  | [] => false
  | WQ :: v =>
    match v with
    | WK :: _ => true
    | WQ :: _ => true
    | _ => z0L v
    end
  | _ :: v => z0L v
  end.

Lemma z1I (u v : zW) (h : z0L v = true) : z0L (u ++ v) = true.
Proof.
  induction u as [| w u IH]; [exact h |].
  destruct w; cbn [app z0L]; try exact IH.
  destruct u as [| w2 u'].
  - cbn [app]; destruct v as [| w2 v']; [discriminate h |].
    destruct w2; cbn [z0L] in h |- *; exact h || reflexivity.
  - cbn [app]; destruct w2; [exact IH | reflexivity | reflexivity].
Qed.

Lemma zDg_pos_z0L {A H : nat} {w : zW} (hD : zDg A H w) (hPos : (0 < A)%nat) :
  z0L (w ++ [WK]) = true.
Proof.
  induction hD as [| A1 H1 u1 hDu IH | A1 H1 u1 hDu _].
  - lia.
  - cbn [app z0L]; exact (IH ltac:(lia)).
  - destruct hDu; reflexivity.
Qed.

(* ---------- Rationals (Rat := QArith_base.Q) ---------- *)

Notation Rat := QArith_base.Q.
Definition Q_of_nat (n : nat) : Rat := inject_Z (Z.of_nat n).

Lemma Q_of_nat_0 : (Q_of_nat 0 == 0)%Q. Proof. reflexivity. Qed.
Lemma Q_of_nat_1 : (Q_of_nat 1 == 1)%Q. Proof. reflexivity. Qed.
Lemma Q_of_nat_2 : (Q_of_nat 2 == 2)%Q. Proof. reflexivity. Qed.
Lemma Q_of_nat_3 : (Q_of_nat 3 == 3)%Q. Proof. reflexivity. Qed.
Lemma Q_of_nat_4 : (Q_of_nat 4 == 4)%Q. Proof. reflexivity. Qed.
Lemma Q_of_nat_5 : (Q_of_nat 5 == 5)%Q. Proof. reflexivity. Qed.
Lemma Q_of_nat_6 : (Q_of_nat 6 == 6)%Q. Proof. reflexivity. Qed.
Lemma Q_of_nat_8 : (Q_of_nat 8 == 8)%Q. Proof. reflexivity. Qed.

Lemma Q_of_nat_add (a b : nat) : (Q_of_nat (a + b) == Q_of_nat a + Q_of_nat b)%Q.
Proof. unfold Q_of_nat; rewrite Nat2Z.inj_add, inject_Z_plus; reflexivity. Qed.

Lemma Q_of_nat_mul (a b : nat) : (Q_of_nat (a * b) == Q_of_nat a * Q_of_nat b)%Q.
Proof. unfold Q_of_nat; rewrite Nat2Z.inj_mul, inject_Z_mult; reflexivity. Qed.

Lemma Q_of_nat_S (a : nat) : (Q_of_nat (S a) == Q_of_nat a + 1)%Q.
Proof. replace (S a) with (a + 1)%nat by lia; rewrite Q_of_nat_add, Q_of_nat_1; reflexivity. Qed.

Lemma Q_of_nat_pow2 (n : nat) : (Q_of_nat (2 ^ (1 + n)) == Q_of_nat (2 ^ n) * 2)%Q.
Proof. rewrite zP2, Q_of_nat_add; lra. Qed.

Lemma Q_of_nat_pow2_S (n : nat) : (Q_of_nat (2 ^ S n) == Q_of_nat (2 ^ n) * 2)%Q.
Proof. change (S n) with (1 + n)%nat; apply Q_of_nat_pow2. Qed.

Ltac push_Q_of_nat :=
  repeat (rewrite Q_of_nat_add in * || rewrite Q_of_nat_mul in * || rewrite Q_of_nat_S in *);
  repeat (rewrite Q_of_nat_0 in * || rewrite Q_of_nat_1 in * || rewrite Q_of_nat_2 in * ||
          rewrite Q_of_nat_3 in * || rewrite Q_of_nat_4 in * || rewrite Q_of_nat_5 in * ||
          rewrite Q_of_nat_6 in * || rewrite Q_of_nat_8 in *).

Lemma Q_of_nat_le (a b : nat) : (a <= b)%nat <-> (Q_of_nat a <= Q_of_nat b)%Q.
Proof. unfold Q_of_nat, Qle; cbn; lia. Qed.

Lemma Q_of_nat_lt (a b : nat) : (a < b)%nat <-> (Q_of_nat a < Q_of_nat b)%Q.
Proof. unfold Q_of_nat, Qlt; cbn; lia. Qed.

Lemma Q_of_nat_eq (a b : nat) : (a = b)%nat <-> (Q_of_nat a == Q_of_nat b)%Q.
Proof. unfold Q_of_nat, Qeq; cbn; lia. Qed.

Lemma Q_of_nat_nonneg (a : nat) : (0 <= Q_of_nat a)%Q.
Proof. unfold Q_of_nat, Qle; cbn; lia. Qed.

Local Open Scope Q_scope.

Fixpoint z0Y (u : zW) : Rat :=
  match u with
  | [] => 0
  | WV :: v => z0Y v * (1#2)
  | _ :: v => 1 + z0Y v * 2
  end.

Fixpoint z0W (u : zW) : Rat :=
  match u with
  | [] => 0
  | WV :: v => z0W v * (1#2)
  | WK :: v => (11#8) + z0W v * 2
  | WQ :: v => 1 + z0W v * 2
  end.

Fixpoint z0Z (u : zW) : Rat :=
  match u with
  | [] => 0
  | WV :: v => z0Z v * (1#2)
  | WK :: v => 1 + z0Z v * 2
  | WQ :: v => z0Z v * 2
  end.

Fixpoint z10 (u : zW) : Rat :=
  match u with
  | [] => 0
  | WV :: v => z10 v * (1#2)
  | WK :: v => z10 v * 2
  | WQ :: v => 1 + z10 v * 2
  end.

Fixpoint z11 (u : zW) : Rat :=
  match u with
  | [] => 1
  | WV :: v => z11 v * (1#2)
  | _ :: v => z11 v * 2
  end.

Lemma zWn (u : zW) : 0 <= z0Y u /\ 0 <= z0Z u /\ 0 <= z10 u /\ 0 <= z0W u.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [z0Y z0Z z10 z0W]; lra.
Qed.

Lemma zWY (u : zW) : z0Y u <= z0W u /\ z0W u <= (11#8) * z0Y u.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [z0Y z0W]; lra.
Qed.

Lemma z12 (u : zW) : z0Y u == z0Z u + z10 u.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [z0Y z0Z z10]; lra.
Qed.

Lemma zSp (u : zW) : 0 < z11 u.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [z11]; lra.
Qed.

Lemma z13 (u v : zW) : z0Y (u ++ v) == z0Y u + z11 u * z0Y v.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [app z0Y z11]; rewrite IH; ring.
Qed.

Lemma z13W (u v : zW) : z0W (u ++ v) == z0W u + z11 u * z0W v.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [app z0W z11]; rewrite IH; ring.
Qed.

Lemma z14 (u v : zW) : z0Z (u ++ v) == z0Z u + z11 u * z0Z v.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [app z0Z z11]; rewrite IH; ring.
Qed.

Lemma z15 (u v : zW) : z10 (u ++ v) == z10 u + z11 u * z10 v.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [app z10 z11]; rewrite IH; ring.
Qed.

Lemma z16 (u v : zW) : z11 (u ++ v) == z11 u * z11 v.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [app z11]; rewrite IH; ring.
Qed.

Lemma zDw {A H : nat} {u : zW} (h : zDg A H u) :
  z11 u == Q_of_nat (2 ^ H) /\ z0Y u + 1 == Q_of_nat (2 ^ H) /\ z10 u == Q_of_nat A.
Proof.
  induction h as [| A H u h IH | A H u h IH].
  - cbn; repeat split; lra.
  - rewrite zP2, Q_of_nat_add, Q_of_nat_mul; cbn [z11 z0Y z10].
    rewrite Q_of_nat_2; lra.
  - rewrite zP2, !Q_of_nat_add, Q_of_nat_mul; cbn [z11 z0Y z10].
    rewrite Q_of_nat_1, Q_of_nat_2; lra.
Qed.

Lemma z17 {A H : nat} {u : zW} (h : zDg A H u) :
  z0Z u + Q_of_nat A + 1 == Q_of_nat (2 ^ H).
Proof.
  pose proof (zDw h) as Hd.
  pose proof (z12 u) as Hm.
  lra.
Qed.

Fixpoint zHn (u : zW) (h : nat) : option nat :=
  match u with
  | [] => Some h
  | WV :: u' => zHn u' (h + 1)%nat
  | _ :: u' =>
    match h with
    | 0%nat => None
    | S h' => zHn u' h'
    end
  end.

Lemma z1x (u : zW) :
  forall (h H : nat), zHn u h = Some H ->
    z11 u * Q_of_nat (2 ^ H) == Q_of_nat (2 ^ h).
Proof.
  induction u as [| w u IH]; intros h H hE.
  - inversion hE; subst; cbn [z11]; lra.
  - destruct w.
    + cbn [zHn z11] in *.
      pose proof (IH (h + 1)%nat H hE) as hIH.
      replace (h + 1)%nat with (1 + h)%nat in hIH by lia.
      rewrite Q_of_nat_pow2 in hIH; lra.
    + destruct h as [| h]; [discriminate hE |].
      cbn [zHn z11] in *.
      pose proof (IH h H hE) as hIH.
      rewrite Q_of_nat_pow2_S; lra.
    + destruct h as [| h]; [discriminate hE |].
      cbn [zHn z11] in *.
      pose proof (IH h H hE) as hIH.
      rewrite Q_of_nat_pow2_S; lra.
Qed.

Lemma z1B (u : zW) :
  forall (h : nat), z0Y u < Q_of_nat (2 ^ h) -> exists H, zHn u h = Some H.
Proof.
  induction u as [| w u IH]; intros h hM.
  - exists h; reflexivity.
  - destruct w.
    + cbn [z0Y zHn] in *.
      apply (IH (h + 1)%nat).
      replace (h + 1)%nat with (1 + h)%nat by lia.
      rewrite Q_of_nat_pow2; lra.
    + destruct h as [| h].
      * pose proof (proj1 (zWn u)); cbn [z0Y Nat.pow] in *; rewrite Q_of_nat_1 in hM; lra.
      * cbn [z0Y zHn] in *.
        apply (IH h).
        rewrite Q_of_nat_pow2_S in hM; lra.
    + destruct h as [| h].
      * pose proof (proj1 (zWn u)); cbn [z0Y Nat.pow] in *; rewrite Q_of_nat_1 in hM; lra.
      * cbn [z0Y zHn] in *.
        apply (IH h).
        rewrite Q_of_nat_pow2_S in hM; lra.
Qed.

Lemma z1K {n H : nat} {ds : zW} (hD : zDg (1 + n * 4)%nat H ds) (hH : (2 <= H)%nat) :
  exists w, ds = WQ :: WK :: w.
Proof.
  remember (1 + n * 4)%nat as A eqn:HA.
  inverts hD as hD1; [lia | lia |].
  assert (HA1 : A0 = (n * 2)%nat) by lia; subst A0.
  remember (n * 2)%nat as A1 eqn:HA1.
  inverts hD1 as hD2; [lia | eexists; reflexivity | lia].
Qed.

(* ---------- Section 7B: Scan on digit words ---------- *)

Inductive Scan : nat -> zW -> nat -> zW -> Rat -> Prop :=
  | Scan_nil (k : nat) : Scan k [] k [] 0
  | Scan_T {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan ((1 + n) * 2)%nat u k v l ->
      Scan (1 + n)%nat (WV :: u) k (WV :: v) (l * (1#2))
  | Scan_pair0 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (n * 2)%nat u k v l ->
      Scan (1 + n)%nat (WQ :: WK :: u) k (WV :: v) ((1 + l) * (1#2))
  | Scan_pair1 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2)%nat u k v l ->
      Scan (1 + n)%nat (WQ :: WQ :: u) k (WV :: v) ((1#4) + l * (1#2))
  | Scan_short00 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (n * 2)%nat u k v l ->
      Scan (2 + n * 4)%nat (WK :: u) k (WK :: v) (1 + l * 2)
  | Scan_short01 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2)%nat u k v l ->
      Scan (2 + n * 4)%nat (WQ :: u) k (WK :: v) (l * 2)
  | Scan_short10 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (n * 2)%nat u k v l ->
      Scan (4 + n * 4)%nat (WK :: u) k (WQ :: v) (1 + l * 2)
  | Scan_short11 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2)%nat u k v l ->
      Scan (4 + n * 4)%nat (WQ :: u) k (WQ :: v) (l * 2).

Lemma z19 {e : bool} {u : zW} (hI : zPr e u) :
  forall (k : nat), (e = true -> exists n : nat, k = (n * 2)%nat) ->
    (z0Y u + z0Z u) * 2 < Q_of_nat k ->
    exists b v l, Scan k u b v l /\ (0 < b)%nat.
Proof.
  induction hI as [e | e u hI IH | u hI IH | u hI IH | e u hI IH | e u hI IH];
    intros k hEk hk.
  - cbn [z0Y z0Z] in hk.
    assert (hk_pos : 0 < Q_of_nat k) by lra.
    apply (proj2 (Q_of_nat_lt 0 k)) in hk_pos.
    exists k, (@nil Word), 0; split; [constructor | exact hk_pos].
  - pose proof (zWn u) as hw. cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [rewrite Q_of_nat_0 in hk; lra |].
    change (S k) with (1 + k)%nat in *.
    destruct (IH ((1 + k) * 2)%nat (fun _ => ex_intro _ (1 + k)%nat eq_refl))
      as [b [v [l [hS hB]]]].
    { rewrite Q_of_nat_mul, Q_of_nat_2; lra. }
    exists b, (WV :: v), (l * (1#2)); split; [exact (Scan_T hS) | exact hB].
  - pose proof (zWn u) as hw. cbn [z0Y z0Z] in hk.
    destruct (hEk eq_refl) as [n ->].
    destruct (z0F n) as [[a ->] | [a ->]].
    + destruct a as [| a]; [cbn in hk; rewrite Q_of_nat_0 in hk; lra |].
      destruct (IH (a * 2)%nat (fun _ => ex_intro _ a eq_refl))
        as [b [v [l [hS hB]]]].
      { push_Q_of_nat; lra. }
      exists b, (WQ :: v), (1 + l * 2); split; [| exact hB].
      replace (S a * 2 * 2)%nat with (4 + a * 4)%nat by lia.
      exact (Scan_short10 hS).
    + destruct (IH (a * 2)%nat (fun _ => ex_intro _ a eq_refl))
        as [b [v [l [hS hB]]]].
      { push_Q_of_nat; lra. }
      exists b, (WK :: v), (1 + l * 2); split; [| exact hB].
      replace ((1 + a * 2) * 2)%nat with (2 + a * 4)%nat by lia.
      exact (Scan_short00 hS).
  - pose proof (zWn u) as hw. cbn [z0Y z0Z] in hk.
    destruct (hEk eq_refl) as [n ->].
    destruct (z0F n) as [[a ->] | [a ->]].
    + destruct a as [| a]; [cbn in hk; rewrite Q_of_nat_0 in hk; lra |].
      destruct (IH (1 + a * 2)%nat (fun H => ltac:(discriminate H)))
        as [b [v [l [hS hB]]]].
      { push_Q_of_nat; lra. }
      exists b, (WQ :: v), (l * 2); split; [| exact hB].
      replace (S a * 2 * 2)%nat with (4 + a * 4)%nat by lia.
      exact (Scan_short11 hS).
    + destruct (IH (1 + a * 2)%nat (fun H => ltac:(discriminate H)))
        as [b [v [l [hS hB]]]].
      { push_Q_of_nat; lra. }
      exists b, (WK :: v), (l * 2); split; [| exact hB].
      replace ((1 + a * 2) * 2)%nat with (2 + a * 4)%nat by lia.
      exact (Scan_short01 hS).
  - pose proof (zWn u) as hw. cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [rewrite Q_of_nat_0 in hk; lra |].
    change (S k) with (1 + k)%nat in *.
    destruct (IH (k * 2)%nat (fun _ => ex_intro _ k eq_refl))
      as [b [v [l [hS hB]]]].
    { rewrite Q_of_nat_add, Q_of_nat_1 in hk.
      rewrite Q_of_nat_mul, Q_of_nat_2; lra. }
    exists b, (WV :: v), ((1 + l) * (1#2)); split; [exact (Scan_pair0 hS) | exact hB].
  - pose proof (zWn u) as hw. cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [rewrite Q_of_nat_0 in hk; lra |].
    change (S k) with (1 + k)%nat in *.
    destruct (IH (1 + k * 2)%nat (fun H => ltac:(discriminate H)))
      as [b [v [l [hS hB]]]].
    { rewrite Q_of_nat_add, Q_of_nat_1 in hk.
      rewrite Q_of_nat_add, Q_of_nat_mul, Q_of_nat_1, Q_of_nat_2; lra. }
    exists b, (WV :: v), ((1#4) + l * (1#2)); split; [exact (Scan_pair1 hS) | exact hB].
Qed.

Lemma z1a (u : zW) (k : nat) (h : (z0Y u + z0Z u) * 2 < Q_of_nat (k * 2)) :
  exists b v l, Scan (k * 2) u b v l /\ (0 < b)%nat.
Proof.
  exact (z19 (proj1 (z0J u)) (k * 2)%nat (fun _ => ex_intro _ k eq_refl) h).
Qed.

Lemma zSz (n : nat) (u : zW) (b : nat) (v : zW) (l : Rat) :
  ~ Scan (1 + n * 2) (WK :: u) b v l.
Proof.
  intro h. remember (1 + n * 2)%nat as a eqn:Ha.
  inverts h; lia.
Qed.

Lemma zSo (r : nat) :
  forall (n b : nat) (v : zW) (l : Rat),
    ~ Scan (1 + n * 2) (zR (r * 2) WQ ++ [WK]) b v l.
Proof.
  induction r as [| r IH]; intros n b v l hI.
  - exact (zSz n [] b v l hI).
  - replace (S r * 2)%nat with (2 + r * 2)%nat in hI by lia.
    cbn [Nat.add repeat app] in hI.
    remember (1 + n * 2)%nat as a eqn:Ha.
    inverts hI as hJ; try lia.
    exact (IH _ _ _ _ hJ).
Qed.

Lemma zS1 (r : nat) :
  forall (a b : nat) (v : zW) (l : Rat),
    Scan a (zR (1 + r * 2) WQ ++ [WK]) b v l ->
    v = zR (1 + r) WV /\ b = ((a - 1) * 2 ^ (1 + r))%nat /\ l == (1#2).
Proof.
  induction r as [| r IH]; intros a b v l hI.
  - cbn [Nat.mul Nat.add repeat app] in hI.
    inverts hI as hJ.
    + inverts hJ. split; [reflexivity | split; [cbn; lia | lra]].
    + exfalso; exact (zSz _ [] _ _ _ hJ).
    + exfalso; exact (zSz _ [] _ _ _ hJ).
  - replace (1 + S r * 2)%nat with (2 + (1 + r * 2))%nat in hI by lia.
    cbn [Nat.add repeat app] in hI.
    inverts hI as hJ.
    + destruct (IH _ _ _ _ hJ) as [-> [-> Hl0]].
      split; [reflexivity | split; [| lra]].
      replace (1 + n * 2 - 1)%nat with (n * 2)%nat by lia.
      replace (1 + n - 1)%nat with n by lia.
      change (1 + S r)%nat with (1 + (1 + r))%nat.
      cbn [Nat.add Nat.pow].
      rewrite <- Nat.mul_assoc. f_equal; lia.
    + exfalso.
      replace (WQ :: zR (1 + r * 2) WQ ++ [WK]) with (zR (S r * 2) WQ ++ [WK]) in hJ
        by (replace (S r * 2)%nat with (1 + (1 + r * 2))%nat by lia; reflexivity).
      exact (zSo (S r) _ _ _ _ hJ).
    + exfalso.
      replace (WQ :: zR (1 + r * 2) WQ ++ [WK]) with (zR (S r * 2) WQ ++ [WK]) in hJ
        by (replace (S r * 2)%nat with (1 + (1 + r * 2))%nat by lia; reflexivity).
      exact (zSo (S r) _ _ _ _ hJ).
Qed.

Inductive zTd : zW -> Rat -> Prop :=
  | tail_end : zTd [WK] 0
  | tail_zero {u : zW} {z : Rat} : zTd u z -> zTd (WK :: u) (1 + z * 2)
  | tail_one {u : zW} {z : Rat} : zTd u z -> zTd (WQ :: u) (z * 2).

Lemma z1e {u : zW} {z : Rat} (h : zTd u z) : 0 <= z.
Proof. induction h; lra. Qed.

Lemma z1f {u : zW} {z : Rat} (h : zTd (WK :: u) z) :
  (u = [] /\ z == 0) \/ exists y, zTd u y /\ z == 1 + y * 2.
Proof.
  inverts h as hJ; [left; split; [reflexivity | lra] | right; exists z0; split; [exact hJ | lra]].
Qed.

Lemma zTo {u : zW} {z : Rat} (h : zTd (WQ :: u) z) :
  exists y, zTd u y /\ z == y * 2.
Proof.
  inverts h as hJ; exists z0; split; [exact hJ | lra].
Qed.

Lemma z1g {A H : nat} {u : zW} (h : zDg A H u) : zTd (u ++ [WK]) (z0Z u).
Proof.
  induction h; cbn [app z0Z]; constructor; assumption.
Qed.

Lemma z1h {a : nat} {u : zW} {b : nat} {v : zW} {l : Rat}
  (h : Scan a u b v l) :
  forall {z : Rat}, zTd u z ->
    z0Y v <= 1 + z * 2 /\ l <= 1 + z * 2 /\
    (forall n : nat, a = (1 + n * 2)%nat -> z0Y v <= z * 2 /\ l <= (1#2) + z * 2).
Proof.
  induction h as [k | n u k v l hI IH | n u k v l hI IH | n u k v l hI IH
    | n u k v l hI IH | n u k v l hI IH | n u k v l hI IH | n u k v l hI IH];
    intros z hZ.
  - inverts hZ.
  - inverts hZ.
  - destruct (zTo hZ) as [y [hJ Hz]].
    destruct (z1f hJ) as [[-> Hy] | [x [hJ' Hy]]].
    + inverts hI. cbn [z0Y]; repeat split; intros; lra.
    + destruct (IH _ hJ') as [hM [hL _]].
      pose proof (z1e hJ') as hx.
      cbn [z0Y]; repeat split; intros; lra.
  - destruct (zTo hZ) as [y [hJ Hz]].
    destruct (zTo hJ) as [x [hJ' Hy]].
    destruct (proj2 (proj2 (IH _ hJ')) n eq_refl) as [hM hL].
    pose proof (z1e hJ') as hx.
    cbn [z0Y]; repeat split; intros; lra.
  - destruct (z1f hZ) as [[-> Hz] | [x [hJ Hz]]].
    + inverts hI. cbn [z0Y]; repeat split; try lra; intros; lia.
    + destruct (IH _ hJ) as [hM [hL _]].
      cbn [z0Y]; repeat split; try lra; intros; lia.
  - destruct (zTo hZ) as [x [hJ Hz]].
    destruct (proj2 (proj2 (IH _ hJ)) n eq_refl) as [hM hL].
    cbn [z0Y]; repeat split; try lra; intros; lia.
  - destruct (z1f hZ) as [[-> Hz] | [x [hJ Hz]]].
    + inverts hI. cbn [z0Y]; repeat split; try lra; intros; lia.
    + destruct (IH _ hJ) as [hM [hL _]].
      cbn [z0Y]; repeat split; try lra; intros; lia.
  - destruct (zTo hZ) as [x [hJ Hz]].
    destruct (proj2 (proj2 (IH _ hJ)) n eq_refl) as [hM hL].
    cbn [z0Y]; repeat split; try lra; intros; lia.
Qed.

Lemma z0L_odd_scan {n : nat} {w : zW} {b : nat} {v : zW} {l : Rat}
  (h : Scan (1 + n * 2)%nat (w ++ [WQ; WQ; WK]) b v l)
  (hL : z0L (WQ :: w ++ [WK]) = true) :
  z0L (w ++ [WK]) = true.
Proof.
  destruct w as [| t0 w'].
  - exfalso; exact (zSo 1%nat n b v l h).
  - destruct t0.
    + cbn [app z0L] in hL |- *; exact hL.
    + exfalso; exact (zSz n (w' ++ [WQ; WQ; WK]) b v l h).
    + destruct w' as [| t1 w''].
      * reflexivity.
      * destruct t1; try reflexivity.
        cbn [app] in h.
        remember (1 + n * 2)%nat as a eqn:Ha.
        inverts h; lia.
Qed.

Lemma zScan_qqk {a : nat} {u : zW} {b : nat} {v : zW} {l : Rat}
  (h : Scan a u b v l) :
  forall (w0 : zW), u = w0 ++ [WQ; WQ; WK] ->
    z11 v <= (1#8) * z11 u /\
    (z0L (w0 ++ [WK]) = true -> z11 v <= (1#64) * z11 u) /\
    (exists n : nat, b = (n * 4)%nat) /\
    (exists v0 : zW, v = v0 ++ [WV]).
Proof.
  induction h as [k | n u0 k v0 l0 hSub IH | n u0 k v0 l0 hSub IH | n u0 k v0 l0 hSub IH
    | n u0 k v0 l0 hSub IH | n u0 k v0 l0 hSub IH | n u0 k v0 l0 hSub IH | n u0 k v0 l0 hSub IH];
    intros w0 hu.
  - destruct w0; discriminate hu.
  - destruct w0 as [| t0 w']; [discriminate hu |].
    injection hu as <- hu0.
    destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
    repeat split.
    + cbn [z11]; lra.
    + intro hL; pose proof (h2 hL); cbn [z11] in *; lra.
    + exists m; exact hm.
    + exists (WV :: vp); cbn [app]; f_equal; exact hvp.
  - destruct w0 as [| t0 [| t1 w']]; [discriminate hu | destruct t0; discriminate hu |].
    injection hu as <- <- hu0.
    destruct (IH w' hu0) as [h1 [_ [[m hm] [vp hvp]]]].
    pose proof (zSp u0) as hp.
    repeat split.
    + cbn [z11]; lra.
    + intro; cbn [z11]; lra.
    + exists m; exact hm.
    + exists (WV :: vp); cbn [app]; f_equal; exact hvp.
  - destruct w0 as [| t0 [| t1 w']].
    + injection hu as ->; exfalso; exact (zSz n [] k v0 l0 hSub).
    + injection hu as <- ->.
      destruct (zS1 0%nat (1 + n * 2)%nat k v0 l0 hSub) as [-> [hk _]].
      repeat split.
      * cbn [Nat.add repeat z11]; lra.
      * intro; cbn [Nat.add repeat z11]; lra.
      * exists n; cbn in hk; lia.
      * exists [WV]; reflexivity.
    + injection hu as <- <- hu0.
      destruct (IH w' hu0) as [h1 [_ [[m hm] [vp hvp]]]].
      pose proof (zSp u0) as hp.
      repeat split.
      * cbn [z11]; lra.
      * intro; cbn [z11]; lra.
      * exists m; exact hm.
      * exists (WV :: vp); cbn [app]; f_equal; exact hvp.
  - destruct w0 as [| t0 w']; [discriminate hu |].
    injection hu as <- hu0.
    destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
    repeat split.
    + cbn [z11]; lra.
    + intro hL; pose proof (h2 hL); cbn [z11] in *; lra.
    + exists m; exact hm.
    + exists (WK :: vp); cbn [app]; f_equal; exact hvp.
  - destruct w0 as [| t0 w'].
    + injection hu as ->.
      destruct (zS1 0%nat (1 + n * 2)%nat k v0 l0 hSub) as [-> [hk _]].
      repeat split.
      * cbn [Nat.add repeat z11]; lra.
      * intro hL; discriminate hL.
      * exists n; cbn in hk; lia.
      * exists [WK]; reflexivity.
    + injection hu as <- hu0.
      destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
      repeat split.
      * cbn [z11]; lra.
      * intro hL; cbn [app] in hL; rewrite hu0 in hSub;
        pose proof (h2 (z0L_odd_scan hSub hL)); cbn [z11] in *; lra.
      * exists m; exact hm.
      * exists (WK :: vp); cbn [app]; f_equal; exact hvp.
  - destruct w0 as [| t0 w']; [discriminate hu |].
    injection hu as <- hu0.
    destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
    repeat split.
    + cbn [z11]; lra.
    + intro hL; pose proof (h2 hL); cbn [z11] in *; lra.
    + exists m; exact hm.
    + exists (WQ :: vp); cbn [app]; f_equal; exact hvp.
  - destruct w0 as [| t0 w'].
    + injection hu as ->.
      destruct (zS1 0%nat (1 + n * 2)%nat k v0 l0 hSub) as [-> [hk _]].
      repeat split.
      * cbn [Nat.add repeat z11]; lra.
      * intro hL; discriminate hL.
      * exists n; cbn in hk; lia.
      * exists [WQ]; reflexivity.
    + injection hu as <- hu0.
      destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
      repeat split.
      * cbn [z11]; lra.
      * intro hL; cbn [app] in hL; rewrite hu0 in hSub;
        pose proof (h2 (z0L_odd_scan hSub hL)); cbn [z11] in *; lra.
      * exists m; exact hm.
      * exists (WQ :: vp); cbn [app]; f_equal; exact hvp.
Qed.

(* ---------- Section 7C: BScan (15 constructors) and its lemmas ---------- *)

Fixpoint zIv (r : nat) : Rat :=
  match r with
  | O => 1
  | S r' => zIv r' * (1#2)
  end.

Fixpoint zP4 (r : nat) : Rat :=
  match r with
  | O => 1
  | S r' => zP4 r' * 4
  end.

Lemma zIv_P4 (r : nat) :
  0 < zIv r /\ zIv r <= 1 /\ 1 <= zP4 r /\
  ((1 <= r)%nat -> 4 <= zP4 r /\ 8 * zIv r <= zP4 r).
Proof.
  induction r as [| r [h1 [h2 [h3 h4]]]].
  - cbn [zIv zP4]; repeat split; try lra; intros; lia.
  - cbn [zIv zP4]; destruct r as [| r'].
    + cbn [zIv zP4]; repeat split; try lra; intros _; split; lra.
    + destruct (h4 ltac:(lia)) as [h4a h4b].
      repeat split; try lra; intros _; split; lra.
Qed.

Lemma z11_R (r : nat) (u : zW) : z11 (zR r WV ++ u) == zIv r * z11 u.
Proof.
  induction r as [| r IH]; [cbn; lra |].
  cbn [repeat app z11 zIv]; rewrite IH; ring.
Qed.

Lemma z11_QK (r : nat) (u : zW) : z11 (zQK r u) == zP4 r * z11 u.
Proof.
  induction r as [| r IH]; [cbn; lra |].
  cbn [zQK z11 zP4]; rewrite IH; ring.
Qed.

Lemma z0W_R (r : nat) (u : zW) : z0W (zR r WV ++ u) == zIv r * z0W u.
Proof.
  induction r as [| r IH]; [cbn; lra |].
  cbn [repeat app z0W zIv]; rewrite IH; ring.
Qed.

Lemma z0W_QK (r : nat) (u : zW) :
  z0W (zQK r u) == (5#4) * (zP4 r - 1) + zP4 r * z0W u.
Proof.
  induction r as [| r IH]; [cbn; lra |].
  cbn [zQK z0W zP4]; rewrite IH; ring.
Qed.

Inductive BScan : bool -> nat -> zW -> nat -> zW -> Rat -> Rat -> Prop :=
  | BScan_nil (k : nat) : BScan false k [] k [] 0 0
  | BScan_T {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2)%nat u k v a b ->
      BScan false (2 + n)%nat (WV :: u) k (WV :: v) (a * (1#2)) (b * (1#2))
  | BScan_pair0 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2)%nat u k v a b ->
      BScan false (1 + n)%nat (WQ :: WK :: u) k (WV :: v) (a * (1#2)) ((1#4) + b * (1#2))
  | BScan_pair1 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2)%nat u k v a b ->
      BScan false (1 + n)%nat (WQ :: WQ :: u) k (WV :: v) (a * (1#2)) ((1#2) + b * (1#2))
  | BScan_short00 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2)%nat u k v a b ->
      BScan false (2 + n * 4)%nat (WK :: u) k (WK :: v) ((5#2) + a * 2) (b * 2)
  | BScan_short01 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2)%nat u k v a b ->
      BScan false (2 + n * 4)%nat (WQ :: u) k (WK :: v) ((3#2) + a * 2) (b * 2)
  | BScan_short10 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2)%nat u k v a b ->
      BScan false (4 + n * 4)%nat (WK :: u) k (WQ :: v) ((7#2) + a * 2) (b * 2)
  | BScan_short11 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2)%nat u k v a b ->
      BScan false (4 + n * 4)%nat (WQ :: u) k (WQ :: v) ((5#2) + a * 2) (b * 2)
  | BScan_odd_chain0 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (1 + r))%nat u k v a b ->
      BScan false (3 + m * 4)%nat (zQK r (WV :: u)) k (WK :: (zR r WV ++ v))
        ((2 + a * 2) * zIv r) (b * 2 * zIv r)
  | BScan_odd_chain1 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (1 + r))%nat u k v a b ->
      BScan false (5 + m * 4)%nat (zQK r (WV :: u)) k (WQ :: (zR r WV ++ v))
        (1 + (2 + a * 2) * zIv r) (b * 2 * zIv r)
  | BScan_even_chain (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + (1 + m * 2) * 2 ^ (1 + r))%nat u k v a b ->
      BScan false (6 + m * 2)%nat (WK :: zQK r (WV :: u)) k (zR (1 + r) WV ++ v)
        (1 + (1 + a) * (1#2) * zIv r) (b * (1#2) * zIv r)
  | BScan_shift_pair0 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2)%nat u k v a b ->
      BScan true (1 + n)%nat (WK :: u) k (WV :: v) (a * (1#2)) ((1#4) + b * (1#2))
  | BScan_shift_pair1 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2)%nat u k v a b ->
      BScan true (1 + n)%nat (WQ :: u) k (WV :: v) (a * (1#2)) ((1#2) + b * (1#2))
  | BScan_shift_chain0 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (2 + r))%nat u k v a b ->
      BScan true (3 + m * 4)%nat (WK :: zQK r (WV :: u)) k (WK :: (zR (1 + r) WV ++ v))
        ((1 + a) * zIv r) (b * zIv r)
  | BScan_shift_chain1 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (2 + r))%nat u k v a b ->
      BScan true (5 + m * 4)%nat (WK :: zQK r (WV :: u)) k (WQ :: (zR (1 + r) WV ++ v))
        (1 + (1 + a) * zIv r) (b * zIv r).

Lemma zIv_pow2 (r : nat) : Q_of_nat (2 ^ r) * zIv r == 1.
Proof.
  induction r as [| r IH]; [cbn [Nat.pow zIv]; rewrite Q_of_nat_1; lra |].
  rewrite Q_of_nat_pow2_S; cbn [zIv]; nra.
Qed.

Lemma z1i {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan s k u k' v a b) :
  Q_of_nat k - 3 == (Q_of_nat k' - 3) * z11 v + 2 * (a - b).
Proof.
  induction h; cbn [z11]; try (push_Q_of_nat; lra).
  - rewrite z11_R.
    assert (hp : Q_of_nat (2 ^ (1 + r)) * zIv r == 2)
      by (rewrite Q_of_nat_pow2; pose proof (zIv_pow2 r); lra).
    push_Q_of_nat.
    assert (hm : Q_of_nat m * Q_of_nat (2 ^ (1 + r)) * zIv r == Q_of_nat m * 2)
      by (rewrite <- Qmult_assoc, hp; ring).
    nra.
  - rewrite z11_R.
    assert (hp : Q_of_nat (2 ^ (1 + r)) * zIv r == 2)
      by (rewrite Q_of_nat_pow2; pose proof (zIv_pow2 r); lra).
    push_Q_of_nat.
    assert (hm : Q_of_nat m * Q_of_nat (2 ^ (1 + r)) * zIv r == Q_of_nat m * 2)
      by (rewrite <- Qmult_assoc, hp; ring).
    nra.
  - cbn [Nat.add repeat app z11]; rewrite z11_R.
    assert (hp : Q_of_nat (2 ^ (1 + r)) * zIv r == 2)
      by (rewrite Q_of_nat_pow2; pose proof (zIv_pow2 r); lra).
    push_Q_of_nat.
    assert (hm : (1 + Q_of_nat m * 2) * Q_of_nat (2 ^ (1 + r)) * zIv r == (1 + Q_of_nat m * 2) * 2)
      by (rewrite <- Qmult_assoc, hp; ring).
    nra.
  - cbn [Nat.add repeat app z11]; rewrite z11_R.
    assert (hp : Q_of_nat (2 ^ (2 + r)) * zIv r == 4).
    { change (2 + r)%nat with (1 + (1 + r))%nat.
      rewrite !Q_of_nat_pow2; pose proof (zIv_pow2 r); lra. }
    push_Q_of_nat.
    assert (hm : Q_of_nat m * Q_of_nat (2 ^ (2 + r)) * zIv r == Q_of_nat m * 4)
      by (rewrite <- Qmult_assoc, hp; ring).
    nra.
  - cbn [Nat.add repeat app z11]; rewrite z11_R.
    assert (hp : Q_of_nat (2 ^ (2 + r)) * zIv r == 4).
    { change (2 + r)%nat with (1 + (1 + r))%nat.
      rewrite !Q_of_nat_pow2; pose proof (zIv_pow2 r); lra. }
    push_Q_of_nat.
    assert (hm : Q_of_nat m * Q_of_nat (2 ^ (2 + r)) * zIv r == Q_of_nat m * 4)
      by (rewrite <- Qmult_assoc, hp; ring).
    nra.
Qed.

Lemma z1j {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan s k u k' v a b) :
  (s = false ->
    z0W v <= (66#19) * z0W u /\
    a - b <= (64#11) * z0W u /\
    b - a <= (1#2) * z0W u) /\
  (s = true ->
    z0W v <= (33#38) * z0W u - (11#16) /\
    a - b <= (16#11) * z0W u - (3#2) /\
    b - a <= (1#8) * z0W u + (3#8)) /\
  (s = true -> (exists m : nat, k = (1 + m * 4)%nat) ->
    z0W v <= (33#38) * z0W u - (33#38)).
Proof.
  induction h.
  - split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; repeat split; lra | split; intro H; discriminate H].
  - destruct (proj1 (proj2 IHh) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [| split; intro H; discriminate H].
    intros _; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r'];
      [ cbn [zIv zP4]; repeat split; lra
      | destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]];
        destruct (hge1 ltac:(lia)) as [hp4_4 _]; repeat split; nra ].
  - destruct (proj1 (proj2 IHh) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [| split; intro H; discriminate H].
    intros _; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r'];
      [ cbn [zIv zP4]; repeat split; lra
      | destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]];
        destruct (hge1 ltac:(lia)) as [hp4_4 _]; repeat split; nra ].
  - destruct (proj1 (proj2 IHh) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]].
    split; [| split; intro H; discriminate H].
    intros _; cbn [Nat.add repeat app z0W]; rewrite z0W_R, z0W_QK; cbn [z0W]; repeat split; nra.
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intro H; discriminate H | split; [intros _; cbn [z0W]; repeat split; lra | intros _ _; cbn [z0W]; lra]].
  - destruct (proj1 IHh eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intro H; discriminate H | split; [intros _; cbn [z0W]; repeat split; lra | intros _ _; cbn [z0W]; lra]].
  - assert (hdiv : exists m' : nat, (1 + m * 2 ^ (2 + r) = 1 + m' * 4)%nat).
    { exists (m * 2 ^ r)%nat.
      change (2 + r)%nat with (1 + (1 + r))%nat; rewrite !zP2; lia. }
    destruct (proj1 (proj2 IHh) eq_refl) as [_ [h2 h3]].
    pose proof (proj2 (proj2 IHh) eq_refl hdiv) as h1.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intro H; discriminate H | split; [intros _ | intros _ [q hq]; lia]].
    cbn [Nat.add repeat app z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r'];
      [ cbn [zIv zP4]; repeat split; lra
      | destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]];
        destruct (hge1 ltac:(lia)) as [hp4_4 _]; repeat split; nra ].
  - destruct (proj1 (proj2 IHh) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intro H; discriminate H | split; [intros _ | intros _ _]];
      cbn [Nat.add repeat app z0W]; rewrite z0W_R, z0W_QK; cbn [z0W];
      (destruct r as [| r'];
        [ cbn [zIv zP4]; repeat split; lra
        | destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]];
          destruct (hge1 ltac:(lia)) as [hp4_4 _]; repeat split; nra ]).
Qed.

Lemma z1k {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h1 : BScan s k u k' v a b) :
  forall {w : zW} {k'' : nat} {x : zW} {c d : Rat},
    BScan false k' w k'' x c d ->
    exists a' b', BScan s k (u ++ w) k'' (v ++ x) a' b' /\
      a' == a + z11 v * c /\ b' == b + z11 v * d.
Proof.
  induction h1; intros w k'' x c d h2.
  - exists c, d; repeat split; [exact h2 | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), (b' * (1#2)); repeat split; [exact (BScan_T hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#4) + b' * (1#2)); repeat split; [exact (BScan_pair0 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#2) + b' * (1#2)); repeat split; [exact (BScan_pair1 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((5#2) + a' * 2), (b' * 2); repeat split; [exact (BScan_short00 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((3#2) + a' * 2), (b' * 2); repeat split; [exact (BScan_short01 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((7#2) + a' * 2), (b' * 2); repeat split; [exact (BScan_short10 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((5#2) + a' * 2), (b' * 2); repeat split; [exact (BScan_short11 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((2 + a' * 2) * zIv r), (b' * 2 * zIv r); repeat split.
    + rewrite <- (zQK_append r (WV :: u) w); cbn [app]; rewrite <- app_assoc.
      exact (BScan_odd_chain0 r hK).
    + cbn [z11]; rewrite z11_R, hA; ring.
    + cbn [z11]; rewrite z11_R, hB; ring.
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (2 + a' * 2) * zIv r), (b' * 2 * zIv r); repeat split.
    + rewrite <- (zQK_append r (WV :: u) w); cbn [app]; rewrite <- app_assoc.
      exact (BScan_odd_chain1 r hK).
    + cbn [z11]; rewrite z11_R, hA; ring.
    + cbn [z11]; rewrite z11_R, hB; ring.
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (1 + a') * (1#2) * zIv r), (b' * (1#2) * zIv r); repeat split.
    + cbn [Nat.add repeat app]; rewrite <- (zQK_append r (WV :: u) w); cbn [app]; rewrite <- app_assoc.
      exact (BScan_even_chain r hK).
    + cbn [Nat.add repeat app z11]; rewrite z11_R, hA; ring.
    + cbn [Nat.add repeat app z11]; rewrite z11_R, hB; ring.
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#4) + b' * (1#2)); repeat split; [exact (BScan_shift_pair0 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#2) + b' * (1#2)); repeat split; [exact (BScan_shift_pair1 hK) | cbn [z11]; lra | cbn [z11]; lra].
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((1 + a') * zIv r), (b' * zIv r); repeat split.
    + cbn [Nat.add repeat app]; rewrite <- (zQK_append r (WV :: u) w); cbn [app]; rewrite <- app_assoc.
      exact (BScan_shift_chain0 r hK).
    + cbn [Nat.add repeat app z11]; rewrite z11_R, hA; ring.
    + cbn [Nat.add repeat app z11]; rewrite z11_R, hB; ring.
  - destruct (IHh1 _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (1 + a') * zIv r), (b' * zIv r); repeat split.
    + cbn [Nat.add repeat app]; rewrite <- (zQK_append r (WV :: u) w); cbn [app]; rewrite <- app_assoc.
      exact (BScan_shift_chain1 r hK).
    + cbn [Nat.add repeat app z11]; rewrite z11_R, hA; ring.
    + cbn [Nat.add repeat app z11]; rewrite z11_R, hB; ring.
Qed.

Lemma z1n {k : nat} {u : zW} {k' : nat} {v : zW} {l : Rat}
  (hI : Scan k u k' v l) :
  forall {A H : nat}, zDg A H u ->
    exists a b, BScan false k u k' v a b /\ a - b <= (5#2) * z0Y v + l /\ b - a <= 1.
Proof.
  induction hI; intros A H hD.
  - exists 0, 0; repeat split; [exact (BScan_nil k) | cbn [z0Y]; lra | lra].
  - exfalso; exact (z0K hD).
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (zD0 hD1) as [A2 [H2 [hD2 _]]].
    destruct (IHhI _ _ hD2) as [a [b [hJ [hP hM]]]].
    exists (a * (1#2)), ((1#4) + b * (1#2)); repeat split; [exact (BScan_pair0 hJ) | cbn [z0Y]; lra | lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (zD1 hD1) as [A2 [H2 [hD2 _]]].
    destruct (IHhI _ _ hD2) as [a [b [hJ [hP hM]]]].
    exists (a * (1#2)), ((1#2) + b * (1#2)); repeat split; [exact (BScan_pair1 hJ) | cbn [z0Y]; lra | lra].
  - destruct (zD0 hD) as [A1 [H1 [hD1 _]]].
    destruct (IHhI _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((5#2) + a * 2), (b * 2); repeat split; [exact (BScan_short00 hJ) | cbn [z0Y]; lra | lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (IHhI _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((3#2) + a * 2), (b * 2); repeat split; [exact (BScan_short01 hJ) | cbn [z0Y]; lra | lra].
  - destruct (zD0 hD) as [A1 [H1 [hD1 _]]].
    destruct (IHhI _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((7#2) + a * 2), (b * 2); repeat split; [exact (BScan_short10 hJ) | cbn [z0Y]; lra | lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (IHhI _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((5#2) + a * 2), (b * 2); repeat split; [exact (BScan_short11 hJ) | cbn [z0Y]; lra | lra].
Qed.

Lemma zHi_bscan {m k' : nat} {w0 y : zW} {l : Rat} {A0 H0 : nat}
  (hS : Scan (m * 2)%nat (w0 ++ [WQ; WQ; WK]) k' y l)
  (hD0 : zDg A0 H0 w0) :
  exists a b, BScan false (1 + m)%nat ((WQ :: WK :: w0) ++ [WQ; WQ; WK]) k' (WV :: y) a b /\
    z0Y (WV :: y) <= (1#4) * z0Z (WQ :: WK :: w0) /\
    a - b <= (7#8) * z0Z (WQ :: WK :: w0) /\
    b - a <= 1.
Proof.
  assert (hD_qq : zDg 3%nat 2%nat [WQ; WQ]) by exact (zDg_one (zDg_one zDg_nil)).
  pose proof (z0U hD0 hD_qq) as hD_w.
  assert (hS' : Scan (m * 2)%nat ((w0 ++ [WQ; WQ]) ++ [WK]) k' y l)
    by (rewrite <- app_assoc; exact hS).
  destruct (z1h hS' (z1g hD_w)) as [hY [hL _]].
  assert (hZ_eq : z0Z (w0 ++ [WQ; WQ]) == z0Z w0)
    by (rewrite z14; cbn [z0Z]; ring).
  rewrite hZ_eq in hY, hL.
  pose proof (z0U hD_w (zDg_zero zDg_nil)) as hD_wk.
  destruct (z1n hS' hD_wk) as [a0 [b0 [hB0 [hAB0 hBA0]]]].
  rewrite <- app_assoc in hB0.
  exists (a0 * (1#2)), ((1#4) + b0 * (1#2)); repeat split.
  - cbn [app]; exact (BScan_pair0 hB0).
  - cbn [z0Y z0Z]; lra.
  - cbn [z0Z]; lra.
  - lra.
Qed.

Definition zSwt (s : bool) : Rat :=
  match s with
  | false => 1
  | true => 1#4
  end.

Lemma z1p_upper {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan s k u k' v a b) :
  z11 v <= zSwt s * z11 u.
Proof.
  induction h; cbn [z11 zSwt] in *; try lra.
  - pose proof (zSp u); lra.
  - pose proof (zSp u); lra.
  - rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]]; nra.
  - rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]]; nra.
  - cbn [Nat.add repeat app z11]; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]]; nra.
  - cbn [Nat.add repeat app z11]; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]]; nra.
  - cbn [Nat.add repeat app z11]; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]]; nra.
Qed.

Lemma zBz (n : nat) (u : zW) (k' : nat) (v : zW) (a b : Rat) :
  ~ BScan false (1 + n * 2)%nat (WK :: u) k' v a b.
Proof.
  intro h.
  remember false as s eqn:Hs.
  remember (1 + n * 2)%nat as k eqn:Hk.
  remember (WK :: u) as w eqn:Hw.
  inversion h; subst; try discriminate; try lia;
    destruct r; discriminate.
Qed.

Lemma z0L_odd_bscan {n : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan false (1 + n * 2)%nat u k' v a b)
  (hL : z0L (WQ :: u) = true) :
  z0L u = true.
Proof.
  destruct u as [| t0 u']; [discriminate hL |].
  destruct t0.
  - exact hL.
  - exfalso; exact (zBz n u' k' v a b h).
  - remember false as s eqn:Hs.
    remember (1 + n * 2)%nat as k eqn:Hk.
    remember (WQ :: u') as w eqn:Hw.
    inversion h; subst; try discriminate; try lia.
    + match goal with H : _ = WQ :: u' |- _ => injection H as <-; reflexivity end.
    + match goal with H : _ = WQ :: u' |- _ => injection H as <-; reflexivity end.
    + destruct r as [| r']; [discriminate | match goal with H : _ = WQ :: u' |- _ => injection H as <-; reflexivity end].
    + destruct r as [| r']; [discriminate | match goal with H : _ = WQ :: u' |- _ => injection H as <-; reflexivity end].
Qed.

Lemma z1p_z0L {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan s k u k' v a b)
  (hL : z0L u = true) :
  z11 v <= (1#8) * zSwt s * z11 u.
Proof.
  induction h.
  - discriminate hL.
  - pose proof (IHh hL); cbn [z11 zSwt] in *; lra.
  - pose proof (z1p_upper h); cbn [z11 zSwt] in *; lra.
  - pose proof (z1p_upper h); cbn [z11 zSwt] in *; lra.
  - pose proof (IHh hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IHh (z0L_odd_bscan h hL)); cbn [z11 zSwt] in *; lra.
  - pose proof (IHh hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IHh (z0L_odd_bscan h hL)); cbn [z11 zSwt] in *; lra.
  - destruct r as [| r'].
    + pose proof (IHh hL); cbn [zQK repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper h) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8]; nra.
  - destruct r as [| r'].
    + pose proof (IHh hL); cbn [zQK repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper h) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8]; nra.
  - pose proof (z1p_upper h) as hUp.
    cbn [Nat.add repeat app z11 zSwt] in hUp |- *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]]; nra.
  - pose proof (IHh hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IHh (z0L_odd_bscan h hL)); cbn [z11 zSwt] in *; lra.
  - destruct r as [| r'].
    + pose proof (IHh hL); cbn [Nat.add zQK repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper h) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite z11_R, z11_QK;
      change (zIv (1 + S r')) with (zIv (S r') * (1#2)); cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8]; nra.
  - destruct r as [| r'].
    + pose proof (IHh hL); cbn [Nat.add zQK repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper h) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite z11_R, z11_QK;
      change (zIv (1 + S r')) with (zIv (S r') * (1#2)); cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8]; nra.
Qed.

Inductive ModeU : Type := ME | MO | MS.

Inductive zPrU : ModeU -> zW -> Prop :=
  | zPrU_base_E : zPrU ME [WV]
  | zPrU_base_O : zPrU MO [WV]
  | zPrU_T_E {u : zW} : zPrU MO u -> zPrU ME (WV :: u)
  | zPrU_T_O {u : zW} : zPrU MO u -> zPrU MO (WV :: u)
  | zPrU_odd_c (r : nat) {u : zW} : zPrU MS u -> zPrU MO (zQK r (WV :: u))
  | zPrU_short_K {u : zW} : zPrU ME u -> zPrU ME (WK :: u)
  | zPrU_even_c (r : nat) {u : zW} : zPrU MS u -> zPrU ME (WK :: zQK r (WV :: u))
  | zPrU_shift_K {u : zW} : zPrU ME u -> zPrU MS (WK :: u)
  | zPrU_shift_c (r : nat) {u : zW} : zPrU MS u -> zPrU MS (WK :: zQK r (WV :: u))
  | zPrU_short_Q {u : zW} : zPrU MO u -> zPrU ME (WQ :: u)
  | zPrU_shift_Q {u : zW} : zPrU MO u -> zPrU MS (WQ :: u)
  | zPrU_pair0_E {u : zW} : zPrU ME u -> zPrU ME (WQ :: WK :: u)
  | zPrU_pair0_O {u : zW} : zPrU ME u -> zPrU MO (WQ :: WK :: u)
  | zPrU_pair1_E {u : zW} : zPrU MO u -> zPrU ME (WQ :: WQ :: u)
  | zPrU_pair1_O {u : zW} : zPrU MO u -> zPrU MO (WQ :: WQ :: u).

Definition zPrC (w : zW) : Prop :=
  exists r u, w = zQK r (WV :: u) /\ zPrU MS u.

Lemma zPrU_all (u_pre : zW) :
  let w := u_pre ++ [WV] in
  (zPrU ME w \/ zPrC w) /\
  (zPrU MO w \/ (zPrU MS w /\ (zPrU ME (WQ :: w) \/ zPrC (WQ :: w)) /\ zPrU MO (WQ :: w))).
Proof.
  induction u_pre as [| a u [hEC hOS]]; cbn [app].
  - split; [left; exact zPrU_base_E | left; exact zPrU_base_O].
  - destruct a.
    + destruct hOS as [hO | [hS _]].
      * split; [left; exact (zPrU_T_E hO) | left; exact (zPrU_T_O hO)].
      * split; [right; exists 0%nat, (u ++ [WV]); split; [reflexivity | exact hS]
               | left; exact (zPrU_odd_c 0%nat hS)].
    + destruct hEC as [hE | [r [u0 [hw hS]]]].
      * split; [left; exact (zPrU_short_K hE)
               | right; repeat split; [exact (zPrU_shift_K hE) | left; exact (zPrU_pair0_E hE) | exact (zPrU_pair0_O hE)]].
      * rewrite hw.
        split; [left; exact (zPrU_even_c r hS)
               | right; repeat split;
                 [ exact (zPrU_shift_c r hS)
                 | right; exists (S r), u0; split; [reflexivity | exact hS]
                 | exact (zPrU_odd_c (S r) hS) ]].
    + destruct hOS as [hO | [_ [hQ_EC hQ_O]]].
      * split; [left; exact (zPrU_short_Q hO)
               | right; repeat split; [exact (zPrU_shift_Q hO) | left; exact (zPrU_pair1_E hO) | exact (zPrU_pair1_O hO)]].
      * split; [exact hQ_EC | left; exact hQ_O].
Qed.

Lemma zPrU_MO_V (w : zW) : zPrU MO (WV :: (w ++ [WV])).
Proof.
  destruct (proj2 (zPrU_all w)) as [hO | [hS _]].
  - exact (zPrU_T_O hO).
  - exact (zPrU_odd_c 0%nat hS).
Qed.

Lemma zPrU_ME_VV (w : zW) : zPrU ME (WV :: WV :: (w ++ [WV])).
Proof. exact (zPrU_T_E (zPrU_MO_V w)). Qed.

Lemma zPrU_MS_W {u : zW} (h : zPrU MS u) : 1 <= z0W u.
Proof.
  remember MS as m eqn:Hm.
  inverts h; try discriminate.
  - pose proof (proj2 (proj2 (proj2 (zWn u0)))); cbn [z0W]; lra.
  - pose proof (proj2 (proj2 (proj2 (zWn u0)))); cbn [z0W]; rewrite z0W_QK; cbn [z0W].
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]]; nra.
  - pose proof (proj2 (proj2 (proj2 (zWn u0)))); cbn [z0W]; lra.
Qed.

Lemma zPrU_bscan {m : ModeU} {w : zW} (hI : zPrU m w) :
  ((m = ME \/ m = MO) ->
    forall (k : nat),
      (m = ME -> exists n : nat, k = (n * 2)%nat) ->
      (m = MO -> exists n : nat, k = (1 + n * 2)%nat) ->
      16 * z0W w < Q_of_nat k - 3 ->
      exists m' v a b, BScan false k w (1 + m')%nat v a b /\ (0 < m')%nat) /\
  (m = MS ->
    forall (k : nat),
      (exists n : nat, k = (1 + n * 2)%nat) ->
      4 * z0W w - 4 < Q_of_nat k - 3 ->
      exists m' v a b, BScan true k w (1 + m')%nat v a b /\ (0 < m')%nat).
Proof.
  induction hI.
  - (* base_E *)
    split; [| intro H; discriminate H].
    intros _ k hE _ hk.
    destruct (hE eq_refl) as [n ->].
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    eexists ((2 * n - 2) * 2)%nat, [WV], _, _; split; [| lia].
    replace (n * 2)%nat with (2 + (n - 1) * 2)%nat by lia.
    replace (1 + (2 * n - 2) * 2)%nat with (1 + ((n - 1) * 2) * 2)%nat by lia.
    exact (BScan_T (BScan_nil _)).
  - (* base_O *)
    split; [| intro H; discriminate H].
    intros _ k _ hO hk.
    destruct (hO eq_refl) as [n ->].
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (1 + n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    eexists ((2 * n - 1) * 2)%nat, [WV], _, _; split; [| lia].
    replace (1 + n * 2)%nat with (2 + (n * 2 - 1))%nat by lia.
    replace (1 + (2 * n - 1) * 2)%nat with (1 + (n * 2 - 1) * 2)%nat by lia.
    exact (BScan_T (BScan_nil _)).
  - (* T_E *)
    split; [| intro H; discriminate H].
    intros _ k hE _ hk.
    destruct (hE eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    assert (heq_n : (n * 2 = 2 + (n * 2 - 2))%nat) by lia.
    destruct (proj1 IHhI (or_intror eq_refl) (1 + (n * 2 - 2) * 2)%nat
      (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ (n * 2 - 2)%nat eq_refl))
      as [m' [v [a [b [hS hm']]]]].
    { rewrite heq_n in hk; push_Q_of_nat; lra. }
    rewrite heq_n.
    exists m', (WV :: v), (a * (1#2)), (b * (1#2)); split; [exact (BScan_T hS) | exact hm'].
  - (* T_O *)
    split; [| intro H; discriminate H].
    intros _ k _ hO hk.
    destruct (hO eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (1 + n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    assert (heq_n : (1 + n * 2 = 2 + (n * 2 - 1))%nat) by lia.
    destruct (proj1 IHhI (or_intror eq_refl) (1 + (n * 2 - 1) * 2)%nat
      (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl))
      as [m' [v [a [b [hS hm']]]]].
    { rewrite heq_n in hk; push_Q_of_nat; lra. }
    rewrite heq_n.
    exists m', (WV :: v), (a * (1#2)), (b * (1#2)); split; [exact (BScan_T hS) | exact hm'].
  - (* odd_c *)
    split; [| intro H; discriminate H].
    intros _ k _ hO hk.
    destruct (hO eq_refl) as [n ->].
    pose proof (zPrU_MS_W hI) as hWu.
    rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    assert (hq3 : Q_of_nat 3 < Q_of_nat (1 + n * 2)) by (rewrite Q_of_nat_3; nra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    assert (hpow_ge : (2 <= 2 ^ (1 + r))%nat) by (rewrite zP2; pose proof (zPp r); lia).
    destruct (z0F (n - 1)%nat) as [[m hm] | [m hm]].
    + assert (hk_eq : (1 + n * 2 = 3 + m * 4)%nat) by lia.
      assert (hm_pow : (m * 2 <= m * 2 ^ (1 + r))%nat) by (apply Nat.mul_le_mono_l; exact hpow_ge).
      apply (proj1 (Q_of_nat_le _ _)) in hm_pow.
      assert (h_ex : exists n0, (1 + m * 2 ^ (1 + r) = 1 + n0 * 2)%nat)
        by (exists (m * 2 ^ r)%nat; rewrite zP2; lia).
      destruct (proj2 IHhI eq_refl (1 + m * 2 ^ (1 + r))%nat h_ex)
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk;
        rewrite (Q_of_nat_add 3 (m * 4)) in hk;
        replace (m * 4)%nat with ((m * 2) * 2)%nat in hk by lia;
        rewrite (Q_of_nat_mul (m * 2) 2) in hk;
        rewrite (Q_of_nat_add 1 (m * 2 ^ (1 + r)));
        rewrite Q_of_nat_1, Q_of_nat_2, Q_of_nat_3 in *; nra. }
      rewrite hk_eq.
      exists m', (WK :: (zR r WV ++ v)), ((2 + a * 2) * zIv r), (b * 2 * zIv r);
        split; [exact (BScan_odd_chain0 r hSub) | exact hm'].
    + assert (hk_eq : (1 + n * 2 = 5 + m * 4)%nat) by lia.
      assert (hm_pow : (m * 2 <= m * 2 ^ (1 + r))%nat) by (apply Nat.mul_le_mono_l; exact hpow_ge).
      apply (proj1 (Q_of_nat_le _ _)) in hm_pow.
      assert (h_ex : exists n0, (1 + m * 2 ^ (1 + r) = 1 + n0 * 2)%nat)
        by (exists (m * 2 ^ r)%nat; rewrite zP2; lia).
      destruct (proj2 IHhI eq_refl (1 + m * 2 ^ (1 + r))%nat h_ex)
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk;
        rewrite (Q_of_nat_add 5 (m * 4)) in hk;
        replace (m * 4)%nat with ((m * 2) * 2)%nat in hk by lia;
        rewrite (Q_of_nat_mul (m * 2) 2) in hk;
        rewrite (Q_of_nat_add 1 (m * 2 ^ (1 + r)));
        rewrite Q_of_nat_1, Q_of_nat_2, Q_of_nat_5 in *; nra. }
      rewrite hk_eq.
      exists m', (WQ :: (zR r WV ++ v)), (1 + (2 + a * 2) * zIv r), (b * 2 * zIv r);
        split; [exact (BScan_odd_chain1 r hSub) | exact hm'].
  - (* short_K *)
    split; [| intro H; discriminate H].
    intros _ k hE _ hk.
    destruct (hE eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    destruct (z0F n) as [[m ->] | [m ->]].
    + assert (hk_eq : (m * 2 * 2 = 4 + (m - 1) * 4)%nat) by lia.
      destruct (proj1 IHhI (or_introl eq_refl) ((m - 1) * 2)%nat
        (fun _ => ex_intro _ (m - 1)%nat eq_refl) (fun H => ltac:(discriminate H)))
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk; push_Q_of_nat; lra. }
      rewrite hk_eq.
      exists m', (WQ :: v), ((7#2) + a * 2), (b * 2); split; [exact (BScan_short10 hSub) | exact hm'].
    + assert (hk_eq : ((1 + m * 2) * 2 = 2 + m * 4)%nat) by lia.
      destruct (proj1 IHhI (or_introl eq_refl) (m * 2)%nat
        (fun _ => ex_intro _ m eq_refl) (fun H => ltac:(discriminate H)))
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk; push_Q_of_nat; lra. }
      rewrite hk_eq.
      exists m', (WK :: v), ((5#2) + a * 2), (b * 2); split; [exact (BScan_short00 hSub) | exact hm'].
  - (* even_c *)
    split; [| intro H; discriminate H].
    intros _ k hE _ hk.
    destruct (hE eq_refl) as [n ->].
    pose proof (zPrU_MS_W hI) as hWu.
    cbn [z0W] in hk; rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    assert (hq5 : Q_of_nat 5 < Q_of_nat (n * 2)) by (rewrite Q_of_nat_5; nra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq5.
    assert (hk_eq : (n * 2 = 6 + (n - 3) * 2)%nat) by lia.
    assert (hpow_ge : (2 <= 2 ^ (1 + r))%nat) by (rewrite zP2; pose proof (zPp r); lia).
    assert (hm_pow : ((1 + (n - 3) * 2) * 2 <= (1 + (n - 3) * 2) * 2 ^ (1 + r))%nat)
      by (apply Nat.mul_le_mono_l; exact hpow_ge).
    apply (proj1 (Q_of_nat_le _ _)) in hm_pow.
    assert (h_ex : exists n0, (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r) = 1 + n0 * 2)%nat)
      by (exists ((1 + (n - 3) * 2) * 2 ^ r)%nat; rewrite zP2; lia).
    destruct (proj2 IHhI eq_refl (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r))%nat h_ex)
      as [m' [v [a [b [hSub hm']]]]].
    { rewrite hk_eq in hk;
      rewrite (Q_of_nat_add 6 ((n - 3) * 2)) in hk;
      rewrite (Q_of_nat_mul (1 + (n - 3) * 2) 2) in hm_pow;
      rewrite (Q_of_nat_add 1 ((n - 3) * 2)) in hm_pow;
      rewrite (Q_of_nat_add 1 ((1 + (n - 3) * 2) * 2 ^ (1 + r)));
      rewrite Q_of_nat_1, Q_of_nat_2, Q_of_nat_6 in *; nra. }
    rewrite hk_eq.
    exists m', (zR (1 + r) WV ++ v), (1 + (1 + a) * (1#2) * zIv r), (b * (1#2) * zIv r);
      split; [exact (BScan_even_chain r hSub) | exact hm'].
  - (* shift_K *)
    split; [intros [H | H]; discriminate H |].
    intros _ k [n ->] hk.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IHhI (or_introl eq_refl) ((n * 2) * 2)%nat
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) (fun H => ltac:(discriminate H)))
      as [m' [v [a [b [hSub hm']]]]].
    { push_Q_of_nat; lra. }
    exists m', (WV :: v), (a * (1#2)), ((1#4) + b * (1#2)); split; [exact (BScan_shift_pair0 hSub) | exact hm'].
  - (* shift_c *)
    split; [intros [H | H]; discriminate H |].
    intros _ k [n ->] hk.
    pose proof (zPrU_MS_W hI) as hWu.
    cbn [z0W] in hk; rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    assert (hq6 : Q_of_nat 6 < Q_of_nat (1 + n * 2)) by (rewrite Q_of_nat_6; nra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq6.
    assert (hpow_ge : (4 <= 2 ^ (2 + r))%nat)
      by (change (2 + r)%nat with (1 + (1 + r))%nat; rewrite !zP2; pose proof (zPp r); lia).
    destruct (z0F (n - 1)%nat) as [[m hm] | [m hm]].
    + assert (hk_eq : (1 + n * 2 = 3 + m * 4)%nat) by lia.
      assert (hm_pow : (m * 4 <= m * 2 ^ (2 + r))%nat) by (apply Nat.mul_le_mono_l; exact hpow_ge).
      apply (proj1 (Q_of_nat_le _ _)) in hm_pow.
      assert (h_ex : exists n0, (1 + m * 2 ^ (2 + r) = 1 + n0 * 2)%nat)
        by (exists (m * 2 ^ (1 + r))%nat; change (2 + r)%nat with (1 + (1 + r))%nat; rewrite zP2; lia).
      destruct (proj2 IHhI eq_refl (1 + m * 2 ^ (2 + r))%nat h_ex)
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk;
        rewrite (Q_of_nat_add 3 (m * 4)) in hk;
        rewrite (Q_of_nat_add 1 (m * 2 ^ (2 + r)));
        rewrite Q_of_nat_1, Q_of_nat_3 in *; nra. }
      rewrite hk_eq.
      exists m', (WK :: (zR (1 + r) WV ++ v)), ((1 + a) * zIv r), (b * zIv r);
        split; [exact (BScan_shift_chain0 r hSub) | exact hm'].
    + assert (hk_eq : (1 + n * 2 = 5 + m * 4)%nat) by lia.
      assert (hm_pow : (m * 4 <= m * 2 ^ (2 + r))%nat) by (apply Nat.mul_le_mono_l; exact hpow_ge).
      apply (proj1 (Q_of_nat_le _ _)) in hm_pow.
      assert (h_ex : exists n0, (1 + m * 2 ^ (2 + r) = 1 + n0 * 2)%nat)
        by (exists (m * 2 ^ (1 + r))%nat; change (2 + r)%nat with (1 + (1 + r))%nat; rewrite zP2; lia).
      destruct (proj2 IHhI eq_refl (1 + m * 2 ^ (2 + r))%nat h_ex)
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk;
        rewrite (Q_of_nat_add 5 (m * 4)) in hk;
        rewrite (Q_of_nat_add 1 (m * 2 ^ (2 + r)));
        rewrite Q_of_nat_1, Q_of_nat_5 in *; nra. }
      rewrite hk_eq.
      exists m', (WQ :: (zR (1 + r) WV ++ v)), (1 + (1 + a) * zIv r), (b * zIv r);
        split; [exact (BScan_shift_chain1 r hSub) | exact hm'].
  - (* short_Q *)
    split; [| intro H; discriminate H].
    intros _ k hE _ hk.
    destruct (hE eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    destruct (z0F n) as [[m ->] | [m ->]].
    + assert (hk_eq : (m * 2 * 2 = 4 + (m - 1) * 4)%nat) by lia.
      destruct (proj1 IHhI (or_intror eq_refl) (1 + (m - 1) * 2)%nat
        (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ (m - 1)%nat eq_refl))
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk; push_Q_of_nat; lra. }
      rewrite hk_eq.
      exists m', (WQ :: v), ((5#2) + a * 2), (b * 2); split; [exact (BScan_short11 hSub) | exact hm'].
    + assert (hk_eq : ((1 + m * 2) * 2 = 2 + m * 4)%nat) by lia.
      destruct (proj1 IHhI (or_intror eq_refl) (1 + m * 2)%nat
        (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ m eq_refl))
        as [m' [v [a [b [hSub hm']]]]].
      { rewrite hk_eq in hk; push_Q_of_nat; lra. }
      rewrite hk_eq.
      exists m', (WK :: v), ((3#2) + a * 2), (b * 2); split; [exact (BScan_short01 hSub) | exact hm'].
  - (* shift_Q *)
    split; [intros [H | H]; discriminate H |].
    intros _ k [n ->] hk.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IHhI (or_intror eq_refl) (1 + (n * 2) * 2)%nat
      (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ (n * 2)%nat eq_refl))
      as [m' [v [a [b [hSub hm']]]]].
    { push_Q_of_nat; lra. }
    exists m', (WV :: v), (a * (1#2)), ((1#2) + b * (1#2)); split; [exact (BScan_shift_pair1 hSub) | exact hm'].
  - (* pair0_E *)
    split; [| intro H; discriminate H].
    intros _ k hE _ hk.
    destruct (hE eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    assert (hk_eq : (n * 2 = 1 + (n * 2 - 1))%nat) by lia.
    destruct (proj1 IHhI (or_introl eq_refl) ((n * 2 - 1) * 2)%nat
      (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl) (fun H => ltac:(discriminate H)))
      as [m' [v [a [b [hSub hm']]]]].
    { rewrite hk_eq in hk;
      rewrite (Q_of_nat_add 1 (n * 2 - 1)) in hk;
      rewrite (Q_of_nat_mul (n * 2 - 1) 2);
      rewrite Q_of_nat_1, Q_of_nat_2 in *; lra. }
    rewrite hk_eq.
    exists m', (WV :: v), (a * (1#2)), ((1#4) + b * (1#2)); split; [exact (BScan_pair0 hSub) | exact hm'].
  - (* pair0_O *)
    split; [| intro H; discriminate H].
    intros _ k _ hO hk.
    destruct (hO eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IHhI (or_introl eq_refl) ((n * 2) * 2)%nat
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) (fun H => ltac:(discriminate H)))
      as [m' [v [a [b [hSub hm']]]]].
    { push_Q_of_nat; lra. }
    exists m', (WV :: v), (a * (1#2)), ((1#4) + b * (1#2)); split; [exact (BScan_pair0 hSub) | exact hm'].
  - (* pair1_E *)
    split; [| intro H; discriminate H].
    intros _ k hE _ hk.
    destruct (hE eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hq3 : Q_of_nat 3 < Q_of_nat (n * 2)) by (rewrite Q_of_nat_3; lra).
    apply (proj2 (Q_of_nat_lt _ _)) in hq3.
    assert (hk_eq : (n * 2 = 1 + (n * 2 - 1))%nat) by lia.
    destruct (proj1 IHhI (or_intror eq_refl) (1 + (n * 2 - 1) * 2)%nat
      (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl))
      as [m' [v [a [b [hSub hm']]]]].
    { rewrite hk_eq in hk;
      rewrite (Q_of_nat_add 1 (n * 2 - 1)) in hk;
      rewrite (Q_of_nat_add 1 ((n * 2 - 1) * 2));
      rewrite (Q_of_nat_mul (n * 2 - 1) 2);
      rewrite Q_of_nat_1, Q_of_nat_2 in *; lra. }
    rewrite hk_eq.
    exists m', (WV :: v), (a * (1#2)), ((1#2) + b * (1#2)); split; [exact (BScan_pair1 hSub) | exact hm'].
  - (* pair1_O *)
    split; [| intro H; discriminate H].
    intros _ k _ hO hk.
    destruct (hO eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IHhI (or_intror eq_refl) (1 + (n * 2) * 2)%nat
      (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ (n * 2)%nat eq_refl))
      as [m' [v [a [b [hSub hm']]]]].
    { push_Q_of_nat; lra. }
    exists m', (WV :: v), (a * (1#2)), ((1#2) + b * (1#2)); split; [exact (BScan_pair1 hSub) | exact hm'].
Qed.

Lemma zDg_zero_Z {A H : nat} {w : zW} (h : zDg A H w) (h0 : A = 0%nat) :
  z0Z w == Q_of_nat (2 ^ H) - 1.
Proof.
  induction h as [| A1 H1 u1 _ IH | A1 H1 u1 _ _].
  - cbn [z0Z Nat.pow]; rewrite Q_of_nat_1; lra.
  - assert (hA1 : A1 = 0%nat) by lia.
    rewrite Q_of_nat_pow2; cbn [z0Z]; rewrite (IH hA1); ring.
  - lia.
Qed.

Lemma zPiece3 {n_mid : nat} (hn : (2 <= n_mid)%nat) :
  exists m_end d1_tok a_t b_t,
    BScan false (n_mid * 4)%nat [WK; WQ; WQ; WQ; WQ; WK] (m_end * 8)%nat [WQ; d1_tok; WV; WV] a_t b_t /\
    z11 [WQ; d1_tok; WV; WV] == 1 /\
    z0W [WQ; d1_tok; WV; WV] <= 15#4 /\
    z0L [WQ; d1_tok; WV; WV] = true /\
    a_t - b_t <= 6 /\
    b_t - a_t <= 0.
Proof.
  destruct (z0F (n_mid - 1)%nat) as [[m1 hm1] | [m1 hm1]].
  - assert (hk0 : (n_mid * 4 = 4 + ((m1 - 1) * 2 + 2) * 4)%nat) by lia.
    assert (hk1 : (((m1 - 1) * 2 + 2) * 2 = 4 + (m1 - 1) * 4)%nat) by lia.
    pose proof (BScan_pair0 (BScan_nil (((m1 - 1) * 2) * 2 * 2)%nat)) as hB0.
    replace (((m1 - 1) * 2) * 2 * 2)%nat with ((m1 - 1) * 8)%nat in hB0 by lia.
    pose proof (BScan_pair1 hB0) as hB1.
    pose proof (BScan_short11 hB1) as hB2.
    rewrite <- hk1 in hB2.
    pose proof (BScan_short10 hB2) as hB3.
    rewrite <- hk0 in hB3.
    eexists (m1 - 1)%nat, WQ, _, _;
      split; [exact hB3 | split; [cbn; lra | split; [cbn; lra | split; [reflexivity | split; lra]]]].
  - assert (hk0 : (n_mid * 4 = 4 + (1 + m1 * 2) * 4)%nat) by lia.
    assert (hk1 : ((1 + m1 * 2) * 2 = 2 + m1 * 4)%nat) by lia.
    pose proof (BScan_pair0 (BScan_nil ((m1 * 2) * 2 * 2)%nat)) as hB0.
    replace ((m1 * 2) * 2 * 2)%nat with (m1 * 8)%nat in hB0 by lia.
    pose proof (BScan_pair1 hB0) as hB1.
    pose proof (BScan_short01 hB1) as hB2.
    rewrite <- hk1 in hB2.
    pose proof (BScan_short10 hB2) as hB3.
    rewrite <- hk0 in hB3.
    eexists m1, WK, _, _;
      split; [exact hB3 | split; [cbn; lra | split; [cbn; lra | split; [reflexivity | split; lra]]]].
Qed.

Lemma z1l {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h1 : BScan s k u k' v a b) :
  forall {r r' : side}, BRIncs false k' r r' -> BRIncs s k (zTs u r) (zTs v r').
Proof.
  induction h1; intros r0 r' h2; cbn [zTs].
  - exact h2.
  - exact (BRIncs_T (IHh1 _ _ h2)).
  - exact (BRIncs_pair0 (IHh1 _ _ h2)).
  - exact (BRIncs_pair1 (IHh1 _ _ h2)).
  - exact (BRIncs_short00 (IHh1 _ _ h2)).
  - exact (BRIncs_short01 (IHh1 _ _ h2)).
  - exact (BRIncs_short10 (IHh1 _ _ h2)).
  - exact (BRIncs_short11 (IHh1 _ _ h2)).
  - assert (h_in : zTs (zQK r (WV :: u)) r0 = zTs (zQK r [WV]) (zTs u r0))
      by (rewrite <- z0S, <- zQK_append; reflexivity).
    rewrite h_in, z0S; cbn [zTs].
    exact (BRIncs_odd_chain0 r (IHh1 _ _ h2)).
  - assert (h_in : zTs (zQK r (WV :: u)) r0 = zTs (zQK r [WV]) (zTs u r0))
      by (rewrite <- z0S, <- zQK_append; reflexivity).
    rewrite h_in, z0S; cbn [zTs].
    exact (BRIncs_odd_chain1 r (IHh1 _ _ h2)).
  - assert (h_in : zTs (zQK r (WV :: u)) r0 = zTs (zQK r [WV]) (zTs u r0))
      by (rewrite <- z0S, <- zQK_append; reflexivity).
    rewrite h_in.
    change (t *> zTs (zR r WV ++ v) r') with (zTs (zR (1 + r) WV ++ v) r').
    rewrite z0S.
    exact (BRIncs_even_chain r (IHh1 _ _ h2)).
  - exact (BRIncs_shift_pair0 (IHh1 _ _ h2)).
  - exact (BRIncs_shift_pair1 (IHh1 _ _ h2)).
  - assert (h_in : zTs (zQK r (WV :: u)) r0 = zTs (zQK r [WV]) (zTs u r0))
      by (rewrite <- z0S, <- zQK_append; reflexivity).
    rewrite h_in, z0S; cbn [zTs].
    exact (BRIncs_shift_chain0 r (IHh1 _ _ h2)).
  - assert (h_in : zTs (zQK r (WV :: u)) r0 = zTs (zQK r [WV]) (zTs u r0))
      by (rewrite <- z0S, <- zQK_append; reflexivity).
    rewrite h_in, z0S; cbn [zTs].
    exact (BRIncs_shift_chain1 r (IHh1 _ _ h2)).
Qed.


(* ---------- Section 7D: P33 prefix, BGood, BStep, z1N, finite rounds executor ---------- *)

Lemma Q_of_N_to_nat (x : N) : Q_of_nat (N.to_nat x) = inject_Z (Z.of_N x).
Proof. unfold Q_of_nat; f_equal; lia. Qed.

Fixpoint N_pow2 (k : nat) : N :=
  match k with
  | O => 1%N
  | S k' => (2 * N_pow2 k')%N
  end.

Lemma N_to_nat_pow2 (k : nat) : N.to_nat (N_pow2 k) = (2 ^ k)%nat.
Proof.
  induction k as [| k IH]; [reflexivity |].
  cbn [N_pow2 Nat.pow]; lia.
Qed.

Lemma Q_of_nat_pow2_eq (k : nat) : Q_of_nat (2 ^ k) == inject_Z (Z.of_N (N_pow2 k)).
Proof.
  rewrite <- N_to_nat_pow2, Q_of_N_to_nat; reflexivity.
Qed.

Definition zP33 : zW :=
  [WV; WV; WQ; WV; WV; WQ; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV] ++ [WK].
Definition zOut33 : zW :=
  [WV; WQ; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV; WK; WV; WV; WK] ++ [WV].
Definition zTail8 : zW := [WQ; WQ; WK; WK; WQ; WQ; WQ; WQ].

Lemma zDg_tail8 : zDg 243%nat 8%nat zTail8.
Proof.
  exact (zDg_one (zDg_one (zDg_zero (zDg_zero (zDg_one (zDg_one (zDg_one (zDg_one zDg_nil)))))))).
Qed.

Lemma zP3_11 (m k_in k_out : N) {r r' : side}
  (h1 : (k_in = 4 + m * 2)%N) (h2 : (k_out = 1 + m * 4)%N)
  (h : BRIncs false (N.to_nat k_out) r r') :
  BRIncs false (N.to_nat k_in) (t *> (t *> (d1 *> r))) (t *> (d1 *> (t *> r'))).
Proof.
  replace (N.to_nat k_out) with (1 + (N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair1 h) as h_sp.
  pose proof (BRIncs_odd_chain1 0%nat h_sp) as h_oc.
  cbn [zQK repeat zTs] in h_oc.
  replace (5 + N.to_nat m * 4)%nat with (1 + (2 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace (N.to_nat k_in) with (2 + (2 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_01 (m k_in k_out : N) {r r' : side}
  (h1 : (k_in = 3 + m * 2)%N) (h2 : (k_out = 1 + m * 4)%N)
  (h : BRIncs false (N.to_nat k_out) r r') :
  BRIncs false (N.to_nat k_in) (t *> (t *> (d1 *> r))) (t *> (d0 *> (t *> r'))).
Proof.
  replace (N.to_nat k_out) with (1 + (N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair1 h) as h_sp.
  pose proof (BRIncs_odd_chain0 0%nat h_sp) as h_oc.
  cbn [zQK repeat zTs] in h_oc.
  replace (3 + N.to_nat m * 4)%nat with (1 + (1 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace (N.to_nat k_in) with (2 + (1 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_00 (m k_in k_out : N) {r r' : side}
  (h1 : (k_in = 3 + m * 2)%N) (h2 : (k_out = m * 4)%N)
  (h : BRIncs false (N.to_nat k_out) r r') :
  BRIncs false (N.to_nat k_in) (t *> (t *> (d0 *> r))) (t *> (d0 *> (t *> r'))).
Proof.
  replace (N.to_nat k_out) with ((N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair0 h) as h_sp.
  pose proof (BRIncs_odd_chain0 0%nat h_sp) as h_oc.
  cbn [zQK repeat zTs] in h_oc.
  replace (3 + N.to_nat m * 4)%nat with (1 + (1 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace (N.to_nat k_in) with (2 + (1 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_10 (m k_in k_out : N) {r r' : side}
  (h1 : (k_in = 4 + m * 2)%N) (h2 : (k_out = m * 4)%N)
  (h : BRIncs false (N.to_nat k_out) r r') :
  BRIncs false (N.to_nat k_in) (t *> (t *> (d0 *> r))) (t *> (d1 *> (t *> r'))).
Proof.
  replace (N.to_nat k_out) with ((N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair0 h) as h_sp.
  pose proof (BRIncs_odd_chain1 0%nat h_sp) as h_oc.
  cbn [zQK repeat zTs] in h_oc.
  replace (5 + N.to_nat m * 4)%nat with (1 + (2 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace (N.to_nat k_in) with (2 + (2 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zBRIncs_P33 {r r' : side} (h : BRIncs false (N.to_nat 249044%N) r r') :
  BRIncs false 128%nat (zTs zP33 r) (zTs zOut33 r').
Proof.
  change 128%nat with (N.to_nat 128%N).
  unfold zP33, zOut33; cbn [app zTs].
  exact
    (zP3_11 62%N 128%N 249%N eq_refl eq_refl
    (zP3_01 123%N 249%N 493%N eq_refl eq_refl
    (zP3_00 245%N 493%N 980%N eq_refl eq_refl
    (zP3_10 488%N 980%N 1952%N eq_refl eq_refl
    (zP3_11 974%N 1952%N 3897%N eq_refl eq_refl
    (zP3_01 1947%N 3897%N 7789%N eq_refl eq_refl
    (zP3_00 3893%N 7789%N 15572%N eq_refl eq_refl
    (zP3_10 7784%N 15572%N 31136%N eq_refl eq_refl
    (zP3_11 15566%N 31136%N 62265%N eq_refl eq_refl
    (zP3_01 31131%N 62265%N 124525%N eq_refl eq_refl
    (zP3_00 62261%N 124525%N 249044%N eq_refl eq_refl h))))))))))).
Qed.

Inductive BGood : zW -> Prop :=
  | BGood_intro (H : nat) (u : zW) (A : nat) (hi8 : zW) :
      zDg A H hi8 ->
      z11 u * Q_of_nat (2 ^ H) == 128 ->
      z11 u <= 1#16 ->
      (exists w, u = WV :: WV :: (w ++ [WV])) ->
      z0L u = true ->
      (exists w, hi8 = WQ :: WK :: w) ->
      z0W u <= 74#5 ->
      z11 u * z0Z hi8 <= 1273#10 ->
      BGood (u ++ (hi8 ++ zTail8)).

Inductive BStep : zW -> zW -> Prop :=
  | BStep_intro (orig : zW) (n : nat) (v : zW) (a b : Rat) (J : nat) (ds : zW) :
      BScan false (N.to_nat 249044%N) (orig ++ [WK]) (n * 2)%nat v a b ->
      zDg (1 + n)%nat J ds ->
      BStep orig ([WV; WV; WK; WV] ++ v ++ ds).

Lemma z1N {orig : zW} (hG : BGood orig) :
  exists out, BStep orig out /\ BGood out.
Proof.
  destruct hG as [H u A hi8 hDig hHeight hU11 [wu hwu] hLu [w0 hw0] hWu_max hZ_max].
  pose proof (proj2 (proj2 (proj2 (zWn u)))) as hWu_nonneg.
  pose proof (zSp u) as hSu.
  assert (hPrU : zPrU ME u) by (rewrite hwu; exact (zPrU_ME_VV wu)).
  assert (hk_in : 16 * z0W u < Q_of_nat (N.to_nat 249044%N) - 3).
  { rewrite (Q_of_N_to_nat 249044%N); change (inject_Z (Z.of_N 249044%N)) with 249044; lra. }
  assert (h249044_even : ME = ME -> exists n : nat, N.to_nat 249044%N = (n * 2)%nat)
    by (intros _; exists (N.to_nat 124522%N); lia).
  destruct (proj1 (zPrU_bscan hPrU) (or_introl eq_refl) (N.to_nat 249044%N)
    h249044_even (fun Hc => ltac:(discriminate Hc)) hk_in)
    as [m1 [v1 [a1 [b1 [hB1 hm1]]]]].
  pose proof (zSp v1) as hSv1.
  pose proof (proj2 (proj2 (proj2 (zWn v1)))) as hWv1_nonneg.
  assert (h11_v1 : z11 v1 <= (1#8) * z11 u)
    by (pose proof (z1p_z0L hB1 hLu) as h; cbn [zSwt] in h; lra).
  destruct (proj1 (z1j hB1) eq_refl) as [hW_v1 [hAB_1 hBA_1]].
  pose proof (z1i hB1) as hBud1.
  rewrite (Q_of_N_to_nat 249044%N) in hBud1; change (inject_Z (Z.of_N 249044%N)) with 249044 in hBud1.
  rewrite (Q_of_nat_add 1 m1), Q_of_nat_1 in hBud1.
  subst hi8.
  destruct (zD1 hDig) as [A1 [H1 [hD1 [hA1 hH1]]]].
  destruct (zD0 hD1) as [A0 [H0 [hD0 [hA0 hH0]]]].
  destruct (zDw hD0) as [hDw0_1 [hDw0_2 hDw0_3]].
  pose proof (zSp w0) as hSw0.
  pose proof (proj1 (proj2 (zWn w0))) as hZw0_nonneg.
  assert (hPowH : Q_of_nat (2 ^ H) == 4 * z11 w0).
  { rewrite hH1, hH0, (Q_of_nat_pow2 (1 + H0)), (Q_of_nat_pow2 H0); lra. }
  assert (hZ_hi8 : z0Z (WQ :: WK :: w0) == 2 + 4 * z0Z w0) by (cbn [z0Z]; ring).
  assert (hA0_pos : (0 < A0)%nat).
  { destruct (Nat.eq_0_gt_0_cases A0) as [hA0_0 | hpos]; [| exact hpos].
    exfalso; pose proof (zDg_zero_Z hD0 hA0_0) as hZw0_0.
    rewrite <- hDw0_1 in hZw0_0.
    assert (h_prod : z11 u * z0Z (WQ :: WK :: w0) + 2 * z11 u == z11 u * (4 * z11 w0))
      by (rewrite hZ_hi8, hZw0_0; ring).
    assert (h_pow_u : z11 u * Q_of_nat (2 ^ H) == z11 u * (4 * z11 w0))
      by (rewrite hPowH; ring).
    lra. }
  pose proof (zDg_pos_z0L hD0 hA0_pos) as hLw0.
  assert (hY_w0qqk : z0Y (w0 ++ [WQ; WQ; WK]) == z0Y w0 + 7 * z11 w0) by (rewrite z13; cbn [z0Y]; ring).
  assert (hZ_w0qqk : z0Z (w0 ++ [WQ; WQ; WK]) == z0Z w0 + 4 * z11 w0) by (rewrite z14; cbn [z0Z]; ring).
  assert (hScan_cond : (z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2 < Q_of_nat (m1 * 2)).
  { assert (h_yw0 : z0Y w0 == z11 w0 - 1) by lra.
    rewrite (Q_of_nat_mul m1 2), Q_of_nat_2.
    pose proof (Q_of_nat_nonneg m1) as hm1_nn.
    assert (hm1_ub : (Q_of_nat m1 * 2) * z11 v1 <= (Q_of_nat m1 * 2) * ((1#8) * z11 u))
      by (clear - hm1_nn h11_v1; nra).
    assert (h_bud1_exp : (1 + Q_of_nat m1 - 3) * z11 v1 == (1#2) * ((Q_of_nat m1 * 2) * z11 v1) - 2 * z11 v1) by ring.
    assert (h_lhs_u : z11 u * ((z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2) ==
        6 * (z11 u * (4 * z11 w0)) + (1#2) * (z11 u * z0Z (WQ :: WK :: w0)) - 3 * z11 u)
      by (rewrite hY_w0qqk, hZ_w0qqk, h_yw0, hZ_hi8; ring).
    assert (h_pow_u : z11 u * Q_of_nat (2 ^ H) == z11 u * (4 * z11 w0)) by (rewrite hPowH; ring).
    assert (h_rhs_u : (Q_of_nat m1 * 2) * ((1#8) * z11 u) == (1#8) * (z11 u * (Q_of_nat m1 * 2))) by ring.
    assert (h_lt_u : z11 u * ((z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2) < z11 u * (Q_of_nat m1 * 2))
      by lra.
    clear - hSu h_lt_u; nra. }
  destruct (z1a (w0 ++ [WQ; WQ; WK]) m1 hScan_cond) as [b2 [y [l2 [hS2 _]]]].
  destruct (zScan_qqk hS2 w0 eq_refl) as [_ [h11_y_fn [[n_mid hb2_eq] [y0 hy0]]]].
  subst b2.
  assert (h11_y : z11 (WV :: y) <= (1#64) * Q_of_nat (2 ^ H)).
  { pose proof (h11_y_fn hLw0) as hy.
    assert (h11_qqk : z11 (w0 ++ [WQ; WQ; WK]) == 8 * z11 w0) by (rewrite z16; cbn [z11]; ring).
    cbn [z11]; lra. }
  destruct (zHi_bscan hS2 hD0) as [a2 [b2_r [hB2 [hY_vy [hAB_2 hBA_2]]]]].
  assert (hW_vy : z0W (WV :: y) <= (11#32) * z0Z (WQ :: WK :: w0))
    by (pose proof (proj2 (zWY (WV :: y))); lra).
  destruct (z1k hB1 hB2) as [a12 [b12 [hB12 [ha12 hb12]]]].
  assert (h11_v12 : z11 (v1 ++ WV :: y) <= 1#4).
  { rewrite z16; pose proof (zSp (WV :: y)) as hS_vy.
    assert (h_prod : z11 v1 * z11 (WV :: y) <= ((1#8) * z11 u) * ((1#64) * Q_of_nat (2 ^ H)))
      by (clear - h11_v1 h11_y hSv1 hS_vy; nra).
    assert (h_eq : ((1#8) * z11 u) * ((1#64) * Q_of_nat (2 ^ H)) == (1#512) * (z11 u * Q_of_nat (2 ^ H))) by ring.
    lra. }
  pose proof (zSp (v1 ++ WV :: y)) as hSv12.
  pose proof (z1i hB12) as hBud12.
  rewrite (Q_of_N_to_nat 249044%N), (Q_of_nat_mul n_mid 4), Q_of_nat_4 in hBud12.
  change (inject_Z (Z.of_N 249044%N)) with 249044 in hBud12.
  pose proof (proj1 (proj2 (zWn (WQ :: WK :: w0)))) as hZ_hi8_nn.
  assert (hp1_ab : z11 v1 * (a2 - b2_r) <= (7#64) * (z11 u * z0Z (WQ :: WK :: w0))).
  { assert (hp : z11 v1 * (a2 - b2_r) <= ((1#8) * z11 u) * ((7#8) * z0Z (WQ :: WK :: w0)))
      by (clear - h11_v1 hAB_2 hSv1 hZ_hi8_nn; nra).
    assert (heq : ((1#8) * z11 u) * ((7#8) * z0Z (WQ :: WK :: w0)) == (7#64) * (z11 u * z0Z (WQ :: WK :: w0))) by ring.
    lra. }
  assert (h_ab12 : a12 - b12 <= (64#11) * z0W u + (7#64) * (z11 u * z0Z (WQ :: WK :: w0))).
  { assert (h_diff : a12 - b12 == (a1 - b1) + z11 v1 * (a2 - b2_r)) by (rewrite ha12, hb12; ring).
    lra. }
  assert (hn_mid2 : (2 <= n_mid)%nat).
  { destruct (Nat.le_gt_cases 2 n_mid) as [hle | hlt]; [exact hle |].
    exfalso; assert (hn1 : (n_mid <= 1)%nat) by lia.
    apply (proj1 (Q_of_nat_le _ _)) in hn1; rewrite Q_of_nat_1 in hn1.
    assert (h_ub : (Q_of_nat n_mid * 4 - 3) * z11 (v1 ++ WV :: y) <= 1)
      by (clear - hn1 h11_v12 hSv12; nra).
    lra. }
  destruct (zPiece3 hn_mid2) as [m_end [d1_tok [a3 [b3 [hB3 [h11_p3 [hW_p3 [hL_p3 [hAB_3 hBA_3]]]]]]]]].
  destruct (z1k hB12 hB3) as [a [b [hB_all [ha_all hb_all]]]].
  set (v := (v1 ++ WV :: y) ++ [WQ; d1_tok; WV; WV]).
  assert (h11_v : z11 v == z11 (v1 ++ WV :: y)) by (unfold v; rewrite z16, h11_p3; ring).
  pose proof (zSp v) as hSv.
  assert (h11_v_le : z11 v <= 1#4) by lra.
  assert (hW_v : z0W v <= (66#19) * z0W u + (11#256) * (z11 u * z0Z (WQ :: WK :: w0)) + (15#16)).
  { unfold v; rewrite !z13W.
    pose proof (proj2 (proj2 (proj2 (zWn [WQ; d1_tok; WV; WV])))) as hW_p3_nn.
    pose proof (proj2 (proj2 (proj2 (zWn (WV :: y))))) as hW_vy_nn.
    assert (hp1 : z11 v1 * z0W (WV :: y) <= ((1#8) * z11 u) * ((11#32) * z0Z (WQ :: WK :: w0)))
      by (clear - h11_v1 hW_vy hSv1 hW_vy_nn; nra).
    assert (hp2 : z11 (v1 ++ WV :: y) * z0W [WQ; d1_tok; WV; WV] <= (1#4) * (15#4))
      by (clear - h11_v12 hW_p3 hSv12 hW_p3_nn; nra).
    assert (hp1_eq : ((1#8) * z11 u) * ((11#32) * z0Z (WQ :: WK :: w0)) == (11#256) * (z11 u * z0Z (WQ :: WK :: w0))) by ring.
    lra. }
  assert (hAB : a - b <= 508#5).
  { assert (hp2 : z11 (v1 ++ WV :: y) * (a3 - b3) <= (1#4) * 6)
      by (clear - h11_v12 hAB_3 hSv12; nra).
    assert (h_diff : a - b == (a12 - b12) + z11 (v1 ++ WV :: y) * (a3 - b3))
      by (rewrite ha_all, hb_all; ring).
    lra. }
  assert (hBA : b - a <= 8).
  { assert (hp1 : z11 v1 * (b2_r - a2) <= z11 v1) by (clear - hSv1 hBA_2; nra).
    assert (hp2 : z11 (v1 ++ WV :: y) * (b3 - a3) <= 0) by (clear - hSv12 hBA_3; nra).
    assert (h_diff : b - a == (b1 - a1) + z11 v1 * (b2_r - a2) + z11 (v1 ++ WV :: y) * (b3 - a3))
      by (rewrite ha_all, hb_all, ha12, hb12; ring).
    lra. }
  assert (hY_v_lt : z0Y v < Q_of_nat (2 ^ 17)).
  { pose proof (proj1 (zWY v)); rewrite (Q_of_nat_pow2_eq 17).
    change (inject_Z (Z.of_N (N_pow2 17))) with 131072; lra. }
  destruct (z1B v 17%nat hY_v_lt) as [J hHn].
  pose proof (z1x v 17%nat J hHn) as hUnit.
  rewrite (Q_of_nat_pow2_eq 17) in hUnit; change (inject_Z (Z.of_N (N_pow2 17))) with 131072 in hUnit.
  assert (hJ10 : (10 <= J)%nat).
  { destruct (Nat.le_gt_cases 10 J) as [hle | hlt]; [exact hle |].
    exfalso; assert (hJ9 : (J <= 9)%nat) by lia.
    assert (hpow9 : (2 ^ J <= 2 ^ 9)%nat) by (apply Nat.pow_le_mono_r; lia).
    apply (proj1 (Q_of_nat_le _ _)) in hpow9.
    rewrite (Q_of_nat_pow2_eq 9) in hpow9; change (inject_Z (Z.of_N (N_pow2 9))) with 512 in hpow9.
    clear - hpow9 hUnit h11_v_le hSv; nra. }
  set (H8' := (J - 8)%nat).
  assert (hH8'_2 : (2 <= H8')%nat) by lia.
  assert (hJ_eq : J = (H8' + 8)%nat) by lia.
  assert (hUnit_H8' : z11 v * Q_of_nat (2 ^ H8') == 512).
  { assert (hpow : (2 ^ J = 2 ^ H8' * 2 ^ 8)%nat) by (rewrite hJ_eq, Nat.pow_add_r; reflexivity).
    rewrite hpow, Q_of_nat_mul, (Q_of_nat_pow2_eq 8) in hUnit.
    change (inject_Z (Z.of_N (N_pow2 8))) with 256 in hUnit.
    lra. }
  pose proof (z1i hB_all) as hBud.
  fold v in hBud.
  rewrite (Q_of_N_to_nat 249044%N), (Q_of_nat_mul m_end 8), Q_of_nat_8 in hBud.
  change (inject_Z (Z.of_N 249044%N)) with 249044 in hBud.
  assert (hBud_v : (Q_of_nat m_end * 8) * z11 v == 249041 + 3 * z11 v - 2 * (a - b)) by lra.
  set (B := (1 + m_end * 4)%nat).
  assert (hB_cast : Q_of_nat B == 1 + Q_of_nat m_end * 4).
  { unfold B; rewrite Q_of_nat_add, Q_of_nat_mul, Q_of_nat_1, Q_of_nat_4; reflexivity. }
  assert (h243_q : Q_of_nat 243 == 243) by reflexivity.
  assert (h244_q : Q_of_nat 244 == 244) by reflexivity.
  assert (hB_lo : (243 * 2 ^ H8' <= B)%nat).
  { apply (proj2 (Q_of_nat_le _ _)).
    rewrite Q_of_nat_mul, h243_q.
    assert (h_b_v : (Q_of_nat B - 243 * Q_of_nat (2 ^ H8')) * z11 v ==
        z11 v + (1#2) * ((Q_of_nat m_end * 8) * z11 v) - 243 * (z11 v * Q_of_nat (2 ^ H8')))
      by (rewrite hB_cast; ring).
    assert (h_pos_v : 0 < (Q_of_nat B - 243 * Q_of_nat (2 ^ H8')) * z11 v) by lra.
    clear - h_pos_v hSv; nra. }
  assert (hB_hi : (B < 244 * 2 ^ H8')%nat).
  { apply (proj2 (Q_of_nat_lt _ _)).
    rewrite Q_of_nat_mul, h244_q.
    assert (h_b_v : (244 * Q_of_nat (2 ^ H8') - Q_of_nat B) * z11 v ==
        244 * (z11 v * Q_of_nat (2 ^ H8')) - z11 v - (1#2) * ((Q_of_nat m_end * 8) * z11 v))
      by (rewrite hB_cast; ring).
    assert (h_pos_v : 0 < (244 * Q_of_nat (2 ^ H8') - Q_of_nat B) * z11 v) by lra.
    clear - h_pos_v hSv; nra. }
  set (A8' := (B - 243 * 2 ^ H8')%nat).
  assert (hA8'_lt : (A8' < 2 ^ H8')%nat) by lia.
  destruct (z0T H8' A8' hA8'_lt) as [hi8' hD_hi8'].
  assert (hA8'_mod : exists m' : nat, A8' = (1 + m' * 4)%nat).
  { assert (hpow4 : (2 ^ H8' = 2 ^ (H8' - 2) * 4)%nat).
    { replace H8' with ((H8' - 2) + 2)%nat at 1 by lia.
      rewrite Nat.pow_add_r; reflexivity. }
    exists (m_end - 243 * 2 ^ (H8' - 2))%nat.
    unfold A8', B; rewrite hpow4 in *; lia. }
  destruct hA8'_mod as [m_a8 hm_a8].
  assert (hLow' : exists w, hi8' = WQ :: WK :: w).
  { rewrite hm_a8 in hD_hi8'; exact (z1K hD_hi8' hH8'_2). }
  assert (hD_ds' : zDg (1 + m_end * 4)%nat J (hi8' ++ zTail8)).
  { pose proof (z0U hD_hi8' zDg_tail8) as hU.
    replace (A8' + 243 * 2 ^ H8')%nat with (1 + m_end * 4)%nat in hU by (unfold A8', B; lia).
    replace (H8' + 8)%nat with J in hU by lia.
    exact hU. }
  set (u' := [WV; WV; WK; WV] ++ v).
  assert (h11_u' : z11 u' == (1#4) * z11 v) by (unfold u'; cbn [app z11]; ring).
  assert (hW_u' : z0W u' == (11#32) + (1#4) * z0W v) by (unfold u'; cbn [app z0W]; ring).
  pose proof (z17 hD_hi8') as hDef'.
  assert (hA8'_q : Q_of_nat A8' + 243 * Q_of_nat (2 ^ H8') == 1 + Q_of_nat m_end * 4).
  { assert (heq : (A8' + 243 * 2 ^ H8' = B)%nat) by (unfold A8', B; lia).
    pose proof (proj1 (Q_of_nat_eq _ _) heq) as hq.
    rewrite Q_of_nat_add, Q_of_nat_mul, h243_q in hq; lra. }
  assert (hZ_new : z11 u' * z0Z hi8' <= 1273#10).
  { assert (h1 : z0Z hi8' == Q_of_nat (2 ^ H8') - 1 - Q_of_nat A8') by lra.
    assert (h2 : Q_of_nat A8' == 1 + Q_of_nat m_end * 4 - 243 * Q_of_nat (2 ^ H8')) by lra.
    assert (h_z_prod : z11 u' * z0Z hi8' ==
        (244#4) * (z11 v * Q_of_nat (2 ^ H8')) - (1#2) * z11 v -
        (1#8) * ((Q_of_nat m_end * 8) * z11 v))
      by (rewrite h11_u', h1, h2; ring).
    lra. }
  assert (hHeight' : z11 u' * Q_of_nat (2 ^ H8') == 128) by (rewrite h11_u'; lra).
  exists (u' ++ (hi8' ++ zTail8)); split.
  - assert (h_in_eq : (u ++ ((WQ :: WK :: w0) ++ zTail8)) ++ [WK] =
        (u ++ ((WQ :: WK :: w0) ++ [WQ; WQ; WK])) ++ [WK; WQ; WQ; WQ; WQ; WK]).
    { unfold zTail8; repeat rewrite <- app_assoc; reflexivity. }
    assert (h_out_eq : u' ++ (hi8' ++ zTail8) = [WV; WV; WK; WV] ++ v ++ (hi8' ++ zTail8)).
    { unfold u'; repeat rewrite <- app_assoc; reflexivity. }
    rewrite h_out_eq.
    refine (BStep_intro _ (m_end * 4)%nat v a b J (hi8' ++ zTail8) _ hD_ds').
    replace ((m_end * 4) * 2)%nat with (m_end * 8)%nat by lia.
    rewrite h_in_eq; exact hB_all.
  - refine (BGood_intro H8' u' A8' hi8' hD_hi8' hHeight' ltac:(lra) _ _ hLow' ltac:(lra) hZ_new).
    + exists ([WK; WV] ++ v1 ++ (WV :: y) ++ [WQ; d1_tok; WV]).
      unfold u', v; repeat rewrite <- app_assoc; reflexivity.
    + assert (heq_u' : u' = ([WV; WV; WK; WV] ++ (v1 ++ WV :: y)) ++ [WQ; d1_tok; WV; WV]).
      { unfold u', v; repeat rewrite <- app_assoc; reflexivity. }
      rewrite heq_u'; exact (z1I _ _ hL_p3).
Qed.

Lemma z1P {A H : nat} {da : zW} (hD : zDg A H da) (hZ : A = 0%nat) :
  zTs da 0inf = 0inf.
Proof.
  induction hD as [| A1 H1 u1 _ IH | A1 H1 u1 _ _]; [reflexivity | | lia].
  cbn [zTs]; rewrite (IH ltac:(lia)), zDd; reflexivity.
Qed.

Lemma z1Q {A H : nat} {da : zW} (hD : zDg A H da) (hPos : (0 < A)%nat) :
  BRIncs false ((A - 1) * 2)%nat 0inf (zTs da 0inf).
Proof.
  induction hD as [| A1 H1 u1 hDu IH | A1 H1 u1 hDu IH]; [lia | |].
  - pose proof (BRIncs_short00 (IH ltac:(lia))) as hs.
    rewrite zDd in hs; cbn [zTs].
    replace ((A1 * 2 - 1) * 2)%nat with (2 + (A1 - 1) * 4)%nat by lia.
    exact hs.
  - destruct A1 as [| A1].
    + cbn [Nat.mul Nat.add Nat.sub zTs]; rewrite (z1P hDu eq_refl).
      assert (hd : d1 *> 0inf = one *> 0inf) by solve_const0_eq.
      rewrite hd; exact (BRIncs_zero 0inf).
    + pose proof (IH ltac:(lia)) as hIH.
      replace (S A1 - 1)%nat with A1 in hIH by lia.
      pose proof (BRIncs_short10 hIH) as hs.
      rewrite zDd in hs; cbn [zTs].
      replace ((1 + S A1 * 2 - 1) * 2)%nat with (4 + A1 * 4)%nat by lia.
      exact hs.
Qed.

Lemma z1R {orig out : zW} (hS : BStep orig out) :
  exists r, BRIncs false 128%nat (zTs (zP33 ++ orig) 0inf) r /\
    zTs (zP33 ++ out) 0inf = zTs [WV; WV; WQ; WV] r.
Proof.
  destruct hS as [orig n v a b J ds hI hD].
  assert (hB : BRIncs false (n * 2)%nat 0inf (zTs ds 0inf)).
  { replace (n * 2)%nat with ((1 + n - 1) * 2)%nat by lia.
    exact (z1Q hD ltac:(lia)). }
  assert (hR_orig : BRIncs false (N.to_nat 249044%N) (zTs orig 0inf) (zTs (v ++ ds) 0inf)).
  { pose proof (z1l hI hB) as hR.
    rewrite !z0S in hR; cbn [zTs] in hR; rewrite zDd in hR.
    rewrite z0S; exact hR. }
  pose proof (zBRIncs_P33 hR_orig) as hR_p33.
  exists (zTs (zOut33 ++ (v ++ ds)) 0inf); split.
  - rewrite z0S, z0S; exact hR_p33.
  - assert (h_eq : zP33 ++ ([WV; WV; WK; WV] ++ v ++ ds) = [WV; WV; WQ; WV] ++ (zOut33 ++ (v ++ ds))).
    { unfold zP33, zOut33; repeat rewrite <- app_assoc; reflexivity. }
    rewrite h_eq, z0S; reflexivity.
Qed.

Fixpoint zPf_pos (p : positive) : zW :=
  match p with
  | xH => [WQ]
  | xO p' => WK :: zPf_pos p'
  | xI p' => WQ :: zPf_pos p'
  end.

Lemma z1S_pos (p : positive) :
  exists H, Binary (Pos.to_nat p) H (zTs (zPf_pos p) 0inf).
Proof.
  induction p as [p' [H hB] | p' [H hB] |].
  - exists (1 + H)%nat.
    pose proof (Pos2Nat.is_pos p') as hp.
    replace (Pos.to_nat p') with (1 + (Pos.to_nat p' - 1))%nat in hB by lia.
    replace (Pos.to_nat p'~1) with (3 + (Pos.to_nat p' - 1) * 2)%nat by lia.
    exact (Binary_two hB).
  - exists (1 + H)%nat.
    pose proof (Pos2Nat.is_pos p') as hp.
    replace (Pos.to_nat p') with (1 + (Pos.to_nat p' - 1))%nat in hB by lia.
    replace (Pos.to_nat p'~0) with (2 + (Pos.to_nat p' - 1) * 2)%nat by lia.
    exact (Binary_zero hB).
  - exists 1%nat; exact Binary_one.
Qed.

Fixpoint zSw (p u : zW) : option zW :=
  match p, u with
  | [], _ => Some u
  | WV :: p', WV :: u' => zSw p' u'
  | WK :: p', WK :: u' => zSw p' u'
  | WQ :: p', WQ :: u' => zSw p' u'
  | _, _ => None
  end.

Lemma z1T (p : zW) :
  forall (u v : zW), zSw p u = Some v -> u = p ++ v.
Proof.
  induction p as [| w p IH]; intros u v h.
  - injection h as <-; reflexivity.
  - destruct u as [| x u]; [destruct w; discriminate h |].
    destruct w, x; try discriminate h; cbn [zSw app] in *; f_equal; exact (IH u v h).
Qed.

Definition z1U (w : Word) : bool :=
  match w with
  | WK => true
  | _ => false
  end.

Lemma z1V (u : zW) (h : forallb z1U u = true) :
  zTs u 0inf = 0inf.
Proof.
  induction u as [| w u IH]; [reflexivity |].
  destruct w; try discriminate h.
  cbn [forallb z1U] in h; cbn [zTs]; rewrite (IH h), zDd; reflexivity.
Qed.

Inductive Choice : Type :=
  | CT | CP0 | CP1 | CS00 | CS01 | CS10 | CS11
  | COC0 (r : nat) | COC1 (r : nat) | CEC (r : nat)
  | CSP0 | CSP1 | CSC0 (r : nat) | CSC1 (r : nat).

Definition zInS (ch : Choice) : bool :=
  match ch with
  | CSP0 | CSP1 | CSC0 _ | CSC1 _ => true
  | _ => false
  end.

Definition zOutS (ch : Choice) : bool :=
  match ch with
  | COC0 _ | COC1 _ | CEC _ | CSC0 _ | CSC1 _ => true
  | _ => false
  end.

Definition zGetN_N (ch : Choice) (k : N) : N :=
  match ch with
  | CT => (k - 2)%N
  | CP0 | CP1 | CSP0 | CSP1 => (k - 1)%N
  | CS00 | CS01 => N.div (k - 2) 4
  | CS10 | CS11 => N.div (k - 4) 4
  | COC0 _ | CSC0 _ => N.div (k - 3) 4
  | COC1 _ | CSC1 _ => N.div (k - 5) 4
  | CEC _ => N.div (k - 6) 2
  end.

Definition z1W_N (ch : Choice) (n : N) : N :=
  match ch with
  | CT => (2 + n)%N
  | CP0 | CP1 | CSP0 | CSP1 => (1 + n)%N
  | CS00 | CS01 => (2 + n * 4)%N
  | CS10 | CS11 => (4 + n * 4)%N
  | COC0 _ | CSC0 _ => (3 + n * 4)%N
  | COC1 _ | CSC1 _ => (5 + n * 4)%N
  | CEC _ => (6 + n * 2)%N
  end.

Definition z1X_N (ch : Choice) (n : N) : N :=
  match ch with
  | CT | CP1 | CS01 | CS11 | CSP1 => (1 + n * 2)%N
  | CP0 | CS00 | CS10 | CSP0 => (n * 2)%N
  | COC0 r | COC1 r => (1 + n * N_pow2 (1 + r))%N
  | CEC r => (1 + (1 + n * 2) * N_pow2 (1 + r))%N
  | CSC0 r | CSC1 r => (1 + n * N_pow2 (2 + r))%N
  end.

Definition z1Y (ch : Choice) : zW :=
  match ch with
  | CT => [WV]
  | CP0 => [WQ; WK]
  | CP1 => [WQ; WQ]
  | CS00 | CS10 | CSP0 => [WK]
  | CS01 | CS11 | CSP1 => [WQ]
  | COC0 r | COC1 r => zQK r [WV]
  | CEC r | CSC0 r | CSC1 r => WK :: zQK r [WV]
  end.

Definition z1Z (ch : Choice) : zW :=
  match ch with
  | CT | CP0 | CP1 | CSP0 | CSP1 => [WV]
  | CS00 | CS01 => [WK]
  | CS10 | CS11 => [WQ]
  | COC0 r => WK :: zR r WV
  | COC1 r => WQ :: zR r WV
  | CEC r => zR (1 + r) WV
  | CSC0 r => WK :: zR (1 + r) WV
  | CSC1 r => WQ :: zR (1 + r) WV
  end.

Fixpoint z20_N (cs : list Choice) (s : bool) (k : N) (u : zW) : option zW :=
  match cs with
  | [] =>
    let n := N.div2 k in
    if negb s then
      if N.eqb k (n * 2)%N then
        if forallb z1U u then Some (zPf_pos (N.succ_pos n)) else None
      else None
    else None
  | ch0 :: cs' =>
    let n := zGetN_N ch0 k in
    if Bool.eqb s (zInS ch0) then
      if N.eqb k (z1W_N ch0 n) then
        match zSw (z1Y ch0) u with
        | None => None
        | Some w =>
          match z20_N cs' (zOutS ch0) (z1X_N ch0 n) w with
          | None => None
          | Some x => Some (z1Z ch0 ++ x)
          end
        end
      else None
    else None
  end.

Lemma z21_N (cs : list Choice) :
  forall (s : bool) (k : N) (u v : zW), z20_N cs s k u = Some v ->
    BRIncs s (N.to_nat k) (zTs u 0inf) (zTs v 0inf).
Proof.
  induction cs as [| ch0 cs IH]; intros s k u v hE.
  - cbn [z20_N] in hE.
    destruct s; [discriminate | cbn [negb] in hE].
    destruct (N.eqb k (N.div2 k * 2)) eqn:hk; [| discriminate].
    apply N.eqb_eq in hk.
    destruct (forallb z1U u) eqn:hu; [| discriminate].
    inversion hE as [[hv]]; subst v.
    rewrite (z1V u hu).
    destruct (z1S_pos (N.succ_pos (N.div2 k))) as [H hB].
    pose proof (z0H hB) as hR.
    assert (hsucc : Pos.to_nat (N.succ_pos (N.div2 k)) = (1 + N.to_nat (N.div2 k))%nat).
    { pose proof (N.succ_pos_spec (N.div2 k)) as hsp.
      apply (f_equal N.to_nat) in hsp.
      cbn [N.to_nat] in hsp; lia. }
    replace ((Pos.to_nat (N.succ_pos (N.div2 k)) - 1) * 2)%nat with (N.to_nat k) in hR by lia.
    exact hR.
  - cbn [z20_N] in hE.
    destruct (Bool.eqb s (zInS ch0)) eqn:hs; [| discriminate].
    apply Bool.eqb_prop in hs; subst s.
    set (n := zGetN_N ch0 k) in *.
    destruct (N.eqb k (z1W_N ch0 n)) eqn:hk; [| discriminate].
    apply N.eqb_eq in hk.
    destruct (zSw (z1Y ch0) u) as [w |] eqn:hU; [| discriminate].
    destruct (z20_N cs (zOutS ch0) (z1X_N ch0 n) w) as [x |] eqn:hC; [| discriminate].
    inversion hE as [[hv]]; subst v.
    pose proof (z1T (z1Y ch0) u w hU) as rfl_u; subst u.
    pose proof (IH (zOutS ch0) (z1X_N ch0 n) w x hC) as hIH.
    rewrite hk.
    destruct ch0 as [| | | | | | | r | r | r | | | r | r];
      cbn [z1Y z1Z zInS zOutS z1W_N z1X_N] in hIH |- *;
      repeat (rewrite N2Nat.inj_add in hIH || rewrite N2Nat.inj_mul in hIH ||
              rewrite N_to_nat_pow2 in hIH || rewrite N2Nat.inj_add ||
              rewrite N2Nat.inj_mul || rewrite N_to_nat_pow2);
      change (N.to_nat 1) with 1%nat in *;
      change (N.to_nat 2) with 2%nat in *;
      change (N.to_nat 3) with 3%nat in *;
      change (N.to_nat 4) with 4%nat in *;
      change (N.to_nat 5) with 5%nat in *;
      change (N.to_nat 6) with 6%nat in *.
    + exact (BRIncs_T hIH).
    + exact (BRIncs_pair0 hIH).
    + exact (BRIncs_pair1 hIH).
    + exact (BRIncs_short00 hIH).
    + exact (BRIncs_short01 hIH).
    + exact (BRIncs_short10 hIH).
    + exact (BRIncs_short11 hIH).
    + rewrite z0S; cbn [app zTs]; rewrite z0S; exact (BRIncs_odd_chain0 r hIH).
    + rewrite z0S; cbn [app zTs]; rewrite z0S; exact (BRIncs_odd_chain1 r hIH).
    + cbn [app zTs]; rewrite z0S, z0S; exact (BRIncs_even_chain r hIH).
    + exact (BRIncs_shift_pair0 hIH).
    + exact (BRIncs_shift_pair1 hIH).
    + cbn [app zTs]; rewrite z0S, z0S; exact (BRIncs_shift_chain0 r hIH).
    + cbn [app zTs]; rewrite z0S, z0S; exact (BRIncs_shift_chain1 r hIH).
Qed.

Definition z22_N (cs : list Choice) (u : zW) : option zW :=
  match z20_N cs false 128%N (u ++ [WK]) with
  | Some v => Some ([WV; WV; WQ; WV] ++ v)
  | None => None
  end.

Lemma z23_N (cs : list Choice) (u v : zW) (h : z22_N cs u = Some v) :
  exists r, BRIncs false 128%nat (zTs u 0inf) r /\ zTs v 0inf = zTs [WV; WV; WQ; WV] r.
Proof.
  unfold z22_N in h.
  destruct (z20_N cs false 128%N (u ++ [WK])) as [w |] eqn:hE; [| discriminate h].
  injection h as <-.
  exists (zTs w 0inf); split; [| reflexivity].
  pose proof (z21_N cs false 128%N (u ++ [WK]) w hE) as hR.
  change (N.to_nat 128%N) with 128%nat in hR.
  rewrite z0S in hR; cbn [zTs] in hR; rewrite zDd in hR.
  exact hR.
Qed.

Inductive Rounds : side -> side -> Prop :=
  | Rounds_refl (r : side) : Rounds r r
  | Rounds_next {r s t0 : side} :
      BRIncs false 128%nat r s -> Rounds (zTs [WV; WV; WQ; WV] s) t0 -> Rounds r t0.

Fixpoint z24_N (cs : list (list Choice)) (u : zW) : option zW :=
  match cs with
  | [] => Some u
  | c :: cs' =>
    match z22_N c u with
    | None => None
    | Some v => z24_N cs' v
    end
  end.

Lemma z25_N (cs : list (list Choice)) :
  forall (u v : zW), z24_N cs u = Some v ->
    Rounds (zTs u 0inf) (zTs v 0inf).
Proof.
  induction cs as [| c cs IH]; intros u v h.
  - injection h as <-; exact (Rounds_refl _).
  - cbn [z24_N] in h.
    destruct (z22_N c u) as [w |] eqn:hW; [| discriminate h].
    destruct (z23_N c u w hW) as [r [hR hEq]].
    apply (Rounds_next hR).
    rewrite <- hEq; exact (IH w v h).
Qed.

Definition z26 (w : Word) : bool :=
  match w with
  | WV => false
  | _ => true
  end.

Lemma z27 (ds : zW) (h : forallb z26 ds = true) :
  exists A, zDg A (length ds) ds.
Proof.
  induction ds as [| w ds IH]; [exists 0%nat; exact zDg_nil |].
  destruct w; [discriminate h | |].
  - cbn [forallb z26] in h; destruct (IH h) as [A hI].
    exists (A * 2)%nat; exact (zDg_zero hI).
  - cbn [forallb z26] in h; destruct (IH h) as [A hI].
    exists (1 + A * 2)%nat; exact (zDg_one hI).
Qed.

Fixpoint zN11 (u : zW) : nat :=
  match u with
  | [] => 0%nat
  | WV :: u' => (1 + zN11 u')%nat
  | _ :: u' => zN11 u'
  end.

Fixpoint zP11 (u : zW) : nat :=
  match u with
  | [] => 0%nat
  | WV :: u' => zP11 u'
  | _ :: u' => (1 + zP11 u')%nat
  end.

Lemma z11_pow (u : zW) :
  z11 u * Q_of_nat (2 ^ zN11 u) == Q_of_nat (2 ^ zP11 u).
Proof.
  induction u as [| w u IH].
  - cbn [z11 zN11 zP11 Nat.pow]; rewrite Q_of_nat_1; lra.
  - destruct w; cbn [z11 zN11 zP11].
    + rewrite (Q_of_nat_pow2 (zN11 u)); lra.
    + rewrite (Q_of_nat_pow2 (zP11 u)); lra.
    + rewrite (Q_of_nat_pow2 (zP11 u)); lra.
Qed.

Fixpoint zWU_N (u : zW) : N :=
  match u with
  | [] => 0%N
  | WV :: u' => N.div (zWU_N u' + 1) 2
  | WK :: u' => (90112 + 2 * zWU_N u')%N
  | WQ :: u' => (65536 + 2 * zWU_N u')%N
  end.

Lemma zWU_ge (u : zW) :
  65536 * z0W u <= Q_of_nat (N.to_nat (zWU_N u)).
Proof.
  induction u as [| w u IH].
  - cbn [z0W zWU_N N.to_nat]; rewrite Q_of_nat_0; lra.
  - destruct w; cbn [z0W zWU_N].
    + pose proof (N.div_mod (zWU_N u + 1) 2 ltac:(lia)) as hdm.
      pose proof (N.mod_lt (zWU_N u + 1) 2 ltac:(lia)) as hmlt.
      assert (hdiv : (N.to_nat (zWU_N u) <= 2 * N.to_nat (N.div (zWU_N u + 1) 2))%nat) by lia.
      apply (proj1 (Q_of_nat_le _ _)) in hdiv.
      rewrite Q_of_nat_mul, Q_of_nat_2 in hdiv; lra.
    + rewrite N2Nat.inj_add, N2Nat.inj_mul, Q_of_nat_add, Q_of_nat_mul.
      rewrite (Q_of_N_to_nat 90112%N), (Q_of_N_to_nat 2%N).
      change (inject_Z (Z.of_N 90112%N)) with 90112; change (inject_Z (Z.of_N 2%N)) with 2; lra.
    + rewrite N2Nat.inj_add, N2Nat.inj_mul, Q_of_nat_add, Q_of_nat_mul.
      rewrite (Q_of_N_to_nat 65536%N), (Q_of_N_to_nat 2%N).
      change (inject_Z (Z.of_N 65536%N)) with 65536; change (inject_Z (Z.of_N 2%N)) with 2; lra.
Qed.

Fixpoint zZNat_N (u : zW) : N :=
  match u with
  | [] => 0%N
  | WV :: u' => zZNat_N u'
  | WK :: u' => (1 + 2 * zZNat_N u')%N
  | WQ :: u' => (2 * zZNat_N u')%N
  end.

Lemma zZNat_eq (u : zW) (h : forallb z26 u = true) :
  z0Z u == Q_of_nat (N.to_nat (zZNat_N u)).
Proof.
  induction u as [| w u IH]; [cbn [z0Z zZNat_N N.to_nat]; rewrite Q_of_nat_0; reflexivity |].
  destruct w; [discriminate h | |].
  - cbn [forallb z26] in h; cbn [z0Z zZNat_N].
    rewrite N2Nat.inj_add, N2Nat.inj_mul, Q_of_nat_add, Q_of_nat_mul.
    rewrite (Q_of_N_to_nat 1%N), (Q_of_N_to_nat 2%N), (IH h).
    change (inject_Z (Z.of_N 1%N)) with 1; change (inject_Z (Z.of_N 2%N)) with 2; ring.
  - cbn [forallb z26] in h; cbn [z0Z zZNat_N].
    rewrite N2Nat.inj_mul, Q_of_nat_mul.
    rewrite (Q_of_N_to_nat 2%N), (IH h).
    change (inject_Z (Z.of_N 2%N)) with 2; ring.
Qed.

Fixpoint zLastV (u : zW) : bool :=
  match u with
  | [] => false
  | [x] => match x with WV => true | _ => false end
  | _ :: ((y :: ys) as u') => zLastV u'
  end.

Lemma zLastV_eq (u : zW) : zLastV u = true -> exists w, u = w ++ [WV].
Proof.
  induction u as [| x u' IH]; intros h.
  - discriminate h.
  - destruct u' as [| y ys].
    + destruct x; try discriminate h; exists (@nil Word); reflexivity.
    + change (zLastV (y :: ys) = true) in h.
      destruct (IH h) as [w ->]; exists (x :: w); reflexivity.
Qed.

Definition zInitVV (u : zW) : bool :=
  match u with
  | WV :: WV :: u' => zLastV u'
  | _ => false
  end.

Lemma zInitVV_eq (u : zW) (h : zInitVV u = true) : exists w, u = WV :: WV :: (w ++ [WV]).
Proof.
  destruct u as [| [| |] [| [| |] u']]; try discriminate h.
  cbn [zInitVV] in h; destruct (zLastV_eq u' h) as [w ->]; exists w; reflexivity.
Qed.

Definition zInitQK (u : zW) : bool :=
  match u with
  | WQ :: WK :: _ => true
  | _ => false
  end.

Lemma zInitQK_eq (u v : zW) (h : zInitQK u = true) : exists w, u ++ v = WQ :: WK :: w.
Proof.
  destruct u as [| [| |] [| [| |] u']]; try discriminate h.
  exists (u' ++ v); reflexivity.
Qed.

Lemma Q_of_N_leb (a b : N) (h : N.leb a b = true) :
  Q_of_nat (N.to_nat a) <= inject_Z (Z.of_N b).
Proof.
  apply N.leb_le in h.
  rewrite (Q_of_N_to_nat a).
  unfold Qle; cbn; lia.
Qed.

Lemma z28 (u hi_low hi_top : zW)
  (hD_low : forallb z26 hi_low = true)
  (hD_top : forallb z26 hi_top = true)
  (hTopLen : (length hi_top =? 16)%nat = true)
  (hPow : (zP11 u + (length hi_low + 16) =? 7 + zN11 u)%nat = true)
  (hU11_nat : (4 + zP11 u <=? zN11 u)%nat = true)
  (hEnd : zInitVV u = true)
  (hLu : z0L u = true)
  (hLo : zInitQK hi_low = true)
  (hW_nat : N.leb (zWU_N u) 969932%N = true)
  (hZ_nat : N.leb (10 * (1 + zZNat_N hi_top))%N 651776%N = true) :
  BGood (u ++ ((hi_low ++ hi_top) ++ zTail8)).
Proof.
  apply Nat.eqb_eq in hTopLen.
  apply Nat.eqb_eq in hPow.
  apply Nat.leb_le in hU11_nat.
  set (hi8 := hi_low ++ hi_top).
  assert (hD : forallb z26 hi8 = true)
    by (unfold hi8; rewrite forallb_app, hD_low, hD_top; reflexivity).
  destruct (z27 hi8 hD) as [A hI].
  assert (hLen : (length hi8 = length hi_low + 16)%nat)
    by (unfold hi8; rewrite length_app, hTopLen; reflexivity).
  pose proof (z11_pow u) as h11_u.
  assert (hPow2 : (2 ^ zP11 u * 2 ^ length hi8 = 2 ^ 7 * 2 ^ zN11 u)%nat)
    by (rewrite <- Nat.pow_add_r, hLen, hPow, Nat.pow_add_r; reflexivity).
  pose proof (proj1 (Q_of_nat_eq _ _) hPow2) as hPow2_q.
  rewrite !Q_of_nat_mul, (Q_of_nat_pow2_eq 7) in hPow2_q.
  change (inject_Z (Z.of_N (N_pow2 7))) with 128 in hPow2_q.
  pose proof (proj1 (Q_of_nat_lt 0 (2 ^ zN11 u)) (zPp (zN11 u))) as hPos.
  rewrite Q_of_nat_0 in hPos.
  assert (hHeight : z11 u * Q_of_nat (2 ^ length hi8) == 128)
    by (clear - h11_u hPow2_q hPos; nra).
  assert (hLe2 : (2 ^ 4 * 2 ^ zP11 u <= 2 ^ zN11 u)%nat)
    by (rewrite <- Nat.pow_add_r; apply Nat.pow_le_mono_r; lia).
  pose proof (proj1 (Q_of_nat_le _ _) hLe2) as hLe2_q.
  rewrite Q_of_nat_mul, (Q_of_nat_pow2_eq 4) in hLe2_q.
  change (inject_Z (Z.of_N (N_pow2 4))) with 16 in hLe2_q.
  assert (hU11 : z11 u <= 1#16) by (clear - h11_u hLe2_q hPos; nra).
  pose proof (Q_of_N_leb _ _ hW_nat) as hW_q; change (inject_Z (Z.of_N 969932%N)) with 969932 in hW_q.
  pose proof (zWU_ge u) as hW_ge.
  assert (hW : z0W u <= 74#5) by lra.
  destruct (z27 hi_low hD_low) as [A_low hI_low].
  destruct (z27 hi_top hD_top) as [A_top hI_top].
  destruct (zDw hI_low) as [hDw_low1 [hDw_low2 _]].
  destruct (zDw hI_top) as [hDw_top1 _].
  assert (hZ_low_le : z0Z hi_low <= z11 hi_low).
  { pose proof (z12 hi_low); pose proof (proj1 (proj2 (proj2 (zWn hi_low)))); lra. }
  assert (h11_top : z11 hi_top == 65536).
  { rewrite hTopLen, (Q_of_nat_pow2_eq 16) in hDw_top1.
    change (inject_Z (Z.of_N (N_pow2 16))) with 65536 in hDw_top1; exact hDw_top1. }
  pose proof (proj1 (zDw hI)) as h11_hi8.
  assert (h11_split : z11 hi8 == z11 hi_low * z11 hi_top) by (unfold hi8; apply z16).
  assert (h_u_low : z11 u * z11 hi_low == 1#512).
  { assert (h_eq : z11 u * Q_of_nat (2 ^ length hi8) == 65536 * (z11 u * z11 hi_low))
      by (rewrite <- h11_hi8, h11_split, h11_top; ring).
    lra. }
  assert (hZ_split : z0Z hi8 == z0Z hi_low + z11 hi_low * z0Z hi_top) by (unfold hi8; apply z14).
  pose proof (zZNat_eq hi_top hD_top) as hZ_top_eq.
  pose proof (Q_of_N_leb _ _ hZ_nat) as hZ_top_q.
  rewrite N2Nat.inj_mul, N2Nat.inj_add, Q_of_nat_mul, Q_of_nat_add in hZ_top_q.
  rewrite (Q_of_N_to_nat 10%N), (Q_of_N_to_nat 1%N) in hZ_top_q.
  change (inject_Z (Z.of_N 10%N)) with 10 in hZ_top_q.
  change (inject_Z (Z.of_N 1%N)) with 1 in hZ_top_q.
  change (inject_Z (Z.of_N 651776%N)) with 651776 in hZ_top_q.
  pose proof (zSp u) as hSu.
  assert (hZ : z11 u * z0Z hi8 <= 1273#10).
  { assert (h_uz_split : z11 u * z0Z hi8 == z11 u * z0Z hi_low + (z11 u * z11 hi_low) * z0Z hi_top)
      by (rewrite hZ_split; ring).
    assert (h_uz_low : z11 u * z0Z hi_low <= z11 u * z11 hi_low) by (clear - hSu hZ_low_le; nra).
    assert (h_uz_top : (z11 u * z11 hi_low) * z0Z hi_top == (1#512) * Q_of_nat (N.to_nat (zZNat_N hi_top)))
      by (rewrite h_u_low, hZ_top_eq; ring).
    lra. }
  exact (BGood_intro (length hi8) u A hi8 hI hHeight hU11
    (zInitVV_eq u hEnd) hLu (zInitQK_eq hi_low hi_top hLo) hW hZ).
Qed.


(* ---------- Section 7E: Initial trajectory, witness data, and nonhalt ---------- *)

Local Open Scope nat_scope.

Definition w_pre3_rest : list sym := t ++ t ++ (t ++ d1).
Definition w_pre5_rest : list sym := w_pre3_rest ++ t ++ (t ++ d0).
Definition w_pre_rest : list sym := w_pre5_rest ++ t ++ (t ++ d0).
Definition w_pre : list sym := w_word ++ w_pre_rest.

Lemma zW_pre3_seg :
  Seg [ch; cj; ch] ([ch] ^^ 4 ++ [cp] ++ [ch] ^^ 2) w_pre3_rest (t ++ t ++ (d0 ++ t)).
Proof.
  unfold w_pre3_rest; exact (zS0 (zS0 zW_s1 zW_s2) zW_s3).
Qed.

Lemma zW_pre5_seg :
  Seg [ch; cj; ch] ([ch] ^^ 8 ++ [cj; ch]) w_pre5_rest (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t)).
Proof.
  unfold w_pre5_rest; exact (zS0 (zS0 zW_pre3_seg zW_s4) zW_s5).
Qed.

Lemma zW_pre_seg :
  Seg [ch; cj; ch] ([ch] ^^ 16) w_pre_rest
    (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))).
Proof.
  unfold w_pre_rest; exact (zS0 (zS0 zW_pre5_seg zW_s6) zW_s7).
Qed.

Lemma zW_pre_full {r r' : side} (h : Side ([ch] ^^ 16) r r') :
  zCL lh (w_pre *> r) -[ canon_tm ]->+ zCf r'.
Proof.
  pose proof (zW_pre_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  assert (h_in : w_word *> (w_pre_rest *> r) = w_pre *> r)
    by (unfold w_pre; rewrite Str_app_assoc; reflexivity).
  assert (h_out : (w_word ++ t ++ t ++ (t ++ d1)) *>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))) *> r') =
      w_base *> r') by reflexivity.
  unfold zCf.
  rewrite <- h_out, <- h_in.
  exact h_turn.
Qed.

Lemma z108_seg :
  Seg ([ch] ^^ 16) ([cj] ++ [ch] ^^ 31) (d0 ++ t ++ (t ++ one)) (d0 ++ t ++ t).
Proof.
  assert (h1 : Seg ([ch] ^^ 16) ([ch] ^^ 8) d0 d0) by exact (zH_d0_even 8).
  assert (h2 : Seg ([ch] ^^ 8) ([ch] ^^ 16) t t) by exact (zS3 8).
  assert (h3 : Seg ([ch] ^^ 16) ([cj] ++ [ch] ^^ 31) (t ++ one) t).
  { change ([ch] ^^ 16) with ([ch] ++ [ch] ^^ 15).
    change ([cj] ++ [ch] ^^ 31) with ([cj; ch] ++ [ch] ^^ (15 * 2)).
    exact (zSg zH2 (zS3 15)). }
  exact (zS0 (zS0 h1 h2) h3).
Qed.

Lemma z2q {orig out : zW} (hS : BStep orig out) :
  zCf (zTs (zP33 ++ orig) 0inf) -[ canon_tm ]->+ zCf (zTs (zP33 ++ out) 0inf).
Proof.
  destruct (z1R hS) as [r [hI hEq]].
  rewrite hEq.
  exact (z2p hI).
Qed.

Lemma z2r {r r' : side} (h : Rounds r r') :
  zCf r -[ canon_tm ]->* zCf r'.
Proof.
  induction h as [r | r s t0 hR _ IH].
  - finish.
  - eapply evstep_trans; [apply progress_evstep; exact (z2p hR) | exact IH].
Qed.

Definition z29_0108 : zW := ([WK;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WQ;WQ;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK] ++ [WQ;WQ;WQ;WQ]).

Definition z2a_0108 : list (list Choice) := [
  [CS10;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CP1;CP0;CP1;CP1;CP0;CP0;CS01;CP1;CP0];
  ([CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT] ++ [CP0;CS11;CP0;CS11;CP0;CS10;CS10;CS00;CS00;CS10;CS10;CS10;CS10;CS10;CS11;CP0;CP0;CP1;CP0]);
  (([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT] ++ [(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;CP0;CS10;CP1;CP1;CP1;CT;CT;CT;(COC0 0);CSP1;CP0;CS11;CP0;CP1;CP0;CP1;CP0;CP0;CS00;CS00;CS11]) ++ [CP1;CP0]);
  (([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT] ++ [CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS10]) ++ [CS01;CT;CT;CP0;CS10;CS10;CP0;CS01;CP0;CP0;CS00;CP1;CP0;CS11;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CP0;CP0;CS00;CS11;CP1;CP0]);
  (([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CS10;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT] ++ [CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT]) ++ ([CT;CT;CT;(COC0 0);CSP0;CT;CP0;CT;CT;CT;CP1;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT] ++ [CP0;CS10;CS11;CP1;CP1;CP1;CP0;CS10;CS00;CP0;CP0;CP1;CP0;CS10;CS10;CS01;CP0;CS11;CP1;CP1;CP1;CP1;CP0;CP1;CP0;CP0;CS01;CP0;CS10;CS11;CP1;CP0]));
  ((([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT] ++ [CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT]) ++ ([CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT] ++ [CT;CT;CP1;CT;CT;CT;CT;CP0;CT;CT;CT;(COC0 0);CSP1;(COC1 1);CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CP1;CT;CT;CP0;CP0;CP1;CP1])) ++ ([CP0;CS10;CS00;CP0;CP1;CP1;CP0;CP0;CS00;CP0;CS00;CP0;CS01;CP1;CP0;CP0;CS01;CP0;CS10;CS10;CP1;CP0;CS11;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CP0;CP0] ++ [CP0;CS00;CS11;CP1;CP0]));
  ((([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT] ++ [CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;(COC0 0)]) ++ ([CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT;CT;CT;CT] ++ [CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT])) ++ (([CT;CT;CT;CT;CT;CT;CT;CT;CP0;CT;CT;CT;CT;(COC0 0);(CSC1 0);(CSC1 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT] ++ [CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CP0;CP0;CP1;CP1;CP1;CP0;CS11;CP1;CP0;CP0;CS00;CS00;CS01;CP0;CS11;CP1;CP1;CP0;CP0;CS00;CS00;CS00;CS00;CS10]) ++ ([CS00;CP0;CS00;CS10;CS11;CP0;CP1;CP1;CP0;CS10;CS00;CS11;CP1;CP0;CS10;CS01;CP1;CP0;CP0;CS01;CP0;CS10;CS11;CP0;CP0;CS01;CP1;CP1;CP1;CP1;CP0;CP1] ++ [CP0;CP0;CS00;CS00;CS11;CP0;CS10;CS01;CP1;CP0])));
  (((([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0)] ++ [CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT;CT;(COC0 0)]) ++ ([CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT] ++ [CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT])) ++ (([CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;(COC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT] ++ [CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;(COC0 0);CSP0;CS10;(CEC 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CS10;CS00;(CEC 1)]) ++ ([CSP0;CP1;CT;CT;CT;CT;CP0;CS11;CT;CT;CP0;CT;CT;(COC0 0);CSP0;CT;CP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS10;CS01;CT] ++ [CP0;CT;CT;CP0;CS10;CP1;CP0;CS11;CP0;CS10;CS01;CP0;CS11;CP1;CP1;CP0;CS10;CP0;CS00;CS10;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CS10;CP1;CP1;CP1;CP0]))) ++ ([CP0;CP1;CP1;CP1;CP1;CP1;CP0;CS11;CP1;CP0;CS10;CP0;CS00;CP1;CP0;CS10;CS11;CP1;CP0;CP0;CP1;CP0;CS10;CP1;CP0;CS11;CP1;CP1;CP1;CP1;CP1;CP1] ++ [CP0;CP0;CP0;CS00;CS11;CP0;CS10;CS01;CP1;CP0]));
  (((([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CS10;CT;CT;CT;CT;(COC0 0);CSP0;CT] ++ [CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1]) ++ ([CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP0;CT] ++ [CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT])) ++ (([CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0)] ++ [CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);(CSC0 0);CSP1;CT;CT;CT;CT]) ++ ([(COC0 0);CSP0;CT;CP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT] ++ [(COC0 0);CSP0;CT;CP0;CT;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 1);CSP1;CT;CT;(COC0 0);CSP1;(COC1 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT]))) ++ ((([CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;(COC1 0);CSP0;CT;CT;CP1;CT;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT] ++ [CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CP0;CT;CT;CP0;CS10;CS11;CP1;CP1;CP0;CP0;CS01;CP0;CS10;CS11;CP0;CS10;CP1;CP0;CS10;CS11;CP1;CP0;CS11;CP0]) ++ ([CP1;CP0;CS11;CP0;CS10;CS00;CP0;CS00;CS00;CS00;CS00;CP1;CP1;CP0;CP0;CS00;CP1;CP0;CS10;CP1;CP1;CP0;CP0;CP1;CP1;CP0;CS10;CP0;CS00;CS11;CP0;CS10] ++ [CP1;CP1;CP1;CP1;CP1;CP0;CS10;CP1;CP1;CP1;CP1;CP0;CP1;CP1;CP1;CP1;CP0;CP0;CP1;CP1;CP0;CS10;CP0;CP1;CP0;CS10;CS11;CP1;CP0;CP0;CS01;CP0])) ++ [CS10;CS11;CP0;CP0;CS01;CP1;CP1;CP1;CP1;CP0;CP1;CP0;CP0;CS01;CP0;CS10;CS11;CP0;CS10;CS11;CP1;CP0]));
  ((((([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT] ++ [(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;(COC1 0)]) ++ ([CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP0] ++ [CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT])) ++ (([CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT] ++ [(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CS10;CT;CT;CT;CT]) ++ ([CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT] ++ [CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0]))) ++ ((([CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT] ++ [CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CP1;CT;CT;CT;(COC0 0);CSP0;CT;CP1;(COC1 0);CSP1;CT;CT;CP1;CT;(COC0 0);CSP1;CT;CT;(COC0 0);CSP1]) ++ ([CT;(COC0 1);CSP0;CS10;CS00;CS10;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP0;CS11;(COC1 0);CSP1;CT;CT;CT;CT;CT] ++ [(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CT;CP1;CT;CT;(COC0 0);CSP0;CT;CP1;CT;(COC0 0);CSP0;CT;CT])) ++ (([CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CP1;CT;CP1;CT;CT;CP0;CP0;CP1;CP0;CS11;CP0;CS11;CP0;CP1;CP0;CS11;CP1;CP0;CS10;CP1;CP0;CP0;CS00;CP0] ++ [CS01;CP0;CS10;CS01;CP0;CS11;CP0;CP1;CP1;CP0;CS10;CP1;CP0;CS10;CP0;CP0;CS01;CP1;CP1;CP1;CP0;CP1;CP1;CP0;CP0;CS00;CS00;CS01;CP0;CS10;CP0;CP1]) ++ ([CP1;CP0;CS10;CP0;CS00;CP1;CP0;CS11;CP1;CP1;CP0;CS10;CP0;CP1;CP0;CS11;CP0;CP1;CP1;CP1;CP0;CP1;CP1;CP0;CS10;CP0;CS00;CP0;CS00;CP0;CP1;CP1] ++ [CP1;CP1;CP1;CP1;CP0;CS10;CP1;CP1;CP1;CP0;CP0;CP1;CP1;CP1;CP1;CP1;CP0;CS11;CP1;CP0;CS10;CS00;CP0;CP1;CP0;CS10;CS11;CP1;CP0;CP0;CP1;CP0])))) ++ [CS10;CP1;CP0;CS11;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CP0;CP0;CP0;CS00;CS11;CP0;CS10;CS11;CP1;CP0]);
  ((((([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;(COC1 0);CSP1] ++ [CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11]) ++ ([CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT] ++ [(COC1 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1])) ++ (([CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT] ++ [(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0)]) ++ ([(CSC0 0);CSP1;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT] ++ [CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT]))) ++ ((([CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CP1;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT] ++ [(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP1;CT;CT;CT]) ++ ([CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CP0;CS11;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CP1] ++ [CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT])) ++ (([CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP1;CT;(COC0 0)] ++ [CSP1;CT;CT;(COC0 0);(CSC1 0);CSP0;CT;(COC1 1);CSP1;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS10;(CEC 0);CSP1]) ++ ([CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;(COC0 0);CSP1;CT;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 0);(CSC0 0);CSP0;CT;CT] ++ [CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CP0;CT;CT;CT;CP1;CT;CT;CT;CT;(COC0 0);CSP1])))) ++ ((([CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CP1;CT;CT;CP0;CP0;CS01;CP1;CP1;CP0;CP0;CP0;CS00;CS10;CS11;CP0;CS10] ++ [CP1;CP0;CS10;CS11;CP1;CP0;CS10;CS00;CP0;CS01;CP0;CS11;CP1;CP0;CP0;CS01;CP1;CP0;CP1;CP0;CS11;CP0;CP0;CS00;CS00;CS00;CP0;CS00;CS00;CP0;CS01;CP0]) ++ ([CP1;CP1;CP0;CS10;CS00;CP0;CP0;CS00;CS10;CS10;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CS11;CP1;CP0;CP0;CS01;CP0;CP0;CS00;CS00;CS11;CP1;CP0;CS10;CS00;CS01] ++ [CP0;CS10;CS10;CS00;CS10;CS10;CS11;CP0;CS11;CP1;CP0;CS10;CP0;CP1;CP1;CP0;CS11;CP0;CS11;CP1;CP1;CP0;CS10;CS01;CP1;CP0;CS10;CS01;CP0;CS10;CS00;CP1])) ++ (([CP0;CS10;CP1;CP1;CP0;CS10;CP0;CS00;CS11;CP0;CS10;CS11;CP1;CP1;CP1;CP0;CS10;CP1;CP0;CS10;CP0;CP1;CP1;CP0;CP0;CP1;CP1;CP0;CS10;CP0;CS00;CP1] ++ [CP0;CS10;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CS10;CP1;CP1;CP1;CP1;CP0;CP1;CP1;CP1;CP1;CP0;CP0;CS01;CP1;CP0;CS10;CS00;CP0;CP1;CP0;CS10;CS11;CP1]) ++ [CP0;CP0;CS01;CP0;CS10;CS11;CP0;CP0;CS01;CP1;CP1;CP1;CP1;CP0;CP1;CP0;CP0;CS00;CS00;CS11;CP0;CS10;CS01;CP0;CS10;CS01;CP1;CP0])));
  ((((([CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0)] ++ [(CSC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0)]) ++ ([CSP1;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT] ++ [(COC1 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT])) ++ (([CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT] ++ [(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0]) ++ ([CS10;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT] ++ [CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;CT]))) ++ ((([CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0)] ++ [CSP1;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0)]) ++ ([CSP0;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT] ++ [CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT])) ++ (([(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT] ++ [CT;(COC0 0);CSP0;CS11;CT;CT;(COC0 0);CSP1;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT]) ++ ([CT;CT;(COC0 0);(CSC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CP0;CT;CT;CT;CT;CT] ++ [CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0)])))) ++ (((([CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CP1;(COC0 0);CSP1;CT;CT;CP1] ++ [CT;CT;(COC0 1);(CSC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CS10;(CEC 0);CSP0;(CEC 0);CSP0;CT;CT;CT;CT;CP0;CT;(COC1 0);CSP0;CP1;CT]) ++ ([CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CS10;CS01;CT;CT;CP0;(CEC 0);CSP1;CP0;CS11;CP1;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT] ++ [(COC0 0);CSP1;(COC1 0);CSP1;CT;CT;CT;CP0;CT;CT;CP0;CT;CP0;CT;(COC1 0);CSP1;CT;CT;(COC0 0);CSP1;(COC1 0);CSP0;CS11;CT;CP1;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0)])) ++ (([CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT] ++ [CT;(COC0 0);CSP0;CT;CT;CP0;CT;CT;CT;CP1;CT;CT;(COC0 0);CSP0;CT;CP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS10;CS01;CT;CP0]) ++ ([CT;CP0;CT;CT;CP0;CS10;CS11;CP0;CS11;CP1;CP0;CP0;CS01;CP1;CP0;CS10;CS01;CP1;CP0;CP0;CS01;CP0;CP0;CS00;CS01;CP0;CP0;CS01;CP0;CP0;CS00;CS00] ++ [CS10;CS10;CS01;CP0;CS11;CP0;CS10;CS10;CP1;CP1;CP1;CP0;CS10;CP1;CP0;CS10;CS10;CP0;CS00;CS10;CS01;CP1;CP1;CP1;CP1;CP0;CP1;CP1;CP0;CS10;CP0;CS01]))) ++ ((([CP1;CP0;CP0;CP0;CS01;CP0;CS10;CS00;CS10;CS10;CP1;CP0;CS10;CS10;CS10;CS01;CP0;CS11;CP0;CS11;CP0;CS10;CS10;CP1;CP1;CP1;CP0;CS10;CP1;CP1;CP0;CS10] ++ [CP0;CS00;CS11;CP1;CP0;CS10;CP1;CP1;CP1;CP1;CP1;CP0;CS10;CS01;CP1;CP0;CS10;CS01;CP0;CP1;CP0;CP0;CS00;CS00;CS10;CP1;CP0;CS11;CP0;CS10;CS00;CS11]) ++ ([CP1;CP1;CP1;CP1;CP0;CP1;CP1;CP0;CP0;CS01;CP1;CP1;CP0;CS10;CP0;CS01;CP1;CP1;CP1;CP0;CS10;CS01;CP1;CP0;CP0;CS00;CS00;CP0;CP1;CP0;CS10;CP1] ++ [CP1;CP0;CS10;CP0;CS00;CS11;CP0;CS10;CS11;CP1;CP1;CP1;CP0;CS10;CP1;CP0;CS11;CP0;CP1;CP1;CP1;CP0;CP1;CP1;CP0;CS10;CP0;CS00;CP1;CP0;CS10;CP1])) ++ ([CP1;CP1;CP1;CP1;CP1;CP0;CS10;CP1;CP1;CP1;CP0;CP0;CP1;CP1;CP1;CP1;CP1;CP0;CS11;CP1;CP0;CS10;CS00;CP0;CP1;CP0;CS10;CS11;CP1;CP0;CP0;CP1] ++ [CP0;CS10;CP1;CP0;CS11;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CP0;CP0;CS00;CS11;CP0;CS10;CS01;CP0;CS10;CS01;CP1;CP0]))))
].

Definition z2b_0108 : zW := ((((([WV;WV;WK;WK;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV] ++ [WV;WV;WV;WK;WQ;WV;WV;WQ;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV]) ++ ([WV;WV;WV;WK;WV;WV;WQ;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV] ++ [WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV])) ++ (([WK;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV] ++ [WV;WV;WK;WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV]) ++ ([WK;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WK;WV;WV;WV] ++ [WV;WK;WQ;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV]))) ++ ((([WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK] ++ [WV;WV;WV;WK;WV;WV;WV;WV;WV;WK;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WK;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV]) ++ ([WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV] ++ [WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK])) ++ (([WQ;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WK;WV;WQ;WV;WV;WK;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WV;WV] ++ [WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WK;WV;WV;WV;WK;WV;WV;WV;WK;WV;WV;WV;WV]) ++ ([WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV] ++ [WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV])))) ++ (((([WK;WV;WV;WV;WV;WV;WK;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WK;WV;WV;WV;WV;WK;WV;WV;WK] ++ [WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WK;WV;WV;WQ;WV;WQ;WK]) ++ ([WV;WV;WV;WV;WV;WV;WQ;WV;WQ;WV;WV;WK;WV;WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WQ;WV] ++ [WV;WV;WK;WV;WQ;WV;WQ;WV;WV;WV;WV;WV;WK;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WQ;WV;WV;WQ;WV;WV])) ++ (([WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV] ++ [WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WQ;WK;WV;WV;WV;WV;WV;WV;WV;WQ;WQ;WV;WQ;WV;WV;WV;WK;WV;WV;WQ]) ++ ([WK;WV;WV;WV;WK;WV;WV;WK;WK;WV;WV;WK;WV;WV;WK;WK;WQ;WQ;WK;WV;WQ;WV;WQ;WQ;WV;WV;WV;WV;WQ;WV;WV;WQ] ++ [WQ;WV;WK;WQ;WK;WV;WV;WV;WV;WV;WV;WV;WV;WQ;WV;WK;WV;WV;WV;WV;WK;WV;WQ;WK;WQ;WQ;WV;WV;WQ;WQ;WQ;WK]))) ++ ((([WV;WQ;WV;WQ;WV;WQ;WQ;WV;WV;WV;WV;WQ;WV;WV;WV;WQ;WV;WK;WQ;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WQ;WK;WV;WV] ++ [WQ;WK;WV;WV;WV;WV;WK;WK;WQ;WV;WV;WQ;WV;WQ;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WQ;WV;WK]) ++ ([WV;WV;WV;WV;WQ;WK;WV;WV;WV;WK;WK;WV;WV;WV;WQ;WV;WV;WV;WQ;WV;WK;WQ;WV;WQ;WQ;WV;WV;WV;WV;WQ;WV;WV] ++ [WQ;WV;WV;WV;WV;WV;WV;WV;WV;WQ;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV])) ++ ([WV;WV;WQ;WV;WV;WQ;WK;WV;WV;WV;WQ;WQ;WV;WV;WV;WV;WV;WQ;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WQ] ++ [WV;WQ;WK;WV;WQ;WK;WV;WV])))).

Definition z2c_low_0108 : zW := (((([WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WK;WK;WK;WQ;WQ;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ] ++ [WK;WQ;WQ;WK;WQ;WQ;WQ;WK;WQ;WK;WK;WQ;WQ;WK;WQ;WK;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK;WK;WK;WK;WQ;WK]) ++ ([WK;WQ;WQ;WK;WQ;WK;WK;WK;WK;WK;WK;WK;WK;WQ;WQ;WQ;WK;WK;WK;WQ;WK;WQ;WK;WK;WK;WQ;WK;WK;WQ;WK;WQ;WQ] ++ [WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK;WQ;WQ;WK;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WK;WK;WQ;WQ;WK;WK;WK])) ++ (([WK;WQ;WK;WK;WK;WK;WQ;WK;WQ;WK;WK;WQ;WQ;WK;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK;WQ;WQ;WQ;WQ;WK;WK;WK] ++ [WQ;WQ;WK;WQ;WQ;WQ;WK;WK;WQ;WK;WK;WK;WK;WQ;WK;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK]) ++ ([WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ] ++ [WK;WQ;WQ;WQ;WQ;WQ;WK;WK;WK;WK;WQ;WK;WK;WQ;WK;WQ;WK;WQ;WK;WQ;WQ;WQ;WK;WK;WQ;WK;WK;WQ;WQ;WK;WQ;WK]))) ++ ((([WQ;WK;WK;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WK;WK;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ] ++ [WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WQ;WQ;WK;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ]) ++ ([WK;WQ;WK;WK;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ] ++ [WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WK;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ])) ++ (([WQ;WQ;WK;WK;WQ;WK;WK;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WK;WQ;WQ;WQ;WQ] ++ [WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ]) ++ ([WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WK;WK;WK;WQ] ++ [WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WK;WK;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ])))).

Definition z2c_top_0108 : zW := [WQ;WK;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WK;WK;WQ;WQ;WK;WK].
Definition z2c_0108 : zW := z2c_low_0108 ++ z2c_top_0108.

Lemma z2d_0108 :
  Rounds (zTs z29_0108 0inf) (zTs (zP33 ++ (z2b_0108 ++ (z2c_0108 ++ zTail8))) 0inf).
Proof.
  apply (z25_N z2a_0108 z29_0108 (zP33 ++ (z2b_0108 ++ (z2c_0108 ++ zTail8)))).
  vm_compute; reflexivity.
Qed.

Lemma z2e_0108 : BGood (z2b_0108 ++ (z2c_0108 ++ zTail8)).
Proof.
  apply (z28 z2b_0108 z2c_low_0108 z2c_top_0108); vm_compute; reflexivity.
Qed.

Definition zTail_0108 : zW := [WQ;WQ;WV;WV;WV;WK;WV;WV;WV;WV;WK;WV;WQ;WQ;WK;WQ;WQ;WQ;WK;WQ;WQ;WQ].
Definition zCh_0108 : list Choice := [CP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CP0;CP1;CP0;CP1;CP0].
Definition zBrOut_0108 : zW := ([WV;WV;WV;WK;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WQ;WQ;WQ;WK;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WQ] ++ [WQ]).

Local Open Scope sym_scope.

Definition zCk0_0108 : cconfig := (@nil Sym, @nil Sym, 0, D).
Definition zCk5_0108 : cconfig :=
  ([0; 1],
   (([0;0;0;0;1;1;0;1;0;1;1;0;0;1;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;0;0] ++
     [0;1;1;0;0;1;1;0;0;0;0;0;0;1;1;0;0;1;1;0;0;1;1;0;1;0;1;1;0;0;1;1]) ++
    ([0;0;1;1;0;0;0;0;1;1;0;0;1;1;0;0;1;1;0;0;1;1;0;0;0;0;1;1;0;0;1;0] ++
     [1;0;0;0;1;0;1;0;1;0;0;0;1;0;1;0;1])),
   1, C).

Fixpoint cconfig_steps_pos (m : TM) (p : positive) (x : cconfig) : option cconfig :=
  match p with
  | xH => cconfig_step m x
  | xO p' =>
    match cconfig_steps_pos m p' x with
    | None => None
    | Some x1 => cconfig_steps_pos m p' x1
    end
  | xI p' =>
    match cconfig_step m x with
    | None => None
    | Some x0 =>
      match cconfig_steps_pos m p' x0 with
      | None => None
      | Some x1 => cconfig_steps_pos m p' x1
      end
    end
  end.

Lemma cconfig_steps_pos_spec (m : TM) (p : positive) : forall (x y : cconfig),
  cconfig_steps_pos m p x = Some y ->
  cconfig_to_config x -[ m ]->* cconfig_to_config y.
Proof.
  induction p as [p IH | p IH |]; intros x y H; cbn [cconfig_steps_pos] in H.
  - pose proof (cconfig_step_spec m x) as H0.
    destruct (cconfig_step m x) as [x0 |] eqn:E0; [| discriminate].
    destruct (cconfig_steps_pos m p x0) as [x1 |] eqn:E1; [| discriminate].
    eapply evstep_step; [exact H0 |].
    eapply evstep_trans; [exact (IH x0 x1 E1) | exact (IH x1 y H)].
  - destruct (cconfig_steps_pos m p x) as [x1 |] eqn:E1; [| discriminate].
    eapply evstep_trans; [exact (IH x x1 E1) | exact (IH x1 y H)].
  - pose proof (cconfig_step_spec m x) as H0.
    destruct (cconfig_step m x) as [x0 |] eqn:E0; [| discriminate].
    inversion H; subst; eapply evstep_step; [exact H0 | finish].
Qed.

Definition cconfig_steps_pos_eqb (m : TM) (p : positive) (x y : cconfig) : bool :=
  match cconfig_steps_pos m p x with
  | None => false
  | Some z => cconfig_eqb z y
  end.

Lemma cconfig_steps_pos_eqb_spec (m : TM) (p : positive) (x y : cconfig) :
  cconfig_steps_pos_eqb m p x y = true ->
  cconfig_to_config x -[ m ]->* cconfig_to_config y.
Proof.
  unfold cconfig_steps_pos_eqb.
  destruct (cconfig_steps_pos m p x) as [z |] eqn:E; [| discriminate].
  intros Heq.
  rewrite <- (cconfig_eqb_spec z y Heq).
  exact (cconfig_steps_pos_spec m p x z E).
Qed.

Lemma z0E_0108 : cconfig_to_config zCk0_0108 -[ canon_tm ]->+ zCf (zTs z29_0108 0inf).
Proof.
  assert (h_all : cconfig_to_config zCk0_0108 -[ canon_tm ]->* cconfig_to_config zCk5_0108).
  { apply (cconfig_steps_pos_eqb_spec canon_tm 40537%positive zCk0_0108 zCk5_0108).
    vm_compute; reflexivity. }
  assert (heq : cconfig_to_config zCk5_0108 =
      zCL lh (w_pre *> ((d0 ++ t ++ (t ++ one)) *> zTs zTail_0108 0inf)))
    by solve_const0_eq.
  rewrite heq in h_all.
  assert (h_br0 : BRIncs false (N.to_nat 64%N) (zTs (zTail_0108 ++ [WK]) 0inf) (zTs zBrOut_0108 0inf)).
  { apply (z21_N zCh_0108 false 64%N (zTail_0108 ++ [WK]) zBrOut_0108).
    vm_compute; reflexivity. }
  change (N.to_nat 64%N) with 64%nat in h_br0.
  rewrite z0S in h_br0; cbn [zTs] in h_br0; rewrite zDd in h_br0.
  pose proof (z2o h_br0 [] ([cj] ++ [ch] ^^ 31%nat) (Num_even 31%nat)) as h_side31.
  cbn [Str_app] in h_side31.
  pose proof (zSc z108_seg h_side31) as h_side16.
  pose proof (zW_pre_full h_side16) as h_turn.
  assert (h_out : (d0 ++ t ++ t) *> zTs zBrOut_0108 0inf = zTs z29_0108 0inf) by reflexivity.
  rewrite h_out in h_turn.
  eapply evstep_progress_trans; [exact h_all | exact h_turn].
Qed.

Lemma nonhalt_canon : ~ halts canon_tm (cconfig_to_config zCk0_0108).
Proof.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [apply progress_evstep; exact z0E_0108 | exact (z2r z2d_0108)].
  - apply (progress_nonhalt_cond canon_tm zW
      (z2b_0108 ++ (z2c_0108 ++ zTail8))
      (fun w => zCf (zTs (zP33 ++ w) 0inf))
      BGood).
    + intros w hGood.
      destruct (z1N hGood) as [w' [hStep hGood']].
      exists w'; split; [exact (z2q hStep) | exact hGood'].
    + exact z2e_0108.
Qed.

Definition zStInv (q : Q) : Q :=
  match q with
  | A => D
  | B => F
  | C => E
  | D => A
  | E => B
  | F => C
  end.

Lemma perm_flip_canon : Perm (flip tm) canon_tm zStInv.
Proof.
  split.
  - intros [] [] H; vm_compute in H |- *; congruence.
  - intros [] [] s' d q' H; vm_compute in H |- *; inversion H; subst; reflexivity.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  intros H.
  apply flip_halts in H.
  exact (perm_nonhalt (flip tm) canon_tm zStInv A tape0 perm_flip_canon nonhalt_canon H).
Qed.

Print Assumptions nonhalt.
