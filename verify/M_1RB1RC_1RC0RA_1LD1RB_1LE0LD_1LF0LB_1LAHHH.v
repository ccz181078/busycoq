From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import micromega.Lia.
From Coq Require Import QArith.QArith.
From Coq Require Import micromega.Lqa.
Notation Rat := QArith_base.Q.

From BusyCoq Require Import Individual62.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm : TM := Eval compute in (TM_from_str "1RB1RC_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LA---"%string).
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

(* Stage 2: Word, BRIncs, Num, z2f..z2p, Binary, zPr, zDg, Weights, zHn *)

Inductive Word : Type := WV | WK | WQ.

Definition word_eqb (x y : Word) : bool :=
  match x, y with
  | WV, WV | WK, WK | WQ, WQ => true
  | _, _ => false
  end.

Lemma word_eqb_spec (x y : Word) : word_eqb x y = true <-> x = y.
Proof. destruct x, y; cbn; split; intros H; congruence. Qed.

Definition zW := list Word.
Definition zR (n : nat) (w : Word) : zW := repeat w n.

Fixpoint zQK (r : nat) (u : zW) : zW :=
  match r with
  | O => u
  | S r' => WQ :: WK :: zQK r' u
  end.

Lemma zQK_append (r : nat) (u v : zW) :
    zQK r (u ++ v) = zQK r u ++ v.
Proof.
  induction r as [| r IH]; [reflexivity | cbn; rewrite IH; reflexivity].
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
  induction u as [| a u IH]; [reflexivity | destruct a; cbn [app zTs]; rewrite IH; reflexivity].
Qed.

Lemma zTs_R (r_ch : nat) (r : side) :
    zTs (zR r_ch WV) r = (t ^^ r_ch) *> r.
Proof.
  induction r_ch as [| r_ch IH]; [reflexivity |].
  change (zR (S r_ch) WV) with (WV :: zR r_ch WV).
  cbn [zTs lpow].
  rewrite IH, Str_app_assoc.
  reflexivity.
Qed.

Lemma zTs_QK (r_ch : nat) (r : side) :
    zTs (zQK r_ch [WV]) r = ((d1 ++ d0) ^^ r_ch ++ [1; 1]) *> (d0 *> r).
Proof.
  induction r_ch as [| r_ch IH].
  - reflexivity.
  - cbn [zQK zTs lpow].
    rewrite IH.
    reflexivity.
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
  inversion hN as [| m Hk | m Hk | ]; subst w hs; try lia.
  - cbn [Str_app].
    destruct m as [| m]; [lia |].
    change (S m) with (1 + m).
    refine (zSc (z0m m) _).
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch] ^^ (1 + m * 2))).
    { replace (1 + n * 2) with (1 + (1 + m * 2) * 2) by lia.
      exact (Num_odd (1 + m * 2)). }
    exact (hI [] _ hN1).
  - cbn [Str_app].
    refine (zSc (z0n m) _).
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch] ^^ (m * 2))).
    { replace (1 + n * 2) with (1 + (m * 2) * 2) by lia.
      exact (Num_odd (m * 2)). }
    exact (hI [] _ hN1).
Qed.

Lemma z2i_p0 {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f false (1 + n) (d1 *> (d0 *> r)) (t *> r').
Proof.
  intros w hs hN.
  inversion hN as [| m Hk | m Hk | ]; subst w hs; try lia.
  - cbn [Str_app].
    rewrite <- (Str_app_assoc d1 d0 r).
    destruct m as [| m].
    + assert (hn0 : (n * 2 = 0)%nat) by lia.
      rewrite hn0 in hI.
      pose proof (z2g hI) as hr'; subst r'.
      rewrite <- (Str_app_assoc t one r).
      exact (zSc z0e (Side_nil r)).
    + change (S m) with (1 + m).
      refine (zSc (z0o m) _).
      assert (hN2 : Num false (n * 2) [] ([cj] ++ [ch] ^^ (1 + m * 2))).
      { replace (n * 2) with (2 + (1 + m * 2) * 2) by lia.
        exact (Num_even (1 + m * 2)). }
      exact (hI [] _ hN2).
  - cbn [Str_app].
    rewrite <- (Str_app_assoc d1 d0 r).
    refine (zSc (z0p m) _).
    assert (hN2 : Num false (n * 2) [] ([cj] ++ [ch] ^^ (m * 2))).
    { replace (n * 2) with (2 + (m * 2) * 2) by lia.
      exact (Num_even (m * 2)). }
    exact (hI [] _ hN2).
Qed.

Lemma z2j {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f false (1 + n) (d1 *> (d1 *> r)) (t *> r').
Proof.
  intros w hs hN.
  inversion hN as [| m Hk | m Hk | ]; subst w hs; try lia.
  - cbn [Str_app].
    rewrite <- (Str_app_assoc d1 d1 r).
    refine (zSc (z0q m) _).
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch] ^^ (m * 2))).
    { replace (1 + n * 2) with (1 + (m * 2) * 2) by lia.
      exact (Num_odd (m * 2)). }
    exact (hI [] _ hN1).
  - cbn [Str_app].
    rewrite <- (Str_app_assoc d1 d1 r).
    refine (zSc (z0r m) _).
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch] ^^ (1 + m * 2))).
    { replace (1 + n * 2) with (1 + (1 + m * 2) * 2) by lia.
      exact (Num_odd (1 + m * 2)). }
    exact (hI [] _ hN1).
Qed.

Lemma z2k {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f false (2 + n * 4) (d0 *> r) (d0 *> r').
Proof.
  intros w hs hN.
  inversion hN as [| m Hk | m Hk | ]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = n * 2) by lia; subst m.
  destruct n as [| n].
  - pose proof (z2g hI) as hr'; subst r'.
    rewrite <- (Str_app_assoc d0 one r).
    exact (zSc z0i (Side_nil r)).
  - replace (S n * 2) with (2 + n * 2) by lia.
    refine (zSc (z0s n) _).
    assert (hN2 : Num false (S n * 2) [] ([cj] ++ [ch] ^^ n)).
    { replace (S n * 2) with (2 + n * 2) by lia.
      exact (Num_even n). }
    exact (hI [] _ hN2).
Qed.

Lemma z2l {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f false (2 + n * 4) (d1 *> r) (d0 *> r').
Proof.
  intros w hs hN.
  inversion hN as [| m Hk | m Hk | ]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = n * 2) by lia; subst m.
  refine (zSc (z0t n) _).
  exact (hI [] _ (Num_odd n)).
Qed.

Lemma z2m {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f false (4 + n * 4) (d0 *> r) (d1 *> r').
Proof.
  intros w hs hN.
  inversion hN as [| m Hk | m Hk | ]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = 1 + n * 2) by lia; subst m.
  destruct n as [| n].
  - pose proof (z2g hI) as hr'; subst r'.
    rewrite <- (Str_app_assoc d1 one r).
    exact (zSc z0u (Side_nil r)).
  - replace (1 + S n * 2) with (3 + n * 2) by lia.
    refine (zSc (z0v n) _).
    assert (hN2 : Num false (S n * 2) [] ([cj] ++ [ch] ^^ n)).
    { replace (S n * 2) with (2 + n * 2) by lia.
      exact (Num_even n). }
    exact (hI [] _ hN2).
Qed.

Lemma z2n {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f false (4 + n * 4) (d1 *> r) (d1 *> r').
Proof.
  intros w hs hN.
  inversion hN as [| m Hk | m Hk | ]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = 1 + n * 2) by lia; subst m.
  refine (zSc (z0w n) _).
  exact (hI [] _ (Num_odd n)).
Qed.

Lemma z2_oc0 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
    z2f false (3 + m * 4) (zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR r_ch WV) r').
Proof.
  intros w hs hN.
  inversion hN as [| n Hk | n Hk | ]; subst w hs; try lia.
  cbn [Str_app].
  assert (hn : n = 1 + m * 2) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 (t ^^ r_ch) r').
  assert (h_seg : Seg ([cp] ++ [ch] ^^ (1 + m * 2)) ([ch; cp] ++ [ch] ^^ (m * 2 ^ r_ch))
      ((d1 ++ d0) ^^ r_ch ++ [1; 1]) (d0 ++ t ^^ r_ch)).
  { change ([cp] ++ [ch] ^^ (1 + m * 2)) with ([cp; ch] ++ [ch] ^^ (m * 2)).
    exact (zSg (zOdd_base r_ch) (zS0 (zH_d0_even m) (zT_pow r_ch m))). }
  refine (zSc h_seg _).
  assert (h_num : Num true (1 + m * 2 ^ (1 + r_ch)) d0 ([ch; cp] ++ [ch] ^^ (m * 2 ^ r_ch))).
  { replace (1 + m * 2 ^ (1 + r_ch)) with (1 + (m * 2 ^ r_ch) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ r_ch)). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_oc1 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
    z2f false (5 + m * 4) (zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR r_ch WV) r').
Proof.
  intros w hs hN.
  inversion hN as [| n Hk | n Hk | ]; subst w hs; try lia.
  cbn [Str_app].
  assert (hn : n = 1 + (1 + m * 2)) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d1 (t ^^ r_ch) r').
  assert (h_seg : Seg ([cp] ++ [ch] ^^ (1 + (1 + m * 2))) ([ch; cp] ++ [ch] ^^ (m * 2 ^ r_ch))
      ((d1 ++ d0) ^^ r_ch ++ [1; 1]) (d1 ++ t ^^ r_ch)).
  { change ([cp] ++ [ch] ^^ (1 + (1 + m * 2))) with ([cp; ch] ++ [ch] ^^ (1 + m * 2)).
    exact (zSg (zOdd_base r_ch) (zS0 (zH_d0_odd m) (zT_pow r_ch m))). }
  refine (zSc h_seg _).
  assert (h_num : Num true (1 + m * 2 ^ (1 + r_ch)) d0 ([ch; cp] ++ [ch] ^^ (m * 2 ^ r_ch))).
  { replace (1 + m * 2 ^ (1 + r_ch)) with (1 + (m * 2 ^ r_ch) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ r_ch)). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_ec (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) r r') :
    z2f false (6 + m * 2) (d0 *> zTs (zQK r_ch [WV]) r) (zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN.
  inversion hN as [| n Hk | n Hk | ]; subst w hs; try lia.
  cbn [Str_app].
  assert (hn : n = 1 + (1 + m)) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 ((d1 ++ d0) ^^ r_ch ++ [1; 1]) (d0 *> r)).
  assert (h_seg : Seg ([cj] ++ [ch] ^^ (1 + (1 + m))) ([ch; cp] ++ [ch] ^^ ((1 + m * 2) * 2 ^ r_ch))
      (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1])) (t ^^ (1 + r_ch))).
  { assert (h1 : Seg [cj; ch; ch] ([ch; cp] ++ [ch] ^^ (2 ^ r_ch)) (d0 ++ ((d1 ++ d0) ^^ r_ch ++ [1; 1])) (t ^^ (1 + r_ch)))
      by exact (zEven_base r_ch).
    pose proof (zSg h1 (zT_pow (1 + r_ch) m)) as h3.
    change ([cj; ch; ch] ++ [ch] ^^ m) with ([cj] ++ [ch] ^^ (1 + (1 + m))) in h3.
    assert (heq_out : ([ch; cp] ++ [ch] ^^ (2 ^ r_ch)) ++ [ch] ^^ (m * 2 ^ (1 + r_ch)) =
        [ch; cp] ++ [ch] ^^ ((1 + m * 2) * 2 ^ r_ch)).
    { rewrite <- app_assoc, <- (z07 [ch]).
      f_equal; f_equal.
      cbn [Nat.add Nat.pow]; lia. }
    rewrite heq_out in h3.
    exact h3. }
  refine (zSc h_seg _).
  assert (h_num : Num true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) d0 ([ch; cp] ++ [ch] ^^ ((1 + m * 2) * 2 ^ r_ch))).
  { replace (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) with (1 + ((1 + m * 2) * 2 ^ r_ch) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift ((1 + m * 2) * 2 ^ r_ch)). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_sp0 {n : nat} {r r' : side}
    (hI : z2f false (n * 2) r r') : z2f true (1 + n) (d0 *> r) (t *> r').
Proof.
  intros w hs hN.
  inversion hN as [| | | m Hk]; subst w hs.
  assert (hn : n = m * 2) by lia; subst n.
  rewrite <- (Str_app_assoc d0 d0 r).
  destruct m as [| m].
  - change (0 * 2 * 2)%nat with 0%nat in hI.
    pose proof (z2g hI) as hr'; subst r'.
    rewrite <- (Str_app_assoc t one r).
    assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ 0%nat) [] (d0 ++ d0) (t ++ one)).
    { cbn [lpow app].
      exact (zSg (zS0 zH0 (z0a d0)) z0e). }
    exact (zSc h_seg (Side_nil r)).
  - change (S m) with (1 + m) in hI |- *.
    assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ (1 + m)) ([cj] ++ [ch] ^^ (1 + m * 2)) (d0 ++ d0) t).
    { change ([ch; cp] ++ [ch] ^^ (1 + m)) with ([ch] ++ ([cp] ++ [ch] ^^ (1 + m))).
      exact (zSg (zS0 zH0 (z0a d0)) (z0o m)). }
    refine (zSc h_seg _).
    assert (hN2 : Num false ((1 + m) * 2 * 2) [] ([cj] ++ [ch] ^^ (1 + m * 2))).
    { replace ((1 + m) * 2 * 2) with (2 + (1 + m * 2) * 2) by lia.
      exact (Num_even (1 + m * 2)). }
    exact (hI [] _ hN2).
Qed.

Lemma z2_sp1 {n : nat} {r r' : side}
    (hI : z2f false (1 + n * 2) r r') : z2f true (1 + n) (d1 *> r) (t *> r').
Proof.
  intros w hs hN.
  inversion hN as [| | | m Hk]; subst w hs.
  assert (hn : n = m * 2) by lia; subst n.
  rewrite <- (Str_app_assoc d0 d1 r).
  assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ m) ([cp] ++ [ch] ^^ (m * 2)) (d0 ++ d1) t).
  { change ([ch; cp] ++ [ch] ^^ m) with ([ch] ++ ([cp] ++ [ch] ^^ m)).
    exact (zSg (zS0 zH0 (z0a d1)) (z0q m)). }
  refine (zSc h_seg _).
  assert (hN1 : Num false (1 + m * 2 * 2) [] ([cp] ++ [ch] ^^ (m * 2))).
  { replace (1 + m * 2 * 2) with (1 + (m * 2) * 2) by lia.
    exact (Num_odd (m * 2)). }
  exact (hI [] _ hN1).
Qed.

Lemma z2_sc0 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
    z2f true (3 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN.
  inversion hN as [| | | n Hk]; subst w hs.
  assert (hn : n = 1 + m * 2) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 (t ^^ (1 + r_ch)) r').
  assert (h_in : d0 *> (d0 *> (((d1 ++ d0) ^^ r_ch ++ [1; 1]) *> (d0 *> r))) =
      (d0 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])) *> (d0 *> r)) by reflexivity.
  rewrite h_in.
  assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ (1 + m * 2)) ([ch; cp] ++ [ch] ^^ (m * 2 ^ (1 + r_ch)))
      (d0 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])) (d0 ++ t ^^ (1 + r_ch))).
  { assert (h0 : Seg [ch] [] (d0 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])) ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1])).
    { change ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1]) with (d1 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])).
      exact (zS0 zH0 (z0a (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1]))). }
    pose proof (zOdd_base (1 + r_ch)) as h1.
    pose proof (zS0 (zH_d0_even m) (zT_pow (1 + r_ch) m)) as h2.
    change ([ch; cp] ++ [ch] ^^ (1 + m * 2)) with ([ch] ++ ([cp; ch] ++ [ch] ^^ (m * 2))).
    exact (zSg h0 (zSg h1 h2)). }
  refine (zSc h_seg _).
  assert (h_num : Num true (1 + m * 2 ^ (2 + r_ch)) d0 ([ch; cp] ++ [ch] ^^ (m * 2 ^ (1 + r_ch)))).
  { replace (1 + m * 2 ^ (2 + r_ch)) with (1 + (m * 2 ^ (1 + r_ch)) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ (1 + r_ch))). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_sc1 (r_ch : nat) {m : nat} {r r' : side}
    (hI : z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
    z2f true (5 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN.
  inversion hN as [| | | n Hk]; subst w hs.
  assert (hn : n = 1 + (1 + m * 2)) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d1 (t ^^ (1 + r_ch)) r').
  assert (h_in : d0 *> (d0 *> (((d1 ++ d0) ^^ r_ch ++ [1; 1]) *> (d0 *> r))) =
      (d0 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])) *> (d0 *> r)) by reflexivity.
  rewrite h_in.
  assert (h_seg : Seg ([ch; cp] ++ [ch] ^^ (1 + (1 + m * 2))) ([ch; cp] ++ [ch] ^^ (m * 2 ^ (1 + r_ch)))
      (d0 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])) (d1 ++ t ^^ (1 + r_ch))).
  { assert (h0 : Seg [ch] [] (d0 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])) ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1])).
    { change ((d1 ++ d0) ^^ (1 + r_ch) ++ [1; 1]) with (d1 ++ (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1])).
      exact (zS0 zH0 (z0a (d0 ++ (d1 ++ d0) ^^ r_ch ++ [1; 1]))). }
    pose proof (zOdd_base (1 + r_ch)) as h1.
    pose proof (zS0 (zH_d0_odd m) (zT_pow (1 + r_ch) m)) as h2.
    change ([ch; cp] ++ [ch] ^^ (1 + (1 + m * 2))) with ([ch] ++ ([cp; ch] ++ [ch] ^^ (1 + m * 2))).
    exact (zSg h0 (zSg h1 h2)). }
  refine (zSc h_seg _).
  assert (h_num : Num true (1 + m * 2 ^ (2 + r_ch)) d0 ([ch; cp] ++ [ch] ^^ (m * 2 ^ (1 + r_ch)))).
  { replace (1 + m * 2 ^ (2 + r_ch)) with (1 + (m * 2 ^ (1 + r_ch)) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ (1 + r_ch))). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2o {s : bool} {k : nat} {r r' : side} (hI : BRIncs s k r r') :
    z2f s k r r'.
Proof.
  induction hI.
  - intros w hs hN; inversion hN; subst; try lia; exact (Side_nil (one *> r)).
  - exact (z2h IHhI).
  - exact (z2i_p0 IHhI).
  - exact (z2j IHhI).
  - exact (z2k IHhI).
  - exact (z2l IHhI).
  - exact (z2m IHhI).
  - exact (z2n IHhI).
  - exact (z2_oc0 r_ch IHhI).
  - exact (z2_oc1 r_ch IHhI).
  - exact (z2_ec r_ch IHhI).
  - exact (z2_sp0 IHhI).
  - exact (z2_sp1 IHhI).
  - exact (z2_sc0 r_ch IHhI).
  - exact (z2_sc1 r_ch IHhI).
Qed.

Lemma z2p {r r' : side} (hI : BRIncs false 128 r r') :
    zCf r -[ canon_tm ]->+ zCf (zTs [WV; WV; WQ; WV] r').
Proof.
  pose proof (z2o hI [] ([cj] ++ [ch] ^^ 63) (Num_even 63)) as hC.
  cbn [Str_app] in hC.
  pose proof (zW_full hC) as hW.
  assert (heq : (t ++ t ++ d1 ++ t) *> r' = zTs [WV; WV; WQ; WV] r') by reflexivity.
  rewrite <- heq.
  exact hW.
Qed.

(* Section 7A: Binary, Digits (zDg), Weights (z0Y..z11, z0W), z0L, zHn *)

Local Open Scope nat_scope.

Inductive Binary : nat -> nat -> side -> Prop :=
  | Binary_one : Binary 1 1 (d1 *> 0inf)
  | Binary_zero {n H : nat} {r : side} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 *> r)
  | Binary_two {n H : nat} {r : side} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 *> r).

Lemma zPp (n : nat) : 0 < 2 ^ n.
Proof. induction n as [| n IH]; cbn [Nat.pow]; lia. Qed.

Lemma zP2 (n : nat) : 2 ^ (1 + n) = 2 ^ n + 2 ^ n.
Proof. cbn [Nat.add Nat.pow]; lia. Qed.

Lemma z0F (n : nat) : (exists a, n = a * 2) \/ (exists a, n = 1 + a * 2).
Proof.
  induction n as [| n [[a Ha] | [a Ha]]].
  - left; exists 0; lia.
  - right; exists a; lia.
  - left; exists (S a); lia.
Qed.

Lemma z0H {A H : nat} {r : side} (h : Binary A H r) :
    BRIncs false ((A - 1) * 2) 0inf r.
Proof.
  induction h as [| n H r _ IH | n H r _ IH].
  - change ((1 - 1) * 2) with 0.
    pose proof (BRIncs_zero 0inf) as h0.
    assert (hd : d1 *> 0inf = one *> 0inf) by solve_const0_eq.
    rewrite hd; exact h0.
  - replace ((1 + n - 1) * 2) with (n * 2) in IH by lia.
    pose proof (BRIncs_short00 IH) as hs.
    rewrite zDd in hs.
    replace ((2 + n * 2 - 1) * 2) with (2 + n * 4) by lia.
    exact hs.
  - replace ((1 + n - 1) * 2) with (n * 2) in IH by lia.
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
  inversion h; subst.
  - exact (zPr_nil true).
  - exact (zPr_T true H).
  - exact (zPr_pair0 true H).
  - exact (zPr_pair1 true H).
Qed.

Lemma z0J (u : zW) :
    zPr true u /\ (zPr false u \/ zPr false (WQ :: u)).
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
Proof. inversion h. Qed.

Lemma zD0 {A H : nat} {u : zW} (h : zDg A H (WK :: u)) :
    exists A' H', zDg A' H' u /\ A = A' * 2 /\ H = 1 + H'.
Proof.
  inversion h as [| A' H' u' hD | ]; subst.
  exists A', H'; auto.
Qed.

Lemma zD1 {A H : nat} {u : zW} (h : zDg A H (WQ :: u)) :
    exists A' H', zDg A' H' u /\ A = 1 + A' * 2 /\ H = 1 + H'.
Proof.
  inversion h as [| | A' H' u' hD ]; subst.
  exists A', H'; auto.
Qed.

Lemma z0T (H : nat) : forall A, A < 2 ^ H -> exists u, zDg A H u.
Proof.
  induction H as [| H IH]; intros A hA.
  - cbn [Nat.pow] in hA.
    assert (A = 0) by lia; subst A.
    exists ([] : zW); exact zDg_nil.
  - cbn [Nat.pow] in hA.
    destruct (z0F A) as [[a rfl_a] | [a rfl_a]]; subst A.
    + destruct (IH a ltac:(lia)) as [u hI].
      exists (WK :: u); exact (zDg_zero hI).
    + destruct (IH a ltac:(lia)) as [u hI].
      exists (WQ :: u); exact (zDg_one hI).
Qed.

Lemma z0U {A H : nat} {u : zW} (h1 : zDg A H u) :
    forall {B J : nat} {v : zW}, zDg B J v -> zDg (A + B * 2 ^ H) (H + J) (u ++ v).
Proof.
  induction h1 as [| A H u _ IH | A H u _ IH]; intros B J v h2.
  - cbn [Nat.pow Nat.add app].
    replace (B * 1) with B by lia.
    exact h2.
  - pose proof (zDg_zero (IH B J v h2)) as h3.
    replace ((A + B * 2 ^ H) * 2) with (A * 2 + B * 2 ^ (1 + H)) in h3
      by (rewrite zP2; lia).
    exact h3.
  - pose proof (zDg_one (IH B J v h2)) as h3.
    replace (1 + (A + B * 2 ^ H) * 2) with ((1 + A * 2) + B * 2 ^ (1 + H)) in h3
      by (rewrite zP2; lia).
    exact h3.
Qed.

Lemma z0W_lt {A H : nat} {u : zW} (h : zDg A H u) : A < 2 ^ H.
Proof.
  induction h as [| A H u _ IH | A H u _ IH]; [cbn; lia | rewrite zP2; lia | rewrite zP2; lia].
Qed.

Lemma z0X {A H : nat} {u : zW} (h1 : zDg A H u) :
    forall {v : zW}, zDg A H v -> u = v.
Proof.
  induction h1 as [| A H u _ IH | A H u _ IH]; intros v h2.
  - inversion h2; subst; try lia; reflexivity.
  - inversion h2 as [| A' H' v' hD | ]; subst; try lia.
    assert (A = A') by lia; subst A'.
    f_equal; exact (IH v' hD).
  - inversion h2 as [| | A' H' v' hD ]; subst; try lia.
    assert (A = A') by lia; subst A'.
    f_equal; exact (IH v' hD).
Qed.

Fixpoint z0L (u : zW) : bool :=
  match u with
  | [] => false
  | WQ :: (WK :: _ as v) => true
  | WQ :: (WQ :: _ as v) => true
  | _ :: v => z0L v
  end.

Lemma z1I (u v : zW) (h : z0L v = true) : z0L (u ++ v) = true.
Proof.
  induction u as [| w u IH]; [exact h |].
  destruct w; [exact IH | exact IH |].
  destruct u as [| w2 u'].
  - destruct v as [| w2 v']; [discriminate |].
    destruct w2; cbn in h |- *; [exact h | reflexivity | reflexivity].
  - destruct w2; [exact IH | reflexivity | reflexivity].
Qed.

Lemma zDg_pos_z0L {A H : nat} {w : zW} (hD : zDg A H w) (hPos : 0 < A) :
    z0L (w ++ [WK]) = true.
Proof.
  induction hD as [| A1 H1 u1 _ IH | A1 H1 u1 hDu _].
  - lia.
  - exact (IH ltac:(lia)).
  - inversion hDu; reflexivity.
Qed.

(* Rational weights and Qnat helpers *)

Local Open Scope Q_scope.

Definition Qnat (n : nat) : Rat := inject_Z (Z.of_nat n).

Lemma Qnat_0 : Qnat 0 == 0. Proof. reflexivity. Qed.
Lemma Qnat_1 : Qnat 1 == 1. Proof. reflexivity. Qed.
Lemma Qnat_S (n : nat) : Qnat (S n) == Qnat n + 1.
Proof. unfold Qnat; rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus; reflexivity. Qed.
Lemma Qnat_add (a b : nat) : Qnat (a + b) == Qnat a + Qnat b.
Proof. unfold Qnat; rewrite Nat2Z.inj_add, inject_Z_plus; reflexivity. Qed.
Lemma Qnat_mul (a b : nat) : Qnat (a * b) == Qnat a * Qnat b.
Proof. unfold Qnat; rewrite Nat2Z.inj_mul, inject_Z_mult; reflexivity. Qed.
Lemma Qnat_nonneg (n : nat) : 0 <= Qnat n.
Proof. unfold Qnat, Qle; cbn; lia. Qed.
Lemma Qnat_le_iff (a b : nat) : (a <= b)%nat <-> Qnat a <= Qnat b.
Proof. unfold Qnat, Qle; cbn; lia. Qed.
Lemma Qnat_lt_iff (a b : nat) : (a < b)%nat <-> Qnat a < Qnat b.
Proof. unfold Qnat, Qlt; cbn; lia. Qed.
Lemma Qnat_eq_iff (a b : nat) : a = b <-> Qnat a == Qnat b.
Proof. unfold Qnat, Qeq; cbn; lia. Qed.
Lemma Qnat_pow2_S (n : nat) : Qnat (2 ^ S n) == Qnat (2 ^ n) * 2.
Proof.
  replace (2 ^ S n)%nat with (2 ^ n * 2)%nat by (cbn [Nat.pow]; lia).
  rewrite Qnat_mul; reflexivity.
Qed.
Lemma Qnat_pow2_1_add (n : nat) : Qnat (2 ^ (1 + n)) == Qnat (2 ^ n) * 2.
Proof. apply Qnat_pow2_S. Qed.

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
  induction u as [| a u [h1 [h2 [h3 h4]]]]; [cbn; repeat split; lra |].
  destruct a; cbn [z0Y z0Z z10 z0W]; repeat split; lra.
Qed.

Lemma zWY (u : zW) : z0Y u <= z0W u /\ z0W u <= (11#8) * z0Y u.
Proof.
  induction u as [| a u [h1 h2]]; [cbn; split; lra |].
  destruct a; cbn [z0Y z0W]; split; lra.
Qed.

Lemma z12 (u : zW) : z0Y u == z0Z u + z10 u.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [z0Y z0Z z10]; rewrite IH; ring.
Qed.

Lemma zSp (u : zW) : 0 < z11 u.
Proof.
  induction u as [| a u IH]; [cbn; lra |].
  destruct a; cbn [z11]; lra.
Qed.

Lemma z13 (u v : zW) : z0Y (u ++ v) == z0Y u + z11 u * z0Y v.
Proof.
  induction u as [| a u IH]; [cbn [app z0Y z11]; ring |].
  destruct a; cbn [app z0Y z11]; rewrite IH; ring.
Qed.

Lemma z13W (u v : zW) : z0W (u ++ v) == z0W u + z11 u * z0W v.
Proof.
  induction u as [| a u IH]; [cbn [app z0W z11]; ring |].
  destruct a; cbn [app z0W z11]; rewrite IH; ring.
Qed.

Lemma z14 (u v : zW) : z0Z (u ++ v) == z0Z u + z11 u * z0Z v.
Proof.
  induction u as [| a u IH]; [cbn [app z0Z z11]; ring |].
  destruct a; cbn [app z0Z z11]; rewrite IH; ring.
Qed.

Lemma z15 (u v : zW) : z10 (u ++ v) == z10 u + z11 u * z10 v.
Proof.
  induction u as [| a u IH]; [cbn [app z10 z11]; ring |].
  destruct a; cbn [app z10 z11]; rewrite IH; ring.
Qed.

Lemma z16 (u v : zW) : z11 (u ++ v) == z11 u * z11 v.
Proof.
  induction u as [| a u IH]; [cbn [app z11]; ring |].
  destruct a; cbn [app z11]; rewrite IH; ring.
Qed.

Lemma zDw {A H : nat} {u : zW} (h : zDg A H u) :
    z11 u == Qnat (2 ^ H) /\ z0Y u + 1 == Qnat (2 ^ H) /\ z10 u == Qnat A.
Proof.
  induction h as [| A H u _ [h1 [h2 h3]] | A H u _ [h1 [h2 h3]]].
  - cbn [z11 z0Y z10 Nat.pow]; repeat split; reflexivity.
  - cbn [z11 z0Y z10].
    rewrite Qnat_pow2_1_add, Qnat_mul; change (Qnat 2) with 2.
    repeat split; lra.
  - cbn [z11 z0Y z10].
    rewrite Qnat_pow2_1_add, Qnat_add, Qnat_mul; change (Qnat 1) with 1; change (Qnat 2) with 2.
    repeat split; lra.
Qed.

Lemma z17 {A H : nat} {u : zW} (h : zDg A H u) :
    z0Z u + Qnat A + 1 == Qnat (2 ^ H).
Proof.
  destruct (zDw h) as [h1 [h2 h3]].
  pose proof (z12 u) as hm.
  lra.
Qed.

Fixpoint zHn (u : zW) (h : nat) : option nat :=
  match u, h with
  | [], h => Some h
  | WV :: u', h => zHn u' (h + 1)
  | _ :: _, O => None
  | _ :: u', S h' => zHn u' h'
  end.

Lemma z1x (u : zW) :
    forall (h H : nat), zHn u h = Some H ->
      z11 u * Qnat (2 ^ H) == Qnat (2 ^ h).
Proof.
  induction u as [| w u IH]; intros h H hE.
  - cbn in hE; inversion hE; subst H; cbn [z11]; ring.
  - destruct w.
    + cbn [zHn z11] in hE |- *.
      pose proof (IH (h + 1)%nat H hE) as hIH.
      replace (h + 1)%nat with (S h) in hIH by lia.
      rewrite Qnat_pow2_S in hIH.
      lra.
    + destruct h as [| h]; [discriminate |].
      cbn [zHn z11] in hE |- *.
      pose proof (IH h H hE) as hIH.
      rewrite Qnat_pow2_S.
      lra.
    + destruct h as [| h]; [discriminate |].
      cbn [zHn z11] in hE |- *.
      pose proof (IH h H hE) as hIH.
      rewrite Qnat_pow2_S.
      lra.
Qed.

Lemma z1B (u : zW) :
    forall (h : nat), z0Y u < Qnat (2 ^ h) -> exists H, zHn u h = Some H.
Proof.
  induction u as [| w u IH]; intros h hM.
  - exists h; reflexivity.
  - destruct w.
    + cbn [z0Y zHn] in hM |- *.
      apply (IH (h + 1)%nat).
      replace (h + 1)%nat with (S h) by lia.
      rewrite Qnat_pow2_S; lra.
    + destruct h as [| h].
      * pose proof (proj1 (zWn u)) as hw.
        cbn [z0Y Nat.pow] in hM; change (Qnat 1) with 1 in hM; lra.
      * cbn [z0Y zHn] in hM |- *.
        apply (IH h).
        rewrite Qnat_pow2_S in hM; lra.
    + destruct h as [| h].
      * pose proof (proj1 (zWn u)) as hw.
        cbn [z0Y Nat.pow] in hM; change (Qnat 1) with 1 in hM; lra.
      * cbn [z0Y zHn] in hM |- *.
        apply (IH h).
        rewrite Qnat_pow2_S in hM; lra.
Qed.

Lemma z1K {n H : nat} {ds : zW} (hD : zDg (1 + n * 4) H ds) (hH : (2 <= H)%nat) :
    exists w, ds = WQ :: WK :: w.
Proof.
  inversion hD as [| | A1 H1 u1 hD1 ]; subst; try lia.
  assert (A1 = (n * 2)%nat) by lia; subst A1.
  inversion hD1 as [| A2 H2 w _ | ]; subst; try lia.
  exists w; reflexivity.
Qed.


(* Stage 3 Part A: Section 7B (Scan) and Section 7C (BScan, z1i, z1j, z1k) *)

Ltac push_Qnat_all :=
  repeat rewrite ?Qnat_add, ?Qnat_mul in *;
  change (Qnat 0) with 0 in *;
  change (Qnat 1) with 1 in *;
  change (Qnat 2) with 2 in *;
  change (Qnat 3) with 3 in *;
  change (Qnat 4) with 4 in *;
  change (Qnat 5) with 5 in *;
  change (Qnat 6) with 6 in *;
  change (Qnat 8) with 8 in *.

Inductive Scan : nat -> zW -> nat -> zW -> Rat -> Prop :=
  | Scan_nil (k : nat) : Scan k [] k [] 0
  | Scan_T {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan ((1 + n) * 2) u k v l -> Scan (1 + n) (WV :: u) k (WV :: v) (l * (1#2))
  | Scan_pair0 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (1 + n) (WQ :: WK :: u) k (WV :: v) ((1 + l) * (1#2))
  | Scan_pair1 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (1 + n) (WQ :: WQ :: u) k (WV :: v) ((1#4) + l * (1#2))
  | Scan_short00 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (2 + n * 4) (WK :: u) k (WK :: v) (1 + l * 2)
  | Scan_short01 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (2 + n * 4) (WQ :: u) k (WK :: v) (l * 2)
  | Scan_short10 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (4 + n * 4) (WK :: u) k (WQ :: v) (1 + l * 2)
  | Scan_short11 {n : nat} {u : zW} {k : nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (4 + n * 4) (WQ :: u) k (WQ :: v) (l * 2).

Lemma z19 {e : bool} {u : zW} (hI : zPr e u) :
    forall (k : nat), (e = true -> exists n, k = (n * 2)%nat) ->
      (z0Y u + z0Z u) * 2 < Qnat k ->
      exists b v l, Scan k u b v l /\ (0 < b)%nat.
Proof.
  induction hI as [e | e u _ IH | u _ IH | u _ IH | e u _ IH | e u _ IH]; intros k hEk hk.
  - cbn [z0Y z0Z] in hk.
    assert (hk_pos : Qnat 0 < Qnat k) by (change (Qnat 0) with 0; lra).
    apply Qnat_lt_iff in hk_pos.
    exists k, ([] : zW), 0; split; [exact (Scan_nil k) | exact hk_pos].
  - pose proof (zWn u) as [hy [hz _]].
    cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [change (Qnat 0) with 0 in hk; lra |].
    change (S k) with (1 + k)%nat in hk |- *.
    destruct (IH ((1 + k) * 2)%nat (fun _ => ex_intro _ (1 + k)%nat eq_refl)
      ltac:(push_Qnat_all; lra)) as [b [v [l [hS hB]]]].
    exists b, (WV :: v), (l * (1#2)); split; [exact (Scan_T hS) | exact hB].
  - pose proof (zWn u) as [hy [hz _]].
    cbn [z0Y z0Z] in hk.
    destruct (hEk eq_refl) as [n ->].
    destruct (z0F n) as [[a ->] | [a ->]].
    + destruct a as [| a]; [change (Qnat (0 * 2 * 2)) with 0 in hk; lra |].
      change (S a) with (1 + a)%nat in hk |- *.
      destruct (IH (a * 2)%nat (fun _ => ex_intro _ a eq_refl)
        ltac:(push_Qnat_all; lra)) as [b [v [l [hS hB]]]].
      exists b, (WQ :: v), (1 + l * 2); split; [| exact hB].
      replace ((1 + a) * 2 * 2)%nat with (4 + a * 4)%nat by lia.
      exact (Scan_short10 hS).
    + destruct (IH (a * 2)%nat (fun _ => ex_intro _ a eq_refl)
        ltac:(push_Qnat_all; lra)) as [b [v [l [hS hB]]]].
      exists b, (WK :: v), (1 + l * 2); split; [| exact hB].
      replace ((1 + a * 2) * 2)%nat with (2 + a * 4)%nat by lia.
      exact (Scan_short00 hS).
  - pose proof (zWn u) as [hy [hz _]].
    cbn [z0Y z0Z] in hk.
    destruct (hEk eq_refl) as [n ->].
    destruct (z0F n) as [[a ->] | [a ->]].
    + destruct a as [| a]; [change (Qnat (0 * 2 * 2)) with 0 in hk; lra |].
      change (S a) with (1 + a)%nat in hk |- *.
      destruct (IH (1 + a * 2)%nat (fun h => ltac:(discriminate))
        ltac:(push_Qnat_all; lra)) as [b [v [l [hS hB]]]].
      exists b, (WQ :: v), (l * 2); split; [| exact hB].
      replace ((1 + a) * 2 * 2)%nat with (4 + a * 4)%nat by lia.
      exact (Scan_short11 hS).
    + destruct (IH (1 + a * 2)%nat (fun h => ltac:(discriminate))
        ltac:(push_Qnat_all; lra)) as [b [v [l [hS hB]]]].
      exists b, (WK :: v), (l * 2); split; [| exact hB].
      replace ((1 + a * 2) * 2)%nat with (2 + a * 4)%nat by lia.
      exact (Scan_short01 hS).
  - pose proof (zWn u) as [hy [hz _]].
    cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [change (Qnat 0) with 0 in hk; lra |].
    change (S k) with (1 + k)%nat in hk |- *.
    destruct (IH (k * 2)%nat (fun _ => ex_intro _ k eq_refl)
      ltac:(push_Qnat_all; lra)) as [b [v [l [hS hB]]]].
    exists b, (WV :: v), ((1 + l) * (1#2)); split; [exact (Scan_pair0 hS) | exact hB].
  - pose proof (zWn u) as [hy [hz _]].
    cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [change (Qnat 0) with 0 in hk; lra |].
    change (S k) with (1 + k)%nat in hk |- *.
    destruct (IH (1 + k * 2)%nat (fun h => ltac:(discriminate))
      ltac:(push_Qnat_all; lra)) as [b [v [l [hS hB]]]].
    exists b, (WV :: v), ((1#4) + l * (1#2)); split; [exact (Scan_pair1 hS) | exact hB].
Qed.

Lemma z1a (u : zW) (k : nat) (h : (z0Y u + z0Z u) * 2 < Qnat (k * 2)) :
    exists b v l, Scan (k * 2) u b v l /\ (0 < b)%nat.
Proof.
  exact (z19 (proj1 (z0J u)) (k * 2)%nat (fun _ => ex_intro _ k eq_refl) h).
Qed.

Lemma zSz (n : nat) (u : zW) (b : nat) (v : zW) (l : Rat) :
    ~ Scan (1 + n * 2) (WK :: u) b v l.
Proof.
  intros h; inversion h; lia.
Qed.

Lemma zSo (r : nat) :
    forall (n b : nat) (v : zW) (l : Rat),
      ~ Scan (1 + n * 2) (zR (r * 2) WQ ++ [WK]) b v l.
Proof.
  induction r as [| r IH]; intros n b v l hI.
  - cbn in hI; exact (zSz n [] b v l hI).
  - replace (S r * 2)%nat with (S (S (r * 2))) in hI by lia.
    cbn [zR repeat app] in hI.
    inversion hI as [| | | m u0 k0 v0 l0 hJ | | m u0 k0 v0 l0 hJ | | m u0 k0 v0 l0 hJ];
      subst; try lia.
    eapply IH; exact hJ.
Qed.

Lemma zS1 (r : nat) :
    forall (a b : nat) (v : zW) (l : Rat),
      Scan a (zR (1 + r * 2) WQ ++ [WK]) b v l ->
      v = zR (1 + r) WV /\ b = ((a - 1) * 2 ^ (1 + r))%nat /\ l == (1#2).
Proof.
  induction r as [| r IH]; intros a b v l hI.
  - cbn [Nat.mul Nat.add zR repeat app] in hI.
    inversion hI as [| | m u0 k0 v0 l0 hJ | | | m u0 k0 v0 l0 hJ | | m u0 k0 v0 l0 hJ]; subst.
    + inversion hJ; subst.
      split; [reflexivity | split; [cbn [Nat.add Nat.pow]; lia | lra]].
    + exfalso; exact (zSz m [] b v0 l0 hJ).
    + exfalso; exact (zSz m [] b v0 l0 hJ).
  - replace (1 + S r * 2)%nat with (S (S (1 + r * 2))) in hI by lia.
    cbn [zR repeat app] in hI.
    inversion hI as [| | | m u0 k0 v0 l0 hJ | | m u0 k0 v0 l0 hJ | | m u0 k0 v0 l0 hJ]; subst.
    + destruct (IH (1 + m * 2)%nat b v0 l0 hJ) as [-> [-> hl0]].
      split; [reflexivity | split; [| lra]].
      replace (1 + S r)%nat with (S (1 + r)) by lia.
      cbn [Nat.pow]; lia.
    + exfalso; apply (zSo (S r) m b v0 l0).
      replace (S r * 2)%nat with (S (1 + r * 2)) by lia.
      cbn [zR repeat app]; exact hJ.
    + exfalso; apply (zSo (S r) m b v0 l0).
      replace (S r * 2)%nat with (S (1 + r * 2)) by lia.
      cbn [zR repeat app]; exact hJ.
Qed.

Inductive zTd : zW -> Rat -> Prop :=
  | zTd_end : zTd [WK] 0
  | zTd_zero {u : zW} {z : Rat} : zTd u z -> zTd (WK :: u) (1 + z * 2)
  | zTd_one {u : zW} {z : Rat} : zTd u z -> zTd (WQ :: u) (z * 2).

Lemma z1e {u : zW} {z : Rat} (h : zTd u z) : 0 <= z.
Proof. induction h; lra. Qed.

Lemma z1f {u : zW} {z : Rat} (h : zTd (WK :: u) z) :
    (u = [] /\ z = 0) \/ exists y, zTd u y /\ z = 1 + y * 2.
Proof.
  inversion h as [| u0 z0 hJ | ]; subst.
  - left; split; reflexivity.
  - right; exists z0; split; [exact hJ | reflexivity].
Qed.

Lemma zTo {u : zW} {z : Rat} (h : zTd (WQ :: u) z) :
    exists y, zTd u y /\ z = y * 2.
Proof.
  inversion h as [| | u0 z0 hJ ]; subst.
  exists z0; split; [exact hJ | reflexivity].
Qed.

Lemma z1g {A H : nat} {u : zW} (h : zDg A H u) :
    zTd (u ++ [WK]) (z0Z u).
Proof.
  induction h as [| A H u _ IH | A H u _ IH].
  - exact zTd_end.
  - exact (zTd_zero IH).
  - exact (zTd_one IH).
Qed.

Lemma z1h {a : nat} {u : zW} {b : nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    forall {z : Rat}, zTd u z ->
      z0Y v <= 1 + z * 2 /\ l <= 1 + z * 2 /\
      (forall n, a = (1 + n * 2)%nat -> z0Y v <= z * 2 /\ l <= (1#2) + z * 2).
Proof.
  induction h as [k | n u k v l _ _ | m u k v l hI IH | m u k v l hI IH |
    m u k v l hI IH | m u k v l _ IH | m u k v l hI IH | m u k v l _ IH];
    intros z hZ.
  - inversion hZ.
  - inversion hZ.
  - destruct (zTo hZ) as [y [hJ ->]].
    destruct (z1f hJ) as [[-> ->] | [x [hJ' ->]]].
    + inversion hI; subst.
      cbn [z0Y]; repeat split; lra.
    + destruct (IH x hJ') as [hM [hL _]].
      pose proof (z1e hJ') as hx.
      cbn [z0Y]; repeat split; lra.
  - destruct (zTo hZ) as [y [hJ ->]].
    destruct (zTo hJ) as [x [hJ' ->]].
    destruct (IH x hJ') as [_ [_ hOdd]].
    destruct (hOdd m eq_refl) as [hM hL].
    pose proof (z1e hJ') as hx.
    cbn [z0Y]; repeat split; lra.
  - destruct (z1f hZ) as [[-> ->] | [x [hJ ->]]].
    + inversion hI; subst.
      cbn [z0Y]; repeat split; try lra; lia.
    + destruct (IH x hJ) as [hM [hL _]].
      cbn [z0Y]; repeat split; try lra; lia.
  - destruct (zTo hZ) as [x [hJ ->]].
    destruct (IH x hJ) as [_ [_ hOdd]].
    destruct (hOdd m eq_refl) as [hM hL].
    cbn [z0Y]; repeat split; try lra; lia.
  - destruct (z1f hZ) as [[-> ->] | [x [hJ ->]]].
    + inversion hI; subst.
      cbn [z0Y]; repeat split; try lra; lia.
    + destruct (IH x hJ) as [hM [hL _]].
      cbn [z0Y]; repeat split; try lra; lia.
  - destruct (zTo hZ) as [x [hJ ->]].
    destruct (IH x hJ) as [_ [_ hOdd]].
    destruct (hOdd m eq_refl) as [hM hL].
    cbn [z0Y]; repeat split; try lra; lia.
Qed.

Lemma z0L_odd_scan {n : nat} {w : zW} {b : nat} {v : zW} {l : Rat}
    (h : Scan (1 + n * 2) (w ++ [WQ; WQ; WK]) b v l)
    (hL : z0L (WQ :: w ++ [WK]) = true) :
    z0L (w ++ [WK]) = true.
Proof.
  destruct w as [| t0 w'].
  - exfalso; exact (zSo 1 n b v l h).
  - destruct t0.
    + exact hL.
    + exfalso; exact (zSz n (w' ++ [WQ; WQ; WK]) b v l h).
    + destruct w' as [| t1 w''].
      * reflexivity.
      * destruct t1; [| reflexivity | reflexivity].
        cbn [app] in h.
        inversion h; lia.
Qed.

Lemma zScan_qqk {a : nat} {u : zW} {b : nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    forall (w0 : zW), u = w0 ++ [WQ; WQ; WK] ->
      z11 v <= (1#8) * z11 u /\
      (z0L (w0 ++ [WK]) = true -> z11 v <= (1#64) * z11 u) /\
      (exists n, b = (n * 4)%nat) /\
      (exists v0, v = v0 ++ [WV]).
Proof.
  induction h as [k | n u0 k v0 l0 _ IH | n u0 k v0 l0 _ IH | n u0 k v0 l0 hSub IH |
    n u0 k v0 l0 _ IH | n u0 k v0 l0 hSub IH | n u0 k v0 l0 _ IH | n u0 k v0 l0 hSub IH];
    intros w0 hu.
  - destruct w0; discriminate.
  - destruct w0 as [| t0 w']; [discriminate |].
    cbn [app] in hu; injection hu as ht0 hu0; subst t0.
    destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
    split; [| split; [| split]].
    + cbn [z11]; lra.
    + intros hL; pose proof (h2 hL); cbn [z11]; lra.
    + exists m; exact hm.
    + exists (WV :: vp); subst v0; reflexivity.
  - destruct w0 as [| t0 [| t1 w']]; try discriminate.
    cbn [app] in hu; injection hu as ht0 ht1 hu0; subst t0 t1.
    destruct (IH w' hu0) as [h1 [_ [[m hm] [vp hvp]]]].
    pose proof (zSp u0) as hp.
    split; [| split; [| split]].
    + cbn [z11]; lra.
    + intros _; cbn [z11]; lra.
    + exists m; exact hm.
    + exists (WV :: vp); subst v0; reflexivity.
  - destruct w0 as [| t0 [| t1 w']].
    + cbn [app] in hu; injection hu as hu0; subst u0.
      exfalso; exact (zSz n [] k v0 l0 hSub).
    + cbn [app] in hu; injection hu as ht0 hu0; subst t0 u0.
      destruct (zS1 0 (1 + n * 2) k v0 l0 hSub) as [-> [hk _]].
      cbn [zR repeat z11 Nat.add Nat.pow] in hk |- *.
      split; [lra | split; [intros _; lra | split]].
      * exists n; lia.
      * exists [WV]; reflexivity.
    + cbn [app] in hu; injection hu as ht0 ht1 hu0; subst t0 t1.
      destruct (IH w' hu0) as [h1 [_ [[m hm] [vp hvp]]]].
      pose proof (zSp u0) as hp.
      split; [| split; [| split]].
      * cbn [z11]; lra.
      * intros _; cbn [z11]; lra.
      * exists m; exact hm.
      * exists (WV :: vp); subst v0; reflexivity.
  - destruct w0 as [| t0 w']; [discriminate |].
    cbn [app] in hu; injection hu as ht0 hu0; subst t0.
    destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
    split; [| split; [| split]].
    + cbn [z11]; lra.
    + intros hL; pose proof (h2 hL); cbn [z11]; lra.
    + exists m; exact hm.
    + exists (WK :: vp); subst v0; reflexivity.
  - destruct w0 as [| t0 w'].
    + cbn [app] in hu; injection hu as hu0; subst u0.
      destruct (zS1 0 (1 + n * 2) k v0 l0 hSub) as [-> [hk _]].
      cbn [zR repeat z11 Nat.add Nat.pow] in hk |- *.
      split; [lra | split; [| split]].
      * intros hL; discriminate.
      * exists n; lia.
      * exists [WK]; reflexivity.
    + cbn [app] in hu; injection hu as ht0 hu0; subst t0.
      destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
      split; [| split; [| split]].
      * cbn [z11]; lra.
      * intros hL; rewrite hu0 in hSub; pose proof (h2 (z0L_odd_scan hSub hL)); cbn [z11]; lra.
      * exists m; exact hm.
      * exists (WK :: vp); subst v0; reflexivity.
  - destruct w0 as [| t0 w']; [discriminate |].
    cbn [app] in hu; injection hu as ht0 hu0; subst t0.
    destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
    split; [| split; [| split]].
    + cbn [z11]; lra.
    + intros hL; pose proof (h2 hL); cbn [z11]; lra.
    + exists m; exact hm.
    + exists (WQ :: vp); subst v0; reflexivity.
  - destruct w0 as [| t0 w'].
    + cbn [app] in hu; injection hu as hu0; subst u0.
      destruct (zS1 0 (1 + n * 2) k v0 l0 hSub) as [-> [hk _]].
      cbn [zR repeat z11 Nat.add Nat.pow] in hk |- *.
      split; [lra | split; [| split]].
      * intros hL; discriminate.
      * exists n; lia.
      * exists [WQ]; reflexivity.
    + cbn [app] in hu; injection hu as ht0 hu0; subst t0.
      destruct (IH w' hu0) as [h1 [h2 [[m hm] [vp hvp]]]].
      split; [| split; [| split]].
      * cbn [z11]; lra.
      * intros hL; rewrite hu0 in hSub; pose proof (h2 (z0L_odd_scan hSub hL)); cbn [z11]; lra.
      * exists m; exact hm.
      * exists (WQ :: vp); subst v0; reflexivity.
Qed.

(* Section 7C: BScan (15 constructors) and its lemmas *)

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
    0 < zIv r /\ zIv r <= 1 /\ 1 <= zP4 r /\ ((1 <= r)%nat -> 4 <= zP4 r /\ 8 * zIv r <= zP4 r).
Proof.
  induction r as [| r [h1 [h2 [h3 h4]]]].
  - cbn [zIv zP4]; repeat split; try lra; lia.
  - cbn [zIv zP4].
    destruct r as [| r'].
    + cbn [zIv zP4]; repeat split; lra.
    + destruct (h4 ltac:(lia)) as [h4a h4b].
      repeat split; lra.
Qed.

Lemma z11_R (r : nat) (u : zW) :
    z11 (zR r WV ++ u) == zIv r * z11 u.
Proof.
  induction r as [| r IH]; [cbn [zR repeat app zIv]; ring |].
  change (zR (S r) WV) with (WV :: zR r WV).
  cbn [app z11 zIv]; rewrite IH; ring.
Qed.

Lemma z11_QK (r : nat) (u : zW) :
    z11 (zQK r u) == zP4 r * z11 u.
Proof.
  induction r as [| r IH]; [cbn [zQK zP4]; ring |].
  cbn [zQK z11 zP4]; rewrite IH; ring.
Qed.

Lemma z0W_R (r : nat) (u : zW) :
    z0W (zR r WV ++ u) == zIv r * z0W u.
Proof.
  induction r as [| r IH]; [cbn [zR repeat app zIv]; ring |].
  change (zR (S r) WV) with (WV :: zR r WV).
  cbn [app z0W zIv]; rewrite IH; ring.
Qed.

Lemma z0W_QK (r : nat) (u : zW) :
    z0W (zQK r u) == (5#4) * (zP4 r - 1) + zP4 r * z0W u.
Proof.
  induction r as [| r IH]; [cbn [zQK zP4]; ring |].
  cbn [zQK z0W zP4]; rewrite IH; ring.
Qed.

Inductive BScan : bool -> nat -> zW -> nat -> zW -> Rat -> Rat -> Prop :=
  | BScan_nil (k : nat) : BScan false k [] k [] 0 0
  | BScan_T {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (2 + n) (WV :: u) k (WV :: v) (a * (1#2)) (b * (1#2))
  | BScan_pair0 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan false (1 + n) (WQ :: WK :: u) k (WV :: v) (a * (1#2)) ((1#4) + b * (1#2))
  | BScan_pair1 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (1 + n) (WQ :: WQ :: u) k (WV :: v) (a * (1#2)) ((1#2) + b * (1#2))
  | BScan_short00 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan false (2 + n * 4) (WK :: u) k (WK :: v) ((5#2) + a * 2) (b * 2)
  | BScan_short01 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (2 + n * 4) (WQ :: u) k (WK :: v) ((3#2) + a * 2) (b * 2)
  | BScan_short10 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan false (4 + n * 4) (WK :: u) k (WQ :: v) ((7#2) + a * 2) (b * 2)
  | BScan_short11 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (4 + n * 4) (WQ :: u) k (WQ :: v) ((5#2) + a * 2) (b * 2)
  | BScan_odd_chain0 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (1 + r)) u k v a b ->
      BScan false (3 + m * 4) (zQK r (WV :: u)) k (WK :: (zR r WV ++ v))
        ((2 + a * 2) * zIv r) (b * 2 * zIv r)
  | BScan_odd_chain1 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (1 + r)) u k v a b ->
      BScan false (5 + m * 4) (zQK r (WV :: u)) k (WQ :: (zR r WV ++ v))
        (1 + (2 + a * 2) * zIv r) (b * 2 * zIv r)
  | BScan_even_chain (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + (1 + m * 2) * 2 ^ (1 + r)) u k v a b ->
      BScan false (6 + m * 2) (WK :: zQK r (WV :: u)) k (zR (1 + r) WV ++ v)
        (1 + (1 + a) * (1#2) * zIv r) (b * (1#2) * zIv r)
  | BScan_shift_pair0 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan true (1 + n) (WK :: u) k (WV :: v) (a * (1#2)) ((1#4) + b * (1#2))
  | BScan_shift_pair1 {n : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan true (1 + n) (WQ :: u) k (WV :: v) (a * (1#2)) ((1#2) + b * (1#2))
  | BScan_shift_chain0 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (2 + r)) u k v a b ->
      BScan true (3 + m * 4) (WK :: zQK r (WV :: u)) k (WK :: (zR (1 + r) WV ++ v))
        ((1 + a) * zIv r) (b * zIv r)
  | BScan_shift_chain1 (r : nat) {m : nat} {u : zW} {k : nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (2 + r)) u k v a b ->
      BScan true (5 + m * 4) (WK :: zQK r (WV :: u)) k (WQ :: (zR (1 + r) WV ++ v))
        (1 + (1 + a) * zIv r) (b * zIv r).

Lemma zIv_pow2 (r : nat) :
    Qnat (2 ^ r) * zIv r == 1.
Proof.
  induction r as [| r IH]; [cbn [Nat.pow zIv]; reflexivity |].
  rewrite Qnat_pow2_S; cbn [zIv]; lra.
Qed.

Lemma z1i {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
    (h : BScan s k u k' v a b) :
    Qnat k - 3 == (Qnat k' - 3) * z11 v + 2 * (a - b).
Proof.
  induction h as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH].
  - cbn [z11]; ring.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; rewrite z11_R.
    assert (hp : Qnat (2 ^ (1 + r)) * zIv r == 2)
      by (rewrite Qnat_pow2_1_add; pose proof (zIv_pow2 r); lra).
    push_Qnat_all.
    assert (h1 : (3 + Qnat m * 4) - 3 == (1 + Qnat m * Qnat (2 ^ (1 + r)) - 3) * (2 * zIv r) + 4 * zIv r)
      by (transitivity (Qnat m * 2 * (Qnat (2 ^ (1 + r)) * zIv r)); [rewrite hp; ring | ring]).
    rewrite h1, IH; ring.
  - cbn [z11]; rewrite z11_R.
    assert (hp : Qnat (2 ^ (1 + r)) * zIv r == 2)
      by (rewrite Qnat_pow2_1_add; pose proof (zIv_pow2 r); lra).
    push_Qnat_all.
    assert (h1 : (5 + Qnat m * 4) - 3 == (1 + Qnat m * Qnat (2 ^ (1 + r)) - 3) * (2 * zIv r) + 4 * zIv r + 2)
      by (transitivity (2 + Qnat m * 2 * (Qnat (2 ^ (1 + r)) * zIv r)); [rewrite hp; ring | ring]).
    rewrite h1, IH; ring.
  - change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z11]; rewrite z11_R.
    assert (hp : Qnat (2 ^ (1 + r)) * zIv r == 2)
      by (rewrite Qnat_pow2_1_add; pose proof (zIv_pow2 r); lra).
    push_Qnat_all.
    assert (h1 : (6 + Qnat m * 2) - 3 == (1 + (1 + Qnat m * 2) * Qnat (2 ^ (1 + r)) - 3) * ((1#2) * zIv r) + zIv r + 2)
      by (transitivity (2 + (1 + Qnat m * 2) * (1#2) * (Qnat (2 ^ (1 + r)) * zIv r)); [rewrite hp; ring | ring]).
    rewrite h1, IH; ring.
  - cbn [z11]; push_Qnat_all; lra.
  - cbn [z11]; push_Qnat_all; lra.
  - change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z11]; rewrite z11_R.
    assert (hp : Qnat (2 ^ (2 + r)) * zIv r == 4).
    { change (2 + r)%nat with (1 + (1 + r))%nat.
      rewrite Qnat_pow2_1_add, Qnat_pow2_1_add; pose proof (zIv_pow2 r); lra. }
    push_Qnat_all.
    assert (h1 : (3 + Qnat m * 4) - 3 == (1 + Qnat m * Qnat (2 ^ (2 + r)) - 3) * zIv r + 2 * zIv r)
      by (transitivity (Qnat m * (Qnat (2 ^ (2 + r)) * zIv r)); [rewrite hp; ring | ring]).
    rewrite h1, IH; ring.
  - change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z11]; rewrite z11_R.
    assert (hp : Qnat (2 ^ (2 + r)) * zIv r == 4).
    { change (2 + r)%nat with (1 + (1 + r))%nat.
      rewrite Qnat_pow2_1_add, Qnat_pow2_1_add; pose proof (zIv_pow2 r); lra. }
    push_Qnat_all.
    assert (h1 : (5 + Qnat m * 4) - 3 == (1 + Qnat m * Qnat (2 ^ (2 + r)) - 3) * zIv r + 2 * zIv r + 2)
      by (transitivity (2 + Qnat m * (Qnat (2 ^ (2 + r)) * zIv r)); [rewrite hp; ring | ring]).
    rewrite h1, IH; ring.
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
    (s = true -> (exists m, k = (1 + m * 4)%nat) ->
      z0W v <= (33#38) * z0W u - (33#38)).
Proof.
  induction h as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH].
  - repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    repeat split; try (intros; discriminate); cbn [z0W]; lra.
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _ | split; intros; discriminate].
    cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r']; [cbn [zIv zP4]; repeat split; lra |].
    destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
    destruct (hge1 ltac:(lia)) as [hp4_4 _].
    repeat split; nra.
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _ | split; intros; discriminate].
    cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r']; [cbn [zIv zP4]; repeat split; lra |].
    destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
    destruct (hge1 ltac:(lia)) as [hp4_4 _].
    repeat split; nra.
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _ | split; intros; discriminate].
    change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]].
    repeat split; nra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros; discriminate | split; [intros _ | intros _ _]]; cbn [z0W]; repeat split; lra.
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros; discriminate | split; [intros _ | intros _ _]]; cbn [z0W]; repeat split; lra.
  - assert (hdiv : exists m', (1 + m * 2 ^ (2 + r) = 1 + m' * 4)%nat).
    { exists (m * 2 ^ r)%nat; cbn [Nat.add Nat.pow]; lia. }
    destruct (proj1 (proj2 IH) eq_refl) as [_ [h2 h3]].
    pose proof (proj2 (proj2 IH) eq_refl hdiv) as h1.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros; discriminate | split; [intros _ | intros _ [q hq]; lia]].
    change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r']; [cbn [zIv zP4]; repeat split; lra |].
    destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
    destruct (hge1 ltac:(lia)) as [hp4_4 _].
    repeat split; nra.
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros; discriminate | split; [intros _ | intros _ _]].
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
      cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
      destruct r as [| r']; [cbn [zIv zP4]; repeat split; lra |].
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [hp4_4 _].
      repeat split; nra.
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
      cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
      destruct r as [| r']; [cbn [zIv zP4]; lra |].
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [hp4_4 _].
      nra.
Qed.

Lemma z1k {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
    (h1 : BScan s k u k' v a b) :
    forall {w : zW} {k'' : nat} {x : zW} {c d : Rat},
      BScan false k' w k'' x c d ->
      exists a' b', BScan s k (u ++ w) k'' (v ++ x) a' b' /\
        a' == a + z11 v * c /\ b' == b + z11 v * d.
Proof.
  induction h1 as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH];
    intros w k'' x c d h2.
  - exists c, d; split; [exact h2 | split; [cbn [z11]; ring | cbn [z11]; ring]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), (b' * (1#2)); split; [exact (BScan_T hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#4) + b' * (1#2)); split; [exact (BScan_pair0 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#2) + b' * (1#2)); split; [exact (BScan_pair1 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists ((5#2) + a' * 2), (b' * 2); split; [exact (BScan_short00 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists ((3#2) + a' * 2), (b' * 2); split; [exact (BScan_short01 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists ((7#2) + a' * 2), (b' * 2); split; [exact (BScan_short10 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists ((5#2) + a' * 2), (b' * 2); split; [exact (BScan_short11 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists ((2 + a' * 2) * zIv r), (b' * 2 * zIv r); split; [| split].
    + rewrite <- zQK_append; cbn [app]; rewrite <- app_assoc; exact (BScan_odd_chain0 r hK).
    + cbn [z11]; rewrite z11_R, hA; ring.
    + cbn [z11]; rewrite z11_R, hB; ring.
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (2 + a' * 2) * zIv r), (b' * 2 * zIv r); split; [| split].
    + rewrite <- zQK_append; cbn [app]; rewrite <- app_assoc; exact (BScan_odd_chain1 r hK).
    + cbn [z11]; rewrite z11_R, hA; ring.
    + cbn [z11]; rewrite z11_R, hB; ring.
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (1 + a') * (1#2) * zIv r), (b' * (1#2) * zIv r); split; [| split].
    + cbn [app]; rewrite <- zQK_append, <- app_assoc; exact (BScan_even_chain r hK).
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)); cbn [z11]; rewrite z11_R, hA; ring.
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)); cbn [z11]; rewrite z11_R, hB; ring.
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#4) + b' * (1#2)); split; [exact (BScan_shift_pair0 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#2) + b' * (1#2)); split; [exact (BScan_shift_pair1 hK) | split; [cbn [z11]; lra | cbn [z11]; lra]].
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists ((1 + a') * zIv r), (b' * zIv r); split; [| split].
    + cbn [app]; rewrite <- zQK_append, <- app_assoc; exact (BScan_shift_chain0 r hK).
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)); cbn [z11]; rewrite z11_R, hA; ring.
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)); cbn [z11]; rewrite z11_R, hB; ring.
  - destruct (IH w k'' x c d h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (1 + a') * zIv r), (b' * zIv r); split; [| split].
    + cbn [app]; rewrite <- zQK_append, <- app_assoc; exact (BScan_shift_chain1 r hK).
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)); cbn [z11]; rewrite z11_R, hA; ring.
    + change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)); cbn [z11]; rewrite z11_R, hB; ring.
Qed.


(* Stage 3 Part B: z1n..z1l *)

Lemma Qnat_le (a b : nat) : (a <= b)%nat -> Qnat a <= Qnat b.
Proof. apply Qnat_le_iff. Qed.

Lemma z1n {k : nat} {u : zW} {k' : nat} {v : zW} {l : Rat}
    (hI : Scan k u k' v l) :
    forall {A H : nat}, zDg A H u ->
      exists a b, BScan false k u k' v a b /\ a - b <= (5#2) * z0Y v + l /\ b - a <= 1.
Proof.
  induction hI as [k | n u k v l _ _ | n u k v l _ IH | n u k v l _ IH |
    n u k v l _ IH | n u k v l _ IH | n u k v l _ IH | n u k v l _ IH];
    intros A H hD.
  - exists 0, 0; split; [exact (BScan_nil k) | split; cbn [z0Y]; lra].
  - exfalso; exact (z0K hD).
  - destruct (zD1 hD) as [A1 [H1 [hD1 [_ _]]]].
    destruct (zD0 hD1) as [A2 [H2 [hD2 [_ _]]]].
    destruct (IH A2 H2 hD2) as [a [b [hJ [hP hM]]]].
    exists (a * (1#2)), ((1#4) + b * (1#2)); split; [exact (BScan_pair0 hJ) | split; cbn [z0Y]; lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 [_ _]]]].
    destruct (zD1 hD1) as [A2 [H2 [hD2 [_ _]]]].
    destruct (IH A2 H2 hD2) as [a [b [hJ [hP hM]]]].
    exists (a * (1#2)), ((1#2) + b * (1#2)); split; [exact (BScan_pair1 hJ) | split; cbn [z0Y]; lra].
  - destruct (zD0 hD) as [A1 [H1 [hD1 [_ _]]]].
    destruct (IH A1 H1 hD1) as [a [b [hJ [hP hM]]]].
    exists ((5#2) + a * 2), (b * 2); split; [exact (BScan_short00 hJ) | split; cbn [z0Y]; lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 [_ _]]]].
    destruct (IH A1 H1 hD1) as [a [b [hJ [hP hM]]]].
    exists ((3#2) + a * 2), (b * 2); split; [exact (BScan_short01 hJ) | split; cbn [z0Y]; lra].
  - destruct (zD0 hD) as [A1 [H1 [hD1 [_ _]]]].
    destruct (IH A1 H1 hD1) as [a [b [hJ [hP hM]]]].
    exists ((7#2) + a * 2), (b * 2); split; [exact (BScan_short10 hJ) | split; cbn [z0Y]; lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 [_ _]]]].
    destruct (IH A1 H1 hD1) as [a [b [hJ [hP hM]]]].
    exists ((5#2) + a * 2), (b * 2); split; [exact (BScan_short11 hJ) | split; cbn [z0Y]; lra].
Qed.

Lemma zHi_bscan {m k' : nat} {w0 y : zW} {l : Rat} {A0 H0 : nat}
    (hS : Scan (m * 2) (w0 ++ [WQ; WQ; WK]) k' y l)
    (hD0 : zDg A0 H0 w0) :
    exists a b, BScan false (1 + m) ((WQ :: WK :: w0) ++ [WQ; WQ; WK]) k' (WV :: y) a b /\
      z0Y (WV :: y) <= (1#4) * z0Z (WQ :: WK :: w0) /\
      a - b <= (7#8) * z0Z (WQ :: WK :: w0) /\
      b - a <= 1.
Proof.
  assert (hD_qq : zDg 3 2 [WQ; WQ]) by exact (zDg_one (zDg_one zDg_nil)).
  pose proof (z0U hD0 hD_qq) as hD_w.
  assert (hS' : Scan (m * 2) ((w0 ++ [WQ; WQ]) ++ [WK]) k' y l)
    by (rewrite <- app_assoc; exact hS).
  destruct (z1h hS' (z1g hD_w)) as [hY [hL _]].
  assert (hZ_eq : z0Z (w0 ++ [WQ; WQ]) == z0Z w0)
    by (rewrite z14; cbn [z0Z]; ring).
  rewrite hZ_eq in hY, hL.
  pose proof (z0U hD_w (zDg_zero zDg_nil)) as hD_wk.
  destruct (z1n hS' hD_wk) as [a0 [b0 [hB0 [hAB0 hBA0]]]].
  rewrite <- app_assoc in hB0.
  exists (a0 * (1#2)), ((1#4) + b0 * (1#2)).
  split; [exact (BScan_pair0 hB0) | split; [cbn [z0Y z0Z]; lra | split; [cbn [z0Z]; lra | lra]]].
Qed.

Definition zSwt (s : bool) : Rat :=
  if s then (1#4) else 1.

Lemma z1p_upper {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
    (h : BScan s k u k' v a b) :
    z11 v <= zSwt s * z11 u.
Proof.
  induction h as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH].
  - cbn [z11 zSwt]; lra.
  - cbn [z11 zSwt] in *; lra.
  - pose proof (zSp u); cbn [z11 zSwt] in *; lra.
  - pose proof (zSp u); cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [? [? [? _]]]; nra.
  - cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [? [? [? _]]]; nra.
  - change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [? [? [? _]]]; nra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [? [? [? _]]]; nra.
  - change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [? [? [? _]]]; nra.
Qed.

Lemma zBz (n : nat) (u : zW) (k' : nat) (v : zW) (a b : Rat) :
    ~ BScan false (1 + n * 2) (WK :: u) k' v a b.
Proof.
  intros h; inversion h; try lia; destruct r; discriminate.
Qed.

Lemma z0L_odd_bscan {n : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
    (h : BScan false (1 + n * 2) u k' v a b)
    (hL : z0L (WQ :: u) = true) :
    z0L u = true.
Proof.
  destruct u as [| t0 u']; [discriminate |].
  destruct t0; [exact hL | exfalso; exact (zBz n u' k' v a b h) |].
  inversion h; subst; try lia; try reflexivity.
  - destruct r as [| r']; [discriminate | cbn [zQK] in *; inversion H0; subst; reflexivity].
  - destruct r as [| r']; [discriminate | cbn [zQK] in *; inversion H0; subst; reflexivity].
Qed.

Lemma z1p_z0L {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
    (h : BScan s k u k' v a b)
    (hL : z0L u = true) :
    z11 v <= (1#8) * zSwt s * z11 u.
Proof.
  induction h as [k | n u k v a b _ IH | n u k v a b hSub _ | n u k v a b hSub _ |
    n u k v a b _ IH | n u k v a b hSub IH | n u k v a b _ IH | n u k v a b hSub IH |
    r m u k v a b hSub IH | r m u k v a b hSub IH | r m u k v a b hSub _ |
    n u k v a b _ IH | n u k v a b hSub IH | r m u k v a b hSub IH | r m u k v a b hSub IH].
  - discriminate.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (z1p_upper hSub); cbn [z11 zSwt] in *; lra.
  - pose proof (z1p_upper hSub); cbn [z11 zSwt] in *; lra.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IH (z0L_odd_bscan hSub hL)); cbn [z11 zSwt] in *; lra.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IH (z0L_odd_bscan hSub hL)); cbn [z11 zSwt] in *; lra.
  - destruct r as [| r'].
    + cbn [zQK z0L] in hL; pose proof (IH hL); cbn [zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [? [? [? hge1]]].
      destruct (hge1 ltac:(lia)); nra.
  - destruct r as [| r'].
    + cbn [zQK z0L] in hL; pose proof (IH hL); cbn [zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [? [? [? hge1]]].
      destruct (hge1 ltac:(lia)); nra.
  - pose proof (z1p_upper hSub) as hUp.
    change (zR (1 + r) WV ++ v) with (WV :: (zR r WV ++ v)).
    cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u); destruct (zIv_P4 r) as [? [? [? _]]]; nra.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IH (z0L_odd_bscan hSub hL)); cbn [z11 zSwt] in *; lra.
  - destruct r as [| r'].
    + cbn [zQK z0L] in hL; pose proof (IH hL); cbn [Nat.add zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      change (zR (1 + S r') WV ++ v) with (WV :: (zR (S r') WV ++ v)).
      cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [? [? [? hge1]]].
      destruct (hge1 ltac:(lia)); nra.
  - destruct r as [| r'].
    + cbn [zQK z0L] in hL; pose proof (IH hL); cbn [Nat.add zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      change (zR (1 + S r') WV ++ v) with (WV :: (zR (S r') WV ++ v)).
      cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u); destruct (zIv_P4 (S r')) as [? [? [? hge1]]].
      destruct (hge1 ltac:(lia)); nra.
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
  induction u_pre as [| a u [hEC hOS]].
  - split; [left; exact zPrU_base_E | left; exact zPrU_base_O].
  - cbn [app].
    destruct a.
    + destruct hOS as [hO | [hS [_ _]]].
      * split; [left; exact (zPrU_T_E hO) | left; exact (zPrU_T_O hO)].
      * split; [right; exists 0%nat, (u ++ [WV]); split; [reflexivity | exact hS] |
          left; exact (zPrU_odd_c 0 hS)].
    + destruct hEC as [hE | [r [u0 [hw hS]]]].
      * split; [left; exact (zPrU_short_K hE) |
          right; split; [exact (zPrU_shift_K hE) |
            split; [left; exact (zPrU_pair0_E hE) | exact (zPrU_pair0_O hE)]]].
      * rewrite hw.
        split; [left; exact (zPrU_even_c r hS) |
          right; split; [exact (zPrU_shift_c r hS) |
            split; [right; exists (S r), u0; split; [reflexivity | exact hS] |
              exact (zPrU_odd_c (S r) hS)]]].
    + destruct hOS as [hO | [_ [hQ_EC hQ_O]]].
      * split; [left; exact (zPrU_short_Q hO) |
          right; split; [exact (zPrU_shift_Q hO) |
            split; [left; exact (zPrU_pair1_E hO) | exact (zPrU_pair1_O hO)]]].
      * split; [exact hQ_EC | left; exact hQ_O].
Qed.

Lemma zPrU_MO_V (w : zW) : zPrU MO (WV :: (w ++ [WV])).
Proof.
  destruct (proj2 (zPrU_all w)) as [hO | [hS _]].
  - exact (zPrU_T_O hO).
  - exact (zPrU_odd_c 0 hS).
Qed.

Lemma zPrU_ME_VV (w : zW) : zPrU ME (WV :: WV :: (w ++ [WV])).
Proof.
  exact (zPrU_T_E (zPrU_MO_V w)).
Qed.

Lemma zPrU_MS_W {u : zW} (h : zPrU MS u) : 1 <= z0W u.
Proof.
  inversion h as [| | | | | | | u0 hE | r u0 hS | | u0 hO | | | | ]; subst.
  - pose proof (proj2 (proj2 (proj2 (zWn u0)))); cbn [z0W]; lra.
  - pose proof (proj2 (proj2 (proj2 (zWn u0)))).
    cbn [z0W]; rewrite z0W_QK; cbn [z0W].
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]]; nra.
  - pose proof (proj2 (proj2 (proj2 (zWn u0)))); cbn [z0W]; lra.
Qed.

Lemma zPrU_bscan {m : ModeU} {w : zW} (hI : zPrU m w) :
    ((m = ME \/ m = MO) ->
      forall (k : nat),
        (m = ME -> exists n, k = (n * 2)%nat) ->
        (m = MO -> exists n, k = (1 + n * 2)%nat) ->
        16 * z0W w < Qnat k - 3 ->
        exists m' v a b, BScan false k w (1 + m') v a b /\ (0 < m')%nat) /\
    (m = MS ->
      forall (k : nat),
        (exists n, k = (1 + n * 2)%nat) ->
        4 * z0W w - 4 < Qnat k - 3 ->
        exists m' v a b, BScan true k w (1 + m') v a b /\ (0 < m')%nat).
Proof.
  induction hI as [| | u hO IH | u hO IH | r u hS IH | u hE IH | r u hS IH |
    u hE IH | r u hS IH | u hO IH | u hO IH | u hE IH | u hE IH | u hO IH | u hO IH].
  - split; [intros _ k hE _ hk | intros; discriminate].
    destruct (hE eq_refl) as [n ->].
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    exists ((2 * n - 2) * 2)%nat, [WV], (0 * (1#2)), (0 * (1#2)); split; [| lia].
    replace (n * 2)%nat with (2 + (n - 1) * 2)%nat by lia.
    replace (1 + (2 * n - 2) * 2)%nat with (1 + ((n - 1) * 2) * 2)%nat by lia.
    exact (BScan_T (BScan_nil (1 + ((n - 1) * 2) * 2))).
  - split; [intros _ k _ hO hk | intros; discriminate].
    destruct (hO eq_refl) as [n ->].
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    exists ((2 * n - 1) * 2)%nat, [WV], (0 * (1#2)), (0 * (1#2)); split; [| lia].
    replace (1 + n * 2)%nat with (2 + (n * 2 - 1))%nat by lia.
    replace (1 + (2 * n - 1) * 2)%nat with (1 + (n * 2 - 1) * 2)%nat by lia.
    exact (BScan_T (BScan_nil (1 + (n * 2 - 1) * 2))).
  - split; [intros _ k hE _ hk | intros; discriminate].
    destruct (hE eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    assert (hn_q : Qnat (n * 2) == Qnat (2 + (n * 2 - 2)))
      by (apply Qnat_eq_iff; lia).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2 - 2) * 2)%nat
      (fun h => ltac:(discriminate)) (fun _ => ex_intro _ (n * 2 - 2)%nat eq_refl)
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hS hm']]]]].
    replace (n * 2)%nat with (2 + (n * 2 - 2))%nat by lia.
    exists m', (WV :: v), (a * (1#2)), (b * (1#2)); split; [exact (BScan_T hS) | exact hm'].
  - split; [intros _ k _ hO_k hk | intros; discriminate].
    destruct (hO_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    assert (hn_q : Qnat (1 + n * 2) == Qnat (2 + (n * 2 - 1)))
      by (apply Qnat_eq_iff; lia).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2 - 1) * 2)%nat
      (fun h => ltac:(discriminate)) (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl)
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hS hm']]]]].
    replace (1 + n * 2)%nat with (2 + (n * 2 - 1))%nat by lia.
    exists m', (WV :: v), (a * (1#2)), (b * (1#2)); split; [exact (BScan_T hS) | exact hm'].
  - split; [intros _ k _ hO_k hk | intros; discriminate].
    destruct (hO_k eq_refl) as [n ->].
    pose proof (zPrU_MS_W hS) as hWu.
    rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; nra]).
    assert (hpow_ge : (2 <= 2 ^ (1 + r))%nat)
      by (rewrite zP2; pose proof (zPp r); lia).
    destruct (z0F (n - 1)) as [[m hm] | [m hm]].
    + assert (hk_eq : (1 + n * 2 = 3 + m * 4)%nat) by lia.
      assert (hm_pow : (m * 2 <= m * 2 ^ (1 + r))%nat) by nia.
      pose proof (Qnat_le _ _ hm_pow) as hm_pow_q.
      assert (hm_q : Qnat n == Qnat (1 + m * 2)) by (apply Qnat_eq_iff; lia).
      assert (h_odd_sub : exists n', (1 + m * 2 ^ (1 + r) = 1 + n' * 2)%nat)
        by (exists (m * 2 ^ r)%nat; rewrite zP2; lia).
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (1 + r))%nat h_odd_sub
        ltac:(push_Qnat_all; nra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WK :: (zR r WV ++ v)), ((2 + a * 2) * zIv r), (b * 2 * zIv r);
        split; [exact (BScan_odd_chain0 r hSub) | exact hm'].
    + assert (hk_eq : (1 + n * 2 = 5 + m * 4)%nat) by lia.
      assert (hm_pow : (m * 2 <= m * 2 ^ (1 + r))%nat) by nia.
      pose proof (Qnat_le _ _ hm_pow) as hm_pow_q.
      assert (hm_q : Qnat n == Qnat (2 + m * 2)) by (apply Qnat_eq_iff; lia).
      assert (h_odd_sub : exists n', (1 + m * 2 ^ (1 + r) = 1 + n' * 2)%nat)
        by (exists (m * 2 ^ r)%nat; rewrite zP2; lia).
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (1 + r))%nat h_odd_sub
        ltac:(push_Qnat_all; nra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WQ :: (zR r WV ++ v)), (1 + (2 + a * 2) * zIv r), (b * 2 * zIv r);
        split; [exact (BScan_odd_chain1 r hSub) | exact hm'].
  - split; [intros _ k hE_k _ hk | intros; discriminate].
    destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    destruct (z0F n) as [[m ->] | [m ->]].
    + assert (hm1 : (1 <= m)%nat) by lia.
      assert (hk_eq : (m * 2 * 2 = 4 + (m - 1) * 4)%nat) by lia.
      assert (hm_q : Qnat m == Qnat (1 + (m - 1))) by (apply Qnat_eq_iff; lia).
      destruct (proj1 IH (or_introl eq_refl) ((m - 1) * 2)%nat
        (fun _ => ex_intro _ (m - 1)%nat eq_refl) (fun h => ltac:(discriminate))
        ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WQ :: v), ((7#2) + a * 2), (b * 2);
        split; [exact (BScan_short10 hSub) | exact hm'].
    + assert (hk_eq : ((1 + m * 2) * 2 = 2 + m * 4)%nat) by lia.
      destruct (proj1 IH (or_introl eq_refl) (m * 2)%nat
        (fun _ => ex_intro _ m eq_refl) (fun h => ltac:(discriminate))
        ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WK :: v), ((5#2) + a * 2), (b * 2);
        split; [exact (BScan_short00 hSub) | exact hm'].
  - split; [intros _ k hE_k _ hk | intros; discriminate].
    destruct (hE_k eq_refl) as [n ->].
    pose proof (zPrU_MS_W hS) as hWu.
    cbn [z0W] in hk; rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    assert (hn3 : (3 <= n)%nat)
      by (assert ((3 <= n \/ n <= 2)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 2 hle); push_Qnat_all; nra]).
    assert (hk_eq : (n * 2 = 6 + (n - 3) * 2)%nat) by lia.
    assert (hn_q : Qnat n == Qnat (3 + (n - 3))) by (apply Qnat_eq_iff; lia).
    assert (hpow_ge : (2 <= 2 ^ (1 + r))%nat) by (rewrite zP2; pose proof (zPp r); lia).
    assert (hm_pow : ((1 + (n - 3) * 2) * 2 <= (1 + (n - 3) * 2) * 2 ^ (1 + r))%nat) by nia.
    pose proof (Qnat_le _ _ hm_pow) as hm_pow_q.
    assert (h_odd_sub : exists n', (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r) = 1 + n' * 2)%nat)
      by (exists ((1 + (n - 3) * 2) * 2 ^ r)%nat; rewrite zP2; lia).
    destruct (proj2 IH eq_refl (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r))%nat h_odd_sub
      ltac:(push_Qnat_all; nra)) as [m' [v [a [b [hSub hm']]]]].
    rewrite hk_eq.
    exists m', (zR (1 + r) WV ++ v), (1 + (1 + a) * (1#2) * zIv r), (b * (1#2) * zIv r);
      split; [exact (BScan_even_chain r hSub) | exact hm'].
  - split; [intros [h | h]; discriminate | intros _ k [n ->] hk].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IH (or_introl eq_refl) ((n * 2) * 2)%nat
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) (fun h => ltac:(discriminate))
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v), (a * (1#2)), ((1#4) + b * (1#2));
      split; [exact (BScan_shift_pair0 hSub) | exact hm'].
  - split; [intros [h | h]; discriminate | intros _ k [n ->] hk].
    pose proof (zPrU_MS_W hS) as hWu.
    cbn [z0W] in hk; rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    assert (hn4 : (4 <= n)%nat)
      by (assert ((4 <= n \/ n <= 3)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 3 hle); push_Qnat_all; nra]).
    assert (hpow_ge : (4 <= 2 ^ (2 + r))%nat)
      by (change (2 + r)%nat with (1 + (1 + r))%nat; rewrite zP2, zP2; pose proof (zPp r); lia).
    destruct (z0F (n - 1)) as [[m hm] | [m hm]].
    + assert (hk_eq : (1 + n * 2 = 3 + m * 4)%nat) by lia.
      assert (hm_q : Qnat n == Qnat (1 + m * 2)) by (apply Qnat_eq_iff; lia).
      assert (h_even_sub : exists n', (1 + m * 2 ^ (2 + r) = 1 + n' * 2)%nat)
        by (exists (m * 2 ^ (1 + r))%nat; change (2 + r)%nat with (1 + (1 + r))%nat; rewrite zP2; lia).
      assert (hm_pow : (m * 4 <= m * 2 ^ (2 + r))%nat) by nia.
      pose proof (Qnat_le _ _ hm_pow) as hm_pow_q.
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (2 + r))%nat h_even_sub
        ltac:(push_Qnat_all; nra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WK :: (zR (1 + r) WV ++ v)), ((1 + a) * zIv r), (b * zIv r);
        split; [exact (BScan_shift_chain0 r hSub) | exact hm'].
    + assert (hk_eq : (1 + n * 2 = 5 + m * 4)%nat) by lia.
      assert (hm_q : Qnat n == Qnat (2 + m * 2)) by (apply Qnat_eq_iff; lia).
      assert (h_even_sub : exists n', (1 + m * 2 ^ (2 + r) = 1 + n' * 2)%nat)
        by (exists (m * 2 ^ (1 + r))%nat; change (2 + r)%nat with (1 + (1 + r))%nat; rewrite zP2; lia).
      assert (hm_pow : (m * 4 <= m * 2 ^ (2 + r))%nat) by nia.
      pose proof (Qnat_le _ _ hm_pow) as hm_pow_q.
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (2 + r))%nat h_even_sub
        ltac:(push_Qnat_all; nra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WQ :: (zR (1 + r) WV ++ v)), (1 + (1 + a) * zIv r), (b * zIv r);
        split; [exact (BScan_shift_chain1 r hSub) | exact hm'].
  - split; [intros _ k hE_k _ hk | intros; discriminate].
    destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    destruct (z0F n) as [[m ->] | [m ->]].
    + assert (hm1 : (1 <= m)%nat) by lia.
      assert (hk_eq : (m * 2 * 2 = 4 + (m - 1) * 4)%nat) by lia.
      assert (hm_q : Qnat m == Qnat (1 + (m - 1))) by (apply Qnat_eq_iff; lia).
      destruct (proj1 IH (or_intror eq_refl) (1 + (m - 1) * 2)%nat
        (fun h => ltac:(discriminate)) (fun _ => ex_intro _ (m - 1)%nat eq_refl)
        ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WQ :: v), ((5#2) + a * 2), (b * 2);
        split; [exact (BScan_short11 hSub) | exact hm'].
    + assert (hk_eq : ((1 + m * 2) * 2 = 2 + m * 4)%nat) by lia.
      destruct (proj1 IH (or_intror eq_refl) (1 + m * 2)%nat
        (fun h => ltac:(discriminate)) (fun _ => ex_intro _ m eq_refl)
        ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
      rewrite hk_eq.
      exists m', (WK :: v), ((3#2) + a * 2), (b * 2);
        split; [exact (BScan_short01 hSub) | exact hm'].
  - split; [intros [h | h]; discriminate | intros _ k [n ->] hk].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2) * 2)%nat
      (fun h => ltac:(discriminate)) (fun _ => ex_intro _ (n * 2)%nat eq_refl)
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v), (a * (1#2)), ((1#2) + b * (1#2));
      split; [exact (BScan_shift_pair1 hSub) | exact hm'].
  - split; [intros _ k hE_k _ hk | intros; discriminate].
    destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    assert (hk_eq : (n * 2 = 1 + (n * 2 - 1))%nat) by lia.
    assert (hn_q : Qnat (n * 2) == Qnat (1 + (n * 2 - 1))) by (apply Qnat_eq_iff; lia).
    destruct (proj1 IH (or_introl eq_refl) ((n * 2 - 1) * 2)%nat
      (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl) (fun h => ltac:(discriminate))
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
    rewrite hk_eq.
    exists m', (WV :: v), (a * (1#2)), ((1#4) + b * (1#2));
      split; [exact (BScan_pair0 hSub) | exact hm'].
  - split; [intros _ k _ hO_k hk | intros; discriminate].
    destruct (hO_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IH (or_introl eq_refl) ((n * 2) * 2)%nat
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) (fun h => ltac:(discriminate))
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v), (a * (1#2)), ((1#4) + b * (1#2));
      split; [exact (BScan_pair0 hSub) | exact hm'].
  - split; [intros _ k hE_k _ hk | intros; discriminate].
    destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat)
      by (assert ((2 <= n \/ n <= 1)%nat) as [? | hle] by lia;
          [assumption | pose proof (Qnat_le n 1 hle); push_Qnat_all; lra]).
    assert (hk_eq : (n * 2 = 1 + (n * 2 - 1))%nat) by lia.
    assert (hn_q : Qnat (n * 2) == Qnat (1 + (n * 2 - 1))) by (apply Qnat_eq_iff; lia).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2 - 1) * 2)%nat
      (fun h => ltac:(discriminate)) (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl)
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
    rewrite hk_eq.
    exists m', (WV :: v), (a * (1#2)), ((1#2) + b * (1#2));
      split; [exact (BScan_pair1 hSub) | exact hm'].
  - split; [intros _ k _ hO_k hk | intros; discriminate].
    destruct (hO_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2) * 2)%nat
      (fun h => ltac:(discriminate)) (fun _ => ex_intro _ (n * 2)%nat eq_refl)
      ltac:(push_Qnat_all; lra)) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v), (a * (1#2)), ((1#2) + b * (1#2));
      split; [exact (BScan_pair1 hSub) | exact hm'].
Qed.

Lemma zDg_zero_Z {A H : nat} {w : zW} (h : zDg A H w) (h0 : A = 0%nat) :
    z0Z w == Qnat (2 ^ H) - 1.
Proof.
  induction h as [| A1 H1 u1 _ IH | A1 H1 u1 _ _].
  - cbn [z0Z Nat.pow]; reflexivity.
  - assert (hA1 : A1 = 0%nat) by lia.
    rewrite Qnat_pow2_1_add; cbn [z0Z]; rewrite (IH hA1); ring.
  - lia.
Qed.

Lemma zPiece3 {n_mid : nat} (hn : (2 <= n_mid)%nat) :
    exists m_end d1_t a_t b_t,
      BScan false (n_mid * 4) [WK; WQ; WQ; WQ; WQ; WK] (m_end * 8) [WQ; d1_t; WV; WV] a_t b_t /\
      z11 [WQ; d1_t; WV; WV] == 1 /\
      z0W [WQ; d1_t; WV; WV] <= (15#4) /\
      z0L [WQ; d1_t; WV; WV] = true /\
      a_t - b_t <= 6 /\
      b_t - a_t <= 0.
Proof.
  destruct (z0F (n_mid - 1)) as [[m1 hm1] | [m1 hm1]].
  - assert (hk0 : (n_mid * 4 = 4 + ((m1 - 1) * 2 + 2) * 4)%nat) by lia.
    assert (hk1 : (((m1 - 1) * 2 + 2) * 2 = 4 + (m1 - 1) * 4)%nat) by lia.
    assert (hB0 : BScan false (1 + ((m1 - 1) * 2) * 2) [WQ; WK] ((m1 - 1) * 8) [WV] (0 * (1#2)) ((1#4) + 0 * (1#2))).
    { pose proof (BScan_pair0 (BScan_nil (((m1 - 1) * 2) * 2 * 2))) as h.
      replace (((m1 - 1) * 2) * 2 * 2)%nat with ((m1 - 1) * 8)%nat in h by lia.
      exact h. }
    pose proof (BScan_pair1 hB0) as hB1.
    pose proof (BScan_short11 hB1) as hB2.
    rewrite <- hk1 in hB2.
    pose proof (BScan_short10 hB2) as hB3.
    rewrite <- hk0 in hB3.
    eexists (m1 - 1)%nat, WQ, _, _.
    split; [exact hB3 | cbn [z11 z0W z0L]; split; [lra | split; [lra | split; [reflexivity | split; lra]]]].
  - assert (hk0 : (n_mid * 4 = 4 + (1 + m1 * 2) * 4)%nat) by lia.
    assert (hk1 : ((1 + m1 * 2) * 2 = 2 + m1 * 4)%nat) by lia.
    assert (hB0 : BScan false (1 + (m1 * 2) * 2) [WQ; WK] (m1 * 8) [WV] (0 * (1#2)) ((1#4) + 0 * (1#2))).
    { pose proof (BScan_pair0 (BScan_nil ((m1 * 2) * 2 * 2))) as h.
      replace ((m1 * 2) * 2 * 2)%nat with (m1 * 8)%nat in h by lia.
      exact h. }
    pose proof (BScan_pair1 hB0) as hB1.
    pose proof (BScan_short01 hB1) as hB2.
    rewrite <- hk1 in hB2.
    pose proof (BScan_short10 hB2) as hB3.
    rewrite <- hk0 in hB3.
    eexists m1, WK, _, _.
    split; [exact hB3 | cbn [z11 z0W z0L]; split; [lra | split; [lra | split; [reflexivity | split; lra]]]].
Qed.

Lemma z1l {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
    (h1 : BScan s k u k' v a b) :
    forall {r r' : side}, BRIncs false k' r r' -> BRIncs s k (zTs u r) (zTs v r').
Proof.
  induction h1 as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH |
    r_ch m u k v a b _ IH | r_ch m u k v a b _ IH | r_ch m u k v a b _ IH |
    n u k v a b _ IH | n u k v a b _ IH | r_ch m u k v a b _ IH | r_ch m u k v a b _ IH];
    intros r r' h2.
  - exact h2.
  - exact (BRIncs_T (IH r r' h2)).
  - exact (BRIncs_pair0 (IH r r' h2)).
  - exact (BRIncs_pair1 (IH r r' h2)).
  - exact (BRIncs_short00 (IH r r' h2)).
  - exact (BRIncs_short01 (IH r r' h2)).
  - exact (BRIncs_short10 (IH r r' h2)).
  - exact (BRIncs_short11 (IH r r' h2)).
  - change (WV :: u) with ([WV] ++ u); rewrite zQK_append, z0S; cbn [zTs]; rewrite z0S.
    exact (BRIncs_odd_chain0 r_ch (IH r r' h2)).
  - change (WV :: u) with ([WV] ++ u); rewrite zQK_append, z0S; cbn [zTs]; rewrite z0S.
    exact (BRIncs_odd_chain1 r_ch (IH r r' h2)).
  - cbn [zTs]; change (WV :: u) with ([WV] ++ u); rewrite zQK_append, z0S, z0S.
    exact (BRIncs_even_chain r_ch (IH r r' h2)).
  - exact (BRIncs_shift_pair0 (IH r r' h2)).
  - exact (BRIncs_shift_pair1 (IH r r' h2)).
  - cbn [zTs]; change (WV :: u) with ([WV] ++ u); rewrite zQK_append, z0S, z0S.
    exact (BRIncs_shift_chain0 r_ch (IH r r' h2)).
  - cbn [zTs]; change (WV :: u) with ([WV] ++ u); rewrite zQK_append, z0S, z0S.
    exact (BRIncs_shift_chain1 r_ch (IH r r' h2)).
Qed.


(* Stage 4 Part A: Section 7D (P33, BGood, BStep, z1N, Choice, Rounds, z28) *)

From Coq Require Import BinNat Pnat Nnat.

Definition zP33 : zW :=
  [WV; WV; WQ; WV; WV; WQ; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV;
   WQ; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV; WK].
Definition zOut33 : zW :=
  [WV; WQ; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV; WK;
   WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV; WK; WV; WV; WK; WV].
Definition zTail8 : zW := [WQ; WQ; WK; WK; WQ; WQ; WQ; WQ].

Lemma zDg_tail8 : zDg 243 8 zTail8.
Proof.
  exact (zDg_one (zDg_one (zDg_zero (zDg_zero (zDg_one (zDg_one (zDg_one (zDg_one zDg_nil)))))))).
Qed.

Lemma zP3_11 (m : nat) {k_in k_out : nat} {r r' : side}
    (h1 : k_in = (4 + m * 2)%nat) (h2 : k_out = (1 + m * 4)%nat)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t *> (t *> (d1 *> r))) (t *> (d1 *> (t *> r'))).
Proof.
  replace k_out with (1 + (m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_odd_chain1 0 (BRIncs_shift_pair1 h)) as h_oc.
  replace (5 + m * 4)%nat with (1 + (2 + m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (2 + m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_01 (m : nat) {k_in k_out : nat} {r r' : side}
    (h1 : k_in = (3 + m * 2)%nat) (h2 : k_out = (1 + m * 4)%nat)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t *> (t *> (d1 *> r))) (t *> (d0 *> (t *> r'))).
Proof.
  replace k_out with (1 + (m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_odd_chain0 0 (BRIncs_shift_pair1 h)) as h_oc.
  replace (3 + m * 4)%nat with (1 + (1 + m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (1 + m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_00 (m : nat) {k_in k_out : nat} {r r' : side}
    (h1 : k_in = (3 + m * 2)%nat) (h2 : k_out = (m * 4)%nat)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t *> (t *> (d0 *> r))) (t *> (d0 *> (t *> r'))).
Proof.
  replace k_out with ((m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_odd_chain0 0 (BRIncs_shift_pair0 h)) as h_oc.
  replace (3 + m * 4)%nat with (1 + (1 + m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (1 + m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_10 (m : nat) {k_in k_out : nat} {r r' : side}
    (h1 : k_in = (4 + m * 2)%nat) (h2 : k_out = (m * 4)%nat)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t *> (t *> (d0 *> r))) (t *> (d1 *> (t *> r'))).
Proof.
  replace k_out with ((m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_odd_chain1 0 (BRIncs_shift_pair0 h)) as h_oc.
  replace (5 + m * 4)%nat with (1 + (2 + m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (2 + m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Definition N_124522 : nat := N.to_nat 124522%N.
Definition N_249044 : nat := (N_124522 * 2)%nat.

Lemma Qnat_N_to_nat (n : N) : Qnat (N.to_nat n) == inject_Z (Z.of_N n).
Proof. unfold Qnat; rewrite N_nat_Z; reflexivity. Qed.

Lemma Qnat_249044 : Qnat N_249044 == 249044.
Proof.
  unfold N_249044, N_124522.
  rewrite Qnat_mul, Qnat_N_to_nat; reflexivity.
Qed.

Lemma Qnat_pow2_8 : Qnat (2 ^ 8) == 256.
Proof. vm_compute; reflexivity. Qed.

Lemma Qnat_pow2_9 : Qnat (2 ^ 9) == 512.
Proof. vm_compute; reflexivity. Qed.

Lemma Qnat_pow2_16 : Qnat (2 ^ 16) == 65536.
Proof.
  change 16%nat with (8 + 8)%nat.
  rewrite Nat.pow_add_r, Qnat_mul; vm_compute; reflexivity.
Qed.

Lemma Qnat_pow2_17 : Qnat (2 ^ 17) == 131072.
Proof.
  change 17%nat with (8 + 9)%nat.
  rewrite Nat.pow_add_r, Qnat_mul; vm_compute; reflexivity.
Qed.

Lemma nat_lin_eq (a b c d : N) :
    (a = c + b * d)%N -> N.to_nat a = (N.to_nat c + N.to_nat b * N.to_nat d)%nat.
Proof. intros ->; rewrite N2Nat.inj_add, N2Nat.inj_mul; reflexivity. Qed.

Lemma nat_mul_eq (a b d : N) :
    (a = b * d)%N -> N.to_nat a = (N.to_nat b * N.to_nat d)%nat.
Proof. intros ->; rewrite N2Nat.inj_mul; reflexivity. Qed.

Lemma zBRIncs_P33 {r r' : side} (h : BRIncs false N_249044 r r') :
    BRIncs false 128 (zTs zP33 r) (zTs zOut33 r').
Proof.
  unfold zP33, zOut33; cbn [zTs].
  change 128%nat with (N.to_nat 128%N).
  eapply (zP3_11 (N.to_nat 62%N) (k_out := N.to_nat 249%N));
    [apply (nat_lin_eq 128 62 4 2); reflexivity | apply (nat_lin_eq 249 62 1 4); reflexivity |].
  eapply (zP3_01 (N.to_nat 123%N) (k_out := N.to_nat 493%N));
    [apply (nat_lin_eq 249 123 3 2); reflexivity | apply (nat_lin_eq 493 123 1 4); reflexivity |].
  eapply (zP3_00 (N.to_nat 245%N) (k_out := N.to_nat 980%N));
    [apply (nat_lin_eq 493 245 3 2); reflexivity | apply (nat_mul_eq 980 245 4); reflexivity |].
  eapply (zP3_10 (N.to_nat 488%N) (k_out := N.to_nat 1952%N));
    [apply (nat_lin_eq 980 488 4 2); reflexivity | apply (nat_mul_eq 1952 488 4); reflexivity |].
  eapply (zP3_11 (N.to_nat 974%N) (k_out := N.to_nat 3897%N));
    [apply (nat_lin_eq 1952 974 4 2); reflexivity | apply (nat_lin_eq 3897 974 1 4); reflexivity |].
  eapply (zP3_01 (N.to_nat 1947%N) (k_out := N.to_nat 7789%N));
    [apply (nat_lin_eq 3897 1947 3 2); reflexivity | apply (nat_lin_eq 7789 1947 1 4); reflexivity |].
  eapply (zP3_00 (N.to_nat 3893%N) (k_out := N.to_nat 15572%N));
    [apply (nat_lin_eq 7789 3893 3 2); reflexivity | apply (nat_mul_eq 15572 3893 4); reflexivity |].
  eapply (zP3_10 (N.to_nat 7784%N) (k_out := N.to_nat 31136%N));
    [apply (nat_lin_eq 15572 7784 4 2); reflexivity | apply (nat_mul_eq 31136 7784 4); reflexivity |].
  eapply (zP3_11 (N.to_nat 15566%N) (k_out := N.to_nat 62265%N));
    [apply (nat_lin_eq 31136 15566 4 2); reflexivity | apply (nat_lin_eq 62265 15566 1 4); reflexivity |].
  eapply (zP3_01 (N.to_nat 31131%N) (k_out := N.to_nat 124525%N));
    [apply (nat_lin_eq 62265 31131 3 2); reflexivity | apply (nat_lin_eq 124525 31131 1 4); reflexivity |].
  eapply (zP3_00 (N.to_nat 62261%N) (k_out := N_249044));
    [apply (nat_lin_eq 124525 62261 3 2); reflexivity |
     unfold N_249044, N_124522; change 2%nat with (N.to_nat 2%N);
     rewrite <- (N2Nat.inj_mul 124522 2); apply (nat_mul_eq 249044 62261 4); reflexivity |].
  exact h.
Qed.

Opaque N_124522 N_249044.

Lemma N_249044_even : exists n, N_249044 = (n * 2)%nat.
Proof. Transparent N_249044. exists N_124522; reflexivity. Opaque N_249044. Qed.

Inductive BGood : zW -> Prop :=
  | BGood_intro (H : nat) (u : zW) (A : nat) (hi8 : zW) :
      zDg A H hi8 ->
      z11 u * Qnat (2 ^ H) == 128 ->
      z11 u <= (1#16) ->
      (exists w, u = WV :: WV :: (w ++ [WV])) ->
      z0L u = true ->
      (exists w, hi8 = WQ :: WK :: w) ->
      z0W u <= (74#5) ->
      z11 u * z0Z hi8 <= (1273#10) ->
      BGood (u ++ (hi8 ++ zTail8)).

Inductive BStep : zW -> zW -> Prop :=
  | BStep_intro (orig : zW) (n : nat) (v : zW) (a b : Rat) (J : nat) (ds : zW) :
      BScan false N_249044 (orig ++ [WK]) (n * 2) v a b ->
      zDg (1 + n) J ds ->
      BStep orig ([WV; WV; WK; WV] ++ v ++ ds).

Lemma z1N {orig : zW} (hG : BGood orig) :
    exists out, BStep orig out /\ BGood out.
Proof.
  destruct hG as [H u A hi8 hDig hHeight hU11 [wu hwu] hLu [w0 hw0] hWu_max hZ_max].
  pose proof (proj2 (proj2 (proj2 (zWn u)))) as hWu_nonneg.
  pose proof (zSp u) as hSu.
  assert (hPrU : zPrU ME u) by (rewrite hwu; exact (zPrU_ME_VV wu)).
  assert (hk_in : 16 * z0W u < Qnat N_249044 - 3)
    by (rewrite Qnat_249044; lra).
  destruct (proj1 (zPrU_bscan hPrU) (or_introl eq_refl) N_249044
    (fun _ => N_249044_even) (fun h => ltac:(discriminate)) hk_in)
    as [m1 [v1 [a1 [b1 [hB1 hm1]]]]].
  pose proof (zSp v1) as hSv1.
  pose proof (proj2 (proj2 (proj2 (zWn v1)))) as hWv1_nonneg.
  assert (h11_v1 : z11 v1 <= (1#8) * z11 u).
  { pose proof (z1p_z0L hB1 hLu) as hp; cbn [zSwt] in hp; lra. }
  destruct (proj1 (z1j hB1) eq_refl) as [hW_v1 [hAB_1 hBA_1]].
  pose proof (z1i hB1) as hBud1.
  rewrite Qnat_249044 in hBud1.
  subst hi8.
  destruct (zD1 hDig) as [A1 [H1 [hD1 [hA1 hH1]]]].
  destruct (zD0 hD1) as [A0 [H0 [hD0 [hA0 hH0]]]].
  destruct (zDw hD0) as [hDw0_1 [hDw0_2 hDw0_3]].
  pose proof (zSp w0) as hSw0.
  pose proof (proj1 (proj2 (zWn w0))) as hZw0_nonneg.
  assert (hPowH : Qnat (2 ^ H) == 4 * z11 w0).
  { rewrite hH1, hH0, Qnat_pow2_1_add, Qnat_pow2_1_add; lra. }
  assert (hZ_hi8 : z0Z (WQ :: WK :: w0) == 2 + 4 * z0Z w0) by (cbn [z0Z]; ring).
  assert (hA0_pos : (0 < A0)%nat).
  { assert ((0 < A0 \/ A0 = 0)%nat) as [? | hA0_0] by lia; [assumption |].
    pose proof (zDg_zero_Z hD0 hA0_0) as hZw0_0.
    rewrite <- hDw0_1 in hZw0_0.
    assert (h_prod : z11 u * z0Z (WQ :: WK :: w0) + 2 * z11 u == z11 u * (4 * z11 w0))
      by (rewrite hZ_hi8, hZw0_0; ring).
    assert (h_pow_u : z11 u * Qnat (2 ^ H) == z11 u * (4 * z11 w0))
      by (rewrite hPowH; ring).
    lra. }
  pose proof (zDg_pos_z0L hD0 hA0_pos) as hLw0.
  assert (hY_w0qqk : z0Y (w0 ++ [WQ; WQ; WK]) == z0Y w0 + 7 * z11 w0)
    by (rewrite z13; cbn [z0Y]; ring).
  assert (hZ_w0qqk : z0Z (w0 ++ [WQ; WQ; WK]) == z0Z w0 + 4 * z11 w0)
    by (rewrite z14; cbn [z0Z]; ring).
  assert (hScan_cond : (z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2 < Qnat (m1 * 2)).
  { assert (h_yw0 : z0Y w0 == z11 w0 - 1) by lra.
    rewrite Qnat_add in hBud1; rewrite Qnat_mul;
      change (Qnat 1) with 1 in hBud1; change (Qnat 2) with 2.
    pose proof (Qnat_nonneg m1) as hm1_nn.
    assert (hm1_ub : (Qnat m1 * 2) * z11 v1 <= (Qnat m1 * 2) * ((1#8) * z11 u)) by (clear - hm1_nn h11_v1; nra).
    assert (h_bud1_exp : (1 + Qnat m1 - 3) * z11 v1 == (1#2) * ((Qnat m1 * 2) * z11 v1) - 2 * z11 v1) by ring.
    assert (h_lhs_u : z11 u * ((z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2) ==
        6 * (z11 u * (4 * z11 w0)) + (1#2) * (z11 u * z0Z (WQ :: WK :: w0)) - 3 * z11 u)
      by (rewrite hY_w0qqk, hZ_w0qqk, h_yw0, hZ_hi8; ring).
    assert (h_pow_u : z11 u * Qnat (2 ^ H) == z11 u * (4 * z11 w0)) by (rewrite hPowH; ring).
    assert (h_rhs_u : (Qnat m1 * 2) * ((1#8) * z11 u) == (1#8) * (z11 u * (Qnat m1 * 2))) by ring.
    assert (h_lt_u : z11 u * ((z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2) < z11 u * (Qnat m1 * 2))
      by lra.
    clear - hSu h_lt_u; nra. }
  destruct (z1a (w0 ++ [WQ; WQ; WK]) m1 hScan_cond) as [b2 [y [l2 [hS2 _]]]].
  destruct (zScan_qqk hS2 w0 eq_refl) as [_ [h11_y_fn [[n_mid hb2_eq] [y0 hy0]]]].
  subst b2.
  assert (h11_y : z11 (WV :: y) <= (1#64) * Qnat (2 ^ H)).
  { pose proof (h11_y_fn hLw0) as hy.
    assert (h11_qqk : z11 (w0 ++ [WQ; WQ; WK]) == 8 * z11 w0)
      by (rewrite z16; cbn [z11]; ring).
    cbn [z11]; lra. }
  destruct (zHi_bscan hS2 hD0) as [a2 [b2_r [hB2 [hY_vy [hAB_2 hBA_2]]]]].
  assert (hW_vy : z0W (WV :: y) <= (11#32) * z0Z (WQ :: WK :: w0)).
  { pose proof (proj2 (zWY (WV :: y))); lra. }
  destruct (z1k hB1 hB2) as [a12 [b12 [hB12 [ha12 hb12]]]].
  assert (h11_v12 : z11 (v1 ++ (WV :: y)) <= (1#4)).
  { rewrite z16.
    pose proof (zSp (WV :: y)) as hS_vy.
    assert (h_prod : z11 v1 * z11 (WV :: y) <= ((1#8) * z11 u) * ((1#64) * Qnat (2 ^ H)))
      by (clear - h11_v1 h11_y hSv1 hS_vy; nra).
    assert (h_eq : ((1#8) * z11 u) * ((1#64) * Qnat (2 ^ H)) == (1#512) * (z11 u * Qnat (2 ^ H))) by ring.
    lra. }
  pose proof (zSp (v1 ++ (WV :: y))) as hSv12.
  pose proof (z1i hB12) as hBud12.
  rewrite Qnat_249044 in hBud12.
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
  { assert ((2 <= n_mid \/ n_mid <= 1)%nat) as [? | hle] by lia; [assumption |].
    pose proof (Qnat_le n_mid 1 hle) as hq.
    rewrite Qnat_mul in hBud12; change (Qnat 1) with 1 in hq; change (Qnat 4) with 4 in hBud12.
    assert (h_ub : (Qnat n_mid * 4 - 3) * z11 (v1 ++ (WV :: y)) <= 1)
      by (clear - hq h11_v12 hSv12; nra).
    lra. }
  destruct (zPiece3 hn_mid2) as [m_end [d1_tok [a3 [b3 [hB3 [h11_p3 [hW_p3 [hL_p3 [hAB_3 hBA_3]]]]]]]]].
  destruct (z1k hB12 hB3) as [a [b [hB_all [ha_all hb_all]]]].
  set (v := (v1 ++ (WV :: y)) ++ [WQ; d1_tok; WV; WV]).
  assert (h11_v : z11 v == z11 (v1 ++ (WV :: y)))
    by (unfold v; rewrite z16, h11_p3; ring).
  pose proof (zSp v) as hSv.
  assert (h11_v_le : z11 v <= (1#4)) by lra.
  assert (hW_v : z0W v <= (66#19) * z0W u + (11#256) * (z11 u * z0Z (WQ :: WK :: w0)) + (15#16)).
  { unfold v; rewrite z13W, z13W.
    pose proof (proj2 (proj2 (proj2 (zWn [WQ; d1_tok; WV; WV])))) as hW_p3_nn.
    pose proof (proj2 (proj2 (proj2 (zWn (WV :: y))))) as hW_vy_nn.
    assert (hp1 : z11 v1 * z0W (WV :: y) <= ((1#8) * z11 u) * ((11#32) * z0Z (WQ :: WK :: w0)))
      by (clear - h11_v1 hW_vy hSv1 hW_vy_nn; nra).
    assert (hp2 : z11 (v1 ++ (WV :: y)) * z0W [WQ; d1_tok; WV; WV] <= (1#4) * (15#4))
      by (clear - h11_v12 hW_p3 hSv12 hW_p3_nn; nra).
    assert (hp1_eq : ((1#8) * z11 u) * ((11#32) * z0Z (WQ :: WK :: w0)) == (11#256) * (z11 u * z0Z (WQ :: WK :: w0))) by ring.
    lra. }
  assert (hAB : a - b <= (508#5)).
  { assert (hp2 : z11 (v1 ++ (WV :: y)) * (a3 - b3) <= (1#4) * 6)
      by (clear - h11_v12 hAB_3 hSv12; nra).
    assert (h_diff : a - b == (a12 - b12) + z11 (v1 ++ (WV :: y)) * (a3 - b3))
      by (rewrite ha_all, hb_all; ring).
    lra. }
  assert (hBA : b - a <= 8).
  { assert (hp1 : z11 v1 * (b2_r - a2) <= z11 v1) by (clear - hSv1 hBA_2; nra).
    assert (hp2 : z11 (v1 ++ (WV :: y)) * (b3 - a3) <= 0) by (clear - hSv12 hBA_3; nra).
    assert (h_diff : b - a == (b1 - a1) + z11 v1 * (b2_r - a2) + z11 (v1 ++ (WV :: y)) * (b3 - a3))
      by (rewrite ha_all, hb_all, ha12, hb12; ring).
    lra. }
  assert (hY_v_lt : z0Y v < Qnat (2 ^ 17)).
  { pose proof (proj1 (zWY v)); rewrite Qnat_pow2_17; lra. }
  destruct (z1B v 17 hY_v_lt) as [J hHn].
  pose proof (z1x v 17 J hHn) as hUnit.
  assert (hJ10 : (10 <= J)%nat).
  { assert ((10 <= J \/ J <= 9)%nat) as [? | hJ9] by lia; [assumption |].
    assert (hpow9 : (2 ^ J <= 2 ^ 9)%nat) by (apply Nat.pow_le_mono_r; lia).
    pose proof (Qnat_le _ _ hpow9) as hpow9_q.
    rewrite Qnat_pow2_9 in hpow9_q.
    rewrite Qnat_pow2_17 in hUnit.
    clear - hpow9_q hUnit h11_v_le hSv; nra. }
  set (H8' := (J - 8)%nat).
  assert (hH8'_2 : (2 <= H8')%nat) by lia.
  assert (hJ_eq : J = (H8' + 8)%nat) by lia.
  assert (hUnit_H8' : z11 v * Qnat (2 ^ H8') == 512).
  { rewrite hJ_eq, Nat.pow_add_r, Qnat_mul, Qnat_pow2_8, Qnat_pow2_17 in hUnit.
    lra. }
  pose proof (z1i hB_all) as hBud.
  rewrite Qnat_249044 in hBud.
  change (z11 ((v1 ++ (WV :: y)) ++ [WQ; d1_tok; WV; WV])) with (z11 v) in hBud.
  assert (hBud_v : (Qnat m_end * 8) * z11 v == 249041 + 3 * z11 v - 2 * (a - b)).
  { rewrite Qnat_mul in hBud; change (Qnat 8) with 8 in hBud.
    assert (h2 : (Qnat m_end * 8 - 3) * z11 v == (Qnat m_end * 8) * z11 v - 3 * z11 v) by ring.
    lra. }
  set (B := (1 + m_end * 4)%nat).
  assert (hB_cast : Qnat B == 1 + Qnat m_end * 4)
    by (unfold B; rewrite Qnat_add, Qnat_mul; change (Qnat 1) with 1; change (Qnat 4) with 4; reflexivity).
  assert (hB_lo : (243 * 2 ^ H8' <= B)%nat).
  { apply Qnat_le_iff.
    rewrite Qnat_mul; change (Qnat 243) with 243.
    assert (h_b_v : (Qnat B - 243 * Qnat (2 ^ H8')) * z11 v ==
        z11 v + (1#2) * ((Qnat m_end * 8) * z11 v) - 243 * (z11 v * Qnat (2 ^ H8')))
      by (rewrite hB_cast; ring).
    assert (h_pos_v : 0 < (Qnat B - 243 * Qnat (2 ^ H8')) * z11 v) by lra.
    clear - h_pos_v hSv; nra. }
  assert (hB_hi : (B < 244 * 2 ^ H8')%nat).
  { apply Qnat_lt_iff.
    rewrite Qnat_mul; change (Qnat 244) with 244.
    assert (h_b_v : (244 * Qnat (2 ^ H8') - Qnat B) * z11 v ==
        244 * (z11 v * Qnat (2 ^ H8')) - z11 v - (1#2) * ((Qnat m_end * 8) * z11 v))
      by (rewrite hB_cast; ring).
    assert (h_pos_v : 0 < (244 * Qnat (2 ^ H8') - Qnat B) * z11 v) by lra.
    clear - h_pos_v hSv; nra. }
  set (A8' := (B - 243 * 2 ^ H8')%nat).
  assert (hA8'_lt : (A8' < 2 ^ H8')%nat) by lia.
  destruct (z0T H8' A8' hA8'_lt) as [hi8' hD_hi8'].
  assert (hA8'_mod : exists m', A8' = (1 + m' * 4)%nat).
  { assert (hpow4 : (2 ^ H8' = 2 ^ (H8' - 2) * 4)%nat).
    { replace H8' with ((H8' - 2) + 2)%nat at 1 by lia.
      rewrite Nat.pow_add_r; change (2 ^ 2)%nat with 4%nat; lia. }
    exists (m_end - 243 * 2 ^ (H8' - 2))%nat.
    unfold A8', B; lia. }
  destruct hA8'_mod as [m_a8 hm_a8].
  assert (hLow' : exists w, hi8' = WQ :: WK :: w).
  { rewrite hm_a8 in hD_hi8'; exact (z1K hD_hi8' hH8'_2). }
  assert (hD_ds' : zDg (1 + m_end * 4) J (hi8' ++ zTail8)).
  { pose proof (z0U hD_hi8' zDg_tail8) as hU.
    replace (A8' + 243 * 2 ^ H8')%nat with (1 + m_end * 4)%nat in hU by (unfold A8', B; lia).
    rewrite <- hJ_eq in hU; exact hU. }
  set (u' := [WV; WV; WK; WV] ++ v).
  assert (h11_u' : z11 u' == (1#4) * z11 v) by (unfold u'; cbn [app z11]; ring).
  assert (hW_u' : z0W u' == (11#32) + (1#4) * z0W v) by (unfold u'; cbn [app z0W]; ring).
  pose proof (z17 hD_hi8') as hDef'.
  assert (hA8'_q : Qnat A8' + 243 * Qnat (2 ^ H8') == 1 + Qnat m_end * 4).
  { assert (heq : (A8' + 243 * 2 ^ H8' = 1 + m_end * 4)%nat) by (unfold A8', B; lia).
    apply Qnat_eq_iff in heq.
    rewrite Qnat_add, Qnat_mul, Qnat_add, Qnat_mul in heq;
      change (Qnat 243) with 243 in heq;
      change (Qnat 1) with 1 in heq;
      change (Qnat 4) with 4 in heq.
    exact heq. }
  assert (hZ_new : z11 u' * z0Z hi8' <= (1273#10)).
  { assert (h1 : z0Z hi8' == Qnat (2 ^ H8') - 1 - Qnat A8') by lra.
    assert (h2 : Qnat A8' == 1 + Qnat m_end * 4 - 243 * Qnat (2 ^ H8')) by lra.
    assert (h_z_prod : z11 u' * z0Z hi8' ==
        (244#4) * (z11 v * Qnat (2 ^ H8')) - (1#2) * z11 v -
        (1#8) * ((Qnat m_end * 8) * z11 v))
      by (rewrite h11_u', h1, h2; ring).
    lra. }
  assert (hHeight' : z11 u' * Qnat (2 ^ H8') == 128).
  { rewrite h11_u'; lra. }
  exists (u' ++ (hi8' ++ zTail8)); split.
  - assert (h_in_eq : (u ++ ((WQ :: WK :: w0) ++ zTail8)) ++ [WK] =
        (u ++ ((WQ :: WK :: w0) ++ [WQ; WQ; WK])) ++ [WK; WQ; WQ; WQ; WQ; WK]).
    { unfold zTail8; repeat rewrite <- app_assoc; reflexivity. }
    assert (h_out_eq : u' ++ (hi8' ++ zTail8) = [WV; WV; WK; WV] ++ v ++ (hi8' ++ zTail8)).
    { unfold u'; repeat rewrite <- app_assoc; reflexivity. }
    rewrite h_out_eq.
    refine (BStep_intro _ (m_end * 4) v a b J (hi8' ++ zTail8) _ hD_ds').
    replace ((m_end * 4) * 2)%nat with (m_end * 8)%nat by lia.
    rewrite h_in_eq; exact hB_all.
  - refine (BGood_intro H8' u' A8' hi8' hD_hi8' hHeight' ltac:(lra) _ _ hLow' ltac:(lra) hZ_new).
    + exists ([WK; WV] ++ v1 ++ (WV :: y) ++ [WQ; d1_tok; WV]).
      unfold u', v; repeat rewrite <- app_assoc; reflexivity.
    + assert (heq_u' : u' = ([WV; WV; WK; WV] ++ (v1 ++ (WV :: y))) ++ [WQ; d1_tok; WV; WV])
        by (unfold u', v; repeat rewrite <- app_assoc; reflexivity).
      rewrite heq_u'; exact (z1I _ _ hL_p3).
Qed.

Lemma z1P {A H : nat} {da : zW} (hD : zDg A H da) (hZ : A = 0%nat) :
    zTs da 0inf = 0inf.
Proof.
  induction hD as [| A H u _ IH | A H u _ _].
  - reflexivity.
  - assert (hA0 : A = 0%nat) by lia.
    cbn [zTs]; rewrite (IH hA0), zDd; reflexivity.
  - lia.
Qed.

Lemma z1Q {A H : nat} {da : zW} (hD : zDg A H da) (hPos : (0 < A)%nat) :
    BRIncs false ((A - 1) * 2) 0inf (zTs da 0inf).
Proof.
  induction hD as [| A H u _ IH | A H u hDu IH].
  - lia.
  - assert (hA_pos : (0 < A)%nat) by lia.
    pose proof (BRIncs_short00 (IH hA_pos)) as hs.
    rewrite zDd in hs.
    replace ((A * 2 - 1) * 2)%nat with (2 + (A - 1) * 4)%nat by lia.
    exact hs.
  - destruct A as [| A].
    + cbn [zTs]; rewrite (z1P hDu eq_refl).
      pose proof (BRIncs_zero 0inf) as h0.
      assert (hd : d1 *> 0inf = one *> 0inf) by solve_const0_eq.
      rewrite hd; exact h0.
    + assert (hA_pos : (0 < S A)%nat) by lia.
      pose proof (IH hA_pos) as hIH.
      replace ((S A - 1) * 2)%nat with (A * 2)%nat in hIH by lia.
      pose proof (BRIncs_short10 hIH) as hs.
      rewrite zDd in hs.
      replace ((1 + S A * 2 - 1) * 2)%nat with (4 + A * 4)%nat by lia.
      exact hs.
Qed.

Lemma z1R {orig out : zW} (hS : BStep orig out) :
    exists r, BRIncs false 128 (zTs (zP33 ++ orig) 0inf) r /\
      zTs (zP33 ++ out) 0inf = zTs [WV; WV; WQ; WV] r.
Proof.
  destruct hS as [orig n v a b J ds hI hD].
  assert (hB : BRIncs false (n * 2) 0inf (zTs ds 0inf)).
  { replace (n * 2)%nat with ((1 + n - 1) * 2)%nat by lia.
    exact (z1Q hD ltac:(lia)). }
  assert (hR_orig : BRIncs false N_249044 (zTs orig 0inf) (zTs (v ++ ds) 0inf)).
  { pose proof (z1l hI hB) as hR.
    rewrite z0S in hR; cbn [zTs] in hR; rewrite zDd, <- z0S in hR.
    exact hR. }
  pose proof (zBRIncs_P33 hR_orig) as hR_p33.
  exists (zTs (zOut33 ++ (v ++ ds)) 0inf); split.
  - rewrite z0S, z0S; exact hR_p33.
  - assert (h_eq : zP33 ++ ([WV; WV; WK; WV] ++ v ++ ds) = [WV; WV; WQ; WV] ++ (zOut33 ++ (v ++ ds)))
      by (unfold zP33, zOut33; repeat rewrite <- app_assoc; reflexivity).
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
  | [], u => Some u
  | WV :: p', WV :: u' => zSw p' u'
  | WK :: p', WK :: u' => zSw p' u'
  | WQ :: p', WQ :: u' => zSw p' u'
  | _, _ => None
  end.

Lemma z1T (p : zW) :
    forall (u v : zW), zSw p u = Some v -> u = p ++ v.
Proof.
  induction p as [| w p IH]; intros u v h.
  - cbn in h; inversion h; reflexivity.
  - destruct u as [| x u']; [destruct w; discriminate |].
    destruct w, x; try discriminate; cbn in h; rewrite (IH u' v h); reflexivity.
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
  destruct w; try discriminate.
  cbn [forallb z1U] in h.
  cbn [zTs]; rewrite (IH h), zDd; reflexivity.
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

Definition zGetN (ch : Choice) (k : N) : N :=
  match ch with
  | CT => (k - 2)%N
  | CP0 | CP1 | CSP0 | CSP1 => (k - 1)%N
  | CS00 | CS01 => N.div (k - 2) 4
  | CS10 | CS11 => N.div (k - 4) 4
  | COC0 _ | CSC0 _ => N.div (k - 3) 4
  | COC1 _ | CSC1 _ => N.div (k - 5) 4
  | CEC _ => N.div (k - 6) 2
  end.

Definition z1W (ch : Choice) (n : N) : N :=
  match ch with
  | CT => (2 + n)%N
  | CP0 | CP1 | CSP0 | CSP1 => (1 + n)%N
  | CS00 | CS01 => (2 + n * 4)%N
  | CS10 | CS11 => (4 + n * 4)%N
  | COC0 _ | CSC0 _ => (3 + n * 4)%N
  | COC1 _ | CSC1 _ => (5 + n * 4)%N
  | CEC _ => (6 + n * 2)%N
  end.

Definition z1X (ch : Choice) (n : N) : N :=
  match ch with
  | CT | CP1 | CS01 | CS11 | CSP1 => (1 + n * 2)%N
  | CP0 | CS00 | CS10 | CSP0 => (n * 2)%N
  | COC0 r | COC1 r => (1 + n * 2 ^ N.of_nat (1 + r))%N
  | CEC r => (1 + (1 + n * 2) * 2 ^ N.of_nat (1 + r))%N
  | CSC0 r | CSC1 r => (1 + n * 2 ^ N.of_nat (2 + r))%N
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

Fixpoint z20 (cs : list Choice) (s : bool) (k : N) (u : zW) : option zW :=
  match cs with
  | [] =>
    let n := N.div2 k in
    if negb s then
      if N.eqb k (n * 2)%N then
        if forallb z1U u then Some (zPf_pos (N.succ_pos n)) else None
      else None
    else None
  | ch0 :: cs' =>
    let n := zGetN ch0 k in
    if Bool.eqb s (zInS ch0) then
      if N.eqb k (z1W ch0 n) then
        match zSw (z1Y ch0) u with
        | None => None
        | Some w =>
          match z20 cs' (zOutS ch0) (z1X ch0 n) w with
          | None => None
          | Some x => Some (z1Z ch0 ++ x)
          end
        end
      else None
    else None
  end.

Lemma N_to_nat_pow2 (m : nat) : N.to_nat (2 ^ N.of_nat m)%N = (2 ^ m)%nat.
Proof.
  induction m as [| m IH]; [reflexivity |].
  rewrite Nat2N.inj_succ, N.pow_succ_r', N2Nat.inj_mul, IH; cbn [Nat.pow]; lia.
Qed.

Lemma z21 (cs : list Choice) :
    forall (s : bool) (k : N) (u v : zW), z20 cs s k u = Some v ->
      BRIncs s (N.to_nat k) (zTs u 0inf) (zTs v 0inf).
Proof.
  induction cs as [| ch0 cs IH]; intros s k u v hE.
  - cbn [z20] in hE.
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
  - cbn [z20] in hE.
    destruct (Bool.eqb s (zInS ch0)) eqn:hs; [| discriminate].
    apply Bool.eqb_prop in hs; subst s.
    set (n := zGetN ch0 k) in *.
    destruct (N.eqb k (z1W ch0 n)) eqn:hk; [| discriminate].
    apply N.eqb_eq in hk.
    destruct (zSw (z1Y ch0) u) as [w |] eqn:hU; [| discriminate].
    destruct (z20 cs (zOutS ch0) (z1X ch0 n) w) as [x |] eqn:hC; [| discriminate].
    inversion hE as [[hv]]; subst v.
    pose proof (z1T (z1Y ch0) u w hU) as rfl_u; subst u.
    pose proof (IH (zOutS ch0) (z1X ch0 n) w x hC) as hIH.
    rewrite hk.
    destruct ch0 as [| | | | | | | r | r | r | | | r | r];
      cbn [z1Y z1Z zInS zOutS z1W z1X] in hIH |- *;
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

Definition z22 (cs : list Choice) (u : zW) : option zW :=
  match z20 cs false 128%N (u ++ [WK]) with
  | Some v => Some ([WV; WV; WQ; WV] ++ v)
  | None => None
  end.

Lemma z23 (cs : list Choice) (u v : zW) (h : z22 cs u = Some v) :
    exists r, BRIncs false 128 (zTs u 0inf) r /\ zTs v 0inf = zTs [WV; WV; WQ; WV] r.
Proof.
  unfold z22 in h.
  destruct (z20 cs false 128%N (u ++ [WK])) as [w |] eqn:hE; [| discriminate].
  inversion h as [[hv]]; subst v.
  exists (zTs w 0inf); split.
  - pose proof (z21 cs false 128%N (u ++ [WK]) w hE) as hR.
    change (N.to_nat 128%N) with 128%nat in hR.
    rewrite z0S in hR; cbn [zTs] in hR; rewrite zDd in hR.
    exact hR.
  - reflexivity.
Qed.

Inductive Rounds : side -> side -> Prop :=
  | Rounds_refl (r : side) : Rounds r r
  | Rounds_next {r s t0 : side} :
      BRIncs false 128 r s -> Rounds (zTs [WV; WV; WQ; WV] s) t0 -> Rounds r t0.

Fixpoint z24 (cs : list (list Choice)) (u : zW) : option zW :=
  match cs with
  | [] => Some u
  | c :: cs' =>
    match z22 c u with
    | None => None
    | Some v => z24 cs' v
    end
  end.

Lemma z25 (cs : list (list Choice)) :
    forall (u v : zW), z24 cs u = Some v ->
      Rounds (zTs u 0inf) (zTs v 0inf).
Proof.
  induction cs as [| c cs IH]; intros u v h.
  - cbn in h; inversion h; subst v; exact (Rounds_refl _).
  - cbn [z24] in h.
    destruct (z22 c u) as [w |] eqn:hW; [| discriminate].
    destruct (z23 c u w hW) as [r [hR hEq]].
    refine (Rounds_next hR _).
    rewrite <- hEq.
    exact (IH w v h).
Qed.

Definition z26 (w : Word) : bool :=
  match w with
  | WV => false
  | _ => true
  end.

Lemma z27 (ds : zW) (h : forallb z26 ds = true) :
    exists A, zDg A (List.length ds) ds.
Proof.
  induction ds as [| w ds IH].
  - exists 0%nat; exact zDg_nil.
  - destruct w; [discriminate | |]; cbn [forallb z26] in h;
      destruct (IH h) as [A hI]; cbn [List.length].
    + exists (A * 2)%nat; exact (zDg_zero hI).
    + exists (1 + A * 2)%nat; exact (zDg_one hI).
Qed.

Fixpoint zN11 (u : zW) : nat :=
  match u with
  | [] => 0%nat
  | WV :: u' => (1 + zN11 u')%nat
  | WK :: u' => zN11 u'
  | WQ :: u' => zN11 u'
  end.

Fixpoint zP11 (u : zW) : nat :=
  match u with
  | [] => 0%nat
  | WV :: u' => zP11 u'
  | WK :: u' => (1 + zP11 u')%nat
  | WQ :: u' => (1 + zP11 u')%nat
  end.

Lemma z11_pow (u : zW) :
    z11 u * Qnat (2 ^ zN11 u) == Qnat (2 ^ zP11 u).
Proof.
  induction u as [| w u IH]; [cbn [z11 zN11 zP11 Nat.pow]; reflexivity |].
  destruct w; cbn [z11 zN11 zP11].
  - rewrite Qnat_pow2_1_add; lra.
  - rewrite Qnat_pow2_1_add; lra.
  - rewrite Qnat_pow2_1_add; lra.
Qed.

Definition QN (n : N) : Rat := inject_Z (Z.of_N n).

Lemma QN_add (a b : N) : QN (a + b) == QN a + QN b.
Proof. unfold QN; rewrite N2Z.inj_add, inject_Z_plus; reflexivity. Qed.

Lemma QN_mul (a b : N) : QN (a * b) == QN a * QN b.
Proof. unfold QN; rewrite N2Z.inj_mul, inject_Z_mult; reflexivity. Qed.

Lemma QN_leb (a b : N) : (a <=? b)%N = true -> QN a <= QN b.
Proof.
  intros H; apply N.leb_le in H.
  unfold QN, Qle; cbn; lia.
Qed.

Fixpoint zWU (u : zW) : N :=
  match u with
  | [] => 0%N
  | WV :: u' => N.div2 (zWU u' + 1)%N
  | WK :: u' => (90112 + 2 * zWU u')%N
  | WQ :: u' => (65536 + 2 * zWU u')%N
  end.

Lemma zWU_ge (u : zW) :
    65536 * z0W u <= QN (zWU u).
Proof.
  induction u as [| w u IH]; [cbn [z0W zWU]; change (QN 0) with 0; lra |].
  destruct w; cbn [z0W zWU].
  - assert (hdiv : (zWU u <= 2 * N.div2 (zWU u + 1))%N).
    { rewrite N.div2_div.
      pose proof (N.div_mod (zWU u + 1) 2 ltac:(lia)) as hdm.
      pose proof (N.mod_lt (zWU u + 1) 2 ltac:(lia)) as hlt.
      lia. }
    assert (hdiv_q : QN (zWU u) <= 2 * QN (N.div2 (zWU u + 1))).
    { rewrite <- (QN_mul 2).
      apply QN_leb, N.leb_le, hdiv. }
    lra.
  - rewrite QN_add, QN_mul; change (QN 90112) with 90112; change (QN 2) with 2; lra.
  - rewrite QN_add, QN_mul; change (QN 65536) with 65536; change (QN 2) with 2; lra.
Qed.

Fixpoint zZNat (u : zW) : N :=
  match u with
  | [] => 0%N
  | WV :: u' => zZNat u'
  | WK :: u' => (1 + 2 * zZNat u')%N
  | WQ :: u' => (2 * zZNat u')%N
  end.

Lemma zZNat_eq (u : zW) (h : forallb z26 u = true) :
    z0Z u == QN (zZNat u).
Proof.
  induction u as [| w u IH]; [cbn [z0Z zZNat]; reflexivity |].
  destruct w; [discriminate | |]; cbn [forallb z26] in h;
    cbn [z0Z zZNat]; rewrite (IH h).
  - rewrite QN_add, QN_mul; change (QN 1) with 1; change (QN 2) with 2; ring.
  - rewrite QN_mul; change (QN 2) with 2; ring.
Qed.

Fixpoint zLastV (u : zW) : bool :=
  match u with
  | [] => false
  | [x] => word_eqb x WV
  | _ :: ((y :: ys) as u') => zLastV u'
  end.

Lemma zLastV_eq (u : zW) : zLastV u = true -> exists w, u = w ++ [WV].
Proof.
  induction u as [| x u' IH]; intros h.
  - discriminate.
  - destruct u' as [| y ys].
    + destruct x; try discriminate; exists ([] : zW); reflexivity.
    + change (zLastV (y :: ys) = true) in h.
      destruct (IH h) as [w ->].
      exists (x :: w); reflexivity.
Qed.

Definition zInitVV (u : zW) : bool :=
  match u with
  | WV :: WV :: u' => zLastV u'
  | _ => false
  end.

Lemma zInitVV_eq (u : zW) (h : zInitVV u = true) : exists w, u = WV :: WV :: (w ++ [WV]).
Proof.
  destruct u as [| [| |] [| [| |] u']]; try discriminate.
  change (zLastV u' = true) in h.
  destruct (zLastV_eq u' h) as [w ->].
  exists w; reflexivity.
Qed.

Definition zInitQK (u : zW) : bool :=
  match u with
  | WQ :: WK :: _ => true
  | _ => false
  end.

Lemma zInitQK_eq (u v : zW) (h : zInitQK u = true) : exists w, u ++ v = WQ :: WK :: w.
Proof.
  destruct u as [| [| |] [| [| |] u']]; try discriminate.
  exists (u' ++ v); reflexivity.
Qed.

Lemma z28 (u hi_low hi_top : zW)
    (hD_low : forallb z26 hi_low = true)
    (hD_top : forallb z26 hi_top = true)
    (hTopLen : List.length hi_top = 16%nat)
    (hPow : (zP11 u + (List.length hi_low + 16) =? 7 + zN11 u)%nat = true)
    (hU11_nat : (4 + zP11 u <=? zN11 u)%nat = true)
    (hEnd : zInitVV u = true)
    (hLu : z0L u = true)
    (hLo : zInitQK hi_low = true)
    (hW_nat : (zWU u <=? 969932)%N = true)
    (hZ_nat : (10 * (1 + zZNat hi_top) <=? 651776)%N = true) :
    BGood (u ++ ((hi_low ++ hi_top) ++ zTail8)).
Proof.
  apply Nat.eqb_eq in hPow.
  apply Nat.leb_le in hU11_nat.
  set (hi8 := hi_low ++ hi_top).
  assert (hD : forallb z26 hi8 = true)
    by (unfold hi8; rewrite forallb_app, hD_low, hD_top; reflexivity).
  destruct (z27 hi8 hD) as [A hI].
  assert (hLen : List.length hi8 = (List.length hi_low + 16)%nat)
    by (unfold hi8; rewrite List.length_app, hTopLen; reflexivity).
  pose proof (z11_pow u) as h11_u.
  assert (hPow2 : (2 ^ zP11 u * 2 ^ List.length hi8 = 128 * 2 ^ zN11 u)%nat).
  { rewrite <- Nat.pow_add_r, hLen, hPow, Nat.pow_add_r; change (2 ^ 7)%nat with 128%nat; lia. }
  apply Qnat_eq_iff in hPow2.
  rewrite Qnat_mul, Qnat_mul in hPow2; change (Qnat 128) with 128 in hPow2.
  assert (hPos : 0 < Qnat (2 ^ zN11 u))
    by (change 0 with (Qnat 0); apply Qnat_lt_iff; exact (zPp (zN11 u))).
  assert (hHeight : z11 u * Qnat (2 ^ List.length hi8) == 128) by (clear - h11_u hPow2 hPos; nra).
  assert (hLe2 : (16 * 2 ^ zP11 u <= 2 ^ zN11 u)%nat).
  { pose proof (Nat.pow_le_mono_r 2 (4 + zP11 u) (zN11 u) ltac:(lia) hU11_nat) as hmono.
    rewrite Nat.pow_add_r in hmono; change (2 ^ 4)%nat with 16%nat in hmono; lia. }
  apply Qnat_le in hLe2.
  rewrite Qnat_mul in hLe2; change (Qnat 16) with 16 in hLe2.
  assert (hU11 : z11 u <= (1#16)) by (clear - h11_u hLe2 hPos; nra).
  pose proof (QN_leb _ _ hW_nat) as hW_q; change (QN 969932) with 969932 in hW_q.
  pose proof (zWU_ge u) as hW_ge.
  assert (hW : z0W u <= (74#5)) by lra.
  destruct (z27 hi_low hD_low) as [A_low hI_low].
  destruct (z27 hi_top hD_top) as [A_top hI_top].
  destruct (zDw hI_low) as [hDw_low1 [hDw_low2 _]].
  destruct (zDw hI_top) as [hDw_top1 _].
  assert (hZ_low_le : z0Z hi_low <= z11 hi_low).
  { pose proof (z12 hi_low); pose proof (proj1 (proj2 (proj2 (zWn hi_low)))); lra. }
  assert (h11_top : z11 hi_top == 65536).
  { rewrite hTopLen, Qnat_pow2_16 in hDw_top1; exact hDw_top1. }
  pose proof (proj1 (zDw hI)) as h11_hi8.
  assert (h11_split : z11 hi8 == z11 hi_low * z11 hi_top) by (unfold hi8; exact (z16 hi_low hi_top)).
  assert (h_u_low : z11 u * z11 hi_low == (1#512)).
  { assert (h_eq : z11 u * Qnat (2 ^ List.length hi8) == 65536 * (z11 u * z11 hi_low))
      by (rewrite <- h11_hi8, h11_split, h11_top; ring).
    lra. }
  assert (hZ_split : z0Z hi8 == z0Z hi_low + z11 hi_low * z0Z hi_top)
    by (unfold hi8; exact (z14 hi_low hi_top)).
  pose proof (zZNat_eq hi_top hD_top) as hZ_top_eq.
  pose proof (QN_leb _ _ hZ_nat) as hZ_top_q.
  rewrite QN_mul, QN_add in hZ_top_q;
    change (QN 10) with 10 in hZ_top_q;
    change (QN 1) with 1 in hZ_top_q;
    change (QN 651776) with 651776 in hZ_top_q.
  pose proof (zSp u) as hSu.
  assert (hZ : z11 u * z0Z hi8 <= (1273#10)).
  { assert (h_uz_split : z11 u * z0Z hi8 == z11 u * z0Z hi_low + (z11 u * z11 hi_low) * z0Z hi_top)
      by (rewrite hZ_split; ring).
    assert (h_uz_low : z11 u * z0Z hi_low <= z11 u * z11 hi_low) by (clear - hSu hZ_low_le; nra).
    assert (h_uz_top : (z11 u * z11 hi_low) * z0Z hi_top == (1#512) * QN (zZNat hi_top))
      by (rewrite h_u_low, hZ_top_eq; ring).
    lra. }
  exact (BGood_intro (List.length hi8) u A hi8 hI hHeight hU11
    (zInitVV_eq u hEnd) hLu (zInitQK_eq hi_low hi_top hLo) hW hZ).
Qed.

(* Stage 4 Part B: Certificate, Initial Execution, Non-halting Theorem *)

Local Close Scope Q_scope.
Local Open Scope nat_scope.

Definition z29 : zW := [WV; WV; WV; WK; WK; WV; WV; WQ; WV; WQ; WQ; WV; WV; WV; WV; WV; WQ; WK; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ].
Definition z2a : list (list Choice) := [
  [CT; CT; (COC0 0); CSP0; CS10; CT; (COC1 0); CSP1; CT; CP1; CT; CT; CT; CT; CT; CP0; CS11; CP1; CP0; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CP1; CP1; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CP0; CT; CP1; CT; CT; CP0; CS10; CP0; CS00; CS00; CS00; CS11; CP1; CP1; CP1; CP0; CS10; CP0; CS00; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); (CSC0 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CS10; CS10; CS11; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CS11; CT; CT; CP0; CS10; CS11; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CP1; CP0; CS10; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CT; (COC0 0); CSP0; CS10; CT; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; CP1; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CP1; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CP1; CT; CT; CP0; CS10; CS11; CP0; CS10; CS11; CP1; CP0; CS10; CS00; CS10; CS10; CS11; CP1; CP1; CP1; CP1; CP0; CS10; CS01; CP1; CP1; CP0; CS10; CS00; CP1; CP0; CS10; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CP1; CT; CP1; CT; CT; CP0; CS11; CP1; CT; CT; CT; CT; CT; CP0; CT; CT; CT; CP0; CT; CT; CP1; CT; CT; CP0; CS11; CP0; CS11; CP0; CS11; CP0; CS11; CP1; CP0; CS10; CS00; CS10; CP0; CP0; CS00; CS10; CS01; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CP0; CS00; CS01; CP0; CS10; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; (COC1 0); CSP1; (COC1 0); CSP1; CT; CT; CP0; CS11; CT; (COC0 0); CSP0; CP0; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CS10; CT; CP1; CT; CT; CP0; CS10; CS10; CS00; CP1; CP1; CP0; CS10; CS00; CS10; CS10; CP0; CS00; CS10; CS00; CS00; CS10; CP1; CP0; CS10; CP0; CS00; CS00; CS00; CS00; CS10; CS10; CS00; CS10; CS00; CP0; CS01; CP1; CP1; CP1; CP0; CP0; CS00; CP0; CS01; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CS10; CP0; CS00; CS11; CP0; CS10; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); (CSC0 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP1; CP0; CT; CT; CT; CP0; CP1; (COC0 0); CSP0; CP0; CS00; CS01; CT; (COC0 0); CSP1; (COC1 0); CSP0; CS10; CS00; CS10; CS11; (COC0 2); CSP0; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CS11; CT; CP0; CT; CT; CP0; CS11; CP0; CS11; CP1; CP0; CP1; CP1; CP1; CP0; CS11; CP1; CP1; CP1; CP1; CP1; CP0; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CS10; CS00; CS01; CP1; CP0; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CP1; CP0; CS10; CS11; CP0; CS10; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CT; (COC0 0); CSP0; CS10; CT; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; (CEC 0); (CSC0 0); CSP1; CT; CP0; CS11; CP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CP0; CS10; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CP1; CT; CP0; CT; CT; CP0; CS10; CP0; CS00; CP1; CP0; CS11; CP1; CP0; CS11; CP1; CP0; CS11; CP1; CP1; CP0; CP0; CS01; CP0; CS10; CS10; CS10; CP0; CS00; CP1; CP0; CS10; CP0; CS00; CS00; CS01; CP0; CS10; CP1; CP0; CP0; CS00; CS00; CS11; CP1; CP0; CS10; CS00; CP0; CS01; CP0; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CS01; CP1; CP1; CP1; CP0; CP0; CS00; CP0; CS01; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CS01; CP1; CP1; CP0; CS10; CS00; CP1; CP0; CS10; CS11; CP0; CS10; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); (CSC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CP1; (COC1 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP0; CS10; (CEC 0); CSP1; CT; CT; (COC0 0); CSP0; CS10; CS01; CT; CT; (COC0 1); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CP0; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP0; CT; CT; CT; CT; CT; CT; CP0; CT; CT; CT; CP0; CT; CT; CP1; CT; CP1; CT; CT; CP0; CS10; CS10; CP1; CP0; CS11; CP0; CS11; CP1; CP0; CS10; CP1; CP0; CP0; CS00; CP0; CP1; CP0; CS10; CS10; CS00; CS00; CS00; CS00; CS01; CP1; CP1; CP0; CS10; CP1; CP0; CS11; CP1; CP1; CP1; CP1; CP1; CP0; CS11; CP1; CP0; CS10; CS01; CP0; CS10; CS01; CP0; CP1; CP1; CP0; CS11; CP0; CS10; CP0; CP0; CS00; CS10; CP1; CP0; CS10; CP1; CP1; CP0; CS10; CS00; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CS11; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CS10; CS00; CS01; CP1; CP0; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CP0; CS00; CS01; CP0; CS10; CS11; CP0; CS10; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CP0; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP1; CT; (COC0 0); CSP1; (COC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CP0; CT; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CP1; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP1; CP0; CS10; CS00; CS10; CS00; CT; CT; (COC0 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CP0; CT; CP0; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; CP0; CT; CT; CT; (COC0 0); CSP0; CS10; CS00; CS11; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; CP0; CS10; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CS10; CT; CP1; CT; CP0; CT; CT; CP0; CS11; CP0; CS11; CP0; CS11; CP1; CP0; CS11; CP1; CP0; CS10; CP1; CP1; CP1; CP1; CP0; CS10; CS01; CP1; CP0; CP0; CP0; CS00; CP0; CS00; CS00; CP0; CS00; CS00; CS10; CS00; CS10; CP0; CP0; CS00; CS10; CS00; CS10; CS10; CS00; CS10; CS10; CS10; CS00; CP1; CP1; CP0; CS10; CS01; CP0; CP0; CS01; CP1; CP1; CP0; CP0; CS01; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP0; CP1; CP0; CS10; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CS01; CP1; CP0; CP0; CP0; CP1; CP0; CP1; CP0; CP0; CP1; CP0; CP0; CS00; CS00; CP0; CP1; CP0; CS10; CP1; CP0; CP0; CS00; CS00; CP1; CP1; CP1; CP0; CS10; CS01; CP0; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CS01; CP1; CP1; CP1; CP0; CP0; CS00; CP0; CS01; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP1; CP0; CS10; CP0; CS00; CS11; CP0; CS10; CS01; CP0; CS10; CS11; CP1; CP0]
].
Definition z2b : zW := [WV; WV; WV; WK; WV; WQ; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WQ; WV; WV; WV; WV; WK; WQ; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WK; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WK; WQ; WV; WV; WQ; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WV; WK; WV; WQ; WV; WQ; WV; WV; WV; WV; WK; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WQ; WK; WQ; WK; WV; WV; WK; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WQ; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WK; WQ; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WQ; WV; WQ; WV; WQ; WV; WV; WQ; WV; WV; WQ; WV; WV; WV; WV; WV; WQ; WK; WV; WV; WV; WV; WK; WV; WK; WK; WV; WK; WK; WQ; WK; WQ; WV; WV; WK; WQ; WK; WQ; WQ; WK; WQ; WQ; WQ; WK; WV; WV; WV; WQ; WK; WV; WV; WK; WV; WV; WV; WV; WK; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WQ; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WK; WV; WV; WV; WQ; WV; WV; WV; WK; WK; WV; WV; WV; WV; WQ; WK; WV; WV; WV; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WQ; WK; WV; WV; WV; WV; WV; WK; WV; WK; WV; WV; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WQ; WV; WK; WQ; WV; WQ; WK; WV; WQ; WQ; WV; WV].
Definition z2c_low : zW := [WQ; WK; WK; WK; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WQ; WK; WK; WQ; WK; WQ; WK; WQ; WK; WK; WQ; WK; WK; WK; WQ; WQ; WK; WQ; WQ; WK; WQ; WK; WQ; WK; WK; WQ; WQ; WK; WQ; WQ; WK; WQ; WK; WK; WK; WQ; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WK; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WK; WQ; WQ; WK; WK; WK; WQ; WQ; WQ; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WK; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WK; WQ; WK; WK; WK; WQ; WK; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WQ; WK; WK; WK; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ].
Definition z2c_top : zW := [WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ; WK; WK; WQ; WQ; WK; WK].
Definition z2c : zW := z2c_low ++ z2c_top.
Local Close Scope nat_scope.

Lemma z2d :
    Rounds (zTs z29 0inf) (zTs (zP33 ++ (z2b ++ (z2c ++ zTail8))) 0inf).
Proof.
  apply (z25 z2a z29 (zP33 ++ (z2b ++ (z2c ++ zTail8)))).
  vm_compute; reflexivity.
Qed.

Lemma z2e :
    BGood (z2b ++ (z2c ++ zTail8)).
Proof.
  unfold z2c.
  apply (z28 z2b z2c_low z2c_top); vm_compute; reflexivity.
Qed.

Fixpoint zTs_list (u : zW) : list sym :=
  match u with
  | [] => []
  | WV :: u' => t ++ zTs_list u'
  | WK :: u' => d0 ++ zTs_list u'
  | WQ :: u' => d1 ++ zTs_list u'
  end.

Lemma zTs_list_spec (u : zW) (r : side) :
    zTs_list u *> r = zTs u r.
Proof.
  induction u as [| w u IH]; [reflexivity |].
  destruct w; cbn [zTs_list zTs]; rewrite Str_app_assoc, IH; reflexivity.
Qed.

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
  cconfig_to_config x -[ m ]->+ cconfig_to_config y.
Proof.
  induction p as [p IH | p IH |]; intros x y H; cbn [cconfig_steps_pos] in H.
  - pose proof (cconfig_step_spec m x) as H0.
    destruct (cconfig_step m x) as [x0 |] eqn:E0; [| discriminate].
    destruct (cconfig_steps_pos m p x0) as [x1 |] eqn:E1; [| discriminate].
    eapply progress_step; [exact H0 |].
    eapply progress_trans; [exact (IH x0 x1 E1) | exact (IH x1 y H)].
  - destruct (cconfig_steps_pos m p x) as [x1 |] eqn:E1; [| discriminate].
    eapply progress_trans; [exact (IH x x1 E1) | exact (IH x1 y H)].
  - pose proof (cconfig_step_spec m x) as H0.
    destruct (cconfig_step m x) as [x0 |] eqn:E0; [| discriminate].
    inversion H; subst; exact (progress_base H0).
Qed.

Definition cconfig_steps_pos_eqb (m : TM) (p : positive) (x y : cconfig) : bool :=
  match cconfig_steps_pos m p x with
  | None => false
  | Some z => cconfig_eqb z y
  end.

Lemma cconfig_steps_pos_eqb_spec (m : TM) (p : positive) (x y : cconfig) :
  cconfig_steps_pos_eqb m p x y = true ->
  cconfig_to_config x -[ m ]->+ cconfig_to_config y.
Proof.
  unfold cconfig_steps_pos_eqb.
  destruct (cconfig_steps_pos m p x) as [z |] eqn:E; [| discriminate].
  intros Heq.
  rewrite <- (cconfig_eqb_spec z y Heq).
  exact (cconfig_steps_pos_spec m p x z E).
Qed.

Lemma z0E : (E;; 0inf {{0}} 0inf) -[ canon_tm ]->+ zCf (zTs z29 0inf).
Proof.
  assert (Hstep : cconfig_to_config ([], [], 0, E) -[ canon_tm ]->+
      cconfig_to_config ([0; 1], [0] ++ w_base ++ zTs_list z29, 1, C)).
  { apply (cconfig_steps_pos_eqb_spec canon_tm 38584%positive).
    vm_compute; reflexivity. }
  assert (Hrhs : cconfig_to_config ([0; 1], [0] ++ w_base ++ zTs_list z29, 1, C) = zCf (zTs z29 0inf)).
  { unfold cconfig_to_config, zCf, zCL, lh.
    cbn [hd tl List.app Str_app].
    rewrite !Str_app_assoc, zTs_list_spec.
    reflexivity. }
  rewrite Hrhs in Hstep.
  exact Hstep.
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
  - exact (evstep_refl _ _).
  - eapply evstep_trans; [apply progress_evstep; exact (z2p hR) | exact IH].
Qed.

Lemma canon_nonhalt : ~ halts canon_tm (E;; 0inf {{0}} 0inf).
Proof.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [apply progress_evstep; exact z0E | exact (z2r z2d)].
  - apply (progress_nonhalt_cond canon_tm zW (z2b ++ (z2c ++ zTail8))
      (fun w => zCf (zTs (zP33 ++ w) 0inf)) BGood).
    + intros w hG.
      destruct (z1N hG) as [w' [hStep hG']].
      exists w'; split; [exact (z2q hStep) | exact hG'].
    + exact z2e.
Qed.

Definition zStMap (q : Q) : Q :=
  match q with
  | A => B
  | B => C
  | C => D
  | D => E
  | E => A
  | F => F
  end.

Lemma perm_canon_tm : Perm canon_tm tm zStMap.
Proof.
  split.
  - intros q s; destruct q, s; cbn; intro H; try discriminate; reflexivity.
  - intros q s s' d q'; destruct q, s; cbn; intro H; inversion H; subst; reflexivity.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  change c0 with (zStMap E;; 0inf {{0}} 0inf).
  exact (perm_nonhalt' canon_tm tm zStMap E (0inf {{0}} 0inf) perm_canon_tm canon_nonhalt).
Qed.

Print Assumptions nonhalt.
