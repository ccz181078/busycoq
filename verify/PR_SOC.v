(* Classification: SOC.
   Consolidated from busycoq PR #20, #23, pinned in PR19_28_INVENTORY.json.
   Original proofs: Dahoas.
   Common declarations are reused; each blank-state initialization is checked separately. *)

From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import micromega.Lia.
From Coq Require Import QArith.QArith.
From Coq Require Import micromega.Lqa.
From Coq Require Import BinNat Pnat Nnat PArith.
From BusyCoq Require Import Individual62.
From Coq Require Import BinNat Pnat Nnat.

Module TM1.
Import List.

Import Bool.

Import String.

Import PeanoNat.

Import Lia.

Import QArith.

Import Lqa.

Notation Rat := QArith_base.Q.

Import BinNat Pnat Nnat PArith.

Import BusyCoq.Individual62.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LF---_1RA1RB").

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
    destruct (cconfig_step m x) as [x0 |] eqn:F; [| discriminate].
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
  forall l, zCR l c r1 -[ tm ]->+ zCL l r2.

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
    (h1 : forall l r, zCR l c (w1 *> r) -[ tm ]->+ zCL l (w2 *> r)) :
    Seg [c] [] w1 w2.
Proof.
  intros r1 r2 h; inversion h; subst.
  exact (Side_cons (fun l => h1 l r2) (Side_nil _)).
Qed.

Lemma zS2 (mid : list sym) {c_in c_out : Call} {w1 w2 : list sym}
    (h1 : forall l r, zCR l c_in (w1 *> r) -[ tm ]->+ zCR (mid *> l) c_out r)
    (h2 : forall l r, zCL (mid *> l) r -[ tm ]->+ zCL l (w2 *> r)) :
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
    (h1 : forall l r, zCR l c_in (w1 *> r) -[ tm ]->+ zCR (mid1 *> l) c1 r)
    (h2 : forall l r, zCL (mid1 *> l) r -[ tm ]->+ zCR (mid2 *> l) c2 r)
    (h3 : forall l r, zCL (mid2 *> l) r -[ tm ]->+ zCL l (w2 *> r)) :
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
    (h1 : forall l r, zCR l c_in (w1 *> r) -[ tm ]->+ zCR (mid1 *> l) c1 r)
    (h2 : forall l r, zCL (mid1 *> l) r -[ tm ]->+ zCR (mid2 *> l) c2 r)
    (h3 : forall l r, zCL (mid2 *> l) r -[ tm ]->+ zCR (mid3 *> l) c3 r)
    (h4 : forall l r, zCL (mid3 *> l) r -[ tm ]->+ zCL l (w2 *> r)) :
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
  assert (h1 : zCR l cp ([0; 1; 1; 0; 0; 0] *> r) -[ tm ]->+ zCR ([1; 0; 1; 0] *> l) cp ([0; 1] *> r)) by exec_canon.
  assert (h2 : zCL ([1; 0; 1; 0] *> l) r_out -[ tm ]->+ zCL l (t *> r_out)) by exec_canon.
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
  assert (hs1 : zCR l ch ([1; 0; 1; 1; 0; 0; 0] *> r) -[ tm ]->+ zCR ([1; 0; 1; 1] *> l) cp ([0; 1] *> r)) by exec_canon.
  assert (hs2 : zCL ([1; 0; 1; 1] *> l) r_mid -[ tm ]->+ zCR ([1; 0; 1; 0] *> l) ch r_mid) by exec_canon.
  assert (hs3 : zCL ([1; 0; 1; 0] *> l) r_out -[ tm ]->+ zCL l (t *> r_out)) by exec_canon.
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
    zCL lh (w_word *> r) -[ tm ]->+ zCL lh ((w_word ++ t ++ t ++ (t ++ d1)) *> r').
Proof.
  inversion h as [| ? ? ? r_mid1 ? hc1 hrest1]; subst.
  inversion hrest1 as [| ? ? ? r_mid2 ? hc2 hrest2]; subst.
  inversion hrest2 as [| ? ? ? ? ? hc3 hnil]; subst.
  inversion hnil; subst.
  assert (h1a : zCL lh (w_word *> r) -[ tm ]->+
      ([1; 1; 0; 1; 1; 1; 1; 0; 1] *> 0inf) <{{C}} ([1; 1; 1; 0; 0; 0; 0; 1; 1; 1; 0; 1; 0] *> r)) by exec_canon.
  assert (h1b : ([1; 1; 0; 1; 1; 1; 1; 0; 1] *> 0inf) <{{C}} ([1; 1; 1; 0; 0; 0; 0; 1; 1; 1; 0; 1; 0] *> r) -[ tm ]->+
      zCR ([1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) ch r) by exec_canon.
  assert (h2a : forall s1, zCL ([1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) s1 -[ tm ]->+
      ([1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) {{A}}> ([1; 0; 1; 0; 0; 0; 0; 1] *> s1)) by exec_canon.
  assert (h2b : forall s1, ([1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1] *> 0inf) {{A}}> ([1; 0; 1; 0; 0; 0; 0; 1] *> s1) -[ tm ]->+
      zCR ([1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) cj s1) by exec_canon.
  assert (h3 : forall s2, zCL ([1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) s2 -[ tm ]->+
      zCR ([1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) ch s2) by exec_canon.
  assert (h4a : zCL ([1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1] *> 0inf) r' -[ tm ]->+
      ([1; 0; 0; 1] *> 0inf) <{{D}} ([1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 0] *> r')) by exec_canon.
  assert (h4b : ([1; 0; 0; 1] *> 0inf) <{{D}} ([1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 0] *> r') -[ tm ]->+
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
    zCf r -[ tm ]->+ zCf ((t ++ t ++ d1 ++ t) *> r').
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
    zCf r -[ tm ]->+ zCf (zTs [WV; WV; WQ; WV] r').
Proof.
  pose proof (z2o hI [] ([cj] ++ [ch] ^^ 63) (Num_even 63)) as hC.
  cbn [Str_app] in hC.
  pose proof (zW_full hC) as hW.
  assert (heq : (t ++ t ++ d1 ++ t) *> r' = zTs [WV; WV; WQ; WV] r') by reflexivity.
  rewrite <- heq.
  exact hW.
Qed.

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

Import BinNat Pnat Nnat.

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

Local Close Scope Q_scope.

Local Open Scope nat_scope.

Lemma zH_d1_odd (n : nat) : Seg ([ch] ^^ (1 + n * 2)) ([ch] ^^ (1 + n)) d1 d0.
Proof.
  change ([ch] ^^ (1 + n * 2)) with ([ch] ++ [ch] ^^ (n * 2)).
  change ([ch] ^^ (1 + n)) with ([ch] ++ [ch] ^^ n).
  exact (zSg zH4 (zSa z0k n)).
Qed.

Lemma nat_div2_parity (n : nat) :
  (n = Nat.div2 n * 2 /\ Nat.div2 (S n) = Nat.div2 n) \/
  (n = 1 + Nat.div2 n * 2 /\ Nat.div2 (S n) = 1 + Nat.div2 n).
Proof.
  induction n as [| n [[h1 h2] | [h1 h2]]]; cbn [Nat.div2] in *.
  - left; lia.
  - right; rewrite h2; lia.
  - left; rewrite h2; lia.
Qed.

Fixpoint zHExec (k : nat) (u : zW) {struct u} : option zW :=
  match k, u with
  | 0, u => Some u
  | S _, [] => None
  | S k', WV :: u' =>
    match zHExec (S k' * 2) u' with
    | Some v => Some (WV :: v)
    | None => None
    end
  | S k', WK :: u' =>
    let m := Nat.div2 (S k') in
    if S k' =? m * 2 then
      match zHExec m u' with
      | Some v => Some (WK :: v)
      | None => None
      end
    else
      match zHExec m u' with
      | Some v => Some (WQ :: v)
      | None => None
      end
  | S k', WQ :: u' =>
    let m := Nat.div2 (S k') in
    if S k' =? m * 2 then
      match zHExec m u' with
      | Some v => Some (WQ :: v)
      | None => None
      end
    else
      match zHExec (1 + m) u' with
      | Some v => Some (WK :: v)
      | None => None
      end
  end.

Lemma zHExec_ok (u : zW) :
  forall (k : nat) (v : zW), zHExec k u = Some v ->
    Side ([ch] ^^ k) (zTs u 0inf) (zTs v 0inf).
Proof.
  induction u as [| w u IH]; intros [| k'] v h; cbn [zHExec] in h.
  - inversion h; subst; exact (Side_nil _).
  - discriminate.
  - inversion h; subst; exact (Side_nil _).
  - destruct w.
    + destruct (zHExec (S k' * 2) u) as [v' |] eqn:hE; [| discriminate].
      inversion h; subst; cbn [zTs].
      exact (zSc (zS3 (S k')) (IH _ _ hE)).
    + set (m := Nat.div2 (S k')) in *.
      destruct (S k' =? m * 2) eqn:hk.
      * apply Nat.eqb_eq in hk.
        destruct (zHExec m u) as [v' |] eqn:hE; [| discriminate].
        inversion h; subst; cbn [zTs]; rewrite hk.
        exact (zSc (zH_d0_even m) (IH _ _ hE)).
      * apply Nat.eqb_neq in hk.
        destruct (zHExec m u) as [v' |] eqn:hE; [| discriminate].
        inversion h; subst; cbn [zTs].
        assert (heq : S k' = 1 + m * 2)
          by (pose proof (nat_div2_parity (S k')); unfold m in *; lia).
        rewrite heq.
        exact (zSc (zH_d0_odd m) (IH _ _ hE)).
    + set (m := Nat.div2 (S k')) in *.
      destruct (S k' =? m * 2) eqn:hk.
      * apply Nat.eqb_eq in hk.
        destruct (zHExec m u) as [v' |] eqn:hE; [| discriminate].
        inversion h; subst; cbn [zTs]; rewrite hk.
        exact (zSc (zH_d1_even m) (IH _ _ hE)).
      * apply Nat.eqb_neq in hk.
        destruct (zHExec (1 + m) u) as [v' |] eqn:hE; [| discriminate].
        inversion h; subst; cbn [zTs].
        assert (heq : S k' = 1 + m * 2)
          by (pose proof (nat_div2_parity (S k')); unfold m in *; lia).
        rewrite heq.
        exact (zSc (zH_d1_odd m) (IH _ _ hE)).
Qed.

Definition w_pre3_rest : list sym := t ++ t ++ (t ++ d1).

Definition w_pre3 : list sym := w_word ++ w_pre3_rest.

Definition w_pre5_rest : list sym := w_pre3_rest ++ t ++ (t ++ d0).

Definition w_pre5 : list sym := w_word ++ w_pre5_rest.

Definition w_pre_rest : list sym := w_pre5_rest ++ t ++ (t ++ d0).

Definition w_pre : list sym := w_word ++ w_pre_rest.

Lemma zW_pre3_seg :
    Seg [ch; cj; ch] ([ch] ^^ 4 ++ [cp] ++ [ch] ^^ 2) w_pre3_rest
      (t ++ t ++ (d0 ++ t)).
Proof.
  exact (zS0 (zS0 zW_s1 zW_s2) zW_s3).
Qed.

Lemma zW_pre5_seg :
    Seg [ch; cj; ch] ([ch] ^^ 8 ++ [cj; ch]) w_pre5_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t)).
Proof.
  exact (zS0 (zS0 zW_pre3_seg zW_s4) zW_s5).
Qed.

Lemma zW_pre_seg :
    Seg [ch; cj; ch] ([ch] ^^ 16) w_pre_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))).
Proof.
  exact (zS0 (zS0 zW_pre5_seg zW_s6) zW_s7).
Qed.

Lemma zW_pre3_full {r r' : side} (h : Side ([ch] ^^ 4 ++ ([cp] ++ [ch] ^^ 2)) r r') :
    zCL lh (w_pre3 *> r) -[ tm ]->+ zCL lh (w_pre5 *> (t *> r')).
Proof.
  pose proof (zW_pre3_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  assert (h_in : w_word *> (w_pre3_rest *> r) = w_pre3 *> r) by reflexivity.
  assert (h_out : (w_word ++ t ++ t ++ (t ++ d1)) *> ((t ++ t ++ (d0 ++ t)) *> r') =
      w_pre5 *> (t *> r')) by reflexivity.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

Lemma zW_pre5_full {r r' : side} (h : Side ([ch] ^^ 8 ++ [cj; ch]) r r') :
    zCL lh (w_pre5 *> r) -[ tm ]->+ zCL lh (w_pre *> (t *> r')).
Proof.
  pose proof (zW_pre5_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  assert (h_in : w_word *> (w_pre5_rest *> r) = w_pre5 *> r) by reflexivity.
  assert (h_out : (w_word ++ t ++ t ++ (t ++ d1)) *>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t)) *> r') =
      w_pre *> (t *> r')) by reflexivity.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

Lemma zW_pre_full {r r' : side} (h : Side ([ch] ^^ 16) r r') :
    zCL lh (w_pre *> r) -[ tm ]->+ zCf r'.
Proof.
  pose proof (zW_pre_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  assert (h_in : w_word *> (w_pre_rest *> r) = w_pre *> r) by reflexivity.
  assert (h_out : (w_word ++ t ++ t ++ (t ++ d1)) *>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))) *> r') =
      w_base *> r') by reflexivity.
  unfold zCf.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

Local Close Scope nat_scope.

Record CCfg : Type := mkCCfg {
  cq : Q;
  chead : sym;
  cleft : list sym;
  cright : list sym;
}.

Definition c_to_cfg (c : CCfg) : Q * tape :=
  cq c;; (cleft c *> 0inf) {{chead c}} (cright c *> 0inf).

Definition c_push (a : sym) (l : list sym) : list sym :=
  match a, l with
  | 0, [] => []
  | _, _ => a :: l
  end.

Definition c_hd (l : list sym) : sym :=
  match l with
  | [] => 0
  | x :: _ => x
  end.

Definition c_tl (l : list sym) : list sym :=
  match l with
  | [] => []
  | _ :: xs => xs
  end.

Lemma c_push_eq (a : sym) (l : list sym) :
  c_push a l *> 0inf = a >> (l *> 0inf).
Proof.
  unfold c_push; destruct a, l; cbn; try reflexivity.
  rewrite <- const_unfold; reflexivity.
Qed.

Lemma c_hd_eq (l : list sym) :
  hd (l *> 0inf) = c_hd l.
Proof. destruct l; reflexivity. Qed.

Lemma c_tl_eq (l : list sym) :
  tl (l *> 0inf) = c_tl l *> 0inf.
Proof. destruct l; reflexivity. Qed.

Definition c_step (c : CCfg) : option CCfg :=
  match tm (cq c, chead c) with
  | None => None
  | Some (a, L, q') =>
      Some (mkCCfg q' (c_hd (cleft c)) (c_tl (cleft c)) (c_push a (cright c)))
  | Some (a, R, q') =>
      Some (mkCCfg q' (c_hd (cright c)) (c_push a (cleft c)) (c_tl (cright c)))
  end.

Lemma c_step_spec (c c' : CCfg) :
  c_step c = Some c' -> c_to_cfg c -[ tm ]-> c_to_cfg c'.
Proof.
  unfold c_step, c_to_cfg; intros H.
  destruct (tm (cq c, chead c)) as [[[a d] q'] |] eqn:F; [| discriminate].
  destruct d; inversion H; subst; clear H; cbn [cq chead cleft cright].
  - apply (step_left (l := cleft c *> 0inf) (r := cright c *> 0inf)) in F.
    unfold move_left in F.
    rewrite c_hd_eq, c_tl_eq, <- c_push_eq in F.
    exact F.
  - apply (step_right (l := cleft c *> 0inf) (r := cright c *> 0inf)) in F.
    unfold move_right in F.
    rewrite c_hd_eq, c_tl_eq, <- c_push_eq in F.
    exact F.
Qed.

Fixpoint c_steps_pos (p : positive) (c : CCfg) : option CCfg :=
  match p with
  | xH => c_step c
  | xO p' =>
      match c_steps_pos p' c with
      | None => None
      | Some cm => c_steps_pos p' cm
      end
  | xI p' =>
      match c_steps_pos p' c with
      | None => None
      | Some cm1 =>
          match c_steps_pos p' cm1 with
          | None => None
          | Some cm2 => c_step cm2
          end
      end
  end.

Lemma c_steps_pos_spec (p : positive) (c c' : CCfg) :
  c_steps_pos p c = Some c' -> c_to_cfg c -[ tm ]->+ c_to_cfg c'.
Proof.
  revert c c'; induction p as [p IHp | p IHp |]; intros c c' H; cbn [c_steps_pos] in H.
  - destruct (c_steps_pos p c) as [cm1 |] eqn:E1; [| discriminate].
    destruct (c_steps_pos p cm1) as [cm2 |] eqn:E2; [| discriminate].
    eapply progress_trans; [exact (IHp _ _ E1) |].
    eapply progress_trans; [exact (IHp _ _ E2) |].
    apply progress_base; exact (c_step_spec _ _ H).
  - destruct (c_steps_pos p c) as [cm |] eqn:E1; [| discriminate].
    eapply progress_trans; [exact (IHp _ _ E1) | exact (IHp _ _ H)].
  - apply progress_base; exact (c_step_spec _ _ H).
Qed.

Lemma z2q {orig out : zW} (hS : BStep orig out) :
  zCf (zTs (zP33 ++ orig) 0inf) -[ tm ]->+ zCf (zTs (zP33 ++ out) 0inf).
Proof.
  destruct (z1R hS) as [r [hI hEq]].
  rewrite hEq.
  exact (z2p hI).
Qed.

Lemma z2r {r r' : side} (h : Rounds r r') :
  zCf r -[ tm ]->* zCf r'.
Proof.
  induction h as [r | r s t0 hR _ IH].
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep; exact (z2p hR) | exact IH].
Qed.

Definition z29_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WQ; WV; WV; WV; WK; WV; WV; WQ; WK; WV; WV; WV; WQ; WQ; WQ; WV; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WQ; WK; WK; WK; WK; WK; WK; WQ].

Definition z2a_0539 : list (list Choice) := [
  [CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; CP0; CT; CT; (COC0 0); CSP1; CP1; (COC1 0); CSP0; CS11; CP1; CP0; CS10; CP0; CP1; CP0; CS10; CS10; CS00; CS00; CS10; CP0];
  [CT; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP1; CP0; CS10; CS01; (COC0 0); CSP0; CS10; CS01; CP0; CS10; CP0; CP0; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CP0; CS10; CT; (COC1 1); CSP1; CT; (COC0 0); (CSC0 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CT; CP0; CP1; CP1; CP0; CS10; CP0; CS00; CS10; CS00; CP0; CP0; CP0; CS01; CP1; CP0; CP0; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CS10; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CP0; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CP0; CS11; CP1; CP0; CP1; CP0; CS10; CP0; CS01; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CS01; CP0; CS10; CS01; CP1; CP0; CS10; CP0; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CS10; (CEC 0); CSP0; CT; CP0; CT; (COC1 0); CSP1; (COC1 0); CSP0; CT; CT; CP0; CS10; CP1; CP0; CP0; CS00; CS00; CS10; CS10; CP0; CS00; CS11; CP1; CP0; CS10; CS00; CS01; CP1; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CP0; CP0; CP1; CP0; CS10; CS10; CS00; CP0; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CS10; CP1; (COC0 0); CSP0; CS11; CT; CT; CP0; CS10; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS10; CS00; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 1); CSP0; CT; CT; CP0; CS10; CS11; CP0; CS11; CP0; CP1; CP1; CP1; CP0; CS10; CP0; CS00; CS10; CS10; CS01; CP0; CP0; CP1; CP0; CS10; CS10; CS01; CP0; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); (CSC0 0); CSP1; (COC1 0); (CSC0 0); CSP1; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CT; CP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; CP1; (COC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CS11; CP0; CT; CT; CT; (COC0 0); CSP1; CP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS10; (CEC 0); (CSC0 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CP1; CT; CT; CP0; CS10; CP0; CS00; CP0; CP0; CS00; CS10; CP0; CP0; CS00; CS10; CS01; CP0; CS10; CP0; CS00; CS01; CP0; CP0; CP0; CP1; CP0; CS10; CS10; CS00; CS00; CS11; CP1; CP0; CP1; CP0; CS10; CS11; CP0; CS11; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CP0; CP0; CS01; CP1; CP0; CP0; CS01; CP0; CS10; CS11; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CS10; CT; CT; CP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CT; (COC1 0); CSP0; CS11; CT; (COC0 0); (CSC1 1); CSP1; (COC1 0); CSP0; CS10; CT; CT; CT; CT; (COC0 0); CSP1; CP0; CS10; CS01; CT; CT; CT; CT; CP1; (COC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CS10; CS00; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CP1; CT; CT; CP0; CS10; CP1; CP0; CS10; CS10; CS11; CP0; CS10; CS00; CP1; CP0; CS10; CS10; CS01; CP0; CS10; CP0; CP0; CP1; CP1; CP0; CP1; CP0; CS10; CP1; CP0; CP0; CP0; CS00; CP0; CP0; CP1; CP0; CP1; CP1; CP0; CS10; CS00; CS10; CS10; CS01; CP0; CP0; CP1; CP0; CS10; CS10; CS01; CP0; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CS01; CP0; CS10; CS01; CP1; CP0; CS10; CP0; CS01; CP0; CS10; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); (CSC0 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP1; (COC1 0); CSP1; (COC1 0); CSP0; CS11; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; CP0; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CT; CP0; CT; (COC1 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; (COC0 0); CSP1; CP1; CT; CP0; CT; (COC1 0); CSP1; (COC1 1); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CP0; CS11; CP0; CT; CT; CT; (COC0 0); CSP1; CP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS10; (CEC 0); CSP0; CT; CP0; CT; (COC1 0); CSP1; (COC1 0); CSP0; CT; CP0; CT; CT; CP0; CS11; CP0; CP0; CS00; CS00; CS00; CP0; CP0; CS00; CS10; CP0; CP1; CP0; CS10; CS10; CP1; CP1; CP0; CS10; CS00; CS10; CS01; CP0; CP0; CS00; CS00; CS10; CS10; CS10; CS11; CP0; CS10; CS01; CP0; CS10; CS00; CP0; CP1; CP1; CP1; CP0; CP0; CS00; CS01; CP0; CS10; CP0; CS00; CS00; CP0; CP0; CP1; CP0; CP0; CP0; CP0; CP1; CP0; CS10; CS10; CS00; CS00; CS01; CP1; CP0; CP1; CP0; CS10; CS11; CP0; CS11; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CP0; CP0; CP1; CP0; CS10; CS10; CS00; CP0; CS01; CP0; CS10; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CS10; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); (CSC1 0); CSP1; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); (CSC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CS10; CS10; CT; (COC1 0); CSP0; CS11; CT; CT; CT; CP1; CT; CT; CT; CP0; CP0; CT; (COC1 0); CSP0; CS10; CP1; CP1; CT; CP0; CT; CP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; (CEC 0); CSP1; (COC1 0); CSP0; CS10; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; CP0; CS10; CS00; CT; CT; CT; CT; CP1; (COC1 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CS10; CS00; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 1); CSP0; CT; CP0; CT; CT; CP0; CS10; CP0; CS00; CS00; CS11; CP1; CP0; CS11; CP0; CS10; CS11; CP0; CS10; CS10; CS11; CP0; CS10; CS01; CP1; CP1; CP0; CS10; CS01; CP0; CP1; CP1; CP0; CP0; CP0; CP0; CP1; CP0; CS10; CS10; CS00; CP0; CS00; CP1; CP0; CS11; CP0; CS10; CS00; CP0; CS01; CP0; CS10; CS10; CS11; CP0; CP0; CS00; CP0; CP0; CS01; CP0; CS10; CS01; CP0; CP0; CS00; CS00; CP1; CP1; CP0; CP0; CP0; CS00; CS11; CP0; CS10; CS01; CP1; CP0; CS11; CP0; CP0; CP0; CP1; CP0; CP1; CP1; CP0; CS10; CS00; CS10; CS10; CS01; CP0; CP0; CP1; CP0; CS10; CS10; CS01; CP0; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CS11; CP0; CS10; CS01; CP1; CP0];
  [CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; (COC1 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); (CSC0 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CS11; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; (COC0 0); CSP0; CS10; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; (COC0 0); CSP0; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CP1; (COC1 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; (COC0 0); CSP1; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CT; CT; CP0; CT; CT; CT; CT; (COC0 0); CSP1; CT; CT; CT; CT; (COC0 0); CSP0; CT; CP0; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 0); CSP0; CS10; CS11; CT; (COC0 0); CSP1; CT; CP1; (COC1 0); CSP1; CP1; CT; CP0; CT; CT; CT; CP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP1; (COC1 1); CSP0; CT; (COC1 0); CSP1; CT; (COC0 1); (CSC1 0); CSP1; CP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CT; CP0; CT; (COC1 0); CSP0; CS10; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CP0; CT; (COC1 0); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CP0; CS11; CP0; CT; CT; CT; (COC0 0); CSP1; CP0; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS10; (CEC 0); (CSC0 0); CSP1; CT; (COC0 0); CSP1; CT; CT; CP1; CT; CP0; CT; CT; CP0; CS10; CS10; CS10; CS01; CP0; CS10; CS10; CS01; CP0; CP0; CP0; CS00; CS10; CP0; CS00; CP0; CS00; CP1; CP0; CP0; CS01; CP1; CP0; CP1; CP0; CP0; CS00; CP0; CS00; CP0; CP1; CP1; CP0; CS10; CS00; CS10; CS00; CP0; CP0; CS00; CS11; CP0; CP0; CS01; CP0; CS10; CS11; CP0; CS11; CP1; CP1; CP0; CS10; CP0; CS00; CS11; CP1; CP1; CP0; CS10; CP0; CS00; CP0; CS01; CP0; CS10; CP0; CP0; CS00; CS11; CP0; CS10; CP1; CP1; CP0; CS10; CS01; CP0; CP0; CS01; CP0; CP0; CS00; CS00; CS10; CS10; CS10; CS11; CP0; CS10; CP0; CS00; CS10; CS10; CS00; CS00; CP1; CP1; CP1; CP0; CP0; CS00; CS01; CP0; CS10; CS11; CP1; CP0; CS10; CP0; CP1; CP0; CP0; CP0; CP0; CP1; CP0; CS10; CS10; CS00; CS00; CS01; CP1; CP0; CP1; CP0; CS10; CS11; CP0; CS11; CP1; CP1; CP1; CP0; CP0; CS00; CS00; CS00; CP0; CP0; CP0; CS01; CP1; CP0; CP0; CS01; CP0; CS10; CS11; CP0; CS10; CS01; CP1; CP0]
].

Definition z2b_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WQ; WV; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WK; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WK; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WQ; WV; WK; WV; WQ; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WQ; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WQ; WQ; WV; WK; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WQ; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WQ; WV; WQ; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WQ; WQ; WQ; WK; WV; WQ; WQ; WK; WV; WV; WV; WK; WQ; WV; WK; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WK; WV; WV; WV; WV; WQ; WK; WQ; WK; WV; WV; WK; WQ; WV; WV; WK; WV; WQ; WQ; WV; WQ; WV; WV; WV; WQ; WV; WK; WQ; WV; WV; WV; WQ; WV; WK; WV; WK; WV; WQ; WV; WV; WK; WQ; WV; WQ; WV; WV; WV; WQ; WK; WV; WV; WK; WV; WV; WK; WK; WQ; WQ; WQ; WQ; WV; WQ; WV; WK; WQ; WQ; WK; WK; WV; WV; WV; WV; WV; WK; WK; WV; WQ; WQ; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WQ; WQ; WK; WK; WK; WV; WV; WV; WV; WQ; WQ; WV; WQ; WV; WV; WV; WV; WV; WK; WK; WK; WV; WV; WV; WK; WV; WV; WV; WK; WV; WQ; WQ; WV; WQ; WK; WV; WV].

Definition z2c_low_0539 : zW := [WQ; WK; WK; WQ; WQ; WK; WK; WK; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WQ; WK; WK; WK; WK; WK; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WQ; WK; WQ; WQ; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WK; WQ; WK; WK; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WK; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WQ; WQ; WK; WK; WK; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WQ; WK; WQ; WQ; WQ; WK; WQ; WQ; WK; WK; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WK; WQ; WK; WQ; WK; WQ; WQ; WK; WK; WK; WK; WQ; WK; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WK; WK; WK; WQ; WQ; WK; WQ; WK; WK; WQ; WK; WQ; WK; WQ; WQ; WK; WK; WQ; WQ; WK; WQ; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WQ; WK; WQ; WK; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WQ; WK; WQ; WK; WQ; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WK; WK; WQ; WQ; WK; WQ; WK; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WK; WK; WK; WK; WQ; WK].

Definition z2c_top_0539 : zW := [WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WK; WK].

Definition z2c_0539 : zW := z2c_low_0539 ++ z2c_top_0539.

Definition zRem1Pad_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WV; WK; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WK].

Definition zMid1_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WV; WK; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WQ].

Definition zCh1_0539 : list Choice := [CT; CT; CT; CT; CT; CT; CT; (COC0 0); (CSC1 0); CSP1; CT; (COC0 0); CSP0; CT; (COC1 0); CSP0; CS10; CS00; CS00; CP1; CP1; CP0; CS10; CS00; CP0].

Definition zOut1_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WQ; WV; WQ; WK; WK; WV; WV; WV; WQ; WK; WV; WK; WK; WQ; WQ; WK; WQ; WQ; WQ].

Definition zRem2Pad_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WQ; WV; WQ; WK; WK; WV; WV; WV; WQ; WK; WV; WK; WK; WQ; WQ; WK; WQ; WQ; WQ; WK; WK; WK; WK; WK].

Definition zMid2_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WQ; WV; WQ; WK; WK; WV; WV; WV; WQ; WK; WV; WK; WK; WQ; WQ; WK; WQ; WQ; WQ; WK; WK; WK; WK; WQ].

Definition zCh2_0539 : list Choice := [CT; CT; CT; CT; CT; CT; CT; (COC0 0); CSP0; CS11; CT; CT; (COC0 0); CSP0; CT; (COC1 0); CSP1; CT; CP0; CS10; CT; CT; CT; (COC0 1); CSP0; CS10; CS01; CP0; CP1; CP0; CS10; CS10; CS10; CP0].

Definition zOut2_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WQ; WV; WV; WV; WK; WV; WV; WQ; WK; WV; WV; WV; WQ; WQ; WQ; WV; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WQ].

Definition zRem3Pad_0539 : zW := [WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WQ; WV; WV; WV; WK; WV; WV; WQ; WK; WV; WV; WV; WQ; WQ; WQ; WV; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WQ; WK; WK; WK; WK; WK; WK; WK].

Definition zCk0_0539 : CCfg := mkCCfg A 0 [] [].

Definition zCk4_0539 : CCfg := mkCCfg C 1 [0; 1] [0; 0; 0; 0; 1; 1; 0; 1; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 0; 1; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1].

Lemma z2d_0539 :
  Rounds (zTs z29_0539 0inf) (zTs (zP33 ++ (z2b_0539 ++ (z2c_0539 ++ zTail8))) 0inf).
Proof.
  apply (z25 z2a_0539 z29_0539 (zP33 ++ (z2b_0539 ++ (z2c_0539 ++ zTail8)))).
  vm_compute; reflexivity.
Qed.

Lemma z2e_0539 :
  BGood (z2b_0539 ++ (z2c_0539 ++ zTail8)).
Proof.
  unfold z2c_0539.
  apply (z28 z2b_0539 z2c_low_0539 z2c_top_0539); vm_compute; reflexivity.
Qed.

Lemma z0E_0539 : c_to_cfg zCk0_0539 -[ tm ]->+ zCf (zTs z29_0539 0inf).
Proof.
  pose proof (c_steps_pos_spec 36519%positive zCk0_0539 zCk4_0539
    ltac:(vm_compute; reflexivity)) as h_all.
  assert (heq1 : c_to_cfg zCk4_0539 = zCL lh (w_pre3 *> zTs zRem1Pad_0539 0inf))
    by solve_const0_eq.
  rewrite heq1 in h_all.
  pose proof (zHExec_ok zRem1Pad_0539 4 zMid1_0539
    ltac:(vm_compute; reflexivity)) as h_h1.
  pose proof (z21 zCh1_0539 false 5%N (zMid1_0539 ++ [WK]) zOut1_0539
    ltac:(vm_compute; reflexivity)) as h_b1_0.
  change (N.to_nat 5%N) with 5%nat in h_b1_0.
  rewrite z0S in h_b1_0; cbn [zTs] in h_b1_0; rewrite zDd in h_b1_0.
  pose proof (z2o h_b1_0 [] ([cp] ++ [ch] ^^ 2) (Num_odd 2)) as h_s1.
  cbn [Str_app] in h_s1.
  pose proof (zW_pre3_full (z08 h_h1 h_s1)) as h_turn1.
  assert (heq2 : t *> zTs zOut1_0539 0inf = zTs zRem2Pad_0539 0inf)
    by solve_const0_eq.
  rewrite heq2 in h_turn1.
  pose proof (zHExec_ok zRem2Pad_0539 8 zMid2_0539
    ltac:(vm_compute; reflexivity)) as h_h2.
  pose proof (z21 zCh2_0539 false 4%N (zMid2_0539 ++ [WK]) zOut2_0539
    ltac:(vm_compute; reflexivity)) as h_b2_0.
  change (N.to_nat 4%N) with 4%nat in h_b2_0.
  rewrite z0S in h_b2_0; cbn [zTs] in h_b2_0; rewrite zDd in h_b2_0.
  pose proof (z2o h_b2_0 [] ([cj] ++ [ch] ^^ 1) (Num_even 1)) as h_s2.
  cbn [Str_app lpow app] in h_s2.
  pose proof (zW_pre5_full (z08 h_h2 h_s2)) as h_turn2.
  assert (heq3 : t *> zTs zOut2_0539 0inf = zTs zRem3Pad_0539 0inf)
    by solve_const0_eq.
  rewrite heq3 in h_turn2.
  pose proof (zHExec_ok zRem3Pad_0539 16 z29_0539
    ltac:(vm_compute; reflexivity)) as h_h3.
  pose proof (zW_pre_full h_h3) as h_turn3.
  eapply progress_trans; [exact h_all |].
  eapply progress_trans; [exact h_turn1 |].
  eapply progress_trans; [exact h_turn2 | exact h_turn3].
Qed.

Lemma nonhalt_canon : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply progress_evstep.
    eapply progress_evstep_trans.
    + exact z0E_0539.
    + exact (z2r z2d_0539).
  - apply (progress_nonhalt_cond tm zW
      (z2b_0539 ++ (z2c_0539 ++ zTail8))
      (fun w => zCf (zTs (zP33 ++ w) 0inf))
      BGood).
    + intros w hG.
      destruct (z1N hG) as [w' [hStep hG']].
      exists w'; split; [exact (z2q hStep) | exact hG'].
    + exact z2e_0539.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. exact nonhalt_canon. Qed.

End TM1.
Print Assumptions TM1.nonhalt.

From Coq Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat NArith.NArith ZArith.ZArith QArith.QArith micromega.Lqa micromega.Lia.

Module TM2.
Import String List Bool PeanoNat NArith ZArith QArith Lqa Lia.

Import BusyCoq.Individual62.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC---_1RD1RE_1RE0RC_1LF1RD_1LA0LF").

Notation cconfig_steps := TM1.cconfig_steps.

Notation cconfig_steps_spec := TM1.cconfig_steps_spec.

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
  - destruct (cconfig_steps m x chunk_size) as [x0 |] eqn:F; [| discriminate].
    eapply evstep_trans; [exact (cconfig_steps_spec m chunk_size x x0 F) | exact (IH x0 y H)].
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

Notation t := TM1.t.

Notation d0 := TM1.d0.

Notation d1 := TM1.d1.

Notation one := TM1.one.

Notation lh := TM1.lh.

Notation w_word := TM1.w_word.

Notation w_rest := TM1.w_rest.

Notation w_base := TM1.w_base.

Notation zDd := TM1.zDd.

Notation Call := TM1.Call.

Notation ch := TM1.ch.

Notation cj := TM1.cj.

Notation cp := TM1.cp.

Notation zCs := TM1.zCs.

Notation zCw := TM1.zCw.

Notation zCR := TM1.zCR.

Notation zCL := TM1.zCL.

Notation zCf := TM1.zCf.

Notation z04 := TM1.z04.

Notation Side := TM1.Side.

Notation Side_nil := TM1.Side_nil.

Notation Side_cons := TM1.Side_cons.

Notation Seg := TM1.Seg.

Notation zLp' := TM1.zLp'.

Notation z06 := TM1.z06.

Notation z07 := TM1.z07.

Notation z08 := TM1.z08.

Notation z09 := TM1.z09.

Notation z0a := TM1.z0a.

Notation z0m_id := TM1.z0m_id.

Notation zSc := TM1.zSc.

Notation zSg := TM1.zSg.

Notation zS0 := TM1.zS0.

Notation zS4 := TM1.zS4.

Notation zS2 := TM1.zS2.

Notation zS5 := TM1.zS5.

Notation zS6 := TM1.zS6.

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

Notation z0b := TM1.z0b.

Notation z0c_p := TM1.z0c_p.

Notation z0c := TM1.z0c.

Notation zH2 := TM1.zH2.

Notation z0d := TM1.z0d.

Notation z0e := TM1.z0e.

Notation z0f := TM1.z0f.

Notation z0g := TM1.z0g.

Notation z0h := TM1.z0h.

Notation z0i := TM1.z0i.

Notation zH1 := TM1.zH1.

Notation zH3 := TM1.zH3.

Notation z0j := TM1.z0j.

Notation zH0 := TM1.zH0.

Notation zH4 := TM1.zH4.

Notation zC_base := TM1.zC_base.

Notation zO_head := TM1.zO_head.

Notation zO_mid := TM1.zO_mid.

Notation zO_b0 := TM1.zO_b0.

Notation zO_b2 := TM1.zO_b2.

Notation zE_head := TM1.zE_head.

Notation zE_b0 := TM1.zE_b0.

Notation zW_td1a := TM1.zW_td1a.

Notation zW_td1b := TM1.zW_td1b.

Notation zW_td0a := TM1.zW_td0a.

Notation zW_td0b := TM1.zW_td0b.

Notation zS3 := TM1.zS3.

Notation zT_pow := TM1.zT_pow.

Notation zSa := TM1.zSa.

Notation z0k := TM1.z0k.

Notation z0l := TM1.z0l.

Notation zH_d0_even := TM1.zH_d0_even.

Notation zH_d0_odd := TM1.zH_d0_odd.

Notation zH_d1_even := TM1.zH_d1_even.

Notation z0m := TM1.z0m.

Notation z0n := TM1.z0n.

Notation z0o := TM1.z0o.

Notation z0p := TM1.z0p.

Notation z0q := TM1.z0q.

Notation z0r := TM1.z0r.

Notation z0s := TM1.z0s.

Notation z0t := TM1.z0t.

Notation z0u := TM1.z0u.

Notation z0v := TM1.z0v.

Notation z0w := TM1.z0w.

Notation zCp_step := TM1.zCp_step.

Notation zCp_chain := TM1.zCp_chain.

Notation zOdd_base := TM1.zOdd_base.

Notation zEven_ch_step := TM1.zEven_ch_step.

Notation zEven_base := TM1.zEven_base.

Notation zW_turn := TM1.zW_turn.

Notation zW_s1 := TM1.zW_s1.

Notation zW_s2 := TM1.zW_s2.

Notation zW_s3 := TM1.zW_s3.

Notation zW_s4 := TM1.zW_s4.

Notation zW_s5 := TM1.zW_s5.

Notation zW_s6 := TM1.zW_s6.

Notation zW_s7 := TM1.zW_s7.

Notation zW_s8 := TM1.zW_s8.

Notation zW_s9 := TM1.zW_s9.

Notation zW_s10 := TM1.zW_s10.

Notation zW_s11 := TM1.zW_s11.

Notation zW_rest_seg := TM1.zW_rest_seg.

Notation zW_full := TM1.zW_full.

Notation Word := TM1.Word.

Notation WV := TM1.WV.

Notation WK := TM1.WK.

Notation WQ := TM1.WQ.

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

Notation Num := TM1.Num.

Notation Num_zero := TM1.Num_zero.

Notation Num_odd := TM1.Num_odd.

Notation Num_even := TM1.Num_even.

Notation Num_shift := TM1.Num_shift.

Notation z2f := TM1.z2f.

Notation z2g := TM1.z2g.

Notation z2h := TM1.z2h.

Notation z2i_p0 := TM1.z2i_p0.

Notation z2j := TM1.z2j.

Notation z2k := TM1.z2k.

Notation z2l := TM1.z2l.

Notation z2m := TM1.z2m.

Notation z2n := TM1.z2n.

Notation zP2 := TM1.zP2.

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

Notation z2_sp0 := TM1.z2_sp0.

Notation z2_sp1 := TM1.z2_sp1.

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
  zCf r -[ TM1.tm ]->+ zCf (zTs [WV; WV; WQ; WV] r').
Proof.
  pose proof (z2o hI [] ([cj] ++ [ch] ^^ 63) (Num_even 63)) as hC.
  cbn [Str_app] in hC.
  pose proof (zW_full hC) as hW.
  assert (heq : (t ++ t ++ d1 ++ t) *> r' = zTs [WV; WV; WQ; WV] r') by reflexivity.
  rewrite <- heq; exact hW.
Qed.

Local Open Scope nat_scope.

Notation Binary := TM1.Binary.

Notation Binary_one := TM1.Binary_one.

Notation Binary_zero := TM1.Binary_zero.

Notation Binary_two := TM1.Binary_two.

Notation zPp := TM1.zPp.

Notation z0F := TM1.z0F.

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

Notation zIv := TM1.zIv.

Notation zP4 := TM1.zP4.

Notation zIv_P4 := TM1.zIv_P4.

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

Notation ModeU := TM1.ModeU.

Notation ME := TM1.ME.

Notation MO := TM1.MO.

Notation MS := TM1.MS.

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
  -  
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
  -  
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
  -  
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
  -  
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
  -  
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
  -  
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
  -  
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
  -  
    split; [intros [H | H]; discriminate H |].
    intros _ k [n ->] hk.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IHhI (or_introl eq_refl) ((n * 2) * 2)%nat
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) (fun H => ltac:(discriminate H)))
      as [m' [v [a [b [hSub hm']]]]].
    { push_Q_of_nat; lra. }
    exists m', (WV :: v), (a * (1#2)), ((1#4) + b * (1#2)); split; [exact (BScan_shift_pair0 hSub) | exact hm'].
  -  
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
  -  
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
  -  
    split; [intros [H | H]; discriminate H |].
    intros _ k [n ->] hk.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W] in hk.
    destruct (proj1 IHhI (or_intror eq_refl) (1 + (n * 2) * 2)%nat
      (fun H => ltac:(discriminate H)) (fun _ => ex_intro _ (n * 2)%nat eq_refl))
      as [m' [v [a [b [hSub hm']]]]].
    { push_Q_of_nat; lra. }
    exists m', (WV :: v), (a * (1#2)), ((1#2) + b * (1#2)); split; [exact (BScan_shift_pair1 hSub) | exact hm'].
  -  
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
  -  
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
  -  
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
  -  
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

Notation z1U := TM1.z1U.

Lemma z1V (u : zW) (h : forallb z1U u = true) :
  zTs u 0inf = 0inf.
Proof.
  induction u as [| w u IH]; [reflexivity |].
  destruct w; try discriminate h.
  cbn [forallb z1U] in h; cbn [zTs]; rewrite (IH h), zDd; reflexivity.
Qed.

Notation Choice := TM1.Choice.

Notation CT := TM1.CT.

Notation CP0 := TM1.CP0.

Notation CP1 := TM1.CP1.

Notation CS00 := TM1.CS00.

Notation CS01 := TM1.CS01.

Notation CS10 := TM1.CS10.

Notation CS11 := TM1.CS11.

Notation COC0 := TM1.COC0.

Notation COC1 := TM1.COC1.

Notation CEC := TM1.CEC.

Notation CSP0 := TM1.CSP0.

Notation CSP1 := TM1.CSP1.

Notation CSC0 := TM1.CSC0.

Notation CSC1 := TM1.CSC1.

Notation zInS := TM1.zInS.

Notation zOutS := TM1.zOutS.

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

Notation z26 := TM1.z26.

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

Local Open Scope nat_scope.

Notation w_pre3_rest := TM1.w_pre3_rest.

Notation w_pre5_rest := TM1.w_pre5_rest.

Notation w_pre_rest := TM1.w_pre_rest.

Notation w_pre := TM1.w_pre.

Notation zW_pre3_seg := TM1.zW_pre3_seg.

Notation zW_pre5_seg := TM1.zW_pre5_seg.

Notation zW_pre_seg := TM1.zW_pre_seg.

Notation zW_pre_full := TM1.zW_pre_full.

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
  zCf (zTs (zP33 ++ orig) 0inf) -[ TM1.tm ]->+ zCf (zTs (zP33 ++ out) 0inf).
Proof.
  destruct (z1R hS) as [r [hI hEq]].
  rewrite hEq.
  exact (z2p hI).
Qed.

Lemma z2r {r r' : side} (h : Rounds r r') :
  zCf r -[ TM1.tm ]->* zCf r'.
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
  destruct (cconfig_steps_pos m p x) as [z |] eqn:F; [| discriminate].
  intros Heq.
  rewrite <- (cconfig_eqb_spec z y Heq).
  exact (cconfig_steps_pos_spec m p x z F).
Qed.

Lemma z0E_0108 : cconfig_to_config zCk0_0108 -[ TM1.tm ]->+ zCf (zTs z29_0108 0inf).
Proof.
  assert (h_all : cconfig_to_config zCk0_0108 -[ TM1.tm ]->* cconfig_to_config zCk5_0108).
  { apply (cconfig_steps_pos_eqb_spec TM1.tm 40537%positive zCk0_0108 zCk5_0108).
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

Lemma nonhalt_canon : ~ halts TM1.tm (cconfig_to_config zCk0_0108).
Proof.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [apply progress_evstep; exact z0E_0108 | exact (z2r z2d_0108)].
  - apply (progress_nonhalt_cond TM1.tm zW
      (z2b_0108 ++ (z2c_0108 ++ zTail8))
      (fun w => zCf (zTs (zP33 ++ w) 0inf))
      BGood).
    + intros w hGood.
      destruct (z1N hGood) as [w' [hStep hGood']].
      exists w'; split; [exact (z2q hStep) | exact hGood'].
    + exact z2e_0108.
Qed.

Definition state_map (q: Q) := match q with A => D | B => E | C => F | D => A | E => B | F => C end.

Lemma perm: Perm TM1.tm tm state_map.
Proof. split.
- intros [] [] H; cbn in *; try discriminate; reflexivity.
- intros [] [] s d q H; cbn in H; inversion H; subst; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. exact (perm_nonhalt' TM1.tm tm state_map D tape0 perm nonhalt_canon). Qed.

End TM2.
Print Assumptions TM2.nonhalt.

From Coq Require Import String List Bool Arith PeanoNat PArith NArith ZArith QArith Lqa Lia.

Module TM3.
Import String List Bool Arith PeanoNat PArith NArith ZArith QArith Lqa Lia.

Import BusyCoq.Individual62.

Import ListNotations.

Open Scope list_scope.

Open Scope sym_scope.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD0LF_1LE---_1RF1RA_1RA0RE").

Notation "c ==> c'" := (c -[ TM1.tm ]-> c')   (at level 55, right associativity).

Notation "c ==>* c'" := (c -[ TM1.tm ]->* c') (at level 40).

Notation "c ==>+ c'" := (c -[ TM1.tm ]->+ c') (at level 40).

Record CCfg : Type := mkCCfg {
  cq : Q;
  chead : Sym;
  cleft : list Sym;
  cright : list Sym;
}.

Definition c_to_cfg (c : CCfg) : Q * tape :=
  cq c;; (cleft c *> 0inf%sym) {{chead c}} (cright c *> 0inf%sym).

Definition c_push (a : Sym) (l : list Sym) : list Sym :=
  match a, l with
  | S0, [] => []
  | _, _ => a :: l
  end.

Definition c_hd (l : list Sym) : Sym :=
  match l with
  | [] => S0
  | x :: _ => x
  end.

Definition c_tl (l : list Sym) : list Sym :=
  match l with
  | [] => []
  | _ :: xs => xs
  end.

Lemma c_push_eq (a : Sym) (l : list Sym) :
  c_push a l *> 0inf%sym = a >> (l *> 0inf%sym).
Proof.
  unfold c_push; destruct a, l; cbn; try reflexivity.
  rewrite <- const_unfold; reflexivity.
Qed.

Lemma c_hd_eq (l : list Sym) :
  hd (l *> 0inf%sym) = c_hd l.
Proof. destruct l; reflexivity. Qed.

Lemma c_tl_eq (l : list Sym) :
  tl (l *> 0inf%sym) = c_tl l *> 0inf%sym.
Proof. destruct l; reflexivity. Qed.

Definition c_step (c : CCfg) : option CCfg :=
  match TM1.tm (cq c, chead c) with
  | None => None
  | Some (a, L, q') =>
      Some (mkCCfg q' (c_hd (cleft c)) (c_tl (cleft c)) (c_push a (cright c)))
  | Some (a, R, q') =>
      Some (mkCCfg q' (c_hd (cright c)) (c_push a (cleft c)) (c_tl (cright c)))
  end.

Lemma c_step_spec (c c' : CCfg) :
  c_step c = Some c' -> c_to_cfg c ==> c_to_cfg c'.
Proof.
  unfold c_step, c_to_cfg; intros H.
  destruct (TM1.tm (cq c, chead c)) as [[[a d] q'] |] eqn:F; [| discriminate].
  destruct d; inversion H; subst; clear H; cbn [cq chead cleft cright].
  - apply (step_left (l := cleft c *> 0inf%sym) (r := cright c *> 0inf%sym)) in F.
    unfold move_left in F.
    rewrite c_hd_eq, c_tl_eq, <- c_push_eq in F.
    exact F.
  - apply (step_right (l := cleft c *> 0inf%sym) (r := cright c *> 0inf%sym)) in F.
    unfold move_right in F.
    rewrite c_hd_eq, c_tl_eq, <- c_push_eq in F.
    exact F.
Qed.

Fixpoint c_steps_pos (p : positive) (c : CCfg) : option CCfg :=
  match p with
  | xH => c_step c
  | xO p' =>
      match c_steps_pos p' c with
      | None => None
      | Some cm => c_steps_pos p' cm
      end
  | xI p' =>
      match c_steps_pos p' c with
      | None => None
      | Some cm1 =>
          match c_steps_pos p' cm1 with
          | None => None
          | Some cm2 => c_step cm2
          end
      end
  end.

Lemma c_steps_pos_spec (p : positive) (c c' : CCfg) :
  c_steps_pos p c = Some c' -> c_to_cfg c ==>+ c_to_cfg c'.
Proof.
  revert c c'; induction p as [p IHp | p IHp |]; intros c c' H; cbn [c_steps_pos] in H.
  - destruct (c_steps_pos p c) as [cm1 |] eqn:E1; [| discriminate].
    destruct (c_steps_pos p cm1) as [cm2 |] eqn:E2; [| discriminate].
    eapply progress_trans; [exact (IHp _ _ E1) |].
    eapply progress_trans; [exact (IHp _ _ E2) |].
    apply progress_base; exact (c_step_spec _ _ H).
  - destruct (c_steps_pos p c) as [cm |] eqn:E1; [| discriminate].
    eapply progress_trans; [exact (IHp _ _ E1) | exact (IHp _ _ H)].
  - apply progress_base; exact (c_step_spec _ _ H).
Qed.

Definition bt : list Sym := [1; 1; 0; 0]%sym.

Definition d0 : list Sym := [0; 0]%sym.

Definition d1 : list Sym := [1; 0]%sym.

Definition one : list Sym := [1]%sym.

Definition lh : side := [1; 0; 1]%sym *> 0inf%sym.

Definition w_word : list Sym := [0; 0; 0; 1; 1; 0; 1; 0]%sym.

Definition w_rest : list Sym :=
  bt ++ bt ++ (bt ++ d1) ++ bt ++ (bt ++ d0) ++ bt ++ (bt ++ d0) ++ bt ++ bt ++ d1 ++ (bt ++ one).

Definition w_base : list Sym := w_word ++ w_rest.

Lemma zDd : d0 *> 0inf%sym = 0inf%sym.
Proof.
  unfold d0; cbn.
  rewrite <- const_unfold, <- const_unfold.
  reflexivity.
Qed.

Inductive Call : Type :=
  | ch
  | cj
  | cp.

Definition zCs (c : Call) : Q :=
  match c with
  | ch => B
  | cj => A
  | cp => A
  end.

Definition zCw (c : Call) : list Sym :=
  match c with
  | ch => [1]%sym
  | cj => [1; 1]%sym
  | cp => [1; 0]%sym
  end.

Definition zCR (l : side) (c : Call) (r : side) : Q * tape :=
  (zCw c *> l) {{zCs c}}> r.

Definition zCL (l : side) (r : side) : Q * tape :=
  l <{{C}} ([0]%sym *> r).

Definition zCf (r : side) : Q * tape :=
  zCL lh (w_base *> r).

Definition z04 (c : Call) (r1 r2 : side) : Prop :=
  forall l : side, zCR l c r1 ==>+ zCL l r2.

Inductive Side : list Call -> side -> side -> Prop :=
  | Side_nil (r : side) : Side [] r r
  | Side_cons {c : Call} {ls : list Call} {r1 r2 r3 : side} :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3.

Definition Seg (ls_in ls_out : list Call) (w1 w2 : list Sym) : Prop :=
  forall r1 r2 : side, Side ls_out r1 r2 -> Side ls_in (w1 *> r1) (w2 *> r2).

Lemma z08 {ls1 ls2 : list Call} {r1 r2 r3 : side}
  (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3.
Proof.
  revert r3 h2.
  induction h1 as [r | c ls ra rb rc hc _ IH]; intros r3 h2;
    [exact h2 | exact (Side_cons hc (IH _ h2))].
Qed.

Lemma z09 {ls1 ls2 : list Call} {r1 r3 : side}
  (h : Side (ls1 ++ ls2) r1 r3) : exists r2, Side ls1 r1 r2 /\ Side ls2 r2 r3.
Proof.
  revert r1 h.
  induction ls1 as [| c ls1 IH]; intros r1 h.
  - exists r1; split; [constructor | exact h].
  - inverts h as hc hrest.
    destruct (IH _ hrest) as [rmid [h1 h2]].
    exists rmid; split; [exact (Side_cons hc h1) | exact h2].
Qed.

Lemma z0a (w : list Sym) : Seg [] [] w w.
Proof. intros r1 r2 h; inverts h; constructor. Qed.

Lemma z0m_id (ls : list Call) : Seg ls ls [] [].
Proof. intros r1 r2 h; exact h. Qed.

Lemma zSc {ls1 ls2 : list Call} {w1 w2 : list Sym} {r1 r2 : side}
  (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
  Side ls1 (w1 *> r1) (w2 *> r2).
Proof. exact (h1 r1 r2 h2). Qed.

Lemma zSg {ls1 ls2 ls3 ls4 : list Call} {w1 w2 w3 : list Sym}
  (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
  Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3.
Proof.
  intros r1 r3 h.
  destruct (z09 h) as [r2 [ha hb]].
  exact (z08 (h1 r1 r2 ha) (h2 r2 r3 hb)).
Qed.

Lemma zS0 {ls1 ls2 ls3 : list Call} {w1 w2 v1 v2 : list Sym}
  (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
  Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2).
Proof.
  intros r1 r2 h.
  rewrite !Str_app_assoc.
  exact (h1 (v1 *> r1) (v2 *> r2) (h2 r1 r2 h)).
Qed.

Lemma zS4 {c : Call} {w1 w2 : list Sym}
  (h1 : forall l r : side, zCR l c (w1 *> r) ==>+ zCL l (w2 *> r)) :
  Seg [c] [] w1 w2.
Proof.
  intros r1 r2 h; inverts h.
  exact (Side_cons (fun l => h1 l _) (Side_nil _)).
Qed.

Lemma zS2 {c_in c_out : Call} {w1 w2 mid : list Sym}
  (h1 : forall l r : side, zCR l c_in (w1 *> r) ==>+ zCR (mid *> l) c_out r)
  (h2 : forall l r : side, zCL (mid *> l) r ==>+ zCL l (w2 *> r)) :
  Seg [c_in] [c_out] w1 w2.
Proof.
  intros r1 r2 h.
  inverts h as hc1 hnil.
  inverts hnil.
  refine (Side_cons (fun l => _) (Side_nil _)).
  eapply progress_trans; [exact (h1 l _) |].
  eapply progress_trans; [exact (hc1 (mid *> l)) | exact (h2 l _)].
Qed.

Lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : list Sym}
  (h1 : forall l r : side, zCR l c_in (w1 *> r) ==>+ zCR (mid1 *> l) c1 r)
  (h2 : forall l r : side, zCL (mid1 *> l) r ==>+ zCR (mid2 *> l) c2 r)
  (h3 : forall l r : side, zCL (mid2 *> l) r ==>+ zCL l (w2 *> r)) :
  Seg [c_in] [c1; c2] w1 w2.
Proof.
  intros r1 r3 h.
  inverts h as hc1 hrest.
  inverts hrest as hc2 hnil.
  inverts hnil.
  refine (Side_cons (fun l => _) (Side_nil _)).
  eapply progress_trans; [exact (h1 l _) |].
  eapply progress_trans; [exact (hc1 (mid1 *> l)) |].
  eapply progress_trans; [exact (h2 l _) |].
  eapply progress_trans; [exact (hc2 (mid2 *> l)) | exact (h3 l _)].
Qed.

Lemma zS6 {c_in c1 c2 c3 : Call} {w1 w2 mid1 mid2 mid3 : list Sym}
  (h1 : forall l r : side, zCR l c_in (w1 *> r) ==>+ zCR (mid1 *> l) c1 r)
  (h2 : forall l r : side, zCL (mid1 *> l) r ==>+ zCR (mid2 *> l) c2 r)
  (h3 : forall l r : side, zCL (mid2 *> l) r ==>+ zCR (mid3 *> l) c3 r)
  (h4 : forall l r : side, zCL (mid3 *> l) r ==>+ zCL l (w2 *> r)) :
  Seg [c_in] [c1; c2; c3] w1 w2.
Proof.
  intros r1 r4 h.
  inverts h as hc1 hrest1.
  inverts hrest1 as hc2 hrest2.
  inverts hrest2 as hc3 hnil.
  inverts hnil.
  refine (Side_cons (fun l => _) (Side_nil _)).
  eapply progress_trans; [exact (h1 l _) |].
  eapply progress_trans; [exact (hc1 (mid1 *> l)) |].
  eapply progress_trans; [exact (h2 l _) |].
  eapply progress_trans; [exact (hc2 (mid2 *> l)) |].
  eapply progress_trans; [exact (h3 l _) |].
  eapply progress_trans; [exact (hc3 (mid3 *> l)) | exact (h4 l _)].
Qed.

Ltac solve_exec :=
  intros;
  unfold zCf, zCR, zCL, zCw, zCs, bt, d0, d1, one, lh, w_word;
  cbn [app Str_app];
  execute.

Lemma z0b : Seg [cp] [] bt [1; 1; 0; 1; 0]%sym.
Proof. apply zS4; solve_exec. Qed.

Lemma z0c_p : Seg [ch] [cp; ch] [1; 1; 0; 1; 0]%sym bt.
Proof. apply (zS5 (mid1 := [1; 0; 1; 1]%sym) (mid2 := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma z0c : Seg [cj] [cp] bt bt.
Proof. apply (zS2 (mid := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma zH2 : Seg [ch] [cj; ch] (bt ++ one) bt.
Proof. apply (zS5 (mid1 := [1; 0; 1; 1]%sym) (mid2 := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma z0d : Seg [ch] [ch; ch] bt bt.
Proof. apply (zS5 (mid1 := [1; 0; 1; 1]%sym) (mid2 := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma z0e : Seg [cp] [] (d1 ++ d0) (bt ++ one).
Proof. apply zS4; solve_exec. Qed.

Lemma z0f : Seg [cj] [cj] (d1 ++ d0) bt.
Proof. apply (zS2 (mid := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma z0g : Seg [cp] [cp] (d1 ++ d1) bt.
Proof. apply (zS2 (mid := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma z0h : Seg [cj] [cp; ch] (d1 ++ d1) bt.
Proof. apply (zS5 (mid1 := [1; 0; 1; 1]%sym) (mid2 := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma z0i : Seg [cj] [] d0 (d0 ++ one).
Proof. apply zS4; solve_exec. Qed.

Lemma zH1 : Seg [ch] [] (d0 ++ one) (d1 ++ one).
Proof. apply zS4; solve_exec. Qed.

Lemma zH3 : Seg [ch] [cj] (d1 ++ one) d0.
Proof. apply (zS2 (mid := [1; 1]%sym)); solve_exec. Qed.

Lemma z0j : Seg [cj] [cp] d1 d0.
Proof. apply (zS2 (mid := [1; 1]%sym)); solve_exec. Qed.

Lemma zH0 : Seg [ch] [] d0 d1.
Proof. apply zS4; solve_exec. Qed.

Lemma zH4 : Seg [ch] [ch] d1 d0.
Proof. apply (zS2 (mid := [1; 1]%sym)); solve_exec. Qed.

Lemma zC_base : Seg [cp] [ch; cp] [0; 1; 1; 1]%sym bt.
Proof. apply (zS5 (mid1 := [0; 1; 1; 1; 0]%sym) (mid2 := [1; 0; 1; 0]%sym)); solve_exec. Qed.

Lemma zO_head : Seg [cp] [] [1; 0; 0; 0]%sym [1; 1; 0; 0; 1]%sym.
Proof. apply zS4; solve_exec. Qed.

Lemma zO_mid : Seg [ch] [ch; cp; ch] [1; 0; 1; 1; 1]%sym bt.
Proof.
  apply (zS6 (mid1 := [0; 1; 1; 1; 1]%sym) (mid2 := [1; 0; 1; 1]%sym) (mid3 := [1; 0; 1; 0]%sym));
    solve_exec.
Qed.

Lemma zO_b0 : Seg [cp] [ch] [1; 1]%sym [1; 1; 0]%sym.
Proof. apply (zS2 (mid := [0; 1; 0]%sym)); solve_exec. Qed.

Lemma zO_b2 : Seg [ch] [cp] [1; 1; 0]%sym d0.
Proof. apply (zS2 (mid := [1; 1]%sym)); solve_exec. Qed.

Lemma zE_head : Seg [cj] [] [0; 0; 1; 0; 0; 0]%sym [0; 0; 1; 1; 0; 0; 0]%sym.
Proof. apply zS4; solve_exec. Qed.

Lemma zE_b0 : Seg [cj] [] [0; 0; 1; 1]%sym [0; 0; 1; 1; 1]%sym.
Proof. apply zS4; solve_exec. Qed.

Lemma zW_td1a : Seg [cp] [] (bt ++ d1) [1; 1; 0; 1; 0; 1; 0]%sym.
Proof. apply zS4; solve_exec. Qed.

Lemma zW_td1b : Seg [ch] [cp] [1; 1; 0; 1; 0; 1; 0]%sym (d0 ++ bt).
Proof. apply (zS2 (mid := [1; 0; 1; 0; 1; 1]%sym)); solve_exec. Qed.

Lemma zW_td0a : Seg [cp] [] (bt ++ d0) [1; 1; 0; 1; 0; 0; 0]%sym.
Proof. apply zS4; solve_exec. Qed.

Lemma zW_td0b : Seg [ch] [] [1; 1; 0; 1; 0; 0; 0]%sym (d0 ++ (bt ++ one)).
Proof. apply zS4; solve_exec. Qed.

Open Scope nat_scope.

Lemma zS3 (n : nat) : Seg ([ch]^^n) ([ch]^^(n * 2)) bt bt.
Proof.
  induction n as [| n IH]; [exact (z0a bt) |].
  replace (S n * 2) with (2 + n * 2) by lia.
  rewrite lpow_add; cbn [lpow app].
  exact (zSg z0d IH).
Qed.

Lemma zT_pow (r : nat) : forall n, Seg ([ch]^^n) ([ch]^^(n * 2 ^ r)) (bt^^r) (bt^^r).
Proof.
  induction r as [| r IH]; intros n.
  - replace (n * 2 ^ 0) with n by (cbn; lia).
    exact (z0m_id _).
  - replace (n * 2 ^ S r) with ((n * 2) * 2 ^ r) by (cbn [Nat.pow]; lia).
    cbn [lpow].
    exact (zS0 (zS3 n) (IH (n * 2))).
Qed.

Lemma zSa {w2 : list Sym} (hw : Seg [ch; ch] [ch] w2 w2) (n : nat) :
  Seg ([ch]^^(n * 2)) ([ch]^^n) w2 w2.
Proof.
  induction n as [| n IH]; [exact (z0a w2) |].
  replace (S n * 2) with (2 + n * 2) by lia.
  rewrite lpow_add; cbn [lpow app].
  exact (zSg hw IH).
Qed.

Lemma z0k : Seg [ch; ch] [ch] d0 d0. Proof. exact (zSg zH0 zH4). Qed.

Lemma z0l : Seg [ch; ch] [ch] d1 d1. Proof. exact (zSg zH4 zH0). Qed.

Lemma zH_d0_even (n : nat) : Seg ([ch]^^(n * 2)) ([ch]^^n) d0 d0.
Proof. exact (zSa z0k n). Qed.

Lemma zH_d0_odd (n : nat) : Seg ([ch]^^(1 + n * 2)) ([ch]^^n) d0 d1.
Proof. cbn [Nat.add lpow app]; exact (zSg zH0 (zSa z0l n)). Qed.

Lemma zH_d1_even (n : nat) : Seg ([ch]^^(n * 2)) ([ch]^^n) d1 d1.
Proof. exact (zSa z0l n). Qed.

Lemma zH_d1_odd (n : nat) : Seg ([ch]^^(1 + n * 2)) ([ch]^^(1 + n)) d1 d0.
Proof. cbn [Nat.add lpow app]; exact (zSg zH4 (zSa z0k n)). Qed.

Lemma z0m (n : nat) : Seg ([cp] ++ [ch]^^(1 + n)) ([cp] ++ [ch]^^(1 + n * 2)) bt bt.
Proof. cbn [Nat.add lpow app]; exact (zSg (zSg z0b z0c_p) (zS3 n)). Qed.

Lemma z0n (n : nat) : Seg ([cj] ++ [ch]^^n) ([cp] ++ [ch]^^(n * 2)) bt bt.
Proof. exact (zSg z0c (zS3 n)). Qed.

Lemma z0o (n : nat) : Seg ([cp] ++ [ch]^^(1 + n)) ([cj] ++ [ch]^^(1 + n * 2)) (d1 ++ d0) bt.
Proof. cbn [Nat.add lpow app]; exact (zSg (zSg z0e zH2) (zS3 n)). Qed.

Lemma z0p (n : nat) : Seg ([cj] ++ [ch]^^n) ([cj] ++ [ch]^^(n * 2)) (d1 ++ d0) bt.
Proof. exact (zSg z0f (zS3 n)). Qed.

Lemma z0q (n : nat) : Seg ([cp] ++ [ch]^^n) ([cp] ++ [ch]^^(n * 2)) (d1 ++ d1) bt.
Proof. exact (zSg z0g (zS3 n)). Qed.

Lemma z0r (n : nat) : Seg ([cj] ++ [ch]^^n) ([cp] ++ [ch]^^(1 + n * 2)) (d1 ++ d1) bt.
Proof. cbn [Nat.add lpow app]; exact (zSg z0h (zS3 n)). Qed.

Lemma z0s (n : nat) : Seg ([cj] ++ [ch]^^(2 + n * 2)) ([cj] ++ [ch]^^n) d0 d0.
Proof.
  pose proof (zSg z0i (zSg zH1 zH3)) as h0.
  cbn [Nat.add lpow app] in *.
  exact (zSg h0 (zSa z0k n)).
Qed.

Lemma z0t (n : nat) : Seg ([cj] ++ [ch]^^(n * 2)) ([cp] ++ [ch]^^n) d1 d0.
Proof. exact (zSg z0j (zSa z0k n)). Qed.

Lemma z0u : Seg [cj; ch] [] d0 (d1 ++ one).
Proof. exact (zSg z0i zH1). Qed.

Lemma z0v (n : nat) : Seg ([cj] ++ [ch]^^(3 + n * 2)) ([cj] ++ [ch]^^n) d0 d1.
Proof.
  pose proof (zSg z0i (zSg zH1 (zSg zH3 zH0))) as h0.
  cbn [Nat.add lpow app] in *.
  exact (zSg h0 (zSa z0l n)).
Qed.

Lemma z0w (n : nat) : Seg ([cj] ++ [ch]^^(1 + n * 2)) ([cp] ++ [ch]^^n) d1 d1.
Proof.
  pose proof (zSg z0j zH0) as h0.
  cbn [Nat.add lpow app] in *.
  exact (zSg h0 (zSa z0l n)).
Qed.

Lemma zCp_step {r r_out : side} (h : Side [cp] ([0; 1]%sym *> r) r_out) :
  Side [cp] ([0; 1; 1; 0; 0; 0]%sym *> r) (bt *> r_out).
Proof.
  inverts h as hcp hnil; inverts hnil.
  refine (Side_cons (fun l => _) (Side_nil _)).
  assert (h1 : zCR l cp ([0; 1; 1; 0; 0; 0]%sym *> r) ==>+ zCR ([1; 0; 1; 0]%sym *> l) cp ([0; 1]%sym *> r))
    by solve_exec.
  assert (h2 : zCL ([1; 0; 1; 0]%sym *> l) r_out ==>+ zCL l (bt *> r_out))
    by solve_exec.
  eapply progress_trans; [exact h1 |].
  eapply progress_trans; [exact (hcp ([1; 0; 1; 0]%sym *> l)) | exact h2].
Qed.

Lemma zCp_chain (m : nat) :
  Seg [cp] [ch; cp] ([0; 1]%sym ++ (d1 ++ d0)^^m ++ [1; 1]%sym) (bt^^(1 + m)).
Proof.
  induction m as [| m IH].
  - cbn [Nat.add lpow app].
    replace (bt ++ []) with bt by reflexivity.
    exact zC_base.
  - intros r1 r2 h.
    pose proof (IH r1 r2 h) as h_sub.
    change (Side [cp] ([0; 1]%sym *> (((d1 ++ d0)^^m ++ [1; 1]%sym) *> r1)) (bt^^(1 + m) *> r2)) in h_sub.
    pose proof (zCp_step h_sub) as h_step.
    change (Side [cp] (([0; 1]%sym ++ (d1 ++ d0)^^(S m) ++ [1; 1]%sym) *> r1) (bt *> (bt^^(1 + m) *> r2))) in h_step.
    rewrite <- Str_app_assoc in h_step.
    exact h_step.
Qed.

Lemma zOdd_base (r : nat) :
  Seg [cp; ch] [ch; cp] ((d1 ++ d0)^^r ++ [1; 1]%sym) (d0 ++ bt^^r).
Proof.
  destruct r as [| m].
  - cbn [lpow app].
    replace (d0 ++ []) with d0 by reflexivity.
    exact (zSg zO_b0 zO_b2).
  - pose proof (zS0 zO_head (z0a ((d1 ++ d0)^^m ++ [1; 1]%sym))) as h1.
    pose proof (zS0 zO_b2 (zCp_chain m)) as h2.
    cbn [Nat.add lpow app] in *.
    exact (zSg h1 h2).
Qed.

Lemma zEven_ch_step {r r_mid r_out : side}
  (h1 : Side [cp] ([0; 1]%sym *> r) r_mid)
  (h2 : Side [ch] r_mid r_out) :
  Side [ch] ([1; 0; 1; 1; 0; 0; 0]%sym *> r) (bt *> r_out).
Proof.
  inverts h1 as hcp hnil1; inverts hnil1.
  inverts h2 as hch hnil2; inverts hnil2.
  refine (Side_cons (fun l => _) (Side_nil _)).
  assert (hs1 : zCR l ch ([1; 0; 1; 1; 0; 0; 0]%sym *> r) ==>+ zCR ([1; 0; 1; 1]%sym *> l) cp ([0; 1]%sym *> r))
    by solve_exec.
  assert (hs2 : zCL ([1; 0; 1; 1]%sym *> l) r_mid ==>+ zCR ([1; 0; 1; 0]%sym *> l) ch r_mid)
    by solve_exec.
  assert (hs3 : zCL ([1; 0; 1; 0]%sym *> l) r_out ==>+ zCL l (bt *> r_out))
    by solve_exec.
  eapply progress_trans; [exact hs1 |].
  eapply progress_trans; [exact (hcp ([1; 0; 1; 1]%sym *> l)) |].
  eapply progress_trans; [exact hs2 |].
  eapply progress_trans; [exact (hch ([1; 0; 1; 0]%sym *> l)) | exact hs3].
Qed.

Lemma zEven_base (r : nat) :
  Seg [cj; ch; ch] ([ch; cp] ++ [ch]^^(2 ^ r)) (d0 ++ (d1 ++ d0)^^r ++ [1; 1]%sym) (bt^^(1 + r)).
Proof.
  destruct r as [| m].
  - cbn [Nat.add Nat.pow lpow app].
    replace (bt ++ []) with bt by reflexivity.
    pose proof (zSg zE_b0 (zSg (zS0 zH0 (z0a [1; 1; 1]%sym)) zO_mid)) as H.
    cbn [d0 d1 app] in H |- *.
    exact H.
  - intros r1 r2 h.
    replace (2 ^ S m) with (1 * 2 ^ (1 + m)) in h by (cbn [Nat.add Nat.pow]; lia).
    destruct (z09 h) as [r_mid [h_cp h_ch_pow]].
    pose proof (zCp_chain m r1 r_mid h_cp) as h_cp_seg.
    assert (h_ch_pow' : Side ([ch]^^(1 * 2 ^ (1 + m))) r_mid r2) by exact h_ch_pow.
    pose proof (zT_pow (1 + m) 1 r_mid r2 h_ch_pow') as h_ch_seg.
    cbn [lpow app] in h_ch_seg.
    change (Side [cp] ([0; 1]%sym *> (((d1 ++ d0)^^m ++ [1; 1]%sym) *> r1)) (bt^^(1 + m) *> r_mid)) in h_cp_seg.
    pose proof (zEven_ch_step h_cp_seg h_ch_seg) as h_step3.
    pose proof ((zS0 zH0 (z0a [1; 1; 0; 0; 0]%sym)) (((d1 ++ d0)^^m ++ [1; 1]%sym) *> r1) _ (Side_nil _)) as h_s2.
    pose proof (z08 h_s2 h_step3) as h_step2.
    pose proof (zE_head (((d1 ++ d0)^^m ++ [1; 1]%sym) *> r1) _ (Side_nil _)) as h_s1.
    pose proof (z08 h_s1 h_step2) as h_step1.
    rewrite <- Str_app_assoc in h_step1.
    exact h_step1.
Qed.

Lemma zW_turn {r r' : side} (h : Side [ch; cj; ch] r r') :
  zCL lh (w_word *> r) ==>+ zCL lh ((w_word ++ bt ++ bt ++ (bt ++ d1)) *> r').
Proof.
  inverts h as hc1 hrest1.
  inverts hrest1 as hc2 hrest2.
  inverts hrest2 as hc3 hnil.
  inverts hnil.
  assert (h1a : zCL lh (w_word *> r) ==>+
      (([1; 1; 0; 1; 1; 1; 1; 0; 1]%sym *> 0inf%sym) <{{C}} ([1; 1; 1; 0; 0; 0; 0; 1; 1; 1; 0; 1; 0]%sym *> r)))
    by solve_exec.
  assert (h1b : (([1; 1; 0; 1; 1; 1; 1; 0; 1]%sym *> 0inf%sym) <{{C}} ([1; 1; 1; 0; 0; 0; 0; 1; 1; 1; 0; 1; 0]%sym *> r)) ==>+
      zCR ([1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) ch r)
    by solve_exec.
  assert (h2a : forall s1, zCL ([1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) s1 ==>+
      (([1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) {{A}}> ([1; 0; 1; 0; 0; 0; 0; 1]%sym *> s1)))
    by solve_exec.
  assert (h2b : forall s1, (([1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) {{A}}> ([1; 0; 1; 0; 0; 0; 0; 1]%sym *> s1)) ==>+
      zCR ([1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) cj s1)
    by solve_exec.
  assert (h3 : forall s2, zCL ([1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) s2 ==>+
      zCR ([1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) ch s2)
    by solve_exec.
  assert (h4a : zCL ([1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) r' ==>+
      (([1; 0; 0; 1]%sym *> 0inf%sym) <{{D}} ([1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 0]%sym *> r')))
    by solve_exec.
  assert (h4b : (([1; 0; 0; 1]%sym *> 0inf%sym) <{{D}} ([1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 0]%sym *> r')) ==>+
      zCL lh ((w_word ++ bt ++ bt ++ (bt ++ d1)) *> r'))
    by solve_exec.
  eapply progress_trans; [exact h1a |].
  eapply progress_trans; [exact h1b |].
  eapply progress_trans; [exact (hc1 _) |].
  eapply progress_trans; [exact (h2a _) |].
  eapply progress_trans; [exact (h2b _) |].
  eapply progress_trans; [exact (hc2 _) |].
  eapply progress_trans; [exact (h3 _) |].
  eapply progress_trans; [exact (hc3 _) |].
  eapply progress_trans; [exact h4a | exact h4b].
Qed.

Lemma zW_s1 : Seg [ch; cj; ch] ([ch]^^2 ++ [cp] ++ [ch]^^2) bt bt.
Proof. cbn [lpow app]; exact (zSg z0d (zSg z0c z0d)). Qed.

Lemma zW_s2 : Seg ([ch]^^2 ++ [cp] ++ [ch]^^2) ([ch]^^4 ++ [cp] ++ [ch]^^3) bt bt.
Proof. cbn [lpow app]; exact (zSg (zS3 2) (z0m 1)). Qed.

Lemma zW_s3 : Seg ([ch]^^4 ++ [cp] ++ [ch]^^3) ([ch]^^4 ++ [cp] ++ [ch]^^2) (bt ++ d1) (d0 ++ bt).
Proof.
  pose proof (zS0 (zS3 4) (zH_d1_even 4)) as ha.
  pose proof (zSg (zSg zW_td1a zW_td1b) (zS0 (zH_d0_even 1) (zS3 1))) as hb.
  cbn [lpow app] in ha, hb |- *.
  exact (zSg ha hb).
Qed.

Lemma zW_s4 : Seg ([ch]^^4 ++ [cp] ++ [ch]^^2) ([ch]^^8 ++ [cp] ++ [ch]^^3) bt bt.
Proof. cbn [lpow app]; exact (zSg (zS3 4) (z0m 1)). Qed.

Lemma zW_s5 : Seg ([ch]^^8 ++ [cp] ++ [ch]^^3) ([ch]^^8 ++ [cj; ch]) (bt ++ d0) (d0 ++ bt).
Proof.
  pose proof (zS0 (zS3 8) (zH_d0_even 8)) as ha.
  pose proof (zSg (zSg zW_td0a zW_td0b) (zSg (zS0 zH0 (z0a (bt ++ one))) (zS0 zH4 zH2))) as hb.
  cbn [lpow app] in ha, hb |- *.
  exact (zSg ha hb).
Qed.

Lemma zW_s6 : Seg ([ch]^^8 ++ [cj; ch]) ([ch]^^16 ++ [cp] ++ [ch]^^2) bt bt.
Proof.
  pose proof (zSg (zS3 8) (z0n 1)) as H.
  cbn [lpow app] in H |- *.
  exact H.
Qed.

Lemma zW_s7 : Seg ([ch]^^16 ++ [cp] ++ [ch]^^2) ([ch]^^16) (bt ++ d0) (d1 ++ (bt ++ one)).
Proof.
  pose proof (zS0 (zS3 16) (zH_d0_even 16)) as ha.
  pose proof (zSg (zSg zW_td0a zW_td0b) (zS0 zH0 (z0a (bt ++ one)))) as hb.
  pose proof (zSg ha hb) as H.
  cbn [lpow app] in H |- *.
  exact H.
Qed.

Lemma zW_s8 : Seg ([ch]^^16) ([ch]^^32) bt bt. Proof. exact (zS3 16). Qed.

Lemma zW_s9 : Seg ([ch]^^32) ([ch]^^64) bt bt. Proof. exact (zS3 32). Qed.

Lemma zW_s10 : Seg ([ch]^^64) ([ch]^^32) d1 d1. Proof. exact (zH_d1_even 32). Qed.

Lemma zW_s11 : Seg ([ch]^^32) ([cj] ++ [ch]^^63) (bt ++ one) bt.
Proof.
  pose proof (zSg zH2 (zS3 31)) as H.
  cbn [lpow app] in H |- *.
  exact H.
Qed.

Lemma zW_rest_seg :
  Seg [ch; cj; ch] ([cj] ++ [ch]^^63) w_rest
    (bt ++ bt ++ (d0 ++ bt) ++ bt ++ (d0 ++ bt) ++ bt ++ (d1 ++ (bt ++ one)) ++ bt ++ bt ++ d1 ++ bt).
Proof.
  unfold w_rest.
  exact (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 zW_s1 zW_s2) zW_s3) zW_s4) zW_s5) zW_s6) zW_s7) zW_s8) zW_s9) zW_s10) zW_s11).
Qed.

Lemma zW_full {r r' : side} (h : Side ([cj] ++ [ch]^^63) r r') :
  zCf r ==>+ zCf ((bt ++ bt ++ d1 ++ bt) *> r').
Proof.
  pose proof (zW_rest_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  unfold zCf.
  assert (h_in : w_word *> (w_rest *> r) = w_base *> r).
  { unfold w_base; rewrite Str_app_assoc; reflexivity. }
  assert (h_out : (w_word ++ bt ++ bt ++ (bt ++ d1)) *>
      ((bt ++ bt ++ (d0 ++ bt) ++ bt ++ (d0 ++ bt) ++ bt ++ (d1 ++ (bt ++ one)) ++ bt ++ bt ++ d1 ++ bt) *> r') =
      w_base *> ((bt ++ bt ++ d1 ++ bt) *> r'))
    by reflexivity.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

Definition w_pre3_rest : list Sym := bt ++ bt ++ (bt ++ d1).

Definition w_pre3 : list Sym := w_word ++ w_pre3_rest.

Definition w_pre5_rest : list Sym := w_pre3_rest ++ bt ++ (bt ++ d0).

Definition w_pre5 : list Sym := w_word ++ w_pre5_rest.

Definition w_pre_rest : list Sym := w_pre5_rest ++ bt ++ (bt ++ d0).

Definition w_pre : list Sym := w_word ++ w_pre_rest.

Lemma zW_pre3_seg :
  Seg [ch; cj; ch] ([ch]^^4 ++ [cp] ++ [ch]^^2) w_pre3_rest
    (bt ++ bt ++ (d0 ++ bt)).
Proof.
  unfold w_pre3_rest.
  exact (zS0 (zS0 zW_s1 zW_s2) zW_s3).
Qed.

Lemma zW_pre5_seg :
  Seg [ch; cj; ch] ([ch]^^8 ++ [cj; ch]) w_pre5_rest
    (bt ++ bt ++ (d0 ++ bt) ++ bt ++ (d0 ++ bt)).
Proof.
  unfold w_pre5_rest.
  exact (zS0 (zS0 zW_pre3_seg zW_s4) zW_s5).
Qed.

Lemma zW_pre_seg :
  Seg [ch; cj; ch] ([ch]^^16) w_pre_rest
    (bt ++ bt ++ (d0 ++ bt) ++ bt ++ (d0 ++ bt) ++ bt ++ (d1 ++ (bt ++ one))).
Proof.
  unfold w_pre_rest.
  exact (zS0 (zS0 zW_pre5_seg zW_s6) zW_s7).
Qed.

Lemma zW_pre3_full {r r' : side} (h : Side ([ch]^^4 ++ [cp] ++ [ch]^^2) r r') :
  zCL lh (w_pre3 *> r) ==>+ zCL lh (w_pre5 *> (bt *> r')).
Proof.
  pose proof (zW_pre3_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  assert (h_in : w_word *> (w_pre3_rest *> r) = w_pre3 *> r).
  { unfold w_pre3; rewrite Str_app_assoc; reflexivity. }
  assert (h_out : (w_word ++ bt ++ bt ++ (bt ++ d1)) *> ((bt ++ bt ++ (d0 ++ bt)) *> r') =
                  w_pre5 *> (bt *> r'))
    by reflexivity.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

Lemma zW_pre5_full {r r' : side} (h : Side ([ch]^^8 ++ [cj; ch]) r r') :
  zCL lh (w_pre5 *> r) ==>+ zCL lh (w_pre *> (bt *> r')).
Proof.
  pose proof (zW_pre5_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  assert (h_in : w_word *> (w_pre5_rest *> r) = w_pre5 *> r).
  { unfold w_pre5; rewrite Str_app_assoc; reflexivity. }
  assert (h_out : (w_word ++ bt ++ bt ++ (bt ++ d1)) *> ((bt ++ bt ++ (d0 ++ bt) ++ bt ++ (d0 ++ bt)) *> r') =
                  w_pre *> (bt *> r'))
    by reflexivity.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

Lemma zW_pre_full {r r' : side} (h : Side ([ch]^^16) r r') :
  zCL lh (w_pre *> r) ==>+ zCf r'.
Proof.
  pose proof (zW_pre_seg r r' h) as h_side.
  pose proof (zW_turn h_side) as h_turn.
  unfold zCf.
  assert (h_in : w_word *> (w_pre_rest *> r) = w_pre *> r).
  { unfold w_pre; rewrite Str_app_assoc; reflexivity. }
  assert (h_out : (w_word ++ bt ++ bt ++ (bt ++ d1)) *>
                  ((bt ++ bt ++ (d0 ++ bt) ++ bt ++ (d0 ++ bt) ++ bt ++ (d1 ++ (bt ++ one))) *> r') =
                  w_base *> r')
    by reflexivity.
  rewrite <- h_in, <- h_out.
  exact h_turn.
Qed.

Lemma z108_seg :
  Seg ([ch]^^16) ([cj] ++ [ch]^^31) (d0 ++ bt ++ (bt ++ one)) (d0 ++ bt ++ bt).
Proof.
  pose proof (zH_d0_even 8) as h1.
  pose proof (zS3 8) as h2.
  pose proof (zSg zH2 (zS3 15)) as h3.
  cbn [lpow app] in h1, h2, h3 |- *.
  exact (zS0 (zS0 h1 h2) h3).
Qed.

Inductive Word : Type :=
  | WV
  | WK
  | WQ.

Notation zW := (list Word).

Definition zR (n : nat) (x : Word) : zW := repeat x n.

Fixpoint zQK (r : nat) (u : zW) : zW :=
  match r with
  | 0 => u
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
  | WV :: u' => bt *> zTs u' r
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
  zTs (zR r_ch WV) r = (bt^^r_ch) *> r.
Proof.
  unfold zR; induction r_ch as [| r_ch IH]; [reflexivity |].
  cbn [repeat zTs lpow]; rewrite IH, Str_app_assoc; reflexivity.
Qed.

Lemma zTs_QK (r_ch : nat) (r : side) :
  zTs (zQK r_ch [WV]) r = ((d1 ++ d0)^^r_ch ++ [1; 1]%sym) *> (d0 *> r).
Proof.
  induction r_ch as [| r_ch IH]; [reflexivity |].
  cbn [zQK zTs lpow].
  rewrite IH; reflexivity.
Qed.

Inductive BRIncs : bool -> nat -> side -> side -> Prop :=
  | BRIncs_zero (r : side) : BRIncs false 0 r (one *> r)
  | BRIncs_T {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (2 + n) (bt *> r) (bt *> r')
  | BRIncs_pair0 {n : nat} {r r' : side} :
      BRIncs false (n * 2) r r' -> BRIncs false (1 + n) (d1 *> (d0 *> r)) (bt *> r')
  | BRIncs_pair1 {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (1 + n) (d1 *> (d1 *> r)) (bt *> r')
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
      BRIncs false (n * 2) r r' -> BRIncs true (1 + n) (d0 *> r) (bt *> r')
  | BRIncs_shift_pair1 {n : nat} {r r' : side} :
      BRIncs false (1 + n * 2) r r' -> BRIncs true (1 + n) (d1 *> r) (bt *> r')
  | BRIncs_shift_chain0 (r_ch : nat) {m : nat} {r r' : side} :
      BRIncs true (1 + m * 2 ^ (2 + r_ch)) r r' ->
      BRIncs true (3 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR (1 + r_ch) WV) r')
  | BRIncs_shift_chain1 (r_ch : nat) {m : nat} {r r' : side} :
      BRIncs true (1 + m * 2 ^ (2 + r_ch)) r r' ->
      BRIncs true (5 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR (1 + r_ch) WV) r').

Inductive Num : bool -> nat -> list Sym -> list Call -> Prop :=
  | Num_zero : Num false 0 one []
  | Num_odd (n : nat) : Num false (1 + n * 2) [] ([cp] ++ [ch]^^n)
  | Num_even (n : nat) : Num false (2 + n * 2) [] ([cj] ++ [ch]^^n)
  | Num_shift (n : nat) : Num true (1 + n * 2) d0 ([ch; cp] ++ [ch]^^n).

Definition z2f (s : bool) (k : nat) (r r' : side) : Prop :=
  forall w hs, Num s k w hs -> Side hs (w *> r) r'.

Lemma z2g {r r' : side} (h : z2f false 0 r r') :
  r' = one *> r.
Proof.
  pose proof (h one [] Num_zero) as h0.
  inverts h0; reflexivity.
Qed.

Lemma z2h {n : nat} {r r' : side}
  (hI : z2f false (1 + n * 2) r r') : z2f false (2 + n) (bt *> r) (bt *> r').
Proof.
  intros w hs hN; inversion hN as [| m | m |]; subst w hs; try lia.
  - cbn [Str_app].
    destruct m as [| m]; [lia |].
    replace (S m) with (1 + m) by lia.
    eapply zSc; [exact (z0m m) |].
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch]^^(1 + m * 2))).
    { replace (1 + n * 2) with (1 + (1 + m * 2) * 2) by lia.
      exact (Num_odd (1 + m * 2)). }
    exact (hI [] _ hN1).
  - cbn [Str_app].
    eapply zSc; [exact (z0n m) |].
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch]^^(m * 2))).
    { replace (1 + n * 2) with (1 + (m * 2) * 2) by lia.
      exact (Num_odd (m * 2)). }
    exact (hI [] _ hN1).
Qed.

Lemma z2i_p0 {n : nat} {r r' : side}
  (hI : z2f false (n * 2) r r') : z2f false (1 + n) (d1 *> (d0 *> r)) (bt *> r').
Proof.
  intros w hs hN; inversion hN as [| m | m |]; subst w hs; try lia.
  - cbn [Str_app].
    rewrite <- Str_app_assoc.
    destruct m as [| m].
    + assert (hn0 : n * 2 = 0) by lia.
      rewrite hn0 in hI.
      rewrite (z2g hI), <- Str_app_assoc.
      exact (zSc z0e (Side_nil r)).
    + replace (S m) with (1 + m) by lia.
      eapply zSc; [exact (z0o m) |].
      assert (hN2 : Num false (n * 2) [] ([cj] ++ [ch]^^(1 + m * 2))).
      { replace (n * 2) with (2 + (1 + m * 2) * 2) by lia.
        exact (Num_even (1 + m * 2)). }
      exact (hI [] _ hN2).
  - cbn [Str_app].
    rewrite <- Str_app_assoc.
    eapply zSc; [exact (z0p m) |].
    assert (hN2 : Num false (n * 2) [] ([cj] ++ [ch]^^(m * 2))).
    { replace (n * 2) with (2 + (m * 2) * 2) by lia.
      exact (Num_even (m * 2)). }
    exact (hI [] _ hN2).
Qed.

Lemma z2j {n : nat} {r r' : side}
  (hI : z2f false (1 + n * 2) r r') : z2f false (1 + n) (d1 *> (d1 *> r)) (bt *> r').
Proof.
  intros w hs hN; inversion hN as [| m | m |]; subst w hs; try lia.
  - cbn [Str_app]; rewrite <- Str_app_assoc.
    eapply zSc; [exact (z0q m) |].
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch]^^(m * 2))).
    { replace (1 + n * 2) with (1 + (m * 2) * 2) by lia.
      exact (Num_odd (m * 2)). }
    exact (hI [] _ hN1).
  - cbn [Str_app]; rewrite <- Str_app_assoc.
    eapply zSc; [exact (z0r m) |].
    assert (hN1 : Num false (1 + n * 2) [] ([cp] ++ [ch]^^(1 + m * 2))).
    { replace (1 + n * 2) with (1 + (1 + m * 2) * 2) by lia.
      exact (Num_odd (1 + m * 2)). }
    exact (hI [] _ hN1).
Qed.

Lemma z2k {n : nat} {r r' : side}
  (hI : z2f false (n * 2) r r') : z2f false (2 + n * 4) (d0 *> r) (d0 *> r').
Proof.
  intros w hs hN; inversion hN as [| m | m |]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = n * 2) by lia; subst m.
  destruct n as [| n].
  - cbn [Nat.mul] in hI.
    rewrite (z2g hI), <- Str_app_assoc.
    exact (zSc z0i (Side_nil r)).
  - replace (S n * 2) with (2 + n * 2) by lia.
    eapply zSc; [exact (z0s n) |].
    assert (hN2 : Num false (S n * 2) [] ([cj] ++ [ch]^^n)).
    { replace (S n * 2) with (2 + n * 2) by lia.
      exact (Num_even n). }
    exact (hI [] _ hN2).
Qed.

Lemma z2l {n : nat} {r r' : side}
  (hI : z2f false (1 + n * 2) r r') : z2f false (2 + n * 4) (d1 *> r) (d0 *> r').
Proof.
  intros w hs hN; inversion hN as [| m | m |]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = n * 2) by lia; subst m.
  eapply zSc; [exact (z0t n) |].
  exact (hI [] _ (Num_odd n)).
Qed.

Lemma z2m {n : nat} {r r' : side}
  (hI : z2f false (n * 2) r r') : z2f false (4 + n * 4) (d0 *> r) (d1 *> r').
Proof.
  intros w hs hN; inversion hN as [| m | m |]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = 1 + n * 2) by lia; subst m.
  destruct n as [| n].
  - cbn [Nat.mul Nat.add] in hI |- *.
    rewrite (z2g hI), <- Str_app_assoc.
    exact (zSc z0u (Side_nil r)).
  - replace (1 + S n * 2) with (3 + n * 2) by lia.
    eapply zSc; [exact (z0v n) |].
    assert (hN2 : Num false (S n * 2) [] ([cj] ++ [ch]^^n)).
    { replace (S n * 2) with (2 + n * 2) by lia.
      exact (Num_even n). }
    exact (hI [] _ hN2).
Qed.

Lemma z2n {n : nat} {r r' : side}
  (hI : z2f false (1 + n * 2) r r') : z2f false (4 + n * 4) (d1 *> r) (d1 *> r').
Proof.
  intros w hs hN; inversion hN as [| m | m |]; subst w hs; try lia.
  cbn [Str_app].
  assert (hm : m = 1 + n * 2) by lia; subst m.
  eapply zSc; [exact (z0w n) |].
  exact (hI [] _ (Num_odd n)).
Qed.

Lemma z2_oc0 (r_ch : nat) {m : nat} {r r' : side}
  (hI : z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
  z2f false (3 + m * 4) (zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR r_ch WV) r').
Proof.
  intros w hs hN; inversion hN as [| n | |]; subst w hs; try lia.
  cbn [Str_app].
  assert (hn : n = 1 + m * 2) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 (bt^^r_ch)).
  assert (h_seg : Seg ([cp] ++ [ch]^^(1 + m * 2)) ([ch; cp] ++ [ch]^^(m * 2 ^ r_ch))
                      ((d1 ++ d0)^^r_ch ++ [1; 1]%sym) (d0 ++ bt^^r_ch)).
  { pose proof (zOdd_base r_ch) as h1.
    pose proof (zS0 (zH_d0_even m) (zT_pow r_ch m)) as h2.
    cbn [Nat.add lpow app] in h1, h2 |- *.
    exact (zSg h1 h2). }
  eapply zSc; [exact h_seg |].
  assert (h_num : Num true (1 + m * 2 ^ (1 + r_ch)) d0 ([ch; cp] ++ [ch]^^(m * 2 ^ r_ch))).
  { replace (1 + m * 2 ^ (1 + r_ch)) with (1 + (m * 2 ^ r_ch) * 2) by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ r_ch)). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_oc1 (r_ch : nat) {m : nat} {r r' : side}
  (hI : z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
  z2f false (5 + m * 4) (zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR r_ch WV) r').
Proof.
  intros w hs hN; inversion hN as [| n | |]; subst w hs; try lia.
  cbn [Str_app].
  assert (hn : n = 1 + (1 + m * 2)) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d1 (bt^^r_ch)).
  assert (h_seg : Seg ([cp] ++ [ch]^^(1 + (1 + m * 2))) ([ch; cp] ++ [ch]^^(m * 2 ^ r_ch))
                      ((d1 ++ d0)^^r_ch ++ [1; 1]%sym) (d1 ++ bt^^r_ch)).
  { pose proof (zOdd_base r_ch) as h1.
    pose proof (zS0 (zH_d0_odd m) (zT_pow r_ch m)) as h2.
    cbn [Nat.add lpow app] in h1, h2 |- *.
    exact (zSg h1 h2). }
  eapply zSc; [exact h_seg |].
  assert (h_num : Num true (1 + m * 2 ^ (1 + r_ch)) d0 ([ch; cp] ++ [ch]^^(m * 2 ^ r_ch))).
  { replace (1 + m * 2 ^ (1 + r_ch)) with (1 + (m * 2 ^ r_ch) * 2) by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ r_ch)). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_ec (r_ch : nat) {m : nat} {r r' : side}
  (hI : z2f true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) r r') :
  z2f false (6 + m * 2) (d0 *> zTs (zQK r_ch [WV]) r) (zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN; inversion hN as [| | n |]; subst w hs; try lia.
  cbn [Str_app].
  assert (hn : n = 1 + (1 + m)) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 ((d1 ++ d0)^^r_ch ++ [1; 1]%sym)).
  assert (h_seg : Seg ([cj] ++ [ch]^^(1 + (1 + m))) ([ch; cp] ++ [ch]^^((1 + m * 2) * 2 ^ r_ch))
                      (d0 ++ ((d1 ++ d0)^^r_ch ++ [1; 1]%sym)) (bt^^(1 + r_ch))).
  { pose proof (zEven_base r_ch) as h1.
    pose proof (zT_pow (1 + r_ch) m) as h2.
    pose proof (zSg h1 h2) as h3.
    rewrite <- app_assoc in h3.
    rewrite <- lpow_add in h3.
    replace (2 ^ r_ch + m * 2 ^ (1 + r_ch)) with ((1 + m * 2) * 2 ^ r_ch) in h3
      by (cbn [Nat.add Nat.pow]; lia).
    exact h3. }
  eapply zSc; [exact h_seg |].
  assert (h_num : Num true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) d0 ([ch; cp] ++ [ch]^^((1 + m * 2) * 2 ^ r_ch))).
  { replace (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) with (1 + ((1 + m * 2) * 2 ^ r_ch) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift ((1 + m * 2) * 2 ^ r_ch)). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_sp0 {n : nat} {r r' : side}
  (hI : z2f false (n * 2) r r') : z2f true (1 + n) (d0 *> r) (bt *> r').
Proof.
  intros w hs hN; inversion hN as [| | | m]; subst w hs; try lia.
  assert (hn : n = m * 2) by lia; subst n.
  rewrite <- Str_app_assoc.
  destruct m as [| m].
  - cbn [Nat.mul] in hI.
    rewrite (z2g hI), <- Str_app_assoc.
    pose proof (zSg (zS0 zH0 (z0a d0)) z0e) as h_seg.
    cbn [lpow app] in h_seg |- *.
    exact (zSc h_seg (Side_nil r)).
  - replace (S m) with (1 + m) in hI |- * by lia.
    pose proof (zSg (zS0 zH0 (z0a d0)) (z0o m)) as h_seg.
    cbn [app] in h_seg |- *.
    eapply zSc; [exact h_seg |].
    assert (hN2 : Num false ((1 + m) * 2 * 2) [] ([cj] ++ [ch]^^(1 + m * 2))).
    { replace ((1 + m) * 2 * 2) with (2 + (1 + m * 2) * 2) by lia.
      exact (Num_even (1 + m * 2)). }
    exact (hI [] _ hN2).
Qed.

Lemma z2_sp1 {n : nat} {r r' : side}
  (hI : z2f false (1 + n * 2) r r') : z2f true (1 + n) (d1 *> r) (bt *> r').
Proof.
  intros w hs hN; inversion hN as [| | | m]; subst w hs; try lia.
  assert (hn : n = m * 2) by lia; subst n.
  rewrite <- Str_app_assoc.
  pose proof (zSg (zS0 zH0 (z0a d1)) (z0q m)) as h_seg.
  cbn [app] in h_seg |- *.
  eapply zSc; [exact h_seg |].
  assert (hN1 : Num false (1 + m * 2 * 2) [] ([cp] ++ [ch]^^(m * 2))).
  { replace (1 + m * 2 * 2) with (1 + (m * 2) * 2) by lia.
    exact (Num_odd (m * 2)). }
  exact (hI [] _ hN1).
Qed.

Lemma z2_sc0 (r_ch : nat) {m : nat} {r r' : side}
  (hI : z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
  z2f true (3 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d0 *> zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN; inversion hN as [| | | n]; subst w hs; try lia.
  assert (hn : n = 1 + m * 2) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d0 (bt^^(1 + r_ch))).
  assert (h_in : d0 *> (d0 *> (((d1 ++ d0)^^r_ch ++ [1; 1]%sym) *> (d0 *> r))) =
                 (d0 ++ (d0 ++ ((d1 ++ d0)^^r_ch ++ [1; 1]%sym))) *> (d0 *> r)).
  { rewrite !Str_app_assoc; reflexivity. }
  rewrite h_in.
  assert (h_seg : Seg ([ch; cp] ++ [ch]^^(1 + m * 2)) ([ch; cp] ++ [ch]^^(m * 2 ^ (1 + r_ch)))
                      (d0 ++ (d0 ++ ((d1 ++ d0)^^r_ch ++ [1; 1]%sym))) (d0 ++ bt^^(1 + r_ch))).
  { pose proof (zS0 zH0 (z0a (d0 ++ ((d1 ++ d0)^^r_ch ++ [1; 1]%sym)))) as h0.
    pose proof (zOdd_base (1 + r_ch)) as h1.
    pose proof (zS0 (zH_d0_even m) (zT_pow (1 + r_ch) m)) as h2.
    cbn [Nat.add lpow app] in h0, h1, h2 |- *.
    rewrite !app_assoc in h0, h1 |- *.
    exact (zSg h0 (zSg h1 h2)). }
  eapply zSc; [exact h_seg |].
  assert (h_num : Num true (1 + m * 2 ^ (2 + r_ch)) d0 ([ch; cp] ++ [ch]^^(m * 2 ^ (1 + r_ch)))).
  { replace (1 + m * 2 ^ (2 + r_ch)) with (1 + (m * 2 ^ (1 + r_ch)) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ (1 + r_ch))). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2_sc1 (r_ch : nat) {m : nat} {r r' : side}
  (hI : z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
  z2f true (5 + m * 4) (d0 *> zTs (zQK r_ch [WV]) r) (d1 *> zTs (zR (1 + r_ch) WV) r').
Proof.
  intros w hs hN; inversion hN as [| | | n]; subst w hs; try lia.
  assert (hn : n = 1 + (1 + m * 2)) by lia; subst n.
  rewrite zTs_QK, zTs_R, <- (Str_app_assoc d1 (bt^^(1 + r_ch))).
  assert (h_in : d0 *> (d0 *> (((d1 ++ d0)^^r_ch ++ [1; 1]%sym) *> (d0 *> r))) =
                 (d0 ++ (d0 ++ ((d1 ++ d0)^^r_ch ++ [1; 1]%sym))) *> (d0 *> r)).
  { rewrite !Str_app_assoc; reflexivity. }
  rewrite h_in.
  assert (h_seg : Seg ([ch; cp] ++ [ch]^^(1 + (1 + m * 2))) ([ch; cp] ++ [ch]^^(m * 2 ^ (1 + r_ch)))
                      (d0 ++ (d0 ++ ((d1 ++ d0)^^r_ch ++ [1; 1]%sym))) (d1 ++ bt^^(1 + r_ch))).
  { pose proof (zS0 zH0 (z0a (d0 ++ ((d1 ++ d0)^^r_ch ++ [1; 1]%sym)))) as h0.
    pose proof (zOdd_base (1 + r_ch)) as h1.
    pose proof (zS0 (zH_d0_odd m) (zT_pow (1 + r_ch) m)) as h2.
    cbn [Nat.add lpow app] in h0, h1, h2 |- *.
    rewrite !app_assoc in h0, h1 |- *.
    exact (zSg h0 (zSg h1 h2)). }
  eapply zSc; [exact h_seg |].
  assert (h_num : Num true (1 + m * 2 ^ (2 + r_ch)) d0 ([ch; cp] ++ [ch]^^(m * 2 ^ (1 + r_ch)))).
  { replace (1 + m * 2 ^ (2 + r_ch)) with (1 + (m * 2 ^ (1 + r_ch)) * 2)
      by (cbn [Nat.add Nat.pow]; lia).
    exact (Num_shift (m * 2 ^ (1 + r_ch))). }
  exact (hI d0 _ h_num).
Qed.

Lemma z2o {s : bool} {k : nat} {r r' : side} (hI : BRIncs s k r r') :
  z2f s k r r'.
Proof.
  induction hI.
  - intros w hs hN; inversion hN; subst; try lia.
    constructor.
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
  zCf r ==>+ zCf (zTs [WV; WV; WQ; WV] r').
Proof.
  pose proof (z2o hI [] ([cj] ++ [ch]^^63) (Num_even 63)) as hC.
  cbn [Str_app] in hC.
  pose proof (zW_full hC) as hW.
  assert (heq : (bt ++ bt ++ d1 ++ bt) *> r' = zTs [WV; WV; WQ; WV] r') by reflexivity.
  rewrite heq in hW.
  exact hW.
Qed.

Inductive Binary : nat -> nat -> side -> Prop :=
  | Binary_one : Binary 1 1 (d1 *> 0inf%sym)
  | Binary_zero {n H : nat} {r : side} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 *> r)
  | Binary_two {n H : nat} {r : side} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 *> r).

Notation zPp := TM1.zPp.

Notation zP2 := TM1.zP2.

Notation z0F := TM1.z0F.

Lemma z0H {A H : nat} {r : side} (h : Binary A H r) :
  BRIncs false ((A - 1) * 2) 0inf%sym r.
Proof.
  induction h as [| n H r _ IH | n H r _ IH].
  - cbn [Nat.sub Nat.mul].
    assert (hd : d1 *> 0inf%sym = one *> 0inf%sym).
    { unfold d1, one; cbn; rewrite <- const_unfold; reflexivity. }
    rewrite hd; exact (BRIncs_zero 0inf%sym).
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
  inverts h as hu; [exact (zPr_nil true) | exact (zPr_T true hu)
                   | exact (zPr_pair0 true hu) | exact (zPr_pair1 true hu)].
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
Proof. inverts h. Qed.

Lemma zD0 {A H : nat} {u : zW} (h : zDg A H (WK :: u)) :
  exists A' H', zDg A' H' u /\ A = A' * 2 /\ H = 1 + H'.
Proof. inverts h as hD; exists A0, H0; auto. Qed.

Lemma zD1 {A H : nat} {u : zW} (h : zDg A H (WQ :: u)) :
  exists A' H', zDg A' H' u /\ A = 1 + A' * 2 /\ H = 1 + H'.
Proof. inverts h as hD; exists A0, H0; auto. Qed.

Lemma z0T (H : nat) : forall A, A < 2 ^ H -> exists u, zDg A H u.
Proof.
  induction H as [| H IH]; intros A hA.
  - cbn in hA; assert (A = 0) by lia; subst A; exists (@nil Word); exact zDg_nil.
  - cbn [Nat.pow] in hA.
    destruct (z0F A) as [[a ->] | [a ->]].
    + destruct (IH a ltac:(lia)) as [u hI].
      exists (WK :: u); exact (zDg_zero hI).
    + destruct (IH a ltac:(lia)) as [u hI].
      exists (WQ :: u); exact (zDg_one hI).
Qed.

Lemma z0U {A H : nat} {u : zW} (h1 : zDg A H u) :
  forall {B J : nat} {v : zW}, zDg B J v -> zDg (A + B * 2 ^ H) (H + J) (u ++ v).
Proof.
  induction h1 as [| A H u _ IH | A H u _ IH]; intros B J v h2.
  - cbn [Nat.add Nat.pow Nat.mul app].
    replace (B * 1) with B by lia; exact h2.
  - pose proof (zDg_zero (IH _ _ _ h2)) as h3.
    cbn [Nat.add Nat.pow app] in h3 |- *.
    replace ((A + B * 2 ^ H) * 2) with (A * 2 + B * (2 * 2 ^ H)) in h3 by lia.
    exact h3.
  - pose proof (zDg_one (IH _ _ _ h2)) as h3.
    cbn [Nat.add Nat.pow app] in h3 |- *.
    replace ((A + B * 2 ^ H) * 2) with (A * 2 + B * (2 * 2 ^ H)) in h3 by lia.
    exact h3.
Qed.

Lemma z0W_lt {A H : nat} {u : zW} (h : zDg A H u) : A < 2 ^ H.
Proof. induction h; cbn [Nat.add Nat.pow]; lia. Qed.

Lemma z0X {A H : nat} {u : zW} (h1 : zDg A H u) :
  forall {v : zW}, zDg A H v -> u = v.
Proof.
  induction h1 as [| A H u _ IH | A H u _ IH]; intros v h2.
  - inverts h2; try lia; reflexivity.
  - inverts h2 as hD; try lia.
    assert (A = A0) by lia; subst A0.
    f_equal; exact (IH _ hD).
  - inverts h2 as hD; try lia.
    assert (A = A0) by lia; subst A0.
    f_equal; exact (IH _ hD).
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
  destruct w; cbn [app z0L]; try exact IH.
  destruct u as [| w2 u'].
  - destruct v as [| w2 v']; [discriminate |].
    destruct w2; cbn [app z0L] in *; [exact h | reflexivity | reflexivity].
  - destruct w2; [exact IH | reflexivity | reflexivity].
Qed.

Lemma zDg_pos_z0L {A H : nat} {w : zW} (hD : zDg A H w) (hPos : 0 < A) :
  z0L (w ++ [WK]) = true.
Proof.
  induction hD as [| A1 H1 u1 _ IH | A1 H1 u1 hDu _]; [lia | exact (IH ltac:(lia)) |].
  destruct hDu; reflexivity.
Qed.

Notation Rat := QArith_base.Q.

Notation Q_of_nat := TM2.Q_of_nat.

Definition Q_of_N (n : N) : Rat := inject_Z (Z.of_N n).

Notation Q_of_nat_0 := TM2.Q_of_nat_0.

Notation Q_of_nat_1 := TM2.Q_of_nat_1.

Notation Q_of_nat_2 := TM2.Q_of_nat_2.

Notation Q_of_nat_3 := TM2.Q_of_nat_3.

Notation Q_of_nat_4 := TM2.Q_of_nat_4.

Notation Q_of_nat_5 := TM2.Q_of_nat_5.

Notation Q_of_nat_6 := TM2.Q_of_nat_6.

Notation Q_of_nat_8 := TM2.Q_of_nat_8.

Lemma Q_of_nat_16 : (Q_of_nat 16 == 16)%Q. Proof. reflexivity. Qed.

Lemma Q_of_nat_128 : (Q_of_nat 128 == 128)%Q. Proof. reflexivity. Qed.

Notation Q_of_nat_add := TM2.Q_of_nat_add.

Notation Q_of_nat_mul := TM2.Q_of_nat_mul.

Notation Q_of_nat_S := TM2.Q_of_nat_S.

Ltac push_Q_of_nat :=
  repeat (rewrite Q_of_nat_add in * || rewrite Q_of_nat_mul in *);
  repeat (rewrite Q_of_nat_128 in * || rewrite Q_of_nat_16 in * ||
          rewrite Q_of_nat_8 in * || rewrite Q_of_nat_6 in * ||
          rewrite Q_of_nat_5 in * || rewrite Q_of_nat_4 in * ||
          rewrite Q_of_nat_3 in * || rewrite Q_of_nat_2 in * ||
          rewrite Q_of_nat_1 in * || rewrite Q_of_nat_0 in *);
  repeat (rewrite Q_of_nat_S in *;
          try rewrite Q_of_nat_0 in *; try rewrite Q_of_nat_1 in *).

Notation Q_of_nat_le := TM2.Q_of_nat_le.

Notation Q_of_nat_lt := TM2.Q_of_nat_lt.

Lemma Q_of_nat_eq (a b : nat) : a = b <-> (Q_of_nat a == Q_of_nat b)%Q.
Proof. unfold Q_of_nat, Qeq; cbn; lia. Qed.

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
  induction h as [| A H u _ IH | A H u _ IH].
  - cbn; push_Q_of_nat; lra.
  - rewrite zP2; cbn [z11 z0Y z10]; push_Q_of_nat; lra.
  - rewrite zP2; cbn [z11 z0Y z10]; push_Q_of_nat; lra.
Qed.

Lemma z17 {A H : nat} {u : zW} (h : zDg A H u) :
  z0Z u + Q_of_nat A + 1 == Q_of_nat (2 ^ H).
Proof.
  pose proof (zDw h); pose proof (z12 u); lra.
Qed.

Fixpoint zHn (u : zW) (h : nat) : option nat :=
  match u, h with
  | [], _ => Some h
  | WV :: u', _ => zHn u' (h + 1)%nat
  | _ :: _, 0%nat => None
  | _ :: u', S h' => zHn u' h'
  end.

Lemma z1x (u : zW) :
  forall (h H : nat), zHn u h = Some H ->
    z11 u * Q_of_nat (2 ^ H) == Q_of_nat (2 ^ h).
Proof.
  induction u as [| w u IH]; intros h H hE.
  - inversion hE; subst H; cbn [z11]; lra.
  - destruct w.
    + cbn [zHn z11] in hE |- *.
      pose proof (IH (h + 1)%nat H hE) as hIH.
      replace (2 ^ (h + 1))%nat with (2 ^ h * 2)%nat in hIH by (rewrite Nat.pow_add_r; cbn; lia).
      push_Q_of_nat; lra.
    + destruct h as [| h]; [discriminate |].
      cbn [zHn z11] in hE |- *.
      pose proof (IH h H hE) as hIH.
      replace (2 ^ S h)%nat with (2 * 2 ^ h)%nat by reflexivity.
      push_Q_of_nat; lra.
    + destruct h as [| h]; [discriminate |].
      cbn [zHn z11] in hE |- *.
      pose proof (IH h H hE) as hIH.
      replace (2 ^ S h)%nat with (2 * 2 ^ h)%nat by reflexivity.
      push_Q_of_nat; lra.
Qed.

Lemma z1B (u : zW) :
  forall (h : nat), z0Y u < Q_of_nat (2 ^ h) -> exists H, zHn u h = Some H.
Proof.
  induction u as [| w u IH]; intros h hM.
  - exists h; reflexivity.
  - destruct w.
    + cbn [z0Y zHn] in hM |- *.
      apply IH.
      replace (2 ^ (h + 1))%nat with (2 ^ h * 2)%nat by (rewrite Nat.pow_add_r; cbn; lia).
      push_Q_of_nat; lra.
    + destruct h as [| h].
      * pose proof (proj1 (zWn u)); cbn [z0Y Nat.pow] in hM; push_Q_of_nat; lra.
      * cbn [z0Y zHn] in hM |- *.
        apply IH.
        replace (2 ^ S h)%nat with (2 * 2 ^ h)%nat in hM by reflexivity.
        push_Q_of_nat; lra.
    + destruct h as [| h].
      * pose proof (proj1 (zWn u)); cbn [z0Y Nat.pow] in hM; push_Q_of_nat; lra.
      * cbn [z0Y zHn] in hM |- *.
        apply IH.
        replace (2 ^ S h)%nat with (2 * 2 ^ h)%nat in hM by reflexivity.
        push_Q_of_nat; lra.
Qed.

Lemma z1K {n H : nat} {ds : zW} (hD : zDg (1 + n * 4) H ds) (hH : (2 <= H)%nat) :
  exists w, ds = WQ :: WK :: w.
Proof.
  inverts hD as hD1; try lia.
  assert (A = (n * 2)%nat) by lia; subst A.
  inverts hD1 as hD2; try lia.
  eexists; reflexivity.
Qed.

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
    (z0Y u + z0Z u) * 2 < Q_of_nat k ->
    exists b v l, Scan k u b v l /\ (0 < b)%nat.
Proof.
  induction hI as [e | e u _ IH | u _ IH | u _ IH | e u _ IH | e u _ IH]; intros k hEk hk.
  - cbn [z0Y z0Z] in hk.
    assert (hk_nat : (0 < k)%nat) by (apply Q_of_nat_lt; push_Q_of_nat; lra).
    exists k, (@nil Word), 0; split; [exact (Scan_nil k) | exact hk_nat].
  - pose proof (zWn u) as hw; cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [push_Q_of_nat; lra |].
    replace (S k) with (1 + k)%nat in * by lia.
    destruct (IH ((1 + k) * 2)%nat (fun _ => ex_intro _ (1 + k)%nat eq_refl)
                 ltac:(push_Q_of_nat; lra)) as [b [v [l [hS hB]]]].
    exists b, (WV :: v), (l * (1#2)); split; [exact (Scan_T hS) | exact hB].
  - pose proof (zWn u) as hw; cbn [z0Y z0Z] in hk.
    destruct (hEk eq_refl) as [n ->].
    destruct (z0F n) as [[a ->] | [a ->]].
    + destruct a as [| a]; [push_Q_of_nat; lra |].
      replace (S a) with (a + 1)%nat in * by lia.
      destruct (IH (a * 2)%nat (fun _ => ex_intro _ a eq_refl)
                   ltac:(push_Q_of_nat; lra)) as [b [v [l [hS hB]]]].
      exists b, (WQ :: v), (1 + l * 2); split; [| exact hB].
      replace ((a + 1) * 2 * 2)%nat with (4 + a * 4)%nat by lia.
      exact (Scan_short10 hS).
    + destruct (IH (a * 2)%nat (fun _ => ex_intro _ a eq_refl)
                   ltac:(push_Q_of_nat; lra)) as [b [v [l [hS hB]]]].
      exists b, (WK :: v), (1 + l * 2); split; [| exact hB].
      replace ((1 + a * 2) * 2)%nat with (2 + a * 4)%nat by lia.
      exact (Scan_short00 hS).
  - pose proof (zWn u) as hw; cbn [z0Y z0Z] in hk.
    destruct (hEk eq_refl) as [n ->].
    destruct (z0F n) as [[a ->] | [a ->]].
    + destruct a as [| a]; [push_Q_of_nat; lra |].
      replace (S a) with (a + 1)%nat in * by lia.
      destruct (IH (1 + a * 2)%nat (fun h => ltac:(discriminate h))
                   ltac:(push_Q_of_nat; lra)) as [b [v [l [hS hB]]]].
      exists b, (WQ :: v), (l * 2); split; [| exact hB].
      replace ((a + 1) * 2 * 2)%nat with (4 + a * 4)%nat by lia.
      exact (Scan_short11 hS).
    + destruct (IH (1 + a * 2)%nat (fun h => ltac:(discriminate h))
                   ltac:(push_Q_of_nat; lra)) as [b [v [l [hS hB]]]].
      exists b, (WK :: v), (l * 2); split; [| exact hB].
      replace ((1 + a * 2) * 2)%nat with (2 + a * 4)%nat by lia.
      exact (Scan_short01 hS).
  - pose proof (zWn u) as hw; cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [push_Q_of_nat; lra |].
    replace (S k) with (1 + k)%nat in * by lia.
    destruct (IH (k * 2)%nat (fun _ => ex_intro _ k eq_refl)
                 ltac:(push_Q_of_nat; lra)) as [b [v [l [hS hB]]]].
    exists b, (WV :: v), ((1 + l) * (1#2)); split; [exact (Scan_pair0 hS) | exact hB].
  - pose proof (zWn u) as hw; cbn [z0Y z0Z] in hk.
    destruct k as [| k]; [push_Q_of_nat; lra |].
    replace (S k) with (1 + k)%nat in * by lia.
    destruct (IH (1 + k * 2)%nat (fun h => ltac:(discriminate h))
                 ltac:(push_Q_of_nat; lra)) as [b [v [l [hS hB]]]].
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
  intros h; remember (1 + n * 2)%nat as a eqn:ha; inverts h; lia.
Qed.

Lemma zSo (r : nat) :
  forall (n b : nat) (v : zW) (l : Rat),
    ~ Scan (1 + n * 2) (zR (r * 2) WQ ++ [WK]) b v l.
Proof.
  induction r as [| r IH]; intros n b v l hI.
  - exact (zSz n [] b v l hI).
  - replace (S r * 2)%nat with (2 + r * 2)%nat in hI by lia.
    cbn [Nat.add zR repeat app] in hI.
    remember (1 + n * 2)%nat as a eqn:ha.
    inverts hI as hJ; try lia.
    exact (IH _ _ _ _ hJ).
Qed.

Lemma zS1 (r : nat) :
  forall (a b : nat) (v : zW) (l : Rat),
    Scan a (zR (1 + r * 2) WQ ++ [WK]) b v l ->
    v = zR (1 + r) WV /\ b = ((a - 1) * 2 ^ (1 + r))%nat /\ l == (1#2).
Proof.
  induction r as [| r IH]; intros a b v l hI.
  - cbn [Nat.mul Nat.add zR repeat app] in hI.
    inverts hI as hJ;
      [ inverts hJ; split; [reflexivity | split; [cbn; lia | lra]]
      | exfalso; exact (zSz _ [] _ _ _ hJ)
      | exfalso; exact (zSz _ [] _ _ _ hJ) ].
  - replace (1 + S r * 2)%nat with (2 + (1 + r * 2))%nat in hI by lia.
    cbn [Nat.add zR repeat app] in hI.
    inverts hI as hJ.
    + destruct (IH _ _ _ _ hJ) as [-> [-> hl]].
      split; [reflexivity | split; [| lra]].
      cbn [Nat.add Nat.sub Nat.pow]; lia.
    + pose proof (zSo (S r) n) as hSo.
      replace (S r * 2)%nat with (2 + r * 2)%nat in hSo by lia.
      exfalso; eapply hSo; exact hJ.
    + pose proof (zSo (S r) n) as hSo.
      replace (S r * 2)%nat with (2 + r * 2)%nat in hSo by lia.
      exfalso; eapply hSo; exact hJ.
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
  inverts h as hJ; [left; auto | right; eexists; split; [exact hJ | reflexivity]].
Qed.

Lemma zTo {u : zW} {z : Rat} (h : zTd (WQ :: u) z) :
  exists y, zTd u y /\ z = y * 2.
Proof.
  inverts h as hJ; eexists; split; [exact hJ | reflexivity].
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
    (forall n : nat, a = (1 + n * 2)%nat -> z0Y v <= z * 2 /\ l <= (1#2) + z * 2).
Proof.
  induction h as [k | n u k v l hI IH | n u k v l hI IH | n u k v l hI IH
                  | n u k v l hI IH | n u k v l hI IH | n u k v l hI IH | n u k v l hI IH];
    intros z hZ.
  - inverts hZ.
  - inverts hZ.
  - destruct (zTo hZ) as [y [hJ ->]].
    destruct (z1f hJ) as [[-> ->] | [x [hJ' ->]]].
    + inverts hI; cbn [z0Y]; split; [lra | split; [lra | intros; split; lra]].
    + destruct (IH _ hJ') as [hM [hL _]].
      pose proof (z1e hJ') as hx.
      cbn [z0Y]; split; [lra | split; [lra | intros; split; lra]].
  - destruct (zTo hZ) as [y [hJ ->]].
    destruct (zTo hJ) as [x [hJ' ->]].
    destruct (IH _ hJ') as [_ [_ hOdd]].
    destruct (hOdd n eq_refl) as [hM hL].
    pose proof (z1e hJ') as hx.
    cbn [z0Y]; split; [lra | split; [lra | intros; split; lra]].
  - destruct (z1f hZ) as [[-> ->] | [x [hJ ->]]].
    + inverts hI; cbn [z0Y]; split; [lra | split; [lra | intros m hm; lia]].
    + destruct (IH _ hJ) as [hM [hL _]]; cbn [z0Y]; split; [lra | split; [lra | intros m hm; lia]].
  - destruct (zTo hZ) as [x [hJ ->]].
    destruct (IH _ hJ) as [_ [_ hOdd]].
    destruct (hOdd n eq_refl) as [hM hL].
    cbn [z0Y]; split; [lra | split; [lra | intros m hm; lia]].
  - destruct (z1f hZ) as [[-> ->] | [x [hJ ->]]].
    + inverts hI; cbn [z0Y]; split; [lra | split; [lra | intros m hm; lia]].
    + destruct (IH _ hJ) as [hM [hL _]]; cbn [z0Y]; split; [lra | split; [lra | intros m hm; lia]].
  - destruct (zTo hZ) as [x [hJ ->]].
    destruct (IH _ hJ) as [_ [_ hOdd]].
    destruct (hOdd n eq_refl) as [hM hL].
    cbn [z0Y]; split; [lra | split; [lra | intros m hm; lia]].
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
        remember (1 + n * 2)%nat as a eqn:ha.
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
  - destruct w0; discriminate.
  - destruct w0 as [| t0 w']; [discriminate |].
    cbn [app] in hu; inversion hu; subst t0 u0.
    destruct (IH w' eq_refl) as [h1 [h2 [[m hm] [vp ->]]]].
    split; [cbn [z11]; lra | split; [intros hL; pose proof (h2 hL); cbn [z11]; lra |]].
    split; [exists m; exact hm | exists (WV :: vp); reflexivity].
  - destruct w0 as [| t0 [| t1 w']]; [discriminate | destruct t0; discriminate |].
    cbn [app] in hu; inversion hu; subst t0 t1 u0.
    destruct (IH w' eq_refl) as [h1 [_ [[m hm] [vp ->]]]].
    pose proof (zSp (w' ++ [WQ; WQ; WK])) as hp.
    split; [cbn [z11]; lra | split; [intros _; cbn [z11]; lra |]].
    split; [exists m; exact hm | exists (WV :: vp); reflexivity].
  - destruct w0 as [| t0 [| t1 w']].
    + cbn [app] in hu; inversion hu; subst u0.
      exfalso; exact (zSz n [] k v0 l0 hSub).
    + cbn [app] in hu; inversion hu; subst t0 u0.
      destruct (zS1 0 (1 + n * 2) k v0 l0 hSub) as [-> [hk _]].
      split; [cbn [Nat.add zR repeat z11]; lra | split; [intros _; cbn [Nat.add zR repeat z11]; lra |]].
      split; [exists n; cbn in hk; lia | exists [WV]; reflexivity].
    + cbn [app] in hu; inversion hu; subst t0 t1 u0.
      destruct (IH w' eq_refl) as [h1 [_ [[m hm] [vp ->]]]].
      pose proof (zSp (w' ++ [WQ; WQ; WK])) as hp.
      split; [cbn [z11]; lra | split; [intros _; cbn [z11]; lra |]].
      split; [exists m; exact hm | exists (WV :: vp); reflexivity].
  - destruct w0 as [| t0 w']; [discriminate |].
    cbn [app] in hu; inversion hu; subst t0 u0.
    destruct (IH w' eq_refl) as [h1 [h2 [[m hm] [vp ->]]]].
    split; [cbn [z11]; lra | split; [intros hL; pose proof (h2 hL); cbn [z11]; lra |]].
    split; [exists m; exact hm | exists (WK :: vp); reflexivity].
  - destruct w0 as [| t0 w'].
    + cbn [app] in hu; inversion hu; subst u0.
      destruct (zS1 0 (1 + n * 2) k v0 l0 hSub) as [-> [hk _]].
      split; [cbn [Nat.add zR repeat z11]; lra | split; [intros hL; discriminate |]].
      split; [exists n; cbn in hk; lia | exists [WK]; reflexivity].
    + cbn [app] in hu; inversion hu; subst t0 u0.
      destruct (IH w' eq_refl) as [h1 [h2 [[m hm] [vp ->]]]].
      split; [cbn [z11]; lra | split; [intros hL; pose proof (h2 (z0L_odd_scan hSub hL)); cbn [z11]; lra |]].
      split; [exists m; exact hm | exists (WK :: vp); reflexivity].
  - destruct w0 as [| t0 w']; [discriminate |].
    cbn [app] in hu; inversion hu; subst t0 u0.
    destruct (IH w' eq_refl) as [h1 [h2 [[m hm] [vp ->]]]].
    split; [cbn [z11]; lra | split; [intros hL; pose proof (h2 hL); cbn [z11]; lra |]].
    split; [exists m; exact hm | exists (WQ :: vp); reflexivity].
  - destruct w0 as [| t0 w'].
    + cbn [app] in hu; inversion hu; subst u0.
      destruct (zS1 0 (1 + n * 2) k v0 l0 hSub) as [-> [hk _]].
      split; [cbn [Nat.add zR repeat z11]; lra | split; [intros hL; discriminate |]].
      split; [exists n; cbn in hk; lia | exists [WQ]; reflexivity].
    + cbn [app] in hu; inversion hu; subst t0 u0.
      destruct (IH w' eq_refl) as [h1 [h2 [[m hm] [vp ->]]]].
      split; [cbn [z11]; lra | split; [intros hL; pose proof (h2 (z0L_odd_scan hSub hL)); cbn [z11]; lra |]].
      split; [exists m; exact hm | exists (WQ :: vp); reflexivity].
Qed.

Fixpoint zIv (r : nat) : Rat :=
  match r with
  | 0%nat => 1
  | S r' => zIv r' * (1#2)
  end.

Fixpoint zP4 (r : nat) : Rat :=
  match r with
  | 0%nat => 1
  | S r' => zP4 r' * 4
  end.

Lemma zIv_P4 (r : nat) :
  0 < zIv r /\ zIv r <= 1 /\ 1 <= zP4 r /\ ((1 <= r)%nat -> 4 <= zP4 r /\ 8 * zIv r <= zP4 r).
Proof.
  induction r as [| r [h1 [h2 [h3 h4]]]].
  - cbn [zIv zP4]; split; [lra | split; [lra | split; [lra | intros; lia]]].
  - cbn [zIv zP4].
    destruct r as [| r'].
    + cbn [zIv zP4]; split; [lra | split; [lra | split; [lra | intros _; split; lra]]].
    + destruct (h4 ltac:(lia)) as [h4a h4b].
      split; [lra | split; [lra | split; [lra | intros _; split; lra]]].
Qed.

Lemma z11_R (r : nat) (u : zW) :
  z11 (zR r WV ++ u) == zIv r * z11 u.
Proof.
  induction r as [| r IH]; [cbn; lra |].
  cbn [zR repeat app z11 zIv]; rewrite IH; ring.
Qed.

Lemma z11_QK (r : nat) (u : zW) :
  z11 (zQK r u) == zP4 r * z11 u.
Proof.
  induction r as [| r IH]; [cbn; lra |].
  cbn [zQK z11 zP4]; rewrite IH; ring.
Qed.

Lemma z0W_R (r : nat) (u : zW) :
  z0W (zR r WV ++ u) == zIv r * z0W u.
Proof.
  induction r as [| r IH]; [cbn; lra |].
  cbn [zR repeat app z0W zIv]; rewrite IH; ring.
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
  Q_of_nat (2 ^ r) * zIv r == 1.
Proof.
  induction r as [| r IH]; [cbn; push_Q_of_nat; lra |].
  replace (2 ^ S r)%nat with (2 * 2 ^ r)%nat by reflexivity.
  cbn [zIv]; push_Q_of_nat; lra.
Qed.

Lemma zR_succ (r : nat) (v : zW) :
  zR (1 + r) WV ++ v = WV :: (zR r WV ++ v).
Proof. reflexivity. Qed.

Lemma z1i {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan s k u k' v a b) :
  Q_of_nat k - 3 == (Q_of_nat k' - 3) * z11 v + 2 * (a - b).
Proof.
  induction h as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                  | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                  | r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH
                  | n u k v a b _ IH | n u k v a b _ IH
                  | r m u k v a b _ IH | r m u k v a b _ IH].
  - cbn [z11]; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; rewrite z11_R.
    assert (hp : Q_of_nat (2 ^ (1 + r)) * zIv r == 2)
      by (pose proof (zIv_pow2 r); rewrite zP2; push_Q_of_nat; lra).
    assert (h_mul : ((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r == Q_of_nat m * 2 - 2 * zIv r).
    { rewrite <- IH; push_Q_of_nat.
      transitivity (Q_of_nat m * (Q_of_nat (2 ^ (1 + r)) * zIv r) - 2 * zIv r); [ring | rewrite hp; ring]. }
    push_Q_of_nat.
    transitivity ((((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r) * 2 + 4 * zIv r);
      [rewrite h_mul; ring | ring].
  - cbn [z11]; rewrite z11_R.
    assert (hp : Q_of_nat (2 ^ (1 + r)) * zIv r == 2)
      by (pose proof (zIv_pow2 r); rewrite zP2; push_Q_of_nat; lra).
    assert (h_mul : ((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r == Q_of_nat m * 2 - 2 * zIv r).
    { rewrite <- IH; push_Q_of_nat.
      transitivity (Q_of_nat m * (Q_of_nat (2 ^ (1 + r)) * zIv r) - 2 * zIv r); [ring | rewrite hp; ring]. }
    push_Q_of_nat.
    transitivity ((((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r) * 2 + 4 * zIv r + 2);
      [rewrite h_mul; ring | ring].
  - assert (hp : Q_of_nat (2 ^ (1 + r)) * zIv r == 2)
      by (pose proof (zIv_pow2 r); rewrite zP2; push_Q_of_nat; lra).
    assert (h_mul : ((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r == 2 + Q_of_nat m * 4 - 2 * zIv r).
    { rewrite <- IH; push_Q_of_nat.
      transitivity ((1 + Q_of_nat m * 2) * (Q_of_nat (2 ^ (1 + r)) * zIv r) - 2 * zIv r); [ring | rewrite hp; ring]. }
    rewrite zR_succ; cbn [z11]; rewrite z11_R; push_Q_of_nat.
    transitivity ((((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r) * (1#2) + zIv r + 2);
      [rewrite h_mul; ring | ring].
  - cbn [z11]; push_Q_of_nat; lra.
  - cbn [z11]; push_Q_of_nat; lra.
  - assert (hp : Q_of_nat (2 ^ (2 + r)) * zIv r == 4)
      by (pose proof (zIv_pow2 r); replace (2 + r)%nat with (1 + (1 + r))%nat by lia;
          rewrite (zP2 (1 + r)), (zP2 r); push_Q_of_nat; lra).
    assert (h_mul : ((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r == Q_of_nat m * 4 - 2 * zIv r).
    { rewrite <- IH; push_Q_of_nat.
      transitivity (Q_of_nat m * (Q_of_nat (2 ^ (2 + r)) * zIv r) - 2 * zIv r); [ring | rewrite hp; ring]. }
    cbn [z11]; rewrite zR_succ; cbn [z11]; rewrite z11_R; push_Q_of_nat.
    transitivity ((((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r) + 2 * zIv r);
      [rewrite h_mul; ring | ring].
  - assert (hp : Q_of_nat (2 ^ (2 + r)) * zIv r == 4)
      by (pose proof (zIv_pow2 r); replace (2 + r)%nat with (1 + (1 + r))%nat by lia;
          rewrite (zP2 (1 + r)), (zP2 r); push_Q_of_nat; lra).
    assert (h_mul : ((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r == Q_of_nat m * 4 - 2 * zIv r).
    { rewrite <- IH; push_Q_of_nat.
      transitivity (Q_of_nat m * (Q_of_nat (2 ^ (2 + r)) * zIv r) - 2 * zIv r); [ring | rewrite hp; ring]. }
    cbn [z11]; rewrite zR_succ; cbn [z11]; rewrite z11_R; push_Q_of_nat.
    transitivity ((((Q_of_nat k - 3) * z11 v + 2 * (a - b)) * zIv r) + 2 * zIv r + 2);
      [rewrite h_mul; ring | ring].
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
  induction h as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                  | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                  | r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH
                  | n u k v a b _ IH | n u k v a b _ IH
                  | r m u k v a b _ IH | r m u k v a b _ IH].
  - split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [intros _; cbn [z0W]; lra | split; [discriminate | discriminate]].
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [| split; [discriminate | discriminate]].
    intros _; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r']; [cbn [zIv zP4]; lra |].
    destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
    destruct (hge1 ltac:(lia)) as [hp4_4 _].
    split; [clear - h1 hw hiv1 hiv2 hp4 hp4_4; nra
           | split; [clear - h2 hw hiv1 hiv2 hp4 hp4_4; nra
                    | clear - h3 hw hiv1 hiv2 hp4 hp4_4; nra]].
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [| split; [discriminate | discriminate]].
    intros _; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r']; [cbn [zIv zP4]; lra |].
    destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
    destruct (hge1 ltac:(lia)) as [hp4_4 _].
    split; [clear - h1 hw hiv1 hiv2 hp4 hp4_4; nra
           | split; [clear - h2 hw hiv1 hiv2 hp4 hp4_4; nra
                    | clear - h3 hw hiv1 hiv2 hp4 hp4_4; nra]].
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [| split; [discriminate | discriminate]].
    intros _; rewrite zR_succ; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]].
    split; [clear - h1 hw hiv1 hiv2 hp4; nra
           | split; [clear - h2 hw hiv1 hiv2 hp4; nra
                    | clear - h3 hw hiv1 hiv2 hp4; nra]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [discriminate | split; [intros _; cbn [z0W]; lra | intros _ _; cbn [z0W]; lra]].
  - destruct (proj1 IH eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [discriminate | split; [intros _; cbn [z0W]; lra | intros _ _; cbn [z0W]; lra]].
  - assert (hdiv : exists m' : nat, (1 + m * 2 ^ (2 + r))%nat = (1 + m' * 4)%nat).
    { exists (m * 2 ^ r)%nat; cbn [Nat.add Nat.pow]; lia. }
    destruct (proj1 (proj2 IH) eq_refl) as [_ [h2 h3]].
    pose proof (proj2 (proj2 IH) eq_refl hdiv) as h1.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [discriminate | split; [| intros _ [q hq]; lia]].
    intros _; cbn [z0W]; rewrite zR_succ; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
    destruct r as [| r']; [cbn [zIv zP4]; lra |].
    destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
    destruct (hge1 ltac:(lia)) as [hp4_4 _].
    split; [clear - h1 hw hiv1 hiv2 hp4 hp4_4; nra
           | split; [clear - h2 hw hiv1 hiv2 hp4 hp4_4; nra
                    | clear - h3 hw hiv1 hiv2 hp4 hp4_4; nra]].
  - destruct (proj1 (proj2 IH) eq_refl) as [h1 [h2 h3]]; pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    split; [discriminate | split; intros _].
    + cbn [z0W]; rewrite zR_succ; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
      destruct r as [| r']; [cbn [zIv zP4]; lra |].
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [hp4_4 _].
      split; [clear - h1 hw hiv1 hiv2 hp4 hp4_4; nra
             | split; [clear - h2 hw hiv1 hiv2 hp4 hp4_4; nra
                      | clear - h3 hw hiv1 hiv2 hp4 hp4_4; nra]].
    + intros _.
      cbn [z0W]; rewrite zR_succ; cbn [z0W]; rewrite z0W_R, z0W_QK; cbn [z0W].
      destruct r as [| r']; [cbn [zIv zP4]; lra |].
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [hp4_4 _].
      clear - h1 hw hiv1 hiv2 hp4 hp4_4; nra.
Qed.

Lemma z1k {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h1 : BScan s k u k' v a b) :
  forall {w : zW} {k'' : nat} {x : zW} {c d : Rat},
    BScan false k' w k'' x c d ->
    exists a' b', BScan s k (u ++ w) k'' (v ++ x) a' b' /\
      a' == a + z11 v * c /\ b' == b + z11 v * d.
Proof.
  induction h1 as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                   | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                   | r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH
                   | n u k v a b _ IH | n u k v a b _ IH
                   | r m u k v a b _ IH | r m u k v a b _ IH];
    intros w k'' x c d h2.
  - exists c, d; split; [exact h2 | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), (b' * (1#2)); split; [exact (BScan_T hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#4) + b' * (1#2)); split; [exact (BScan_pair0 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#2) + b' * (1#2)); split; [exact (BScan_pair1 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((5#2) + a' * 2), (b' * 2); split; [exact (BScan_short00 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((3#2) + a' * 2), (b' * 2); split; [exact (BScan_short01 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((7#2) + a' * 2), (b' * 2); split; [exact (BScan_short10 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((5#2) + a' * 2), (b' * 2); split; [exact (BScan_short11 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((2 + a' * 2) * zIv r), (b' * 2 * zIv r); split.
    + rewrite <- zQK_append; cbn [app]; rewrite <- app_assoc.
      exact (BScan_odd_chain0 r hK).
    + cbn [z11]; rewrite z11_R, hA, hB; split; ring.
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (2 + a' * 2) * zIv r), (b' * 2 * zIv r); split.
    + rewrite <- zQK_append; cbn [app]; rewrite <- app_assoc.
      exact (BScan_odd_chain1 r hK).
    + cbn [z11]; rewrite z11_R, hA, hB; split; ring.
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (1 + a') * (1#2) * zIv r), (b' * (1#2) * zIv r); split.
    + cbn [app]; rewrite <- zQK_append; cbn [app]; rewrite <- app_assoc.
      exact (BScan_even_chain r hK).
    + rewrite zR_succ; cbn [z11]; rewrite z11_R, hA, hB; split; ring.
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#4) + b' * (1#2)); split; [exact (BScan_shift_pair0 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (a' * (1#2)), ((1#2) + b' * (1#2)); split; [exact (BScan_shift_pair1 hK) | cbn [z11]; lra].
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists ((1 + a') * zIv r), (b' * zIv r); split.
    + cbn [app]; rewrite <- zQK_append; cbn [app]; rewrite <- app_assoc.
      exact (BScan_shift_chain0 r hK).
    + cbn [z11]; rewrite zR_succ; cbn [z11]; rewrite z11_R, hA, hB; split; ring.
  - destruct (IH _ _ _ _ _ h2) as [a' [b' [hK [hA hB]]]].
    exists (1 + (1 + a') * zIv r), (b' * zIv r); split.
    + cbn [app]; rewrite <- zQK_append; cbn [app]; rewrite <- app_assoc.
      exact (BScan_shift_chain1 r hK).
    + cbn [z11]; rewrite zR_succ; cbn [z11]; rewrite z11_R, hA, hB; split; ring.
Qed.

Lemma z1n {k : nat} {u : zW} {k' : nat} {v : zW} {l : Rat}
  (hI : Scan k u k' v l) :
  forall {A H : nat}, zDg A H u ->
    exists a b, BScan false k u k' v a b /\ a - b <= (5#2) * z0Y v + l /\ b - a <= 1.
Proof.
  induction hI as [k | n u k v l _ _ | n u k v l _ IH | n u k v l _ IH
                   | n u k v l _ IH | n u k v l _ IH | n u k v l _ IH | n u k v l _ IH];
    intros A H hD.
  - exists 0, 0; split; [exact (BScan_nil k) | cbn [z0Y]; lra].
  - exfalso; exact (z0K hD).
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (zD0 hD1) as [A2 [H2 [hD2 _]]].
    destruct (IH _ _ hD2) as [a [b [hJ [hP hM]]]].
    exists (a * (1#2)), ((1#4) + b * (1#2)); split; [exact (BScan_pair0 hJ) | cbn [z0Y]; lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (zD1 hD1) as [A2 [H2 [hD2 _]]].
    destruct (IH _ _ hD2) as [a [b [hJ [hP hM]]]].
    exists (a * (1#2)), ((1#2) + b * (1#2)); split; [exact (BScan_pair1 hJ) | cbn [z0Y]; lra].
  - destruct (zD0 hD) as [A1 [H1 [hD1 _]]].
    destruct (IH _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((5#2) + a * 2), (b * 2); split; [exact (BScan_short00 hJ) | cbn [z0Y]; lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (IH _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((3#2) + a * 2), (b * 2); split; [exact (BScan_short01 hJ) | cbn [z0Y]; lra].
  - destruct (zD0 hD) as [A1 [H1 [hD1 _]]].
    destruct (IH _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((7#2) + a * 2), (b * 2); split; [exact (BScan_short10 hJ) | cbn [z0Y]; lra].
  - destruct (zD1 hD) as [A1 [H1 [hD1 _]]].
    destruct (IH _ _ hD1) as [a [b [hJ [hP hM]]]].
    exists ((5#2) + a * 2), (b * 2); split; [exact (BScan_short11 hJ) | cbn [z0Y]; lra].
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
    by (rewrite z14; cbn [z0Z]; lra).
  pose proof (z0U hD_w (zDg_zero zDg_nil)) as hD_wk.
  destruct (z1n hS' hD_wk) as [a0 [b0 [hB0 [hAB0 hBA0]]]].
  rewrite <- app_assoc in hB0.
  exists (a0 * (1#2)), ((1#4) + b0 * (1#2)).
  split; [exact (BScan_pair0 hB0) |].
  cbn [z0Y z0Z]; lra.
Qed.

Notation zSwt := TM1.zSwt.

Lemma z1p_upper {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan s k u k' v a b) :
  z11 v <= zSwt s * z11 u.
Proof.
  induction h as [k | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                  | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH | n u k v a b _ IH
                  | r m u k v a b _ IH | r m u k v a b _ IH | r m u k v a b _ IH
                  | n u k v a b _ IH | n u k v a b _ IH
                  | r m u k v a b _ IH | r m u k v a b _ IH].
  - cbn [z11 zSwt]; lra.
  - cbn [z11 zSwt] in *; lra.
  - pose proof (zSp u); cbn [z11 zSwt] in *; lra.
  - pose proof (zSp u); cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u) as hsp; destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]];
    clear - IH hsp hiv1 hiv2 hp4; nra.
  - cbn [z11 zSwt] in *; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u) as hsp; destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]];
    clear - IH hsp hiv1 hiv2 hp4; nra.
  - cbn [zSwt] in *; rewrite zR_succ; cbn [z11]; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u) as hsp; destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]];
    clear - IH hsp hiv1 hiv2 hp4; nra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; lra.
  - cbn [z11 zSwt] in *; rewrite zR_succ; cbn [z11]; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u) as hsp; destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]];
    clear - IH hsp hiv1 hiv2 hp4; nra.
  - cbn [z11 zSwt] in *; rewrite zR_succ; cbn [z11]; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u) as hsp; destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]];
    clear - IH hsp hiv1 hiv2 hp4; nra.
Qed.

Lemma zBz (n : nat) (u : zW) (k' : nat) (v : zW) (a b : Rat) :
  ~ BScan false (1 + n * 2) (WK :: u) k' v a b.
Proof.
  intros h.
  remember false as s eqn:hs.
  remember (1 + n * 2)%nat as k eqn:hk.
  remember (WK :: u) as w eqn:hu.
  destruct h; try discriminate; try lia.
  - destruct r; discriminate.
  - destruct r; discriminate.
Qed.

Lemma z0L_odd_bscan {n : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan false (1 + n * 2) u k' v a b)
  (hL : z0L (WQ :: u) = true) :
  z0L u = true.
Proof.
  destruct u as [| t0 u']; [discriminate |].
  destruct t0.
  - exact hL.
  - exfalso; exact (zBz n u' k' v a b h).
  - remember false as s eqn:hs.
    remember (1 + n * 2)%nat as k eqn:hk.
    remember (WQ :: u') as w eqn:hu.
    destruct h; try discriminate; try lia.
    + inversion hu; subst; reflexivity.
    + inversion hu; subst; reflexivity.
    + destruct r; cbn [zQK] in hu; inversion hu; subst; reflexivity.
    + destruct r; cbn [zQK] in hu; inversion hu; subst; reflexivity.
Qed.

Lemma z1p_z0L {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h : BScan s k u k' v a b)
  (hL : z0L u = true) :
  z11 v <= (1#8) * zSwt s * z11 u.
Proof.
  induction h as [k | n u k v a b _ IH | n u k v a b hSub _ | n u k v a b hSub _
                  | n u k v a b _ IH | n u k v a b hSub IH | n u k v a b _ IH | n u k v a b hSub IH
                  | r m u k v a b hSub IH | r m u k v a b hSub IH | r m u k v a b hSub _
                  | n u k v a b _ IH | n u k v a b hSub IH
                  | r m u k v a b hSub IH | r m u k v a b hSub IH].
  - discriminate.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (z1p_upper hSub); cbn [z11 zSwt] in *; lra.
  - pose proof (z1p_upper hSub); cbn [z11 zSwt] in *; lra.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IH (z0L_odd_bscan hSub hL)); cbn [z11 zSwt] in *; lra.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IH (z0L_odd_bscan hSub hL)); cbn [z11 zSwt] in *; lra.
  - destruct r as [| r'].
    + pose proof (IH hL); cbn [zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u) as hsp.
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8].
      clear - hUp hsp hiv1 hiv2 hp4 h8; nra.
  - destruct r as [| r'].
    + pose proof (IH hL); cbn [zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u) as hsp.
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8].
      clear - hUp hsp hiv1 hiv2 hp4 h8; nra.
  - pose proof (z1p_upper hSub) as hUp.
    cbn [z11 zSwt] in hUp |- *; rewrite zR_succ; cbn [z11]; rewrite z11_R, z11_QK; cbn [z11].
    pose proof (zSp u) as hsp.
    destruct (zIv_P4 r) as [hiv1 [hiv2 [hp4 _]]].
    clear - hUp hsp hiv1 hiv2 hp4; nra.
  - pose proof (IH hL); cbn [z11 zSwt] in *; lra.
  - pose proof (IH (z0L_odd_bscan hSub hL)); cbn [z11 zSwt] in *; lra.
  - destruct r as [| r'].
    + pose proof (IH hL); cbn [Nat.add zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite zR_succ; cbn [z11]; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u) as hsp.
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8].
      clear - hUp hsp hiv1 hiv2 hp4 h8; nra.
  - destruct r as [| r'].
    + pose proof (IH hL); cbn [Nat.add zQK zR repeat app z11 zSwt zIv] in *; lra.
    + pose proof (z1p_upper hSub) as hUp.
      cbn [z11 zSwt] in hUp |- *; rewrite zR_succ; cbn [z11]; rewrite z11_R, z11_QK; cbn [z11].
      pose proof (zSp u) as hsp.
      destruct (zIv_P4 (S r')) as [hiv1 [hiv2 [hp4 hge1]]].
      destruct (hge1 ltac:(lia)) as [_ h8].
      clear - hUp hsp hiv1 hiv2 hp4 h8; nra.
Qed.

Lemma Q_of_nat_sub (a b : nat) : (b <= a)%nat -> Q_of_nat (a - b) == Q_of_nat a - Q_of_nat b.
Proof.
  intro h; unfold Q_of_nat; rewrite Nat2Z.inj_sub by exact h.
  unfold Qeq, Qminus, Qplus, Qopp, inject_Z; cbn; lia.
Qed.

Lemma nat_ge_of_not_Qle (k n : nat) (hk : ~ (Q_of_nat n <= Q_of_nat k)) : (S k <= n)%nat.
Proof.
  destruct (Nat.le_gt_cases n k) as [hle | hgt]; [exfalso; apply hk, Q_of_nat_le, hle | lia].
Qed.

Notation ModeU := TM1.ModeU.

Notation ME := TM1.ME.

Notation MO := TM1.MO.

Notation MS := TM1.MS.

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
               | right; split; [exact (zPrU_shift_K hE)
                              | split; [left; exact (zPrU_pair0_E hE) | exact (zPrU_pair0_O hE)]]].
      * rewrite hw.
        split; [left; exact (zPrU_even_c r hS)
               | right; split; [exact (zPrU_shift_c r hS)
                              | split; [right; exists (S r), u0; split; [reflexivity | exact hS]
                                      | exact (zPrU_odd_c (S r) hS)]]].
    + destruct hOS as [hO | [_ [hQ_EC hQ_O]]].
      * split; [left; exact (zPrU_short_Q hO)
               | right; split; [exact (zPrU_shift_Q hO)
                              | split; [left; exact (zPrU_pair1_E hO) | exact (zPrU_pair1_O hO)]]].
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
  remember MS as m eqn:hm; destruct h; try discriminate.
  - pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W]; lra.
  - pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw.
    cbn [z0W]; rewrite z0W_QK; cbn [z0W].
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    clear - hw hp4; nra.
  - pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W]; lra.
Qed.

Lemma zP4_mul_W (r : nat) {u : zW} (hWu : 1 <= z0W u) :
  z0W u <= zP4 r * z0W u /\ zP4 r <= zP4 r * z0W u.
Proof.
  destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
  split; clear - hWu hp4; nra.
Qed.

Lemma zPrU_bscan {m : ModeU} {w : zW} (hI : zPrU m w) :
  ((m = ME \/ m = MO) ->
    forall (k : nat),
      (m = ME -> exists n, k = (n * 2)%nat) ->
      (m = MO -> exists n, k = (1 + n * 2)%nat) ->
      16 * z0W w < Q_of_nat k - 3 ->
      exists m' v a b, BScan false k w (1 + m') v a b /\ (0 < m')%nat) /\
  (m = MS ->
    forall (k : nat),
      (exists n, k = (1 + n * 2)%nat) ->
      4 * z0W w - 4 < Q_of_nat k - 3 ->
      exists m' v a b, BScan true k w (1 + m') v a b /\ (0 < m')%nat).
Proof.
  induction hI as [| | u hO IH | u hO IH | r u hS IH | u hE IH | r u hS IH
                   | u hE IH | r u hS IH | u hO IH | u hO IH
                   | u hE IH | u hE IH | u hO IH | u hO IH].
  - split; [| discriminate].
    intros _ k hE _ hk; destruct (hE eq_refl) as [n ->]; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hle; push_Q_of_nat; lra).
    exists ((2 * n - 2) * 2)%nat, [WV]; eexists; eexists; split; [| lia].
    replace (n * 2)%nat with (2 + (n - 1) * 2)%nat by lia.
    replace (1 + (2 * n - 2) * 2)%nat with (1 + ((n - 1) * 2) * 2)%nat by lia.
    exact (BScan_T (BScan_nil _)).
  - split; [| discriminate].
    intros _ k _ hO hk; destruct (hO eq_refl) as [n ->]; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hle; push_Q_of_nat; lra).
    exists ((2 * n - 1) * 2)%nat, [WV]; eexists; eexists; split; [| lia].
    replace (1 + n * 2)%nat with (2 + (n * 2 - 1))%nat by lia.
    replace (1 + (2 * n - 1) * 2)%nat with (1 + (n * 2 - 1) * 2)%nat by lia.
    exact (BScan_T (BScan_nil _)).
  - split; [| discriminate].
    intros _ k hE _ hk; destruct (hE eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hw hle; push_Q_of_nat; lra).
    assert (hsub : 16 * z0W u < Q_of_nat (1 + (n * 2 - 2) * 2) - 3)
      by (pose proof (Q_of_nat_sub (n * 2) 2 ltac:(lia)) as hq; clear - hk hw hq; push_Q_of_nat; lra).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2 - 2) * 2)%nat ltac:(discriminate)
      (fun _ => ex_intro _ (n * 2 - 2)%nat eq_refl) hsub) as [m' [v [a [b [hS hm']]]]].
    replace (n * 2)%nat with (2 + (n * 2 - 2))%nat by lia.
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_T hS) | exact hm'].
  - split; [| discriminate].
    intros _ k _ hO_k hk; destruct (hO_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hw hle; push_Q_of_nat; lra).
    assert (hsub : 16 * z0W u < Q_of_nat (1 + (n * 2 - 1) * 2) - 3)
      by (pose proof (Q_of_nat_sub (n * 2) 1 ltac:(lia)) as hq; clear - hk hw hq; push_Q_of_nat; lra).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2 - 1) * 2)%nat ltac:(discriminate)
      (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl) hsub) as [m' [v [a [b [hS hm']]]]].
    replace (1 + n * 2)%nat with (2 + (n * 2 - 1))%nat by lia.
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_T hS) | exact hm'].
  - split; [| discriminate].
    intros _ k _ hO_k hk; destruct (hO_k eq_refl) as [n ->].
    pose proof (zPrU_MS_W hS) as hWu.
    rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    destruct (zP4_mul_W r hWu) as [hPW1 hPW2].
    assert (heq_pw : zP4 r * (z0W u * (1#2)) == (1#2) * (zP4 r * z0W u)) by ring; rewrite heq_pw in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hp4 hPW2 hle; push_Q_of_nat; lra).
    assert (hpow_ge : (2 <= 2 ^ (1 + r))%nat) by (rewrite (zP2 r); pose proof (zPp r); lia).
    destruct (z0F (n - 1)) as [[m hm] | [m hm]].
    + assert (hn_eq : n = (1 + m * 2)%nat) by lia; subst n.
      assert (hm_pow : (m * 2 <= m * 2 ^ (1 + r))%nat) by nia.
      pose proof (proj1 (Q_of_nat_le _ _) hm_pow) as hm_pow_q.
      assert (hsub : 4 * z0W u - 4 < Q_of_nat (1 + m * 2 ^ (1 + r)) - 3)
        by (clear - hk hp4 hPW1 hPW2 hm_pow_q; push_Q_of_nat; lra).
      assert (heven : exists n', (1 + m * 2 ^ (1 + r))%nat = (1 + n' * 2)%nat)
        by (exists (m * 2 ^ r)%nat; rewrite (zP2 r); lia).
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (1 + r))%nat heven hsub) as [m' [v [a [b [hSub hm']]]]].
      replace (1 + (1 + m * 2) * 2)%nat with (3 + m * 4)%nat by lia.
      exists m', (WK :: (zR r WV ++ v)); eexists; eexists; split; [exact (BScan_odd_chain0 r hSub) | exact hm'].
    + assert (hn_eq : n = (2 + m * 2)%nat) by lia; subst n.
      assert (hm_pow : (m * 2 <= m * 2 ^ (1 + r))%nat) by nia.
      pose proof (proj1 (Q_of_nat_le _ _) hm_pow) as hm_pow_q.
      assert (hsub : 4 * z0W u - 4 < Q_of_nat (1 + m * 2 ^ (1 + r)) - 3)
        by (clear - hk hp4 hPW1 hPW2 hm_pow_q; push_Q_of_nat; lra).
      assert (heven : exists n', (1 + m * 2 ^ (1 + r))%nat = (1 + n' * 2)%nat)
        by (exists (m * 2 ^ r)%nat; rewrite (zP2 r); lia).
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (1 + r))%nat heven hsub) as [m' [v [a [b [hSub hm']]]]].
      replace (1 + (2 + m * 2) * 2)%nat with (5 + m * 4)%nat by lia.
      exists m', (WQ :: (zR r WV ++ v)); eexists; eexists; split; [exact (BScan_odd_chain1 r hSub) | exact hm'].
  - split; [| discriminate].
    intros _ k hE_k _ hk; destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hw hle; push_Q_of_nat; lra).
    destruct (z0F n) as [[m ->] | [m ->]].
    + assert (hm1 : (1 <= m)%nat) by lia.
      assert (hsub : 16 * z0W u < Q_of_nat ((m - 1) * 2) - 3)
        by (pose proof (Q_of_nat_sub m 1 hm1) as hq; clear - hk hw hq; push_Q_of_nat; lra).
      destruct (proj1 IH (or_introl eq_refl) ((m - 1) * 2)%nat
        (fun _ => ex_intro _ (m - 1)%nat eq_refl) ltac:(discriminate) hsub) as [m' [v [a [b [hSub hm']]]]].
      replace (m * 2 * 2)%nat with (4 + (m - 1) * 4)%nat by lia.
      exists m', (WQ :: v); eexists; eexists; split; [exact (BScan_short10 hSub) | exact hm'].
    + assert (hsub : 16 * z0W u < Q_of_nat (m * 2) - 3) by (clear - hk hw; push_Q_of_nat; lra).
      destruct (proj1 IH (or_introl eq_refl) (m * 2)%nat
        (fun _ => ex_intro _ m eq_refl) ltac:(discriminate) hsub) as [m' [v [a [b [hSub hm']]]]].
      replace ((1 + m * 2) * 2)%nat with (2 + m * 4)%nat by lia.
      exists m', (WK :: v); eexists; eexists; split; [exact (BScan_short00 hSub) | exact hm'].
  - split; [| discriminate].
    intros _ k hE_k _ hk; destruct (hE_k eq_refl) as [n ->].
    pose proof (zPrU_MS_W hS) as hWu; cbn [z0W] in hk; rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    destruct (zP4_mul_W r hWu) as [hPW1 hPW2].
    assert (heq_pw : zP4 r * (z0W u * (1#2)) == (1#2) * (zP4 r * z0W u)) by ring; rewrite heq_pw in hk.
    assert (hn3 : (3 <= n)%nat) by (apply (nat_ge_of_not_Qle 2); intro hle; clear - hk hp4 hPW2 hle; push_Q_of_nat; lra).
    assert (hpow_ge : (2 <= 2 ^ (1 + r))%nat) by (rewrite (zP2 r); pose proof (zPp r); lia).
    assert (hm_pow : ((1 + (n - 3) * 2) * 2 <= (1 + (n - 3) * 2) * 2 ^ (1 + r))%nat) by nia.
    pose proof (proj1 (Q_of_nat_le _ _) hm_pow) as hm_pow_q.
    assert (hsub : 4 * z0W u - 4 < Q_of_nat (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r)) - 3)
      by (pose proof (Q_of_nat_sub n 3 hn3) as hn_q; clear - hk hp4 hPW1 hPW2 hm_pow_q hn_q; push_Q_of_nat; lra).
    assert (heven : exists n', (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r))%nat = (1 + n' * 2)%nat)
      by (exists ((1 + (n - 3) * 2) * 2 ^ r)%nat; rewrite (zP2 r); lia).
    destruct (proj2 IH eq_refl (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r))%nat heven hsub) as [m' [v [a [b [hSub hm']]]]].
    replace (n * 2)%nat with (6 + (n - 3) * 2)%nat by lia.
    exists m', (zR (1 + r) WV ++ v); eexists; eexists; split; [exact (BScan_even_chain r hSub) | exact hm'].
  - split; [intros [?|?]; discriminate |].
    intros _ k [n ->] hk.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hsub : 16 * z0W u < Q_of_nat ((n * 2) * 2) - 3) by (clear - hk hw; push_Q_of_nat; lra).
    destruct (proj1 IH (or_introl eq_refl) ((n * 2) * 2)%nat
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) ltac:(discriminate) hsub) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_shift_pair0 hSub) | exact hm'].
  - split; [intros [?|?]; discriminate |].
    intros _ k [n ->] hk.
    pose proof (zPrU_MS_W hS) as hWu; cbn [z0W] in hk; rewrite z0W_QK in hk; cbn [z0W] in hk.
    destruct (zIv_P4 r) as [_ [_ [hp4 _]]].
    destruct (zP4_mul_W r hWu) as [hPW1 hPW2].
    assert (heq_pw : zP4 r * (z0W u * (1#2)) == (1#2) * (zP4 r * z0W u)) by ring; rewrite heq_pw in hk.
    assert (hn4 : (4 <= n)%nat) by (apply (nat_ge_of_not_Qle 3); intro hle; clear - hk hp4 hPW2 hle; push_Q_of_nat; lra).
    assert (hpow_ge : (4 <= 2 ^ (2 + r))%nat)
      by (replace (2 + r)%nat with (1 + (1 + r))%nat by lia; rewrite (zP2 (1 + r)), (zP2 r); pose proof (zPp r); lia).
    destruct (z0F (n - 1)) as [[m hm] | [m hm]].
    + assert (hn_eq : n = (1 + m * 2)%nat) by lia; subst n.
      assert (hm_pow : (m * 4 <= m * 2 ^ (2 + r))%nat) by nia.
      pose proof (proj1 (Q_of_nat_le _ _) hm_pow) as hm_pow_q.
      assert (hsub : 4 * z0W u - 4 < Q_of_nat (1 + m * 2 ^ (2 + r)) - 3)
        by (clear - hk hp4 hPW1 hPW2 hm_pow_q; push_Q_of_nat; lra).
      assert (heven : exists n', (1 + m * 2 ^ (2 + r))%nat = (1 + n' * 2)%nat)
        by (exists (m * 2 ^ (1 + r))%nat; replace (2 + r)%nat with (1 + (1 + r))%nat by lia; rewrite (zP2 (1 + r)); lia).
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (2 + r))%nat heven hsub) as [m' [v [a [b [hSub hm']]]]].
      replace (1 + (1 + m * 2) * 2)%nat with (3 + m * 4)%nat by lia.
      exists m', (WK :: (zR (1 + r) WV ++ v)); eexists; eexists; split; [exact (BScan_shift_chain0 r hSub) | exact hm'].
    + assert (hn_eq : n = (2 + m * 2)%nat) by lia; subst n.
      assert (hm_pow : (m * 4 <= m * 2 ^ (2 + r))%nat) by nia.
      pose proof (proj1 (Q_of_nat_le _ _) hm_pow) as hm_pow_q.
      assert (hsub : 4 * z0W u - 4 < Q_of_nat (1 + m * 2 ^ (2 + r)) - 3)
        by (clear - hk hp4 hPW1 hPW2 hm_pow_q; push_Q_of_nat; lra).
      assert (heven : exists n', (1 + m * 2 ^ (2 + r))%nat = (1 + n' * 2)%nat)
        by (exists (m * 2 ^ (1 + r))%nat; replace (2 + r)%nat with (1 + (1 + r))%nat by lia; rewrite (zP2 (1 + r)); lia).
      destruct (proj2 IH eq_refl (1 + m * 2 ^ (2 + r))%nat heven hsub) as [m' [v [a [b [hSub hm']]]]].
      replace (1 + (2 + m * 2) * 2)%nat with (5 + m * 4)%nat by lia.
      exists m', (WQ :: (zR (1 + r) WV ++ v)); eexists; eexists; split; [exact (BScan_shift_chain1 r hSub) | exact hm'].
  - split; [| discriminate].
    intros _ k hE_k _ hk; destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hw hle; push_Q_of_nat; lra).
    destruct (z0F n) as [[m ->] | [m ->]].
    + assert (hm1 : (1 <= m)%nat) by lia.
      assert (hsub : 16 * z0W u < Q_of_nat (1 + (m - 1) * 2) - 3)
        by (pose proof (Q_of_nat_sub m 1 hm1) as hq; clear - hk hw hq; push_Q_of_nat; lra).
      destruct (proj1 IH (or_intror eq_refl) (1 + (m - 1) * 2)%nat ltac:(discriminate)
        (fun _ => ex_intro _ (m - 1)%nat eq_refl) hsub) as [m' [v [a [b [hSub hm']]]]].
      replace (m * 2 * 2)%nat with (4 + (m - 1) * 4)%nat by lia.
      exists m', (WQ :: v); eexists; eexists; split; [exact (BScan_short11 hSub) | exact hm'].
    + assert (hsub : 16 * z0W u < Q_of_nat (1 + m * 2) - 3) by (clear - hk hw; push_Q_of_nat; lra).
      destruct (proj1 IH (or_intror eq_refl) (1 + m * 2)%nat ltac:(discriminate)
        (fun _ => ex_intro _ m eq_refl) hsub) as [m' [v [a [b [hSub hm']]]]].
      replace ((1 + m * 2) * 2)%nat with (2 + m * 4)%nat by lia.
      exists m', (WK :: v); eexists; eexists; split; [exact (BScan_short01 hSub) | exact hm'].
  - split; [intros [?|?]; discriminate |].
    intros _ k [n ->] hk.
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hsub : 16 * z0W u < Q_of_nat (1 + (n * 2) * 2) - 3) by (clear - hk hw; push_Q_of_nat; lra).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2) * 2)%nat ltac:(discriminate)
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) hsub) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_shift_pair1 hSub) | exact hm'].
  - split; [| discriminate].
    intros _ k hE_k _ hk; destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hw hle; push_Q_of_nat; lra).
    assert (hsub : 16 * z0W u < Q_of_nat ((n * 2 - 1) * 2) - 3)
      by (pose proof (Q_of_nat_sub (n * 2) 1 ltac:(lia)) as hq; clear - hk hw hq; push_Q_of_nat; lra).
    destruct (proj1 IH (or_introl eq_refl) ((n * 2 - 1) * 2)%nat
      (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl) ltac:(discriminate) hsub) as [m' [v [a [b [hSub hm']]]]].
    replace (n * 2)%nat with (1 + (n * 2 - 1))%nat by lia.
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_pair0 hSub) | exact hm'].
  - split; [| discriminate].
    intros _ k _ hO_k hk; destruct (hO_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hsub : 16 * z0W u < Q_of_nat ((n * 2) * 2) - 3) by (clear - hk hw; push_Q_of_nat; lra).
    destruct (proj1 IH (or_introl eq_refl) ((n * 2) * 2)%nat
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) ltac:(discriminate) hsub) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_pair0 hSub) | exact hm'].
  - split; [| discriminate].
    intros _ k hE_k _ hk; destruct (hE_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hn2 : (2 <= n)%nat) by (apply (nat_ge_of_not_Qle 1); intro hle; clear - hk hw hle; push_Q_of_nat; lra).
    assert (hsub : 16 * z0W u < Q_of_nat (1 + (n * 2 - 1) * 2) - 3)
      by (pose proof (Q_of_nat_sub (n * 2) 1 ltac:(lia)) as hq; clear - hk hw hq; push_Q_of_nat; lra).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2 - 1) * 2)%nat ltac:(discriminate)
      (fun _ => ex_intro _ (n * 2 - 1)%nat eq_refl) hsub) as [m' [v [a [b [hSub hm']]]]].
    replace (n * 2)%nat with (1 + (n * 2 - 1))%nat by lia.
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_pair1 hSub) | exact hm'].
  - split; [| discriminate].
    intros _ k _ hO_k hk; destruct (hO_k eq_refl) as [n ->].
    pose proof (proj2 (proj2 (proj2 (zWn u)))) as hw; cbn [z0W] in hk.
    assert (hsub : 16 * z0W u < Q_of_nat (1 + (n * 2) * 2) - 3) by (clear - hk hw; push_Q_of_nat; lra).
    destruct (proj1 IH (or_intror eq_refl) (1 + (n * 2) * 2)%nat ltac:(discriminate)
      (fun _ => ex_intro _ (n * 2)%nat eq_refl) hsub) as [m' [v [a [b [hSub hm']]]]].
    exists m', (WV :: v); eexists; eexists; split; [exact (BScan_pair1 hSub) | exact hm'].
Qed.

Lemma zDg_zero_Z {A H : nat} {w : zW} (h : zDg A H w) (h0 : A = 0%nat) :
  z0Z w == Q_of_nat (2 ^ H) - 1.
Proof.
  induction h as [| A1 H1 u1 _ IH | A1 H1 u1 _ _]; [cbn; push_Q_of_nat; lra | | lia].
  assert (hA1 : A1 = 0%nat) by lia.
  rewrite zP2; cbn [z0Z]; rewrite (IH hA1); push_Q_of_nat; lra.
Qed.

Lemma zPiece3 {n_mid : nat} (hn : (2 <= n_mid)%nat) :
  exists m_end d1 a_t b_t,
    BScan false (n_mid * 4) [WK; WQ; WQ; WQ; WQ; WK] (m_end * 8) [WQ; d1; WV; WV] a_t b_t /\
    z11 [WQ; d1; WV; WV] == 1 /\
    z0W [WQ; d1; WV; WV] <= (15#4) /\
    z0L [WQ; d1; WV; WV] = true /\
    a_t - b_t <= 6 /\
    b_t - a_t <= 0.
Proof.
  destruct (z0F (n_mid - 1)) as [[m1 hm1] | [m1 hm1]].
  - assert (hm1_pos : (1 <= m1)%nat) by lia.
    pose proof (BScan_pair0 (BScan_nil (((m1 - 1) * 2) * 2 * 2))) as hB0.
    replace (((m1 - 1) * 2) * 2 * 2)%nat with ((m1 - 1) * 8)%nat in hB0 by lia.
    pose proof (BScan_short11 (BScan_pair1 hB0)) as hB2.
    replace (4 + (m1 - 1) * 4)%nat with (((m1 - 1) * 2 + 2) * 2)%nat in hB2 by lia.
    pose proof (BScan_short10 hB2) as hB3.
    replace (4 + ((m1 - 1) * 2 + 2) * 4)%nat with (n_mid * 4)%nat in hB3 by lia.
    exists (m1 - 1)%nat, WQ; eexists; eexists; split; [exact hB3 |].
    cbn [z11 z0W z0L]; repeat split; lra.
  - pose proof (BScan_pair0 (BScan_nil ((m1 * 2) * 2 * 2))) as hB0.
    replace ((m1 * 2) * 2 * 2)%nat with (m1 * 8)%nat in hB0 by lia.
    pose proof (BScan_short01 (BScan_pair1 hB0)) as hB2.
    replace (2 + m1 * 4)%nat with ((1 + m1 * 2) * 2)%nat in hB2 by lia.
    pose proof (BScan_short10 hB2) as hB3.
    replace (4 + (1 + m1 * 2) * 4)%nat with (n_mid * 4)%nat in hB3 by lia.
    exists m1, WK; eexists; eexists; split; [exact hB3 |].
    cbn [z11 z0W z0L]; repeat split; lra.
Qed.

Lemma z1l {s : bool} {k : nat} {u : zW} {k' : nat} {v : zW} {a b : Rat}
  (h1 : BScan s k u k' v a b) :
  forall {r r' : side}, BRIncs false k' r r' -> BRIncs s k (zTs u r) (zTs v r').
Proof.
  induction h1; intros r0 r0' h2.
  - exact h2.
  - cbn [zTs]; exact (BRIncs_T (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_pair0 (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_pair1 (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_short00 (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_short01 (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_short10 (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_short11 (IHh1 _ _ h2)).
  - replace (zTs (zQK r (WV :: u)) r0) with (zTs (zQK r [WV]) (zTs u r0))
      by (rewrite <- z0S, <- zQK_append; reflexivity).
    cbn [zTs]; rewrite z0S; exact (BRIncs_odd_chain0 r (IHh1 _ _ h2)).
  - replace (zTs (zQK r (WV :: u)) r0) with (zTs (zQK r [WV]) (zTs u r0))
      by (rewrite <- z0S, <- zQK_append; reflexivity).
    cbn [zTs]; rewrite z0S; exact (BRIncs_odd_chain1 r (IHh1 _ _ h2)).
  - replace (zTs (WK :: zQK r (WV :: u)) r0) with (d0 *> zTs (zQK r [WV]) (zTs u r0))
      by (cbn [zTs]; rewrite <- z0S, <- zQK_append; reflexivity).
    rewrite z0S; exact (BRIncs_even_chain r (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_shift_pair0 (IHh1 _ _ h2)).
  - cbn [zTs]; exact (BRIncs_shift_pair1 (IHh1 _ _ h2)).
  - replace (zTs (WK :: zQK r (WV :: u)) r0) with (d0 *> zTs (zQK r [WV]) (zTs u r0))
      by (cbn [zTs]; rewrite <- z0S, <- zQK_append; reflexivity).
    replace (zTs (WK :: (zR (1 + r) WV ++ v)) r0') with (d0 *> zTs (zR (1 + r) WV) (zTs v r0'))
      by (cbn [zTs]; rewrite z0S; reflexivity).
    exact (BRIncs_shift_chain0 r (IHh1 _ _ h2)).
  - replace (zTs (WK :: zQK r (WV :: u)) r0) with (d0 *> zTs (zQK r [WV]) (zTs u r0))
      by (cbn [zTs]; rewrite <- z0S, <- zQK_append; reflexivity).
    replace (zTs (WQ :: (zR (1 + r) WV ++ v)) r0') with (d1 *> zTs (zR (1 + r) WV) (zTs v r0'))
      by (cbn [zTs]; rewrite z0S; reflexivity).
    exact (BRIncs_shift_chain1 r (IHh1 _ _ h2)).
Qed.

Lemma zDg_to_Binary {A H : nat} {ds : zW} (hD : zDg A H ds) :
  forall (n : nat), A = (1 + n)%nat -> (2 ^ (H - 1) <= 1 + n)%nat -> Binary (1 + n) H (zTs ds 0inf%sym).
Proof.
  induction hD as [| A' H' u hD' IH | A' H' u hD' IH]; intros n hA hPow; [lia | |].
  - destruct H' as [| H''].
    + pose proof (z0W_lt hD'); cbn [Nat.pow] in *; lia.
    + replace (1 + S H'' - 1)%nat with (1 + H'')%nat in hPow by lia.
      rewrite zP2 in hPow.
      assert (hPow' : (2 ^ (S H'' - 1) <= 1 + (A' - 1))%nat)
        by (replace (S H'' - 1)%nat with H'' by lia; lia).
      pose proof (Binary_zero (IH (A' - 1)%nat ltac:(lia) hPow')) as hB.
      replace (2 + (A' - 1) * 2)%nat with (1 + n)%nat in hB by lia.
      exact hB.
  - destruct H' as [| H''].
    + pose proof (z0W_lt hD'); cbn [Nat.pow] in *.
      assert (hA'0 : A' = 0%nat) by lia; subst A'.
      assert (hu : u = []) by (symmetry; exact (z0X zDg_nil hD')); subst u.
      assert (hn0 : n = 0%nat) by lia; subst n.
      exact Binary_one.
    + replace (1 + S H'' - 1)%nat with (1 + H'')%nat in hPow by lia.
      rewrite zP2 in hPow.
      pose proof (zPp H'') as h_ge1.
      assert (hPow' : (2 ^ (S H'' - 1) <= 1 + (A' - 1))%nat)
        by (replace (S H'' - 1)%nat with H'' by lia; lia).
      pose proof (Binary_two (IH (A' - 1)%nat ltac:(lia) hPow')) as hB.
      replace (3 + (A' - 1) * 2)%nat with (1 + n)%nat in hB by lia.
      exact hB.
Qed.

Lemma Q_of_nat_N (n : N) : Q_of_nat (N.to_nat n) == inject_Z (Z.of_N n).
Proof. unfold Q_of_nat, Qeq; cbn; lia. Qed.

Notation N_124522 := TM1.N_124522.

Notation N_249044 := TM1.N_249044.

Lemma Q_of_nat_249044 : Q_of_nat N_249044 == 249044.
Proof.
  unfold N_249044, N_124522.
  rewrite Q_of_nat_mul, Q_of_nat_N; reflexivity.
Qed.

Lemma Qnat_pow2_8 : Q_of_nat (2 ^ 8) == 256.
Proof. vm_compute; reflexivity. Qed.

Lemma Qnat_pow2_9 : Q_of_nat (2 ^ 9) == 512.
Proof. vm_compute; reflexivity. Qed.

Lemma Qnat_pow2_16 : Q_of_nat (2 ^ 16) == 65536.
Proof.
  change 16%nat with (8 + 8)%nat.
  rewrite Nat.pow_add_r, Q_of_nat_mul; vm_compute; reflexivity.
Qed.

Lemma Qnat_pow2_17 : Q_of_nat (2 ^ 17) == 131072.
Proof.
  change 17%nat with (8 + 9)%nat.
  rewrite Nat.pow_add_r, Q_of_nat_mul; vm_compute; reflexivity.
Qed.

Definition zP33 : zW :=
  [WV;WV;WQ;WV;WV;WQ;WV;WV;WK;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WV;WV;WK;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WV;WV;WK].

Definition zOut33 : zW :=
  [WV;WQ;WV;WV;WK;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WV;WV;WK;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WV;WV;WK;WV;WV;WK;WV].

Definition zTail8 : zW := [WQ;WQ;WK;WK;WQ;WQ;WQ;WQ].

Lemma zDg_tail8 : zDg 243 8 zTail8.
Proof.
  exact (zDg_one (zDg_one (zDg_zero (zDg_zero (zDg_one (zDg_one (zDg_one (zDg_one zDg_nil)))))))).
Qed.

Lemma zP3_11 (m : N) {k_in k_out : nat} {r r' : side}
  (h1 : k_in = (4 + N.to_nat m * 2)%nat) (h2 : k_out = (1 + N.to_nat m * 4)%nat)
  (h : BRIncs false k_out r r') :
  BRIncs false k_in (bt *> (bt *> (d1 *> r))) (bt *> (d1 *> (bt *> r'))).
Proof.
  replace k_out with (1 + (N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair1 h) as h_sp.
  replace (1 + N.to_nat m * 2)%nat with (1 + N.to_nat m * 2 ^ (1 + 0))%nat in h_sp
    by (cbn [Nat.add Nat.pow]; lia).
  pose proof (BRIncs_odd_chain1 0 h_sp) as h_oc; cbn [zQK zR repeat zTs] in h_oc.
  replace (5 + N.to_nat m * 4)%nat with (1 + (2 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (2 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_01 (m : N) {k_in k_out : nat} {r r' : side}
  (h1 : k_in = (3 + N.to_nat m * 2)%nat) (h2 : k_out = (1 + N.to_nat m * 4)%nat)
  (h : BRIncs false k_out r r') :
  BRIncs false k_in (bt *> (bt *> (d1 *> r))) (bt *> (d0 *> (bt *> r'))).
Proof.
  replace k_out with (1 + (N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair1 h) as h_sp.
  replace (1 + N.to_nat m * 2)%nat with (1 + N.to_nat m * 2 ^ (1 + 0))%nat in h_sp
    by (cbn [Nat.add Nat.pow]; lia).
  pose proof (BRIncs_odd_chain0 0 h_sp) as h_oc; cbn [zQK zR repeat zTs] in h_oc.
  replace (3 + N.to_nat m * 4)%nat with (1 + (1 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (1 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_00 (m : N) {k_in k_out : nat} {r r' : side}
  (h1 : k_in = (3 + N.to_nat m * 2)%nat) (h2 : k_out = (N.to_nat m * 4)%nat)
  (h : BRIncs false k_out r r') :
  BRIncs false k_in (bt *> (bt *> (d0 *> r))) (bt *> (d0 *> (bt *> r'))).
Proof.
  replace k_out with ((N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair0 h) as h_sp.
  replace (1 + N.to_nat m * 2)%nat with (1 + N.to_nat m * 2 ^ (1 + 0))%nat in h_sp
    by (cbn [Nat.add Nat.pow]; lia).
  pose proof (BRIncs_odd_chain0 0 h_sp) as h_oc; cbn [zQK zR repeat zTs] in h_oc.
  replace (3 + N.to_nat m * 4)%nat with (1 + (1 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (1 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zP3_10 (m : N) {k_in k_out : nat} {r r' : side}
  (h1 : k_in = (4 + N.to_nat m * 2)%nat) (h2 : k_out = (N.to_nat m * 4)%nat)
  (h : BRIncs false k_out r r') :
  BRIncs false k_in (bt *> (bt *> (d0 *> r))) (bt *> (d1 *> (bt *> r'))).
Proof.
  replace k_out with ((N.to_nat m * 2) * 2)%nat in h by lia.
  pose proof (BRIncs_shift_pair0 h) as h_sp.
  replace (1 + N.to_nat m * 2)%nat with (1 + N.to_nat m * 2 ^ (1 + 0))%nat in h_sp
    by (cbn [Nat.add Nat.pow]; lia).
  pose proof (BRIncs_odd_chain1 0 h_sp) as h_oc; cbn [zQK zR repeat zTs] in h_oc.
  replace (5 + N.to_nat m * 4)%nat with (1 + (2 + N.to_nat m * 2) * 2)%nat in h_oc by lia.
  replace k_in with (2 + (2 + N.to_nat m * 2))%nat by lia.
  exact (BRIncs_T h_oc).
Qed.

Lemma zBRIncs_P33 {r r' : side} (h : BRIncs false N_249044 r r') :
  BRIncs false 128 (zTs zP33 r) (zTs zOut33 r').
Proof.
  unfold N_249044, N_124522 in h.
  cbn [zP33 zOut33 zTs].
  eapply (zP3_11 62%N); [lia | reflexivity |].
  eapply (zP3_01 123%N); [lia | reflexivity |].
  eapply (zP3_00 245%N); [lia | reflexivity |].
  eapply (zP3_10 488%N); [lia | reflexivity |].
  eapply (zP3_11 974%N); [lia | reflexivity |].
  eapply (zP3_01 1947%N); [lia | reflexivity |].
  eapply (zP3_00 3893%N); [lia | reflexivity |].
  eapply (zP3_10 7784%N); [lia | reflexivity |].
  eapply (zP3_11 15566%N); [lia | reflexivity |].
  eapply (zP3_01 31131%N); [lia | reflexivity |].
  eapply (zP3_00 62261%N); [lia | | exact h]; lia.
Qed.

Opaque N_124522 N_249044.

Notation N_249044_even := TM1.N_249044_even.

Inductive BGood : zW -> Prop :=
  | BGood_intro (H : nat) (u : zW) (A : nat) (hi8 : zW) :
      zDg A H hi8 ->
      z11 u * Q_of_nat (2 ^ H) == 128 ->
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
  pose proof Q_of_nat_249044 as hc249.
  assert (hk_in : 16 * z0W u < Q_of_nat N_249044 - 3)
    by (clear - hc249 hWu_max; lra).
  destruct (proj1 (zPrU_bscan hPrU) (or_introl eq_refl) N_249044
    (fun _ => N_249044_even) ltac:(discriminate) hk_in)
    as [m1 [v1 [a1 [b1 [hB1 _]]]]].
  pose proof (zSp v1) as hSv1; pose proof (proj2 (proj2 (proj2 (zWn v1)))) as hWv1_nonneg.
  assert (h11_v1 : z11 v1 <= (1#8) * z11 u)
    by (pose proof (z1p_z0L hB1 hLu) as h; cbn [zSwt] in h; clear - h; lra).
  destruct (proj1 (z1j hB1) eq_refl) as [hW_v1 [hAB_1 hBA_1]].
  pose proof (z1i hB1) as hBud1; rewrite hc249 in hBud1.
  subst hi8.
  destruct (zD1 hDig) as [A1 [H1 [hD1 [hA1 hH1]]]].
  destruct (zD0 hD1) as [A0 [H0 [hD0 [hA0 hH0]]]].
  destruct (zDw hD0) as [hDw0_1 [hDw0_2 hDw0_3]].
  pose proof (zSp w0) as hSw0; pose proof (proj1 (proj2 (zWn w0))) as hZw0_nonneg.
  assert (hPowH : Q_of_nat (2 ^ H) == 4 * z11 w0).
  { assert (h1 : (2 ^ H = 4 * 2 ^ H0)%nat) by (clear - hH1 hH0; rewrite hH1, hH0; cbn [Nat.add Nat.pow]; lia).
    rewrite h1, Q_of_nat_mul, Q_of_nat_4; clear - hDw0_1; lra. }
  assert (hZ_hi8 : z0Z (WQ :: WK :: w0) == 2 + 4 * z0Z w0) by (cbn [z0Z]; ring).
  assert (hA0_pos : (0 < A0)%nat).
  { destruct A0 as [| A0']; [| clear; lia]. exfalso.
    pose proof (zDg_zero_Z hD0 eq_refl) as hZw0_0.
    rewrite <- hDw0_1 in hZw0_0.
    assert (h_prod : z11 u * z0Z (WQ :: WK :: w0) + 2 * z11 u == z11 u * (4 * z11 w0))
      by (rewrite hZ_hi8, hZw0_0; ring).
    assert (h_pow_u : z11 u * Q_of_nat (2 ^ H) == z11 u * (4 * z11 w0)) by (rewrite hPowH; ring).
    clear - h_prod h_pow_u hHeight hU11 hZ_max; lra. }
  pose proof (zDg_pos_z0L hD0 hA0_pos) as hLw0.
  assert (hY_w0qqk : z0Y (w0 ++ [WQ; WQ; WK]) == z0Y w0 + 7 * z11 w0) by (rewrite z13; cbn [z0Y]; ring).
  assert (hZ_w0qqk : z0Z (w0 ++ [WQ; WQ; WK]) == z0Z w0 + 4 * z11 w0) by (rewrite z14; cbn [z0Z]; ring).
  assert (hScan_cond : (z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2 < Q_of_nat (m1 * 2)).
  { pose proof (proj1 (Q_of_nat_le 0 m1) ltac:(clear; lia)) as hm1_nn; rewrite Q_of_nat_0 in hm1_nn.
    assert (hm1_ub : (Q_of_nat m1 * 2) * z11 v1 <= (Q_of_nat m1 * 2) * ((1#8) * z11 u))
      by (clear - hm1_nn h11_v1; nra).
    assert (h_bud1_exp : (Q_of_nat (1 + m1) - 3) * z11 v1 == (1#2) * ((Q_of_nat m1 * 2) * z11 v1) - 2 * z11 v1)
      by (rewrite Q_of_nat_add, Q_of_nat_1; ring).
    assert (h_yw0 : z0Y w0 == z11 w0 - 1) by (clear - hDw0_1 hDw0_2; lra).
    assert (h_lhs_u : z11 u * ((z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2) ==
        6 * (z11 u * Q_of_nat (2 ^ H)) + (1#2) * (z11 u * z0Z (WQ :: WK :: w0)) - 3 * z11 u)
      by (rewrite hY_w0qqk, hZ_w0qqk, h_yw0, hZ_hi8, hPowH; ring).
    assert (h_rhs_u : (Q_of_nat m1 * 2) * ((1#8) * z11 u) == (1#8) * (z11 u * (Q_of_nat m1 * 2))) by ring.
    assert (h_lt_u : z11 u * ((z0Y (w0 ++ [WQ; WQ; WK]) + z0Z (w0 ++ [WQ; WQ; WK])) * 2) < z11 u * (Q_of_nat m1 * 2))
      by (clear - h_lhs_u hHeight hZ_max hSu hBud1 h_bud1_exp hm1_ub h_rhs_u hAB_1 hWu_max hSv1; lra).
    rewrite Q_of_nat_mul, Q_of_nat_2; clear - hSu h_lt_u; nra. }
  destruct (z1a (w0 ++ [WQ; WQ; WK]) m1 hScan_cond) as [b2 [y [l2 [hS2 _]]]].
  destruct (zScan_qqk hS2 w0 eq_refl) as [_ [h11_y_fn [[n_mid hb2_eq] [y0 hy0]]]]; subst b2.
  assert (h11_y : z11 (WV :: y) <= (1#64) * Q_of_nat (2 ^ H)).
  { pose proof (h11_y_fn hLw0) as hy.
    assert (h11_qqk : z11 (w0 ++ [WQ; WQ; WK]) == 8 * z11 w0) by (rewrite z16; cbn [z11]; ring).
    cbn [z11]; clear - hy h11_qqk hPowH; lra. }
  destruct (zHi_bscan hS2 hD0) as [a2 [b2_r [hB2 [hY_vy [hAB_2 hBA_2]]]]].
  assert (hW_vy : z0W (WV :: y) <= (11#32) * z0Z (WQ :: WK :: w0))
    by (pose proof (proj2 (zWY (WV :: y))) as hwy; clear - hwy hY_vy; lra).
  destruct (z1k hB1 hB2) as [a12 [b12 [hB12 [ha12 hb12]]]].
  assert (h11_v12 : z11 (v1 ++ (WV :: y)) <= (1#4)).
  { rewrite z16; pose proof (zSp (WV :: y)) as hS_vy.
    assert (h_prod : z11 v1 * z11 (WV :: y) <= ((1#8) * z11 u) * ((1#64) * Q_of_nat (2 ^ H)))
      by (clear - h11_v1 h11_y hSv1 hS_vy; nra).
    assert (h_eq : ((1#8) * z11 u) * ((1#64) * Q_of_nat (2 ^ H)) == (1#512) * (z11 u * Q_of_nat (2 ^ H))) by ring.
    clear - h_prod h_eq hHeight; lra. }
  pose proof (zSp (v1 ++ (WV :: y))) as hSv12.
  pose proof (z1i hB12) as hBud12; rewrite hc249 in hBud12.
  pose proof (proj1 (proj2 (zWn (WQ :: WK :: w0)))) as hZ_hi8_nn.
  assert (hp1_ab : z11 v1 * (a2 - b2_r) <= (7#64) * (z11 u * z0Z (WQ :: WK :: w0))).
  { assert (hp : z11 v1 * (a2 - b2_r) <= ((1#8) * z11 u) * ((7#8) * z0Z (WQ :: WK :: w0)))
      by (clear - h11_v1 hAB_2 hSv1 hZ_hi8_nn; nra).
    assert (heq : ((1#8) * z11 u) * ((7#8) * z0Z (WQ :: WK :: w0)) == (7#64) * (z11 u * z0Z (WQ :: WK :: w0))) by ring.
    clear - hp heq; lra. }
  assert (h_ab12 : a12 - b12 <= (64#11) * z0W u + (7#64) * (z11 u * z0Z (WQ :: WK :: w0)))
    by (assert (h_diff : a12 - b12 == (a1 - b1) + z11 v1 * (a2 - b2_r)) by (rewrite ha12, hb12; ring);
        clear - h_diff hAB_1 hp1_ab; lra).
  assert (hn_mid2 : (2 <= n_mid)%nat).
  { apply (nat_ge_of_not_Qle 1); intro hq; rewrite Q_of_nat_1 in hq.
    rewrite Q_of_nat_mul, Q_of_nat_4 in hBud12.
    assert (h_ub : (Q_of_nat n_mid * 4 - 3) * z11 (v1 ++ (WV :: y)) <= 1) by (clear - hq h11_v12 hSv12; nra).
    clear - hBud12 h_ub h_ab12 hWu_max hZ_max; lra. }
  destruct (zPiece3 hn_mid2) as [m_end [d1_tok [a3 [b3 [hB3 [h11_p3 [hW_p3 [hL_p3 [hAB_3 hBA_3]]]]]]]]].
  destruct (z1k hB12 hB3) as [a [b [hB_all [ha_all hb_all]]]].
  set (v := (v1 ++ (WV :: y)) ++ [WQ; d1_tok; WV; WV]).
  assert (h11_v : z11 v == z11 (v1 ++ (WV :: y))) by (unfold v; rewrite z16, h11_p3; ring).
  pose proof (zSp v) as hSv.
  assert (h11_v_le : z11 v <= (1#4)) by (clear - h11_v h11_v12; lra).
  assert (hW_v : z0W v <= (66#19) * z0W u + (11#256) * (z11 u * z0Z (WQ :: WK :: w0)) + (15#16)).
  { unfold v; rewrite z13W, z13W.
    pose proof (proj2 (proj2 (proj2 (zWn [WQ; d1_tok; WV; WV])))) as hW_p3_nn.
    pose proof (proj2 (proj2 (proj2 (zWn (WV :: y))))) as hW_vy_nn.
    assert (hp1 : z11 v1 * z0W (WV :: y) <= ((1#8) * z11 u) * ((11#32) * z0Z (WQ :: WK :: w0)))
      by (clear - h11_v1 hW_vy hSv1 hW_vy_nn; nra).
    assert (hp2 : z11 (v1 ++ (WV :: y)) * z0W [WQ; d1_tok; WV; WV] <= (1#4) * (15#4))
      by (clear - h11_v12 hW_p3 hSv12 hW_p3_nn; nra).
    assert (hp1_eq : ((1#8) * z11 u) * ((11#32) * z0Z (WQ :: WK :: w0)) == (11#256) * (z11 u * z0Z (WQ :: WK :: w0))) by ring.
    clear - hW_v1 hp1 hp1_eq hp2; lra. }
  assert (hAB : a - b <= (508#5)).
  { assert (hp2 : z11 (v1 ++ (WV :: y)) * (a3 - b3) <= (1#4) * 6) by (clear - h11_v12 hAB_3 hSv12; nra).
    assert (h_diff : a - b == (a12 - b12) + z11 (v1 ++ (WV :: y)) * (a3 - b3)) by (rewrite ha_all, hb_all; ring).
    clear - h_diff h_ab12 hp2 hWu_max hZ_max; lra. }
  assert (hBA : b - a <= 8).
  { assert (hp1 : z11 v1 * (b2_r - a2) <= z11 v1) by (clear - hSv1 hBA_2; nra).
    assert (hp2 : z11 (v1 ++ (WV :: y)) * (b3 - a3) <= 0) by (clear - hSv12 hBA_3; nra).
    assert (h_diff : b - a == (b1 - a1) + z11 v1 * (b2_r - a2) + z11 (v1 ++ (WV :: y)) * (b3 - a3))
      by (rewrite ha_all, hb_all, ha12, hb12; ring).
    clear - h_diff hBA_1 hp1 hp2 h11_v1 hU11 hWu_max; lra. }
  assert (hY_v_lt : z0Y v < Q_of_nat (2 ^ 17)).
  { pose proof (proj1 (zWY v)) as hwy.
    rewrite Qnat_pow2_17; clear - hwy hW_v hWu_max hZ_max; lra. }
  destruct (z1B v 17 hY_v_lt) as [J hHn].
  pose proof (z1x v 17 J hHn) as hUnit.
  assert (hJ10 : (10 <= J)%nat).
  { destruct (Nat.le_gt_cases J 9) as [hJ9 | hgt]; [| clear - hgt; lia]. exfalso.
    assert (hpow9 : (2 ^ J <= 2 ^ 9)%nat) by (apply Nat.pow_le_mono_r; clear - hJ9; lia).
    pose proof (proj1 (Q_of_nat_le _ _) hpow9) as hpow9_q.
    rewrite Qnat_pow2_9 in hpow9_q.
    rewrite Qnat_pow2_17 in hUnit.
    clear - hpow9_q hUnit h11_v_le hSv; nra. }
  set (H8' := (J - 8)%nat).
  assert (hH8'_2 : (2 <= H8')%nat) by (unfold H8'; clear - hJ10; lia).
  assert (hJ_eq : J = (H8' + 8)%nat) by (unfold H8'; clear - hJ10; lia).
  assert (hUnit_H8' : z11 v * Q_of_nat (2 ^ H8') == 512).
  { rewrite hJ_eq, Nat.pow_add_r, Q_of_nat_mul, Qnat_pow2_8, Qnat_pow2_17 in hUnit.
    assert (h_eq : z11 v * (Q_of_nat (2 ^ H8') * 256) == 256 * (z11 v * Q_of_nat (2 ^ H8'))) by ring.
    clear - hUnit h_eq; lra. }
  pose proof (z1i hB_all) as hBud; rewrite hc249 in hBud.
  assert (hBud_v : (Q_of_nat m_end * 8) * z11 v == 249041 + 3 * z11 v - 2 * (a - b)).
  { change (z11 ((v1 ++ (WV :: y)) ++ [WQ; d1_tok; WV; WV])) with (z11 v) in hBud.
    rewrite Q_of_nat_mul, Q_of_nat_8 in hBud.
    clear - hBud; lra. }
  set (B := (1 + m_end * 4)%nat).
  assert (hB_cast : Q_of_nat B == 1 + Q_of_nat m_end * 4)
    by (unfold B; rewrite Q_of_nat_add, Q_of_nat_mul, Q_of_nat_1, Q_of_nat_4; reflexivity).
  assert (hB_lo : (243 * 2 ^ H8' <= B)%nat).
  { apply Q_of_nat_le.
    assert (h243 : Q_of_nat (243 * 2 ^ H8') == 243 * Q_of_nat (2 ^ H8')) by (rewrite Q_of_nat_mul; reflexivity).
    assert (h_b_v : (Q_of_nat B - Q_of_nat (243 * 2 ^ H8')) * z11 v ==
        z11 v + (1#2) * ((Q_of_nat m_end * 8) * z11 v) - 243 * (z11 v * Q_of_nat (2 ^ H8')))
      by (rewrite hB_cast, h243; ring).
    assert (h_pos_v : 0 < (Q_of_nat B - Q_of_nat (243 * 2 ^ H8')) * z11 v)
      by (clear - h_b_v hBud_v hUnit_H8' hAB hSv; lra).
    clear - h_pos_v hSv; nra. }
  assert (hB_hi : (B < 244 * 2 ^ H8')%nat).
  { apply Q_of_nat_lt.
    assert (h244 : Q_of_nat (244 * 2 ^ H8') == 244 * Q_of_nat (2 ^ H8')) by (rewrite Q_of_nat_mul; reflexivity).
    assert (h_b_v : (Q_of_nat (244 * 2 ^ H8') - Q_of_nat B) * z11 v ==
        244 * (z11 v * Q_of_nat (2 ^ H8')) - z11 v - (1#2) * ((Q_of_nat m_end * 8) * z11 v))
      by (rewrite hB_cast, h244; ring).
    assert (h_pos_v : 0 < (Q_of_nat (244 * 2 ^ H8') - Q_of_nat B) * z11 v)
      by (clear - h_b_v hBud_v hUnit_H8' hBA h11_v_le; lra).
    clear - h_pos_v hSv; nra. }
  set (A8' := (B - 243 * 2 ^ H8')%nat).
  assert (hA8'_lt : (A8' < 2 ^ H8')%nat) by (unfold A8'; clear - hB_lo hB_hi; lia).
  destruct (z0T H8' A8' hA8'_lt) as [hi8' hD_hi8'].
  assert (hA8'_mod : exists m', A8' = (1 + m' * 4)%nat).
  { assert (hpow4 : (2 ^ H8' = 2 ^ (H8' - 2) * 4)%nat)
      by (replace H8' with ((H8' - 2) + 2)%nat at 1 by (clear - hH8'_2; lia); rewrite Nat.pow_add_r; reflexivity).
    exists (m_end - 243 * 2 ^ (H8' - 2))%nat; unfold A8', B; clear - hB_lo hpow4; lia. }
  destruct hA8'_mod as [m_a8 hm_a8].
  assert (hLow' : exists w, hi8' = WQ :: WK :: w) by (rewrite hm_a8 in hD_hi8'; exact (z1K hD_hi8' hH8'_2)).
  assert (hD_ds' : zDg (1 + m_end * 4) J (hi8' ++ zTail8)).
  { pose proof (z0U hD_hi8' zDg_tail8) as hU.
    replace (A8' + 243 * 2 ^ H8')%nat with (1 + m_end * 4)%nat in hU by (unfold A8', B; clear - hB_lo; lia).
    rewrite <- hJ_eq in hU; exact hU. }
  set (u' := [WV; WV; WK; WV] ++ v).
  assert (h11_u' : z11 u' == (1#4) * z11 v) by (unfold u'; cbn [app z11]; ring).
  assert (hW_u' : z0W u' == (11#32) + (1#4) * z0W v) by (unfold u'; cbn [app z0W]; ring).
  pose proof (z17 hD_hi8') as hDef'.
  assert (hA8'_q : Q_of_nat A8' + 243 * Q_of_nat (2 ^ H8') == 1 + Q_of_nat m_end * 4).
  { assert (heq : (A8' + 243 * 2 ^ H8' = 1 + m_end * 4)%nat) by (unfold A8', B; clear - hB_lo; lia).
    pose proof (proj1 (Q_of_nat_eq _ _) heq) as hq.
    rewrite Q_of_nat_add, Q_of_nat_mul, Q_of_nat_add, Q_of_nat_1, Q_of_nat_mul, Q_of_nat_4 in hq.
    change (Q_of_nat 243) with 243 in hq; exact hq. }
  assert (hZ_new : z11 u' * z0Z hi8' <= (1273#10)).
  { assert (h1 : z0Z hi8' == Q_of_nat (2 ^ H8') - 1 - Q_of_nat A8') by (clear - hDef'; lra).
    assert (h2 : Q_of_nat A8' == 1 + Q_of_nat m_end * 4 - 243 * Q_of_nat (2 ^ H8')) by (clear - hA8'_q; lra).
    assert (h_z_prod : z11 u' * z0Z hi8' ==
        (244#4) * (z11 v * Q_of_nat (2 ^ H8')) - (1#2) * z11 v - (1#8) * ((Q_of_nat m_end * 8) * z11 v))
      by (rewrite h11_u', h1, h2; ring).
    clear - h_z_prod hUnit_H8' hBud_v hAB hSv; lra. }
  assert (hHeight' : z11 u' * Q_of_nat (2 ^ H8') == 128).
  { assert (h_eq : z11 u' * Q_of_nat (2 ^ H8') == (1#4) * (z11 v * Q_of_nat (2 ^ H8'))) by (rewrite h11_u'; ring).
    clear - h_eq hUnit_H8'; lra. }
  exists (u' ++ (hi8' ++ zTail8)); split.
  - assert (h_in_eq : (u ++ ((WQ :: WK :: w0) ++ zTail8)) ++ [WK] =
        (u ++ ((WQ :: WK :: w0) ++ [WQ; WQ; WK])) ++ [WK; WQ; WQ; WQ; WQ; WK])
      by (unfold zTail8; repeat rewrite <- app_assoc; reflexivity).
    assert (h_out_eq : u' ++ (hi8' ++ zTail8) = [WV; WV; WK; WV] ++ v ++ (hi8' ++ zTail8))
      by (unfold u'; repeat rewrite <- app_assoc; reflexivity).
    rewrite h_out_eq.
    refine (BStep_intro _ (m_end * 4) v a b J (hi8' ++ zTail8) _ hD_ds').
    replace ((m_end * 4) * 2)%nat with (m_end * 8)%nat by (clear; lia).
    rewrite h_in_eq; exact hB_all.
  - refine (BGood_intro H8' u' A8' hi8' hD_hi8' hHeight' ltac:(clear - h11_u' h11_v_le; lra)
      _ _ hLow' ltac:(clear - hW_u' hW_v hWu_max hZ_max; lra) hZ_new).
    + exists ([WK; WV] ++ v1 ++ (WV :: y) ++ [WQ; d1_tok; WV]).
      unfold u', v; repeat rewrite <- app_assoc; reflexivity.
    + assert (heq_u' : u' = ([WV; WV; WK; WV] ++ (v1 ++ (WV :: y))) ++ [WQ; d1_tok; WV; WV])
        by (unfold u', v; repeat rewrite <- app_assoc; reflexivity).
      rewrite heq_u'; exact (z1I _ _ hL_p3).
Qed.

Lemma z1P {A H : nat} {da : zW} (hD : zDg A H da) (hZ : A = 0%nat) :
  zTs da 0inf%sym = 0inf%sym.
Proof.
  induction hD as [| A H u _ IH | A H u _ _]; [reflexivity | | lia].
  cbn [zTs]; rewrite (IH ltac:(lia)), zDd; reflexivity.
Qed.

Lemma z1Q {A H : nat} {da : zW} (hD : zDg A H da) (hPos : (0 < A)%nat) :
  BRIncs false ((A - 1) * 2) 0inf%sym (zTs da 0inf%sym).
Proof.
  induction hD as [| A H u _ IH | A H u hDu IH]; [lia | |].
  - pose proof (BRIncs_short00 (IH ltac:(lia))) as hs.
    rewrite zDd in hs; cbn [zTs].
    replace ((A * 2 - 1) * 2)%nat with (2 + (A - 1) * 4)%nat by lia.
    exact hs.
  - destruct A as [| A].
    + cbn [Nat.add Nat.mul Nat.sub zTs]; rewrite (z1P hDu eq_refl).
      assert (hd : d1 *> 0inf%sym = one *> 0inf%sym)
        by (unfold d1, one; cbn; rewrite <- const_unfold; reflexivity).
      rewrite hd; exact (BRIncs_zero 0inf%sym).
    + pose proof (IH ltac:(lia)) as hIH.
      replace ((S A - 1) * 2)%nat with (A * 2)%nat in hIH by lia.
      pose proof (BRIncs_short10 hIH) as hs.
      rewrite zDd in hs; cbn [zTs].
      replace ((1 + S A * 2 - 1) * 2)%nat with (4 + A * 4)%nat by lia.
      exact hs.
Qed.

Lemma z1R {orig out : zW} (hS : BStep orig out) :
  exists r, BRIncs false 128 (zTs (zP33 ++ orig) 0inf%sym) r /\
    zTs (zP33 ++ out) 0inf%sym = zTs [WV; WV; WQ; WV] r.
Proof.
  destruct hS as [orig n v a b J ds hI hD].
  assert (hB : BRIncs false (n * 2) 0inf%sym (zTs ds 0inf%sym)).
  { replace (n * 2)%nat with ((1 + n - 1) * 2)%nat by lia; exact (z1Q hD ltac:(lia)). }
  assert (hR_orig : BRIncs false N_249044 (zTs orig 0inf%sym) (zTs (v ++ ds) 0inf%sym)).
  { pose proof (z1l hI hB) as hR.
    rewrite !z0S in hR; cbn [zTs] in hR; rewrite zDd in hR.
    rewrite z0S; exact hR. }
  pose proof (zBRIncs_P33 hR_orig) as hR_p33.
  exists (zTs (zOut33 ++ (v ++ ds)) 0inf%sym); split.
  - rewrite (z0S zP33 orig), (z0S zOut33 (v ++ ds)); exact hR_p33.
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
  exists H, Binary (Pos.to_nat p) H (zTs (zPf_pos p) 0inf%sym).
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
  - inversion h; reflexivity.
  - destruct u as [| x u]; [destruct w; discriminate |].
    destruct w, x; try discriminate; cbn [zSw app] in *; f_equal; exact (IH _ _ h).
Qed.

Definition z1U (w : Word) : bool :=
  match w with WK => true | _ => false end.

Lemma z1V (u : zW) (h : forallb z1U u = true) :
  zTs u 0inf%sym = 0inf%sym.
Proof.
  induction u as [| w u IH]; [reflexivity |].
  destruct w; cbn [forallb z1U] in h; try discriminate.
  cbn [zTs]; rewrite (IH h), zDd; reflexivity.
Qed.

Notation Choice := TM1.Choice.

Notation CT := TM1.CT.

Notation CP0 := TM1.CP0.

Notation CP1 := TM1.CP1.

Notation CS00 := TM1.CS00.

Notation CS01 := TM1.CS01.

Notation CS10 := TM1.CS10.

Notation CS11 := TM1.CS11.

Notation COC0 := TM1.COC0.

Notation COC1 := TM1.COC1.

Notation CEC := TM1.CEC.

Notation CSP0 := TM1.CSP0.

Notation CSP1 := TM1.CSP1.

Notation CSC0 := TM1.CSC0.

Notation CSC1 := TM1.CSC1.

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
  | CT => k - 2
  | CP0 | CP1 | CSP0 | CSP1 => k - 1
  | CS00 | CS01 => (k - 2) / 4
  | CS10 | CS11 => (k - 4) / 4
  | COC0 _ | CSC0 _ => (k - 3) / 4
  | COC1 _ | CSC1 _ => (k - 5) / 4
  | CEC _ => (k - 6) / 2
  end%N.

Definition z1W (ch : Choice) (n : N) : N :=
  match ch with
  | CT => 2 + n
  | CP0 | CP1 | CSP0 | CSP1 => 1 + n
  | CS00 | CS01 => 2 + n * 4
  | CS10 | CS11 => 4 + n * 4
  | COC0 _ | CSC0 _ => 3 + n * 4
  | COC1 _ | CSC1 _ => 5 + n * 4
  | CEC _ => 6 + n * 2
  end%N.

Definition z1X (ch : Choice) (n : N) : N :=
  match ch with
  | CT | CP1 | CS01 | CS11 | CSP1 => 1 + n * 2
  | CP0 | CS00 | CS10 | CSP0 => n * 2
  | COC0 r | COC1 r => 1 + n * 2 ^ N.of_nat (1 + r)
  | CEC r => 1 + (1 + n * 2) * 2 ^ N.of_nat (1 + r)
  | CSC0 r | CSC1 r => 1 + n * 2 ^ N.of_nat (2 + r)
  end%N.

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

Lemma N_to_nat_pow2 (k : nat) : N.to_nat (2 ^ N.of_nat k)%N = (2 ^ k)%nat.
Proof.
  induction k as [| k IH]; [reflexivity |].
  replace (N.of_nat (S k)) with (1 + N.of_nat k)%N by lia.
  rewrite N.pow_add_r; change (2 ^ 1)%N with 2%N.
  rewrite N2Nat.inj_mul, IH; cbn [Nat.pow N.to_nat]; lia.
Qed.

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

Lemma z21 (cs : list Choice) :
  forall (s : bool) (k : N) (u v : zW), z20 cs s k u = Some v ->
    BRIncs s (N.to_nat k) (zTs u 0inf%sym) (zTs v 0inf%sym).
Proof.
  induction cs as [| ch0 cs IH]; intros s k u v hE; cbn [z20] in hE.
  - destruct s; [discriminate | cbn [negb] in hE].
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
  - destruct (Bool.eqb s (zInS ch0)) eqn:hs; [| discriminate].
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
  exists r, BRIncs false 128 (zTs u 0inf%sym) r /\ zTs v 0inf%sym = zTs [WV; WV; WQ; WV] r.
Proof.
  unfold z22 in h.
  destruct (z20 cs false 128%N (u ++ [WK])) as [w |] eqn:hE; [| discriminate].
  inversion h; subst v; clear h.
  exists (zTs w 0inf%sym); split; [| reflexivity].
  pose proof (z21 cs false 128%N (u ++ [WK]) w hE) as hR.
  change (N.to_nat 128%N) with 128%nat in hR.
  rewrite z0S in hR; cbn [zTs] in hR; rewrite zDd in hR.
  exact hR.
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
    Rounds (zTs u 0inf%sym) (zTs v 0inf%sym).
Proof.
  induction cs as [| c cs IH]; intros u v h; cbn [z24] in h.
  - inversion h; subst v; exact (Rounds_refl _).
  - destruct (z22 c u) as [w |] eqn:hW; [| discriminate].
    destruct (z23 c u w hW) as [r [hR hEq]].
    refine (Rounds_next hR _).
    rewrite <- hEq; exact (IH w v h).
Qed.

Definition z26 (w : Word) : bool :=
  match w with WV => false | _ => true end.

Lemma z27 (ds : zW) (h : forallb z26 ds = true) :
  exists A, zDg A (length ds) ds.
Proof.
  induction ds as [| w ds IH]; [exists 0%nat; exact zDg_nil |].
  destruct w; cbn [forallb z26] in h; [discriminate | |].
  - destruct (IH h) as [A hI]; exists (A * 2)%nat; exact (zDg_zero hI).
  - destruct (IH h) as [A hI]; exists (1 + A * 2)%nat; exact (zDg_one hI).
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
  induction u as [| w u IH]; [cbn; push_Q_of_nat; lra |].
  destruct w; cbn [z11 zN11 zP11].
  - rewrite (zP2 (zN11 u)), Q_of_nat_add; clear - IH; lra.
  - rewrite (zP2 (zP11 u)), Q_of_nat_add; clear - IH; lra.
  - rewrite (zP2 (zP11 u)), Q_of_nat_add; clear - IH; lra.
Qed.

Fixpoint zWU (u : zW) : N :=
  match u with
  | [] => 0
  | WV :: u' => (zWU u' + 1) / 2
  | WK :: u' => 90112 + 2 * zWU u'
  | WQ :: u' => 65536 + 2 * zWU u'
  end%N.

Lemma Q_of_N_add (a b : N) : Q_of_N (a + b) == Q_of_N a + Q_of_N b.
Proof. unfold Q_of_N; rewrite N2Z.inj_add, inject_Z_plus; reflexivity. Qed.

Lemma Q_of_N_mul (a b : N) : Q_of_N (a * b) == Q_of_N a * Q_of_N b.
Proof. unfold Q_of_N; rewrite N2Z.inj_mul, inject_Z_mult; reflexivity. Qed.

Lemma Q_of_N_le (a b : N) : (a <= b)%N <-> Q_of_N a <= Q_of_N b.
Proof. unfold Q_of_N, Qle; cbn; lia. Qed.

Lemma zWU_ge (u : zW) :
  65536 * z0W u <= Q_of_N (zWU u).
Proof.
  induction u as [| w u IH]; [cbn [z0W zWU]; change (Q_of_N 0) with 0; lra |].
  destruct w; cbn [z0W zWU].
  - assert (hdiv : (zWU u <= 2 * ((zWU u + 1) / 2))%N)
      by (pose proof (N.div_mod (zWU u + 1) 2 ltac:(lia));
          pose proof (N.mod_lt (zWU u + 1) 2 ltac:(lia)); lia).
    pose proof (proj1 (Q_of_N_le _ _) hdiv) as hdiv_q; rewrite Q_of_N_mul in hdiv_q.
    change (Q_of_N 2) with 2 in hdiv_q; clear - IH hdiv_q; lra.
  - rewrite Q_of_N_add, Q_of_N_mul.
    change (Q_of_N 90112) with 90112; change (Q_of_N 2) with 2; clear - IH; lra.
  - rewrite Q_of_N_add, Q_of_N_mul.
    change (Q_of_N 65536) with 65536; change (Q_of_N 2) with 2; clear - IH; lra.
Qed.

Fixpoint zZNat (u : zW) : N :=
  match u with
  | [] => 0
  | WV :: u' => zZNat u'
  | WK :: u' => 1 + 2 * zZNat u'
  | WQ :: u' => 2 * zZNat u'
  end%N.

Lemma zZNat_eq (u : zW) (h : forallb z26 u = true) :
  z0Z u == Q_of_N (zZNat u).
Proof.
  induction u as [| w u IH]; [cbn [z0Z zZNat]; reflexivity |].
  destruct w; cbn [forallb z26] in h; [discriminate | |].
  - cbn [z0Z zZNat]; rewrite (IH h), Q_of_N_add, Q_of_N_mul.
    change (Q_of_N 1) with 1; change (Q_of_N 2) with 2; lra.
  - cbn [z0Z zZNat]; rewrite (IH h), Q_of_N_mul.
    change (Q_of_N 2) with 2; lra.
Qed.

Fixpoint zLastV (u : zW) : bool :=
  match u with
  | [] => false
  | x :: u' =>
      match u' with
      | [] => match x with WV => true | _ => false end
      | _ :: _ => zLastV u'
      end
  end.

Lemma zLastV_eq (u : zW) : zLastV u = true -> exists w, u = w ++ [WV].
Proof.
  induction u as [| x u' IH]; intros h; [discriminate |].
  destruct u' as [| y ys].
  - destruct x; try discriminate; exists (@nil Word); reflexivity.
  - change (zLastV (y :: ys) = true) in h.
    destruct (IH h) as [w ->]; exists (x :: w); reflexivity.
Qed.

Definition zInitVV (u : zW) : bool :=
  match u with
  | WV :: WV :: u' => zLastV u'
  | _ => false
  end.

Lemma zInitVV_eq (u : zW) (h : zInitVV u = true) : exists w, u = WV :: WV :: (w ++ [WV]).
Proof.
  destruct u as [| [| |] [| [| |] u']]; try discriminate.
  destruct (zLastV_eq u' h) as [w ->]; exists w; reflexivity.
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
  (hTopLen : length hi_top = 16%nat)
  (hPow : (zP11 u + (length hi_low + 16) =? 7 + zN11 u)%nat = true)
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
  assert (hLen : length hi8 = (length hi_low + 16)%nat)
    by (unfold hi8; rewrite app_length, hTopLen; reflexivity).
  pose proof (z11_pow u) as h11_u.
  assert (hPow2 : (2 ^ zP11 u * 2 ^ length hi8 = 128 * 2 ^ zN11 u)%nat)
    by (rewrite <- Nat.pow_add_r, hLen, hPow, Nat.pow_add_r; reflexivity).
  assert (hPow2_q : Q_of_nat (2 ^ zP11 u) * Q_of_nat (2 ^ length hi8) == 128 * Q_of_nat (2 ^ zN11 u))
    by (pose proof (proj1 (Q_of_nat_eq _ _) hPow2) as hq;
        rewrite !Q_of_nat_mul, Q_of_nat_128 in hq; exact hq).
  pose proof (proj1 (Q_of_nat_lt 0 (2 ^ zN11 u)) (zPp (zN11 u))) as hPos; rewrite Q_of_nat_0 in hPos.
  assert (hHeight : z11 u * Q_of_nat (2 ^ length hi8) == 128)
    by (clear - h11_u hPow2_q hPos; nra).
  assert (hLe2 : (16 * 2 ^ zP11 u <= 2 ^ zN11 u)%nat)
    by (pose proof (Nat.pow_le_mono_r 2 (4 + zP11 u) (zN11 u) ltac:(lia) hU11_nat) as hp;
        rewrite Nat.pow_add_r in hp; cbn [Nat.pow] in hp; lia).
  pose proof (proj1 (Q_of_nat_le _ _) hLe2) as hLe2_q; rewrite Q_of_nat_mul, Q_of_nat_16 in hLe2_q.
  assert (hU11 : z11 u <= (1#16)) by (clear - h11_u hLe2_q hPos; nra).
  apply N.leb_le in hW_nat; pose proof (proj1 (Q_of_N_le _ _) hW_nat) as hW_q.
  assert (hc_w : Q_of_N 969932 == 969932) by reflexivity.
  pose proof (zWU_ge u) as hW_ge.
  assert (hW : z0W u <= (74#5)) by (clear - hW_q hc_w hW_ge; lra).
  destruct (z27 hi_low hD_low) as [A_low hI_low].
  destruct (z27 hi_top hD_top) as [A_top hI_top].
  destruct (zDw hI_low) as [hDw_low1 [hDw_low2 _]].
  destruct (zDw hI_top) as [hDw_top1 _].
  assert (hZ_low_le : z0Z hi_low <= z11 hi_low)
    by (pose proof (z12 hi_low) as h1; pose proof (proj1 (proj2 (proj2 (zWn hi_low)))) as h2;
        clear - h1 h2 hDw_low1 hDw_low2; lra).
  assert (h11_top : z11 hi_top == 65536)
    by (rewrite hTopLen, Qnat_pow2_16 in hDw_top1; exact hDw_top1).
  pose proof (proj1 (zDw hI)) as h11_hi8.
  pose proof (z16 hi_low hi_top) as h11_split; fold hi8 in h11_split.
  assert (h_u_low : z11 u * z11 hi_low == (1#512)).
  { assert (h_eq : z11 u * Q_of_nat (2 ^ length hi8) == 65536 * (z11 u * z11 hi_low))
      by (rewrite <- h11_hi8, h11_split, h11_top; ring).
    clear - hHeight h_eq; lra. }
  pose proof (z14 hi_low hi_top) as hZ_split; fold hi8 in hZ_split.
  pose proof (zZNat_eq hi_top hD_top) as hZ_top_eq.
  apply N.leb_le in hZ_nat; pose proof (proj1 (Q_of_N_le _ _) hZ_nat) as hZ_top_q.
  rewrite Q_of_N_mul, Q_of_N_add in hZ_top_q.
  change (Q_of_N 10) with 10 in hZ_top_q;
  change (Q_of_N 1) with 1 in hZ_top_q;
  change (Q_of_N 651776) with 651776 in hZ_top_q.
  pose proof (zSp u) as hSu.
  assert (hZ : z11 u * z0Z hi8 <= (1273#10)).
  { assert (h_uz_split : z11 u * z0Z hi8 == z11 u * z0Z hi_low + (z11 u * z11 hi_low) * z0Z hi_top)
      by (rewrite hZ_split; ring).
    assert (h_uz_low : z11 u * z0Z hi_low <= z11 u * z11 hi_low) by (clear - hSu hZ_low_le; nra).
    assert (h_uz_top : (z11 u * z11 hi_low) * z0Z hi_top == (1#512) * Q_of_N (zZNat hi_top))
      by (rewrite h_u_low, hZ_top_eq; ring).
    clear - h_uz_split h_uz_low h_u_low h_uz_top hZ_top_q; lra. }
  exact (BGood_intro (length hi8) u A hi8 hI hHeight hU11
    (zInitVV_eq u hEnd) hLu (zInitQK_eq hi_low hi_top hLo) hW hZ).
Qed.

Fixpoint zHExec (u : zW) (k : N) : option zW :=
  if (k =? 0)%N then Some u
  else
    match u with
    | [] => None
    | WV :: u' =>
      match zHExec u' (k * 2)%N with
      | Some v => Some (WV :: v)
      | None => None
      end
    | WK :: u' =>
      let m := (k / 2)%N in
      if (k =? m * 2)%N then
        match zHExec u' m with
        | Some v => Some (WK :: v)
        | None => None
        end
      else
        match zHExec u' m with
        | Some v => Some (WQ :: v)
        | None => None
        end
    | WQ :: u' =>
      let m := (k / 2)%N in
      if (k =? m * 2)%N then
        match zHExec u' m with
        | Some v => Some (WQ :: v)
        | None => None
        end
      else
        match zHExec u' (1 + m)%N with
        | Some v => Some (WK :: v)
        | None => None
        end
    end.

Lemma zHExec_ok (u : zW) :
  forall (k : N) (v : zW), zHExec u k = Some v ->
    Side ([ch]^^(N.to_nat k)) (zTs u 0inf%sym) (zTs v 0inf%sym).
Proof.
  induction u as [| w u IH]; intros k v h; cbn [zHExec] in h.
  - destruct (N.eqb_spec k 0) as [-> |]; [| discriminate].
    inversion h; subst v; exact (Side_nil _).
  - destruct (N.eqb_spec k 0) as [-> | hne0].
    + inversion h; subst v; exact (Side_nil _).
    + destruct w.
      * destruct (zHExec u (k * 2)%N) as [v' |] eqn:hE; [| discriminate].
        inversion h; subst v; clear h; cbn [zTs].
        pose proof (IH (k * 2)%N v' hE) as hIH.
        replace (N.to_nat (k * 2)%N) with (N.to_nat k * 2)%nat in hIH by lia.
        exact (zSc (zS3 (N.to_nat k)) hIH).
      * pose proof (N.div_mod k 2 ltac:(lia)) as hdm.
        pose proof (N.mod_lt k 2 ltac:(lia)) as hlt.
        destruct (N.eqb_spec k ((k / 2) * 2)) as [hk | hk].
        -- destruct (zHExec u (k / 2)%N) as [v' |] eqn:hE; [| discriminate].
           inversion h; subst v; clear h; cbn [zTs].
           replace (N.to_nat k) with (N.to_nat (k / 2)%N * 2)%nat by lia.
           exact (zSc (zH_d0_even (N.to_nat (k / 2)%N)) (IH _ _ hE)).
        -- destruct (zHExec u (k / 2)%N) as [v' |] eqn:hE; [| discriminate].
           inversion h; subst v; clear h; cbn [zTs].
           replace (N.to_nat k) with (1 + N.to_nat (k / 2)%N * 2)%nat by lia.
           exact (zSc (zH_d0_odd (N.to_nat (k / 2)%N)) (IH _ _ hE)).
      * pose proof (N.div_mod k 2 ltac:(lia)) as hdm.
        pose proof (N.mod_lt k 2 ltac:(lia)) as hlt.
        destruct (N.eqb_spec k ((k / 2) * 2)) as [hk | hk].
        -- destruct (zHExec u (k / 2)%N) as [v' |] eqn:hE; [| discriminate].
           inversion h; subst v; clear h; cbn [zTs].
           replace (N.to_nat k) with (N.to_nat (k / 2)%N * 2)%nat by lia.
           exact (zSc (zH_d1_even (N.to_nat (k / 2)%N)) (IH _ _ hE)).
        -- destruct (zHExec u (1 + k / 2)%N) as [v' |] eqn:hE; [| discriminate].
           inversion h; subst v; clear h; cbn [zTs].
           pose proof (IH (1 + k / 2)%N v' hE) as hIH.
           replace (N.to_nat (1 + k / 2)%N) with (1 + N.to_nat (k / 2)%N)%nat in hIH by lia.
           replace (N.to_nat k) with (1 + N.to_nat (k / 2)%N * 2)%nat by lia.
           exact (zSc (zH_d1_odd (N.to_nat (k / 2)%N)) hIH).
Qed.

Lemma z2q {orig out : zW} (hS : BStep orig out) :
  zCf (zTs (zP33 ++ orig) 0inf%sym) ==>+ zCf (zTs (zP33 ++ out) 0inf%sym).
Proof.
  destruct (z1R hS) as [r [hI hEq]]; rewrite hEq; exact (z2p hI).
Qed.

Lemma z2r {r r' : side} (h : Rounds r r') :
  zCf r ==>* zCf r'.
Proof.
  induction h as [r | r s t0 hR _ IH]; [exact (evstep_refl _ _) |].
  exact (evstep_trans _ _ _ _ (progress_evstep _ _ _ (z2p hR)) IH).
Qed.

Local Close Scope Q_scope.

Definition z29_0813 : zW := [WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WK;WV;WV;WV;WK;WV;WQ;WQ;WQ;WV;WK;WQ;WQ;WK;WQ;WQ;WK;WK;WK;WK;WK;WK;WQ].

Definition z2a_0813 : list (list Choice) := [
  [CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CP0;CT;CT;(COC0 0);(CSC0 0);CSP1;CP1;(COC1 0);CSP0;CS11;CP0;CS11;CP0;CS10;CS10;CS00;CS10;CS10;CP0];
  [CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS10;CT;CT;(COC0 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;CP0;CP1;(COC0 0);CSP0;CS10;CS10;CP0;CP1;CP0;CS10;CP1;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CP1;CT;CT;(COC0 0);CSP1;CT;CT;CT;CP0;CP1;CP0;CS10;CS11;CP0;CP0;CP0;CS01;CP1;CP0;CP0;CS01;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;(COC0 0);CSP0;CS10;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CP1;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CP0;CP1;CP0;CS11;CP1;CP0;CP0;CP0;CP0;CP1;CP0;CP0;CP0;CS01;CP1;CP0;CS10;CP0;CS01;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP0;CT;CT;CP0;CS10;CP0;CS00;CS00;CS10;CS00;CP1;CP0;CS10;CP0;CS00;CS00;CP0;CS00;CS10;CS00;CS00;CS10;CS10;CP0;CS01;CP0;CS10;CP0;CP1;CP0;CP0;CP0;CP1;CP0;CS10;CS10;CS00;CP0;CS01;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;(COC0 0);CSP0;CS10;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP0;CS10;CP0;CT;(COC1 0);CSP1;(COC1 0);CSP0;(CEC 0);CSP0;CP0;CS00;CP1;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 1);CSP0;CT;CT;CP0;CS10;CS10;CS10;CS00;CS11;CP0;CS10;CP1;CP0;CS10;CS10;CS10;CS11;CP1;CP1;CP1;CP0;CS10;CS01;CP0;CS10;CP0;CP1;CP0;CP0;CP0;CP1;CP0;CS10;CP1;CP0;CS10;CS11;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP1;CT;(COC0 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);(CSC1 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CP1;CP0;CS11;(COC0 0);CSP1;CT;CT;CP1;CP1;CT;CT;CT;CT;(COC0 1);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CP1;CT;CT;CP0;CS10;CS11;CP0;CS10;CS10;CP0;CS00;CS10;CP0;CP0;CS00;CS10;CP1;CP1;CP0;CS11;CP1;CP0;CS10;CP1;CP0;CS10;CS10;CS00;CS01;CP1;CP1;CP1;CP0;CS10;CS01;CP0;CS10;CP0;CP1;CP0;CP0;CP0;CS01;CP1;CP0;CP0;CS01;CP0;CS10;CS11;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;(COC0 0);CSP0;CS10;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CP1;CT;CP1;(COC1 0);CSP0;CS11;CT;(COC0 0);CSP0;CS11;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CP0;CS10;CT;CT;CT;CT;(COC0 1);CSP1;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CP1;CT;CT;CP0;CS10;CP0;CS00;CS00;CP0;CS00;CS10;CS01;CP0;CS11;CP1;CP0;CS11;CP1;CP0;CP0;CS00;CS01;CP1;CP1;CP0;CP0;CP1;CP1;CP1;CP0;CP1;CP1;CP0;CS11;CP1;CP0;CS10;CP1;CP0;CS10;CS10;CS00;CS01;CP1;CP1;CP1;CP0;CS10;CS01;CP0;CS10;CP0;CP1;CP0;CP0;CP0;CS01;CP1;CP0;CS10;CP0;CS01;CP0;CS10;CS01;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;(COC1 0);CSP0;CS10;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP1;(COC1 0);(CSC1 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 0);CSP0;(CEC 0);(CSC0 1);CSP1;CT;(COC0 0);CSP1;CT;CT;(COC0 0);CSP0;CS10;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CP0;CS10;CT;CT;CT;CT;(COC0 1);CSP1;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP0;CT;CP0;CT;CT;CP0;CS10;CS10;CS10;CS00;CP0;CS00;CS00;CS01;CP0;CS10;CP1;CP0;CS10;CS10;CP1;CP0;CS11;CP0;CP1;CP0;CP1;CP0;CP0;CS01;CP1;CP1;CP0;CS10;CP1;CP1;CP0;CS10;CS01;CP1;CP1;CP0;CS10;CS00;CS00;CS00;CS00;CS10;CS00;CS00;CS10;CS00;CS10;CS11;CP1;CP0;CP0;CS00;CP0;CS00;CS10;CS10;CS00;CP1;CP1;CP0;CS10;CP1;CP0;CS10;CS10;CS00;CS01;CP1;CP1;CP1;CP0;CS10;CS01;CP0;CS10;CP0;CP1;CP0;CP0;CP0;CP1;CP0;CS10;CS10;CS00;CP0;CS01;CP0;CS10;CS01;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;(COC0 0);CSP0;CS10;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CP1;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);(CSC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;CP1;(COC1 1);CSP0;CS10;(CEC 0);CSP1;CT;CT;CP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP1;CT;CT;CT;CP0;CT;CT;CT;CP0;CS10;CS10;CS00;CP0;CS00;CP0;CP1;CT;CT;(COC0 0);(CSC1 0);CSP0;CS11;CP0;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CP0;CS10;CT;CT;CT;CT;(COC0 1);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 1);CSP0;CT;CP0;CT;CT;CP0;CP1;CP0;CS10;CS10;CP1;CP0;CS11;CP0;CP1;CP0;CP1;CP1;CP1;CP0;CP1;CP0;CP0;CP0;CP0;CS00;CS10;CS00;CP1;CP0;CS10;CS11;CP0;CP0;CS00;CP0;CP0;CP1;CP1;CP0;CS10;CP1;CP1;CP0;CS10;CS01;CP1;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CP0;CS01;CP0;CS10;CS10;CS10;CS10;CP0;CS01;CP1;CP0;CS11;CP1;CP0;CS10;CP1;CP0;CS10;CS10;CS00;CS01;CP1;CP1;CP1;CP0;CS10;CS01;CP0;CS10;CP0;CP1;CP0;CP0;CP0;CP1;CP0;CS10;CP1;CP0;CS10;CS11;CP0;CS10;CS01;CP1;CP0];
  [CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;(COC0 0);(CSC0 0);CSP1;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;(COC1 0);(CSC1 0);CSP1;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;(COC1 0);CSP0;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CS11;CT;CT;(COC0 0);CSP0;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CS10;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP1;(COC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;(COC1 1);CSP0;CT;CT;CT;(COC0 0);CSP0;CS11;CT;(COC0 0);CSP1;CT;CT;(COC0 0);CSP0;CT;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;CT;CT;(COC0 0);CSP0;CT;CT;CT;CT;CT;CT;CT;(COC0 0);(CSC1 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CP1;CT;(COC0 0);CSP1;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CP0;CT;CT;CP1;CT;(COC0 0);CSP0;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CT;CP0;CT;CT;CT;CT;CT;CT;CT;CT;(COC0 0);CSP0;CT;CP1;CP1;(COC1 0);CSP0;CT;(COC1 0);CSP1;CT;(COC0 0);CSP1;CT;(COC0 0);CSP1;CP0;CS10;CT;CT;CT;CT;(COC0 1);CSP1;CT;CT;CT;CT;CT;CT;(COC0 0);CSP1;CT;CT;CP1;CT;CP0;CT;CT;CP0;CS10;CP0;CS00;CS00;CP0;CS00;CP0;CS01;CP1;CP1;CP1;CP0;CS10;CS00;CS01;CP0;CP0;CS01;CP0;CP0;CS00;CP0;CP0;CS01;CP1;CP0;CP1;CP0;CS11;CP1;CP1;CP0;CP0;CP1;CP0;CS10;CS10;CS01;CP1;CP0;CS10;CS00;CS00;CP0;CS00;CS00;CP1;CP1;CP0;CS10;CS00;CS11;CP0;CS10;CS01;CP0;CP0;CS00;CS00;CP1;CP1;CP1;CP0;CS11;CP0;CS10;CS10;CS10;CP0;CP0;CS00;CS10;CS00;CP1;CP0;CS10;CS11;CP0;CS10;CS10;CP0;CS00;CS10;CS01;CP0;CS11;CP1;CP1;CP0;CS10;CP1;CP1;CP0;CS10;CS01;CP1;CP1;CP1;CP1;CP1;CP1;CP1;CP1;CP0;CP1;CP0;CP0;CS00;CP0;CS00;CS10;CS00;CS10;CP1;CP1;CP0;CS10;CP1;CP0;CS10;CS10;CS00;CS01;CP1;CP1;CP1;CP0;CS10;CS01;CP0;CS10;CP0;CP1;CP0;CP0;CP0;CS01;CP1;CP0;CP0;CS01;CP0;CS10;CS11;CP0;CS10;CS01;CP1;CP0]
].

Definition z2b_0813 : zW := [WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WK;WK;WV;WV;WQ;WV;WQ;WV;WV;WV;WK;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WQ;WV;WV;WV;WV;WK;WQ;WV;WV;WQ;WV;WV;WQ;WQ;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WQ;WV;WV;WK;WV;WV;WV;WV;WK;WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WK;WV;WV;WK;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WQ;WV;WV;WV;WV;WV;WK;WV;WQ;WV;WK;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WK;WQ;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WQ;WV;WV;WQ;WV;WV;WK;WV;WV;WK;WV;WV;WQ;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WQ;WV;WK;WK;WV;WK;WV;WK;WV;WV;WV;WV;WQ;WK;WK;WV;WV;WK;WV;WV;WK;WV;WV;WK;WV;WV;WV;WV;WQ;WV;WV;WV;WV;WV;WV;WQ;WQ;WK;WV;WV;WQ;WK;WK;WV;WK;WK;WV;WV;WV;WQ;WK;WQ;WV;WQ;WK;WV;WV;WK;WK;WV;WV;WV;WV;WQ;WV;WQ;WQ;WQ;WV;WV;WK;WQ;WK;WV;WV;WQ;WQ;WV;WQ;WQ;WV;WK;WQ;WK;WV;WQ;WV;WV;WV;WQ;WV;WV;WV;WQ;WK;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WV;WK;WV;WK;WQ;WK;WQ;WV;WV;WV;WQ;WV;WV;WQ;WQ;WK;WK;WV;WV;WV;WV;WQ;WK;WV;WQ;WV;WV;WV;WV;WV;WK;WV;WV;WV;WK;WV;WQ;WQ;WV;WQ;WK;WV;WV].

Definition z2c_low_0813 : zW := [WQ;WK;WK;WK;WK;WK;WQ;WK;WQ;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WQ;WK;WQ;WK;WK;WQ;WK;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WQ;WQ;WK;WQ;WQ;WQ;WK;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WK;WK;WK;WQ;WQ;WQ;WK;WK;WK;WK;WQ;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WK;WK;WK;WK;WK;WK;WK;WK;WK;WQ;WQ;WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WK;WQ;WK;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WK;WK;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WK;WQ;WQ;WK;WK;WQ;WQ;WK;WK;WK;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WK;WK;WK;WQ;WQ;WK;WQ;WK;WK;WK;WK;WQ;WQ;WQ;WK;WK;WQ;WK;WK;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WK;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WQ;WK;WQ;WQ;WK;WK;WK;WK;WK;WQ;WK;WQ;WQ;WQ;WQ;WK;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WQ;WK;WK;WK;WK;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WQ;WK;WK;WQ;WQ;WK;WK;WQ;WK;WQ;WQ;WQ;WK].

Definition z2c_top_0813 : zW := [WQ;WK;WQ;WK;WQ;WQ;WQ;WQ;WK;WK;WQ;WK;WQ;WQ;WK;WK].

Definition z2c_0813 : zW := z2c_low_0813 ++ z2c_top_0813.

Lemma z2d_0813 :
  Rounds (zTs z29_0813 0inf%sym) (zTs (zP33 ++ (z2b_0813 ++ (z2c_0813 ++ zTail8))) 0inf%sym).
Proof.
  apply (z25 z2a_0813 z29_0813 (zP33 ++ (z2b_0813 ++ (z2c_0813 ++ zTail8)))).
  vm_compute; reflexivity.
Qed.

Lemma z2e_0813 :
  BGood (z2b_0813 ++ (z2c_0813 ++ zTail8)).
Proof.
  unfold z2c_0813.
  apply (z28 z2b_0813 z2c_low_0813 z2c_top_0813); vm_compute; reflexivity.
Qed.

Definition zPre_0813 : zW := [WV;WV;WV;WV;WV;WV;WV;WK;WV;WV;WQ;WV;WV;WQ;WK;WV;WV;WV;WK;WV;WQ;WQ;WQ;WV;WK;WQ;WQ;WK;WQ;WQ;WK;WK;WK;WK;WK;WK;WK].

Definition zCk0_0813 : CCfg := mkCCfg B S0 [] [].

Definition zCk9_0813 : CCfg := mkCCfg C S1 [0;1]%sym [0;0;0;0;1;1;0;1;0;1;1;0;0;1;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;0;0;0;1;1;0;0;1;1;0;0;0;0;1;1;0;0;1;1;0;0;1;1;0;0;1;1;0;0;1;1;0;0;1;1;0;0;1;1;0;0;0;0;1;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;0;1;0;0;0;1;1;0;0;1;1;0;0;1;1;0;0;0;0;1;1;0;0;1;0;1;0;1;0;1;1;0;0;0;0;1;0;1;0;0;0;1;0;1]%sym.

Fixpoint zTs_list (u : zW) : list Sym :=
  match u with
  | [] => []
  | WV :: u' => bt ++ zTs_list u'
  | WK :: u' => d0 ++ zTs_list u'
  | WQ :: u' => d1 ++ zTs_list u'
  end.

Lemma zTs_list_eq (u : zW) (r : side) :
  zTs u r = zTs_list u *> r.
Proof.
  induction u as [| w u IH]; [reflexivity |].
  destruct w; cbn [zTs zTs_list]; rewrite IH, Str_app_assoc; reflexivity.
Qed.

Lemma zero_cat_0inf (n : nat) : repeat S0 n *> 0inf%sym = 0inf%sym.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [repeat Str_app]; rewrite IH, <- const_unfold; reflexivity.
Qed.

Lemma c_to_cfg_zCk9_0813 :
  c_to_cfg zCk9_0813 = zCL lh (w_pre *> zTs zPre_0813 0inf%sym).
Proof.
  unfold c_to_cfg, zCL, lh; rewrite zTs_list_eq, <- !Str_app_assoc.
  cbn [cq chead cleft zCk9_0813].
  change (([1; 0; 1]%sym *> 0inf%sym) <{{C}} (([0]%sym ++ w_pre ++ zTs_list zPre_0813) *> 0inf%sym))
    with (C;; ([0; 1]%sym *> 0inf%sym) {{1}} (([0]%sym ++ w_pre ++ zTs_list zPre_0813) *> 0inf%sym)).
  f_equal; f_equal.
  transitivity ((cright zCk9_0813 ++ repeat S0 15) *> 0inf%sym).
  - rewrite Str_app_assoc, zero_cat_0inf; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma z0E_0813 : c_to_cfg zCk0_0813 ==>+ zCf (zTs z29_0813 0inf%sym).
Proof.
  assert (h_steps : c_to_cfg zCk0_0813 ==>+ c_to_cfg zCk9_0813)
    by (apply (c_steps_pos_spec 87731%positive); vm_compute; reflexivity).
  rewrite c_to_cfg_zCk9_0813 in h_steps.
  assert (h_side : Side ([ch]^^16) (zTs zPre_0813 0inf%sym) (zTs z29_0813 0inf%sym))
    by (exact (zHExec_ok zPre_0813 16%N z29_0813 ltac:(vm_compute; reflexivity))).
  exact (progress_trans _ _ _ _ h_steps (zW_pre_full h_side)).
Qed.

Lemma canon_nonhalt_inv :
  ~ halts TM1.tm (zCf (zTs (zP33 ++ (z2b_0813 ++ (z2c_0813 ++ zTail8))) 0inf%sym)).
Proof.
  apply (progress_nonhalt_cond TM1.tm zW (z2b_0813 ++ (z2c_0813 ++ zTail8))
    (fun w => zCf (zTs (zP33 ++ w) 0inf%sym)) BGood).
  - intros w hG; destruct (z1N hG) as [w' [hS hG']].
    exists w'; split; [exact (z2q hS) | exact hG'].
  - exact z2e_0813.
Qed.

Lemma canon_nonhalt : ~ halts TM1.tm (c_to_cfg zCk0_0813).
Proof.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [exact (progress_evstep _ _ _ z0E_0813) | exact (z2r z2d_0813)].
  - exact canon_nonhalt_inv.
Qed.

Definition state_map (q: Q) := match q with A => F | B => A | C => B | D => C | E => D | F => E end.

Lemma perm: Perm TM1.tm tm state_map.
Proof. split.
- intros [] [] H; cbn in *; try discriminate; reflexivity.
- intros [] [] s d q H; cbn in H; inversion H; subst; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. exact (perm_nonhalt' TM1.tm tm state_map B tape0 perm canon_nonhalt). Qed.

End TM3.
Print Assumptions TM3.nonhalt.



Module TM4.
Import List.

Import Bool.

Import String.

Import PeanoNat.

Import Lia.

Import QArith.

Import Lqa.

Notation Rat := QArith_base.Q.

Import BusyCoq.Individual62.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB1RC_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LA---").

Notation cconfig_steps := TM1.cconfig_steps.

Notation cconfig_steps_spec := TM1.cconfig_steps_spec.

Notation t := TM1.t.

Notation d0 := TM1.d0.

Notation d1 := TM1.d1.

Notation one := TM1.one.

Notation lh := TM1.lh.

Notation w_word := TM1.w_word.

Notation w_rest := TM1.w_rest.

Notation w_base := TM1.w_base.

Notation zDd := TM1.zDd.

Notation Call := TM1.Call.

Notation ch := TM1.ch.

Notation cj := TM1.cj.

Notation cp := TM1.cp.

Notation zCs := TM1.zCs.

Notation zCw := TM1.zCw.

Notation zCR := TM1.zCR.

Notation zCL := TM1.zCL.

Notation zCf := TM1.zCf.

Notation z04 := TM1.z04.

Notation Side := TM1.Side.

Notation Side_nil := TM1.Side_nil.

Notation Side_cons := TM1.Side_cons.

Notation Seg := TM1.Seg.

Notation zLp' := TM1.zLp'.

Notation z06 := TM1.z06.

Notation z07 := TM1.z07.

Notation z08 := TM1.z08.

Notation z09 := TM1.z09.

Notation z0a := TM1.z0a.

Notation z0m_id := TM1.z0m_id.

Notation zSc := TM1.zSc.

Notation zSg := TM1.zSg.

Notation zS0 := TM1.zS0.

Notation zS4 := TM1.zS4.

Notation zS2 := TM1.zS2.

Notation zS5 := TM1.zS5.

Notation zS6 := TM1.zS6.

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

Notation z0b := TM1.z0b.

Notation z0c_p := TM1.z0c_p.

Notation z0c := TM1.z0c.

Notation zH2 := TM1.zH2.

Notation z0d := TM1.z0d.

Notation z0e := TM1.z0e.

Notation z0f := TM1.z0f.

Notation z0g := TM1.z0g.

Notation z0h := TM1.z0h.

Notation z0i := TM1.z0i.

Notation zH1 := TM1.zH1.

Notation zH3 := TM1.zH3.

Notation z0j := TM1.z0j.

Notation zH0 := TM1.zH0.

Notation zH4 := TM1.zH4.

Notation zC_base := TM1.zC_base.

Notation zO_head := TM1.zO_head.

Notation zO_mid := TM1.zO_mid.

Notation zO_b0 := TM1.zO_b0.

Notation zO_b2 := TM1.zO_b2.

Notation zE_head := TM1.zE_head.

Notation zE_b0 := TM1.zE_b0.

Notation zW_td1a := TM1.zW_td1a.

Notation zW_td1b := TM1.zW_td1b.

Notation zW_td0a := TM1.zW_td0a.

Notation zW_td0b := TM1.zW_td0b.

Notation zS3 := TM1.zS3.

Notation zT_pow := TM1.zT_pow.

Notation zSa := TM1.zSa.

Notation z0k := TM1.z0k.

Notation z0l := TM1.z0l.

Notation zH_d0_even := TM1.zH_d0_even.

Notation zH_d0_odd := TM1.zH_d0_odd.

Notation zH_d1_even := TM1.zH_d1_even.

Notation z0m := TM1.z0m.

Notation z0n := TM1.z0n.

Notation z0o := TM1.z0o.

Notation z0p := TM1.z0p.

Notation z0q := TM1.z0q.

Notation z0r := TM1.z0r.

Notation z0s := TM1.z0s.

Notation z0t := TM1.z0t.

Notation z0u := TM1.z0u.

Notation z0v := TM1.z0v.

Notation z0w := TM1.z0w.

Notation zCp_step := TM1.zCp_step.

Notation zCp_chain := TM1.zCp_chain.

Notation zOdd_base := TM1.zOdd_base.

Notation zEven_ch_step := TM1.zEven_ch_step.

Notation zEven_base := TM1.zEven_base.

Notation zW_turn := TM1.zW_turn.

Notation zW_s1 := TM1.zW_s1.

Notation zW_s2 := TM1.zW_s2.

Notation zW_s3 := TM1.zW_s3.

Notation zW_s4 := TM1.zW_s4.

Notation zW_s5 := TM1.zW_s5.

Notation zW_s6 := TM1.zW_s6.

Notation zW_s7 := TM1.zW_s7.

Notation zW_s8 := TM1.zW_s8.

Notation zW_s9 := TM1.zW_s9.

Notation zW_s10 := TM1.zW_s10.

Notation zW_s11 := TM1.zW_s11.

Notation zW_rest_seg := TM1.zW_rest_seg.

Notation zW_full := TM1.zW_full.

Notation Word := TM1.Word.

Notation WV := TM1.WV.

Notation WK := TM1.WK.

Notation WQ := TM1.WQ.

Notation word_eqb := TM1.word_eqb.

Notation word_eqb_spec := TM1.word_eqb_spec.

Notation zW := TM1.zW.

Notation zR := TM1.zR.

Notation zQK := TM1.zQK.

Notation zQK_append := TM1.zQK_append.

Notation zTs := TM1.zTs.

Notation z0S := TM1.z0S.

Notation zTs_R := TM1.zTs_R.

Notation zTs_QK := TM1.zTs_QK.

Notation BRIncs := TM1.BRIncs.

Notation BRIncs_zero := TM1.BRIncs_zero.

Notation BRIncs_T := TM1.BRIncs_T.

Notation BRIncs_pair0 := TM1.BRIncs_pair0.

Notation BRIncs_pair1 := TM1.BRIncs_pair1.

Notation BRIncs_short00 := TM1.BRIncs_short00.

Notation BRIncs_short01 := TM1.BRIncs_short01.

Notation BRIncs_short10 := TM1.BRIncs_short10.

Notation BRIncs_short11 := TM1.BRIncs_short11.

Notation BRIncs_odd_chain0 := TM1.BRIncs_odd_chain0.

Notation BRIncs_odd_chain1 := TM1.BRIncs_odd_chain1.

Notation BRIncs_even_chain := TM1.BRIncs_even_chain.

Notation BRIncs_shift_pair0 := TM1.BRIncs_shift_pair0.

Notation BRIncs_shift_pair1 := TM1.BRIncs_shift_pair1.

Notation BRIncs_shift_chain0 := TM1.BRIncs_shift_chain0.

Notation BRIncs_shift_chain1 := TM1.BRIncs_shift_chain1.

Notation Num := TM1.Num.

Notation Num_zero := TM1.Num_zero.

Notation Num_odd := TM1.Num_odd.

Notation Num_even := TM1.Num_even.

Notation Num_shift := TM1.Num_shift.

Notation z2f := TM1.z2f.

Notation z2g := TM1.z2g.

Notation z2h := TM1.z2h.

Notation z2i_p0 := TM1.z2i_p0.

Notation z2j := TM1.z2j.

Notation z2k := TM1.z2k.

Notation z2l := TM1.z2l.

Notation z2m := TM1.z2m.

Notation z2n := TM1.z2n.

Notation z2_oc0 := TM1.z2_oc0.

Notation z2_oc1 := TM1.z2_oc1.

Notation z2_ec := TM1.z2_ec.

Notation z2_sp0 := TM1.z2_sp0.

Notation z2_sp1 := TM1.z2_sp1.

Notation z2_sc0 := TM1.z2_sc0.

Notation z2_sc1 := TM1.z2_sc1.

Notation z2o := TM1.z2o.

Notation z2p := TM1.z2p.

Local Open Scope nat_scope.

Notation Binary := TM1.Binary.

Notation Binary_one := TM1.Binary_one.

Notation Binary_zero := TM1.Binary_zero.

Notation Binary_two := TM1.Binary_two.

Notation zPp := TM1.zPp.

Notation zP2 := TM1.zP2.

Notation z0F := TM1.z0F.

Notation z0H := TM1.z0H.

Notation zPr := TM1.zPr.

Notation zPr_nil := TM1.zPr_nil.

Notation zPr_T := TM1.zPr_T.

Notation zPr_short0 := TM1.zPr_short0.

Notation zPr_short1 := TM1.zPr_short1.

Notation zPr_pair0 := TM1.zPr_pair0.

Notation zPr_pair1 := TM1.zPr_pair1.

Notation z0I := TM1.z0I.

Notation z0J := TM1.z0J.

Notation zDg := TM1.zDg.

Notation zDg_nil := TM1.zDg_nil.

Notation zDg_zero := TM1.zDg_zero.

Notation zDg_one := TM1.zDg_one.

Notation z0K := TM1.z0K.

Notation zD0 := TM1.zD0.

Notation zD1 := TM1.zD1.

Notation z0T := TM1.z0T.

Notation z0U := TM1.z0U.

Notation z0W_lt := TM1.z0W_lt.

Notation z0X := TM1.z0X.

Notation z0L := TM1.z0L.

Notation z1I := TM1.z1I.

Notation zDg_pos_z0L := TM1.zDg_pos_z0L.

Local Open Scope Q_scope.

Notation Qnat := TM1.Qnat.

Notation Qnat_0 := TM1.Qnat_0.

Notation Qnat_1 := TM1.Qnat_1.

Notation Qnat_S := TM1.Qnat_S.

Notation Qnat_add := TM1.Qnat_add.

Notation Qnat_mul := TM1.Qnat_mul.

Notation Qnat_nonneg := TM1.Qnat_nonneg.

Notation Qnat_le_iff := TM1.Qnat_le_iff.

Notation Qnat_lt_iff := TM1.Qnat_lt_iff.

Notation Qnat_eq_iff := TM1.Qnat_eq_iff.

Notation Qnat_pow2_S := TM1.Qnat_pow2_S.

Notation Qnat_pow2_1_add := TM1.Qnat_pow2_1_add.

Notation z0Y := TM1.z0Y.

Notation z0W := TM1.z0W.

Notation z0Z := TM1.z0Z.

Notation z10 := TM1.z10.

Notation z11 := TM1.z11.

Notation zWn := TM1.zWn.

Notation zWY := TM1.zWY.

Notation z12 := TM1.z12.

Notation zSp := TM1.zSp.

Notation z13 := TM1.z13.

Notation z13W := TM1.z13W.

Notation z14 := TM1.z14.

Notation z15 := TM1.z15.

Notation z16 := TM1.z16.

Notation zDw := TM1.zDw.

Notation z17 := TM1.z17.

Notation zHn := TM1.zHn.

Notation z1x := TM1.z1x.

Notation z1B := TM1.z1B.

Notation z1K := TM1.z1K.

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

Notation Scan := TM1.Scan.

Notation Scan_nil := TM1.Scan_nil.

Notation Scan_T := TM1.Scan_T.

Notation Scan_pair0 := TM1.Scan_pair0.

Notation Scan_pair1 := TM1.Scan_pair1.

Notation Scan_short00 := TM1.Scan_short00.

Notation Scan_short01 := TM1.Scan_short01.

Notation Scan_short10 := TM1.Scan_short10.

Notation Scan_short11 := TM1.Scan_short11.

Notation z19 := TM1.z19.

Notation z1a := TM1.z1a.

Notation zSz := TM1.zSz.

Notation zSo := TM1.zSo.

Notation zS1 := TM1.zS1.

Notation zTd := TM1.zTd.

Notation zTd_end := TM1.zTd_end.

Notation zTd_zero := TM1.zTd_zero.

Notation zTd_one := TM1.zTd_one.

Notation z1e := TM1.z1e.

Notation z1f := TM1.z1f.

Notation zTo := TM1.zTo.

Notation z1g := TM1.z1g.

Notation z1h := TM1.z1h.

Notation z0L_odd_scan := TM1.z0L_odd_scan.

Notation zScan_qqk := TM1.zScan_qqk.

Notation zIv := TM1.zIv.

Notation zP4 := TM1.zP4.

Notation zIv_P4 := TM1.zIv_P4.

Notation z11_R := TM1.z11_R.

Notation z11_QK := TM1.z11_QK.

Notation z0W_R := TM1.z0W_R.

Notation z0W_QK := TM1.z0W_QK.

Notation BScan := TM1.BScan.

Notation BScan_nil := TM1.BScan_nil.

Notation BScan_T := TM1.BScan_T.

Notation BScan_pair0 := TM1.BScan_pair0.

Notation BScan_pair1 := TM1.BScan_pair1.

Notation BScan_short00 := TM1.BScan_short00.

Notation BScan_short01 := TM1.BScan_short01.

Notation BScan_short10 := TM1.BScan_short10.

Notation BScan_short11 := TM1.BScan_short11.

Notation BScan_odd_chain0 := TM1.BScan_odd_chain0.

Notation BScan_odd_chain1 := TM1.BScan_odd_chain1.

Notation BScan_even_chain := TM1.BScan_even_chain.

Notation BScan_shift_pair0 := TM1.BScan_shift_pair0.

Notation BScan_shift_pair1 := TM1.BScan_shift_pair1.

Notation BScan_shift_chain0 := TM1.BScan_shift_chain0.

Notation BScan_shift_chain1 := TM1.BScan_shift_chain1.

Notation zIv_pow2 := TM1.zIv_pow2.

Notation z1i := TM1.z1i.

Notation z1j := TM1.z1j.

Notation z1k := TM1.z1k.

Notation Qnat_le := TM1.Qnat_le.

Notation z1n := TM1.z1n.

Notation zHi_bscan := TM1.zHi_bscan.

Notation zSwt := TM1.zSwt.

Notation z1p_upper := TM1.z1p_upper.

Notation zBz := TM1.zBz.

Notation z0L_odd_bscan := TM1.z0L_odd_bscan.

Notation z1p_z0L := TM1.z1p_z0L.

Notation ModeU := TM1.ModeU.

Notation ME := TM1.ME.

Notation MO := TM1.MO.

Notation MS := TM1.MS.

Notation zPrU := TM1.zPrU.

Notation zPrU_base_E := TM1.zPrU_base_E.

Notation zPrU_base_O := TM1.zPrU_base_O.

Notation zPrU_T_E := TM1.zPrU_T_E.

Notation zPrU_T_O := TM1.zPrU_T_O.

Notation zPrU_odd_c := TM1.zPrU_odd_c.

Notation zPrU_short_K := TM1.zPrU_short_K.

Notation zPrU_even_c := TM1.zPrU_even_c.

Notation zPrU_shift_K := TM1.zPrU_shift_K.

Notation zPrU_shift_c := TM1.zPrU_shift_c.

Notation zPrU_short_Q := TM1.zPrU_short_Q.

Notation zPrU_shift_Q := TM1.zPrU_shift_Q.

Notation zPrU_pair0_E := TM1.zPrU_pair0_E.

Notation zPrU_pair0_O := TM1.zPrU_pair0_O.

Notation zPrU_pair1_E := TM1.zPrU_pair1_E.

Notation zPrU_pair1_O := TM1.zPrU_pair1_O.

Notation zPrC := TM1.zPrC.

Notation zPrU_all := TM1.zPrU_all.

Notation zPrU_MO_V := TM1.zPrU_MO_V.

Notation zPrU_ME_VV := TM1.zPrU_ME_VV.

Notation zPrU_MS_W := TM1.zPrU_MS_W.

Notation zPrU_bscan := TM1.zPrU_bscan.

Notation zDg_zero_Z := TM1.zDg_zero_Z.

Notation zPiece3 := TM1.zPiece3.

Notation z1l := TM1.z1l.

Import BinNat Pnat Nnat.

Notation zP33 := TM1.zP33.

Notation zOut33 := TM1.zOut33.

Notation zTail8 := TM1.zTail8.

Notation zDg_tail8 := TM1.zDg_tail8.

Notation zP3_11 := TM1.zP3_11.

Notation zP3_01 := TM1.zP3_01.

Notation zP3_00 := TM1.zP3_00.

Notation zP3_10 := TM1.zP3_10.

Notation N_124522 := TM1.N_124522.

Notation N_249044 := TM1.N_249044.

Notation Qnat_N_to_nat := TM1.Qnat_N_to_nat.

Notation Qnat_249044 := TM1.Qnat_249044.

Notation Qnat_pow2_8 := TM1.Qnat_pow2_8.

Notation Qnat_pow2_9 := TM1.Qnat_pow2_9.

Notation Qnat_pow2_16 := TM1.Qnat_pow2_16.

Notation Qnat_pow2_17 := TM1.Qnat_pow2_17.

Notation nat_lin_eq := TM1.nat_lin_eq.

Notation nat_mul_eq := TM1.nat_mul_eq.

Notation zBRIncs_P33 := TM1.zBRIncs_P33.

Opaque N_124522 N_249044.

Notation N_249044_even := TM1.N_249044_even.

Notation BGood := TM1.BGood.

Notation BGood_intro := TM1.BGood_intro.

Notation BStep := TM1.BStep.

Notation BStep_intro := TM1.BStep_intro.

Notation z1N := TM1.z1N.

Notation z1P := TM1.z1P.

Notation z1Q := TM1.z1Q.

Notation z1R := TM1.z1R.

Notation zPf_pos := TM1.zPf_pos.

Notation z1S_pos := TM1.z1S_pos.

Notation zSw := TM1.zSw.

Notation z1T := TM1.z1T.

Notation z1U := TM1.z1U.

Notation z1V := TM1.z1V.

Notation Choice := TM1.Choice.

Notation CT := TM1.CT.

Notation CP0 := TM1.CP0.

Notation CP1 := TM1.CP1.

Notation CS00 := TM1.CS00.

Notation CS01 := TM1.CS01.

Notation CS10 := TM1.CS10.

Notation CS11 := TM1.CS11.

Notation COC0 := TM1.COC0.

Notation COC1 := TM1.COC1.

Notation CEC := TM1.CEC.

Notation CSP0 := TM1.CSP0.

Notation CSP1 := TM1.CSP1.

Notation CSC0 := TM1.CSC0.

Notation CSC1 := TM1.CSC1.

Notation zInS := TM1.zInS.

Notation zOutS := TM1.zOutS.

Notation zGetN := TM1.zGetN.

Notation z1W := TM1.z1W.

Notation z1X := TM1.z1X.

Notation z1Y := TM1.z1Y.

Notation z1Z := TM1.z1Z.

Notation z20 := TM1.z20.

Notation N_to_nat_pow2 := TM1.N_to_nat_pow2.

Notation z21 := TM1.z21.

Notation z22 := TM1.z22.

Notation z23 := TM1.z23.

Notation Rounds := TM1.Rounds.

Notation Rounds_refl := TM1.Rounds_refl.

Notation Rounds_next := TM1.Rounds_next.

Notation z24 := TM1.z24.

Notation z25 := TM1.z25.

Notation z26 := TM1.z26.

Notation z27 := TM1.z27.

Notation zN11 := TM1.zN11.

Notation zP11 := TM1.zP11.

Notation z11_pow := TM1.z11_pow.

Notation QN := TM1.QN.

Notation QN_add := TM1.QN_add.

Notation QN_mul := TM1.QN_mul.

Notation QN_leb := TM1.QN_leb.

Notation zWU := TM1.zWU.

Notation zWU_ge := TM1.zWU_ge.

Notation zZNat := TM1.zZNat.

Notation zZNat_eq := TM1.zZNat_eq.

Notation zLastV := TM1.zLastV.

Notation zLastV_eq := TM1.zLastV_eq.

Notation zInitVV := TM1.zInitVV.

Notation zInitVV_eq := TM1.zInitVV_eq.

Notation zInitQK := TM1.zInitQK.

Notation zInitQK_eq := TM1.zInitQK_eq.

Notation z28 := TM1.z28.

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

Notation cconfig_steps_pos := TM2.cconfig_steps_pos.

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

Notation cconfig_steps_pos_eqb := TM2.cconfig_steps_pos_eqb.

Lemma cconfig_steps_pos_eqb_spec (m : TM) (p : positive) (x y : cconfig) :
  cconfig_steps_pos_eqb m p x y = true ->
  cconfig_to_config x -[ m ]->+ cconfig_to_config y.
Proof.
  unfold cconfig_steps_pos_eqb.
  destruct (cconfig_steps_pos m p x) as [z |] eqn:F; [| discriminate].
  intros Heq.
  rewrite <- (cconfig_eqb_spec z y Heq).
  exact (cconfig_steps_pos_spec m p x z F).
Qed.

Lemma z0E : (F;; 0inf {{0}} 0inf) -[ TM1.tm ]->+ zCf (zTs z29 0inf).
Proof.
  assert (Hstep : cconfig_to_config ([], [], 0, F) -[ TM1.tm ]->+
      cconfig_to_config ([0; 1], [0] ++ w_base ++ zTs_list z29, 1, C)).
  { apply (cconfig_steps_pos_eqb_spec TM1.tm 38584%positive).
    vm_compute; reflexivity. }
  assert (Hrhs : cconfig_to_config ([0; 1], [0] ++ w_base ++ zTs_list z29, 1, C) = zCf (zTs z29 0inf)).
  { unfold cconfig_to_config, zCf, zCL, lh.
    cbn [hd tl List.app Str_app].
    rewrite !Str_app_assoc, zTs_list_spec.
    reflexivity. }
  rewrite Hrhs in Hstep.
  exact Hstep.
Qed.

Notation z2q := TM1.z2q.

Notation z2r := TM1.z2r.

Lemma canon_nonhalt : ~ halts TM1.tm (F;; 0inf {{0}} 0inf).
Proof.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [apply progress_evstep; exact z0E | exact (z2r z2d)].
  - apply (progress_nonhalt_cond TM1.tm zW (z2b ++ (z2c ++ zTail8))
      (fun w => zCf (zTs (zP33 ++ w) 0inf)) BGood).
    + intros w hG.
      destruct (z1N hG) as [w' [hStep hG']].
      exists w'; split; [exact (z2q hStep) | exact hG'].
    + exact z2e.
Qed.

Definition state_map (q: Q) := match q with A => B | B => C | C => D | D => E | E => F | F => A end.

Lemma perm: Perm TM1.tm tm state_map.
Proof. split.
- intros [] [] H; cbn in *; try discriminate; reflexivity.
- intros [] [] s d q H; cbn in H; inversion H; subst; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. exact (perm_nonhalt' TM1.tm tm state_map F tape0 perm canon_nonhalt). Qed.

End TM4.
Print Assumptions TM4.nonhalt.

From Coq Require Import NArith.NArith.

Module TM5.
Import List.

Import Bool.

Import String.

Import PeanoNat.

Import Lia.

Import NArith.

Import QArith.

Import Lqa.

Notation Rat := QArith_base.Q.

Import BusyCoq.Individual62.

Import ListNotations.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RD_1RD0RB_1LE1RC_1LF0LE_1LA0LC").

Notation cconfig_steps := TM1.cconfig_steps.

Notation cconfig_steps_spec := TM1.cconfig_steps_spec.

Notation t := TM1.t.

Notation d0 := TM1.d0.

Notation d1 := TM1.d1.

Notation one := TM1.one.

Notation lh := TM1.lh.

Notation w_word := TM1.w_word.

Notation w_rest := TM1.w_rest.

Notation w_base := TM1.w_base.

Notation zDd := TM1.zDd.

Notation Call := TM1.Call.

Notation ch := TM1.ch.

Notation cj := TM1.cj.

Notation cp := TM1.cp.

Notation zCs := TM1.zCs.

Notation zCw := TM1.zCw.

Notation zCR := TM1.zCR.

Notation zCL := TM1.zCL.

Notation zCf := TM1.zCf.

Notation z04 := TM1.z04.

Notation Side := TM1.Side.

Notation Side_nil := TM1.Side_nil.

Notation Side_cons := TM1.Side_cons.

Notation Seg := TM1.Seg.

Notation zLp' := TM1.zLp'.

Notation z06 := TM1.z06.

Notation z07 := TM1.z07.

Notation z08 := TM1.z08.

Notation z09 := TM1.z09.

Notation z0a := TM1.z0a.

Notation z0m_id := TM1.z0m_id.

Notation zSc := TM1.zSc.

Notation zSg := TM1.zSg.

Notation zS0 := TM1.zS0.

Notation zS4 := TM1.zS4.

Notation zS2 := TM1.zS2.

Notation zS5 := TM1.zS5.

Notation zS6 := TM1.zS6.

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

Notation z0b := TM1.z0b.

Notation z0c_p := TM1.z0c_p.

Notation z0c := TM1.z0c.

Notation zH2 := TM1.zH2.

Notation z0d := TM1.z0d.

Notation z0e := TM1.z0e.

Notation z0f := TM1.z0f.

Notation z0g := TM1.z0g.

Notation z0h := TM1.z0h.

Notation z0i := TM1.z0i.

Notation zH1 := TM1.zH1.

Notation zH3 := TM1.zH3.

Notation z0j := TM1.z0j.

Notation zH0 := TM1.zH0.

Notation zH4 := TM1.zH4.

Notation zC_base := TM1.zC_base.

Notation zO_head := TM1.zO_head.

Notation zO_mid := TM1.zO_mid.

Notation zO_b0 := TM1.zO_b0.

Notation zO_b2 := TM1.zO_b2.

Notation zE_head := TM1.zE_head.

Notation zE_b0 := TM1.zE_b0.

Notation zW_td1a := TM1.zW_td1a.

Notation zW_td1b := TM1.zW_td1b.

Notation zW_td0a := TM1.zW_td0a.

Notation zW_td0b := TM1.zW_td0b.

Notation zS3 := TM1.zS3.

Notation zT_pow := TM1.zT_pow.

Notation zSa := TM1.zSa.

Notation z0k := TM1.z0k.

Notation z0l := TM1.z0l.

Notation zH_d0_even := TM1.zH_d0_even.

Notation zH_d0_odd := TM1.zH_d0_odd.

Notation zH_d1_even := TM1.zH_d1_even.

Notation z0m := TM1.z0m.

Notation z0n := TM1.z0n.

Notation z0o := TM1.z0o.

Notation z0p := TM1.z0p.

Notation z0q := TM1.z0q.

Notation z0r := TM1.z0r.

Notation z0s := TM1.z0s.

Notation z0t := TM1.z0t.

Notation z0u := TM1.z0u.

Notation z0v := TM1.z0v.

Notation z0w := TM1.z0w.

Notation zCp_step := TM1.zCp_step.

Notation zCp_chain := TM1.zCp_chain.

Notation zOdd_base := TM1.zOdd_base.

Notation zEven_ch_step := TM1.zEven_ch_step.

Notation zEven_base := TM1.zEven_base.

Notation zW_turn := TM1.zW_turn.

Notation zW_s1 := TM1.zW_s1.

Notation zW_s2 := TM1.zW_s2.

Notation zW_s3 := TM1.zW_s3.

Notation zW_s4 := TM1.zW_s4.

Notation zW_s5 := TM1.zW_s5.

Notation zW_s6 := TM1.zW_s6.

Notation zW_s7 := TM1.zW_s7.

Notation zW_s8 := TM1.zW_s8.

Notation zW_s9 := TM1.zW_s9.

Notation zW_s10 := TM1.zW_s10.

Notation zW_s11 := TM1.zW_s11.

Notation zW_rest_seg := TM1.zW_rest_seg.

Notation zW_full := TM1.zW_full.

Notation Word := TM1.Word.

Notation WV := TM1.WV.

Notation WK := TM1.WK.

Notation WQ := TM1.WQ.

Notation word_eqb := TM1.word_eqb.

Notation word_eqb_spec := TM1.word_eqb_spec.

Notation zW := TM1.zW.

Notation zR := TM1.zR.

Notation zQK := TM1.zQK.

Notation zQK_append := TM1.zQK_append.

Notation zTs := TM1.zTs.

Notation z0S := TM1.z0S.

Notation zTs_R := TM1.zTs_R.

Notation zTs_QK := TM1.zTs_QK.

Notation BRIncs := TM1.BRIncs.

Notation BRIncs_zero := TM1.BRIncs_zero.

Notation BRIncs_T := TM1.BRIncs_T.

Notation BRIncs_pair0 := TM1.BRIncs_pair0.

Notation BRIncs_pair1 := TM1.BRIncs_pair1.

Notation BRIncs_short00 := TM1.BRIncs_short00.

Notation BRIncs_short01 := TM1.BRIncs_short01.

Notation BRIncs_short10 := TM1.BRIncs_short10.

Notation BRIncs_short11 := TM1.BRIncs_short11.

Notation BRIncs_odd_chain0 := TM1.BRIncs_odd_chain0.

Notation BRIncs_odd_chain1 := TM1.BRIncs_odd_chain1.

Notation BRIncs_even_chain := TM1.BRIncs_even_chain.

Notation BRIncs_shift_pair0 := TM1.BRIncs_shift_pair0.

Notation BRIncs_shift_pair1 := TM1.BRIncs_shift_pair1.

Notation BRIncs_shift_chain0 := TM1.BRIncs_shift_chain0.

Notation BRIncs_shift_chain1 := TM1.BRIncs_shift_chain1.

Notation Num := TM1.Num.

Notation Num_zero := TM1.Num_zero.

Notation Num_odd := TM1.Num_odd.

Notation Num_even := TM1.Num_even.

Notation Num_shift := TM1.Num_shift.

Notation z2f := TM1.z2f.

Notation z2g := TM1.z2g.

Notation z2h := TM1.z2h.

Notation z2i_p0 := TM1.z2i_p0.

Notation z2j := TM1.z2j.

Notation z2k := TM1.z2k.

Notation z2l := TM1.z2l.

Notation z2m := TM1.z2m.

Notation z2n := TM1.z2n.

Notation z2_oc0 := TM1.z2_oc0.

Notation z2_oc1 := TM1.z2_oc1.

Notation z2_ec := TM1.z2_ec.

Notation z2_sp0 := TM1.z2_sp0.

Notation z2_sp1 := TM1.z2_sp1.

Notation z2_sc0 := TM1.z2_sc0.

Notation z2_sc1 := TM1.z2_sc1.

Notation z2o := TM1.z2o.

Notation z2p := TM1.z2p.

Local Open Scope nat_scope.

Notation Binary := TM1.Binary.

Notation Binary_one := TM1.Binary_one.

Notation Binary_zero := TM1.Binary_zero.

Notation Binary_two := TM1.Binary_two.

Notation zPp := TM1.zPp.

Notation zP2 := TM1.zP2.

Notation z0F := TM1.z0F.

Notation z0H := TM1.z0H.

Notation zPr := TM1.zPr.

Notation zPr_nil := TM1.zPr_nil.

Notation zPr_T := TM1.zPr_T.

Notation zPr_short0 := TM1.zPr_short0.

Notation zPr_short1 := TM1.zPr_short1.

Notation zPr_pair0 := TM1.zPr_pair0.

Notation zPr_pair1 := TM1.zPr_pair1.

Notation z0I := TM1.z0I.

Notation z0J := TM1.z0J.

Notation zDg := TM1.zDg.

Notation zDg_nil := TM1.zDg_nil.

Notation zDg_zero := TM1.zDg_zero.

Notation zDg_one := TM1.zDg_one.

Notation z0K := TM1.z0K.

Notation zD0 := TM1.zD0.

Notation zD1 := TM1.zD1.

Notation z0T := TM1.z0T.

Notation z0U := TM1.z0U.

Notation z0W_lt := TM1.z0W_lt.

Notation z0X := TM1.z0X.

Notation z0L := TM1.z0L.

Notation z1I := TM1.z1I.

Notation zDg_pos_z0L := TM1.zDg_pos_z0L.

Local Open Scope Q_scope.

Notation Qnat := TM1.Qnat.

Notation Qnat_0 := TM1.Qnat_0.

Notation Qnat_1 := TM1.Qnat_1.

Notation Qnat_S := TM1.Qnat_S.

Notation Qnat_add := TM1.Qnat_add.

Notation Qnat_mul := TM1.Qnat_mul.

Notation Qnat_nonneg := TM1.Qnat_nonneg.

Notation Qnat_le_iff := TM1.Qnat_le_iff.

Notation Qnat_lt_iff := TM1.Qnat_lt_iff.

Notation Qnat_eq_iff := TM1.Qnat_eq_iff.

Notation Qnat_pow2_S := TM1.Qnat_pow2_S.

Notation Qnat_pow2_1_add := TM1.Qnat_pow2_1_add.

Notation z0Y := TM1.z0Y.

Notation z0W := TM1.z0W.

Notation z0Z := TM1.z0Z.

Notation z10 := TM1.z10.

Notation z11 := TM1.z11.

Notation zWn := TM1.zWn.

Notation zWY := TM1.zWY.

Notation z12 := TM1.z12.

Notation zSp := TM1.zSp.

Notation z13 := TM1.z13.

Notation z13W := TM1.z13W.

Notation z14 := TM1.z14.

Notation z15 := TM1.z15.

Notation z16 := TM1.z16.

Notation zDw := TM1.zDw.

Notation z17 := TM1.z17.

Notation zHn := TM1.zHn.

Notation z1x := TM1.z1x.

Notation z1B := TM1.z1B.

Notation z1K := TM1.z1K.

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

Notation Scan := TM1.Scan.

Notation Scan_nil := TM1.Scan_nil.

Notation Scan_T := TM1.Scan_T.

Notation Scan_pair0 := TM1.Scan_pair0.

Notation Scan_pair1 := TM1.Scan_pair1.

Notation Scan_short00 := TM1.Scan_short00.

Notation Scan_short01 := TM1.Scan_short01.

Notation Scan_short10 := TM1.Scan_short10.

Notation Scan_short11 := TM1.Scan_short11.

Notation z19 := TM1.z19.

Notation z1a := TM1.z1a.

Notation zSz := TM1.zSz.

Notation zSo := TM1.zSo.

Notation zS1 := TM1.zS1.

Notation zTd := TM1.zTd.

Notation zTd_end := TM1.zTd_end.

Notation zTd_zero := TM1.zTd_zero.

Notation zTd_one := TM1.zTd_one.

Notation z1e := TM1.z1e.

Notation z1f := TM1.z1f.

Notation zTo := TM1.zTo.

Notation z1g := TM1.z1g.

Notation z1h := TM1.z1h.

Notation z0L_odd_scan := TM1.z0L_odd_scan.

Notation zScan_qqk := TM1.zScan_qqk.

Notation zIv := TM1.zIv.

Notation zP4 := TM1.zP4.

Notation zIv_P4 := TM1.zIv_P4.

Notation z11_R := TM1.z11_R.

Notation z11_QK := TM1.z11_QK.

Notation z0W_R := TM1.z0W_R.

Notation z0W_QK := TM1.z0W_QK.

Notation BScan := TM1.BScan.

Notation BScan_nil := TM1.BScan_nil.

Notation BScan_T := TM1.BScan_T.

Notation BScan_pair0 := TM1.BScan_pair0.

Notation BScan_pair1 := TM1.BScan_pair1.

Notation BScan_short00 := TM1.BScan_short00.

Notation BScan_short01 := TM1.BScan_short01.

Notation BScan_short10 := TM1.BScan_short10.

Notation BScan_short11 := TM1.BScan_short11.

Notation BScan_odd_chain0 := TM1.BScan_odd_chain0.

Notation BScan_odd_chain1 := TM1.BScan_odd_chain1.

Notation BScan_even_chain := TM1.BScan_even_chain.

Notation BScan_shift_pair0 := TM1.BScan_shift_pair0.

Notation BScan_shift_pair1 := TM1.BScan_shift_pair1.

Notation BScan_shift_chain0 := TM1.BScan_shift_chain0.

Notation BScan_shift_chain1 := TM1.BScan_shift_chain1.

Notation zIv_pow2 := TM1.zIv_pow2.

Notation z1i := TM1.z1i.

Notation z1j := TM1.z1j.

Notation z1k := TM1.z1k.

Notation Qnat_le := TM1.Qnat_le.

Notation z1n := TM1.z1n.

Notation zHi_bscan := TM1.zHi_bscan.

Notation zSwt := TM1.zSwt.

Notation z1p_upper := TM1.z1p_upper.

Notation zBz := TM1.zBz.

Notation z0L_odd_bscan := TM1.z0L_odd_bscan.

Notation z1p_z0L := TM1.z1p_z0L.

Notation ModeU := TM1.ModeU.

Notation ME := TM1.ME.

Notation MO := TM1.MO.

Notation MS := TM1.MS.

Notation zPrU := TM1.zPrU.

Notation zPrU_base_E := TM1.zPrU_base_E.

Notation zPrU_base_O := TM1.zPrU_base_O.

Notation zPrU_T_E := TM1.zPrU_T_E.

Notation zPrU_T_O := TM1.zPrU_T_O.

Notation zPrU_odd_c := TM1.zPrU_odd_c.

Notation zPrU_short_K := TM1.zPrU_short_K.

Notation zPrU_even_c := TM1.zPrU_even_c.

Notation zPrU_shift_K := TM1.zPrU_shift_K.

Notation zPrU_shift_c := TM1.zPrU_shift_c.

Notation zPrU_short_Q := TM1.zPrU_short_Q.

Notation zPrU_shift_Q := TM1.zPrU_shift_Q.

Notation zPrU_pair0_E := TM1.zPrU_pair0_E.

Notation zPrU_pair0_O := TM1.zPrU_pair0_O.

Notation zPrU_pair1_E := TM1.zPrU_pair1_E.

Notation zPrU_pair1_O := TM1.zPrU_pair1_O.

Notation zPrC := TM1.zPrC.

Notation zPrU_all := TM1.zPrU_all.

Notation zPrU_MO_V := TM1.zPrU_MO_V.

Notation zPrU_ME_VV := TM1.zPrU_ME_VV.

Notation zPrU_MS_W := TM1.zPrU_MS_W.

Notation zPrU_bscan := TM1.zPrU_bscan.

Notation zDg_zero_Z := TM1.zDg_zero_Z.

Notation zPiece3 := TM1.zPiece3.

Notation z1l := TM1.z1l.

Import BinNat Pnat Nnat.

Notation zP33 := TM1.zP33.

Notation zOut33 := TM1.zOut33.

Notation zTail8 := TM1.zTail8.

Notation zDg_tail8 := TM1.zDg_tail8.

Notation zP3_11 := TM1.zP3_11.

Notation zP3_01 := TM1.zP3_01.

Notation zP3_00 := TM1.zP3_00.

Notation zP3_10 := TM1.zP3_10.

Notation N_124522 := TM1.N_124522.

Notation N_249044 := TM1.N_249044.

Notation Qnat_N_to_nat := TM1.Qnat_N_to_nat.

Notation Qnat_249044 := TM1.Qnat_249044.

Notation Qnat_pow2_8 := TM1.Qnat_pow2_8.

Notation Qnat_pow2_9 := TM1.Qnat_pow2_9.

Notation Qnat_pow2_16 := TM1.Qnat_pow2_16.

Notation Qnat_pow2_17 := TM1.Qnat_pow2_17.

Notation nat_lin_eq := TM1.nat_lin_eq.

Notation nat_mul_eq := TM1.nat_mul_eq.

Notation zBRIncs_P33 := TM1.zBRIncs_P33.

Opaque N_124522 N_249044.

Notation N_249044_even := TM1.N_249044_even.

Notation BGood := TM1.BGood.

Notation BGood_intro := TM1.BGood_intro.

Notation BStep := TM1.BStep.

Notation BStep_intro := TM1.BStep_intro.

Notation z1N := TM1.z1N.

Notation z1P := TM1.z1P.

Notation z1Q := TM1.z1Q.

Notation z1R := TM1.z1R.

Notation zPf_pos := TM1.zPf_pos.

Notation z1S_pos := TM1.z1S_pos.

Notation zSw := TM1.zSw.

Notation z1T := TM1.z1T.

Notation z1U := TM1.z1U.

Notation z1V := TM1.z1V.

Notation Choice := TM1.Choice.

Notation CT := TM1.CT.

Notation CP0 := TM1.CP0.

Notation CP1 := TM1.CP1.

Notation CS00 := TM1.CS00.

Notation CS01 := TM1.CS01.

Notation CS10 := TM1.CS10.

Notation CS11 := TM1.CS11.

Notation COC0 := TM1.COC0.

Notation COC1 := TM1.COC1.

Notation CEC := TM1.CEC.

Notation CSP0 := TM1.CSP0.

Notation CSP1 := TM1.CSP1.

Notation CSC0 := TM1.CSC0.

Notation CSC1 := TM1.CSC1.

Notation zInS := TM1.zInS.

Notation zOutS := TM1.zOutS.

Notation zGetN := TM1.zGetN.

Notation z1W := TM1.z1W.

Notation z1X := TM1.z1X.

Notation z1Y := TM1.z1Y.

Notation z1Z := TM1.z1Z.

Notation z20 := TM1.z20.

Notation N_to_nat_pow2 := TM1.N_to_nat_pow2.

Notation z21 := TM1.z21.

Notation z22 := TM1.z22.

Notation z23 := TM1.z23.

Notation Rounds := TM1.Rounds.

Notation Rounds_refl := TM1.Rounds_refl.

Notation Rounds_next := TM1.Rounds_next.

Notation z24 := TM1.z24.

Notation z25 := TM1.z25.

Notation z26 := TM1.z26.

Notation z27 := TM1.z27.

Notation zN11 := TM1.zN11.

Notation zP11 := TM1.zP11.

Notation z11_pow := TM1.z11_pow.

Notation QN := TM1.QN.

Notation QN_add := TM1.QN_add.

Notation QN_mul := TM1.QN_mul.

Notation QN_leb := TM1.QN_leb.

Notation zWU := TM1.zWU.

Notation zWU_ge := TM1.zWU_ge.

Notation zZNat := TM1.zZNat.

Notation zZNat_eq := TM1.zZNat_eq.

Notation zLastV := TM1.zLastV.

Notation zLastV_eq := TM1.zLastV_eq.

Notation zInitVV := TM1.zInitVV.

Notation zInitVV_eq := TM1.zInitVV_eq.

Notation zInitQK := TM1.zInitQK.

Notation zInitQK_eq := TM1.zInitQK_eq.

Notation z28 := TM1.z28.

Local Close Scope Q_scope.

Local Open Scope nat_scope.

Notation zH_d1_odd := TM1.zH_d1_odd.

Fixpoint zHExec_N (u : zW) (k : N) : option zW :=
  if N.eqb k 0 then Some u
  else
    match u with
    | [] => None
    | WV :: u' =>
      match zHExec_N u' (k * 2)%N with
      | Some v => Some (WV :: v)
      | None => None
      end
    | WK :: u' =>
      let m := N.div k 2 in
      if N.eqb k (m * 2) then
        match zHExec_N u' m with
        | Some v => Some (WK :: v)
        | None => None
        end
      else
        match zHExec_N u' m with
        | Some v => Some (WQ :: v)
        | None => None
        end
    | WQ :: u' =>
      let m := N.div k 2 in
      if N.eqb k (m * 2) then
        match zHExec_N u' m with
        | Some v => Some (WQ :: v)
        | None => None
        end
      else
        match zHExec_N u' (1 + m)%N with
        | Some v => Some (WK :: v)
        | None => None
        end
    end.

Lemma zHExec_ok_N (u : zW) :
  forall (k : N) (v : zW), zHExec_N u k = Some v ->
    Side ([ch] ^^ (N.to_nat k)) (zTs u 0inf) (zTs v 0inf).
Proof.
  induction u as [| w u IH]; intros k v h; cbn [zHExec_N] in h.
  - destruct (N.eqb_spec k 0) as [-> | hk0]; [inversion h; subst; exact (Side_nil _) | discriminate h].
  - destruct (N.eqb_spec k 0) as [-> | hk0]; [inversion h; subst; exact (Side_nil _) |].
    destruct w.
    + destruct (zHExec_N u (k * 2)%N) as [v' |] eqn:hE; [| discriminate h].
      inversion h; subst; cbn [zTs].
      pose proof (IH (k * 2)%N v' hE) as hIH.
      replace (N.to_nat (k * 2)) with (N.to_nat k * 2)%nat in hIH by lia.
      exact (zSc (zS3 (N.to_nat k)) hIH).
    + pose proof (N.div_mod k 2 ltac:(lia)) as hdm.
      pose proof (N.mod_lt k 2 ltac:(lia)) as hmlt.
      destruct (N.eqb_spec k (N.div k 2 * 2)) as [hk | hk].
      * destruct (zHExec_N u (N.div k 2)) as [v' |] eqn:hE; [| discriminate h].
        inversion h; subst; cbn [zTs].
        replace (N.to_nat k) with (N.to_nat (N.div k 2) * 2)%nat by lia.
        exact (zSc (zH_d0_even (N.to_nat (N.div k 2))) (IH _ _ hE)).
      * destruct (zHExec_N u (N.div k 2)) as [v' |] eqn:hE; [| discriminate h].
        inversion h; subst; cbn [zTs].
        replace (N.to_nat k) with (1 + N.to_nat (N.div k 2) * 2)%nat by lia.
        exact (zSc (zH_d0_odd (N.to_nat (N.div k 2))) (IH _ _ hE)).
    + pose proof (N.div_mod k 2 ltac:(lia)) as hdm.
      pose proof (N.mod_lt k 2 ltac:(lia)) as hmlt.
      destruct (N.eqb_spec k (N.div k 2 * 2)) as [hk | hk].
      * destruct (zHExec_N u (N.div k 2)) as [v' |] eqn:hE; [| discriminate h].
        inversion h; subst; cbn [zTs].
        replace (N.to_nat k) with (N.to_nat (N.div k 2) * 2)%nat by lia.
        exact (zSc (zH_d1_even (N.to_nat (N.div k 2))) (IH _ _ hE)).
      * destruct (zHExec_N u (1 + N.div k 2)%N) as [v' |] eqn:hE; [| discriminate h].
        inversion h; subst; cbn [zTs].
        pose proof (IH (1 + N.div k 2)%N v' hE) as hIH.
        replace (N.to_nat (1 + N.div k 2)) with (1 + N.to_nat (N.div k 2))%nat in hIH by lia.
        replace (N.to_nat k) with (1 + N.to_nat (N.div k 2) * 2)%nat by lia.
        exact (zSc (zH_d1_odd (N.to_nat (N.div k 2))) hIH).
Qed.

Notation w_pre3_rest := TM1.w_pre3_rest.

Notation w_pre5_rest := TM1.w_pre5_rest.

Notation w_pre_rest := TM1.w_pre_rest.

Notation w_pre := TM1.w_pre.

Notation zW_pre3_seg := TM1.zW_pre3_seg.

Notation zW_pre5_seg := TM1.zW_pre5_seg.

Notation zW_pre_seg := TM1.zW_pre_seg.

Notation zW_pre_full := TM1.zW_pre_full.

Notation z2q := TM1.z2q.

Notation z2r := TM1.z2r.

Definition z29_0581 : zW := [WV; WV; WV; WV; WV; WV; WK; WV; WV; WK; WV; WV; WV; WQ; WV; WV; WQ; WK; WK; WV; WK; WK; WQ; WK; WQ; WQ; WK; WK; WK; WK; WK; WK; WQ].

Definition z2a_0581 : list (list Choice) := [
  [CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP1; CT; CT; CP0; (CEC 0%nat); CSP0; CS10; CP0; CS01; CP0; CS10; CS10; CS00; CS10; CS10; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP1; (COC1 0%nat); (CSC0 0%nat); CSP1; CP0; CP1; (COC0 0%nat); CSP0; CP1; CP0; CS10; CS11; CP0; CS10; CP1; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CP0; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CP1; (COC1 0%nat); CSP1; CT; CT; CT; CP0; CP0; CP0; CP0; CP0; CS00; CP0; CP0; CP1; CP0; CP0; CS01; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CP0; CP0; CS00; CS00; CP1; CP0; CS10; CS10; CS10; CP1; CP0; CS10; CP0; CS00; CP0; CP1; CP0; CS10; CP0; CP0; CP1; CP0; CS10; CP0; CS01; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CS10; CT; (COC1 0%nat); CSP1; CP1; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP1; CT; CT; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP0; CT; CT; CP0; CP1; CP0; CS11; CP0; CS10; CS00; CP0; CS00; CP1; CP1; CP1; CP0; CS11; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CP0; CP0; CS01; CP0; CS10; CS00; CS10; CP0; CS01; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP1; CT; (COC0 1%nat); CSP0; CT; CT; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CP0; CS11; (COC0 0%nat); CSP0; CT; CT; CP0; CS10; CS11; CP1; CP0; CS10; CS00; CS00; CP0; CS00; CS10; CP0; CS00; CS10; CS00; CS10; CS11; CP0; CS10; CS01; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CP0; CP0; CS01; CP0; CS10; CP1; CP0; CS10; CS11; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; (COC0 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CP0; CT; CT; CT; CT; CP1; CT; CT; CP0; (CEC 0%nat); CSP0; CS11; (COC1 0%nat); CSP0; CP0; CP1; CT; CP0; CT; CT; CT; (COC0 1%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); (CSC0 0%nat); CSP1; CT; CT; CP1; CT; CT; CP0; CS11; CP1; CP1; CP1; CP0; CP1; CP0; CP1; CP0; CS10; CS11; CP1; CP1; CP0; CP0; CS00; CS01; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CP0; CP0; CP1; CP0; CP0; CS01; CP0; CS10; CS11; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; (COC1 0%nat); CSP0; CT; CT; (COC0 0%nat); (CSC0 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CP1; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CS10; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CP1; CT; CT; CT; (COC0 0%nat); CSP0; CS10; CT; CT; CT; (COC0 1%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CP1; CT; CT; CP0; CP1; CP0; CS10; CS10; CP0; CS01; CP0; CP1; CP1; CP0; CS10; CS00; CS11; CP1; CP0; CP0; CS00; CS00; CS00; CS00; CS01; CP0; CP0; CS00; CS00; CS00; CP0; CS00; CS00; CP0; CP0; CP0; CS00; CS10; CS00; CP0; CP1; CP1; CP1; CP0; CP1; CP0; CS10; CS10; CS10; CS11; CP0; CS10; CS01; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CP0; CP0; CP1; CP0; CS10; CP0; CS01; CP0; CS10; CS11; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; (COC0 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CS10; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CP1; (COC1 0%nat); CSP0; CT; CT; CT; CT; CP0; CS11; CT; CT; (COC0 0%nat); CSP0; CS10; CS00; CS10; CS10; CT; (COC1 0%nat); CSP0; CS10; (CEC 0%nat); CSP0; CS10; CT; CT; (COC0 0%nat); CSP0; CP0; CT; CT; CT; CT; CT; CT; CT; CP1; CP1; CT; CP0; CT; CT; CT; (COC0 1%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; CT; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP0; CT; CP1; CT; CT; CP0; CS10; CP0; CS00; CS00; CP0; CP0; CP0; CS01; CP0; CS10; CS00; CS01; CP0; CP0; CS00; CS00; CS10; CS10; CS00; CS00; CS00; CS10; CS00; CS01; CP1; CP1; CP0; CS11; CP0; CP0; CP1; CP1; CP0; CS10; CS00; CS10; CS00; CS10; CS00; CS10; CS00; CS00; CS10; CS00; CS00; CS00; CS10; CS10; CP0; CP0; CP0; CP0; CP0; CP1; CP0; CP1; CP0; CS10; CS11; CP1; CP1; CP0; CP0; CS00; CS01; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CP0; CP0; CS01; CP0; CS10; CS00; CS10; CP0; CS01; CP0; CS10; CS01; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; (COC1 0%nat); CSP0; CT; CT; (COC0 0%nat); (CSC0 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); (CSC0 0%nat); CSP1; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CP0; CP1; (COC0 0%nat); CSP1; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP0; CS10; CT; CT; (COC0 0%nat); CSP0; CT; CP0; CS10; CT; (COC1 0%nat); CSP0; CS10; CS11; CP0; CS10; CS00; CP0; CS00; CT; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; CP0; CP0; CP0; CP0; CS00; CP0; CS00; CS00; CP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; CP1; CT; CT; CT; (COC0 0%nat); CSP0; CS10; CT; CT; CT; (COC0 1%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CP0; CS11; (COC0 0%nat); CSP0; CT; CP0; CT; CT; CP0; CS10; CS10; CS10; CS01; CP1; CP1; CP1; CP0; CS11; CP1; CP0; CP0; CS00; CS00; CP0; CS00; CS10; CS01; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CP1; CP0; CS10; CP0; CS01; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP0; CP0; CS01; CP0; CS11; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CS00; CS01; CP0; CS10; CP0; CP0; CP1; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CS10; CS00; CS01; CP0; CS10; CS11; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CP0; CP0; CS01; CP0; CS10; CP1; CP0; CS10; CS11; CP0; CS10; CS11; CP1; CP0]; 
  [CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; (COC0 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CS10; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CS10; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP1; CT; CT; CT; (COC0 0%nat); CSP0; CS11; CT; CT; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; (COC1 0%nat); CSP1; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP1; CT; CP1; CT; (COC0 1%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP0; CS10; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; CT; CT; (COC0 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; (COC1 0%nat); CSP0; CT; CT; CT; CP0; CT; CT; CT; CT; CT; CT; CP1; CP0; CT; CT; CT; (COC0 0%nat); CSP1; CT; CT; (COC0 0%nat); CSP0; (CEC 0%nat); CSP0; CP0; CT; CT; CT; (COC0 1%nat); CSP1; CT; (COC0 0%nat); CSP1; (COC1 0%nat); CSP0; CT; CT; CT; (COC0 0%nat); CSP1; CT; CT; CT; (COC0 0%nat); (CSC1 0%nat); CSP1; CT; CT; CT; CT; CT; CT; CT; CT; CT; CT; CP0; (CEC 0%nat); CSP1; CT; CT; CT; CT; CT; CT; (COC0 1%nat); CSP1; CP0; CS10; CT; CP1; CT; CT; CT; (COC0 1%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); CSP1; CT; (COC0 0%nat); (CSC0 0%nat); CSP1; CT; CT; CP1; CT; CP1; CT; CT; CP0; CS10; CS11; CP0; CS10; CS10; CP1; CP1; CP0; CS10; CS00; CS11; CP0; CS10; CS10; CS00; CS01; CP0; CP1; CP0; CP0; CP0; CS00; CS10; CS10; CS00; CS10; CS00; CS10; CS00; CS10; CS10; CS10; CS00; CS10; CS10; CS00; CS10; CS10; CS00; CP0; CS01; CP0; CS10; CP0; CP1; CP0; CS11; CP0; CS11; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CS00; CS00; CP0; CS00; CS10; CS11; CP1; CP0; CP1; CP1; CP1; CP0; CS10; CP1; CP0; CP1; CP0; CS11; CP0; CS11; CP1; CP1; CP1; CP0; CS10; CP1; CP1; CP0; CP0; CS01; CP0; CS11; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP1; CP0; CS10; CS00; CP0; CP0; CP0; CP0; CP1; CP0; CP1; CP0; CS10; CS11; CP1; CP1; CP0; CP0; CS00; CS01; CP1; CP1; CP0; CS10; CS01; CP0; CS10; CP1; CP0; CS10; CP1; CP0; CS10; CP0; CP0; CP1; CP0; CP0; CS01; CP0; CS10; CS11; CP0; CS10; CS11; CP1; CP0]
].

Definition z2b_0581 : zW := [WV; WV; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WK; WV; WQ; WV; WK; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WK; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WQ; WV; WV; WK; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WK; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WQ; WV; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WK; WV; WV; WV; WV; WK; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WK; WV; WV; WV; WQ; WV; WV; WV; WV; WV; WK; WV; WV; WV; WK; WV; WV; WK; WV; WV; WK; WK; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WQ; WQ; WV; WQ; WQ; WV; WV; WV; WQ; WK; WQ; WV; WQ; WQ; WK; WK; WV; WV; WV; WV; WV; WK; WQ; WQ; WK; WQ; WK; WQ; WK; WQ; WQ; WQ; WK; WQ; WQ; WK; WQ; WQ; WK; WV; WK; WV; WQ; WV; WV; WV; WQ; WV; WQ; WV; WV; WV; WV; WV; WV; WQ; WK; WK; WV; WK; WQ; WQ; WV; WV; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WQ; WV; WQ; WV; WV; WV; WV; WQ; WV; WV; WV; WV; WK; WV; WQ; WV; WV; WV; WV; WV; WV; WV; WV; WV; WV; WQ; WK; WV; WV; WV; WV; WV; WV; WV; WV; WQ; WQ; WV; WV; WV; WV; WK; WK; WV; WV; WV; WQ; WK; WV; WQ; WV; WV; WQ; WV; WV; WQ; WV; WV; WV; WV; WV; WK; WV; WQ; WQ; WV; WQ; WQ; WV; WV].

Definition z2c_low_0581 : zW := [WQ; WK; WK; WQ; WK; WK; WK; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WK; WK; WK; WK; WQ; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WK; WK; WQ; WK; WK; WQ; WK; WQ; WK; WQ; WK; WK; WQ; WK; WK; WQ; WK; WK; WQ; WK; WK; WK; WK; WK; WQ; WK; WK; WK; WQ; WK; WQ; WK; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WK; WQ; WQ; WQ; WQ; WK; WK; WQ; WK; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WK; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WK; WQ; WQ; WK; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WQ; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WK; WQ; WQ; WK; WK; WQ; WK; WQ; WK; WQ; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WK; WK; WK; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WQ; WQ; WQ; WK; WK; WQ; WQ; WK; WK; WQ; WQ; WQ; WK; WK; WQ; WQ; WQ; WK].

Definition z2c_top_0581 : zW := [WK; WQ; WK; WQ; WK; WQ; WQ; WQ; WK; WK; WQ; WK; WQ; WQ; WK; WK].

Definition z2c_0581 : zW := z2c_low_0581 ++ z2c_top_0581.

Local Close Scope nat_scope.

Lemma z2d_0581 :
  Rounds (zTs z29_0581 0inf) (zTs (zP33 ++ (z2b_0581 ++ (z2c_0581 ++ zTail8))) 0inf).
Proof.
  apply (z25 z2a_0581 z29_0581 (zP33 ++ (z2b_0581 ++ (z2c_0581 ++ zTail8)))).
  vm_cast_no_check (eq_refl (Some (zP33 ++ (z2b_0581 ++ (z2c_0581 ++ zTail8))))).
Qed.

Lemma z2e_0581 :
  BGood (z2b_0581 ++ (z2c_0581 ++ zTail8)).
Proof.
  unfold z2c_0581.
  apply (z28 z2b_0581 z2c_low_0581 z2c_top_0581);
    [ vm_cast_no_check (eq_refl true)
    | vm_cast_no_check (eq_refl true)
    | reflexivity
    | vm_cast_no_check (eq_refl true)
    | vm_cast_no_check (eq_refl true)
    | vm_cast_no_check (eq_refl true)
    | vm_cast_no_check (eq_refl true)
    | vm_cast_no_check (eq_refl true)
    | vm_cast_no_check (eq_refl true)
    | vm_cast_no_check (eq_refl true) ].
Qed.

Definition zPre_0581 : zW := [WV; WV; WV; WV; WV; WV; WK; WV; WV; WK; WV; WV; WV; WQ; WV; WV; WQ; WK; WK; WV; WK; WK; WQ; WK; WQ; WQ; WK; WK; WK; WK; WK; WK; WK].

Notation zTs_list := TM4.zTs_list.

Notation zTs_list_spec := TM4.zTs_list_spec.

Notation cconfig_steps_pos := TM2.cconfig_steps_pos.

Notation cconfig_steps_pos_spec := TM4.cconfig_steps_pos_spec.

Notation cconfig_steps_pos_eqb := TM2.cconfig_steps_pos_eqb.

Notation cconfig_steps_pos_eqb_spec := TM4.cconfig_steps_pos_eqb_spec.

Definition zCk0_0581 : cconfig := ([], [], 0%sym, E).

Definition zCk6_0581 : cconfig := ([0; 1]%sym, [0]%sym ++ w_pre ++ zTs_list zPre_0581, 1%sym, C).

Lemma z0E_0581 : (E;; tape0) -[ TM1.tm ]->* zCf (zTs z29_0581 0inf).
Proof.
  assert (h_steps : cconfig_to_config zCk0_0581 -[ TM1.tm ]->+ cconfig_to_config zCk6_0581).
  { apply (cconfig_steps_pos_eqb_spec TM1.tm 51601%positive zCk0_0581 zCk6_0581).
     vm_cast_no_check (eq_refl true). }
  cbn [cconfig_to_config zCk0_0581] in h_steps.
  assert (heq6 : cconfig_to_config zCk6_0581 = zCL lh (w_pre *> zTs zPre_0581 0inf)).
  { unfold zCk6_0581, cconfig_to_config, zCL, lh; cbn [hd tl List.app Str_app].
     rewrite !Str_app_assoc, zTs_list_spec; reflexivity. }
  rewrite heq6 in h_steps.
  assert (h_side : Side ([ch] ^^ (N.to_nat 16%N)) (zTs zPre_0581 0inf) (zTs z29_0581 0inf)).
  { apply (zHExec_ok_N zPre_0581 16%N z29_0581).
     vm_cast_no_check (eq_refl (Some z29_0581)). }
  change (N.to_nat 16%N) with 16%nat in h_side.
  eapply evstep_trans; [apply progress_evstep; exact h_steps |].
  apply progress_evstep; exact (zW_pre_full h_side).
Qed.

Lemma nonhalt_canon : ~ halts TM1.tm (E;; tape0).
Proof.
  eapply multistep_nonhalt.
  - eapply evstep_trans; [exact z0E_0581 | exact (z2r z2d_0581)].
  - apply (progress_nonhalt_cond TM1.tm zW (z2b_0581 ++ (z2c_0581 ++ zTail8))
      (fun w => zCf (zTs (zP33 ++ w) 0inf)) BGood).
    + intros w hG.
      destruct (z1N hG) as [w' [hStep hG']].
      exists w'; split; [exact (z2q hStep) | exact hG'].
    + exact z2e_0581.
Qed.

Definition state_map (q: Q) := match q with A => C | B => D | C => E | D => F | E => A | F => B end.

Lemma perm: Perm TM1.tm tm state_map.
Proof. split.
- intros [] [] H; cbn in *; try discriminate; reflexivity.
- intros [] [] s d q H; cbn in H; inversion H; subst; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. exact (perm_nonhalt' TM1.tm tm state_map E tape0 perm nonhalt_canon). Qed.

End TM5.
Print Assumptions TM5.nonhalt.

From Coq Require Import String Bool Lists.List Lia ZifyNat PeanoNat.

Module TM6.
Import BusyCoq.Individual62.

Import String Bool List Lia ZifyNat PeanoNat.

Import ListNotations.

Open Scope list.

Open Scope sym.

Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RA_0RA0LD_1LE---_1RF0LF_0LC0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Ltac pose_div2 x :=
  let H1 := fresh "Hdiv" in
  let H2 := fresh "Hmod" in
  assert (H1 : x = 2 * (x / 2) + x mod 2) by (apply Nat.div_mod; lia);
  assert (H2 : x mod 2 < 2) by (apply Nat.mod_upper_bound; lia).

Ltac omega_div :=
  repeat match goal with
  | |- context [?x / 2] =>
    lazymatch goal with
    | H : x = 2 * (x / 2) + x mod 2 |- _ => fail
    | _ => pose_div2 x
    end
  | H : context [?x / 2] |- _ =>
    lazymatch goal with
    | H' : x = 2 * (x / 2) + x mod 2 |- _ => fail
    | _ => pose_div2 x
    end
  end;
  lia.

Definition cfg_h01B (w s : side) : Q * tape :=
  w <{{E}} (1%sym >> 0%sym >> s).

Definition cfg_modeB (w s : side) : Q * tape :=
  (1%sym >> 0%sym >> w) {{B}}> s.

Definition cfg_modeF (w s : side) : Q * tape :=
  (1%sym >> 0%sym >> w) {{F}}> s.

Lemma step_init_to_h01B :
  c0 -->+ cfg_h01B 0inf%sym (1%sym >> 0inf%sym).
Proof.
  unfold c0, tape0, cfg_h01B; simpl; start_progress.
Qed.

Lemma step_h01B_nil (s : side) :
  cfg_h01B 0inf%sym s -->+
    cfg_modeB (1%sym >> 0%sym >> 0%sym >> 0inf%sym) s.
Proof.
  unfold cfg_h01B, cfg_modeB; simpl; repeat rewrite <- const_unfold; start_progress.
Qed.

Lemma step_h01B_010 (w s : side) :
  cfg_h01B (0%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_0010 (w s : side) :
  cfg_h01B (0%sym >> 0%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_0110 (w s : side) :
  cfg_h01B (0%sym >> 1%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 1%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_110 (w s : side) :
  cfg_h01B (1%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 0%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_1110 (w s : side) :
  cfg_h01B (1%sym >> 1%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_h01B, cfg_modeB; simpl; start_progress. Qed.

Lemma step_h01B_100 (w s : side) :
  cfg_h01B (1%sym >> 0%sym >> 0%sym >> w) s -->+
    cfg_h01B w (1%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_h01B; simpl; start_progress. Qed.

Lemma step_h01B_1010 (w s : side) :
  cfg_h01B (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s -->+
    cfg_h01B w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeB_base (w : side) :
  cfg_modeB w (1%sym >> 0inf%sym) -->+
    cfg_h01B (1%sym >> 0%sym >> w) (1%sym >> 0inf%sym).
Proof. unfold cfg_modeB, cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeB_0100 (w s : side) :
  cfg_modeB w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_h01B w (1%sym >> 0%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_modeB, cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeB_0101 (w s : side) :
  cfg_modeB w (1%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeB; simpl; start_progress. Qed.

Lemma step_modeB_011 (w s : side) :
  cfg_modeB w (1%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeF (0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeB, cfg_modeF; simpl; start_progress. Qed.

Lemma step_modeF_0100 (w s : side) :
  cfg_modeF w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_h01B w (0%sym >> 0%sym >> 1%sym >> 0%sym >> s).
Proof. unfold cfg_modeF, cfg_h01B; simpl; start_progress. Qed.

Lemma step_modeF_0101 (w s : side) :
  cfg_modeF w (1%sym >> 0%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeB (1%sym >> 0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeF, cfg_modeB; simpl; start_progress. Qed.

Lemma step_modeF_011 (w s : side) :
  cfg_modeF w (1%sym >> 1%sym >> 0%sym >> s) -->+
    cfg_modeF (0%sym >> 1%sym >> 0%sym >> w) s.
Proof. unfold cfg_modeF; simpl; start_progress. Qed.

Inductive WTok : Type :=
  | W010
  | W0010
  | W0110
  | W100
  | W110
  | W1010
  | W1110.

Inductive STok : Type :=
  | T0100
  | T0101
  | T011.

Fixpoint evalW (L : list WTok) : side :=
  match L with
  | [] => 0inf%sym
  | W010 :: L' => 0%sym >> 1%sym >> 0%sym >> evalW L'
  | W0010 :: L' => 0%sym >> 0%sym >> 1%sym >> 0%sym >> evalW L'
  | W0110 :: L' => 0%sym >> 1%sym >> 1%sym >> 0%sym >> evalW L'
  | W100 :: L' => 1%sym >> 0%sym >> 0%sym >> evalW L'
  | W110 :: L' => 1%sym >> 1%sym >> 0%sym >> evalW L'
  | W1010 :: L' => 1%sym >> 0%sym >> 1%sym >> 0%sym >> evalW L'
  | W1110 :: L' => 1%sym >> 1%sym >> 1%sym >> 0%sym >> evalW L'
  end.

Fixpoint evalS (S : list STok) : side :=
  match S with
  | [] => 1%sym >> 0inf%sym
  | T0100 :: S' => 0%sym >> 0%sym >> 1%sym >> 0%sym >> evalS S'
  | T0101 :: S' => 1%sym >> 0%sym >> 1%sym >> 0%sym >> evalS S'
  | T011 :: S' => 1%sym >> 1%sym >> 0%sym >> evalS S'
  end.

Lemma sym_h01B_nil (S : list STok) :
  cfg_h01B (evalW []) (evalS S) -->+ cfg_modeB (evalW [W100]) (evalS S).
Proof. exact (step_h01B_nil (evalS S)). Qed.

Lemma sym_h01B_010 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W010 :: L)) (evalS S) -->+ cfg_modeB (evalW (W110 :: L)) (evalS S).
Proof. exact (step_h01B_010 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_0010 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W0010 :: L)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_h01B_0010 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_0110 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W0110 :: L)) (evalS S) -->+ cfg_modeB (evalW (W1110 :: L)) (evalS S).
Proof. exact (step_h01B_0110 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_110 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W110 :: L)) (evalS S) -->+ cfg_modeB (evalW (W100 :: L)) (evalS S).
Proof. exact (step_h01B_110 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_1110 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W1110 :: L)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_h01B_1110 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_100 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W100 :: L)) (evalS S) -->+ cfg_h01B (evalW L) (evalS (T011 :: S)).
Proof. exact (step_h01B_100 (evalW L) (evalS S)). Qed.

Lemma sym_h01B_1010 (L : list WTok) (S : list STok) :
  cfg_h01B (evalW (W1010 :: L)) (evalS S) -->+ cfg_h01B (evalW L) (evalS (T0100 :: S)).
Proof. exact (step_h01B_1010 (evalW L) (evalS S)). Qed.

Lemma sym_modeB_0100 (L : list WTok) (S : list STok) :
  cfg_modeB (evalW L) (evalS (T0100 :: S)) -->+ cfg_h01B (evalW L) (evalS (T0101 :: S)).
Proof. exact (step_modeB_0100 (evalW L) (evalS S)). Qed.

Lemma sym_modeB_0101 (L : list WTok) (S : list STok) :
  cfg_modeB (evalW L) (evalS (T0101 :: S)) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_modeB_0101 (evalW L) (evalS S)). Qed.

Lemma sym_modeB_011 (L : list WTok) (S : list STok) :
  cfg_modeB (evalW L) (evalS (T011 :: S)) -->+ cfg_modeF (evalW (W010 :: L)) (evalS S).
Proof. exact (step_modeB_011 (evalW L) (evalS S)). Qed.

Lemma sym_modeF_0100 (L : list WTok) (S : list STok) :
  cfg_modeF (evalW L) (evalS (T0100 :: S)) -->+ cfg_h01B (evalW L) (evalS (T0100 :: S)).
Proof. exact (step_modeF_0100 (evalW L) (evalS S)). Qed.

Lemma sym_modeF_0101 (L : list WTok) (S : list STok) :
  cfg_modeF (evalW L) (evalS (T0101 :: S)) -->+ cfg_modeB (evalW (W1010 :: L)) (evalS S).
Proof. exact (step_modeF_0101 (evalW L) (evalS S)). Qed.

Lemma sym_modeF_011 (L : list WTok) (S : list STok) :
  cfg_modeF (evalW L) (evalS (T011 :: S)) -->+ cfg_modeF (evalW (W010 :: L)) (evalS S).
Proof. exact (step_modeF_011 (evalW L) (evalS S)). Qed.

Fixpoint shift (b : bool) (u : list WTok) {struct u} : list WTok :=
  match b, u with
  | true, [] => [W100]
  | true, W0010 :: m => W100 :: W010 :: m
  | true, W0110 :: m => W100 :: W110 :: m
  | true, W010 :: m => W100 :: shift true m
  | true, W1010 :: m => W1010 :: shift true m
  | true, W100 :: m => W1010 :: shift false m
  | true, W110 :: m => W110 :: m
  | true, W1110 :: m => W1110 :: m
  | false, [] => []
  | false, W010 :: m => W0010 :: m
  | false, W110 :: m => W0110 :: m
  | false, W100 :: m => W010 :: shift false m
  | false, W1010 :: m => W010 :: shift true m
  | false, W0010 :: m => W0010 :: m
  | false, W0110 :: m => W0110 :: m
  | false, W1110 :: m => W1110 :: m
  end.

Definition isHigh (u : list WTok) : bool :=
  match u with
  | W1010 :: _ | W0010 :: _ | W1110 :: _ | W0110 :: _ => true
  | _ => false
  end.

Fixpoint dem (b : bool) (u : list WTok) {struct u} : nat :=
  match b, u with
  | false, [] => 0
  | true, [] => 3
  | _, W1010 :: m => (dem true m + 1) / 2
  | _, W0010 :: m => (dem true m + 1) / 2 + 1
  | _, W1110 :: m => (dem true m + 1) / 2 + 1
  | _, W0110 :: m => (dem true m + 1) / 2 + 2
  | true, W100 :: m => 2 * dem false m
  | true, W010 :: m => 2 * dem false m + 1
  | true, W110 :: m => Nat.max 3 (2 * dem false m + 2)
  | false, W010 :: m => 3 * dem false m
  | false, W110 :: m => 3 * dem false m - 1
  | false, W100 :: m => 3 * dem false m - 2
  end.

Fixpoint potF (b : bool) (u : list WTok) {struct u} : nat :=
  match b, u with
  | false, [] => 2
  | true, [] => 4
  | _, W1010 :: m => (potF true m + 4) / 2
  | _, W0010 :: m => (potF true m + 4) / 2
  | _, W1110 :: m => (potF true m + 4) / 2
  | _, W0110 :: m => (potF true m + 4) / 2
  | true, W010 :: m => 2 * potF false m + 1
  | true, W100 :: m => 2 * potF false m + 2
  | true, W110 :: m => 2 * potF false m + 3
  | false, W010 :: m => Nat.max 3 (3 * potF false m - 5)
  | false, W110 :: m => Nat.max 3 (3 * potF false m - 4)
  | false, W100 :: m => 3 * potF false m - 3
  end.

Local Opaque Nat.div Nat.max.

Lemma evalW_shift : forall (b : bool) (u : list WTok),
  dem b u = 0 ->
  evalW (shift b u) =
    (if b then 1%sym >> 0%sym >> evalW u else 0%sym >> evalW u).
Proof.
  intros b u; revert b.
  induction u as [| t m IH]; intros [|] H.
  - simpl in H; discriminate.
  - simpl; apply const_unfold.
  - destruct t; simpl in H |- *; try reflexivity; try omega_div.
    + assert (Hm : dem false m = 0) by omega_div.
      rewrite (IH false Hm); reflexivity.
    + assert (Hm : dem true m = 0) by omega_div.
      rewrite (IH true Hm); reflexivity.
  - destruct t; simpl in H |- *; try reflexivity; try omega_div.
    + assert (Hm : dem false m = 0) by omega_div.
      rewrite (IH false Hm); reflexivity.
    + assert (Hm : dem true m = 0) by omega_div.
      rewrite (IH true Hm); reflexivity.
Qed.

Lemma potF_ge (u : list WTok) : potF false u >= 2 /\ potF true u >= 4.
Proof.
  induction u as [| t m [IHf IHt]]; [simpl; lia |].
  destruct t; simpl; split; omega_div.
Qed.

Lemma potF_true_le (u : list WTok) : potF true u <= 2 * potF false u + 3.
Proof.
  destruct u as [| t m]; [simpl; lia |].
  destruct (potF_ge m) as [HpF HpT].
  destruct t; simpl; omega_div.
Qed.

Lemma dem_true_of_dem_false_zero {u : list WTok} (H : dem false u = 0) :
  dem true u <= 3.
Proof.
  destruct u as [| t m]; [simpl; lia |].
  destruct t; simpl in H |- *; omega_div.
Qed.

Lemma isHigh_shift_true {u : list WTok} (H : dem true u = 0) :
  isHigh (shift true u) = true.
Proof.
  destruct u as [| t m]; [simpl in H; discriminate |].
  destruct t; simpl in H |- *; try reflexivity; omega_div.
Qed.

Lemma shift_false_true_le {m : list WTok} (Hm : dem false m = 0)
    (IHf2 : potF false (shift false m) <= 3 * potF false m - 4) :
  3 * dem true (shift false m) <= 2 * dem false (shift false m) + 9 /\
  potF true (shift false m) <= 2 * potF false m + 2.
Proof.
  destruct m as [| t n]; [simpl; lia |].
  destruct (potF_ge n) as [HpF HpT].
  pose proof (potF_true_le n) as Hptle.
  destruct t.
  -  
    assert (Hn : dem false n = 0) by (simpl in Hm; omega_div).
    pose proof (dem_true_of_dem_false_zero Hn) as Hdt.
    simpl; split; omega_div.
  -   simpl in Hm; omega_div.
  -   simpl in Hm; omega_div.
  -  
    simpl in IHf2 |- *.
    revert IHf2; generalize (shift false n); intros s IHf2.
    simpl in IHf2 |- *.
    split; omega_div.
  -  
    assert (Hn : dem false n = 0) by (simpl in Hm; omega_div).
    pose proof (dem_true_of_dem_false_zero Hn) as Hdt.
    simpl; split; omega_div.
  -  
    simpl in IHf2 |- *.
    revert IHf2; generalize (shift true n); intros s IHf2.
    simpl in IHf2 |- *.
    split; omega_div.
  -   simpl in Hm; omega_div.
Qed.

Lemma shift_true_false_eq {m : list WTok} (H : dem true m = 0) :
  dem false (shift true m) = dem true (shift true m) /\
  potF false (shift true m) = potF true (shift true m).
Proof.
  destruct m as [| t n]; [simpl in H; discriminate |].
  destruct t; simpl in H |- *; try (split; reflexivity); omega_div.
Qed.

Lemma shift_bounds (u : list WTok) :
  (dem false u = 0 ->
    2 * dem false (shift false u) <= 6 * potF false u - 9 /\
    potF false (shift false u) <= 3 * potF false u - 4) /\
  (dem true u = 0 ->
    2 * dem true (shift true u) <= potF true u - 2 /\
    potF true (shift true u) <= (potF true u + 4) / 2).
Proof.
  induction u as [| t m [IHf IHt]].
  - split; intro H; [simpl; lia | simpl in H; discriminate].
  - destruct (potF_ge m) as [HpF HpT].
    pose proof (potF_true_le m) as Hptle.
    destruct t.
    +  
      split; intro H.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        pose proof (dem_true_of_dem_false_zero Hm) as Hdt.
        simpl; split; omega_div.
      * simpl in H; omega_div.
    +  
      split; intro H; simpl in H; omega_div.
    +  
      split; intro H; simpl in H; omega_div.
    +  
      split; intro H.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        destruct (IHf Hm) as [IHf1 IHf2].
        simpl; split; omega_div.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        destruct (IHf Hm) as [IHf1 IHf2].
        destruct (shift_false_true_le Hm IHf2) as [Hsf1 Hsf2].
        simpl; split; omega_div.
    +  
      split; intro H.
      * assert (Hm : dem false m = 0) by (simpl in H; omega_div).
        pose proof (dem_true_of_dem_false_zero Hm) as Hdt.
        simpl; split; omega_div.
      * simpl in H; omega_div.
    +  
      split; intro H.
      * assert (Hm : dem true m = 0) by (simpl in H; omega_div).
        destruct (IHt Hm) as [IHt1 IHt2].
        destruct (shift_true_false_eq Hm) as [Hst1 Hst2].
        simpl; split; omega_div.
      * assert (Hm : dem true m = 0) by (simpl in H; omega_div).
        destruct (IHt Hm) as [IHt1 IHt2].
        simpl; split; omega_div.
    +  
      split; intro H; simpl in H; omega_div.
Qed.

Definition ExitAt (S : list STok) (isB : bool) (L' : list WTok) : Q * tape :=
  if isB then cfg_modeB (evalW L') (evalS S) else cfg_modeF (evalW (W010 :: L')) (evalS S).

Definition StepOK (lw : list WTok) (isB : bool) (next : list WTok) : Prop :=
  match lw with
  | [] => isB = true /\ next = [W100]
  | W010 :: rest => isB = true /\ next = W110 :: rest
  | W110 :: rest => isB = true /\ next = W100 :: rest
  | W100 :: rest =>
    isB = false /\
    dem false next <= dem false rest - 1 /\
    potF false next <= potF false rest + 1
  | _ =>
    isB = true /\
    isHigh next = true /\
    dem false next <= dem false lw - 1 /\
    potF false next <= potF false lw + 1
  end.

Lemma stepOK_of_isHigh {w next : list WTok} {isB : bool}
    (Hw : isHigh w = true) (Hok : StepOK w isB next) :
  isB = true /\ isHigh next = true /\
  dem false next <= dem false w - 1 /\
  potF false next <= potF false w + 1.
Proof.
  destruct w as [| t rest]; [simpl in Hw; discriminate |].
  destruct t; simpl in Hw; try discriminate; exact Hok.
Qed.

Lemma dem_potF_of_isHigh {w : list WTok} (Hw : isHigh w = true) :
  dem true w = dem false w /\ potF true w = potF false w.
Proof.
  destruct w as [| t rest]; [simpl in Hw; discriminate |].
  destruct t; simpl in Hw; try discriminate; split; reflexivity.
Qed.

Lemma stepOK_W100_true {M next : list WTok} (Hok : StepOK M true next) :
  StepOK (W100 :: M) false next.
Proof.
  destruct M as [| t rest].
  - destruct Hok as [_ ->].
    simpl; repeat split; lia.
  - destruct t.
    + destruct Hok as [_ ->]; simpl; repeat split; omega_div.
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
    + destruct Hok as [Hb _]; discriminate.
    + destruct Hok as [_ ->]; simpl; repeat split; omega_div.
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
    + destruct Hok as [_ [_ [Hd1 Hp]]]; exact (conj eq_refl (conj Hd1 Hp)).
Qed.

Lemma stepOK_W100_false {M K : list WTok} (Hok : StepOK M false K) :
  StepOK (W100 :: M) false (W010 :: K).
Proof.
  destruct M as [| t rest]; [destruct Hok as [Hb _]; discriminate |].
  destruct t; try (destruct Hok as [Hb _]; discriminate).
  destruct Hok as [_ [Hd1 Hp]].
  destruct (potF_ge rest) as [HpR _].
  simpl; repeat split; omega_div.
Qed.

Lemma stepOK_W1010_TT {M M1 M2 : list WTok}
    (Hok1 : StepOK M true M1) (Hok2 : StepOK M1 true M2) :
  StepOK (W1010 :: M) true (W1010 :: M2).
Proof.
  destruct M as [| t rest].
  - destruct Hok1 as [_ ->]; destruct Hok2 as [Hb _]; discriminate.
  - destruct t.
    +  
      destruct Hok1 as [_ ->].
      destruct Hok2 as [_ ->].
      simpl; repeat split; omega_div.
    +  
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
    +  
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
    +   destruct Hok1 as [Hb _]; discriminate.
    +   destruct Hok1 as [_ ->]; destruct Hok2 as [Hb _]; discriminate.
    +  
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
    +  
      destruct Hok1 as [_ [Hm1 [Hd1 Hp1]]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [_ [Hm2 [Hd2 Hp2]]].
      destruct (dem_potF_of_isHigh Hm2) as [Hdt2 Hpt2].
      simpl in Hd1, Hp1 |- *; repeat split; omega_div.
Qed.

Lemma stepOK_W1010_TF {M M1 M2 : list WTok}
    (Hok1 : StepOK M true M1) (Hok2 : StepOK M1 false M2) :
  StepOK (W1010 :: M) true (W1010 :: W010 :: M2).
Proof.
  destruct M as [| t rest].
  - destruct Hok1 as [_ ->].
    destruct Hok2 as [_ [Hd2 Hp2]].
    simpl in Hd2, Hp2 |- *; repeat split; omega_div.
  - destruct t.
    +   destruct Hok1 as [_ ->]; destruct Hok2 as [Hb _]; discriminate.
    +  
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
    +  
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
    +   destruct Hok1 as [Hb _]; discriminate.
    +  
      destruct Hok1 as [_ ->].
      destruct Hok2 as [_ [Hd2 Hp2]].
      simpl in Hd2, Hp2 |- *; repeat split; omega_div.
    +  
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
    +  
      destruct Hok1 as [_ [Hm1 _]].
      destruct (stepOK_of_isHigh Hm1 Hok2) as [Hb _]; discriminate.
Qed.

Lemma stepOK_W1010_F {M M1 : list WTok}
    (Hok1 : StepOK M false M1) :
  StepOK (W1010 :: M) true (W1010 :: W100 :: M1).
Proof.
  destruct M as [| t rest]; [destruct Hok1 as [Hb _]; discriminate |].
  destruct t; try (destruct Hok1 as [Hb _]; discriminate).
  destruct Hok1 as [_ [Hd1 Hp1]].
  simpl in Hd1, Hp1 |- *; repeat split; omega_div.
Qed.

Lemma pass_W100_B {M M' : list WTok}
    (H : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeB (evalW M') (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W100 :: M)) (evalS S) -->+ cfg_modeF (evalW (W010 :: M')) (evalS S).
Proof.
  exact (ptrans (sym_h01B_100 M S) (ptrans (H (T011 :: S)) (sym_modeB_011 M' S))).
Qed.

Lemma pass_W100_F {M M' : list WTok}
    (H : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeF (evalW M') (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W100 :: M)) (evalS S) -->+ cfg_modeF (evalW (W010 :: M')) (evalS S).
Proof.
  exact (ptrans (sym_h01B_100 M S) (ptrans (H (T011 :: S)) (sym_modeF_011 M' S))).
Qed.

Lemma pass_W1010_BB {M M1 M2 : list WTok}
    (H1 : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeB (evalW M1) (evalS S))
    (H2 : forall S : list STok, cfg_h01B (evalW M1) (evalS S) -->+ cfg_modeB (evalW M2) (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: M2)) (evalS S).
Proof.
  exact (ptrans (sym_h01B_1010 M S)
    (ptrans (H1 (T0100 :: S))
      (ptrans (sym_modeB_0100 M1 S)
        (ptrans (H2 (T0101 :: S))
          (sym_modeB_0101 M2 S))))).
Qed.

Lemma pass_W1010_BF {M M1 M2 : list WTok}
    (H1 : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeB (evalW M1) (evalS S))
    (H2 : forall S : list STok, cfg_h01B (evalW M1) (evalS S) -->+ cfg_modeF (evalW M2) (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: M2)) (evalS S).
Proof.
  exact (ptrans (sym_h01B_1010 M S)
    (ptrans (H1 (T0100 :: S))
      (ptrans (sym_modeB_0100 M1 S)
        (ptrans (H2 (T0101 :: S))
          (sym_modeF_0101 M2 S))))).
Qed.

Lemma pass_W1010_F {M M1 : list WTok}
    (H1 : forall S : list STok, cfg_h01B (evalW M) (evalS S) -->+ cfg_modeF (evalW (W010 :: M1)) (evalS S))
    (S : list STok) :
  cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: W100 :: M1)) (evalS S).
Proof.
  exact (ptrans (sym_h01B_1010 M S)
    (ptrans (H1 (T0100 :: S))
      (ptrans (sym_modeF_0100 (W010 :: M1) S)
        (ptrans (sym_h01B_010 M1 (T0100 :: S))
          (ptrans (sym_modeB_0100 (W110 :: M1) S)
            (ptrans (sym_h01B_110 M1 (T0101 :: S))
              (sym_modeB_0101 (W100 :: M1) S))))))).
Qed.

Fixpoint TreeW (n : nat) (L : list WTok) : Prop :=
  match n with
  | O => True
  | S n' =>
    exists (isB : bool) (next : list WTok),
      StepOK L isB next /\
      (forall S : list STok, cfg_h01B (evalW L) (evalS S) -->+ ExitAt S isB next) /\
      TreeW n' next
  end.

Lemma treeW_succ : forall {n : nat} {L : list WTok}, TreeW (S n) L -> TreeW n L.
Proof.
  induction n as [| n IH]; intros L H.
  - exact I.
  - destruct H as [isB [next [Hok [Hstep Hsub]]]].
    exists isB, next; split; [exact Hok | split; [exact Hstep | exact (IH next Hsub)]].
Qed.

Lemma treeW_triple (n : nat) :
  (forall M : list WTok, TreeW n M -> TreeW n (W100 :: M)) /\
  (forall M : list WTok, TreeW n M -> TreeW n (W110 :: M)) /\
  (forall M : list WTok, TreeW n M -> TreeW n (W010 :: M)).
Proof.
  induction n as [| n [IH100 [IH110 IH010]]].
  - repeat split; intros; exact I.
  - repeat split; intros M H.
    + destruct H as [[|] [next [Hok [Hstep Hsub]]]].
      * exists false, next; split; [exact (stepOK_W100_true Hok) | split; [exact (pass_W100_B Hstep) | exact Hsub]].
      * exists false, (W010 :: next); split;
          [exact (stepOK_W100_false Hok) | split; [exact (pass_W100_F Hstep) | exact (IH010 next Hsub)]].
    + exists true, (W100 :: M); split; [split; reflexivity | split; [exact (sym_h01B_110 M) | exact (IH100 M (treeW_succ H))]].
    + exists true, (W110 :: M); split; [split; reflexivity | split; [exact (sym_h01B_010 M) | exact (IH110 M (treeW_succ H))]].
Qed.

Lemma treeW_W100 {n : nat} {M : list WTok} (H : TreeW n M) : TreeW n (W100 :: M).
Proof. exact (proj1 (treeW_triple n) M H). Qed.

Lemma treeW_W110 {n : nat} {M : list WTok} (H : TreeW n M) : TreeW n (W110 :: M).
Proof. exact (proj1 (proj2 (treeW_triple n)) M H). Qed.

Lemma treeW_W010 {n : nat} {M : list WTok} (H : TreeW n M) : TreeW n (W010 :: M).
Proof. exact (proj2 (proj2 (treeW_triple n)) M H). Qed.

Lemma treeW_nil (n : nat) : TreeW n [].
Proof.
  induction n as [| n IH]; [exact I |].
  exists true, [W100]; split; [split; reflexivity | split; [exact sym_h01B_nil | exact (treeW_W100 IH)]].
Qed.

Lemma treeW_W1010_step {n : nat} {M : list WTok} (t : TreeW (S (S n)) M) :
  exists next : list WTok,
    StepOK (W1010 :: M) true (W1010 :: next) /\
    (forall S : list STok,
      cfg_h01B (evalW (W1010 :: M)) (evalS S) -->+ cfg_modeB (evalW (W1010 :: next)) (evalS S)) /\
    TreeW n next.
Proof.
  destruct t as [[|] [M1 [Hok1 [Hstep1 Hsub1]]]].
  - destruct Hsub1 as [[|] [M2 [Hok2 [Hstep2 Hsub2]]]].
    + exists M2; split;
        [exact (stepOK_W1010_TT Hok1 Hok2) | split; [exact (pass_W1010_BB Hstep1 Hstep2) | exact Hsub2]].
    + exists (W010 :: M2); split;
        [exact (stepOK_W1010_TF Hok1 Hok2) | split; [exact (pass_W1010_BF Hstep1 Hstep2) | exact (treeW_W010 Hsub2)]].
  - exists (W100 :: M1); split;
      [exact (stepOK_W1010_F Hok1) | split; [exact (pass_W1010_F Hstep1) | exact (treeW_W100 (treeW_succ Hsub1))]].
Qed.

Lemma treeW_W1010 : forall (n : nat) {M : list WTok}, TreeW (2 * n) M -> TreeW n (W1010 :: M).
Proof.
  induction n as [| n IH]; intros M t; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  destruct (treeW_W1010_step t) as [next [Hok [Hstep Hsub]]].
  exists true, (W1010 :: next); split; [exact Hok | split; [exact Hstep | exact (IH next Hsub)]].
Qed.

Lemma treeW_W0010 {n : nat} {M : list WTok} (t : TreeW (2 * n) M) : TreeW n (W0010 :: M).
Proof.
  destruct n as [| n]; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  exists true, (W1010 :: M); repeat split.
  - simpl; omega_div.
  - simpl; omega_div.
  - exact (sym_h01B_0010 M).
  - exact (treeW_W1010 n (treeW_succ (treeW_succ t))).
Qed.

Lemma treeW_W1110 {n : nat} {M : list WTok} (t : TreeW (2 * n) M) : TreeW n (W1110 :: M).
Proof.
  destruct n as [| n]; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  exists true, (W1010 :: M); repeat split.
  - simpl; omega_div.
  - simpl; omega_div.
  - exact (sym_h01B_1110 M).
  - exact (treeW_W1010 n (treeW_succ (treeW_succ t))).
Qed.

Lemma treeW_W0110 {n : nat} {M : list WTok} (t : TreeW (2 * n) M) : TreeW n (W0110 :: M).
Proof.
  destruct n as [| n]; [exact I |].
  replace (2 * S n) with (S (S (2 * n))) in t by lia.
  exists true, (W1110 :: M); repeat split.
  - simpl; omega_div.
  - simpl; omega_div.
  - exact (sym_h01B_0110 M).
  - exact (treeW_W1110 (treeW_succ (treeW_succ t))).
Qed.

Lemma buildTreeW (L : list WTok) : forall n : nat, TreeW n L.
Proof.
  induction L as [| t M IH]; intro n.
  - exact (treeW_nil n).
  - destruct t.
    + exact (treeW_W010 (IH n)).
    + exact (treeW_W0010 (IH (2 * n))).
    + exact (treeW_W0110 (IH (2 * n))).
    + exact (treeW_W100 (IH n)).
    + exact (treeW_W110 (IH n)).
    + exact (treeW_W1010 n (IH (2 * n))).
    + exact (treeW_W1110 (IH (2 * n))).
Qed.

Lemma step_modeB_reparse {u w : list WTok}
    (Heq : 1%sym >> 0%sym >> evalW u = evalW w) :
  cfg_modeB (evalW u) (evalS []) -->+ cfg_h01B (evalW w) (evalS []).
Proof.
  rewrite <- Heq.
  exact (step_modeB_base (evalW u)).
Qed.

Definition w4 : list WTok := [W1010; W1010; W1010; W0010; W1010; W010; W100].

Lemma step_init_to_w4 :
  c0 -->+ cfg_h01B (evalW w4) (evalS []).
Proof.
  unfold w4.
  pose proof (pass_W1010_BF sym_h01B_nil (pass_W100_B sym_h01B_nil)) as Hw1.
  pose proof (pass_W1010_F (pass_W100_B Hw1)) as Hw2.
  pose proof (pass_W1010_BB (sym_h01B_010 [W100; W1010]) (sym_h01B_110 [W100; W1010])) as Hw3_a.
  pose proof (pass_W1010_F (pass_W100_F (pass_W100_B Hw1))) as Hw3_b.
  pose proof (pass_W1010_BB Hw3_a Hw3_b) as Hw3.
  assert (Hp0 : c0 -->+ cfg_h01B (evalW [W1010]) (evalS [])).
  { eapply ptrans; [exact step_init_to_h01B |].
    eapply ptrans; [exact (sym_h01B_nil []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  assert (Hp1 : cfg_h01B (evalW [W1010]) (evalS []) -->+
      cfg_h01B (evalW [W1010; W100; W1010]) (evalS [])).
  { eapply ptrans; [exact (Hw1 []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  assert (Hp2 : cfg_h01B (evalW [W1010; W100; W1010]) (evalS []) -->+
      cfg_h01B (evalW [W1010; W1010; W010; W100; W1010]) (evalS [])).
  { eapply ptrans; [exact (Hw2 []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  assert (Hp3 : cfg_h01B (evalW [W1010; W1010; W010; W100; W1010]) (evalS []) -->+
      cfg_h01B (evalW [W1010; W1010; W1010; W0010; W1010; W010; W100]) (evalS [])).
  { eapply ptrans; [exact (Hw3 []) |].
    apply step_modeB_reparse; simpl; repeat rewrite <- const_unfold; reflexivity. }
  exact (ptrans Hp0 (ptrans Hp1 (ptrans Hp2 Hp3))).
Qed.

Definition CfgW (w : list WTok) : Q * tape :=
  cfg_h01B (evalW w) (evalS []).

Definition InvW (w : list WTok) : Prop :=
  isHigh w = true /\ dem false w <= 1 /\ potF false w <= 4.

Lemma invW_step (w : list WTok) (H : InvW w) :
  exists w' : list WTok, CfgW w -->+ CfgW w' /\ InvW w'.
Proof.
  destruct H as [Hw [Hd Hp]].
  destruct (buildTreeW w 1) as [isB [u [Hok [Hstep _]]]].
  destruct (stepOK_of_isHigh Hw Hok) as [-> [Hu_high [Hu_dem1 Hu_pot]]].
  destruct (dem_potF_of_isHigh Hu_high) as [Hdu_eq Hpu_eq].
  assert (Hdu : dem true u = 0) by lia.
  assert (Hpu : potF true u <= 5) by lia.
  pose proof (isHigh_shift_true Hdu) as Hw'_high.
  destruct (dem_potF_of_isHigh Hw'_high) as [Hdw'_eq Hpw'_eq].
  destruct (proj2 (shift_bounds u) Hdu) as [Hb_dem Hb_pot].
  exists (shift true u).
  split.
  - unfold CfgW.
    eapply ptrans; [exact (Hstep []) |].
    apply step_modeB_reparse.
    symmetry; exact (evalW_shift true u Hdu).
  - unfold InvW.
    split; [exact Hw'_high | split; omega_div].
Qed.

Local Transparent Nat.div Nat.max.

Theorem nonhalt: ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := CfgW w4).
  - exact (pev step_init_to_w4).
  - eapply progress_nonhalt_cond with (C := CfgW) (P := InvW) (i0 := w4).
    + exact invW_step.
    + unfold InvW, w4; simpl; repeat split; lia.
Qed.

End TM6.
Print Assumptions TM6.nonhalt.
