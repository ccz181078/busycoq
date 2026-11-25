(* 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- never halts. *)

From Coq Require Import Lia ZifyNat ZifyN PeanoNat Bool String Lists.Streams List NArith ZArith QArith Lqa.
From BusyCoq Require Import Individual62.
Import ListNotations.

Open Scope list_scope.
Open Scope sym_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm := Eval compute in
  (TM_from_str "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---").

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

(* Section 1: Tape words, Call, Side, Seg, atomic Seg lemmas, turnaround *)

Definition V_u : list Sym := [1; 1; 0; 0]%sym.
Definition K_u : list Sym := [0; 0]%sym.
Definition Q_u : list Sym := [1; 0]%sym.
Definition Vp  : list Sym := [0; 1; 1; 0]%sym.
Definition Kp  : list Sym := [0; 0]%sym.
Definition Qp  : list Sym := [0; 1]%sym.

Lemma z00 : 0%sym >> 0inf%sym = 0inf%sym.
Proof. symmetry. apply const_unfold. Qed.

Lemma zKd : K_u *> 0inf%sym = 0inf%sym.
Proof. solve_const0_eq. Qed.

Lemma zKpd : Kp *> 0inf%sym = 0inf%sym.
Proof. solve_const0_eq. Qed.

Inductive Call : Type :=
  | ch
  | cb
  | cf
  | ck.

Definition zInQ (c : Call) : Q :=
  match c with
  | ch | cb => E
  | cf | ck => C
  end.

Definition zInB (c : Call) : Sym :=
  match c with
  | ch | cb => 1%sym
  | cf | ck => 0%sym
  end.

Definition zExQ (c : Call) : Q :=
  match c with
  | ch => A
  | cb => B
  | cf => F
  | ck => B
  end.

Definition zExB (c : Call) : Sym :=
  match c with
  | ch | cb => 1%sym
  | cf | ck => 0%sym
  end.

Definition zCR (w : side) (c : Call) (r : side) : Q * tape :=
  w <{{zInQ c}} ([zInB c] *> r).

Definition zCL (w : side) (c : Call) (r : side) : Q * tape :=
  w {{zExQ c}}> ([zExB c] *> r).

Definition zCf (w : side) : Q * tape :=
  ([0]%sym *> w) {{A}}> 0inf%sym.

Definition z0f (c : Call) (w1 w2 : side) : Prop :=
  forall r, zCR w1 c r -->+ zCL w2 c r.

Inductive Side : list Call -> side -> side -> Prop :=
  | Side_nil (w : side) : Side [] w w
  | Side_cons {c : Call} {ls : list Call} {w1 w2 w3 : side} :
      z0f c w1 w2 -> Side ls w2 w3 -> Side (c :: ls) w1 w3.

Definition Seg (ls_in ls_out : list Call) (w1 w2 : list Sym) : Prop :=
  forall u1 u2, Side ls_out u1 u2 -> Side ls_in (w1 *> u1) (w2 *> u2).

Lemma lpow_0 {A : Type} (l : list A) : l ^^ 0 = [].
Proof. reflexivity. Qed.

Lemma lpow_1 {A : Type} (l : list A) : l ^^ 1 = l.
Proof. cbn. apply app_nil_r. Qed.

Lemma lpow_1_add {A : Type} (l : list A) (n : nat) : l ^^ (1 + n) = l ++ l ^^ n.
Proof. reflexivity. Qed.

Lemma z0j {ls1 ls2 : list Call} {w1 w2 w3 : side}
    (h1 : Side ls1 w1 w2) (h2 : Side ls2 w2 w3) : Side (ls1 ++ ls2) w1 w3.
Proof.
  induction h1 as [w | c ls u1 u2 u3 hc _ ih].
  - exact h2.
  - exact (Side_cons hc (ih h2)).
Qed.

Lemma z0k {ls1 ls2 : list Call} {w1 w3 : side}
    (h : Side (ls1 ++ ls2) w1 w3) : exists w2, Side ls1 w1 w2 /\ Side ls2 w2 w3.
Proof.
  revert w1 h.
  induction ls1 as [| c ls1 ih]; intros w1 h.
  - exists w1. split; [exact (Side_nil w1) | exact h].
  - inversion h as [| c' ls' w1' wmid w3' hc hrest]; subst.
    destruct (ih wmid hrest) as [w2 [h1 h2]].
    exists w2. split; [exact (Side_cons hc h1) | exact h2].
Qed.

Lemma z0l (w : list Sym) : Seg [] [] w w.
Proof.
  intros u1 u2 h. inversion h; subst. exact (Side_nil (w *> u2)).
Qed.

Lemma zSc {ls1 ls2 : list Call} {w1 w2 : list Sym} {u1 u2 : side}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 u1 u2) :
    Side ls1 (w1 *> u1) (w2 *> u2).
Proof.
  exact (h1 u1 u2 h2).
Qed.

Lemma zSg {ls1 ls2 ls3 ls4 : list Call} {w1 w2 w3 : list Sym}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3.
Proof.
  intros u1 u3 h.
  destruct (z0k h) as [u2 [ha hb]].
  exact (z0j (h1 u1 u2 ha) (h2 u2 u3 hb)).
Qed.

Lemma zS0 {ls1 ls2 ls3 : list Call} {w1 w2 v1 v2 : list Sym}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2).
Proof.
  intros u1 u2 h.
  rewrite !Str_app_assoc.
  exact (h1 (v1 *> u1) (v2 *> u2) (h2 u1 u2 h)).
Qed.

Lemma zSC0 {c : Call} {w1 w2 : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c r -->+ zCL (w2 *> u) c r) :
    Seg [c] [] w1 w2.
Proof.
  intros u1 u2 h. inversion h; subst.
  exact (Side_cons (fun r => h1 u2 r) (Side_nil _)).
Qed.

Lemma zSC1 {c_in c1 : Call} {w1 w2 mid1 : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c_in r -->+ zCR u c1 (mid1 *> r))
    (h2 : forall u r, zCL u c1 (mid1 *> r) -->+ zCL (w2 *> u) c_in r) :
    Seg [c_in] [c1] w1 w2.
Proof.
  intros u1 u2 h.
  inversion h as [| ? ? ? u_mid ? hc1 hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun r => _) (Side_nil _)).
  exact (ptrans (h1 u1 r) (ptrans (hc1 (mid1 *> r)) (h2 u2 r))).
Qed.

Lemma zSC2 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c_in r -->+ zCR u c1 (mid1 *> r))
    (h2 : forall u r, zCL u c1 (mid1 *> r) -->+ zCR u c2 (mid2 *> r))
    (h3 : forall u r, zCL u c2 (mid2 *> r) -->+ zCL (w2 *> u) c_in r) :
    Seg [c_in] [c1; c2] w1 w2.
Proof.
  intros u1 u3 h.
  inversion h as [| ? ? ? u2 ? hc1 hrest]; subst.
  inversion hrest as [| ? ? ? u3' ? hc2 hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun r => _) (Side_nil _)).
  exact (ptrans (h1 u1 r)
    (ptrans (hc1 (mid1 *> r))
      (ptrans (h2 u2 r)
        (ptrans (hc2 (mid2 *> r)) (h3 u3 r))))).
Qed.

Lemma zSC3 {c_in c1 c2 c3 : Call} {w1 w2 mid1 mid2 mid3 : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c_in r -->+ zCR u c1 (mid1 *> r))
    (h2 : forall u r, zCL u c1 (mid1 *> r) -->+ zCR u c2 (mid2 *> r))
    (h3 : forall u r, zCL u c2 (mid2 *> r) -->+ zCR u c3 (mid3 *> r))
    (h4 : forall u r, zCL u c3 (mid3 *> r) -->+ zCL (w2 *> u) c_in r) :
    Seg [c_in] [c1; c2; c3] w1 w2.
Proof.
  intros u1 u4 h.
  inversion h as [| ? ? ? u2 ? hc1 hr1]; subst.
  inversion hr1 as [| ? ? ? u3 ? hc2 hr2]; subst.
  inversion hr2 as [| ? ? ? u4' ? hc3 hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun r => _) (Side_nil _)).
  exact (ptrans (h1 u1 r)
    (ptrans (hc1 (mid1 *> r))
      (ptrans (h2 u2 r)
        (ptrans (hc2 (mid2 *> r))
          (ptrans (h3 u3 r)
            (ptrans (hc3 (mid3 *> r)) (h4 u4 r))))))).
Qed.

Lemma zSC4 {c_in c1 c2 c3 c4 : Call} {w1 w2 mid1 mid2 mid3 mid4 : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c_in r -->+ zCR u c1 (mid1 *> r))
    (h2 : forall u r, zCL u c1 (mid1 *> r) -->+ zCR u c2 (mid2 *> r))
    (h3 : forall u r, zCL u c2 (mid2 *> r) -->+ zCR u c3 (mid3 *> r))
    (h4 : forall u r, zCL u c3 (mid3 *> r) -->+ zCR u c4 (mid4 *> r))
    (h5 : forall u r, zCL u c4 (mid4 *> r) -->+ zCL (w2 *> u) c_in r) :
    Seg [c_in] [c1; c2; c3; c4] w1 w2.
Proof.
  intros u1 u5 h.
  inversion h as [| ? ? ? u2 ? hc1 hr1]; subst.
  inversion hr1 as [| ? ? ? u3 ? hc2 hr2]; subst.
  inversion hr2 as [| ? ? ? u4 ? hc3 hr3]; subst.
  inversion hr3 as [| ? ? ? u5' ? hc4 hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun r => _) (Side_nil _)).
  exact (ptrans (h1 u1 r)
    (ptrans (hc1 (mid1 *> r))
      (ptrans (h2 u2 r)
        (ptrans (hc2 (mid2 *> r))
          (ptrans (h3 u3 r)
            (ptrans (hc3 (mid3 *> r))
              (ptrans (h4 u4 r)
                (ptrans (hc4 (mid4 *> r)) (h5 u5 r))))))))).
Qed.

(* 17 atomic Seg lemmas *)
Lemma seg_cf_1 : Seg [cf] [] [1]%sym [1]%sym.
Proof.
  apply zSC0; intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_cb_Q_ch : Seg [cb] [ch] [1; 0]%sym [1; 0]%sym.
Proof.
  eapply (zSC1 (mid1 := [0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_cb_Vj_nil : Seg [cb] [] [1; 0; 0; 0]%sym [1; 0; 0; 1]%sym.
Proof.
  apply zSC0; intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_cb_Va_dbl : Seg [cb] [cb; cf; cb; cf] [1; 0; 0; 1]%sym [1; 0; 0; 1]%sym.
Proof.
  eapply (zSC4 (mid1 := [1; 1; 0; 1]%sym) (mid2 := [1; 1; 0; 1]%sym) (mid3 := [0; 1; 0; 1]%sym) (mid4 := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_cb_Va_ch : Seg [cb] [ch] [1; 0; 0; 1]%sym [1; 0; 0; 0]%sym.
Proof.
  eapply (zSC1 (mid1 := [1; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_cb_11_ckch : Seg [cb] [ck; ch] [1; 1]%sym [1; 0]%sym.
Proof.
  eapply (zSC2 (mid1 := [0; 1]%sym) (mid2 := [0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_cb_V_cf : Seg [cb] [cf] [1; 1; 0; 0]%sym [1; 0; 0; 1]%sym.
Proof.
  eapply (zSC1 (mid1 := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_cb_V_ck : Seg [cb] [ck; cb; cf] [1; 1; 0; 0]%sym [1; 0; 0; 1]%sym.
Proof.
  eapply (zSC3 (mid1 := [0; 1; 0; 1]%sym) (mid2 := [0; 1; 0; 1]%sym) (mid3 := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_K : Seg [ch] [] [0; 0]%sym [0; 1]%sym.
Proof.
  apply zSC0; intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_Qp_dbl : Seg [ch] [cb; cf; cb; cf] [0; 1]%sym [0; 1]%sym.
Proof.
  eapply (zSC4 (mid1 := [1; 1]%sym) (mid2 := [1; 1]%sym) (mid3 := [0; 1]%sym) (mid4 := [0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_Qp_ch : Seg [ch] [ch] [0; 1]%sym [0; 0]%sym.
Proof.
  eapply (zSC1 (mid1 := [1; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_Vp_ch : Seg [ch] [ch; ch] [0; 1; 1; 0]%sym [0; 1; 1; 0]%sym.
Proof.
  eapply (zSC2 (mid1 := [0; 1; 1; 1]%sym) (mid2 := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_Q_cbcf : Seg [ch] [cb; cf] [1; 0]%sym [0; 1]%sym.
Proof.
  eapply (zSC2 (mid1 := [0; 1]%sym) (mid2 := [0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_11_cf : Seg [ch] [cf] [1; 1]%sym [0; 1]%sym.
Proof.
  eapply (zSC1 (mid1 := [0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_11_ck : Seg [ch] [ck; cb; cf] [1; 1]%sym [0; 1]%sym.
Proof.
  eapply (zSC3 (mid1 := [0; 1]%sym) (mid2 := [0; 1]%sym) (mid3 := [0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_V_ckch : Seg [ch] [ck; ch] [1; 1; 0; 0]%sym [0; 1; 1; 0]%sym.
Proof.
  eapply (zSC2 (mid1 := [0; 1; 0; 1]%sym) (mid2 := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ck_K : Seg [ck] [] [0; 0]%sym [1; 1]%sym.
Proof.
  apply zSC0; intros u r; unfold zCR, zCL, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress.
Qed.

Definition pairA : list Call := [cb; cf].

Lemma seg_cf_keep (w : list Sym) : Seg [cf] [] (1%sym :: w) (1%sym :: w).
Proof. exact (zS0 seg_cf_1 (z0l w)). Qed.

Lemma seg_pairA_Va_dbl : Seg pairA (pairA ^^ 2) [1; 0; 0; 1]%sym [1; 0; 0; 1]%sym.
Proof.
  pose proof (zSg seg_cb_Va_dbl (seg_cf_keep [0; 0; 1]%sym)) as h.
  cbn in h. exact h.
Qed.

Lemma seg_pairA_Va_pow (n : nat) : Seg (pairA ^^ n) (pairA ^^ (n * 2)) [1; 0; 0; 1]%sym [1; 0; 0; 1]%sym.
Proof.
  induction n as [| n ih].
  - exact (z0l [1; 0; 0; 1]%sym).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite lpow_S, lpow_add.
    exact (zSg seg_pairA_Va_dbl ih).
Qed.

Lemma seg_pairA_Va_half1 : Seg pairA [ch] [1; 0; 0; 1]%sym [1; 0; 0; 0]%sym.
Proof.
  pose proof (zSg seg_cb_Va_ch (seg_cf_keep [0; 0; 0]%sym)) as h.
  cbn in h. exact h.
Qed.

Lemma seg_pairA_Vj_restore : Seg pairA [] [1; 0; 0; 0]%sym [1; 0; 0; 1]%sym.
Proof.
  pose proof (zSg seg_cb_Vj_nil (seg_cf_keep [0; 0; 1]%sym)) as h.
  cbn in h. exact h.
Qed.

Lemma seg_pairA_even_Va (q : nat) : Seg (pairA ^^ (q * 2)) ([ch] ^^ q) [1; 0; 0; 1]%sym [1; 0; 0; 1]%sym.
Proof.
  induction q as [| q ih].
  - exact (z0l [1; 0; 0; 1]%sym).
  - replace (S q * 2) with (2 + q * 2) by lia.
    rewrite lpow_add, lpow_S.
    assert (h2 : Seg (pairA ^^ 2) [ch] [1; 0; 0; 1]%sym [1; 0; 0; 1]%sym).
    { pose proof (zSg seg_pairA_Va_half1 seg_pairA_Vj_restore) as h.
      cbn in h. exact h. }
    exact (zSg h2 ih).
Qed.

Lemma seg_pairA_odd_Va (q : nat) : Seg (pairA ^^ (1 + q * 2)) ([ch] ^^ (1 + q)) [1; 0; 0; 1]%sym [1; 0; 0; 0]%sym.
Proof.
  replace (1 + q * 2) with (q * 2 + 1) by lia.
  replace (1 + q) with (q + 1) by lia.
  rewrite !lpow_add, !lpow_1.
  exact (zSg (seg_pairA_even_Va q) seg_pairA_Va_half1).
Qed.

Lemma seg_pairA_V_cf : Seg pairA [cf] V_u [1; 0; 0; 1]%sym.
Proof.
  pose proof (zSg seg_cb_V_cf (seg_cf_keep [0; 0; 1]%sym)) as h.
  cbn in h. exact h.
Qed.

Lemma seg_pairA_V_ck : Seg pairA ([ck] ++ pairA) V_u [1; 0; 0; 1]%sym.
Proof.
  pose proof (zSg seg_cb_V_ck (seg_cf_keep [0; 0; 1]%sym)) as h.
  cbn in h. exact h.
Qed.

Lemma seg_ch_Vp_pow (n : nat) : Seg ([ch] ^^ n) ([ch] ^^ (n * 2)) Vp Vp.
Proof.
  induction n as [| n ih].
  - exact (z0l Vp).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite lpow_S, lpow_add.
    exact (zSg seg_ch_Vp_ch ih).
Qed.

Lemma seg_pairA_Q_pow (n : nat) : Seg (pairA ^^ n) ([ch] ^^ n) Q_u Q_u.
Proof.
  induction n as [| n ih].
  - exact (z0l Q_u).
  - rewrite !lpow_S.
    assert (h1 : Seg pairA [ch] Q_u Q_u).
    { pose proof (zSg seg_cb_Q_ch (seg_cf_keep [0]%sym)) as h.
      cbn in h. exact h. }
    exact (zSg h1 ih).
Qed.

Lemma seg_ch_Qp_dbl_pow (n : nat) : Seg ([ch] ^^ n) (pairA ^^ (n * 2)) Qp Qp.
Proof.
  induction n as [| n ih].
  - exact (z0l Qp).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite lpow_S, lpow_add.
    assert (h1 : Seg [ch] (pairA ^^ 2) Qp Qp) by (cbn; exact seg_ch_Qp_dbl).
    exact (zSg h1 ih).
Qed.

Lemma seg_ch_K_even (q : nat) : Seg ([ch] ^^ (q * 2)) ([ch] ^^ q) K_u K_u.
Proof.
  induction q as [| q ih].
  - exact (z0l K_u).
  - replace (S q * 2) with (2 + q * 2) by lia.
    rewrite lpow_add, lpow_S.
    assert (h2 : Seg ([ch] ^^ 2) [ch] K_u K_u) by (cbn; exact (zSg seg_ch_K seg_ch_Qp_ch)).
    exact (zSg h2 ih).
Qed.

Lemma seg_ch_K_odd (q : nat) : Seg ([ch] ^^ (1 + q * 2)) ([ch] ^^ q) K_u Qp.
Proof.
  replace (1 + q * 2) with (q * 2 + 1) by lia.
  rewrite lpow_add, lpow_1.
  pose proof (zSg (seg_ch_K_even q) seg_ch_K) as h.
  rewrite app_nil_r in h. exact h.
Qed.

Lemma seg_ch_Qp_even (q : nat) : Seg ([ch] ^^ (q * 2)) ([ch] ^^ q) Qp Qp.
Proof.
  induction q as [| q ih].
  - exact (z0l Qp).
  - replace (S q * 2) with (2 + q * 2) by lia.
    rewrite lpow_add, lpow_S.
    assert (h2 : Seg ([ch] ^^ 2) [ch] Qp Qp).
    { pose proof (zSg seg_ch_Qp_ch seg_ch_K) as h.
      cbn in h |- *. exact h. }
    exact (zSg h2 ih).
Qed.

Lemma seg_ch_Qp_odd (q : nat) : Seg ([ch] ^^ (1 + q * 2)) ([ch] ^^ (1 + q)) Qp K_u.
Proof.
  rewrite !lpow_1_add.
  exact (zSg seg_ch_Qp_ch (seg_ch_K_even q)).
Qed.

Lemma raw_PureA_V_dbl2 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 2)%N) :
    Seg (pairA ^^ (N.to_nat n1)) ([cf] ++ pairA ^^ (N.to_nat n2)) V_u [1; 0; 0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + (N.to_nat n1 - 1)) by lia.
  replace (N.to_nat n2) with ((N.to_nat n1 - 1) * 2) by lia.
  rewrite lpow_1_add.
  exact (zSg seg_pairA_V_cf (seg_pairA_Va_pow (N.to_nat n1 - 1))).
Qed.

Lemma raw_PureA_V_dbl1 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 1)%N) :
    Seg (pairA ^^ (N.to_nat n1)) ([ck] ++ pairA ^^ (N.to_nat n2)) V_u [1; 0; 0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + (N.to_nat n1 - 1)) by lia.
  replace (N.to_nat n2) with (1 + (N.to_nat n1 - 1) * 2) by lia.
  rewrite !lpow_1_add, app_assoc.
  exact (zSg seg_pairA_V_ck (seg_pairA_Va_pow (N.to_nat n1 - 1))).
Qed.

Lemma raw_PureA_V_half0 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 0)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg (pairA ^^ (N.to_nat n1)) ([cf] ++ [ch] ^^ (N.to_nat n2)) V_u [1; 0; 0; 0]%sym.
Proof.
  set (q := N.to_nat n2 - 1).
  replace (N.to_nat n1) with (1 + (1 + q * 2)) by lia.
  replace (N.to_nat n2) with (1 + q) by lia.
  rewrite lpow_1_add.
  exact (zSg seg_pairA_V_cf (seg_pairA_odd_Va q)).
Qed.

Lemma raw_PureA_V_half1 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 1)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg (pairA ^^ (N.to_nat n1)) ([cf] ++ [ch] ^^ (N.to_nat n2)) V_u [1; 0; 0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + N.to_nat n2 * 2) by lia.
  rewrite lpow_1_add.
  exact (zSg seg_pairA_V_cf (seg_pairA_even_Va (N.to_nat n2))).
Qed.

Lemma raw_CfA_V_dbl2 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 2)%N) :
    Seg ([cf] ++ pairA ^^ (N.to_nat n1)) ([cf] ++ pairA ^^ (N.to_nat n2)) V_u [1; 0; 0; 1]%sym.
Proof.
  pose proof (zSg (seg_cf_keep [1; 0; 0]%sym) (raw_PureA_V_dbl2 hn h2)) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CfA_V_dbl1 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 1)%N) :
    Seg ([cf] ++ pairA ^^ (N.to_nat n1)) ([ck] ++ pairA ^^ (N.to_nat n2)) V_u [1; 0; 0; 1]%sym.
Proof.
  pose proof (zSg (seg_cf_keep [1; 0; 0]%sym) (raw_PureA_V_dbl1 hn h2)) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CfA_V_half0 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 0)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg ([cf] ++ pairA ^^ (N.to_nat n1)) ([cf] ++ [ch] ^^ (N.to_nat n2)) V_u [1; 0; 0; 0]%sym.
Proof.
  pose proof (zSg (seg_cf_keep [1; 0; 0]%sym) (raw_PureA_V_half0 hn hp h2)) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CfA_V_half1 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 1)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg ([cf] ++ pairA ^^ (N.to_nat n1)) ([cf] ++ [ch] ^^ (N.to_nat n2)) V_u [1; 0; 0; 1]%sym.
Proof.
  pose proof (zSg (seg_cf_keep [1; 0; 0]%sym) (raw_PureA_V_half1 hn hp h2)) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_PureH_V_dbl1 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 1)%N) :
    Seg ([ch] ^^ (N.to_nat n1)) ([ck] ++ [ch] ^^ (N.to_nat n2)) V_u [0; 1; 1; 0]%sym.
Proof.
  replace (N.to_nat n1) with (1 + (N.to_nat n1 - 1)) by lia.
  replace (N.to_nat n2) with (1 + (N.to_nat n1 - 1) * 2) by lia.
  rewrite !lpow_1_add.
  pose proof (zSg seg_ch_V_ckch (seg_ch_Vp_pow (N.to_nat n1 - 1))) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CfH_V_dbl1 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 1)%N) :
    Seg ([cf] ++ [ch] ^^ (N.to_nat n1)) ([ck] ++ [ch] ^^ (N.to_nat n2)) V_u [0; 1; 1; 0]%sym.
Proof.
  pose proof (zSg (seg_cf_keep [1; 0; 0]%sym) (raw_PureH_V_dbl1 hn h2)) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CkA_K_keep {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = n1) :
    Seg ([ck] ++ pairA ^^ (N.to_nat n1)) ([ck] ++ [ch] ^^ (N.to_nat n2)) K_u [1; 0]%sym.
Proof.
  set (q := N.to_nat n1 - 1).
  replace (N.to_nat n1) with (1 + q) by lia.
  replace (N.to_nat n2) with (1 + q) by lia.
  rewrite !lpow_1_add.
  assert (hp1 : Seg pairA [ck; ch] [1; 1]%sym Q_u).
  { pose proof (zSg seg_cb_11_ckch (seg_cf_keep [0]%sym)) as h.
    cbn in h. exact h. }
  pose proof (zSg hp1 (seg_pairA_Q_pow q)) as hp_all.
  pose proof (zSg seg_ck_K hp_all) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CkH_K_dbl2 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 2)%N) :
    Seg ([ck] ++ [ch] ^^ (N.to_nat n1)) ([cf] ++ pairA ^^ (N.to_nat n2)) K_u [0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + (N.to_nat n1 - 1)) by lia.
  replace (N.to_nat n2) with ((N.to_nat n1 - 1) * 2) by lia.
  rewrite lpow_1_add.
  pose proof (zSg seg_ch_11_cf (seg_ch_Qp_dbl_pow (N.to_nat n1 - 1))) as hh.
  pose proof (zSg seg_ck_K hh) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CkH_K_dbl1 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 1)%N) :
    Seg ([ck] ++ [ch] ^^ (N.to_nat n1)) ([ck] ++ pairA ^^ (N.to_nat n2)) K_u [0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + (N.to_nat n1 - 1)) by lia.
  replace (N.to_nat n2) with (1 + (N.to_nat n1 - 1) * 2) by lia.
  rewrite !lpow_1_add.
  pose proof (zSg seg_ch_11_ck (seg_ch_Qp_dbl_pow (N.to_nat n1 - 1))) as hh.
  pose proof (zSg seg_ck_K hh) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CkH_K_half0 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 0)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg ([ck] ++ [ch] ^^ (N.to_nat n1)) ([cf] ++ [ch] ^^ (N.to_nat n2)) K_u [0; 0]%sym.
Proof.
  set (q := N.to_nat n2 - 1).
  replace (N.to_nat n1) with (1 + (1 + q * 2)) by lia.
  replace (N.to_nat n2) with (1 + q) by lia.
  rewrite lpow_1_add.
  pose proof (zSg seg_ch_11_cf (seg_ch_Qp_odd q)) as hh.
  pose proof (zSg seg_ck_K hh) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CkH_K_half1 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 1)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg ([ck] ++ [ch] ^^ (N.to_nat n1)) ([cf] ++ [ch] ^^ (N.to_nat n2)) K_u [0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + N.to_nat n2 * 2) by lia.
  rewrite lpow_1_add.
  pose proof (zSg seg_ch_11_cf (seg_ch_Qp_even (N.to_nat n2))) as hh.
  pose proof (zSg seg_ck_K hh) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_PureH_K_half0 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 0)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg ([ch] ^^ (N.to_nat n1)) ([ch] ^^ (N.to_nat n2)) K_u [0; 0]%sym.
Proof.
  replace (N.to_nat n1) with (N.to_nat n2 * 2) by lia.
  exact (seg_ch_K_even (N.to_nat n2)).
Qed.

Lemma raw_PureH_K_half1 {n1 n2 : N} (hn : (2 <= n1)%N) (hp : (n1 mod 2 = 1)%N) (h2 : n2 = (n1 / 2)%N) :
    Seg ([ch] ^^ (N.to_nat n1)) ([ch] ^^ (N.to_nat n2)) K_u [0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + N.to_nat n2 * 2) by lia.
  exact (seg_ch_K_odd (N.to_nat n2)).
Qed.

Lemma raw_PureH_K_dbl2 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 2)%N) :
    Seg ([ch] ^^ (N.to_nat n1)) (pairA ^^ (N.to_nat n2)) K_u [0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + (N.to_nat n1 - 1)) by lia.
  replace (N.to_nat n2) with ((N.to_nat n1 - 1) * 2) by lia.
  rewrite lpow_1_add.
  pose proof (zSg seg_ch_K (seg_ch_Qp_dbl_pow (N.to_nat n1 - 1))) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_PureA_Q_keep {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = n1) :
    Seg (pairA ^^ (N.to_nat n1)) ([ch] ^^ (N.to_nat n2)) Q_u [1; 0]%sym.
Proof.
  subst n2. exact (seg_pairA_Q_pow (N.to_nat n1)).
Qed.

Lemma raw_CfA_Q_keep {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = n1) :
    Seg ([cf] ++ pairA ^^ (N.to_nat n1)) ([ch] ^^ (N.to_nat n2)) Q_u [1; 0]%sym.
Proof.
  pose proof (zSg (seg_cf_keep [0]%sym) (raw_PureA_Q_keep hn h2)) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_PureH_Q_dbl1 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 1)%N) :
    Seg ([ch] ^^ (N.to_nat n1)) (pairA ^^ (N.to_nat n2)) Q_u [0; 1]%sym.
Proof.
  replace (N.to_nat n1) with (1 + (N.to_nat n1 - 1)) by lia.
  replace (N.to_nat n2) with (1 + (N.to_nat n1 - 1) * 2) by lia.
  rewrite !lpow_1_add.
  pose proof (zSg seg_ch_Q_cbcf (seg_ch_Qp_dbl_pow (N.to_nat n1 - 1))) as h.
  cbn [List.app] in h. exact h.
Qed.

Lemma raw_CfH_Q_dbl1 {n1 n2 : N} (hn : (2 <= n1)%N) (h2 : n2 = (2 * n1 - 1)%N) :
    Seg ([cf] ++ [ch] ^^ (N.to_nat n1)) (pairA ^^ (N.to_nat n2)) Q_u [0; 1]%sym.
Proof.
  pose proof (zSg (seg_cf_keep [0]%sym) (raw_PureH_Q_dbl1 hn h2)) as h.
  cbn [List.app] in h. exact h.
Qed.

(* 7-leg Hub Turnaround (pairA ^^ 3 = 6 subcalls) *)
Lemma zP0 (w : side) : zCf w -->+ zCR w cb ([0; 1]%sym *> 0inf%sym).
Proof. unfold zCf, zCR, zInQ, zInB; cbn [List.app Str_app]; fast_start_progress. Qed.

Lemma zP1 (w : side) : zCL w cb ([0; 1]%sym *> 0inf%sym) -->+ zCR w cf ([0; 1]%sym *> 0inf%sym).
Proof. unfold zCL, zCR, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress. Qed.

Lemma zP2 (w : side) : zCL w cf ([0; 1]%sym *> 0inf%sym) -->+ zCR w cb ([1; 1; 0; 1]%sym *> 0inf%sym).
Proof. unfold zCL, zCR, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress. Qed.

Lemma zP3 (w : side) : zCL w cb ([1; 1; 0; 1]%sym *> 0inf%sym) -->+ zCR w cf ([1; 1; 0; 1]%sym *> 0inf%sym).
Proof. unfold zCL, zCR, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress. Qed.

Lemma zP4 (w : side) : zCL w cf ([1; 1; 0; 1]%sym *> 0inf%sym) -->+ zCR w cb ([0; 1; 0; 1]%sym *> 0inf%sym).
Proof. unfold zCL, zCR, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress. Qed.

Lemma zP5 (w : side) : zCL w cb ([0; 1; 0; 1]%sym *> 0inf%sym) -->+ zCR w cf ([0; 1; 0; 1]%sym *> 0inf%sym).
Proof. unfold zCL, zCR, zInQ, zInB, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress. Qed.

Lemma zP6 (w : side) : zCL w cf ([0; 1; 0; 1]%sym *> 0inf%sym) -->+ zCf ([1; 1; 0; 0; 1]%sym *> w).
Proof. unfold zCL, zCf, zExQ, zExB; cbn [List.app Str_app]; fast_start_progress. Qed.

Lemma Side_turnaround {w w' : side} (h : Side (pairA ^^ 3) w w') :
    zCf w -->+ zCf ([1; 1; 0; 0; 1]%sym *> w').
Proof.
  cbn in h.
  inversion h as [| ? ? ? w1 ? hc1 h1]; subst.
  inversion h1 as [| ? ? ? w2 ? hc2 h2]; subst.
  inversion h2 as [| ? ? ? w3 ? hc3 h3]; subst.
  inversion h3 as [| ? ? ? w4 ? hc4 h4]; subst.
  inversion h4 as [| ? ? ? w5 ? hc5 h5]; subst.
  inversion h5 as [| ? ? ? w6 ? hc6 h6]; subst.
  inversion h6; subst.
  exact (ptrans (zP0 w)
    (ptrans (hc1 ([0; 1]%sym *> 0inf%sym))
      (ptrans (zP1 w1)
        (ptrans (hc2 ([0; 1]%sym *> 0inf%sym))
          (ptrans (zP2 w2)
            (ptrans (hc3 ([1; 1; 0; 1]%sym *> 0inf%sym))
              (ptrans (zP3 w3)
                (ptrans (hc4 ([1; 1; 0; 1]%sym *> 0inf%sym))
                  (ptrans (zP4 w4)
                    (ptrans (hc5 ([0; 1; 0; 1]%sym *> 0inf%sym))
                      (ptrans (zP5 w5)
                        (ptrans (hc6 ([0; 1; 0; 1]%sym *> 0inf%sym)) (zP6 w'))))))))))))).
Qed.

(* Section 2: Word, zDg, Mode, DState, StepRule, Scan, Step_exec *)

Inductive Word : Type :=
  | V
  | K
  | Q_w.

Definition word_eqb (x y : Word) : bool :=
  match x, y with
  | V, V | K, K | Q_w, Q_w => true
  | _, _ => false
  end.

Lemma word_eqb_eq (x y : Word) : word_eqb x y = true <-> x = y.
Proof. destruct x, y; cbn; split; intro h; congruence. Qed.

Fixpoint list_word_eqb (u v : list Word) : bool :=
  match u, v with
  | [], [] => true
  | x :: u', y :: v' => word_eqb x y && list_word_eqb u' v'
  | _, _ => false
  end.

Lemma list_word_eqb_eq : forall u v : list Word, list_word_eqb u v = true <-> u = v.
Proof.
  induction u as [| x u ih]; intros [| y v]; cbn.
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff, word_eqb_eq, ih.
    split; [intros [-> ->]; reflexivity | intro h; injection h as -> ->; auto].
Qed.

Fixpoint zWt (u : list Word) : list Sym :=
  match u with
  | [] => []
  | V :: u' => V_u ++ zWt u'
  | K :: u' => K_u ++ zWt u'
  | Q_w :: u' => Q_u ++ zWt u'
  end.

Fixpoint zWt' (u : list Word) : list Sym :=
  match u with
  | [] => []
  | V :: u' => Vp ++ zWt' u'
  | K :: u' => Kp ++ zWt' u'
  | Q_w :: u' => Qp ++ zWt' u'
  end.

Fixpoint zTs (u : list Word) (r : side) : side :=
  match u with
  | [] => r
  | V :: u' => V_u *> zTs u' r
  | K :: u' => K_u *> zTs u' r
  | Q_w :: u' => Q_u *> zTs u' r
  end.

Fixpoint zTs' (u : list Word) (r : side) : side :=
  match u with
  | [] => r
  | V :: u' => Vp *> zTs' u' r
  | K :: u' => Kp *> zTs' u' r
  | Q_w :: u' => Qp *> zTs' u' r
  end.

Lemma zWt_zTs (u : list Word) (r : side) : zWt u *> r = zTs u r.
Proof.
  induction u as [| a u ih]; [reflexivity |].
  destruct a; cbn [zWt zTs]; rewrite Str_app_assoc, ih; reflexivity.
Qed.

Lemma zWt'_zTs' (u : list Word) (r : side) : zWt' u *> r = zTs' u r.
Proof.
  induction u as [| a u ih]; [reflexivity |].
  destruct a; cbn [zWt' zTs']; rewrite Str_app_assoc, ih; reflexivity.
Qed.

Lemma zTs_append (u v : list Word) (r : side) : zTs (u ++ v) r = zTs u (zTs v r).
Proof.
  induction u as [| a u ih]; [reflexivity |].
  destruct a; cbn [List.app zTs]; rewrite ih; reflexivity.
Qed.

Lemma zWt_shift (v : list Word) : [0]%sym ++ zWt v = zWt' v ++ [0]%sym.
Proof.
  induction v as [| a v ih]; [reflexivity |].
  destruct a; unfold V_u, K_u, Q_u, Vp, Kp, Qp; cbn in ih |- *;
    rewrite <- ih; reflexivity.
Qed.

Lemma zTs_shift (v : list Word) : [0]%sym *> zTs v 0inf%sym = zTs' v 0inf%sym.
Proof.
  rewrite <- zWt_zTs, <- Str_app_assoc, zWt_shift, Str_app_assoc.
  cbn [Str_app]. rewrite z00, zWt'_zTs'. reflexivity.
Qed.

Lemma zTs_V_shift (v : list Word) : [1; 1; 0]%sym *> zTs' v 0inf%sym = zTs (V :: v) 0inf%sym.
Proof.
  rewrite <- zTs_shift, <- Str_app_assoc. reflexivity.
Qed.

Lemma zPow1_N (n : nat) : (2 ^ (N.of_nat (1 + n)) = 2 ^ (N.of_nat n) + 2 ^ (N.of_nat n))%N.
Proof.
  rewrite Nat2N.inj_add, N.pow_add_r.
  change (2 ^ N.of_nat 1)%N with 2%N. lia.
Qed.

Lemma z0U (n : N) : (exists a : N, n = (a * 2)%N) \/ (exists a : N, n = (1 + a * 2)%N).
Proof.
  destruct (N.eq_dec (n mod 2) 0) as [h | h].
  - left. exists (n / 2)%N. lia.
  - right. exists (n / 2)%N. lia.
Qed.

Inductive zDg : N -> nat -> list Word -> Prop :=
  | zDg_nil : zDg 0%N 0 []
  | zDg_zero {A : N} {H : nat} {u : list Word} :
      zDg A H u -> zDg (A * 2)%N (1 + H) (K :: u)
  | zDg_one {A : N} {H : nat} {u : list Word} :
      zDg A H u -> zDg (1 + A * 2)%N (1 + H) (Q_w :: u).

Lemma zDg_exists (H : nat) : forall A : N, (A < 2 ^ (N.of_nat H))%N -> exists u, zDg A H u.
Proof.
  induction H as [| H ih]; intros A hA.
  - cbn in hA. assert (A = 0%N) by lia. subst A.
    exists (@nil Word). exact zDg_nil.
  - change (S H) with (1 + H) in hA |- *.
    rewrite zPow1_N in hA.
    destruct (z0U A) as [[a ->] | [a ->]].
    + destruct (ih a ltac:(lia)) as [u hI].
      exists (K :: u). exact (zDg_zero hI).
    + destruct (ih a ltac:(lia)) as [u hI].
      exists (Q_w :: u). exact (zDg_one hI).
Qed.

Lemma zDg_append {A : N} {H : nat} {u : list Word} (h1 : zDg A H u) :
    forall {B : N} {J : nat} {v : list Word},
      zDg B J v -> zDg (A + B * 2 ^ (N.of_nat H))%N (H + J) (u ++ v).
Proof.
  induction h1 as [| A H u _ ih | A H u _ ih]; intros B J v h2.
  - cbn [List.app Nat.add].
    replace (0 + B * 2 ^ N.of_nat 0)%N with B by (cbn; lia).
    exact h2.
  - pose proof (zDg_zero (ih _ _ _ h2)) as h3.
    replace ((A + B * 2 ^ N.of_nat H) * 2)%N
      with (A * 2 + B * 2 ^ N.of_nat (1 + H))%N in h3
      by (rewrite zPow1_N; lia).
    exact h3.
  - pose proof (zDg_one (ih _ _ _ h2)) as h3.
    replace (1 + (A + B * 2 ^ N.of_nat H) * 2)%N
      with ((1 + A * 2) + B * 2 ^ N.of_nat (1 + H))%N in h3
      by (rewrite zPow1_N; lia).
    exact h3.
Qed.

Fixpoint checkDg (b : N) (u : list Word) : bool :=
  match u with
  | [] => (b =? 0)%N
  | K :: u' => (b mod 2 =? 0)%N && checkDg (b / 2)%N u'
  | Q_w :: u' => (b mod 2 =? 1)%N && checkDg (b / 2)%N u'
  | V :: _ => false
  end.

Lemma checkDg_sound : forall (u : list Word) (b : N),
    checkDg b u = true -> zDg b (length u) u.
Proof.
  induction u as [| w u ih]; intros b h; cbn in h.
  - apply N.eqb_eq in h. subst b. exact zDg_nil.
  - destruct w.
    + discriminate.
    + apply Bool.andb_true_iff in h as [hb hrec].
      apply N.eqb_eq in hb.
      pose proof (zDg_zero (ih (b / 2)%N hrec)) as hZ.
      replace ((b / 2) * 2)%N with b in hZ by lia.
      exact hZ.
    + apply Bool.andb_true_iff in h as [hb hrec].
      apply N.eqb_eq in hb.
      pose proof (zDg_one (ih (b / 2)%N hrec)) as hO.
      replace (1 + (b / 2) * 2)%N with b in hO by lia.
      exact hO.
Qed.

Lemma Side_ch_default {b' : N} {H : nat} {da : list Word} (h : zDg b' H da) :
    Side ([ch] ^^ (N.to_nat b')) 0inf%sym (zTs' da 0inf%sym).
Proof.
  induction h as [| A H u _ ih | A H u _ ih].
  - exact (Side_nil 0inf%sym).
  - replace (N.to_nat (A * 2)%N) with (N.to_nat A * 2) by lia.
    pose proof (zSc (seg_ch_K_even (N.to_nat A)) ih) as hS.
    rewrite zKd in hS. cbn [zTs']. exact hS.
  - replace (N.to_nat (1 + A * 2)%N) with (1 + N.to_nat A * 2) by lia.
    pose proof (zSc (seg_ch_K_odd (N.to_nat A)) ih) as hS.
    rewrite zKd in hS. cbn [zTs']. exact hS.
Qed.

Inductive Mode : Type :=
  | PA1 | FA1 | KA1 | KHV | PHV | FH0 | FH1 | PH0 | PH1.

Definition mode_eqb (m1 m2 : Mode) : bool :=
  match m1, m2 with
  | PA1, PA1 | FA1, FA1 | KA1, KA1 | KHV, KHV | PHV, PHV
  | FH0, FH0 | FH1, FH1 | PH0, PH0 | PH1, PH1 => true
  | _, _ => false
  end.

Lemma mode_eqb_eq (m1 m2 : Mode) : mode_eqb m1 m2 = true <-> m1 = m2.
Proof. destruct m1, m2; cbn; split; intro h; congruence. Qed.

Inductive DState : Type :=
  | S2 | S3 | S4 | S5.

Definition dstate_eqb (s1 s2 : DState) : bool :=
  match s1, s2 with
  | S2, S2 | S3, S3 | S4, S4 | S5, S5 => true
  | _, _ => false
  end.

Lemma dstate_eqb_eq (s1 s2 : DState) : dstate_eqb s1 s2 = true <-> s1 = s2.
Proof. destruct s1, s2; cbn; split; intro h; congruence. Qed.

Definition modeCalls (m : Mode) (n : N) : list Call :=
  match m with
  | PA1 => pairA ^^ (N.to_nat n)
  | FA1 => [cf] ++ pairA ^^ (N.to_nat n)
  | KA1 => [ck] ++ pairA ^^ (N.to_nat n)
  | KHV => [ck] ++ [ch] ^^ (N.to_nat n)
  | PHV => [ch] ^^ (N.to_nat n)
  | FH0 => [cf] ++ [ch] ^^ (N.to_nat n)
  | FH1 => [cf] ++ [ch] ^^ (N.to_nat n)
  | PH0 => [ch] ^^ (N.to_nat n)
  | PH1 => [ch] ^^ (N.to_nat n)
  end.

Definition modeRem (m : Mode) : list Sym :=
  match m with
  | PA1 | FA1 | KA1 => [1]%sym
  | KHV | PHV => [1; 1; 0]%sym
  | FH0 | PH0 => [0]%sym
  | FH1 | PH1 => [1]%sym
  end.

Definition modeMatches (m : Mode) (s : DState) : bool :=
  match m, s with
  | PA1, S2 | FA1, S2 => true
  | KHV, S3 | PHV, S3 | PH0, S3 | PH1, S3 => true
  | PHV, S4 | FH0, S4 | PH0, S4 | FH1, S4 | PH1, S4 => true
  | KA1, S5 | PHV, S5 | PH0, S5 | PH1, S5 => true
  | _, _ => false
  end.

Definition dfaStep (w : Word) (s : DState) : DState :=
  match w, s with
  | V, S3 => S4
  | V, _ => S2
  | K, S3 => S5
  | K, _ => S3
  | Q_w, S2 => S4
  | Q_w, _ => S2
  end.

Fixpoint dfaRun (u : list Word) (s : DState) : DState :=
  match u with
  | [] => s
  | w :: u' => dfaStep w (dfaRun u' s)
  end.

Lemma dfaStep_VV (s : DState) : dfaStep V (dfaStep V s) = S2.
Proof. destruct s; reflexivity. Qed.

Inductive NKinds : Type :=
  | dbl2 | dbl1 | keep | half0 | half1.

Definition validKind (k : NKinds) (n1 n2 : N) : Prop :=
  match k with
  | dbl2  => (2 <= n1)%N /\ n2 = (2 * n1 - 2)%N
  | dbl1  => (2 <= n1)%N /\ n2 = (2 * n1 - 1)%N
  | keep  => (2 <= n1)%N /\ n2 = n1
  | half0 => (2 <= n1)%N /\ (n1 mod 2 = 0)%N /\ n2 = (n1 / 2)%N
  | half1 => (2 <= n1)%N /\ (n1 mod 2 = 1)%N /\ n2 = (n1 / 2)%N
  end.

Inductive StepRule : Type :=
  | R00 | R01 | R02 | R03 | R04 | R05 | R06 | R07 | R08 | R09
  | R10 | R11 | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19
  | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27 | R28 | R29
  | R30 | R31 | R32 | R33.

Definition rInMode (r : StepRule) : Mode :=
  match r with
  | R00 | R01 | R02 | R03 | R04 => PA1
  | R05 | R06 | R07 | R08 | R09 => FA1
  | R10 => KA1
  | R11 | R12 | R13 | R14 => KHV
  | R15 | R16 | R17 | R18 | R19 => PHV
  | R20 | R21 => FH0
  | R22 | R23 => FH1
  | R24 | R25 | R26 | R27 | R28 => PH0
  | R29 | R30 | R31 | R32 | R33 => PH1
  end.

Definition rWord (r : StepRule) : Word :=
  match r with
  | R00 | R01 | R02 | R03 | R05 | R06 | R07 | R08 | R15 | R20 | R22 | R24 | R29 => V
  | R10 | R11 | R12 | R13 | R14 | R16 | R17 | R18 | R25 | R26 | R27 | R30 | R31 | R32 => K
  | R04 | R09 | R19 | R21 | R23 | R28 | R33 => Q_w
  end.

Definition rKind (r : StepRule) : NKinds :=
  match r with
  | R00 | R05 | R11 | R18 | R27 | R32 => dbl2
  | R01 | R06 | R12 | R15 | R19 | R20 | R21 | R22 | R23 | R24 | R28 | R29 | R33 => dbl1
  | R04 | R09 | R10 => keep
  | R02 | R07 | R13 | R16 | R25 | R30 => half0
  | R03 | R08 | R14 | R17 | R26 | R31 => half1
  end.

Definition rOutMode (r : StepRule) : Mode :=
  match r with
  | R00 | R05 | R11 => FA1
  | R01 | R06 | R12 => KA1
  | R02 | R07 | R13 => FH0
  | R03 | R08 | R14 => FH1
  | R04 | R09 => PHV
  | R10 | R15 | R20 | R22 | R24 | R29 => KHV
  | R16 | R25 | R30 => PH0
  | R17 | R26 | R31 => PH1
  | R18 | R19 | R21 | R23 | R27 | R28 | R32 | R33 => PA1
  end.

Definition rOb (r : StepRule) : list Sym :=
  match r with
  | R00 | R01 | R03 | R05 | R06 | R08 => [1; 0; 0; 1]%sym
  | R02 | R07 => [1; 0; 0; 0]%sym
  | R04 | R09 | R10 => [1; 0]%sym
  | R11 | R12 | R14 | R17 | R18 | R19 | R21 | R23 | R26 | R27 | R28 | R31 | R32 | R33 => [0; 1]%sym
  | R13 | R16 | R25 | R30 => [0; 0]%sym
  | R15 | R20 | R22 | R24 | R29 => [0; 1; 1; 0]%sym
  end.

Definition rEmit (r : StepRule) : list Word :=
  match r with
  | R00 | R01 | R02 | R03 | R05 | R06 | R07 | R08
  | R11 | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19 => [V]
  | R04 | R09 | R10 => []
  | R20 | R21 | R24 | R25 | R26 | R27 | R28 => [K]
  | R22 | R23 | R29 | R30 | R31 | R32 | R33 => [Q_w]
  end.

Definition rG (r : StepRule) : nat :=
  match r with
  | R01 | R06 | R12 => 2
  | R04 | R09 => 3
  | R10 => 1
  | _ => 0
  end.

Lemma stepRule_rem (r : StepRule) :
    modeRem (rInMode r) ++ rOb r = zWt (rEmit r) ++ modeRem (rOutMode r).
Proof. destruct r; reflexivity. Qed.

Lemma stepRule_seg (r : StepRule) (n1 n2 : N) (h : validKind (rKind r) n1 n2) :
    Seg (modeCalls (rInMode r) n1) (modeCalls (rOutMode r) n2) (zWt [rWord r]) (rOb r).
Proof.
  destruct r; cbn [rKind validKind] in h;
    cbn [rInMode rOutMode rWord rOb modeCalls zWt List.app];
    try (destruct h as [hn [hp h2]]);
    try (destruct h as [hn h2]).
  - exact (raw_PureA_V_dbl2 hn h2).
  - exact (raw_PureA_V_dbl1 hn h2).
  - exact (raw_PureA_V_half0 hn hp h2).
  - exact (raw_PureA_V_half1 hn hp h2).
  - exact (raw_PureA_Q_keep hn h2).
  - exact (raw_CfA_V_dbl2 hn h2).
  - exact (raw_CfA_V_dbl1 hn h2).
  - exact (raw_CfA_V_half0 hn hp h2).
  - exact (raw_CfA_V_half1 hn hp h2).
  - exact (raw_CfA_Q_keep hn h2).
  - exact (raw_CkA_K_keep hn h2).
  - exact (raw_CkH_K_dbl2 hn h2).
  - exact (raw_CkH_K_dbl1 hn h2).
  - exact (raw_CkH_K_half0 hn hp h2).
  - exact (raw_CkH_K_half1 hn hp h2).
  - exact (raw_PureH_V_dbl1 hn h2).
  - exact (raw_PureH_K_half0 hn hp h2).
  - exact (raw_PureH_K_half1 hn hp h2).
  - exact (raw_PureH_K_dbl2 hn h2).
  - exact (raw_PureH_Q_dbl1 hn h2).
  - exact (raw_CfH_V_dbl1 hn h2).
  - exact (raw_CfH_Q_dbl1 hn h2).
  - exact (raw_CfH_V_dbl1 hn h2).
  - exact (raw_CfH_Q_dbl1 hn h2).
  - exact (raw_PureH_V_dbl1 hn h2).
  - exact (raw_PureH_K_half0 hn hp h2).
  - exact (raw_PureH_K_half1 hn hp h2).
  - exact (raw_PureH_K_dbl2 hn h2).
  - exact (raw_PureH_Q_dbl1 hn h2).
  - exact (raw_PureH_V_dbl1 hn h2).
  - exact (raw_PureH_K_half0 hn hp h2).
  - exact (raw_PureH_K_half1 hn hp h2).
  - exact (raw_PureH_K_dbl2 hn h2).
  - exact (raw_PureH_Q_dbl1 hn h2).
Qed.

Inductive Scan : Mode -> DState -> N -> list Word -> Mode -> DState -> N -> list Word -> nat -> Prop :=
  | Scan_nil (m : Mode) (s : DState) (n : N)
      (hm : modeMatches m s = true) (hn : (2 <= n)%N) :
      Scan m s n [] m s n [] 0
  | Scan_step {r : StepRule} {s1 s2 s3 : DState} {n1 n2 n3 : N} {g : nat} {u v : list Word} {m3 : Mode}
      (hs : s1 = dfaStep (rWord r) s2)
      (hm1 : modeMatches (rInMode r) s1 = true)
      (hv : validKind (rKind r) n1 n2)
      (hrest : Scan (rOutMode r) s2 n2 u m3 s3 n3 v g) :
      Scan (rInMode r) s1 n1 (rWord r :: u) m3 s3 n3 (rEmit r ++ v) (rG r + g).

Lemma Scan_match_in {m1 : Mode} {s1 : DState} {n1 : N} {u : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v : list Word} {g : nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) : modeMatches m1 s1 = true.
Proof. destruct h; assumption. Qed.

Lemma Scan_exit_ge2 {m1 : Mode} {s1 : DState} {n1 : N} {u : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v : list Word} {g : nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) : (2 <= n2)%N /\ modeMatches m2 s2 = true.
Proof.
  induction h as [m s n hm hn | r s1 s2 s3 n1 n2 n3 g u v m3 hs hm1 hv _ ih].
  - exact (conj hn hm).
  - exact ih.
Qed.

Lemma Scan_append {m1 : Mode} {s1 : DState} {n1 : N} {u1 : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v1 : list Word} {g1 : nat}
    (h1 : Scan m1 s1 n1 u1 m2 s2 n2 v1 g1) :
    forall {m3 : Mode} {s3 : DState} {n3 : N} {u2 v2 : list Word} {g2 : nat},
      Scan m2 s2 n2 u2 m3 s3 n3 v2 g2 ->
      Scan m1 s1 n1 (u1 ++ u2) m3 s3 n3 (v1 ++ v2) (g1 + g2).
Proof.
  induction h1 as [m s n hm hn | r s1 s2 s3' n1 n2 n3' g1 u1 v1 m3' hs hm1 hv _ ih];
    intros m3 s3 n3 u2 v2 g2 h2.
  - cbn [List.app Nat.add]. exact h2.
  - pose proof (ih _ _ _ _ _ _ h2) as hI.
    rewrite <- app_assoc, <- Nat.add_assoc.
    exact (Scan_step hs hm1 hv hI).
Qed.

Lemma Side_of_Scan {m1 : Mode} {s1 : DState} {n1 : N} {u : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v : list Word} {g : nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    forall (u_tail w_tail : side),
      Side (modeCalls m2 n2) u_tail w_tail ->
      exists w_out,
        Side (modeCalls m1 n1) (zTs u u_tail) w_out /\
        modeRem m1 *> w_out = zTs v (modeRem m2 *> w_tail).
Proof.
  induction h as [m s n hm hn | r s1 s2 s3 n1 n2 n3 g u v m3 hs hm1 hv _ ih];
    intros u_tail w_tail hSide.
  - exists w_tail. split; [exact hSide | reflexivity].
  - destruct (ih u_tail w_tail hSide) as [w_mid [hSide_mid hEq_mid]].
    pose proof (stepRule_seg r n1 n2 hv) as hSeg1.
    pose proof (zSc hSeg1 hSide_mid) as hSide1.
    assert (h_in_eq : zWt [rWord r] *> zTs u u_tail = zTs (rWord r :: u) u_tail).
    { destruct (rWord r); cbn [zWt zTs List.app]; reflexivity. }
    rewrite h_in_eq in hSide1.
    exists (rOb r *> w_mid). split; [exact hSide1 |].
    rewrite <- Str_app_assoc, stepRule_rem, Str_app_assoc, hEq_mid, zWt_zTs, <- zTs_append.
    reflexivity.
Qed.

Definition Step (u u' : list Word) : Prop :=
  exists (body : list Word) (m_end : Mode) (n_end : N) (v_body da : list Word) (H g : nat),
    u = body ++ [Q_w] /\
    (m_end = PA1 \/ m_end = FA1) /\
    Scan PA1 S2 3%N body m_end S2 n_end v_body g /\
    zDg n_end H da /\
    u' = V :: (v_body ++ V :: da).

Inductive Rounds : list Word -> list Word -> Prop :=
  | Rounds_refl (u : list Word) : Rounds u u
  | Rounds_next {u v w : list Word} : Step u v -> Rounds v w -> Rounds u w.

Lemma Step_exec {u u' : list Word} (h : Step u u') :
    zCf (zTs u 0inf%sym) -->+ zCf (zTs u' 0inf%sym).
Proof.
  destruct h as [body [m_end [n_end [v_body [da [H [g [-> [hm_end [hScan [hDg ->]]]]]]]]]]].
  pose proof (proj1 (Scan_exit_ge2 hScan)) as hn_end.
  pose proof (Side_ch_default hDg) as hSide_da.
  assert (hSegQ : Seg (modeCalls m_end n_end) (modeCalls PHV n_end) Q_u [1; 0]%sym).
  { destruct hm_end as [-> | ->]; cbn [modeCalls].
    - exact (raw_PureA_Q_keep hn_end eq_refl).
    - exact (raw_CfA_Q_keep hn_end eq_refl). }
  pose proof (zSc hSegQ hSide_da) as hSideQ.
  destruct (Side_of_Scan hScan (Q_u *> 0inf%sym) ([1; 0]%sym *> zTs' da 0inf%sym) hSideQ)
    as [w_out [hSide0 hEq0]].
  assert (h_u_eq : zTs body (Q_u *> 0inf%sym) = zTs (body ++ [Q_w]) 0inf%sym).
  { rewrite zTs_append. reflexivity. }
  rewrite h_u_eq in hSide0.
  assert (h_rem_end : modeRem m_end = [1]%sym).
  { destruct hm_end as [-> | ->]; reflexivity. }
  rewrite h_rem_end in hEq0.
  rewrite <- Str_app_assoc in hEq0.
  cbn [List.app] in hEq0.
  rewrite zTs_V_shift, <- zTs_append in hEq0.
  cbn [modeRem Str_app] in hEq0.
  pose proof (Side_turnaround hSide0) as hTurn.
  assert (h_top : [1; 1; 0; 0; 1]%sym *> w_out = zTs (V :: (v_body ++ V :: da)) 0inf%sym).
  { cbn [zTs V_u Str_app]. do 4 f_equal. exact hEq0. }
  rewrite h_top in hTurn.
  exact hTurn.
Qed.

Lemma Rounds_exec {u v : list Word} (h : Rounds u v) :
    zCf (zTs u 0inf%sym) -->* zCf (zTs v 0inf%sym).
Proof.
  induction h as [u | u v w hS _ ih].
  - apply evstep_refl.
  - exact (pev (pe_trans (Step_exec hS) ih)).
Qed.

(* Section 3: Affine Evaluator for Concrete Rounds and Symbolic head_w, s_full, top_body *)

Fixpoint evalAffineScan (rs : list StepRule) (m : Mode) (s : DState) (mb cb : N) (u : list Word) :
    option (Mode * N * N * list Word * nat) :=
  match rs, u with
  | [], [] =>
    if modeMatches m s && (2 <=? cb)%N then Some (m, mb, cb, [], 0) else None
  | r :: rs', w :: u' =>
    if mode_eqb m (rInMode r) && word_eqb w (rWord r) &&
       modeMatches m (dfaStep w (dfaRun u' s)) && (2 <=? cb)%N then
      match rKind r with
      | dbl2 =>
        match evalAffineScan rs' (rOutMode r) s (2 * mb)%N (2 * cb - 2)%N u' with
        | None => None
        | Some (m_end, mb_end, cb_end, v, g) =>
          Some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
        end
      | dbl1 =>
        match evalAffineScan rs' (rOutMode r) s (2 * mb)%N (2 * cb - 1)%N u' with
        | None => None
        | Some (m_end, mb_end, cb_end, v, g) =>
          Some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
        end
      | keep =>
        match evalAffineScan rs' (rOutMode r) s mb cb u' with
        | None => None
        | Some (m_end, mb_end, cb_end, v, g) =>
          Some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
        end
      | half0 =>
        if (mb mod 2 =? 0)%N && (cb mod 2 =? 0)%N then
          match evalAffineScan rs' (rOutMode r) s (mb / 2)%N (cb / 2)%N u' with
          | None => None
          | Some (m_end, mb_end, cb_end, v, g) =>
            Some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
          end
        else None
      | half1 =>
        if (mb mod 2 =? 0)%N && (cb mod 2 =? 1)%N then
          match evalAffineScan rs' (rOutMode r) s (mb / 2)%N (cb / 2)%N u' with
          | None => None
          | Some (m_end, mb_end, cb_end, v, g) =>
            Some (m_end, mb_end, cb_end, rEmit r ++ v, rG r + g)
          end
        else None
      end
    else None
  | _, _ => None
  end.

Lemma evalAffineScan_sound :
    forall rs m s (mb cb : N) u m_end mb_end cb_end v g (q : N),
      evalAffineScan rs m s mb cb u = Some (m_end, mb_end, cb_end, v, g) ->
      Scan m (dfaRun u s) (mb * q + cb)%N u m_end s (mb_end * q + cb_end)%N v g.
Proof.
  induction rs as [| r rs ih]; intros m s mb cb u m_end mb_end cb_end v g q h.
  - destruct u as [| w u']; [| cbn in h; discriminate].
    cbn [evalAffineScan dfaRun] in h |- *.
    destruct (modeMatches m s && (2 <=? cb)%N) eqn:hc; [| discriminate].
    apply Bool.andb_true_iff in hc as [hm hcb].
    apply N.leb_le in hcb.
    injection h as <- <- <- <- <-.
    exact (Scan_nil m s (mb * q + cb)%N hm ltac:(lia)).
  - destruct u as [| w u']; [cbn in h; discriminate |].
    cbn [evalAffineScan] in h.
    destruct (mode_eqb m (rInMode r) && word_eqb w (rWord r) &&
              modeMatches m (dfaStep w (dfaRun u' s)) && (2 <=? cb)%N) eqn:hc; [| discriminate].
    apply Bool.andb_true_iff in hc as [hc hcb].
    apply Bool.andb_true_iff in hc as [hc hm1].
    apply Bool.andb_true_iff in hc as [hm hw].
    apply mode_eqb_eq in hm. subst m.
    apply word_eqb_eq in hw. subst w.
    apply N.leb_le in hcb.
    cbn [dfaRun].
    destruct (rKind r) eqn:hk.
    + (* dbl2 *)
      destruct (evalAffineScan rs (rOutMode r) s (2 * mb)%N (2 * cb - 2)%N u')
        as [[[[[me mbe] cbe] v1] g1] |] eqn:hrec; [| discriminate].
      injection h as <- <- <- <- <-.
      pose proof (ih (rOutMode r) s (2 * mb)%N (2 * cb - 2)%N u' me mbe cbe v1 g1 q hrec) as hI.
      assert (hm_eq : (2 * mb * q = 2 * (mb * q))%N) by lia.
      replace (2 * mb * q + (2 * cb - 2))%N with (2 * (mb * q + cb) - 2)%N in hI by lia.
      refine (Scan_step eq_refl hm1 _ hI).
      rewrite hk. cbn [validKind]. lia.
    + (* dbl1 *)
      destruct (evalAffineScan rs (rOutMode r) s (2 * mb)%N (2 * cb - 1)%N u')
        as [[[[[me mbe] cbe] v1] g1] |] eqn:hrec; [| discriminate].
      injection h as <- <- <- <- <-.
      pose proof (ih (rOutMode r) s (2 * mb)%N (2 * cb - 1)%N u' me mbe cbe v1 g1 q hrec) as hI.
      assert (hm_eq : (2 * mb * q = 2 * (mb * q))%N) by lia.
      replace (2 * mb * q + (2 * cb - 1))%N with (2 * (mb * q + cb) - 1)%N in hI by lia.
      refine (Scan_step eq_refl hm1 _ hI).
      rewrite hk. cbn [validKind]. lia.
    + (* keep *)
      destruct (evalAffineScan rs (rOutMode r) s mb cb u')
        as [[[[[me mbe] cbe] v1] g1] |] eqn:hrec; [| discriminate].
      injection h as <- <- <- <- <-.
      pose proof (ih (rOutMode r) s mb cb u' me mbe cbe v1 g1 q hrec) as hI.
      refine (Scan_step eq_refl hm1 _ hI).
      rewrite hk. cbn [validKind]. lia.
    + (* half0 *)
      destruct ((mb mod 2 =? 0)%N && (cb mod 2 =? 0)%N) eqn:hp0; [| discriminate].
      apply Bool.andb_true_iff in hp0 as [hmb2 hcb2].
      apply N.eqb_eq in hmb2. apply N.eqb_eq in hcb2.
      destruct (evalAffineScan rs (rOutMode r) s (mb / 2)%N (cb / 2)%N u')
        as [[[[[me mbe] cbe] v1] g1] |] eqn:hrec; [| discriminate].
      injection h as <- <- <- <- <-.
      pose proof (ih (rOutMode r) s (mb / 2)%N (cb / 2)%N u' me mbe cbe v1 g1 q hrec) as hI.
      assert (hm2 : (2 * (mb / 2) = mb)%N) by lia.
      assert (hm_eq : (2 * (mb / 2 * q) = mb * q)%N).
      { rewrite N.mul_assoc, hm2. reflexivity. }
      replace (mb / 2 * q + cb / 2)%N with ((mb * q + cb) / 2)%N in hI by lia.
      refine (Scan_step eq_refl hm1 _ hI).
      rewrite hk. cbn [validKind]. lia.
    + (* half1 *)
      destruct ((mb mod 2 =? 0)%N && (cb mod 2 =? 1)%N) eqn:hp1; [| discriminate].
      apply Bool.andb_true_iff in hp1 as [hmb2 hcb2].
      apply N.eqb_eq in hmb2. apply N.eqb_eq in hcb2.
      destruct (evalAffineScan rs (rOutMode r) s (mb / 2)%N (cb / 2)%N u')
        as [[[[[me mbe] cbe] v1] g1] |] eqn:hrec; [| discriminate].
      injection h as <- <- <- <- <-.
      pose proof (ih (rOutMode r) s (mb / 2)%N (cb / 2)%N u' me mbe cbe v1 g1 q hrec) as hI.
      assert (hm2 : (2 * (mb / 2) = mb)%N) by lia.
      assert (hm_eq : (2 * (mb / 2 * q) = mb * q)%N).
      { rewrite N.mul_assoc, hm2. reflexivity. }
      replace (mb / 2 * q + cb / 2)%N with ((mb * q + cb) / 2)%N in hI by lia.
      refine (Scan_step eq_refl hm1 _ hI).
      rewrite hk. cbn [validKind]. lia.
Qed.

Definition checkStep (rs : list StepRule) (body da u' : list Word) : bool :=
  dstate_eqb (dfaRun body S2) S2 &&
  match evalAffineScan rs PA1 S2 0%N 3%N body with
  | Some (m_end, 0%N, n_end, v_body, _) =>
    (mode_eqb m_end PA1 || mode_eqb m_end FA1) && checkDg n_end da && list_word_eqb u' (V :: (v_body ++ V :: da))
  | _ => false
  end.

Lemma checkStep_sound (rs : list StepRule) (body da u' : list Word)
    (h : checkStep rs body da u' = true) : Step (body ++ [Q_w]) u'.
Proof.
  unfold checkStep in h.
  apply Bool.andb_true_iff in h as [hdfa hrest].
  apply dstate_eqb_eq in hdfa.
  destruct (evalAffineScan rs PA1 S2 0%N 3%N body)
    as [[[[[m_end mb_end] n_end] v_body] g] |] eqn:hrec; [| discriminate].
  destruct mb_end as [| p]; [| discriminate].
  apply Bool.andb_true_iff in hrest as [hrest hu'].
  apply Bool.andb_true_iff in hrest as [hm_end hdg].
  apply Bool.orb_true_iff in hm_end.
  assert (hm_end' : m_end = PA1 \/ m_end = FA1).
  { destruct hm_end as [hm | hm]; apply mode_eqb_eq in hm; [left | right]; exact hm. }
  apply list_word_eqb_eq in hu'.
  pose proof (evalAffineScan_sound rs PA1 S2 0%N 3%N body m_end 0%N n_end v_body g 0%N hrec) as hScan.
  rewrite hdfa in hScan. cbn [N.mul N.add] in hScan.
  exists body m_end n_end v_body. exists da (length da) g.
  exact (conj eq_refl (conj hm_end' (conj hScan (conj (checkDg_sound da n_end hdg) hu')))).
Qed.

(* Section 4: Algebraic Identities & Potential Bounds Across All 34 StepRules *)

Definition Rat := QArith_base.Q.
Definition qN (n : N) : Rat := inject_Z (Z.of_N n).
Definition qpow2 (k : nat) : Rat := inject_Z (2 ^ (Z.of_nat k))%Z.

Ltac norm_qN :=
  repeat match goal with
  | H : context [qN (Npos ?p)] |- _ => change (qN (Npos p)) with (Zpos p # 1)%Q in H
  | |- context [qN (Npos ?p)] => change (qN (Npos p)) with (Zpos p # 1)%Q
  | H : context [qN N0] |- _ => change (qN N0) with 0%Q in H
  | |- context [qN N0] => change (qN N0) with 0%Q
  end.

Lemma qN_add (a b : N) : (qN (a + b) == qN a + qN b)%Q.
Proof. unfold qN. rewrite N2Z.inj_add, inject_Z_plus. reflexivity. Qed.

Lemma qN_mul (a b : N) : (qN (a * b) == qN a * qN b)%Q.
Proof. unfold qN. rewrite N2Z.inj_mul, inject_Z_mult. reflexivity. Qed.

Lemma qN_sub (a b : N) : (b <= a)%N -> (qN (a - b) == qN a - qN b)%Q.
Proof.
  intro H. unfold qN, Qminus.
  rewrite N2Z.inj_sub by exact H.
  rewrite <- inject_Z_opp, <- inject_Z_plus. reflexivity.
Qed.

Lemma qN_nonneg (a : N) : (0 <= qN a)%Q.
Proof.
  unfold qN. change 0%Q with (inject_Z 0). rewrite <- Zle_Qle. lia.
Qed.

Lemma qN_le_iff (a b : N) : (a <= b)%N <-> (qN a <= qN b)%Q.
Proof. unfold qN. rewrite <- Zle_Qle. lia. Qed.

Lemma qN_lt_iff (a b : N) : (a < b)%N <-> (qN a < qN b)%Q.
Proof. unfold qN. rewrite <- Zlt_Qlt. lia. Qed.

Lemma qN_eq_iff (a b : N) : a = b <-> (qN a == qN b)%Q.
Proof. unfold qN. rewrite inject_Z_injective. lia. Qed.

Lemma qpow2_0 : (qpow2 0 == 1)%Q.
Proof. reflexivity. Qed.

Lemma qpow2_add (a b : nat) : (qpow2 (a + b) == qpow2 a * qpow2 b)%Q.
Proof.
  unfold qpow2. rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
  rewrite inject_Z_mult. reflexivity.
Qed.

Lemma qpow2_1_add (k : nat) : (qpow2 (1 + k) == 2 * qpow2 k)%Q.
Proof.
  rewrite qpow2_add. change (qpow2 1) with 2%Q. reflexivity.
Qed.

Lemma qpow2_pos (k : nat) : (0 < qpow2 k)%Q.
Proof.
  unfold qpow2. change 0%Q with (inject_Z 0). rewrite <- Zlt_Qlt.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma qpow2_mono {a b : nat} (h : a <= b) : (qpow2 a <= qpow2 b)%Q.
Proof.
  unfold qpow2. rewrite <- Zle_Qle.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma qN_pow2 (k : nat) : (qN (2 ^ (N.of_nat k))%N == qpow2 k)%Q.
Proof.
  unfold qN, qpow2.
  rewrite N2Z.inj_pow, nat_N_Z. reflexivity.
Qed.

Fixpoint z13 (u : list Word) : Rat :=
  match u with
  | [] => 1%Q
  | V :: u' => ((1#2) * z13 u')%Q
  | K :: u' => (2 * z13 u')%Q
  | Q_w :: u' => (2 * z13 u')%Q
  end.

Fixpoint zW (u : list Word) : Rat :=
  match u with
  | [] => 0%Q
  | V :: u' => ((1#8) + (1#2) * zW u')%Q
  | K :: u' => (1 + 2 * zW u')%Q
  | Q_w :: u' => ((1#4) + 2 * zW u')%Q
  end.

Lemma z13_pos (u : list Word) : (0 < z13 u)%Q.
Proof.
  induction u as [| a u ih]; [cbn; lra |].
  destruct a; cbn [z13]; lra.
Qed.

Lemma z13_append (u v : list Word) : (z13 (u ++ v) == z13 u * z13 v)%Q.
Proof.
  induction u as [| a u ih]; [cbn; lra |].
  destruct a; cbn [List.app z13]; rewrite ih; lra.
Qed.

Lemma zW_nonneg (u : list Word) : (0 <= zW u)%Q.
Proof.
  induction u as [| a u ih]; [cbn; lra |].
  destruct a; cbn [zW]; lra.
Qed.

Lemma zW_append (u t : list Word) : (zW (u ++ t) == zW u + z13 u * zW t)%Q.
Proof.
  induction u as [| a u ih]; [cbn; lra |].
  destruct a; cbn [List.app zW z13]; rewrite ih; lra.
Qed.

Definition psi (m : Mode) : Rat :=
  match m with
  | KA1 | KHV | PHV => 1%Q
  | _ => 4%Q
  end.

Definition phi (m : Mode) : Rat :=
  match m with
  | FH0 | FH1 | PH0 | PH1 => 4%Q
  | _ => 1%Q
  end.

Definition alpha (m : Mode) : Rat :=
  match m with
  | PA1 | FA1 => 96%Q
  | _ => 24%Q
  end.

Definition addW (w : Word) : Rat :=
  match w with
  | V => (1#8)%Q
  | K => 1%Q
  | Q_w => (1#4)%Q
  end.

Definition mulW (w : Word) : Rat :=
  match w with
  | V => (1#2)%Q
  | K => 2%Q
  | Q_w => 2%Q
  end.

Lemma zW_cons (w : Word) (u : list Word) : zW (w :: u) = (addW w + mulW w * zW u)%Q.
Proof. destruct w; reflexivity. Qed.

Definition multZW (m : Mode) : Rat :=
  match m with
  | KHV => (15#32)%Q
  | PHV => (15#4)%Q
  | _ => (15#8)%Q
  end.

Definition cSt (m : Mode) (p : N) : Rat :=
  match m, p with
  | PA1, 0%N | FA1, 0%N => (35#128)%Q
  | PA1, 1%N | FA1, 1%N => (7#256)%Q
  | FH0, _ | PH0, _ => (49#64)%Q
  | FH1, _ | PH1, _ => (1#64)%Q
  | KA1, 0%N | KHV, 0%N => 1%Q
  | KA1, 1%N | KHV, 1%N => 0%Q
  | _, _ => 0%Q
  end.

Definition kqA (m : Mode) (s : DState) : Rat :=
  match m, s with
  | PA1, S2 | FA1, S2 => (1#8)%Q
  | KA1, S5 => (1#64)%Q
  | KHV, S3 => (1#32)%Q
  | PHV, S4 => (1#32)%Q
  | PHV, S3 | PHV, S5 => (1#4)%Q
  | FH0, S4 | PH0, S4 | FH1, S4 | PH1, S4 => (1#8)%Q
  | PH0, S3 | PH0, S5 | PH1, S3 | PH1, S5 => 1%Q
  | _, _ => 0%Q
  end.

Definition kqC (m : Mode) (s : DState) : Rat :=
  match m, s with
  | PA1, S2 | FA1, S2 => (-(1#8))%Q
  | KA1, S5 => (1#2)%Q
  | KHV, S3 => (1#2)%Q
  | PHV, S4 => (1#16)%Q
  | PHV, S3 | PHV, S5 => (-(3#8))%Q
  | FH0, S4 | PH0, S4 => (3#4)%Q
  | FH1, S4 | PH1, S4 => 0%Q
  | PH0, S3 | PH0, S5 => (-1)%Q
  | PH1, S3 | PH1, S5 => (-(7#4))%Q
  | _, _ => 0%Q
  end.

Lemma stepRule_z13 (r : StepRule) :
    (psi (rOutMode r) * z13 (rEmit r) * qpow2 (rG r) == psi (rInMode r) * z13 [rWord r])%Q.
Proof.
  destruct r; vm_compute; reflexivity.
Qed.

Lemma Scan_z13 {m1 : Mode} {s1 : DState} {n1 : N} {u : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v : list Word} {g : nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    (psi m2 * z13 v * qpow2 g == psi m1 * z13 u)%Q.
Proof.
  induction h as [m s n hm hn | r s1 s2 s3 n1 n2 n3 g u v m3 hs hm1 hv _ ih].
  - cbn [z13]. rewrite qpow2_0. lra.
  - pose proof (stepRule_z13 r) as hr.
    assert (hu : (z13 (rWord r :: u) == z13 [rWord r] * z13 u)%Q).
    { destruct (rWord r); cbn [z13]; lra. }
    rewrite z13_append, qpow2_add, hu.
    transitivity ((psi m3 * z13 v * qpow2 g) * (z13 (rEmit r) * qpow2 (rG r)))%Q; [ring |].
    rewrite ih.
    transitivity ((psi (rOutMode r) * z13 (rEmit r) * qpow2 (rG r)) * z13 u)%Q; [ring |].
    rewrite hr. ring.
Qed.

Definition n2Slope (k : NKinds) : Rat :=
  match k with
  | dbl2 | dbl1 => 2%Q
  | keep => 1%Q
  | half0 | half1 => (1#2)%Q
  end.

Definition n2Const (k : NKinds) : Rat :=
  match k with
  | dbl2 => (-2)%Q
  | dbl1 => (-1)%Q
  | keep | half0 => 0%Q
  | half1 => (-(1#2))%Q
  end.

Lemma validKind_rat {k : NKinds} {n1 n2 : N} (hv : validKind k n1 n2) :
    (qN n2 == n2Slope k * qN n1 + n2Const k)%Q.
Proof.
  destruct k; cbn [validKind] in hv; cbn [n2Slope n2Const].
  - destruct hv as [hn ->]. rewrite qN_sub, qN_mul by lia. norm_qN. lra.
  - destruct hv as [hn ->]. rewrite qN_sub, qN_mul by lia. norm_qN. lra.
  - destruct hv as [_ ->]. lra.
  - destruct hv as [_ [hp ->]].
    assert (h1 : ((n1 / 2) * 2 = n1)%N) by lia.
    apply qN_eq_iff in h1. rewrite qN_mul in h1. norm_qN. lra.
  - destruct hv as [_ [hp ->]].
    assert (h1 : (1 + (n1 / 2) * 2 = n1)%N) by lia.
    apply qN_eq_iff in h1. rewrite qN_add, qN_mul in h1. norm_qN. lra.
Qed.

Lemma stepRule_delta (r : StepRule) (n1 n2 : N) (hv : validKind (rKind r) n1 n2) :
    (0 <= phi (rInMode r) * qN n1 - phi (rOutMode r) * qN n2 * z13 (rEmit r))%Q /\
    (phi (rInMode r) * qN n1 - phi (rOutMode r) * qN n2 * z13 (rEmit r) <= 16 * zW (rEmit r))%Q.
Proof.
  pose proof (validKind_rat hv) as hq.
  destruct r;
    cbn [rInMode rOutMode rKind rEmit phi n2Slope n2Const z13 zW] in *;
    lra.
Qed.

Lemma Scan_delta {m1 : Mode} {s1 : DState} {n1 : N} {u : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v : list Word} {g : nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    (0 <= phi m1 * qN n1 - phi m2 * qN n2 * z13 v)%Q /\
    (phi m1 * qN n1 - phi m2 * qN n2 * z13 v <= 16 * zW v)%Q.
Proof.
  induction h as [m s n hm hn | r s1 s2 s3 n1 n2 n3 g u v m3 hs hm1 hv _ [ih_lo ih_hi]].
  - cbn [z13 zW]. lra.
  - destruct (stepRule_delta r n1 n2 hv) as [hs_lo hs_hi].
    pose proof (z13_pos (rEmit r)) as hz_em.
    rewrite z13_append, zW_append.
    nra.
Qed.

Definition pickRule (m : Mode) (w : Word) (s : DState) (par : N) : StepRule :=
  match m, w, s, par with
  | PA1, V, S2, 0%N => R00
  | PA1, V, S2, 1%N => R00
  | PA1, V, S4, 0%N => R02
  | PA1, V, S4, 1%N => R03
  | PA1, V, S5, 0%N => R01
  | PA1, V, S5, 1%N => R01
  | PA1, Q_w, S3, 0%N => R04
  | PA1, Q_w, S3, 1%N => R04
  | PA1, Q_w, S4, 0%N => R04
  | PA1, Q_w, S4, 1%N => R04
  | PA1, Q_w, S5, 0%N => R04
  | PA1, Q_w, S5, 1%N => R04
  | FA1, V, S2, 0%N => R05
  | FA1, V, S2, 1%N => R05
  | FA1, V, S4, 0%N => R07
  | FA1, V, S4, 1%N => R08
  | FA1, V, S5, 0%N => R06
  | FA1, V, S5, 1%N => R06
  | FA1, Q_w, S3, 0%N => R09
  | FA1, Q_w, S3, 1%N => R09
  | FA1, Q_w, S4, 0%N => R09
  | FA1, Q_w, S4, 1%N => R09
  | FA1, Q_w, S5, 0%N => R09
  | FA1, Q_w, S5, 1%N => R09
  | KA1, K, S3, 0%N => R10
  | KA1, K, S3, 1%N => R10
  | KHV, K, S2, 0%N => R11
  | KHV, K, S2, 1%N => R11
  | KHV, K, S4, 0%N => R13
  | KHV, K, S4, 1%N => R14
  | KHV, K, S5, 0%N => R12
  | KHV, K, S5, 1%N => R12
  | PHV, V, S3, 0%N => R15
  | PHV, V, S3, 1%N => R15
  | PHV, K, S2, 0%N => R18
  | PHV, K, S2, 1%N => R18
  | PHV, K, S3, 0%N => R16
  | PHV, K, S3, 1%N => R17
  | PHV, K, S4, 0%N => R16
  | PHV, K, S4, 1%N => R17
  | PHV, K, S5, 0%N => R16
  | PHV, K, S5, 1%N => R17
  | PHV, Q_w, S2, 0%N => R19
  | PHV, Q_w, S2, 1%N => R19
  | FH0, V, S3, 0%N => R20
  | FH0, V, S3, 1%N => R20
  | FH0, Q_w, S2, 0%N => R21
  | FH0, Q_w, S2, 1%N => R21
  | FH1, V, S3, 0%N => R22
  | FH1, V, S3, 1%N => R22
  | FH1, Q_w, S2, 0%N => R23
  | FH1, Q_w, S2, 1%N => R23
  | PH0, V, S3, 0%N => R24
  | PH0, V, S3, 1%N => R24
  | PH0, K, S2, 0%N => R27
  | PH0, K, S2, 1%N => R27
  | PH0, K, S3, 0%N => R25
  | PH0, K, S3, 1%N => R26
  | PH0, K, S4, 0%N => R25
  | PH0, K, S4, 1%N => R26
  | PH0, K, S5, 0%N => R25
  | PH0, K, S5, 1%N => R26
  | PH0, Q_w, S2, 0%N => R28
  | PH0, Q_w, S2, 1%N => R28
  | PH1, V, S3, 0%N => R29
  | PH1, V, S3, 1%N => R29
  | PH1, K, S2, 0%N => R32
  | PH1, K, S2, 1%N => R32
  | PH1, K, S3, 0%N => R30
  | PH1, K, S3, 1%N => R31
  | PH1, K, S4, 0%N => R30
  | PH1, K, S4, 1%N => R31
  | PH1, K, S5, 0%N => R30
  | PH1, K, S5, 1%N => R31
  | PH1, Q_w, S2, 0%N => R33
  | PH1, Q_w, S2, 1%N => R33
  | _, _, _, _ => R00
  end.

Definition evalKind (k : NKinds) (n1 : N) : N :=
  match k with
  | dbl2 => (2 * n1 - 2)%N
  | dbl1 => (2 * n1 - 1)%N
  | keep => n1
  | half0 | half1 => (n1 / 2)%N
  end.

Definition kindParOk (k : NKinds) (p : N) : bool :=
  match k with
  | half0 => (p =? 0)%N
  | half1 => (p =? 1)%N
  | _ => true
  end.

Lemma validKind_eval {k : NKinds} {n1 : N} (hn1 : (2 <= n1)%N)
    (hok : kindParOk k (n1 mod 2)%N = true) : validKind k n1 (evalKind k n1).
Proof.
  destruct k; cbn [validKind evalKind]; try exact (conj hn1 eq_refl).
  - cbn [kindParOk] in hok. apply N.eqb_eq in hok. exact (conj hn1 (conj hok eq_refl)).
  - cbn [kindParOk] in hok. apply N.eqb_eq in hok. exact (conj hn1 (conj hok eq_refl)).
Qed.

Definition checkPickRule (m1 : Mode) (w : Word) (s2 : DState) (par : N) : bool :=
  let r := pickRule m1 w s2 par in
  if modeMatches m1 (dfaStep w s2) then
    mode_eqb (rInMode r) m1 && word_eqb (rWord r) w &&
    modeMatches (rOutMode r) s2 && kindParOk (rKind r) par
  else
    true.

Lemma checkPickRule_all (m1 : Mode) (w : Word) (s2 : DState) (par : N)
    (hp : par = 0%N \/ par = 1%N) : checkPickRule m1 w s2 par = true.
Proof.
  destruct hp as [-> | ->]; destruct m1, w, s2; reflexivity.
Qed.

Lemma N_mod2_01 (n : N) : (n mod 2 = 0)%N \/ (n mod 2 = 1)%N.
Proof. lia. Qed.

Lemma stepRule_survive (r : StepRule) (n1 n2 : N) (zw : Rat)
    (hz : (0 <= zw)%Q) (hv : validKind (rKind r) n1 n2)
    (hb : (alpha (rInMode r) * (addW (rWord r) + mulW (rWord r) * zw) <= qN n1 - 2)%Q) :
    (2 <= n2)%N /\ (alpha (rOutMode r) * zw <= qN n2 - 2)%Q.
Proof.
  pose proof (validKind_rat hv) as hq.
  destruct r;
    cbn [rInMode rWord rKind rOutMode alpha addW mulW n2Slope n2Const] in *;
    (split; [apply qN_le_iff; norm_qN; lra | lra]).
Qed.

Lemma step_survive (m1 : Mode) (w : Word) (s2 : DState) (n1 : N) (zw : Rat)
    (hz : (0 <= zw)%Q) (hn1 : (2 <= n1)%N) (hm1 : modeMatches m1 (dfaStep w s2) = true)
    (hb : (alpha m1 * (addW w + mulW w * zw) <= qN n1 - 2)%Q) :
    exists (r : StepRule) (n2 : N),
      rInMode r = m1 /\ rWord r = w /\ dfaStep (rWord r) s2 = dfaStep w s2 /\
      modeMatches (rOutMode r) s2 = true /\ validKind (rKind r) n1 n2 /\
      (2 <= n2)%N /\ (alpha (rOutMode r) * zw <= qN n2 - 2)%Q.
Proof.
  set (r := pickRule m1 w s2 (n1 mod 2)%N).
  pose proof (checkPickRule_all m1 w s2 (n1 mod 2)%N (N_mod2_01 n1)) as hc.
  unfold checkPickRule in hc. fold r in hc.
  rewrite hm1 in hc.
  apply Bool.andb_true_iff in hc as [hc hpar].
  apply Bool.andb_true_iff in hc as [hc hm2].
  apply Bool.andb_true_iff in hc as [hin hword].
  apply mode_eqb_eq in hin. apply word_eqb_eq in hword.
  pose proof (validKind_eval hn1 hpar) as hv.
  assert (hb' : (alpha (rInMode r) * (addW (rWord r) + mulW (rWord r) * zw) <= qN n1 - 2)%Q).
  { rewrite hin, hword. exact hb. }
  destruct (stepRule_survive r n1 (evalKind (rKind r) n1) zw hz hv hb') as [hn2 hb2].
  exists r (evalKind (rKind r) n1).
  refine (conj hin (conj hword (conj _ (conj hm2 (conj hv (conj hn2 hb2)))))).
  rewrite hword. reflexivity.
Qed.

Lemma Scan_survive (u : list Word) (s_end : DState) :
    forall (m1 : Mode) (n1 : N),
      (2 <= n1)%N ->
      modeMatches m1 (dfaRun u s_end) = true ->
      (alpha m1 * zW u <= qN n1 - 2)%Q ->
      exists m2 n2 v g, Scan m1 (dfaRun u s_end) n1 u m2 s_end n2 v g.
Proof.
  induction u as [| w u ih]; intros m1 n1 hn1 hm1 hb.
  - exists m1 n1 (@nil Word) 0. exact (Scan_nil m1 s_end n1 hm1 hn1).
  - pose proof (zW_nonneg u) as hzw.
    rewrite zW_cons in hb.
    cbn [dfaRun] in hm1 |- *.
    destruct (step_survive m1 w (dfaRun u s_end) n1 (zW u) hzw hn1 hm1 hb)
      as [r [n2 [<- [<- [_ [hm2 [hv [hn2 hb2]]]]]]]].
    destruct (ih (rOutMode r) n2 hn2 hm2 hb2) as [m_end [n_end [v [g hS]]]].
    exists m_end n_end (rEmit r ++ v) (rG r + g).
    exact (Scan_step eq_refl hm1 hv hS).
Qed.

Definition validParProp (k : NKinds) (n1 n2 : N) : Prop :=
  match k with
  | dbl2 => (n2 mod 2 = 0)%N
  | dbl1 => (n2 mod 2 = 1)%N
  | keep => (n2 mod 2 = n1 mod 2)%N
  | half0 => (n1 mod 2 = 0)%N
  | half1 => (n1 mod 2 = 1)%N
  end.

Lemma validKind_par {k : NKinds} {n1 n2 : N} (hv : validKind k n1 n2) :
    validParProp k n1 n2.
Proof.
  destruct k; cbn [validKind validParProp] in *.
  - destruct hv as [hn ->]. lia.
  - destruct hv as [hn ->]. lia.
  - destruct hv as [_ ->]. reflexivity.
  - exact (proj1 (proj2 hv)).
  - exact (proj1 (proj2 hv)).
Qed.

Lemma stepRule_zW_contract (r : StepRule) (n1 n2 : N) (zw_u : Rat)
    (hzw : (0 <= zw_u)%Q) (hv : validKind (rKind r) n1 n2) :
    (zW (rEmit r) + z13 (rEmit r) * (multZW (rOutMode r) * zw_u + cSt (rOutMode r) (n2 mod 2)%N) <=
     multZW (rInMode r) * (addW (rWord r) + mulW (rWord r) * zw_u) + cSt (rInMode r) (n1 mod 2)%N)%Q.
Proof.
  pose proof (validKind_par hv) as hpar.
  destruct (N_mod2_01 n1) as [hp1 | hp1];
    destruct (N_mod2_01 n2) as [hp2 | hp2];
    destruct r;
    cbn [rKind validParProp] in hpar;
    try congruence;
    rewrite hp1, hp2;
    cbn [rEmit rOutMode rInMode rWord cSt zW z13 multZW addW mulW];
    lra.
Qed.

Lemma cSt_nonneg (m : Mode) (p : N) : (0 <= cSt m (p mod 2)%N)%Q.
Proof.
  destruct (N_mod2_01 p) as [hp | hp]; rewrite hp; destruct m; cbn [cSt]; lra.
Qed.

Lemma Scan_zW_contract {m1 : Mode} {s1 : DState} {n1 : N} {u : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v : list Word} {g : nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) :
    (zW v <= multZW m1 * zW u + cSt m1 (n1 mod 2)%N)%Q.
Proof.
  induction h as [m s n hm hn | r s1 s2 s3 n1 n2 n3 g u v m3 hs hm1 hv _ ih].
  - pose proof (cSt_nonneg m n) as hc. cbn [zW]. lra.
  - pose proof (stepRule_zW_contract r n1 n2 (zW u) (zW_nonneg u) hv) as hstep.
    pose proof (z13_pos (rEmit r)) as hz_em.
    rewrite <- (zW_cons (rWord r) u) in hstep.
    rewrite zW_append.
    nra.
Qed.

Definition minPowS (s : DState) : N :=
  match s with
  | S2 => 1%N
  | S3 | S4 => 2%N
  | S5 => 4%N
  end.

Lemma minPowS_step2 (w1 w2 : Word) (s : DState) :
    (minPowS (dfaStep w1 (dfaStep w2 s)) <= 4)%N.
Proof.
  destruct w1, w2, s; cbn; lia.
Qed.

Lemma zPp_N (n : N) : (0 < 2 ^ n)%N.
Proof.
  assert (H : (2 ^ n <> 0)%N) by (apply N.pow_nonzero; lia).
  lia.
Qed.

Lemma dfaRun_KQ_min {A : N} {H : nat} {ds : list Word} (h : zDg A H ds) :
    (minPowS (dfaRun ds S2) <= 2 ^ (N.of_nat H))%N.
Proof.
  destruct h as [| A1 H1 ds1 h1 | A1 H1 ds1 h1].
  - cbn. lia.
  - destruct h1 as [| A2 H2 u2 _ | A2 H2 u2 _].
    + cbn. lia.
    + pose proof (zPp_N (N.of_nat H2)) as hp.
      pose proof (minPowS_step2 K K (dfaRun u2 S2)) as hm.
      cbn [dfaRun]. rewrite !zPow1_N. lia.
    + pose proof (zPp_N (N.of_nat H2)) as hp.
      pose proof (minPowS_step2 K Q_w (dfaRun u2 S2)) as hm.
      cbn [dfaRun]. rewrite !zPow1_N. lia.
  - destruct h1 as [| A2 H2 u2 _ | A2 H2 u2 _].
    + cbn. lia.
    + pose proof (zPp_N (N.of_nat H2)) as hp.
      pose proof (minPowS_step2 Q_w K (dfaRun u2 S2)) as hm.
      cbn [dfaRun]. rewrite !zPow1_N. lia.
    + pose proof (zPp_N (N.of_nat H2)) as hp.
      pose proof (minPowS_step2 Q_w Q_w (dfaRun u2 S2)) as hm.
      cbn [dfaRun]. rewrite !zPow1_N. lia.
Qed.

Lemma zDg_z13_zW {A : N} {H : nat} {ds : list Word} (h : zDg A H ds) :
    (z13 ds == qpow2 H)%Q /\ (zW ds <= qpow2 H - 1)%Q.
Proof.
  induction h as [| A H u _ [ih1 ih2] | A H u _ [ih1 ih2]].
  - cbn [z13 zW]. rewrite qpow2_0. lra.
  - rewrite qpow2_1_add. cbn [z13 zW]. lra.
  - rewrite qpow2_1_add. cbn [z13 zW]. lra.
Qed.

Lemma stepRule_KQ_zW (r : StepRule) (s2 : DState) (P : Rat)
    (hw : rWord r <> V)
    (hm1 : modeMatches (rInMode r) (dfaStep (rWord r) s2) = true)
    (hm2 : modeMatches (rOutMode r) s2 = true)
    (hP : (qN (minPowS s2) <= P)%Q) :
    (zW (rEmit r) + z13 (rEmit r) * (kqA (rOutMode r) s2 * P + kqC (rOutMode r) s2) <=
     kqA (rInMode r) (dfaStep (rWord r) s2) * (2 * P) + kqC (rInMode r) (dfaStep (rWord r) s2))%Q.
Proof.
  destruct r; cbn [rWord] in hw; try (exfalso; exact (hw eq_refl));
    destruct s2; cbn [rInMode rOutMode rWord dfaStep modeMatches] in hm1, hm2;
    try discriminate;
    cbn [rEmit rOutMode rInMode rWord dfaStep zW z13 kqA kqC minPowS] in *;
    norm_qN; lra.
Qed.

Lemma Scan_dfaRun {m1 : Mode} {s1 : DState} {n1 : N} {u : list Word}
    {m2 : Mode} {s2 : DState} {n2 : N} {v : list Word} {g : nat}
    (h : Scan m1 s1 n1 u m2 s2 n2 v g) : s1 = dfaRun u s2.
Proof.
  induction h as [m s n hm hn | r s1 s2 s3 n1 n2 n3 g u v m3 hs hm1 hv _ ih].
  - reflexivity.
  - subst s1 s2. reflexivity.
Qed.

Lemma mul_le_of_nonneg_l {c x y : Rat} (hc : (0 <= c)%Q) (hxy : (x <= y)%Q) :
    (c * x <= c * y)%Q.
Proof. nra. Qed.

Lemma Scan_KQ_zW_aux {m1 : Mode} {s1 : DState} {n1 : N} {ds : list Word}
    {m2 : Mode} {s_end : DState} {n2 : N} {v : list Word} {g : nat}
    (hS : Scan m1 s1 n1 ds m2 s_end n2 v g) :
    s_end = S2 ->
    forall {A : N} {H : nat}, zDg A H ds ->
      (zW v <= kqA m1 s1 * qpow2 H + kqC m1 s1)%Q.
Proof.
  induction hS as [m s n hm hn | r s1 s2 s3 n1 n2 n3 g ds' v m3 hs hm1 hv hrest ih];
    intros hs_end A H hD.
  - subst s.
    inversion hD; subst.
    destruct m; cbn [modeMatches] in hm; try discriminate;
      cbn [zW kqA kqC]; rewrite qpow2_0; lra.
  - subst s3 s1.
    assert (hD_tail : exists A' H', zDg A' H' ds' /\ H = 1 + H' /\ rWord r <> V).
    { inversion hD as [| A' H' u' hD' | A' H' u' hD']; subst.
      - exists A' H'. repeat split; [exact hD' | intro hc; rewrite hc in *; discriminate].
      - exists A' H'. repeat split; [exact hD' | intro hc; rewrite hc in *; discriminate]. }
    destruct hD_tail as [A' [H' [hD' [-> hw_ne]]]].
    pose proof (Scan_dfaRun hrest) as hs2_eq.
    pose proof (Scan_match_in hrest) as hm2.
    assert (hP : (qN (minPowS s2) <= qpow2 H')%Q).
    { rewrite hs2_eq, <- qN_pow2. apply qN_le_iff. exact (dfaRun_KQ_min hD'). }
    pose proof (stepRule_KQ_zW r s2 (qpow2 H') hw_ne hm1 hm2 hP) as hstep.
    pose proof (ih eq_refl _ _ hD') as ih'.
    pose proof (z13_pos (rEmit r)) as hz_em.
    pose proof (mul_le_of_nonneg_l (Qlt_le_weak _ _ hz_em) ih') as hm_ih.
    rewrite zW_append, qpow2_1_add.
    lra.
Qed.

Lemma Scan_KQ_zW {m1 : Mode} {s1 : DState} {n1 : N} {ds : list Word}
    {m2 : Mode} {n2 : N} {v : list Word} {g : nat}
    (hS : Scan m1 s1 n1 ds m2 S2 n2 v g) :
    forall {A : N} {H : nat}, zDg A H ds ->
      (zW v <= kqA m1 s1 * qpow2 H + kqC m1 s1)%Q.
Proof.
  intros A H hD. exact (Scan_KQ_zW_aux hS eq_refl hD).
Qed.

Fixpoint zDen (u : list Word) : N :=
  match u with
  | [] => 1%N
  | _ :: u' => (8 * zDen u')%N
  end.

Fixpoint z13Num (u : list Word) : N :=
  match u with
  | [] => 1%N
  | V :: u' => (4 * z13Num u')%N
  | K :: u' => (16 * z13Num u')%N
  | Q_w :: u' => (16 * z13Num u')%N
  end.

Fixpoint zWNum (u : list Word) : N :=
  match u with
  | [] => 0%N
  | V :: u' => (zDen u' + 4 * zWNum u')%N
  | K :: u' => (8 * zDen u' + 16 * zWNum u')%N
  | Q_w :: u' => (2 * zDen u' + 16 * zWNum u')%N
  end.

Lemma zDen_pos (u : list Word) : (0 < zDen u)%N.
Proof.
  induction u as [| a u ih]; cbn [zDen]; lia.
Qed.

Lemma z13Num_eq (u : list Word) : (qN (z13Num u) == z13 u * qN (zDen u))%Q.
Proof.
  induction u as [| a u ih].
  - cbn [z13Num z13 zDen]. norm_qN. lra.
  - destruct a; cbn [z13Num z13 zDen]; rewrite !qN_mul, ih; norm_qN; lra.
Qed.

Lemma zWNum_eq (u : list Word) : (qN (zWNum u) == zW u * qN (zDen u))%Q.
Proof.
  induction u as [| a u ih].
  - cbn [zWNum zW zDen]. norm_qN. lra.
  - destruct a; cbn [zWNum zW zDen]; rewrite qN_add, !qN_mul, ih; norm_qN; lra.
Qed.

Definition checkZWLe (u : list Word) (p q : N) : bool :=
  (q * zWNum u <=? p * zDen u)%N.

Lemma checkZWLe_sound (u : list Word) (p q : N)
    (h : checkZWLe u p q = true) : (qN q * zW u <= qN p)%Q.
Proof.
  unfold checkZWLe in h.
  apply N.leb_le, qN_le_iff in h.
  rewrite !qN_mul, zWNum_eq in h.
  pose proof (zDen_pos u) as hd.
  apply qN_lt_iff in hd. norm_qN.
  nra.
Qed.

Definition checkZ13Pow2 (u : list Word) (e : nat) (p q : N) : bool :=
  (q * z13Num u * 2 ^ (N.of_nat e) =? p * zDen u)%N.

Lemma checkZ13Pow2_sound (u : list Word) (e : nat) (p q : N)
    (h : checkZ13Pow2 u e p q = true) :
    (qN q * z13 u * qpow2 e == qN p)%Q.
Proof.
  unfold checkZ13Pow2 in h.
  apply N.eqb_eq, qN_eq_iff in h.
  rewrite !qN_mul, z13Num_eq, qN_pow2 in h.
  pose proof (zDen_pos u) as hd.
  apply qN_lt_iff in hd. norm_qN.
  nra.
Qed.

Definition kqA4096 (m : Mode) (s : DState) : N :=
  match m, s with
  | PA1, S2 | FA1, S2 => 512%N
  | KA1, S5 => 64%N
  | KHV, S3 => 128%N
  | PHV, S4 => 128%N
  | PHV, S3 | PHV, S5 => 1024%N
  | FH0, S4 | PH0, S4 | FH1, S4 | PH1, S4 => 512%N
  | PH0, S3 | PH0, S5 | PH1, S3 | PH1, S5 => 4096%N
  | _, _ => 0%N
  end.

Lemma kqA4096_eq (m : Mode) (s : DState) :
    (4096 * kqA m s == qN (kqA4096 m s))%Q.
Proof.
  destruct m, s; cbn [kqA kqA4096]; norm_qN; lra.
Qed.

Definition kqCPos4096 (m : Mode) (s : DState) : N :=
  match m, s with
  | KA1, S5 => 2048%N
  | KHV, S3 => 2048%N
  | PHV, S4 => 256%N
  | FH0, S4 | PH0, S4 => 3072%N
  | _, _ => 0%N
  end.

Lemma kqCPos4096_ge (m : Mode) (s : DState) :
    (4096 * kqC m s <= qN (kqCPos4096 m s))%Q.
Proof.
  destruct m, s; cbn [kqC kqCPos4096]; norm_qN; lra.
Qed.

Declare Scope word_scope.
Delimit Scope word_scope with word.
Local Notation "'Q'" := Q_w : word_scope.
Open Scope word_scope.

(* Section 5: Fixed Segments (head_w, s_full, top_base) and Concrete Orbit init -> u_0 -> u_10 *)

Definition head_w : list Word :=
  [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;V;K].

Definition v_head : list Word :=
  [V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;V;K;V].

Definition b_head : N := 266862588%N.

Lemma Scan_head : Scan PA1 S2 3%N head_w FA1 S2 b_head v_head 0.
Proof.
  pose proof (evalAffineScan_sound
    [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11]
    PA1 S2 0%N 3%N head_w FA1 0%N b_head v_head 0 0%N
    ltac:(vm_compute; reflexivity)) as h.
  change (dfaRun head_w S2) with S2 in h.
  cbn [N.mul N.add] in h.
  exact h.
Qed.

Definition top_base : list Word := [Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q].
Definition top_body : list Word := [Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q].
Definition v_top : list Word := [V;V;V;V;Q;V;V;V].
Definition A_top : N := 65151%N.

Lemma zDg_top : zDg A_top 16 top_base.
Proof. exact (checkDg_sound top_base A_top ltac:(vm_compute; reflexivity)). Qed.

Lemma Scan_top {m_top : Mode} (hm : m_top = PA1 \/ m_top = FA1) (b_top : N) (hb : (2 <= b_top)%N) :
    Scan m_top S2 b_top top_body PA1 S2 (64 * (b_top - 2) + 41)%N v_top 21.
Proof.
  replace b_top with (1 * (b_top - 2) + 2)%N at 1 by lia.
  destruct hm as [-> | ->].
  - pose proof (evalAffineScan_sound
      [R04;R19;R04;R19;R04;R19;R04;R17;R32;R04;R19;R04;R19;R04;R19]
      PA1 S2 1%N 2%N top_body PA1 64%N 41%N v_top 21 (b_top - 2)%N
      ltac:(vm_compute; reflexivity)) as h.
    change (dfaRun top_body S2) with S2 in h.
    exact h.
  - pose proof (evalAffineScan_sound
      [R09;R19;R04;R19;R04;R19;R04;R17;R32;R04;R19;R04;R19;R04;R19]
      FA1 S2 1%N 2%N top_body PA1 64%N 41%N v_top 21 (b_top - 2)%N
      ltac:(vm_compute; reflexivity)) as h.
    change (dfaRun top_body S2) with S2 in h.
    exact h.
Qed.

Definition bot_w : list Word := [Q;K;K;Q;K;Q].
Definition A_bot : N := 41%N.

Lemma zDg_bot : zDg A_bot 6 bot_w.
Proof. exact (checkDg_sound bot_w A_bot ltac:(vm_compute; reflexivity)). Qed.

Definition s_base : list Word := [V;V;V;V;Q;V;V;V;V].
Definition s_full : list Word := s_base ++ bot_w.

Definition sRuleTable (m_in : Mode) (s_ds : DState) : list StepRule :=
  match m_in, s_ds with
  | PA1, S2 => [R00;R05;R05;R07;R21;R00;R05;R05;R05;R09;R16;R27;R04;R16;R28]
  | PA1, _  => [R00;R05;R05;R07;R21;R00;R05;R05;R05;R09;R16;R27;R04;R18;R04]
  | FA1, S2 => [R05;R05;R05;R07;R21;R00;R05;R05;R05;R09;R16;R27;R04;R16;R28]
  | FA1, _  => [R05;R05;R05;R07;R21;R00;R05;R05;R05;R09;R16;R27;R04;R18;R04]
  | _, _    => []
  end.

Definition checkOneS (m_in : Mode) (s_ds : DState) (r16 : N) : bool :=
  match evalAffineScan (sRuleTable m_in s_ds) m_in s_ds 16%N (64 + r16)%N s_full with
  | Some (m_ds, mb_s, cb_s, v_s, g_s) =>
    (6 <=? g_s) && (2048 <=? mb_s)%N && (7919 <=? cb_s)%N &&
    checkZWLe v_s 43%N 128%N &&
    (z13Num v_s * kqA4096 m_ds s_ds <=? 4 * zDen v_s)%N &&
    (z13Num v_s * kqCPos4096 m_ds s_ds <=? zDen v_s)%N
  | None => false
  end.

Lemma checkOneS_all (m_in : Mode) (s_ds : DState) (r16 : N)
    (hm : m_in = PA1 \/ m_in = FA1) (hr : (r16 < 16)%N) :
    checkOneS m_in s_ds r16 = true.
Proof.
  assert (hr_cases :
    r16 = 0%N \/ r16 = 1%N \/ r16 = 2%N \/ r16 = 3%N \/
    r16 = 4%N \/ r16 = 5%N \/ r16 = 6%N \/ r16 = 7%N \/
    r16 = 8%N \/ r16 = 9%N \/ r16 = 10%N \/ r16 = 11%N \/
    r16 = 12%N \/ r16 = 13%N \/ r16 = 14%N \/ r16 = 15%N) by lia.
  destruct hm as [-> | ->]; destruct s_ds;
    repeat (destruct hr_cases as [-> | hr_cases]);
    try subst r16;
    vm_compute; reflexivity.
Qed.

Lemma Scan_s_all {m_p : Mode} (hm_p : m_p = PA1 \/ m_p = FA1) (s_ds : DState)
    {bp : N} (hbp : (64 <= bp)%N) :
    exists m_ds b_ds v_s g_s,
      Scan m_p S2 bp s_full m_ds s_ds b_ds v_s g_s /\
      6 <= g_s /\
      (128 * bp <= b_ds + 2200)%N /\
      (zW v_s <= 43 # 128)%Q /\
      (z13 v_s * kqA m_ds s_ds <= 1 # 1024)%Q /\
      (z13 v_s * kqC m_ds s_ds <= 1 # 4096)%Q.
Proof.
  set (q := ((bp - 64) / 16)%N).
  set (r16 := ((bp - 64) mod 16)%N).
  assert (hr16_lt : (r16 < 16)%N) by (unfold r16; lia).
  pose proof (checkOneS_all m_p s_ds r16 hm_p hr16_lt) as hc.
  unfold checkOneS in hc.
  destruct (evalAffineScan (sRuleTable m_p s_ds) m_p s_ds 16%N (64 + r16)%N s_full)
    as [[[[[m_ds mb_s] cb_s] v_s] g_s] |] eqn:hrec; [| discriminate].
  apply Bool.andb_true_iff in hc as [hc hC_b].
  apply Bool.andb_true_iff in hc as [hc hA_b].
  apply Bool.andb_true_iff in hc as [hc hzw_b].
  apply Bool.andb_true_iff in hc as [hc hcb_s].
  apply Bool.andb_true_iff in hc as [hg_s hmb_s].
  apply Nat.leb_le in hg_s.
  apply N.leb_le in hmb_s.
  apply N.leb_le in hcb_s.
  apply N.leb_le in hA_b.
  apply N.leb_le in hC_b.
  pose proof (evalAffineScan_sound (sRuleTable m_p s_ds) m_p s_ds 16%N (64 + r16)%N s_full
    m_ds mb_s cb_s v_s g_s q hrec) as hScan.
  assert (hd_s : dfaRun s_full s_ds = S2).
  { destruct s_ds; reflexivity. }
  assert (hbp_eq : (16 * q + (64 + r16) = bp)%N) by (unfold q, r16; lia).
  rewrite hd_s, hbp_eq in hScan.
  assert (hmq : (2048 * q <= mb_s * q)%N).
  { apply N.mul_le_mono_nonneg_r; lia. }
  assert (hb_ds : (128 * bp <= mb_s * q + cb_s + 2200)%N).
  { unfold q, r16 in *; lia. }
  assert (hzw_r : (zW v_s <= 43 # 128)%Q).
  { pose proof (checkZWLe_sound v_s 43%N 128%N hzw_b) as h128.
    norm_qN. lra. }
  pose proof (zDen_pos v_s) as hd_pos.
  apply qN_lt_iff in hd_pos. norm_qN.
  assert (hA_r : (z13 v_s * kqA m_ds s_ds <= 1 # 1024)%Q).
  { apply qN_le_iff in hA_b.
    rewrite !qN_mul, z13Num_eq, <- kqA4096_eq in hA_b.
    norm_qN. nra. }
  assert (hC_r : (z13 v_s * kqC m_ds s_ds <= 1 # 4096)%Q).
  { apply qN_le_iff in hC_b.
    rewrite qN_mul, z13Num_eq in hC_b.
    assert (hx : (z13 v_s * qN (kqCPos4096 m_ds s_ds) <= 1)%Q) by nra.
    pose proof (kqCPos4096_ge m_ds s_ds) as hc_le.
    pose proof (z13_pos v_s) as hz13_pos.
    nra. }
  exists m_ds (mb_s * q + cb_s)%N v_s g_s.
  exact (conj hScan (conj hg_s (conj hb_ds (conj hzw_r (conj hA_r hC_r))))).
Qed.

Definition u_0 : list Word := [V; Q].

Lemma init_to_u0 : c0 -->* zCf (zTs u_0 0inf%sym).
Proof.
  unfold u_0; cbn [zTs]; unfold zCf, V_u, Q_u; cbn [Str_app].
  solve_init.
Qed.

Definition u_1 : list Word := [V;V;V;K;K;Q].
Lemma step_0 : Step u_0 u_1.
Proof. exact (checkStep_sound [R00] [V] [K;K;Q] u_1 ltac:(vm_compute; reflexivity)). Qed.

Definition u_2 : list Word := [V;V;V;V;V;V;K;K;Q;K;Q].
Lemma step_1 : Step u_1 u_2.
Proof. exact (checkStep_sound [R00;R05;R06;R10;R11] [V;V;V;K;K] [K;K;Q;K;Q] u_2 ltac:(vm_compute; reflexivity)). Qed.

Definition u_3 : list Word := [V;V;V;V;V;V;V;V;V;V;K;Q;Q;K;K;K;K;K;Q].
Lemma step_2 : Step u_2 u_3.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R06;R10;R11;R09;R18] [V;V;V;V;V;V;K;K;Q;K] [K;Q;Q;K;K;K;K;K;Q] u_3 ltac:(vm_compute; reflexivity)). Qed.

Definition u_4 : list Word := [V;V;V;V;V;V;V;V;V;V;K;V;Q;V;Q;Q;Q;Q;V;K;K;Q;Q;Q].
Lemma step_3 : Step u_3 u_4.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R14;R23;R04;R17;R31;R31;R31;R32] [V;V;V;V;V;V;V;V;V;V;K;Q;Q;K;K;K;K;K] [K;K;Q;Q;Q] u_4 ltac:(vm_compute; reflexivity)). Qed.

Definition u_5 : list Word := [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;Q;Q;Q;Q;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q].
Lemma step_4 : Step u_4 u_5.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R21;R00;R09;R19;R04;R19;R01;R10;R11;R09;R19] [V;V;V;V;V;V;V;V;V;V;K;V;Q;V;Q;Q;Q;Q;V;K;K;Q;Q] [Q;Q;Q;Q;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q] u_5 ltac:(vm_compute; reflexivity)). Qed.

Definition u_6 : list Word := [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;Q;K;K;Q;K;Q;Q;K;K;K;K;K;K;K;K;Q;K;Q;Q;Q;Q;Q;Q;Q].
Lemma step_5 : Step u_5 u_6.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R05;R05;R05;R05;R09;R19;R04;R19;R04;R18;R04;R18;R04;R19;R04;R19;R04;R19] [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;Q;Q;Q;Q;Q;K;Q;K;Q;Q;Q;Q;Q;Q] [Q;K;K;Q;K;Q;Q;K;K;K;K;K;K;K;K;Q;K;Q;Q;Q;Q;Q;Q;Q] u_6 ltac:(vm_compute; reflexivity)). Qed.

Definition u_7 : list Word := [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;K;V;Q;Q;Q;Q;Q;Q;Q;V;V;V;V;V;Q;K;K;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q].
Lemma step_6 : Step u_6 u_7.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R09;R16;R27;R04;R16;R28;R04;R17;R31;R31;R31;R31;R31;R31;R32;R04;R18;R04;R19;R04;R19;R04;R19] [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;Q;K;K;Q;K;Q;Q;K;K;K;K;K;K;K;K;Q;K;Q;Q;Q;Q;Q;Q] [Q;K;K;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q] u_7 ltac:(vm_compute; reflexivity)). Qed.

Definition u_8 : list Word := [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;Q;V;V;K;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;Q;V;V;V;V;Q;K;K;Q;K;Q;Q;Q;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q].
Lemma step_7 : Step u_7 u_8.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R07;R20;R14;R22;R11;R07;R21;R04;R19;R04;R19;R04;R19;R00;R05;R05;R05;R05;R09;R16;R27;R04;R18;R04;R16;R28;R04;R19;R04;R19;R04;R19;R04;R17;R32;R04;R19;R04;R19;R04;R19] [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;K;V;Q;Q;Q;Q;Q;Q;Q;V;V;V;V;V;Q;K;K;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q] [Q;K;K;Q;K;Q;Q;Q;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q] u_8 ltac:(vm_compute; reflexivity)). Qed.

Definition u_9 : list Word := [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;Q;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;K;V;V;V;V;V;K;V;V;V;V;V;V;V;Q;V;V;V;V;V;V;V;V;Q;V;V;V;V;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;K;Q;K;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q].
Lemma step_8 : Step u_8 u_9.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R21;R03;R22;R11;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R07;R21;R00;R05;R05;R05;R09;R16;R27;R04;R18;R04;R19;R04;R18;R04;R19;R04;R18;R04;R19;R04;R17;R32;R04;R19;R04;R19;R04;R19;R04;R19;R04;R19;R04;R19;R04;R19;R04;R17;R32;R04;R19;R04;R19;R04;R19] [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;Q;V;V;K;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;Q;V;V;V;V;Q;K;K;Q;K;Q;Q;Q;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q] [Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;K;Q;K;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q] u_9 ltac:(vm_compute; reflexivity)). Qed.

Definition u_10 : list Word := [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;K;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;K;V;V;V;V;V;K;V;V;V;V;V;V;V;V;K;V;V;V;V;V;V;V;V;K;V;V;V;V;V;K;V;V;V;V;V;K;V;K;V;V;V;V;Q;V;V;V;V;V;V;V;V;V;V;V;V;V;Q;V;V;V;V;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;K;Q;Q;Q;K;Q;K;K;Q;K;K;K;Q;Q;Q;K;Q;Q;Q;Q;Q;Q;K;Q;Q;Q;Q;Q;Q;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;K;K;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q].
Lemma step_9 : Step u_9 u_10.
Proof. exact (checkStep_sound [R00;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R07;R21;R00;R05;R05;R05;R05;R05;R05;R07;R20;R11;R07;R20;R11;R05;R05;R05;R07;R20;R11;R05;R05;R05;R07;R20;R11;R05;R05;R05;R05;R05;R05;R07;R21;R00;R05;R05;R05;R05;R05;R05;R07;R21;R00;R05;R05;R05;R09;R16;R27;R04;R18;R04;R19;R04;R19;R04;R18;R04;R16;R27;R04;R16;R27;R04;R19;R04;R18;R04;R19;R04;R17;R32;R04;R19;R04;R19;R04;R19;R04;R18;R04;R18;R04;R19;R04;R19;R04;R19;R04;R19;R04;R19;R04;R19;R04;R19;R04;R17;R32;R04;R19;R04;R19;R04;R19] [V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;V;K;V;V;K;V;Q;V;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;K;V;V;V;V;V;K;V;V;V;V;V;V;V;Q;V;V;V;V;V;V;V;V;Q;V;V;V;V;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;K;Q;K;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q;K;Q;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q] [Q;K;K;Q;K;Q;Q;Q;Q;Q;K;K;Q;Q;Q;K;Q;K;K;Q;K;K;K;Q;Q;Q;K;Q;Q;Q;Q;Q;Q;K;Q;Q;Q;Q;Q;Q;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;K;K;K;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;Q] u_10 ltac:(vm_compute; reflexivity)). Qed.

Lemma rounds_0_10 : Rounds u_0 u_10.
Proof.
  exact
    (Rounds_next step_0 (Rounds_next step_1 (Rounds_next step_2 (Rounds_next step_3
      (Rounds_next step_4 (Rounds_next step_5 (Rounds_next step_6 (Rounds_next step_7
        (Rounds_next step_8 (Rounds_next step_9 (Rounds_refl u_10))))))))))).
Qed.

(* Section 6: 5-Piece Invariant Good u, Unconditional Closure Good_step, and nonhalt *)

Definition Good (u : list Word) : Prop :=
  exists (p_w ds_core : list Word) (A_core : N) (m : nat),
    u = head_w ++ p_w ++ s_full ++ ds_core ++ top_base /\
    (exists p_tail, p_w = V :: V :: p_tail) /\
    8 <= m /\
    zDg A_core m ds_core /\
    (z13 p_w * qpow2 m == 2048)%Q /\
    (zW p_w <= 43)%Q.

Definition p_init : list Word :=
  [V;V;K;V;V;V;V;V;V;V;V;K;V;V;K;V;V;V;V;V;K;V;V;V;V;V;K;V;V;V;V;V;V;V;V;K;V;V;V;V;V;V;V;V;K;V;V;V;V;V;K;V;V;V;V;V;K;V;K;V;V;V;V;Q;V;V;V;V;V;V;V;V;V].

Definition ds_core_init : list Word :=
  [Q;Q;Q;Q;K;K;Q;Q;Q;K;Q;K;K;Q;K;K;K;Q;Q;Q;K;Q;Q;Q;Q;Q;Q;K;Q;Q;Q;Q;Q;Q;K;Q;Q;Q;K;Q;Q;Q;K;K;Q;Q;Q;Q;Q;Q;K;K;K;Q;Q;Q;Q;Q;Q;Q;Q;Q].

Lemma good_u10 : Good u_10.
Proof.
  exists p_init ds_core_init 4603791232746792399%N 62.
  split; [vm_compute; reflexivity |].
  split; [exists (List.tl (List.tl p_init)); vm_compute; reflexivity |].
  split; [lia |].
  split; [exact (checkDg_sound ds_core_init 4603791232746792399%N ltac:(vm_compute; reflexivity)) |].
  split.
  - pose proof (checkZ13Pow2_sound p_init 62 2048%N 1%N ltac:(vm_compute; reflexivity)) as h.
    norm_qN. lra.
  - pose proof (checkZWLe_sound p_init 43%N 1%N ltac:(vm_compute; reflexivity)) as h.
    norm_qN. lra.
Qed.

Lemma bound_b_end_zDg {mid_all v_mid : list Word} {m_top : Mode} {b_top : N} {g_mid : nat}
    (hm_top : m_top = PA1 \/ m_top = FA1)
    (hb_top : (2 <= b_top)%N)
    (hg_mid : 6 <= g_mid)
    (hS_mid : Scan FA1 S2 b_head mid_all m_top S2 b_top v_mid g_mid)
    (hz13_vmid : (z13 v_mid * qpow2 g_mid == 1024)%Q)
    (hzW_vmid : (zW v_mid <= 43821 # 512)%Q) :
    exists (A_core' : N) (ds_core' : list Word),
      zDg A_core' (g_mid + 2) ds_core' /\
      zDg (64 * (b_top - 2) + 41)%N (22 + g_mid + 2)
          (bot_w ++ ds_core' ++ top_base).
Proof.
  destruct (Scan_delta hS_mid) as [hd_lo hd_hi].
  assert (hphi_top : phi m_top = 1%Q) by (destruct hm_top as [-> | ->]; reflexivity).
  rewrite hphi_top in hd_lo, hd_hi.
  cbn [phi] in hd_lo, hd_hi.
  assert (h_pow_ge64 : (64 <= qpow2 g_mid)%Q).
  { change 64%Q with (qpow2 6). exact (qpow2_mono hg_mid). }
  assert (h_pow_pos : (0 <= qpow2 g_mid)%Q) by lra.
  unfold b_head in hd_lo, hd_hi. norm_qN.
  assert (hbt_lo : (266861218 <= qN b_top * z13 v_mid)%Q) by lra.
  assert (hbt_hi : (qN b_top * z13 v_mid <= 266862588)%Q) by lra.
  assert (h_assoc : ((qN b_top * z13 v_mid) * qpow2 g_mid == 1024 * qN b_top)%Q).
  { transitivity (qN b_top * (z13 v_mid * qpow2 g_mid))%Q; [ring |].
    rewrite hz13_vmid. ring. }
  assert (hm1 : (266861218 * qpow2 g_mid <= 1024 * qN b_top)%Q) by (rewrite <- h_assoc; nra).
  assert (hm2 : (1024 * qN b_top <= 266862588 * qpow2 g_mid)%Q) by (rewrite <- h_assoc; nra).
  set (n_end := (64 * (b_top - 2) + 41)%N).
  assert (hn_end_r : (16 * qN n_end == 1024 * qN b_top - 1392)%Q).
  { unfold n_end. rewrite qN_add, qN_mul, qN_sub by exact hb_top. norm_qN. ring. }
  assert (h_shift_r : (qpow2 (8 + g_mid) == 256 * qpow2 g_mid)%Q).
  { rewrite qpow2_add. change (qpow2 8) with 256%Q. reflexivity. }
  assert (h_nend_lo_r : (qN A_top * qpow2 (8 + g_mid) < qN n_end)%Q).
  { rewrite h_shift_r. unfold A_top. norm_qN. lra. }
  assert (h_nend_hi_r : (qN n_end < qN (A_top + 1) * qpow2 (8 + g_mid))%Q).
  { rewrite qN_add, h_shift_r. unfold A_top. norm_qN. lra. }
  rewrite <- qN_pow2, <- qN_mul in h_nend_lo_r, h_nend_hi_r.
  apply qN_lt_iff in h_nend_lo_r.
  apply qN_lt_iff in h_nend_hi_r.
  set (P := (2 ^ (N.of_nat (g_mid + 2)))%N).
  assert (hp_pos : (0 < P)%N) by (unfold P; apply zPp_N).
  set (A_core' := ((b_top - 2) mod P)%N).
  assert (h_Acore'_lt : (A_core' < P)%N) by (unfold A_core'; lia).
  destruct (zDg_exists (g_mid + 2) A_core' h_Acore'_lt) as [ds_core' hD_core'].
  pose proof (zDg_append zDg_bot hD_core') as h_bot_mid.
  pose proof (zDg_append h_bot_mid zDg_top) as h_all.
  assert (h_pow_eq : (2 ^ (N.of_nat (8 + g_mid)) = 64 * P)%N).
  { unfold P. replace (8 + g_mid) with (6 + (g_mid + 2)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r. change (2 ^ N.of_nat 6)%N with 64%N. reflexivity. }
  assert (h_pow_eq2 : (2 ^ (N.of_nat (6 + (g_mid + 2))) = 64 * P)%N).
  { unfold P. rewrite Nat2N.inj_add, N.pow_add_r. change (2 ^ N.of_nat 6)%N with 64%N. reflexivity. }
  rewrite h_pow_eq in h_nend_lo_r, h_nend_hi_r.
  assert (hbt_lo_P : (P * A_top <= b_top - 2)%N) by (unfold A_top, n_end in *; lia).
  assert (hbt_hi_P : (b_top - 2 < P * (A_top + 1))%N) by (unfold A_top, n_end in *; lia).
  assert (h_div_bt : ((b_top - 2) / P = A_top)%N).
  { symmetry. apply (N.div_unique (b_top - 2) P A_top ((b_top - 2) - P * A_top)%N); unfold A_top in *; lia. }
  pose proof (N.div_mod (b_top - 2) P ltac:(lia)) as hdm.
  rewrite h_div_bt in hdm.
  assert (h_val_all : (A_bot + A_core' * 2 ^ (N.of_nat 6) + A_top * 2 ^ (N.of_nat (6 + (g_mid + 2))))%N = n_end).
  { rewrite h_pow_eq2. change (2 ^ N.of_nat 6)%N with 64%N.
    unfold A_core' in hdm.
    unfold A_bot, A_top, n_end in *.
    lia. }
  assert (h_len_all : (6 + (g_mid + 2)) + 16 = 22 + g_mid + 2) by lia.
  rewrite h_val_all, h_len_all, <- app_assoc in h_all.
  exists A_core' ds_core'.
  exact (conj hD_core' h_all).
Qed.

Lemma Scan_FA1_V_emit {m0 m2 : Mode} {s0 s2 : DState} {n1 n2 : N} {u0 v : list Word} {g : nat}
    (h : Scan m0 s0 n1 u0 m2 s2 n2 v g)
    (hm0 : m0 = FA1) (hu0 : exists p_rest, u0 = V :: p_rest) :
    exists v_tail, v = V :: v_tail.
Proof.
  destruct hu0 as [p_rest hu_eq].
  destruct h as [| r s1 s2' s3 n1' n2' n3 g' u' v_rest m3 hs hm1 hv hrest].
  - discriminate hu_eq.
  - assert (hw : rWord r = V) by (injection hu_eq as hw _; exact hw).
    destruct r; cbn [rInMode] in hm0; try discriminate hm0;
      cbn [rWord] in hw; try discriminate hw;
      cbn [rEmit List.app]; exists v_rest; reflexivity.
Qed.

Lemma Good_step {u : list Word} (hG : Good u) :
    exists u', Step u u' /\ Good u'.
Proof.
  destruct hG as [p_w [ds_core [A_core [m [-> [[p_tail hp_start] [hm [hD_core [hz13 hzW]]]]]]]]].
  assert (hdfa_p : dfaRun p_w S2 = S2).
  { rewrite hp_start. cbn [dfaRun]. apply dfaStep_VV. }
  assert (hb_head_ok : (alpha FA1 * zW p_w <= qN b_head - 2)%Q).
  { cbn [alpha]. unfold b_head. norm_qN. lra. }
  assert (hm_fa1 : modeMatches FA1 (dfaRun p_w S2) = true).
  { rewrite hdfa_p. reflexivity. }
  destruct (Scan_survive p_w S2 FA1 b_head ltac:(unfold b_head; lia) hm_fa1 hb_head_ok)
    as [m_p [bp [v_p [gp hS_p]]]].
  rewrite hdfa_p in hS_p.
  pose proof (proj2 (Scan_exit_ge2 hS_p)) as hm_p_match.
  assert (hm_p : m_p = PA1 \/ m_p = FA1).
  { destruct m_p; cbn [modeMatches] in hm_p_match; try discriminate; [left | right]; reflexivity. }
  assert (hz13_vp_eq : (z13 v_p * qpow2 gp == z13 p_w)%Q).
  { pose proof (Scan_z13 hS_p) as h.
    assert (hpsi_p : psi m_p = 4%Q) by (destruct hm_p as [-> | ->]; reflexivity).
    rewrite hpsi_p in h. cbn [psi] in h. lra. }
  assert (h_pow_gp_ge1 : (1 <= qpow2 gp)%Q).
  { change 1%Q with (qpow2 0). apply qpow2_mono. lia. }
  pose proof (z13_pos v_p) as hz13_vp_pos.
  assert (hz13_vp_le_pw : (z13 v_p <= z13 p_w)%Q).
  { rewrite <- hz13_vp_eq. nra. }
  assert (h_pow_m_ge256 : (256 <= qpow2 m)%Q).
  { change 256%Q with (qpow2 8). exact (qpow2_mono hm). }
  pose proof (z13_pos p_w) as hz13_pw_pos.
  assert (hz13_pw_le8 : (z13 p_w <= 8)%Q) by nra.
  assert (hz13_vp_le8 : (z13 v_p <= 8)%Q) by lra.
  assert (hz13_vp_powm : (z13 v_p * qpow2 m <= 2048)%Q).
  { rewrite <- hz13. nra. }
  assert (hzw_vp : (zW v_p <= 10355 # 128)%Q).
  { pose proof (Scan_zW_contract hS_p) as hc.
    replace (b_head mod 2)%N with 0%N in hc by (vm_compute; reflexivity).
    cbn [multZW cSt] in hc. lra. }
  assert (hbp_lb : (130303 * 2 ^ (N.of_nat m) <= bp)%N).
  { destruct (Scan_delta hS_p) as [_ hd_hi].
    assert (hphi_p : phi m_p = 1%Q) by (destruct hm_p as [-> | ->]; reflexivity).
    rewrite hphi_p in hd_hi. cbn [phi] in hd_hi. unfold b_head in hd_hi. norm_qN.
    assert (h1 : (266861293 <= qN bp * z13 v_p)%Q) by lra.
    pose proof (qpow2_pos m) as hqm_pos.
    pose proof (qN_nonneg bp) as hbp_nn.
    assert (h_assoc : ((qN bp * z13 v_p) * qpow2 m == qN bp * (z13 v_p * qpow2 m))%Q) by ring.
    assert (hm1 : (266861293 * qpow2 m <= qN bp * (z13 v_p * qpow2 m))%Q) by (rewrite <- h_assoc; nra).
    assert (hm2 : (qN bp * (z13 v_p * qpow2 m) <= qN bp * 2048)%Q) by nra.
    assert (h_rat : (130303 * qpow2 m <= qN bp)%Q) by lra.
    apply qN_le_iff. rewrite qN_mul, qN_pow2. norm_qN. exact h_rat. }
  assert (hbp_ge64 : (64 <= bp)%N).
  { pose proof (zPp_N (N.of_nat m)) as hpm. lia. }
  set (s_ds := dfaRun ds_core S2).
  destruct (Scan_s_all hm_p s_ds hbp_ge64)
    as [m_ds [b_ds [v_s [g_s [hS_s [hg_s [hb_ds [hzw_vs [hkqA_vs hkqC_vs]]]]]]]]].
  destruct (zDg_z13_zW hD_core) as [hz13_ds hzW_ds].
  assert (hb_ds_ge2 : (2 <= b_ds)%N) by lia.
  pose proof (proj2 (Scan_exit_ge2 hS_s)) as hm_ds_match.
  assert (hb_ds_ok : (alpha m_ds * zW ds_core <= qN b_ds - 2)%Q).
  { assert (ha_hi : (alpha m_ds <= 96)%Q) by (destruct m_ds; cbn [alpha]; lra).
    pose proof (zW_nonneg ds_core) as hzw_nn.
    assert (hm1 : (alpha m_ds * zW ds_core <= 96 * (qpow2 m - 1))%Q) by nra.
    assert (hbp_r : (130303 * qpow2 m <= qN bp)%Q).
    { pose proof (proj1 (qN_le_iff _ _) hbp_lb) as hr.
      rewrite qN_mul, qN_pow2 in hr. norm_qN. exact hr. }
    assert (hbds_r : (128 * qN bp <= qN b_ds + 2200)%Q).
    { pose proof (proj1 (qN_le_iff _ _) hb_ds) as hr.
      rewrite qN_mul, qN_add in hr. norm_qN. exact hr. }
    pose proof (qpow2_pos m) as hqm_pos.
    lra. }
  destruct (Scan_survive ds_core S2 m_ds b_ds hb_ds_ge2 hm_ds_match hb_ds_ok)
    as [m_top [b_top [v_ds [g_ds hS_ds]]]].
  destruct (Scan_exit_ge2 hS_ds) as [hb_top hm_top_match].
  assert (hm_top : m_top = PA1 \/ m_top = FA1).
  { destruct m_top; cbn [modeMatches] in hm_top_match; try discriminate; [left | right]; reflexivity. }
  set (mid_all := p_w ++ s_full ++ ds_core).
  set (v_mid := v_p ++ v_s ++ v_ds).
  set (g_mid := gp + g_s + g_ds).
  assert (hg_mid : 6 <= g_mid) by (unfold g_mid; lia).
  assert (hS_mid : Scan FA1 S2 b_head mid_all m_top S2 b_top v_mid g_mid).
  { pose proof (Scan_append (Scan_append hS_p hS_s) hS_ds) as h123.
    unfold mid_all, v_mid, g_mid. rewrite <- !app_assoc in h123. exact h123. }
  pose proof (Scan_KQ_zW hS_ds hD_core) as hzW_vds.
  pose proof (z13_pos v_s) as hz13_vs_pos.
  pose proof (qpow2_pos m) as hqm_pos.
  assert (h_tail : (zW (v_s ++ v_ds) <= (1377 # 4096) + (1 # 1024) * qpow2 m)%Q).
  { rewrite zW_append.
    pose proof (mul_le_of_nonneg_l (Qlt_le_weak _ _ hz13_vs_pos) hzW_vds) as hm_vds.
    assert (h_lin : (z13 v_s * (kqA m_ds s_ds * qpow2 m + kqC m_ds s_ds) ==
      (z13 v_s * kqA m_ds s_ds) * qpow2 m + z13 v_s * kqC m_ds s_ds)%Q) by ring.
    assert (hm_A : ((z13 v_s * kqA m_ds s_ds) * qpow2 m <= (1 # 1024) * qpow2 m)%Q) by nra.
    assert (h_rhs : (z13 v_s * (kqA m_ds s_ds * qpow2 m + kqC m_ds s_ds) <=
      (1 # 1024) * qpow2 m + (1 # 4096))%Q).
    { rewrite h_lin. lra. }
    pose proof (Qle_trans _ _ _ hm_vds h_rhs) as hm_vds2.
    lra. }
  assert (hzW_vmid : (zW v_mid <= 43821 # 512)%Q).
  { unfold v_mid. rewrite zW_append.
    pose proof (mul_le_of_nonneg_l (Qlt_le_weak _ _ hz13_vp_pos) h_tail) as hm_tail.
    assert (h_dist : (z13 v_p * ((1377 # 4096) + (1 # 1024) * qpow2 m) ==
      (1377 # 4096) * z13 v_p + (1 # 1024) * (z13 v_p * qpow2 m))%Q) by ring.
    assert (h_rhs2 : (z13 v_p * ((1377 # 4096) + (1 # 1024) * qpow2 m) <=
      (1377 # 512) + 2)%Q).
    { rewrite h_dist. lra. }
    pose proof (Qle_trans _ _ _ hm_tail h_rhs2) as hm_tail2.
    lra. }
  assert (hz13_vmid : (z13 v_mid * qpow2 g_mid == 1024)%Q).
  { pose proof (Scan_z13 hS_mid) as h.
    assert (hpsi_top : psi m_top = 4%Q) by (destruct hm_top as [-> | ->]; reflexivity).
    rewrite hpsi_top in h. cbn [psi] in h.
    assert (hs_z13 : (z13 s_full == 1 # 2)%Q).
    { pose proof (checkZ13Pow2_sound s_full 0 1%N 2%N ltac:(vm_compute; reflexivity)) as hs.
      change (qpow2 0) with 1%Q in hs. norm_qN. lra. }
    assert (hmid_z13 : (z13 mid_all == 1024)%Q).
    { unfold mid_all. rewrite !z13_append, hs_z13, hz13_ds. nra. }
    rewrite hmid_z13 in h. nra. }
  pose proof (Scan_top hm_top b_top hb_top) as hS_top.
  destruct (bound_b_end_zDg hm_top hb_top hg_mid hS_mid hz13_vmid hzW_vmid)
    as [A_core' [ds_core' [hD_core' hD_end]]].
  set (body := head_w ++ mid_all ++ top_body).
  set (v_body := v_head ++ v_mid ++ v_top).
  set (da := bot_w ++ ds_core' ++ top_base).
  set (u' := V :: (v_body ++ V :: da)).
  assert (h_u_eq : head_w ++ p_w ++ s_full ++ ds_core ++ top_base = body ++ [Q]).
  { assert (ht : top_body ++ [Q] = top_base) by reflexivity.
    unfold body, mid_all. rewrite <- ht. rewrite !app_assoc. reflexivity. }
  assert (hS_body : Scan PA1 S2 3%N body PA1 S2 (64 * (b_top - 2) + 41)%N v_body (0 + g_mid + 21)).
  { pose proof (Scan_append (Scan_append Scan_head hS_mid) hS_top) as hSb.
    unfold body, v_body. rewrite <- !app_assoc in hSb. exact hSb. }
  exists u'. split.
  - exists body PA1 (64 * (b_top - 2) + 41)%N v_body.
    exists da (22 + g_mid + 2) (0 + g_mid + 21).
    exact (conj h_u_eq (conj (or_introl eq_refl) (conj hS_body (conj hD_end eq_refl)))).
  - destruct (Scan_FA1_V_emit hS_p eq_refl (ex_intro _ (V :: p_tail) hp_start))
      as [vp_tail hvp_eq].
    set (p_w' := V :: v_mid).
    set (m' := g_mid + 2).
    exists p_w' ds_core' A_core' m'.
    split.
    + assert (hv_h : V :: v_head = head_w ++ [V]) by reflexivity.
      assert (hs_eq : s_full = v_top ++ [V] ++ bot_w) by reflexivity.
      unfold u', v_body, da, p_w'.
      change (V :: (v_head ++ v_mid ++ v_top) ++ V :: bot_w ++ ds_core' ++ top_base)
        with (((V :: v_head) ++ v_mid ++ v_top) ++ ([V] ++ bot_w ++ ds_core' ++ top_base)).
      change (V :: v_mid) with ([V] ++ v_mid).
      rewrite hv_h, hs_eq.
      rewrite <- !app_assoc. reflexivity.
    + split.
      * exists (vp_tail ++ v_s ++ v_ds). unfold p_w', v_mid. rewrite hvp_eq. reflexivity.
      * split; [unfold m'; lia |].
        split; [exact hD_core' |].
        split.
        -- unfold p_w', m'. cbn [z13]. rewrite qpow2_add. change (qpow2 2) with 4%Q. nra.
        -- unfold p_w'. cbn [zW]. lra.
Qed.

Close Scope word_scope.

Lemma nonhalt : ~ halts tm c0.
Proof.
  apply (multistep_nonhalt tm c0 (zCf (zTs u_10 0inf%sym))
           (etrans init_to_u0 (Rounds_exec rounds_0_10))).
  apply (progress_nonhalt_cond tm (list Word) u_10 (fun u => zCf (zTs u 0inf%sym)) Good).
  - intros u hG.
    destruct (Good_step hG) as [u' [hStep hG']].
    exists u'. split; [exact (Step_exec hStep) | exact hG'].
  - exact good_u10.
Qed.
