(* 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LC--- never halts. *)

From Coq Require Import Lia ZifyNat ZifyN PeanoNat Bool String List Lists.Streams NArith ZArith QArith Lqa.
From BusyCoq Require Import Individual62.
Import ListNotations.

Open Scope list_scope.
Open Scope sym_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm := Eval compute in
  (TM_from_str "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LC---").

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
Definition pref_cap : list Sym :=
  [1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0]%sym.

Lemma z00 : 0%sym >> 0inf%sym = 0inf%sym.
Proof. symmetry. apply const_unfold. Qed.

Lemma zKd : K_u *> 0inf%sym = 0inf%sym.
Proof. solve_const0_eq. Qed.

Lemma zKpd : Kp *> 0inf%sym = 0inf%sym.
Proof. solve_const0_eq. Qed.

Inductive Call : Type :=
  | ch
  | ca.

Definition zCs (c : Call) : Q :=
  match c with
  | ch => D
  | ca => C
  end.

Definition zCR (w : side) (c : Call) (r : side) : Q * tape :=
  w <{{zCs c}} ([1]%sym *> r).

Definition zCL (w : side) (r : side) : Q * tape :=
  ([0]%sym *> w) {{A}}> r.

Definition zCf (w : side) : Q * tape :=
  ([0]%sym *> pref_cap *> w) {{A}}> 0inf%sym.

Definition z0f (c : Call) (w1 w2 : side) : Prop :=
  forall r, zCR w1 c r -->+ zCL w2 r.

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

Lemma z0m (ls : list Call) : Seg ls ls [] [].
Proof.
  intros u1 u2 h. exact h.
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

Lemma zS4 {c : Call} {w1 w2 : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c r -->+ zCL (w2 *> u) r) :
    Seg [c] [] w1 w2.
Proof.
  intros u1 u2 h. inversion h; subst.
  exact (Side_cons (fun r => h1 u2 r) (Side_nil _)).
Qed.

Lemma zS2 {c_in c_out : Call} {w1 w2 mid : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c_in r -->+ zCR u c_out (mid *> r))
    (h2 : forall u r, zCL u (mid *> r) -->+ zCL (w2 *> u) r) :
    Seg [c_in] [c_out] w1 w2.
Proof.
  intros u1 u2 h.
  inversion h as [| ? ? ? u_mid ? hc1 hnil]; subst.
  inversion hnil; subst.
  refine (Side_cons (fun r => _) (Side_nil _)).
  exact (ptrans (h1 u1 r) (ptrans (hc1 (mid *> r)) (h2 u2 r))).
Qed.

Lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : list Sym}
    (h1 : forall u r, zCR (w1 *> u) c_in r -->+ zCR u c1 (mid1 *> r))
    (h2 : forall u r, zCL u (mid1 *> r) -->+ zCR u c2 (mid2 *> r))
    (h3 : forall u r, zCL u (mid2 *> r) -->+ zCL (w2 *> u) r) :
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

(* 12 atomic Seg lemmas *)
Lemma seg_ch_V : Seg [ch] [ch; ch] V_u V_u.
Proof.
  eapply (zS5 (mid1 := [1; 0; 1; 1]%sym) (mid2 := [1; 0; 1; 0]%sym));
    intros u r; unfold zCR, zCL, zCs, V_u; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_V : Seg [ca] [ch] V_u Vp.
Proof.
  eapply (zS2 (mid := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zCs, V_u, Vp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_Vp : Seg [ca] [ca; ca] Vp Vp.
Proof.
  eapply (zS5 (mid1 := [0; 1; 1; 1]%sym) (mid2 := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zCs, Vp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_K : Seg [ch] [] K_u Q_u.
Proof.
  apply zS4; intros u r; unfold zCR, zCL, zCs, K_u, Q_u; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ch_Q : Seg [ch] [ch] Q_u K_u.
Proof.
  eapply (zS2 (mid := [1; 1]%sym));
    intros u r; unfold zCR, zCL, zCs, Q_u, K_u; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_VpQ : Seg [ca] [ca] (Vp ++ Q_u) (Kp ++ Vp).
Proof.
  eapply (zS2 (mid := [0; 1; 0; 1; 1; 1]%sym));
    intros u r; unfold zCR, zCL, zCs, Vp, Q_u, Kp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_KpVp : Seg [ca] [] (Kp ++ Vp) (Qp ++ Vp).
Proof.
  apply zS4; intros u r; unfold zCR, zCL, zCs, Kp, Vp, Qp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_QpVp : Seg [ca] [ca; ca] (Qp ++ Vp) (Kp ++ Vp).
Proof.
  eapply (zS5 (mid1 := [0; 1; 1; 1; 1; 1]%sym) (mid2 := [0; 1; 0; 1; 1; 1]%sym));
    intros u r; unfold zCR, zCL, zCs, Qp, Vp, Kp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_Kp : Seg [ca] [] Kp Qp.
Proof.
  apply zS4; intros u r; unfold zCR, zCL, zCs, Kp, Qp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_Qp : Seg [ca] [ca] Qp Kp.
Proof.
  eapply (zS2 (mid := [1; 1]%sym));
    intros u r; unfold zCR, zCL, zCs, Qp, Kp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_KQ : Seg [ca] [] (K_u ++ Q_u) Vp.
Proof.
  apply zS4; intros u r; unfold zCR, zCL, zCs, K_u, Q_u, Vp; cbn [List.app Str_app]; fast_start_progress.
Qed.

Lemma seg_ca_QQ : Seg [ca] [ca] (Q_u ++ Q_u) Vp.
Proof.
  eapply (zS2 (mid := [0; 1; 0; 1]%sym));
    intros u r; unfold zCR, zCL, zCs, Q_u, Vp; cbn [List.app Str_app]; fast_start_progress.
Qed.


(* Turnaround zP0..zP126 *)
Definition tr1 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr2 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr3 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr4 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr5 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr6 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr7 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr8 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr9 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr10 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr11 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr12 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr13 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr14 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr15 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr16 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr17 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr18 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr19 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr20 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr21 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr22 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr23 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr24 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr25 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr26 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr27 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr28 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr29 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr30 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr31 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr32 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr33 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr34 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr35 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr36 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr37 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr38 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr39 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr40 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr41 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr42 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr43 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr44 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr45 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr46 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr47 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr48 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr49 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr50 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr51 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr52 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr53 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr54 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr55 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr56 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr57 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr58 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr59 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr60 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr61 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr62 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr63 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr64 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1]%sym.
Definition tr65 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr66 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr67 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr68 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr69 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr70 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr71 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr72 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr73 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr74 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr75 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr76 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr77 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr78 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr79 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr80 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr81 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr82 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr83 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr84 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr85 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr86 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr87 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr88 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr89 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr90 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr91 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr92 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr93 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr94 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr95 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr96 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1]%sym.
Definition tr97 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr98 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr99 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr100 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr101 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr102 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr103 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr104 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr105 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr106 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr107 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr108 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr109 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr110 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr111 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr112 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr113 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr114 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr115 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr116 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr117 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr118 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr119 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr120 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr121 : list Sym := [0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr122 : list Sym := [0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr123 : list Sym := [0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr124 : list Sym := [0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr125 : list Sym := [0; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.
Definition tr126 : list Sym := [0; 1; 0; 0; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1]%sym.

Lemma zP0 (w : side) : zCf w -->+ zCR w ca (tr1 *> 0inf%sym).
Proof. unfold zCf, zCR, zCs, pref_cap, tr1. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP1 (w : side) : zCL w (tr1 *> 0inf%sym) -->+ zCR w ca (tr2 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr1, tr2. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP2 (w : side) : zCL w (tr2 *> 0inf%sym) -->+ zCR w ca (tr3 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr2, tr3. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP3 (w : side) : zCL w (tr3 *> 0inf%sym) -->+ zCR w ca (tr4 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr3, tr4. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP4 (w : side) : zCL w (tr4 *> 0inf%sym) -->+ zCR w ca (tr5 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr4, tr5. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP5 (w : side) : zCL w (tr5 *> 0inf%sym) -->+ zCR w ca (tr6 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr5, tr6. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP6 (w : side) : zCL w (tr6 *> 0inf%sym) -->+ zCR w ca (tr7 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr6, tr7. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP7 (w : side) : zCL w (tr7 *> 0inf%sym) -->+ zCR w ca (tr8 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr7, tr8. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP8 (w : side) : zCL w (tr8 *> 0inf%sym) -->+ zCR w ca (tr9 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr8, tr9. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP9 (w : side) : zCL w (tr9 *> 0inf%sym) -->+ zCR w ca (tr10 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr9, tr10. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP10 (w : side) : zCL w (tr10 *> 0inf%sym) -->+ zCR w ca (tr11 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr10, tr11. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP11 (w : side) : zCL w (tr11 *> 0inf%sym) -->+ zCR w ca (tr12 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr11, tr12. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP12 (w : side) : zCL w (tr12 *> 0inf%sym) -->+ zCR w ca (tr13 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr12, tr13. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP13 (w : side) : zCL w (tr13 *> 0inf%sym) -->+ zCR w ca (tr14 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr13, tr14. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP14 (w : side) : zCL w (tr14 *> 0inf%sym) -->+ zCR w ca (tr15 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr14, tr15. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP15 (w : side) : zCL w (tr15 *> 0inf%sym) -->+ zCR w ca (tr16 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr15, tr16. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP16 (w : side) : zCL w (tr16 *> 0inf%sym) -->+ zCR w ca (tr17 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr16, tr17. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP17 (w : side) : zCL w (tr17 *> 0inf%sym) -->+ zCR w ca (tr18 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr17, tr18. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP18 (w : side) : zCL w (tr18 *> 0inf%sym) -->+ zCR w ca (tr19 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr18, tr19. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP19 (w : side) : zCL w (tr19 *> 0inf%sym) -->+ zCR w ca (tr20 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr19, tr20. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP20 (w : side) : zCL w (tr20 *> 0inf%sym) -->+ zCR w ca (tr21 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr20, tr21. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP21 (w : side) : zCL w (tr21 *> 0inf%sym) -->+ zCR w ca (tr22 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr21, tr22. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP22 (w : side) : zCL w (tr22 *> 0inf%sym) -->+ zCR w ca (tr23 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr22, tr23. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP23 (w : side) : zCL w (tr23 *> 0inf%sym) -->+ zCR w ca (tr24 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr23, tr24. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP24 (w : side) : zCL w (tr24 *> 0inf%sym) -->+ zCR w ca (tr25 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr24, tr25. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP25 (w : side) : zCL w (tr25 *> 0inf%sym) -->+ zCR w ca (tr26 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr25, tr26. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP26 (w : side) : zCL w (tr26 *> 0inf%sym) -->+ zCR w ca (tr27 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr26, tr27. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP27 (w : side) : zCL w (tr27 *> 0inf%sym) -->+ zCR w ca (tr28 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr27, tr28. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP28 (w : side) : zCL w (tr28 *> 0inf%sym) -->+ zCR w ca (tr29 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr28, tr29. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP29 (w : side) : zCL w (tr29 *> 0inf%sym) -->+ zCR w ca (tr30 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr29, tr30. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP30 (w : side) : zCL w (tr30 *> 0inf%sym) -->+ zCR w ca (tr31 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr30, tr31. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP31 (w : side) : zCL w (tr31 *> 0inf%sym) -->+ zCR w ca (tr32 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr31, tr32. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP32 (w : side) : zCL w (tr32 *> 0inf%sym) -->+ zCR w ca (tr33 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr32, tr33. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP33 (w : side) : zCL w (tr33 *> 0inf%sym) -->+ zCR w ca (tr34 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr33, tr34. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP34 (w : side) : zCL w (tr34 *> 0inf%sym) -->+ zCR w ca (tr35 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr34, tr35. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP35 (w : side) : zCL w (tr35 *> 0inf%sym) -->+ zCR w ca (tr36 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr35, tr36. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP36 (w : side) : zCL w (tr36 *> 0inf%sym) -->+ zCR w ca (tr37 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr36, tr37. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP37 (w : side) : zCL w (tr37 *> 0inf%sym) -->+ zCR w ca (tr38 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr37, tr38. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP38 (w : side) : zCL w (tr38 *> 0inf%sym) -->+ zCR w ca (tr39 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr38, tr39. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP39 (w : side) : zCL w (tr39 *> 0inf%sym) -->+ zCR w ca (tr40 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr39, tr40. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP40 (w : side) : zCL w (tr40 *> 0inf%sym) -->+ zCR w ca (tr41 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr40, tr41. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP41 (w : side) : zCL w (tr41 *> 0inf%sym) -->+ zCR w ca (tr42 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr41, tr42. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP42 (w : side) : zCL w (tr42 *> 0inf%sym) -->+ zCR w ca (tr43 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr42, tr43. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP43 (w : side) : zCL w (tr43 *> 0inf%sym) -->+ zCR w ca (tr44 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr43, tr44. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP44 (w : side) : zCL w (tr44 *> 0inf%sym) -->+ zCR w ca (tr45 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr44, tr45. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP45 (w : side) : zCL w (tr45 *> 0inf%sym) -->+ zCR w ca (tr46 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr45, tr46. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP46 (w : side) : zCL w (tr46 *> 0inf%sym) -->+ zCR w ca (tr47 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr46, tr47. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP47 (w : side) : zCL w (tr47 *> 0inf%sym) -->+ zCR w ca (tr48 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr47, tr48. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP48 (w : side) : zCL w (tr48 *> 0inf%sym) -->+ zCR w ca (tr49 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr48, tr49. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP49 (w : side) : zCL w (tr49 *> 0inf%sym) -->+ zCR w ca (tr50 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr49, tr50. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP50 (w : side) : zCL w (tr50 *> 0inf%sym) -->+ zCR w ca (tr51 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr50, tr51. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP51 (w : side) : zCL w (tr51 *> 0inf%sym) -->+ zCR w ca (tr52 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr51, tr52. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP52 (w : side) : zCL w (tr52 *> 0inf%sym) -->+ zCR w ca (tr53 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr52, tr53. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP53 (w : side) : zCL w (tr53 *> 0inf%sym) -->+ zCR w ca (tr54 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr53, tr54. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP54 (w : side) : zCL w (tr54 *> 0inf%sym) -->+ zCR w ca (tr55 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr54, tr55. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP55 (w : side) : zCL w (tr55 *> 0inf%sym) -->+ zCR w ca (tr56 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr55, tr56. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP56 (w : side) : zCL w (tr56 *> 0inf%sym) -->+ zCR w ca (tr57 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr56, tr57. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP57 (w : side) : zCL w (tr57 *> 0inf%sym) -->+ zCR w ca (tr58 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr57, tr58. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP58 (w : side) : zCL w (tr58 *> 0inf%sym) -->+ zCR w ca (tr59 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr58, tr59. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP59 (w : side) : zCL w (tr59 *> 0inf%sym) -->+ zCR w ca (tr60 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr59, tr60. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP60 (w : side) : zCL w (tr60 *> 0inf%sym) -->+ zCR w ca (tr61 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr60, tr61. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP61 (w : side) : zCL w (tr61 *> 0inf%sym) -->+ zCR w ca (tr62 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr61, tr62. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP62 (w : side) : zCL w (tr62 *> 0inf%sym) -->+ zCR w ca (tr63 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr62, tr63. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP63 (w : side) : zCL w (tr63 *> 0inf%sym) -->+ zCR w ca (tr64 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr63, tr64. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP64 (w : side) : zCL w (tr64 *> 0inf%sym) -->+ zCR w ca (tr65 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr64, tr65. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP65 (w : side) : zCL w (tr65 *> 0inf%sym) -->+ zCR w ca (tr66 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr65, tr66. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP66 (w : side) : zCL w (tr66 *> 0inf%sym) -->+ zCR w ca (tr67 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr66, tr67. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP67 (w : side) : zCL w (tr67 *> 0inf%sym) -->+ zCR w ca (tr68 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr67, tr68. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP68 (w : side) : zCL w (tr68 *> 0inf%sym) -->+ zCR w ca (tr69 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr68, tr69. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP69 (w : side) : zCL w (tr69 *> 0inf%sym) -->+ zCR w ca (tr70 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr69, tr70. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP70 (w : side) : zCL w (tr70 *> 0inf%sym) -->+ zCR w ca (tr71 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr70, tr71. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP71 (w : side) : zCL w (tr71 *> 0inf%sym) -->+ zCR w ca (tr72 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr71, tr72. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP72 (w : side) : zCL w (tr72 *> 0inf%sym) -->+ zCR w ca (tr73 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr72, tr73. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP73 (w : side) : zCL w (tr73 *> 0inf%sym) -->+ zCR w ca (tr74 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr73, tr74. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP74 (w : side) : zCL w (tr74 *> 0inf%sym) -->+ zCR w ca (tr75 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr74, tr75. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP75 (w : side) : zCL w (tr75 *> 0inf%sym) -->+ zCR w ca (tr76 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr75, tr76. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP76 (w : side) : zCL w (tr76 *> 0inf%sym) -->+ zCR w ca (tr77 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr76, tr77. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP77 (w : side) : zCL w (tr77 *> 0inf%sym) -->+ zCR w ca (tr78 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr77, tr78. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP78 (w : side) : zCL w (tr78 *> 0inf%sym) -->+ zCR w ca (tr79 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr78, tr79. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP79 (w : side) : zCL w (tr79 *> 0inf%sym) -->+ zCR w ca (tr80 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr79, tr80. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP80 (w : side) : zCL w (tr80 *> 0inf%sym) -->+ zCR w ca (tr81 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr80, tr81. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP81 (w : side) : zCL w (tr81 *> 0inf%sym) -->+ zCR w ca (tr82 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr81, tr82. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP82 (w : side) : zCL w (tr82 *> 0inf%sym) -->+ zCR w ca (tr83 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr82, tr83. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP83 (w : side) : zCL w (tr83 *> 0inf%sym) -->+ zCR w ca (tr84 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr83, tr84. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP84 (w : side) : zCL w (tr84 *> 0inf%sym) -->+ zCR w ca (tr85 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr84, tr85. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP85 (w : side) : zCL w (tr85 *> 0inf%sym) -->+ zCR w ca (tr86 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr85, tr86. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP86 (w : side) : zCL w (tr86 *> 0inf%sym) -->+ zCR w ca (tr87 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr86, tr87. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP87 (w : side) : zCL w (tr87 *> 0inf%sym) -->+ zCR w ca (tr88 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr87, tr88. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP88 (w : side) : zCL w (tr88 *> 0inf%sym) -->+ zCR w ca (tr89 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr88, tr89. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP89 (w : side) : zCL w (tr89 *> 0inf%sym) -->+ zCR w ca (tr90 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr89, tr90. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP90 (w : side) : zCL w (tr90 *> 0inf%sym) -->+ zCR w ca (tr91 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr90, tr91. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP91 (w : side) : zCL w (tr91 *> 0inf%sym) -->+ zCR w ca (tr92 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr91, tr92. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP92 (w : side) : zCL w (tr92 *> 0inf%sym) -->+ zCR w ca (tr93 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr92, tr93. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP93 (w : side) : zCL w (tr93 *> 0inf%sym) -->+ zCR w ca (tr94 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr93, tr94. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP94 (w : side) : zCL w (tr94 *> 0inf%sym) -->+ zCR w ca (tr95 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr94, tr95. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP95 (w : side) : zCL w (tr95 *> 0inf%sym) -->+ zCR w ca (tr96 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr95, tr96. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP96 (w : side) : zCL w (tr96 *> 0inf%sym) -->+ zCR w ca (tr97 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr96, tr97. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP97 (w : side) : zCL w (tr97 *> 0inf%sym) -->+ zCR w ca (tr98 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr97, tr98. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP98 (w : side) : zCL w (tr98 *> 0inf%sym) -->+ zCR w ca (tr99 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr98, tr99. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP99 (w : side) : zCL w (tr99 *> 0inf%sym) -->+ zCR w ca (tr100 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr99, tr100. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP100 (w : side) : zCL w (tr100 *> 0inf%sym) -->+ zCR w ca (tr101 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr100, tr101. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP101 (w : side) : zCL w (tr101 *> 0inf%sym) -->+ zCR w ca (tr102 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr101, tr102. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP102 (w : side) : zCL w (tr102 *> 0inf%sym) -->+ zCR w ca (tr103 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr102, tr103. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP103 (w : side) : zCL w (tr103 *> 0inf%sym) -->+ zCR w ca (tr104 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr103, tr104. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP104 (w : side) : zCL w (tr104 *> 0inf%sym) -->+ zCR w ca (tr105 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr104, tr105. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP105 (w : side) : zCL w (tr105 *> 0inf%sym) -->+ zCR w ca (tr106 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr105, tr106. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP106 (w : side) : zCL w (tr106 *> 0inf%sym) -->+ zCR w ca (tr107 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr106, tr107. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP107 (w : side) : zCL w (tr107 *> 0inf%sym) -->+ zCR w ca (tr108 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr107, tr108. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP108 (w : side) : zCL w (tr108 *> 0inf%sym) -->+ zCR w ca (tr109 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr108, tr109. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP109 (w : side) : zCL w (tr109 *> 0inf%sym) -->+ zCR w ca (tr110 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr109, tr110. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP110 (w : side) : zCL w (tr110 *> 0inf%sym) -->+ zCR w ca (tr111 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr110, tr111. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP111 (w : side) : zCL w (tr111 *> 0inf%sym) -->+ zCR w ca (tr112 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr111, tr112. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP112 (w : side) : zCL w (tr112 *> 0inf%sym) -->+ zCR w ca (tr113 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr112, tr113. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP113 (w : side) : zCL w (tr113 *> 0inf%sym) -->+ zCR w ca (tr114 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr113, tr114. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP114 (w : side) : zCL w (tr114 *> 0inf%sym) -->+ zCR w ca (tr115 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr114, tr115. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP115 (w : side) : zCL w (tr115 *> 0inf%sym) -->+ zCR w ca (tr116 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr115, tr116. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP116 (w : side) : zCL w (tr116 *> 0inf%sym) -->+ zCR w ca (tr117 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr116, tr117. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP117 (w : side) : zCL w (tr117 *> 0inf%sym) -->+ zCR w ca (tr118 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr117, tr118. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP118 (w : side) : zCL w (tr118 *> 0inf%sym) -->+ zCR w ca (tr119 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr118, tr119. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP119 (w : side) : zCL w (tr119 *> 0inf%sym) -->+ zCR w ca (tr120 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr119, tr120. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP120 (w : side) : zCL w (tr120 *> 0inf%sym) -->+ zCR w ca (tr121 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr120, tr121. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP121 (w : side) : zCL w (tr121 *> 0inf%sym) -->+ zCR w ca (tr122 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr121, tr122. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP122 (w : side) : zCL w (tr122 *> 0inf%sym) -->+ zCR w ca (tr123 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr122, tr123. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP123 (w : side) : zCL w (tr123 *> 0inf%sym) -->+ zCR w ca (tr124 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr123, tr124. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP124 (w : side) : zCL w (tr124 *> 0inf%sym) -->+ zCR w ca (tr125 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr124, tr125. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP125 (w : side) : zCL w (tr125 *> 0inf%sym) -->+ zCR w ca (tr126 *> 0inf%sym).
Proof. unfold zCL, zCR, zCs, tr125, tr126. cbn [List.app Str_app]. fast_start_progress. Qed.

Lemma zP126 (w : side) : zCL w (tr126 *> 0inf%sym) -->+ zCf ([1; 1; 0]%sym *> w).
Proof. unfold zCL, zCf, tr126, pref_cap. cbn [List.app Str_app]. fast_start_progress. Qed.

(* Section 2: Words, Shift Identity, zDg, Parse, Scan, Step *)

Inductive Word : Type :=
  | V
  | K
  | Q_w.

Declare Scope word_scope.
Notation "'Q'" := Q_w : word_scope.
Delimit Scope word_scope with word.

Definition word_eqb (x y : Word) : bool :=
  match x, y with
  | V, V => true
  | K, K => true
  | Q_w, Q_w => true
  | _, _ => false
  end.

Lemma word_eqb_eq (x y : Word) : word_eqb x y = true <-> x = y.
Proof. destruct x, y; cbn; split; intro H; congruence. Qed.

Fixpoint list_word_eqb (u v : list Word) : bool :=
  match u, v with
  | [], [] => true
  | x :: u', y :: v' => word_eqb x y && list_word_eqb u' v'
  | _, _ => false
  end.

Lemma list_word_eqb_eq (u v : list Word) : list_word_eqb u v = true <-> u = v.
Proof.
  revert v. induction u as [| x u' ih]; intros [| y v']; cbn.
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff, word_eqb_eq, ih.
    split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Definition dVal (w : Word) : N :=
  match w with
  | V => 0%N
  | K => 0%N
  | Q_w => 1%N
  end.

Lemma dVal_le_one (w : Word) : (dVal w <= 1)%N.
Proof. destruct w; cbn; lia. Qed.

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

Lemma zWt_cons (w : Word) (u : list Word) : zWt (w :: u) = zWt [w] ++ zWt u.
Proof. destruct w; cbn; rewrite ?app_nil_r; reflexivity. Qed.

Lemma zWt'_cons (w : Word) (u : list Word) : zWt' (w :: u) = zWt' [w] ++ zWt' u.
Proof. destruct w; cbn; rewrite ?app_nil_r; reflexivity. Qed.

Lemma zWt_append (u v : list Word) : zWt (u ++ v) = zWt u ++ zWt v.
Proof.
  induction u as [| a u ih]; [reflexivity |].
  destruct a; cbn [List.app zWt]; rewrite ih, app_assoc; reflexivity.
Qed.

Lemma zWt'_append (u v : list Word) : zWt' (u ++ v) = zWt' u ++ zWt' v.
Proof.
  induction u as [| a u ih]; [reflexivity |].
  destruct a; cbn [List.app zWt']; rewrite ih, app_assoc; reflexivity.
Qed.

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

Lemma zTs'_append (u v : list Word) (r : side) : zTs' (u ++ v) r = zTs' u (zTs' v r).
Proof.
  induction u as [| a u ih]; [reflexivity |].
  destruct a; cbn [List.app zTs']; rewrite ih; reflexivity.
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

Lemma zTs_rep_K (n : nat) : zTs (repeat K n) 0inf%sym = 0inf%sym.
Proof.
  induction n as [| n ih]; [reflexivity |].
  cbn [repeat zTs]. rewrite ih, zKd. reflexivity.
Qed.

Lemma zPp (n : nat) : 0 < 2 ^ n.
Proof.
  assert (H : 2 ^ n <> 0) by (apply Nat.pow_nonzero; lia).
  lia.
Qed.

Lemma zPp_N (n : N) : (0 < 2 ^ n)%N.
Proof.
  assert (H : (2 ^ n <> 0)%N) by (apply N.pow_nonzero; lia).
  lia.
Qed.

Lemma zPow1 (n : nat) : 2 ^ (1 + n) = 2 ^ n + 2 ^ n.
Proof. cbn [Nat.add Nat.pow]. lia. Qed.

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

Lemma zDg_lt {A : N} {H : nat} {u : list Word} (h : zDg A H u) :
    (A < 2 ^ (N.of_nat H))%N.
Proof.
  induction h as [| A H u _ ih | A H u _ ih].
  - cbn. lia.
  - rewrite zPow1_N. lia.
  - rewrite zPow1_N. lia.
Qed.

Lemma zDg_len {A : N} {H : nat} {u : list Word} (h : zDg A H u) :
    length u = H.
Proof.
  induction h as [| A H u _ ih | A H u _ ih]; cbn; lia.
Qed.

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

Inductive Parse : N -> list Word -> N -> nat -> Prop :=
  | Parse_nil (a : N) : Parse a [] a 0
  | Parse_T {a a' : N} {g : nat} {u : list Word} :
      Parse (1 + a * 2)%N u a' g -> Parse a (V :: u) a' g
  | Parse_VK {a a' : N} {g : nat} {u : list Word} :
      Parse a u a' g -> Parse a (V :: K :: u) a' g
  | Parse_D {a q1 a' : N} {g : nat} {w0 : Word} {u : list Word} :
      w0 <> V -> (a + dVal w0 = q1 * 2)%N ->
      Parse q1 u a' g -> Parse a (w0 :: u) a' g
  | Parse_P {a q2 a' : N} {g : nat} {w0 w1 : Word} {u : list Word} :
      w0 <> V -> w1 <> V ->
      ((a + dVal w0) / 2 + dVal w1 = 1 + q2 * 2)%N ->
      Parse q2 u a' g -> Parse a (w0 :: w1 :: u) a' (1 + g).

Inductive Scan : N -> N -> list Word -> N -> N -> list Word -> nat -> Prop :=
  | Scan_nil (a b : N) :
      (1 <= b)%N -> Scan a b [] a b [] 0
  | Scan_T {a b a' b' : N} {g : nat} {u v : list Word} :
      (2 <= b)%N ->
      Scan (1 + a * 2)%N ((b - 1) * 2)%N u a' b' v g ->
      Scan a b (V :: u) a' b' (V :: v) g
  | Scan_VK0 {a k a' b' : N} {g : nat} {u v : list Word} :
      (1 <= k)%N ->
      Scan a (1 + (k - 1) * 2)%N u a' b' v g ->
      Scan a (k * 2)%N (V :: K :: u) a' b' (K :: V :: v) g
  | Scan_VK1 {a k a' b' : N} {g : nat} {u v : list Word} :
      (1 <= k)%N ->
      Scan a (1 + (k - 1) * 2)%N u a' b' v g ->
      Scan a (1 + k * 2)%N (V :: K :: u) a' b' (Q_w :: V :: v) g
  | Scan_D {a b q1 a' b' : N} {g : nat} {w0 : Word} {u v : list Word} :
      w0 <> V -> (a + dVal w0 = q1 * 2)%N -> (2 <= b)%N ->
      Scan q1 (b / 2)%N u a' b' v g ->
      Scan a b (w0 :: u) a' b' ((if (b mod 2 =? 1)%N then Q_w else K) :: v) g
  | Scan_P0 {a b q1 q2 a' b' : N} {g : nat} {w0 w1 : Word} {u v : list Word} :
      w0 <> V -> w1 <> V ->
      (a + dVal w0 = q1 * 2)%N -> (q1 + dVal w1 = 1 + q2 * 2)%N -> (2 <= b)%N ->
      Scan q2 ((b - 1) * 2)%N u a' b' v g ->
      Scan a b (w0 :: w1 :: u) a' b' (V :: v) (1 + g)
  | Scan_P1 {a b q1 q2 a' b' : N} {g : nat} {w0 w1 : Word} {u v : list Word} :
      w0 <> V -> w1 <> V ->
      (a + dVal w0 = 1 + q1 * 2)%N -> (q1 + dVal w1 = 1 + q2 * 2)%N -> (2 <= b)%N ->
      Scan q2 (1 + (b - 1) * 2)%N u a' b' v g ->
      Scan a b (w0 :: w1 :: u) a' b' (V :: v) (1 + g).

Definition Step (u u' : list Word) : Prop :=
  exists (n : nat) (b' : N) (v da : list Word) (H g : nat),
    Scan 0%N 126%N (u ++ repeat K n) 0%N b' v g /\
    zDg b' H da /\
    u' = V :: (v ++ da).

Inductive Rounds : list Word -> list Word -> Prop :=
  | Rounds_refl (u : list Word) : Rounds u u
  | Rounds_next {u v w : list Word} : Step u v -> Rounds v w -> Rounds u w.

(* Power Seg lemmas and Seg_of_Scan *)

Lemma seg_ch_V_pow (n : nat) : Seg ([ch] ^^ n) ([ch] ^^ (n * 2)) V_u V_u.
Proof.
  induction n as [| n ih].
  - exact (z0l V_u).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite lpow_S, lpow_add.
    exact (zSg seg_ch_V ih).
Qed.

Lemma seg_ca_Vp_pow (n : nat) : Seg ([ca] ^^ n) ([ca] ^^ (n * 2)) Vp Vp.
Proof.
  induction n as [| n ih].
  - exact (z0l Vp).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite lpow_S, lpow_add.
    exact (zSg seg_ca_Vp ih).
Qed.

Lemma seg_double {c : Call} {w : list Sym} (hw : Seg [c; c] [c] w w) (n : nat) :
    Seg ([c] ^^ (n * 2)) ([c] ^^ n) w w.
Proof.
  induction n as [| n ih].
  - exact (z0l w).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite lpow_add, lpow_S.
    exact (zSg hw ih).
Qed.

Lemma seg_ch_K_even (n : nat) : Seg ([ch] ^^ (n * 2)) ([ch] ^^ n) K_u K_u.
Proof. exact (seg_double (zSg seg_ch_K seg_ch_Q) n). Qed.

Lemma seg_ch_Q_even (n : nat) : Seg ([ch] ^^ (n * 2)) ([ch] ^^ n) Q_u Q_u.
Proof. exact (seg_double (zSg seg_ch_Q seg_ch_K) n). Qed.

Lemma seg_ch_K_odd (n : nat) : Seg ([ch] ^^ (1 + n * 2)) ([ch] ^^ n) K_u Q_u.
Proof.
  replace (1 + n * 2) with (n * 2 + 1) by lia.
  rewrite lpow_add, lpow_1.
  pose proof (zSg (seg_ch_K_even n) seg_ch_K) as h.
  rewrite app_nil_r in h. exact h.
Qed.

Lemma seg_ch_Q_odd (n : nat) : Seg ([ch] ^^ (1 + n * 2)) ([ch] ^^ (1 + n)) Q_u K_u.
Proof.
  rewrite lpow_1_add.
  exact (zSg seg_ch_Q (seg_ch_K_even n)).
Qed.

Lemma seg_ch_d_even {w0 : Word} {a q1 : N}
    (hw0 : w0 <> V) (hq1 : (a + dVal w0 = q1 * 2)%N) :
    Seg ([ch] ^^ (N.to_nat a)) ([ch] ^^ (N.to_nat q1)) (zWt [w0]) K_u.
Proof.
  destruct w0.
  - contradiction.
  - cbn [dVal] in hq1.
    replace (N.to_nat a) with (N.to_nat q1 * 2) by lia.
    cbn [zWt]. rewrite app_nil_r. exact (seg_ch_K_even (N.to_nat q1)).
  - cbn [dVal] in hq1.
    destruct (N.eq_dec q1 0) as [-> | hq1_nz].
    + lia.
    + set (m := N.to_nat q1 - 1).
      replace (N.to_nat a) with (1 + m * 2) by lia.
      replace (N.to_nat q1) with (1 + m) by lia.
      cbn [zWt]. rewrite app_nil_r. exact (seg_ch_Q_odd m).
Qed.

Lemma seg_ch_d_odd {w0 : Word} {a q1 : N}
    (hw0 : w0 <> V) (hq1 : (a + dVal w0 = 1 + q1 * 2)%N) :
    Seg ([ch] ^^ (N.to_nat a)) ([ch] ^^ (N.to_nat q1)) (zWt [w0]) Q_u.
Proof.
  destruct w0.
  - contradiction.
  - cbn [dVal] in hq1.
    replace (N.to_nat a) with (1 + N.to_nat q1 * 2) by lia.
    cbn [zWt]. rewrite app_nil_r. exact (seg_ch_K_odd (N.to_nat q1)).
  - cbn [dVal] in hq1.
    replace (N.to_nat a) with (N.to_nat q1 * 2) by lia.
    cbn [zWt]. rewrite app_nil_r. exact (seg_ch_Q_even (N.to_nat q1)).
Qed.

Lemma seg_ca_Kp_even (n : nat) : Seg ([ca] ^^ (n * 2)) ([ca] ^^ n) Kp Kp.
Proof. exact (seg_double (zSg seg_ca_Kp seg_ca_Qp) n). Qed.

Lemma seg_ca_Kp_odd (n : nat) : Seg ([ca] ^^ (1 + n * 2)) ([ca] ^^ n) Kp Qp.
Proof.
  replace (1 + n * 2) with (n * 2 + 1) by lia.
  rewrite lpow_add, lpow_1.
  pose proof (zSg (seg_ca_Kp_even n) seg_ca_Kp) as h.
  rewrite app_nil_r in h. exact h.
Qed.

Lemma seg_ca_KpVp_even (n : nat) :
    Seg ([ca] ^^ (n * 2)) ([ca] ^^ (n * 2)) (Kp ++ Vp) (Kp ++ Vp).
Proof.
  induction n as [| n ih].
  - exact (z0l (Kp ++ Vp)).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite lpow_add.
    exact (zSg (zSg seg_ca_KpVp seg_ca_QpVp) ih).
Qed.

Lemma Side_ca_default {b' : N} {H : nat} {da : list Word} (h : zDg b' H da) :
    Side ([ca] ^^ (N.to_nat b')) 0inf%sym (zTs' da 0inf%sym).
Proof.
  induction h as [| A H u _ ih | A H u _ ih].
  - exact (Side_nil 0inf%sym).
  - replace (N.to_nat (A * 2)%N) with (N.to_nat A * 2) by lia.
    pose proof (zSc (seg_ca_Kp_even (N.to_nat A)) ih) as hS.
    rewrite zKpd in hS. cbn [zTs']. exact hS.
  - replace (N.to_nat (1 + A * 2)%N) with (1 + N.to_nat A * 2) by lia.
    pose proof (zSc (seg_ca_Kp_odd (N.to_nat A)) ih) as hS.
    rewrite zKpd in hS. cbn [zTs']. exact hS.
Qed.

Lemma seg_Scan_T (a b : N) (hb : (2 <= b)%N) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat b))
        ([ch] ^^ (N.to_nat (1 + a * 2)%N) ++ [ca] ^^ (N.to_nat ((b - 1) * 2)%N)) V_u Vp.
Proof.
  replace (N.to_nat b) with (1 + (N.to_nat b - 1)) by lia.
  rewrite lpow_1_add, app_assoc.
  replace (N.to_nat (1 + a * 2)%N) with (N.to_nat a * 2 + 1) by lia.
  rewrite lpow_add, lpow_1.
  replace (N.to_nat ((b - 1) * 2)%N) with ((N.to_nat b - 1) * 2) by lia.
  exact (zSg (zSg (seg_ch_V_pow (N.to_nat a)) seg_ca_V) (seg_ca_Vp_pow (N.to_nat b - 1))).
Qed.

Lemma seg_Scan_VK_base (a : N) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca]) ([ch] ^^ (N.to_nat a)) (V_u ++ K_u) (Vp ++ Q_u).
Proof.
  assert (hV : Seg ([ch] ^^ (N.to_nat a) ++ [ca]) ([ch] ^^ (1 + N.to_nat a * 2)) V_u Vp).
  { replace (1 + N.to_nat a * 2) with (N.to_nat a * 2 + 1) by lia.
    rewrite lpow_add, lpow_1.
    exact (zSg (seg_ch_V_pow (N.to_nat a)) seg_ca_V). }
  exact (zS0 hV (seg_ch_K_odd (N.to_nat a))).
Qed.

Lemma seg_Scan_VK0 (a k : N) (hk : (1 <= k)%N) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat (k * 2)%N))
        ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat (1 + (k - 1) * 2)%N))
        (V_u ++ K_u) (Kp ++ Vp).
Proof.
  replace (N.to_nat (k * 2)%N) with (1 + (1 + (N.to_nat k - 1) * 2)) by lia.
  replace (N.to_nat (1 + (k - 1) * 2)%N) with (1 + (N.to_nat k - 1) * 2) by lia.
  rewrite !lpow_1_add, app_assoc.
  exact (zSg (seg_Scan_VK_base a)
             (zSg seg_ca_VpQ (seg_ca_KpVp_even (N.to_nat k - 1)))).
Qed.

Lemma seg_Scan_VK1 (a k : N) (hk : (1 <= k)%N) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat (1 + k * 2)%N))
        ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat (1 + (k - 1) * 2)%N))
        (V_u ++ K_u) (Qp ++ Vp).
Proof.
  replace (N.to_nat (1 + k * 2)%N) with (N.to_nat (k * 2)%N + 1) by lia.
  rewrite lpow_add, lpow_1, app_assoc.
  pose proof (zSg (seg_Scan_VK0 a k hk) seg_ca_KpVp) as h.
  rewrite app_nil_r in h. exact h.
Qed.

Lemma seg_Scan_D {w0 : Word} {a b q1 : N}
    (hw0 : w0 <> V) (hq1 : (a + dVal w0 = q1 * 2)%N) (hb : (2 <= b)%N) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat b))
        ([ch] ^^ (N.to_nat q1) ++ [ca] ^^ (N.to_nat (b / 2)%N))
        (zWt [w0]) (zWt' [if (b mod 2 =? 1)%N then Q_w else K]).
Proof.
  pose proof (seg_ch_d_even hw0 hq1) as h_ch.
  destruct (N.eqb_spec (b mod 2)%N 1%N) as [hb1 | hb0].
  - replace (N.to_nat b) with (1 + N.to_nat (b / 2)%N * 2) by lia.
    cbn [zWt']. rewrite app_nil_r.
    exact (zSg h_ch (seg_ca_Kp_odd (N.to_nat (b / 2)%N))).
  - replace (N.to_nat b) with (N.to_nat (b / 2)%N * 2) by lia.
    cbn [zWt']. rewrite app_nil_r.
    exact (zSg h_ch (seg_ca_Kp_even (N.to_nat (b / 2)%N))).
Qed.

Lemma seg_Scan_P0 {w0 w1 : Word} {a b q1 q2 : N}
    (hw0 : w0 <> V) (hw1 : w1 <> V)
    (hq1 : (a + dVal w0 = q1 * 2)%N) (hq2 : (q1 + dVal w1 = 1 + q2 * 2)%N) (hb : (2 <= b)%N) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat b))
        ([ch] ^^ (N.to_nat q2) ++ [ca] ^^ (N.to_nat ((b - 1) * 2)%N))
        (zWt [w0; w1]) Vp.
Proof.
  pose proof (zS0 (seg_ch_d_even hw0 hq1) (seg_ch_d_odd hw1 hq2)) as h_ch.
  rewrite <- zWt_cons in h_ch.
  replace (N.to_nat b) with (1 + (N.to_nat b - 1)) by lia.
  replace (N.to_nat ((b - 1) * 2)%N) with ((N.to_nat b - 1) * 2) by lia.
  rewrite lpow_1_add.
  pose proof (zSg seg_ca_KQ (seg_ca_Vp_pow (N.to_nat b - 1))) as h_ca.
  cbn [List.app] in h_ca.
  exact (zSg h_ch h_ca).
Qed.

Lemma seg_Scan_P1 {w0 w1 : Word} {a b q1 q2 : N}
    (hw0 : w0 <> V) (hw1 : w1 <> V)
    (hq1 : (a + dVal w0 = 1 + q1 * 2)%N) (hq2 : (q1 + dVal w1 = 1 + q2 * 2)%N) (hb : (2 <= b)%N) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat b))
        ([ch] ^^ (N.to_nat q2) ++ [ca] ^^ (N.to_nat (1 + (b - 1) * 2)%N))
        (zWt [w0; w1]) Vp.
Proof.
  pose proof (zS0 (seg_ch_d_odd hw0 hq1) (seg_ch_d_odd hw1 hq2)) as h_ch.
  rewrite <- zWt_cons in h_ch.
  replace (N.to_nat b) with (1 + (N.to_nat b - 1)) by lia.
  replace (N.to_nat (1 + (b - 1) * 2)%N) with (1 + (N.to_nat b - 1) * 2) by lia.
  rewrite !lpow_1_add.
  exact (zSg h_ch (zSg seg_ca_QQ (seg_ca_Vp_pow (N.to_nat b - 1)))).
Qed.

Lemma Seg_of_Scan {a b a' b' : N} {g : nat} {u v : list Word}
    (h : Scan a b u a' b' v g) :
    Seg ([ch] ^^ (N.to_nat a) ++ [ca] ^^ (N.to_nat b))
        ([ch] ^^ (N.to_nat a') ++ [ca] ^^ (N.to_nat b'))
        (zWt u) (zWt' v).
Proof.
  induction h as
    [ a b _
    | a b a' b' g u v hb _ ih
    | a k a' b' g u v hk _ ih
    | a k a' b' g u v hk _ ih
    | a b q1 a' b' g w0 u v hw0 hq1 hb _ ih
    | a b q1 q2 a' b' g w0 w1 u v hw0 hw1 hq1 hq2 hb _ ih
    | a b q1 q2 a' b' g w0 w1 u v hw0 hw1 hq1 hq2 hb _ ih ].
  - exact (z0m _).
  - exact (zS0 (seg_Scan_T a b hb) ih).
  - pose proof (zS0 (seg_Scan_VK0 a k hk) ih) as h0.
    rewrite <- !app_assoc in h0. exact h0.
  - pose proof (zS0 (seg_Scan_VK1 a k hk) ih) as h0.
    rewrite <- !app_assoc in h0. exact h0.
  - pose proof (zS0 (seg_Scan_D hw0 hq1 hb) ih) as h0.
    rewrite <- zWt_cons, <- zWt'_cons in h0. exact h0.
  - pose proof (zS0 (seg_Scan_P0 hw0 hw1 hq1 hq2 hb) ih) as h0.
    rewrite <- (zWt_append [w0; w1] u) in h0. exact h0.
  - pose proof (zS0 (seg_Scan_P1 hw0 hw1 hq1 hq2 hb) ih) as h0.
    rewrite <- (zWt_append [w0; w1] u) in h0. exact h0.
Qed.


Lemma Side_cons_inv {c : Call} {ls : list Call} {w1 w3 : side}
    (h : Side (c :: ls) w1 w3) :
    exists w2, z0f c w1 w2 /\ Side ls w2 w3.
Proof.
  inversion h; subst. exists w2. split; assumption.
Qed.

Lemma Side_nil_inv {w1 w2 : side} (h : Side [] w1 w2) : w1 = w2.
Proof.
  inversion h; reflexivity.
Qed.

Lemma Side_turnaround {w w' : side} (h : Side ([ca] ^^ 126) w w') :
    zCf w -->+ zCf ([1; 1; 0]%sym *> w').
Proof.
  cbn [lpow List.app] in h.
  destruct (Side_cons_inv h) as [w1 [hc1 h1]].
  destruct (Side_cons_inv h1) as [w2 [hc2 h2]].
  destruct (Side_cons_inv h2) as [w3 [hc3 h3]].
  destruct (Side_cons_inv h3) as [w4 [hc4 h4]].
  destruct (Side_cons_inv h4) as [w5 [hc5 h5]].
  destruct (Side_cons_inv h5) as [w6 [hc6 h6]].
  destruct (Side_cons_inv h6) as [w7 [hc7 h7]].
  destruct (Side_cons_inv h7) as [w8 [hc8 h8]].
  destruct (Side_cons_inv h8) as [w9 [hc9 h9]].
  destruct (Side_cons_inv h9) as [w10 [hc10 h10]].
  destruct (Side_cons_inv h10) as [w11 [hc11 h11]].
  destruct (Side_cons_inv h11) as [w12 [hc12 h12]].
  destruct (Side_cons_inv h12) as [w13 [hc13 h13]].
  destruct (Side_cons_inv h13) as [w14 [hc14 h14]].
  destruct (Side_cons_inv h14) as [w15 [hc15 h15]].
  destruct (Side_cons_inv h15) as [w16 [hc16 h16]].
  destruct (Side_cons_inv h16) as [w17 [hc17 h17]].
  destruct (Side_cons_inv h17) as [w18 [hc18 h18]].
  destruct (Side_cons_inv h18) as [w19 [hc19 h19]].
  destruct (Side_cons_inv h19) as [w20 [hc20 h20]].
  destruct (Side_cons_inv h20) as [w21 [hc21 h21]].
  destruct (Side_cons_inv h21) as [w22 [hc22 h22]].
  destruct (Side_cons_inv h22) as [w23 [hc23 h23]].
  destruct (Side_cons_inv h23) as [w24 [hc24 h24]].
  destruct (Side_cons_inv h24) as [w25 [hc25 h25]].
  destruct (Side_cons_inv h25) as [w26 [hc26 h26]].
  destruct (Side_cons_inv h26) as [w27 [hc27 h27]].
  destruct (Side_cons_inv h27) as [w28 [hc28 h28]].
  destruct (Side_cons_inv h28) as [w29 [hc29 h29]].
  destruct (Side_cons_inv h29) as [w30 [hc30 h30]].
  destruct (Side_cons_inv h30) as [w31 [hc31 h31]].
  destruct (Side_cons_inv h31) as [w32 [hc32 h32]].
  destruct (Side_cons_inv h32) as [w33 [hc33 h33]].
  destruct (Side_cons_inv h33) as [w34 [hc34 h34]].
  destruct (Side_cons_inv h34) as [w35 [hc35 h35]].
  destruct (Side_cons_inv h35) as [w36 [hc36 h36]].
  destruct (Side_cons_inv h36) as [w37 [hc37 h37]].
  destruct (Side_cons_inv h37) as [w38 [hc38 h38]].
  destruct (Side_cons_inv h38) as [w39 [hc39 h39]].
  destruct (Side_cons_inv h39) as [w40 [hc40 h40]].
  destruct (Side_cons_inv h40) as [w41 [hc41 h41]].
  destruct (Side_cons_inv h41) as [w42 [hc42 h42]].
  destruct (Side_cons_inv h42) as [w43 [hc43 h43]].
  destruct (Side_cons_inv h43) as [w44 [hc44 h44]].
  destruct (Side_cons_inv h44) as [w45 [hc45 h45]].
  destruct (Side_cons_inv h45) as [w46 [hc46 h46]].
  destruct (Side_cons_inv h46) as [w47 [hc47 h47]].
  destruct (Side_cons_inv h47) as [w48 [hc48 h48]].
  destruct (Side_cons_inv h48) as [w49 [hc49 h49]].
  destruct (Side_cons_inv h49) as [w50 [hc50 h50]].
  destruct (Side_cons_inv h50) as [w51 [hc51 h51]].
  destruct (Side_cons_inv h51) as [w52 [hc52 h52]].
  destruct (Side_cons_inv h52) as [w53 [hc53 h53]].
  destruct (Side_cons_inv h53) as [w54 [hc54 h54]].
  destruct (Side_cons_inv h54) as [w55 [hc55 h55]].
  destruct (Side_cons_inv h55) as [w56 [hc56 h56]].
  destruct (Side_cons_inv h56) as [w57 [hc57 h57]].
  destruct (Side_cons_inv h57) as [w58 [hc58 h58]].
  destruct (Side_cons_inv h58) as [w59 [hc59 h59]].
  destruct (Side_cons_inv h59) as [w60 [hc60 h60]].
  destruct (Side_cons_inv h60) as [w61 [hc61 h61]].
  destruct (Side_cons_inv h61) as [w62 [hc62 h62]].
  destruct (Side_cons_inv h62) as [w63 [hc63 h63]].
  destruct (Side_cons_inv h63) as [w64 [hc64 h64]].
  destruct (Side_cons_inv h64) as [w65 [hc65 h65]].
  destruct (Side_cons_inv h65) as [w66 [hc66 h66]].
  destruct (Side_cons_inv h66) as [w67 [hc67 h67]].
  destruct (Side_cons_inv h67) as [w68 [hc68 h68]].
  destruct (Side_cons_inv h68) as [w69 [hc69 h69]].
  destruct (Side_cons_inv h69) as [w70 [hc70 h70]].
  destruct (Side_cons_inv h70) as [w71 [hc71 h71]].
  destruct (Side_cons_inv h71) as [w72 [hc72 h72]].
  destruct (Side_cons_inv h72) as [w73 [hc73 h73]].
  destruct (Side_cons_inv h73) as [w74 [hc74 h74]].
  destruct (Side_cons_inv h74) as [w75 [hc75 h75]].
  destruct (Side_cons_inv h75) as [w76 [hc76 h76]].
  destruct (Side_cons_inv h76) as [w77 [hc77 h77]].
  destruct (Side_cons_inv h77) as [w78 [hc78 h78]].
  destruct (Side_cons_inv h78) as [w79 [hc79 h79]].
  destruct (Side_cons_inv h79) as [w80 [hc80 h80]].
  destruct (Side_cons_inv h80) as [w81 [hc81 h81]].
  destruct (Side_cons_inv h81) as [w82 [hc82 h82]].
  destruct (Side_cons_inv h82) as [w83 [hc83 h83]].
  destruct (Side_cons_inv h83) as [w84 [hc84 h84]].
  destruct (Side_cons_inv h84) as [w85 [hc85 h85]].
  destruct (Side_cons_inv h85) as [w86 [hc86 h86]].
  destruct (Side_cons_inv h86) as [w87 [hc87 h87]].
  destruct (Side_cons_inv h87) as [w88 [hc88 h88]].
  destruct (Side_cons_inv h88) as [w89 [hc89 h89]].
  destruct (Side_cons_inv h89) as [w90 [hc90 h90]].
  destruct (Side_cons_inv h90) as [w91 [hc91 h91]].
  destruct (Side_cons_inv h91) as [w92 [hc92 h92]].
  destruct (Side_cons_inv h92) as [w93 [hc93 h93]].
  destruct (Side_cons_inv h93) as [w94 [hc94 h94]].
  destruct (Side_cons_inv h94) as [w95 [hc95 h95]].
  destruct (Side_cons_inv h95) as [w96 [hc96 h96]].
  destruct (Side_cons_inv h96) as [w97 [hc97 h97]].
  destruct (Side_cons_inv h97) as [w98 [hc98 h98]].
  destruct (Side_cons_inv h98) as [w99 [hc99 h99]].
  destruct (Side_cons_inv h99) as [w100 [hc100 h100]].
  destruct (Side_cons_inv h100) as [w101 [hc101 h101]].
  destruct (Side_cons_inv h101) as [w102 [hc102 h102]].
  destruct (Side_cons_inv h102) as [w103 [hc103 h103]].
  destruct (Side_cons_inv h103) as [w104 [hc104 h104]].
  destruct (Side_cons_inv h104) as [w105 [hc105 h105]].
  destruct (Side_cons_inv h105) as [w106 [hc106 h106]].
  destruct (Side_cons_inv h106) as [w107 [hc107 h107]].
  destruct (Side_cons_inv h107) as [w108 [hc108 h108]].
  destruct (Side_cons_inv h108) as [w109 [hc109 h109]].
  destruct (Side_cons_inv h109) as [w110 [hc110 h110]].
  destruct (Side_cons_inv h110) as [w111 [hc111 h111]].
  destruct (Side_cons_inv h111) as [w112 [hc112 h112]].
  destruct (Side_cons_inv h112) as [w113 [hc113 h113]].
  destruct (Side_cons_inv h113) as [w114 [hc114 h114]].
  destruct (Side_cons_inv h114) as [w115 [hc115 h115]].
  destruct (Side_cons_inv h115) as [w116 [hc116 h116]].
  destruct (Side_cons_inv h116) as [w117 [hc117 h117]].
  destruct (Side_cons_inv h117) as [w118 [hc118 h118]].
  destruct (Side_cons_inv h118) as [w119 [hc119 h119]].
  destruct (Side_cons_inv h119) as [w120 [hc120 h120]].
  destruct (Side_cons_inv h120) as [w121 [hc121 h121]].
  destruct (Side_cons_inv h121) as [w122 [hc122 h122]].
  destruct (Side_cons_inv h122) as [w123 [hc123 h123]].
  destruct (Side_cons_inv h123) as [w124 [hc124 h124]].
  destruct (Side_cons_inv h124) as [w125 [hc125 h125]].
  destruct (Side_cons_inv h125) as [w126 [hc126 h126]].
  apply Side_nil_inv in h126. subst w126.
  pose proof (ptrans (hc126 (tr126 *> 0inf%sym)) (zP126 w')) as hp126.
  pose proof (ptrans (hc125 (tr125 *> 0inf%sym)) (ptrans (zP125 w125) hp126)) as hp125.
  pose proof (ptrans (hc124 (tr124 *> 0inf%sym)) (ptrans (zP124 w124) hp125)) as hp124.
  pose proof (ptrans (hc123 (tr123 *> 0inf%sym)) (ptrans (zP123 w123) hp124)) as hp123.
  pose proof (ptrans (hc122 (tr122 *> 0inf%sym)) (ptrans (zP122 w122) hp123)) as hp122.
  pose proof (ptrans (hc121 (tr121 *> 0inf%sym)) (ptrans (zP121 w121) hp122)) as hp121.
  pose proof (ptrans (hc120 (tr120 *> 0inf%sym)) (ptrans (zP120 w120) hp121)) as hp120.
  pose proof (ptrans (hc119 (tr119 *> 0inf%sym)) (ptrans (zP119 w119) hp120)) as hp119.
  pose proof (ptrans (hc118 (tr118 *> 0inf%sym)) (ptrans (zP118 w118) hp119)) as hp118.
  pose proof (ptrans (hc117 (tr117 *> 0inf%sym)) (ptrans (zP117 w117) hp118)) as hp117.
  pose proof (ptrans (hc116 (tr116 *> 0inf%sym)) (ptrans (zP116 w116) hp117)) as hp116.
  pose proof (ptrans (hc115 (tr115 *> 0inf%sym)) (ptrans (zP115 w115) hp116)) as hp115.
  pose proof (ptrans (hc114 (tr114 *> 0inf%sym)) (ptrans (zP114 w114) hp115)) as hp114.
  pose proof (ptrans (hc113 (tr113 *> 0inf%sym)) (ptrans (zP113 w113) hp114)) as hp113.
  pose proof (ptrans (hc112 (tr112 *> 0inf%sym)) (ptrans (zP112 w112) hp113)) as hp112.
  pose proof (ptrans (hc111 (tr111 *> 0inf%sym)) (ptrans (zP111 w111) hp112)) as hp111.
  pose proof (ptrans (hc110 (tr110 *> 0inf%sym)) (ptrans (zP110 w110) hp111)) as hp110.
  pose proof (ptrans (hc109 (tr109 *> 0inf%sym)) (ptrans (zP109 w109) hp110)) as hp109.
  pose proof (ptrans (hc108 (tr108 *> 0inf%sym)) (ptrans (zP108 w108) hp109)) as hp108.
  pose proof (ptrans (hc107 (tr107 *> 0inf%sym)) (ptrans (zP107 w107) hp108)) as hp107.
  pose proof (ptrans (hc106 (tr106 *> 0inf%sym)) (ptrans (zP106 w106) hp107)) as hp106.
  pose proof (ptrans (hc105 (tr105 *> 0inf%sym)) (ptrans (zP105 w105) hp106)) as hp105.
  pose proof (ptrans (hc104 (tr104 *> 0inf%sym)) (ptrans (zP104 w104) hp105)) as hp104.
  pose proof (ptrans (hc103 (tr103 *> 0inf%sym)) (ptrans (zP103 w103) hp104)) as hp103.
  pose proof (ptrans (hc102 (tr102 *> 0inf%sym)) (ptrans (zP102 w102) hp103)) as hp102.
  pose proof (ptrans (hc101 (tr101 *> 0inf%sym)) (ptrans (zP101 w101) hp102)) as hp101.
  pose proof (ptrans (hc100 (tr100 *> 0inf%sym)) (ptrans (zP100 w100) hp101)) as hp100.
  pose proof (ptrans (hc99 (tr99 *> 0inf%sym)) (ptrans (zP99 w99) hp100)) as hp99.
  pose proof (ptrans (hc98 (tr98 *> 0inf%sym)) (ptrans (zP98 w98) hp99)) as hp98.
  pose proof (ptrans (hc97 (tr97 *> 0inf%sym)) (ptrans (zP97 w97) hp98)) as hp97.
  pose proof (ptrans (hc96 (tr96 *> 0inf%sym)) (ptrans (zP96 w96) hp97)) as hp96.
  pose proof (ptrans (hc95 (tr95 *> 0inf%sym)) (ptrans (zP95 w95) hp96)) as hp95.
  pose proof (ptrans (hc94 (tr94 *> 0inf%sym)) (ptrans (zP94 w94) hp95)) as hp94.
  pose proof (ptrans (hc93 (tr93 *> 0inf%sym)) (ptrans (zP93 w93) hp94)) as hp93.
  pose proof (ptrans (hc92 (tr92 *> 0inf%sym)) (ptrans (zP92 w92) hp93)) as hp92.
  pose proof (ptrans (hc91 (tr91 *> 0inf%sym)) (ptrans (zP91 w91) hp92)) as hp91.
  pose proof (ptrans (hc90 (tr90 *> 0inf%sym)) (ptrans (zP90 w90) hp91)) as hp90.
  pose proof (ptrans (hc89 (tr89 *> 0inf%sym)) (ptrans (zP89 w89) hp90)) as hp89.
  pose proof (ptrans (hc88 (tr88 *> 0inf%sym)) (ptrans (zP88 w88) hp89)) as hp88.
  pose proof (ptrans (hc87 (tr87 *> 0inf%sym)) (ptrans (zP87 w87) hp88)) as hp87.
  pose proof (ptrans (hc86 (tr86 *> 0inf%sym)) (ptrans (zP86 w86) hp87)) as hp86.
  pose proof (ptrans (hc85 (tr85 *> 0inf%sym)) (ptrans (zP85 w85) hp86)) as hp85.
  pose proof (ptrans (hc84 (tr84 *> 0inf%sym)) (ptrans (zP84 w84) hp85)) as hp84.
  pose proof (ptrans (hc83 (tr83 *> 0inf%sym)) (ptrans (zP83 w83) hp84)) as hp83.
  pose proof (ptrans (hc82 (tr82 *> 0inf%sym)) (ptrans (zP82 w82) hp83)) as hp82.
  pose proof (ptrans (hc81 (tr81 *> 0inf%sym)) (ptrans (zP81 w81) hp82)) as hp81.
  pose proof (ptrans (hc80 (tr80 *> 0inf%sym)) (ptrans (zP80 w80) hp81)) as hp80.
  pose proof (ptrans (hc79 (tr79 *> 0inf%sym)) (ptrans (zP79 w79) hp80)) as hp79.
  pose proof (ptrans (hc78 (tr78 *> 0inf%sym)) (ptrans (zP78 w78) hp79)) as hp78.
  pose proof (ptrans (hc77 (tr77 *> 0inf%sym)) (ptrans (zP77 w77) hp78)) as hp77.
  pose proof (ptrans (hc76 (tr76 *> 0inf%sym)) (ptrans (zP76 w76) hp77)) as hp76.
  pose proof (ptrans (hc75 (tr75 *> 0inf%sym)) (ptrans (zP75 w75) hp76)) as hp75.
  pose proof (ptrans (hc74 (tr74 *> 0inf%sym)) (ptrans (zP74 w74) hp75)) as hp74.
  pose proof (ptrans (hc73 (tr73 *> 0inf%sym)) (ptrans (zP73 w73) hp74)) as hp73.
  pose proof (ptrans (hc72 (tr72 *> 0inf%sym)) (ptrans (zP72 w72) hp73)) as hp72.
  pose proof (ptrans (hc71 (tr71 *> 0inf%sym)) (ptrans (zP71 w71) hp72)) as hp71.
  pose proof (ptrans (hc70 (tr70 *> 0inf%sym)) (ptrans (zP70 w70) hp71)) as hp70.
  pose proof (ptrans (hc69 (tr69 *> 0inf%sym)) (ptrans (zP69 w69) hp70)) as hp69.
  pose proof (ptrans (hc68 (tr68 *> 0inf%sym)) (ptrans (zP68 w68) hp69)) as hp68.
  pose proof (ptrans (hc67 (tr67 *> 0inf%sym)) (ptrans (zP67 w67) hp68)) as hp67.
  pose proof (ptrans (hc66 (tr66 *> 0inf%sym)) (ptrans (zP66 w66) hp67)) as hp66.
  pose proof (ptrans (hc65 (tr65 *> 0inf%sym)) (ptrans (zP65 w65) hp66)) as hp65.
  pose proof (ptrans (hc64 (tr64 *> 0inf%sym)) (ptrans (zP64 w64) hp65)) as hp64.
  pose proof (ptrans (hc63 (tr63 *> 0inf%sym)) (ptrans (zP63 w63) hp64)) as hp63.
  pose proof (ptrans (hc62 (tr62 *> 0inf%sym)) (ptrans (zP62 w62) hp63)) as hp62.
  pose proof (ptrans (hc61 (tr61 *> 0inf%sym)) (ptrans (zP61 w61) hp62)) as hp61.
  pose proof (ptrans (hc60 (tr60 *> 0inf%sym)) (ptrans (zP60 w60) hp61)) as hp60.
  pose proof (ptrans (hc59 (tr59 *> 0inf%sym)) (ptrans (zP59 w59) hp60)) as hp59.
  pose proof (ptrans (hc58 (tr58 *> 0inf%sym)) (ptrans (zP58 w58) hp59)) as hp58.
  pose proof (ptrans (hc57 (tr57 *> 0inf%sym)) (ptrans (zP57 w57) hp58)) as hp57.
  pose proof (ptrans (hc56 (tr56 *> 0inf%sym)) (ptrans (zP56 w56) hp57)) as hp56.
  pose proof (ptrans (hc55 (tr55 *> 0inf%sym)) (ptrans (zP55 w55) hp56)) as hp55.
  pose proof (ptrans (hc54 (tr54 *> 0inf%sym)) (ptrans (zP54 w54) hp55)) as hp54.
  pose proof (ptrans (hc53 (tr53 *> 0inf%sym)) (ptrans (zP53 w53) hp54)) as hp53.
  pose proof (ptrans (hc52 (tr52 *> 0inf%sym)) (ptrans (zP52 w52) hp53)) as hp52.
  pose proof (ptrans (hc51 (tr51 *> 0inf%sym)) (ptrans (zP51 w51) hp52)) as hp51.
  pose proof (ptrans (hc50 (tr50 *> 0inf%sym)) (ptrans (zP50 w50) hp51)) as hp50.
  pose proof (ptrans (hc49 (tr49 *> 0inf%sym)) (ptrans (zP49 w49) hp50)) as hp49.
  pose proof (ptrans (hc48 (tr48 *> 0inf%sym)) (ptrans (zP48 w48) hp49)) as hp48.
  pose proof (ptrans (hc47 (tr47 *> 0inf%sym)) (ptrans (zP47 w47) hp48)) as hp47.
  pose proof (ptrans (hc46 (tr46 *> 0inf%sym)) (ptrans (zP46 w46) hp47)) as hp46.
  pose proof (ptrans (hc45 (tr45 *> 0inf%sym)) (ptrans (zP45 w45) hp46)) as hp45.
  pose proof (ptrans (hc44 (tr44 *> 0inf%sym)) (ptrans (zP44 w44) hp45)) as hp44.
  pose proof (ptrans (hc43 (tr43 *> 0inf%sym)) (ptrans (zP43 w43) hp44)) as hp43.
  pose proof (ptrans (hc42 (tr42 *> 0inf%sym)) (ptrans (zP42 w42) hp43)) as hp42.
  pose proof (ptrans (hc41 (tr41 *> 0inf%sym)) (ptrans (zP41 w41) hp42)) as hp41.
  pose proof (ptrans (hc40 (tr40 *> 0inf%sym)) (ptrans (zP40 w40) hp41)) as hp40.
  pose proof (ptrans (hc39 (tr39 *> 0inf%sym)) (ptrans (zP39 w39) hp40)) as hp39.
  pose proof (ptrans (hc38 (tr38 *> 0inf%sym)) (ptrans (zP38 w38) hp39)) as hp38.
  pose proof (ptrans (hc37 (tr37 *> 0inf%sym)) (ptrans (zP37 w37) hp38)) as hp37.
  pose proof (ptrans (hc36 (tr36 *> 0inf%sym)) (ptrans (zP36 w36) hp37)) as hp36.
  pose proof (ptrans (hc35 (tr35 *> 0inf%sym)) (ptrans (zP35 w35) hp36)) as hp35.
  pose proof (ptrans (hc34 (tr34 *> 0inf%sym)) (ptrans (zP34 w34) hp35)) as hp34.
  pose proof (ptrans (hc33 (tr33 *> 0inf%sym)) (ptrans (zP33 w33) hp34)) as hp33.
  pose proof (ptrans (hc32 (tr32 *> 0inf%sym)) (ptrans (zP32 w32) hp33)) as hp32.
  pose proof (ptrans (hc31 (tr31 *> 0inf%sym)) (ptrans (zP31 w31) hp32)) as hp31.
  pose proof (ptrans (hc30 (tr30 *> 0inf%sym)) (ptrans (zP30 w30) hp31)) as hp30.
  pose proof (ptrans (hc29 (tr29 *> 0inf%sym)) (ptrans (zP29 w29) hp30)) as hp29.
  pose proof (ptrans (hc28 (tr28 *> 0inf%sym)) (ptrans (zP28 w28) hp29)) as hp28.
  pose proof (ptrans (hc27 (tr27 *> 0inf%sym)) (ptrans (zP27 w27) hp28)) as hp27.
  pose proof (ptrans (hc26 (tr26 *> 0inf%sym)) (ptrans (zP26 w26) hp27)) as hp26.
  pose proof (ptrans (hc25 (tr25 *> 0inf%sym)) (ptrans (zP25 w25) hp26)) as hp25.
  pose proof (ptrans (hc24 (tr24 *> 0inf%sym)) (ptrans (zP24 w24) hp25)) as hp24.
  pose proof (ptrans (hc23 (tr23 *> 0inf%sym)) (ptrans (zP23 w23) hp24)) as hp23.
  pose proof (ptrans (hc22 (tr22 *> 0inf%sym)) (ptrans (zP22 w22) hp23)) as hp22.
  pose proof (ptrans (hc21 (tr21 *> 0inf%sym)) (ptrans (zP21 w21) hp22)) as hp21.
  pose proof (ptrans (hc20 (tr20 *> 0inf%sym)) (ptrans (zP20 w20) hp21)) as hp20.
  pose proof (ptrans (hc19 (tr19 *> 0inf%sym)) (ptrans (zP19 w19) hp20)) as hp19.
  pose proof (ptrans (hc18 (tr18 *> 0inf%sym)) (ptrans (zP18 w18) hp19)) as hp18.
  pose proof (ptrans (hc17 (tr17 *> 0inf%sym)) (ptrans (zP17 w17) hp18)) as hp17.
  pose proof (ptrans (hc16 (tr16 *> 0inf%sym)) (ptrans (zP16 w16) hp17)) as hp16.
  pose proof (ptrans (hc15 (tr15 *> 0inf%sym)) (ptrans (zP15 w15) hp16)) as hp15.
  pose proof (ptrans (hc14 (tr14 *> 0inf%sym)) (ptrans (zP14 w14) hp15)) as hp14.
  pose proof (ptrans (hc13 (tr13 *> 0inf%sym)) (ptrans (zP13 w13) hp14)) as hp13.
  pose proof (ptrans (hc12 (tr12 *> 0inf%sym)) (ptrans (zP12 w12) hp13)) as hp12.
  pose proof (ptrans (hc11 (tr11 *> 0inf%sym)) (ptrans (zP11 w11) hp12)) as hp11.
  pose proof (ptrans (hc10 (tr10 *> 0inf%sym)) (ptrans (zP10 w10) hp11)) as hp10.
  pose proof (ptrans (hc9 (tr9 *> 0inf%sym)) (ptrans (zP9 w9) hp10)) as hp9.
  pose proof (ptrans (hc8 (tr8 *> 0inf%sym)) (ptrans (zP8 w8) hp9)) as hp8.
  pose proof (ptrans (hc7 (tr7 *> 0inf%sym)) (ptrans (zP7 w7) hp8)) as hp7.
  pose proof (ptrans (hc6 (tr6 *> 0inf%sym)) (ptrans (zP6 w6) hp7)) as hp6.
  pose proof (ptrans (hc5 (tr5 *> 0inf%sym)) (ptrans (zP5 w5) hp6)) as hp5.
  pose proof (ptrans (hc4 (tr4 *> 0inf%sym)) (ptrans (zP4 w4) hp5)) as hp4.
  pose proof (ptrans (hc3 (tr3 *> 0inf%sym)) (ptrans (zP3 w3) hp4)) as hp3.
  pose proof (ptrans (hc2 (tr2 *> 0inf%sym)) (ptrans (zP2 w2) hp3)) as hp2.
  pose proof (ptrans (hc1 (tr1 *> 0inf%sym)) (ptrans (zP1 w1) hp2)) as hp1.
  exact (ptrans (zP0 w) hp1).
Qed.

Lemma Step_exec {u u' : list Word} (h : Step u u') :
    zCf (zTs u 0inf%sym) -->+ zCf (zTs u' 0inf%sym).
Proof.
  destruct h as [n [b' [v [da [H [g [hScan [hDg ->]]]]]]]].
  pose proof (Seg_of_Scan hScan) as hSeg.
  change ([ch] ^^ (N.to_nat 0%N) ++ [ca] ^^ (N.to_nat 126%N)) with ([ca] ^^ 126) in hSeg.
  change ([ch] ^^ (N.to_nat 0%N) ++ [ca] ^^ (N.to_nat b')) with ([ca] ^^ (N.to_nat b')) in hSeg.
  pose proof (zSc hSeg (Side_ca_default hDg)) as hSide0.
  rewrite zWt_zTs, zTs_append, zTs_rep_K, zWt'_zTs', <- zTs'_append in hSide0.
  pose proof (Side_turnaround hSide0) as hTurn.
  rewrite zTs_V_shift in hTurn.
  exact hTurn.
Qed.

Lemma Rounds_exec {u v : list Word} (h : Rounds u v) :
    zCf (zTs u 0inf%sym) -->* zCf (zTs v 0inf%sym).
Proof.
  induction h as [u | u v w hS _ ih].
  - apply evstep_refl.
  - exact (pev (pe_trans (Step_exec hS) ih)).
Qed.

(* Section 3: Universal Parse_V_start, Scan_of_Parse, and Trace Evaluators *)

Definition CanParse (a : N) (u : list Word) : Prop :=
  exists a' g, Parse a u a' g.

Lemma K_neq_V : K <> V. Proof. discriminate. Qed.
Lemma Q_neq_V : Q_w <> V. Proof. discriminate. Qed.

Lemma Parse_all (u : list Word) :
    (forall a : N, CanParse a (V :: u)) /\
    (forall (w0 : Word) (a q1 : N),
        w0 <> V -> (a + dVal w0 = q1 * 2)%N -> CanParse a (w0 :: u)) /\
    (forall (w1 : Word) (k : N),
        w1 <> V -> CanParse k u \/ CanParse (2 * k + 1 - dVal w1)%N (w1 :: u)).
Proof.
  induction u as [| x u' [hV [hEven hChoice]]].
  - split; [| split].
    + intro a. exists (1 + a * 2)%N, 0. exact (Parse_T (Parse_nil _)).
    + intros w0 a q1 hw0 hq1. exists q1, 0. exact (Parse_D hw0 hq1 (Parse_nil q1)).
    + intros w1 k _. left. exists k, 0. exact (Parse_nil k).
  - destruct x.
    + split; [| split].
      * intro a. destruct (hV (1 + a * 2)%N) as [a' [g hp]].
        exists a', g. exact (Parse_T hp).
      * intros w0 a q1 hw0 hq1. destruct (hV q1) as [a' [g hp]].
        exists a', g. exact (Parse_D hw0 hq1 hp).
      * intros w1 k _. left. exact (hV k).
    + assert (h_choice_K : forall (w1 : Word) (k : N),
          w1 <> V -> CanParse k (K :: u') \/ CanParse (2 * k + 1 - dVal w1)%N (w1 :: K :: u')).
      { intros w1 k hw1.
        destruct (z0U (k + dVal K)%N) as [[q2 hq2] | [q2 hq2]].
        - left. exact (hEven K k q2 K_neq_V hq2).
        - destruct (hChoice K q2 K_neq_V) as [[a' [g hp2]] | hR].
          + right.
            assert (hdiv : ((2 * k + 1 - dVal w1 + dVal w1) / 2 + dVal K = 1 + q2 * 2)%N)
              by (destruct w1; cbn [dVal] in *; lia).
            exists a', (1 + g). exact (Parse_P hw1 K_neq_V hdiv hp2).
          + left.
            replace k with (2 * q2 + 1 - dVal K)%N by (cbn [dVal] in *; lia).
            exact hR. }
      assert (h_even_K : forall (w0 : Word) (a q1 : N),
          w0 <> V -> (a + dVal w0 = q1 * 2)%N -> CanParse a (w0 :: K :: u')).
      { intros w0 a q1 hw0 hq1.
        destruct (z0U (q1 + dVal K)%N) as [[q2 hq2] | [q2 hq2]].
        - destruct (hEven K q1 q2 K_neq_V hq2) as [a' [g hp]].
          exists a', g. exact (Parse_D hw0 hq1 hp).
        - destruct (hChoice K q2 K_neq_V) as [[a' [g hp2]] | hR].
          + assert (hdiv : ((a + dVal w0) / 2 + dVal K = 1 + q2 * 2)%N)
              by (destruct w0; cbn [dVal] in *; lia).
            exists a', (1 + g). exact (Parse_P hw0 K_neq_V hdiv hp2).
          + replace (2 * q2 + 1 - dVal K)%N with q1 in hR by (cbn [dVal] in *; lia).
            destruct hR as [a' [g hp]].
            exists a', g. exact (Parse_D hw0 hq1 hp). }
      assert (h_V_K : forall a : N, CanParse a (V :: K :: u')).
      { intro a.
        destruct (hChoice K a K_neq_V) as [[a' [g hp]] | hR].
        - exists a', g. exact (Parse_VK hp).
        - replace (2 * a + 1 - dVal K)%N with (1 + a * 2)%N in hR by (cbn [dVal]; lia).
          destruct hR as [a' [g hp]].
          exists a', g. exact (Parse_T hp). }
      exact (conj h_V_K (conj h_even_K h_choice_K)).
    + assert (h_choice_Q : forall (w1 : Word) (k : N),
          w1 <> V -> CanParse k (Q_w :: u') \/ CanParse (2 * k + 1 - dVal w1)%N (w1 :: Q_w :: u')).
      { intros w1 k hw1.
        destruct (z0U (k + dVal Q_w)%N) as [[q2 hq2] | [q2 hq2]].
        - left. exact (hEven Q_w k q2 Q_neq_V hq2).
        - destruct (hChoice Q_w q2 Q_neq_V) as [[a' [g hp2]] | hR].
          + right.
            assert (hdiv2 : ((2 * k + 1 - dVal w1 + dVal w1) / 2 + dVal Q_w = 1 + q2 * 2)%N)
              by (destruct w1; cbn [dVal] in *; lia).
            exists a', (1 + g). exact (Parse_P hw1 Q_neq_V hdiv2 hp2).
          + left.
            replace k with (2 * q2 + 1 - dVal Q_w)%N by (cbn [dVal] in *; lia).
            exact hR. }
      assert (h_even_Q : forall (w0 : Word) (a q1 : N),
          w0 <> V -> (a + dVal w0 = q1 * 2)%N -> CanParse a (w0 :: Q_w :: u')).
      { intros w0 a q1 hw0 hq1.
        destruct (z0U (q1 + dVal Q_w)%N) as [[q2 hq2] | [q2 hq2]].
        - destruct (hEven Q_w q1 q2 Q_neq_V hq2) as [a' [g hp]].
          exists a', g. exact (Parse_D hw0 hq1 hp).
        - destruct (hChoice Q_w q2 Q_neq_V) as [[a' [g hp2]] | hR].
          + assert (hdiv : ((a + dVal w0) / 2 + dVal Q_w = 1 + q2 * 2)%N)
              by (destruct w0; cbn [dVal] in *; lia).
            exists a', (1 + g). exact (Parse_P hw0 Q_neq_V hdiv hp2).
          + replace (2 * q2 + 1 - dVal Q_w)%N with q1 in hR by (cbn [dVal] in *; lia).
            destruct hR as [a' [g hp]].
            exists a', g. exact (Parse_D hw0 hq1 hp). }
      assert (h_V_Q : forall a : N, CanParse a (V :: Q_w :: u')).
      { intro a.
        assert (hev : ((1 + a * 2) + dVal Q_w = (1 + a) * 2)%N) by (cbn [dVal]; lia).
        destruct (hEven Q_w (1 + a * 2)%N (1 + a)%N Q_neq_V hev) as [a' [g hp]].
        exists a', g. exact (Parse_T hp). }
      exact (conj h_V_Q (conj h_even_Q h_choice_Q)).
Qed.

Lemma Parse_V_start (a : N) (u : list Word) : exists a' g, Parse a (V :: u) a' g.
Proof. exact (proj1 (Parse_all u) a). Qed.

(* Algebraic summaries in QArith *)

Definition Rat := QArith_base.Q.
Definition qN (n : N) : Rat := inject_Z (Z.of_N n).
Definition qnat (n : nat) : Rat := inject_Z (Z.of_nat n).
Definition qpow2 (k : nat) : Rat := inject_Z (2 ^ (Z.of_nat k))%Z.

Lemma qN_0 : (qN 0 == 0)%Q. Proof. reflexivity. Qed.
Lemma qN_1 : (qN 1 == 1)%Q. Proof. reflexivity. Qed.
Lemma qN_2 : (qN 2 == 2)%Q. Proof. reflexivity. Qed.

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

Lemma qpow2_S (k : nat) : (qpow2 (S k) == 2 * qpow2 k)%Q.
Proof. exact (qpow2_1_add k). Qed.

Lemma qpow2_pos (k : nat) : (0 < qpow2 k)%Q.
Proof.
  unfold qpow2. change 0%Q with (inject_Z 0). rewrite <- Zlt_Qlt.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma qpow2_ge_1 (k : nat) : (1 <= qpow2 k)%Q.
Proof.
  unfold qpow2. change 1%Q with (inject_Z 1). rewrite <- Zle_Qle.
  change 1%Z with (2 ^ 0)%Z. apply Z.pow_le_mono_r; lia.
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

Fixpoint z10 (u : list Word) : Rat :=
  match u with
  | [] => 0%Q
  | V :: u' => ((1#2) * z10 u')%Q
  | _ :: u' => (1 + 2 * z10 u')%Q
  end.

Fixpoint z12 (u : list Word) : Rat :=
  match u with
  | [] => 0%Q
  | V :: u' => ((1#2) * z12 u')%Q
  | K :: u' => (2 * z12 u')%Q
  | Q_w :: u' => (1 + 2 * z12 u')%Q
  end.

Fixpoint z13 (u : list Word) : Rat :=
  match u with
  | [] => 1%Q
  | V :: u' => ((1#2) * z13 u')%Q
  | _ :: u' => (2 * z13 u')%Q
  end.

Fixpoint zWPair (u : list Word) : Rat * Rat :=
  match u with
  | [] => (0%Q, 0%Q)
  | V :: u' =>
    let p := zWPair u' in
    (snd p, ((1#2) * snd p)%Q)
  | K :: u' =>
    let p := zWPair u' in
    (((3#2) + 2 * fst p)%Q, (1 + fst p)%Q)
  | Q_w :: u' =>
    let p := zWPair u' in
    (((3#2) + 2 * fst p)%Q, ((3#4) + fst p)%Q)
  end.

Definition zW (u : list Word) : Rat := fst (zWPair u).
Definition zW_V (u : list Word) : Rat := snd (zWPair u).

Fixpoint dCount (u : list Word) : nat :=
  match u with
  | [] => 0
  | V :: u' => dCount u'
  | _ :: u' => 1 + dCount u'
  end.

Lemma zW_nil : zW [] = 0%Q. Proof. reflexivity. Qed.
Lemma zW_V_nil : zW_V [] = 0%Q. Proof. reflexivity. Qed.
Lemma zW_cons_V (u : list Word) : zW (V :: u) = zW_V u. Proof. reflexivity. Qed.
Lemma zW_V_cons_V (u : list Word) : zW_V (V :: u) = ((1#2) * zW_V u)%Q. Proof. reflexivity. Qed.
Lemma zW_cons_K (u : list Word) : zW (K :: u) = ((3#2) + 2 * zW u)%Q. Proof. reflexivity. Qed.
Lemma zW_V_cons_K (u : list Word) : zW_V (K :: u) = (1 + zW u)%Q. Proof. reflexivity. Qed.
Lemma zW_cons_Q (u : list Word) : zW (Q_w :: u) = ((3#2) + 2 * zW u)%Q. Proof. reflexivity. Qed.
Lemma zW_V_cons_Q (u : list Word) : zW_V (Q_w :: u) = ((3#4) + zW u)%Q. Proof. reflexivity. Qed.

Lemma z10_nonneg (u : list Word) : (0 <= z10 u)%Q.
Proof.
  induction u as [| a u ih]; [cbn; lra |].
  destruct a; cbn [z10]; lra.
Qed.

Lemma z12_nonneg (u : list Word) : (0 <= z12 u)%Q.
Proof.
  induction u as [| a u ih]; [cbn; lra |].
  destruct a; cbn [z12]; lra.
Qed.

Lemma z10_cons_d {w0 : Word} (hw0 : w0 <> V) (u : list Word) :
    z10 (w0 :: u) = (1 + 2 * z10 u)%Q.
Proof. destruct w0; [contradiction | reflexivity | reflexivity]. Qed.

Lemma z13_cons_d {w0 : Word} (hw0 : w0 <> V) (u : list Word) :
    z13 (w0 :: u) = (2 * z13 u)%Q.
Proof. destruct w0; [contradiction | reflexivity | reflexivity]. Qed.

Lemma zW_cons_d {w0 : Word} (hw0 : w0 <> V) (u : list Word) :
    zW (w0 :: u) = ((3#2) + 2 * zW u)%Q.
Proof. destruct w0; [contradiction | reflexivity | reflexivity]. Qed.

Lemma Scan_of_Parse {a a' : N} {g : nat} {u : list Word} (h : Parse a u a' g) :
    forall b : N, (2 + 4 * z10 u < qN b)%Q ->
      exists (b' : N) (v : list Word), Scan a b u a' b' v g /\ (3 <= b')%N.
Proof.
  induction h as
    [ a
    | a a' g u _ ih
    | a a' g u _ ih
    | a q1 a' g w0 u hw0 hq1 _ ih
    | a q2 a' g w0 w1 u hw0 hw1 hq2 _ ih ]; intros b hb.
  - cbn [z10] in hb.
    assert (hb_q : (qN 2 < qN b)%Q) by (norm_qN; lra).
    apply qN_lt_iff in hb_q.
    exists b, (@nil Word). split; [exact (Scan_nil a b ltac:(lia)) | lia].
  - pose proof (z10_nonneg u) as hz.
    cbn [z10] in hb.
    assert (hb_q : (qN 2 < qN b)%Q) by (norm_qN; lra).
    apply qN_lt_iff in hb_q.
    assert (hb_next : (2 + 4 * z10 u < qN ((b - 1) * 2)%N)%Q).
    { rewrite qN_mul, qN_sub by lia. norm_qN. lra. }
    destruct (ih ((b - 1) * 2)%N hb_next) as [b' [v [hS hb']]].
    exists b', (V :: v). split; [refine (Scan_T _ hS); lia | exact hb'].
  - pose proof (z10_nonneg u) as hz.
    cbn [z10] in hb.
    assert (hb_q : (qN 4 < qN b)%Q) by (norm_qN; lra).
    apply qN_lt_iff in hb_q.
    destruct (z0U b) as [[k ->] | [k ->]].
    + assert (hk : (1 <= k)%N) by lia.
      assert (hb_next : (2 + 4 * z10 u < qN (1 + (k - 1) * 2)%N)%Q).
      { rewrite qN_add, qN_mul, qN_sub by lia.
        rewrite qN_mul in hb. norm_qN. lra. }
      destruct (ih (1 + (k - 1) * 2)%N hb_next) as [b' [v [hS hb']]].
      exists b', (K :: V :: v). split; [exact (Scan_VK0 hk hS) | exact hb'].
    + assert (hk : (1 <= k)%N) by lia.
      assert (hb_next : (2 + 4 * z10 u < qN (1 + (k - 1) * 2)%N)%Q).
      { rewrite qN_add, qN_mul, qN_sub by lia.
        rewrite qN_add, qN_mul in hb. norm_qN. lra. }
      destruct (ih (1 + (k - 1) * 2)%N hb_next) as [b' [v [hS hb']]].
      exists b', (Q_w :: V :: v). split; [exact (Scan_VK1 hk hS) | exact hb'].
  - pose proof (z10_nonneg u) as hz.
    rewrite (z10_cons_d hw0) in hb.
    assert (hb_q : (qN 6 < qN b)%Q) by (norm_qN; lra).
    apply qN_lt_iff in hb_q.
    assert (hmod : (b <= (b / 2) * 2 + 1)%N) by lia.
    apply qN_le_iff in hmod.
    rewrite qN_add, qN_mul in hmod.
    assert (hb_div : (2 + 4 * z10 u < qN (b / 2)%N)%Q) by (norm_qN; lra).
    destruct (ih (b / 2)%N hb_div) as [b' [v [hS hb']]].
    exists b', ((if (b mod 2 =? 1)%N then Q_w else K) :: v).
    split; [refine (Scan_D hw0 hq1 _ hS); lia | exact hb'].
  - pose proof (z10_nonneg u) as hz.
    rewrite (z10_cons_d hw0), (z10_cons_d hw1) in hb.
    assert (hb_q : (qN 14 < qN b)%Q) by (norm_qN; lra).
    apply qN_lt_iff in hb_q.
    destruct (z0U (a + dVal w0)%N) as [[q1 hq1] | [q1 hq1]].
    + assert (hq2' : (q1 + dVal w1 = 1 + q2 * 2)%N) by lia.
      assert (hb_next : (2 + 4 * z10 u < qN ((b - 1) * 2)%N)%Q).
      { rewrite qN_mul, qN_sub by lia. norm_qN. lra. }
      destruct (ih ((b - 1) * 2)%N hb_next) as [b' [v [hS hb']]].
      exists b', (V :: v). split; [refine (Scan_P0 hw0 hw1 hq1 hq2' _ hS); lia | exact hb'].
    + assert (hq2' : (q1 + dVal w1 = 1 + q2 * 2)%N) by lia.
      assert (hb_next : (2 + 4 * z10 u < qN (1 + (b - 1) * 2)%N)%Q).
      { rewrite qN_add, qN_mul, qN_sub by lia. norm_qN. lra. }
      destruct (ih (1 + (b - 1) * 2)%N hb_next) as [b' [v [hS hb']]].
      exists b', (V :: v). split; [refine (Scan_P1 hw0 hw1 hq1 hq2' _ hS); lia | exact hb'].
Qed.

Lemma Scan_append {a b a1 b1 : N} {g1 : nat} {u1 v1 : list Word}
    (h1 : Scan a b u1 a1 b1 v1 g1) :
    forall {a2 b2 : N} {g2 : nat} {u2 v2 : list Word},
      Scan a1 b1 u2 a2 b2 v2 g2 ->
      Scan a b (u1 ++ u2) a2 b2 (v1 ++ v2) (g1 + g2).
Proof.
  induction h1 as
    [ a b _
    | a b a1 b1 g1 u1 v1 hb _ ih
    | a k a1 b1 g1 u1 v1 hk _ ih
    | a k a1 b1 g1 u1 v1 hk _ ih
    | a b q1 a1 b1 g1 w0 u1 v1 hw0 hq1 hb _ ih
    | a b q1 q2 a1 b1 g1 w0 w1 u1 v1 hw0 hw1 hq1 hq2 hb _ ih
    | a b q1 q2 a1 b1 g1 w0 w1 u1 v1 hw0 hw1 hq1 hq2 hb _ ih ];
    intros a2 b2 g2 u2 v2 h2; cbn [List.app Nat.add].
  - exact h2.
  - exact (Scan_T hb (ih _ _ _ _ _ h2)).
  - exact (Scan_VK0 hk (ih _ _ _ _ _ h2)).
  - exact (Scan_VK1 hk (ih _ _ _ _ _ h2)).
  - exact (Scan_D hw0 hq1 hb (ih _ _ _ _ _ h2)).
  - exact (Scan_P0 hw0 hw1 hq1 hq2 hb (ih _ _ _ _ _ h2)).
  - exact (Scan_P1 hw0 hw1 hq1 hq2 hb (ih _ _ _ _ _ h2)).
Qed.

(* Trace evaluators *)

Definition word_is_not_V (w : Word) : bool :=
  match w with
  | V => false
  | _ => true
  end.

Lemma word_is_not_V_iff (w : Word) : word_is_not_V w = true <-> w <> V.
Proof. destruct w; cbn; split; intro H; congruence. Qed.

Fixpoint evalAffineScan (ts : list nat) (ma ca mb cb : N) (u : list Word)
  : option (N * N * N * N * list Word * nat) :=
  match ts with
  | [] =>
    match u with
    | [] => if (1 <=? cb)%N then Some (ma, ca, mb, cb, [], 0) else None
    | _ => None
    end
  | t :: ts' =>
    match t with
    | 0 =>
      match u with
      | V :: u' =>
        if (2 <=? cb)%N then
          match evalAffineScan ts' (ma * 2)%N (1 + ca * 2)%N (mb * 2)%N ((cb - 1) * 2)%N u' with
          | Some (ma', ca', mb', cb', v, g) => Some (ma', ca', mb', cb', V :: v, g)
          | None => None
          end
        else None
      | _ => None
      end
    | 1 =>
      match u with
      | V :: K :: u' =>
        if (2 <=? cb)%N && (mb mod 2 =? 0)%N && (cb mod 2 =? 0)%N then
          match evalAffineScan ts' ma ca mb (cb - 1)%N u' with
          | Some (ma', ca', mb', cb', v, g) => Some (ma', ca', mb', cb', K :: V :: v, g)
          | None => None
          end
        else None
      | _ => None
      end
    | 2 =>
      match u with
      | V :: K :: u' =>
        if (3 <=? cb)%N && (mb mod 2 =? 0)%N && (cb mod 2 =? 1)%N then
          match evalAffineScan ts' ma ca mb (cb - 2)%N u' with
          | Some (ma', ca', mb', cb', v, g) => Some (ma', ca', mb', cb', Q_w :: V :: v, g)
          | None => None
          end
        else None
      | _ => None
      end
    | 3 =>
      match u with
      | w0 :: u' =>
        if word_is_not_V w0 && (ma mod 2 =? 0)%N && ((ca + dVal w0) mod 2 =? 0)%N
           && (2 <=? cb)%N && (mb mod 2 =? 0)%N then
          match evalAffineScan ts' (ma / 2)%N ((ca + dVal w0) / 2)%N (mb / 2)%N (cb / 2)%N u' with
          | Some (ma', ca', mb', cb', v, g) =>
            Some (ma', ca', mb', cb', (if (cb mod 2 =? 1)%N then Q_w else K) :: v, g)
          | None => None
          end
        else None
      | _ => None
      end
    | 4 =>
      match u with
      | w0 :: w1 :: u' =>
        if word_is_not_V w0 && word_is_not_V w1 && (ma mod 4 =? 0)%N
           && ((ca + dVal w0) mod 2 =? 0)%N
           && (((ca + dVal w0) / 2 + dVal w1) mod 2 =? 1)%N && (2 <=? cb)%N then
          match evalAffineScan ts' (ma / 4)%N (((ca + dVal w0) / 2 + dVal w1) / 2)%N
                               (mb * 2)%N ((cb - 1) * 2)%N u' with
          | Some (ma', ca', mb', cb', v, g) => Some (ma', ca', mb', cb', V :: v, 1 + g)
          | None => None
          end
        else None
      | _ => None
      end
    | 5 =>
      match u with
      | w0 :: w1 :: u' =>
        if word_is_not_V w0 && word_is_not_V w1 && (ma mod 4 =? 0)%N
           && ((ca + dVal w0) mod 2 =? 1)%N
           && (((ca + dVal w0) / 2 + dVal w1) mod 2 =? 1)%N && (2 <=? cb)%N then
          match evalAffineScan ts' (ma / 4)%N (((ca + dVal w0) / 2 + dVal w1) / 2)%N
                               (mb * 2)%N (1 + (cb - 1) * 2)%N u' with
          | Some (ma', ca', mb', cb', v, g) => Some (ma', ca', mb', cb', V :: v, 1 + g)
          | None => None
          end
        else None
      | _ => None
      end
    | _ => None
    end
  end.

Lemma affine_b_ge (mb xb cb k : N) (hcb : (k <= cb)%N) : (k <= mb * xb + cb)%N.
Proof. nia. Qed.

Lemma affine_mul2_a (ma ca xa : N) :
    (ma * 2 * xa + (1 + ca * 2) = 1 + (ma * xa + ca) * 2)%N.
Proof. nia. Qed.

Lemma affine_mul2_b0 (mb cb xb : N) (hcb : (2 <= cb)%N) :
    (mb * 2 * xb + (cb - 1) * 2 = (mb * xb + cb - 1) * 2)%N.
Proof. nia. Qed.

Lemma affine_mul2_b1 (mb cb xb : N) (hcb : (2 <= cb)%N) :
    (mb * 2 * xb + (1 + (cb - 1) * 2) = 1 + (mb * xb + cb - 1) * 2)%N.
Proof. nia. Qed.

Lemma affine_vk0_aux (m2 c2 xb : N) (hc2 : (1 <= c2)%N) :
    let k := (m2 * xb + c2)%N in
    (1 <= k)%N /\ (m2 * 2 * xb + c2 * 2 = k * 2)%N /\
    (m2 * 2 * xb + (c2 * 2 - 1) = 1 + (k - 1) * 2)%N.
Proof. intro k; unfold k; split; [nia | split; nia]. Qed.

Lemma affine_vk0 (mb cb xb : N)
    (hcb : (2 <= cb)%N) (hmb : (mb mod 2 = 0)%N) (hcb2 : (cb mod 2 = 0)%N) :
    let k := ((mb / 2) * xb + cb / 2)%N in
    (1 <= k)%N /\ (mb * xb + cb = k * 2)%N /\ (mb * xb + (cb - 1) = 1 + (k - 1) * 2)%N.
Proof.
  assert (hmb_eq : (mb = (mb / 2) * 2)%N) by lia.
  assert (hcb_eq : (cb = (cb / 2) * 2)%N) by lia.
  assert (hc2 : (1 <= cb / 2)%N) by lia.
  pose proof (affine_vk0_aux (mb / 2)%N (cb / 2)%N xb hc2) as H.
  cbv zeta in H |- *.
  rewrite <- hmb_eq, <- hcb_eq in H.
  exact H.
Qed.

Lemma affine_vk1_aux (m2 c2 xb : N) (hc2 : (1 <= c2)%N) :
    let k := (m2 * xb + c2)%N in
    (1 <= k)%N /\ (m2 * 2 * xb + (1 + c2 * 2) = 1 + k * 2)%N /\
    (m2 * 2 * xb + (1 + c2 * 2 - 2) = 1 + (k - 1) * 2)%N.
Proof. intro k; unfold k; split; [nia | split; nia]. Qed.

Lemma affine_vk1 (mb cb xb : N)
    (hcb : (3 <= cb)%N) (hmb : (mb mod 2 = 0)%N) (hcb2 : (cb mod 2 = 1)%N) :
    let k := ((mb / 2) * xb + cb / 2)%N in
    (1 <= k)%N /\ (mb * xb + cb = 1 + k * 2)%N /\ (mb * xb + (cb - 2) = 1 + (k - 1) * 2)%N.
Proof.
  assert (hmb_eq : (mb = (mb / 2) * 2)%N) by lia.
  assert (hcb_eq : (cb = 1 + (cb / 2) * 2)%N) by lia.
  assert (hc2 : (1 <= cb / 2)%N) by lia.
  pose proof (affine_vk1_aux (mb / 2)%N (cb / 2)%N xb hc2) as H.
  cbv zeta in H |- *.
  rewrite <- hmb_eq, <- hcb_eq in H.
  exact H.
Qed.

Lemma affine_div2_even_aux (m2 cd2 xa : N) :
    (m2 * 2 * xa + cd2 * 2 = (m2 * xa + cd2) * 2)%N.
Proof. nia. Qed.

Lemma affine_div2_even (ma ca xa d0 : N)
    (hma : (ma mod 2 = 0)%N) (hca : ((ca + d0) mod 2 = 0)%N) :
    ((ma * xa + ca) + d0 = ((ma / 2) * xa + (ca + d0) / 2) * 2)%N.
Proof.
  assert (hma_eq : (ma = (ma / 2) * 2)%N) by lia.
  assert (hca_eq : (ca + d0 = ((ca + d0) / 2) * 2)%N) by lia.
  pose proof (affine_div2_even_aux (ma / 2)%N ((ca + d0) / 2)%N xa) as H.
  rewrite <- hma_eq, <- hca_eq in H.
  rewrite <- N.add_assoc. exact H.
Qed.

Lemma affine_div2_odd_aux (m2 cd2 xa : N) :
    (m2 * 2 * xa + (1 + cd2 * 2) = 1 + (m2 * xa + cd2) * 2)%N.
Proof. nia. Qed.

Lemma affine_div2_odd (ma ca xa d0 : N)
    (hma : (ma mod 2 = 0)%N) (hca : ((ca + d0) mod 2 = 1)%N) :
    ((ma * xa + ca) + d0 = 1 + ((ma / 2) * xa + (ca + d0) / 2) * 2)%N.
Proof.
  assert (hma_eq : (ma = (ma / 2) * 2)%N) by lia.
  assert (hca_eq : (ca + d0 = 1 + ((ca + d0) / 2) * 2)%N) by lia.
  pose proof (affine_div2_odd_aux (ma / 2)%N ((ca + d0) / 2)%N xa) as H.
  rewrite <- hma_eq, <- hca_eq in H.
  rewrite <- N.add_assoc. exact H.
Qed.

Lemma affine_div2_b_aux (m2 c2 r xb : N) :
    (m2 * 2 * xb + (c2 * 2 + r) = (m2 * xb + c2) * 2 + r)%N.
Proof. nia. Qed.

Lemma affine_div2_b_qr (k r : N) (hr : (r < 2)%N) :
    (k = (k * 2 + r) / 2)%N /\ ((k * 2 + r) mod 2 = r)%N.
Proof. split; lia. Qed.

Lemma affine_div2_b (mb cb xb : N) (hmb : (mb mod 2 = 0)%N) :
    ((mb / 2) * xb + cb / 2 = (mb * xb + cb) / 2)%N /\
    ((mb * xb + cb) mod 2 = cb mod 2)%N.
Proof.
  assert (hmb_eq : (mb = (mb / 2) * 2)%N) by lia.
  assert (hcb_eq : (cb = (cb / 2) * 2 + cb mod 2)%N) by lia.
  assert (hr : (cb mod 2 < 2)%N) by lia.
  pose proof (affine_div2_b_aux (mb / 2)%N (cb / 2)%N (cb mod 2)%N xb) as H.
  rewrite <- hmb_eq, <- hcb_eq in H.
  rewrite H.
  exact (affine_div2_b_qr ((mb / 2) * xb + cb / 2)%N (cb mod 2)%N hr).
Qed.

Lemma affine_div4 (ma ca xa d0 d1 : N)
    (hma : (ma mod 4 = 0)%N) (hca1 : (((ca + d0) / 2 + d1) mod 2 = 1)%N) :
    (ma mod 2 = 0)%N /\
    (((ma / 2) * xa + (ca + d0) / 2) + d1 =
     1 + ((ma / 4) * xa + ((ca + d0) / 2 + d1) / 2) * 2)%N.
Proof.
  assert (hma2 : (ma / 2 = (ma / 4) * 2)%N) by lia.
  assert (hma_mod2 : (ma mod 2 = 0)%N) by lia.
  assert (hca_eq : ((ca + d0) / 2 + d1 = 1 + (((ca + d0) / 2 + d1) / 2) * 2)%N) by lia.
  split; [exact hma_mod2 |].
  pose proof (affine_div2_odd_aux (ma / 4)%N (((ca + d0) / 2 + d1) / 2)%N xa) as H.
  rewrite <- hma2, <- hca_eq in H.
  rewrite <- N.add_assoc. exact H.
Qed.

Lemma evalAffineScan_sound :
    forall (ts : list nat) (ma ca mb cb : N) (u : list Word)
           (ma' ca' mb' cb' : N) (v : list Word) (g : nat) (xa xb : N),
      evalAffineScan ts ma ca mb cb u = Some (ma', ca', mb', cb', v, g) ->
      Scan (ma * xa + ca)%N (mb * xb + cb)%N u (ma' * xa + ca')%N (mb' * xb + cb')%N v g.
Proof.
  induction ts as [| t ts ih]; intros ma ca mb cb u ma' ca' mb' cb' v g xa xb h.
  - cbn [evalAffineScan] in h.
    destruct u as [| w0 u']; [| discriminate].
    destruct (N.leb_spec0 1 cb) as [hcb | _]; [| discriminate].
    inversion h; subst.
    exact (Scan_nil _ _ (affine_b_ge mb' xb cb' 1 hcb)).
  - cbn [evalAffineScan] in h.
    destruct t as [| [| [| [| [| [| t]]]]]].
    + (* t = 0: T *)
      destruct u as [| w0 u']; [discriminate |].
      destruct w0; try discriminate.
      destruct (N.leb_spec0 2 cb) as [hcb | _]; [| discriminate].
      destruct (evalAffineScan ts (ma * 2)%N (1 + ca * 2)%N (mb * 2)%N ((cb - 1) * 2)%N u')
        as [[[[[[ma1 ca1] mb1] cb1] v1] g1] |] eqn:hrec; [| discriminate].
      inversion h; subst.
      pose proof (ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec) as hI.
      rewrite (affine_mul2_a ma ca xa), (affine_mul2_b0 mb cb xb hcb) in hI.
      exact (Scan_T (affine_b_ge mb xb cb 2 hcb) hI).
    + (* t = 1: VK0 *)
      destruct u as [| [| |] [| [| |] u']]; try discriminate.
      destruct ((2 <=? cb)%N && (mb mod 2 =? 0)%N && (cb mod 2 =? 0)%N) eqn:hcond; [| discriminate].
      apply Bool.andb_true_iff in hcond as [hcond hcb2].
      apply Bool.andb_true_iff in hcond as [hcb hmb].
      apply N.leb_le in hcb. apply N.eqb_eq in hmb. apply N.eqb_eq in hcb2.
      destruct (evalAffineScan ts ma ca mb (cb - 1)%N u')
        as [[[[[[ma1 ca1] mb1] cb1] v1] g1] |] eqn:hrec; [| discriminate].
      inversion h; subst.
      pose proof (ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec) as hI.
      destruct (affine_vk0 mb cb xb hcb hmb hcb2) as [hk [heq1 heq2]].
      rewrite heq1. rewrite heq2 in hI.
      exact (Scan_VK0 hk hI).
    + (* t = 2: VK1 *)
      destruct u as [| [| |] [| [| |] u']]; try discriminate.
      destruct ((3 <=? cb)%N && (mb mod 2 =? 0)%N && (cb mod 2 =? 1)%N) eqn:hcond; [| discriminate].
      apply Bool.andb_true_iff in hcond as [hcond hcb2].
      apply Bool.andb_true_iff in hcond as [hcb hmb].
      apply N.leb_le in hcb. apply N.eqb_eq in hmb. apply N.eqb_eq in hcb2.
      destruct (evalAffineScan ts ma ca mb (cb - 2)%N u')
        as [[[[[[ma1 ca1] mb1] cb1] v1] g1] |] eqn:hrec; [| discriminate].
      inversion h; subst.
      pose proof (ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec) as hI.
      destruct (affine_vk1 mb cb xb hcb hmb hcb2) as [hk [heq1 heq2]].
      rewrite heq1. rewrite heq2 in hI.
      exact (Scan_VK1 hk hI).
    + (* t = 3: D *)
      destruct u as [| w0 u']; [discriminate |].
      destruct (word_is_not_V w0 && (ma mod 2 =? 0)%N && ((ca + dVal w0) mod 2 =? 0)%N
                && (2 <=? cb)%N && (mb mod 2 =? 0)%N) eqn:hcond; [| discriminate].
      apply Bool.andb_true_iff in hcond as [hcond hmb].
      apply Bool.andb_true_iff in hcond as [hcond hcb].
      apply Bool.andb_true_iff in hcond as [hcond hca].
      apply Bool.andb_true_iff in hcond as [hw0 hma].
      apply word_is_not_V_iff in hw0.
      apply N.eqb_eq in hma. apply N.eqb_eq in hca.
      apply N.leb_le in hcb. apply N.eqb_eq in hmb.
      destruct (evalAffineScan ts (ma / 2)%N ((ca + dVal w0) / 2)%N (mb / 2)%N (cb / 2)%N u')
        as [[[[[[ma1 ca1] mb1] cb1] v1] g1] |] eqn:hrec; [| discriminate].
      inversion h; subst.
      pose proof (ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec) as hI.
      pose proof (affine_div2_even ma ca xa (dVal w0) hma hca) as hq1.
      destruct (affine_div2_b mb cb xb hmb) as [hdiv hmod].
      rewrite hdiv in hI.
      pose proof (Scan_D hw0 hq1 (affine_b_ge mb xb cb 2 hcb) hI) as hD.
      rewrite hmod in hD. exact hD.
    + (* t = 4: P0 *)
      destruct u as [| w0 [| w1 u']]; try discriminate.
      destruct (word_is_not_V w0 && word_is_not_V w1 && (ma mod 4 =? 0)%N
                && ((ca + dVal w0) mod 2 =? 0)%N
                && (((ca + dVal w0) / 2 + dVal w1) mod 2 =? 1)%N && (2 <=? cb)%N) eqn:hcond;
        [| discriminate].
      apply Bool.andb_true_iff in hcond as [hcond hcb].
      apply Bool.andb_true_iff in hcond as [hcond hca1].
      apply Bool.andb_true_iff in hcond as [hcond hca0].
      apply Bool.andb_true_iff in hcond as [hcond hma].
      apply Bool.andb_true_iff in hcond as [hw0 hw1].
      apply word_is_not_V_iff in hw0. apply word_is_not_V_iff in hw1.
      apply N.eqb_eq in hma. apply N.eqb_eq in hca0. apply N.eqb_eq in hca1.
      apply N.leb_le in hcb.
      destruct (evalAffineScan ts (ma / 4)%N (((ca + dVal w0) / 2 + dVal w1) / 2)%N
                               (mb * 2)%N ((cb - 1) * 2)%N u')
        as [[[[[[ma1 ca1] mb1] cb1] v1] g1] |] eqn:hrec; [| discriminate].
      inversion h; subst.
      pose proof (ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec) as hI.
      destruct (affine_div4 ma ca xa (dVal w0) (dVal w1) hma hca1) as [hma2 hq2].
      pose proof (affine_div2_even ma ca xa (dVal w0) hma2 hca0) as hq1.
      rewrite (affine_mul2_b0 mb cb xb hcb) in hI.
      exact (Scan_P0 hw0 hw1 hq1 hq2 (affine_b_ge mb xb cb 2 hcb) hI).
    + (* t = 5: P1 *)
      destruct u as [| w0 [| w1 u']]; try discriminate.
      destruct (word_is_not_V w0 && word_is_not_V w1 && (ma mod 4 =? 0)%N
                && ((ca + dVal w0) mod 2 =? 1)%N
                && (((ca + dVal w0) / 2 + dVal w1) mod 2 =? 1)%N && (2 <=? cb)%N) eqn:hcond;
        [| discriminate].
      apply Bool.andb_true_iff in hcond as [hcond hcb].
      apply Bool.andb_true_iff in hcond as [hcond hca1].
      apply Bool.andb_true_iff in hcond as [hcond hca0].
      apply Bool.andb_true_iff in hcond as [hcond hma].
      apply Bool.andb_true_iff in hcond as [hw0 hw1].
      apply word_is_not_V_iff in hw0. apply word_is_not_V_iff in hw1.
      apply N.eqb_eq in hma. apply N.eqb_eq in hca0. apply N.eqb_eq in hca1.
      apply N.leb_le in hcb.
      destruct (evalAffineScan ts (ma / 4)%N (((ca + dVal w0) / 2 + dVal w1) / 2)%N
                               (mb * 2)%N (1 + (cb - 1) * 2)%N u')
        as [[[[[[ma1 ca1] mb1] cb1] v1] g1] |] eqn:hrec; [| discriminate].
      inversion h; subst.
      pose proof (ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec) as hI.
      destruct (affine_div4 ma ca xa (dVal w0) (dVal w1) hma hca1) as [hma2 hq2].
      pose proof (affine_div2_odd ma ca xa (dVal w0) hma2 hca0) as hq1.
      rewrite (affine_mul2_b1 mb cb xb hcb) in hI.
      exact (Scan_P1 hw0 hw1 hq1 hq2 (affine_b_ge mb xb cb 2 hcb) hI).
    + discriminate.
Qed.

Definition checkAffineScan (ts : list nat) (ma ca mb cb : N) (u : list Word)
    (ma' ca' mb' cb' : N) (v : list Word) (g : nat) : bool :=
  match evalAffineScan ts ma ca mb cb u with
  | Some (ma1, ca1, mb1, cb1, v1, g1) =>
    (ma1 =? ma')%N && (ca1 =? ca')%N && (mb1 =? mb')%N && (cb1 =? cb')%N
    && list_word_eqb v1 v && Nat.eqb g1 g
  | None => false
  end.

Lemma checkAffineScan_sound (ts : list nat) (ma ca mb cb : N) (u : list Word)
    (ma' ca' mb' cb' : N) (v : list Word) (g : nat) (xa xb : N)
    (h : checkAffineScan ts ma ca mb cb u ma' ca' mb' cb' v g = true) :
    Scan (ma * xa + ca)%N (mb * xb + cb)%N u (ma' * xa + ca')%N (mb' * xb + cb')%N v g.
Proof.
  unfold checkAffineScan in h.
  destruct (evalAffineScan ts ma ca mb cb u)
    as [[[[[[ma1 ca1] mb1] cb1] v1] g1] |] eqn:hrec; [| discriminate].
  apply Bool.andb_true_iff in h as [h hg].
  apply Bool.andb_true_iff in h as [h hv].
  apply Bool.andb_true_iff in h as [h hcb].
  apply Bool.andb_true_iff in h as [h hmb].
  apply Bool.andb_true_iff in h as [hma hca].
  apply N.eqb_eq in hma. apply N.eqb_eq in hca.
  apply N.eqb_eq in hmb. apply N.eqb_eq in hcb.
  apply list_word_eqb_eq in hv. apply Nat.eqb_eq in hg.
  subst.
  exact (evalAffineScan_sound ts ma ca mb cb u ma' ca' mb' cb' v g xa xb hrec).
Qed.

Definition checkStep (n : nat) (ts : list nat) (u da u' : list Word) : bool :=
  match evalAffineScan ts 0%N 0%N 0%N 126%N (u ++ repeat K n) with
  | Some (0%N, 0%N, 0%N, b', v, _) => checkDg b' da && list_word_eqb u' (V :: (v ++ da))
  | _ => false
  end.

Lemma checkStep_sound (n : nat) (ts : list nat) (u da u' : list Word)
    (h : checkStep n ts u da u' = true) : Step u u'.
Proof.
  unfold checkStep in h.
  destruct (evalAffineScan ts 0%N 0%N 0%N 126%N (u ++ repeat K n))
    as [[[[[[ma' ca'] mb'] b'] v] g] |] eqn:hrec; [| discriminate].
  destruct ma'; [| discriminate].
  destruct ca'; [| discriminate].
  destruct mb'; [| discriminate].
  apply Bool.andb_true_iff in h as [hDg hu'].
  apply list_word_eqb_eq in hu'.
  pose proof (evalAffineScan_sound ts 0%N 0%N 0%N 126%N (u ++ repeat K n) 0%N 0%N 0%N b' v g 0%N 0%N hrec) as hScan.
  cbn [N.mul N.add] in hScan.
  exists n, b', v, da, (length da), g.
  split; [exact hScan | split; [exact (checkDg_sound da b' hDg) | exact hu']].
Qed.

(* Section 4: Algebraic Bounds *)

Lemma zW_nonneg_and_le_two (u : list Word) :
    (0 <= zW u)%Q /\ (0 <= zW_V u)%Q /\ (zW u <= 2 * zW_V u)%Q.
Proof.
  induction u as [| a u [h1 [h2 h3]]].
  - cbn [zW zW_V zWPair fst snd]. lra.
  - destruct a;
      rewrite ?zW_cons_V, ?zW_V_cons_V, ?zW_cons_K, ?zW_V_cons_K, ?zW_cons_Q, ?zW_V_cons_Q;
      lra.
Qed.

Lemma zW_nonneg (u : list Word) : (0 <= zW u)%Q.
Proof. exact (proj1 (zW_nonneg_and_le_two u)). Qed.

Lemma zW_V_nonneg (u : list Word) : (0 <= zW_V u)%Q.
Proof. exact (proj1 (proj2 (zW_nonneg_and_le_two u))). Qed.

Lemma zW_le_two_zW_V (u : list Word) : (zW u <= 2 * zW_V u)%Q.
Proof. exact (proj2 (proj2 (zW_nonneg_and_le_two u))). Qed.

Lemma z10_z12_le_zW (u : list Word) : (2 * z10 u + z12 u <= 2 * zW u)%Q.
Proof.
  induction u as [| a u ih].
  - cbn [z10 z12 zW zWPair fst]. lra.
  - pose proof (zW_le_two_zW_V u) as hle.
    destruct a; cbn [z10 z12]; rewrite ?zW_cons_V, ?zW_cons_K, ?zW_cons_Q; lra.
Qed.

Lemma z10_z12_le_four_zW_V (u : list Word) : (2 * z10 u + z12 u <= 4 * zW_V u)%Q.
Proof.
  pose proof (z10_z12_le_zW u) as h1.
  pose proof (zW_le_two_zW_V u) as h2.
  lra.
Qed.

Lemma z13_pos (u : list Word) : (0 < z13 u)%Q.
Proof.
  induction u as [| a u ih].
  - cbn [z13]. lra.
  - destruct a; cbn [z13]; lra.
Qed.

Lemma z13_append (u v : list Word) : (z13 (u ++ v) == z13 u * z13 v)%Q.
Proof.
  induction u as [| a u ih].
  - cbn [List.app z13]. lra.
  - destruct a; cbn [List.app z13]; rewrite ih; lra.
Qed.

Lemma zW_append_both (u t : list Word) :
    (zW (u ++ t) <= zW u + 2 * z13 u * zW_V t)%Q /\
    (zW_V (u ++ t) <= zW_V u + z13 u * zW_V t)%Q.
Proof.
  induction u as [| a u [ihW ihWV]].
  - cbn [List.app z13 zW zW_V zWPair fst snd].
    pose proof (zW_le_two_zW_V t) as hle. lra.
  - destruct a; cbn [List.app z13];
      rewrite ?zW_cons_V, ?zW_V_cons_V, ?zW_cons_K, ?zW_V_cons_K, ?zW_cons_Q, ?zW_V_cons_Q;
      lra.
Qed.

Lemma zW_V_append (u t : list Word) : (zW_V (u ++ t) <= zW_V u + z13 u * zW_V t)%Q.
Proof. exact (proj2 (zW_append_both u t)). Qed.

Definition cPar (b : N) : Rat :=
  if (b mod 2 =? 1)%N then (1#7)%Q else (2#7)%Q.

Lemma cPar_bounds (b : N) : ((1#7) <= cPar b)%Q /\ (cPar b <= (2#7))%Q.
Proof.
  unfold cPar. destruct (b mod 2 =? 1)%N; lra.
Qed.

Lemma cPar_even (k : N) : cPar (k * 2)%N = (2#7)%Q.
Proof.
  unfold cPar. replace ((k * 2) mod 2)%N with 0%N by lia. reflexivity.
Qed.

Lemma cPar_odd (k : N) : cPar (1 + k * 2)%N = (1#7)%Q.
Proof.
  unfold cPar. replace ((1 + k * 2) mod 2)%N with 1%N by lia. reflexivity.
Qed.

Lemma Scan_zW_contract {a b a' b' : N} {g : nat} {u v : list Word}
    (h : Scan a b u a' b' v g) :
    (zW_V v <= (6#7) * zW u + cPar b)%Q.
Proof.
  induction h as
    [ a b _
    | a b a' b' g u v _ _ ih
    | a k a' b' g u v _ _ ih
    | a k a' b' g u v _ _ ih
    | a b q1 a' b' g w0 u v hw0 _ _ _ ih
    | a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih
    | a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih ].
  - pose proof (proj1 (cPar_bounds b)) as hc.
    cbn [zW_V zW zWPair fst snd]. lra.
  - pose proof (proj1 (cPar_bounds b)) as hc_in.
    rewrite cPar_even in ih.
    pose proof (zW_le_two_zW_V u) as hle.
    rewrite zW_V_cons_V, zW_cons_V. lra.
  - rewrite cPar_odd in ih.
    rewrite cPar_even.
    rewrite !zW_V_cons_K, !zW_cons_V, !zW_V_cons_K. lra.
  - rewrite cPar_odd in ih.
    rewrite cPar_odd.
    rewrite !zW_V_cons_Q, !zW_cons_V, !zW_V_cons_K. lra.
  - pose proof (proj2 (cPar_bounds (b / 2)%N)) as hc_next.
    pose proof (zW_le_two_zW_V v) as hle.
    rewrite (zW_cons_d hw0).
    unfold cPar.
    destruct (b mod 2 =? 1)%N; rewrite ?zW_V_cons_Q, ?zW_V_cons_K; lra.
  - pose proof (proj1 (cPar_bounds b)) as hc_in.
    pose proof (proj2 (cPar_bounds ((b - 1) * 2)%N)) as hc_next.
    pose proof (zW_nonneg u) as hzW.
    rewrite (zW_cons_d hw0), (zW_cons_d hw1), zW_V_cons_V. lra.
  - pose proof (proj1 (cPar_bounds b)) as hc_in.
    pose proof (proj2 (cPar_bounds (1 + (b - 1) * 2)%N)) as hc_next.
    pose proof (zW_nonneg u) as hzW.
    rewrite (zW_cons_d hw0), (zW_cons_d hw1), zW_V_cons_V. lra.
Qed.

Lemma dCount_bound (v : list Word) :
    (zW v <= (3#2) * (qpow2 (dCount v) - 1))%Q /\
    (zW_V v <= qpow2 (dCount v) - 1)%Q.
Proof.
  induction v as [| a v [ihW ihWV]].
  - cbn [dCount zW zW_V zWPair fst snd]. rewrite qpow2_0. lra.
  - pose proof (qpow2_ge_1 (dCount v)) as hpow_pos.
    destruct a.
    + cbn [dCount]. rewrite zW_cons_V, zW_V_cons_V. lra.
    + cbn [dCount]. rewrite qpow2_1_add, zW_cons_K, zW_V_cons_K. lra.
    + cbn [dCount]. rewrite qpow2_1_add, zW_cons_Q, zW_V_cons_Q. lra.
Qed.

Lemma dCount_bound_WV (v : list Word) :
    (zW_V v <= (3#4) * qpow2 (dCount v) + (1#4))%Q.
Proof.
  destruct v as [| a u].
  - cbn [dCount zW_V zWPair snd]. rewrite qpow2_0. lra.
  - destruct (dCount_bound u) as [hW hWV].
    pose proof (qpow2_ge_1 (dCount u)) as hpow_pos.
    destruct a.
    + cbn [dCount]. rewrite zW_V_cons_V. lra.
    + cbn [dCount]. rewrite qpow2_1_add, zW_V_cons_K. lra.
    + cbn [dCount]. rewrite qpow2_1_add, zW_V_cons_Q. lra.
Qed.

Lemma zDg_not_V {A : N} {m : nat} {u : list Word} (h : zDg A m (V :: u)) : False.
Proof. inversion h. Qed.

Lemma zDg_cons_inv {A : N} {m : nat} {w0 : Word} {u : list Word}
    (h : zDg A m (w0 :: u)) :
    exists A' m', zDg A' m' u /\ A = (dVal w0 + A' * 2)%N /\ m = 1 + m'.
Proof.
  inversion h as [| A' H' u' hD | A' H' u' hD]; subst.
  - exists A', H'. split; [exact hD | split; [cbn [dVal]; lia | reflexivity]].
  - exists A', H'. split; [exact hD | split; [cbn [dVal]; lia | reflexivity]].
Qed.

Lemma zDg_Scan_dCount {a b a' b' : N} {g : nat} {u v : list Word}
    (hS : Scan a b u a' b' v g) :
    forall {A : N} {m : nat}, zDg A m u -> dCount v + 2 * g = m.
Proof.
  induction hS as
    [ a b _
    | a b a' b' g u v _ _ _
    | a k a' b' g u v _ _ _
    | a k a' b' g u v _ _ _
    | a b q1 a' b' g w0 u v _ _ _ _ ih
    | a b q1 q2 a' b' g w0 w1 u v _ _ _ _ _ _ ih
    | a b q1 q2 a' b' g w0 w1 u v _ _ _ _ _ _ ih ];
    intros A m hDg.
  - inversion hDg; reflexivity.
  - exfalso; exact (zDg_not_V hDg).
  - exfalso; exact (zDg_not_V hDg).
  - exfalso; exact (zDg_not_V hDg).
  - destruct (zDg_cons_inv hDg) as [A' [m' [hD' [_ ->]]]].
    pose proof (ih _ _ hD') as hI.
    assert (hd_out : dCount ((if (b mod 2 =? 1)%N then Q_w else K) :: v) = 1 + dCount v)
      by (destruct (b mod 2 =? 1)%N; reflexivity).
    rewrite hd_out. lia.
  - destruct (zDg_cons_inv hDg) as [A1 [m1 [hD1 [_ ->]]]].
    destruct (zDg_cons_inv hD1) as [A2 [m2 [hD2 [_ ->]]]].
    pose proof (ih _ _ hD2) as hI.
    cbn [dCount]. lia.
  - destruct (zDg_cons_inv hDg) as [A1 [m1 [hD1 [_ ->]]]].
    destruct (zDg_cons_inv hD1) as [A2 [m2 [hD2 [_ ->]]]].
    pose proof (ih _ _ hD2) as hI.
    cbn [dCount]. lia.
Qed.

Lemma zDg_z13_z10 {A : N} {m : nat} {u : list Word} (h : zDg A m u) :
    (z13 u == qpow2 m)%Q /\ (z10 u == qpow2 m - 1)%Q.
Proof.
  induction h as [| A m u _ [ih13 ih10] | A m u _ [ih13 ih10]].
  - cbn [z13 z10]. rewrite qpow2_0. lra.
  - cbn [z13 z10]. rewrite qpow2_1_add. lra.
  - cbn [z13 z10]. rewrite qpow2_1_add. lra.
Qed.

Lemma z13_Scan {a b a' b' : N} {g : nat} {u v : list Word}
    (h : Scan a b u a' b' v g) :
    (z13 v * qpow2 (3 * g) == z13 u)%Q.
Proof.
  induction h as
    [ a b _
    | a b a' b' g u v _ _ ih
    | a k a' b' g u v _ _ ih
    | a k a' b' g u v _ _ ih
    | a b q1 a' b' g w0 u v hw0 _ _ _ ih
    | a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih
    | a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih ].
  - cbn [z13 Nat.mul]. rewrite qpow2_0. lra.
  - cbn [z13]. lra.
  - cbn [z13]. lra.
  - cbn [z13]. lra.
  - assert (hv : z13 ((if (b mod 2 =? 1)%N then Q_w else K) :: v) = (2 * z13 v)%Q)
      by (destruct (b mod 2 =? 1)%N; reflexivity).
    rewrite hv, (z13_cons_d hw0). lra.
  - rewrite (z13_cons_d hw0), (z13_cons_d hw1).
    replace (3 * (1 + g)) with (3 + 3 * g) by lia.
    rewrite qpow2_add. change (qpow2 3) with 8%Q.
    cbn [z13]. lra.
  - rewrite (z13_cons_d hw0), (z13_cons_d hw1).
    replace (3 * (1 + g)) with (3 + 3 * g) by lia.
    rewrite qpow2_add. change (qpow2 3) with 8%Q.
    cbn [z13]. lra.
Qed.

Lemma Parse_P_rel (a q2 d0 d1 : N)
    (h : ((a + d0) / 2 + d1 = 1 + q2 * 2)%N) :
    exists r1 : N, (r1 <= 1)%N /\ (4 * q2 + 2 + r1 = a + d0 + 2 * d1)%N.
Proof.
  exists ((a + d0) mod 2)%N. lia.
Qed.

Lemma Parse_la {a a' : N} {g : nat} {u : list Word} (h : Parse a u a' g) :
    (0 <= (qN a' + 1) * z13 u - (qN a + 1))%Q /\
    ((qN a' + 1) * z13 u - (qN a + 1) <= 2 * z10 u)%Q.
Proof.
  induction h as
    [ a
    | a a' g u _ [ih1 ih2]
    | a a' g u _ [ih1 ih2]
    | a q1 a' g w0 u hw0 hq1 _ [ih1 ih2]
    | a q2 a' g w0 w1 u hw0 hw1 hq2 _ [ih1 ih2] ].
  - cbn [z13 z10]. lra.
  - cbn [z13 z10]. rewrite qN_add, qN_mul in ih1, ih2. norm_qN. lra.
  - cbn [z13 z10]. lra.
  - rewrite (z13_cons_d hw0), (z10_cons_d hw0).
    apply qN_eq_iff in hq1. rewrite qN_add, qN_mul in hq1. norm_qN.
    pose proof (qN_nonneg (dVal w0)) as hd0.
    pose proof (proj1 (qN_le_iff _ _) (dVal_le_one w0)) as hd1. norm_qN.
    lra.
  - rewrite (z13_cons_d hw0), (z13_cons_d hw1), (z10_cons_d hw0), (z10_cons_d hw1).
    destruct (Parse_P_rel a q2 (dVal w0) (dVal w1) hq2) as [r1 [hr1 hrel]].
    apply qN_le_iff in hr1. apply qN_eq_iff in hrel.
    rewrite !qN_add, !qN_mul in hrel. norm_qN.
    pose proof (qN_nonneg r1) as hr0.
    pose proof (qN_nonneg (dVal w0)) as hd0_0.
    pose proof (proj1 (qN_le_iff _ _) (dVal_le_one w0)) as hd0_1.
    pose proof (qN_nonneg (dVal w1)) as hd1_0.
    pose proof (proj1 (qN_le_iff _ _) (dVal_le_one w1)) as hd1_1.
    norm_qN. lra.
Qed.

Lemma Parse_zDg_D_step (a q1 a' d0 A' p : N)
    (hq1 : (a + d0 = q1 * 2)%N)
    (hL : (a' * p <= q1 + A')%N)
    (hR : (q1 + A' < (a' + 1) * p)%N) :
    (a' * (p + p) <= a + (d0 + A' * 2))%N /\
    (a + (d0 + A' * 2) < (a' + 1) * (p + p))%N.
Proof. lia. Qed.

Lemma Parse_zDg_P_step (a q2 a' d0 d1 A2 p : N)
    (hq2 : ((a + d0) / 2 + d1 = 1 + q2 * 2)%N)
    (hL : (a' * p <= q2 + A2)%N)
    (hR : (q2 + A2 < (a' + 1) * p)%N) :
    (a' * (p + p + (p + p)) <= a + (d0 + (d1 + A2 * 2) * 2))%N /\
    (a + (d0 + (d1 + A2 * 2) * 2) < (a' + 1) * (p + p + (p + p)))%N.
Proof. lia. Qed.

Lemma Parse_zDg_a {a a' : N} {g : nat} {u : list Word} (hP : Parse a u a' g) :
    forall {A : N} {m : nat},
      zDg A m u ->
      (a' * 2 ^ (N.of_nat m) <= a + A)%N /\ (a + A < (a' + 1) * 2 ^ (N.of_nat m))%N.
Proof.
  induction hP as
    [ a
    | a a' g u _ _
    | a a' g u _ _
    | a q1 a' g w0 u _ hq1 _ ih
    | a q2 a' g w0 w1 u _ _ hq2 _ ih ];
    intros A m hDg.
  - inversion hDg; subst. cbn. lia.
  - exfalso; exact (zDg_not_V hDg).
  - exfalso; exact (zDg_not_V hDg).
  - destruct (zDg_cons_inv hDg) as [A' [m' [hD' [-> ->]]]].
    destruct (ih _ _ hD') as [hL hR].
    rewrite zPow1_N.
    exact (Parse_zDg_D_step a q1 a' (dVal w0) A' (2 ^ (N.of_nat m'))%N hq1 hL hR).
  - destruct (zDg_cons_inv hDg) as [A1 [m1 [hD1 [-> ->]]]].
    destruct (zDg_cons_inv hD1) as [A2 [m2 [hD2 [-> ->]]]].
    destruct (ih _ _ hD2) as [hL hR].
    rewrite (zPow1_N (1 + m2)), (zPow1_N m2).
    exact (Parse_zDg_P_step a q2 a' (dVal w0) (dVal w1) A2 (2 ^ (N.of_nat m2))%N hq2 hL hR).
Qed.

Lemma Scan_delta {a b a' b' : N} {g : nat} {u v : list Word}
    (h : Scan a b u a' b' v g) :
    (-1 <= (qN b - 2) - (qN b' - 2) * z13 v)%Q /\
    ((qN b - 2) - (qN b' - 2) * z13 v <= 2 * z10 v + z12 v)%Q.
Proof.
  induction h as
    [ a b _
    | a b a' b' g u v hb _ [ih1 ih2]
    | a k a' b' g u v hk _ [ih1 ih2]
    | a k a' b' g u v hk _ [ih1 ih2]
    | a b q1 a' b' g w0 u v _ _ _ _ [ih1 ih2]
    | a b q1 q2 a' b' g w0 w1 u v _ _ _ _ hb _ [ih1 ih2]
    | a b q1 q2 a' b' g w0 w1 u v _ _ _ _ hb _ [ih1 ih2] ].
  - cbn [z13 z10 z12]. lra.
  - cbn [z13 z10 z12].
    rewrite qN_mul, qN_sub in ih1, ih2 by lia. norm_qN. lra.
  - cbn [z13 z10 z12].
    rewrite qN_add, qN_mul, qN_sub in ih1, ih2 by lia.
    rewrite qN_mul. norm_qN. lra.
  - cbn [z13 z10 z12].
    rewrite qN_add, qN_mul, qN_sub in ih1, ih2 by lia.
    rewrite qN_add, qN_mul. norm_qN. lra.
  - destruct (z0U b) as [[k ->] | [k ->]].
    + replace ((k * 2) mod 2)%N with 0%N by lia.
      replace ((k * 2) / 2)%N with k in ih1, ih2 by lia.
      cbn [N.eqb z13 z10 z12]. rewrite qN_mul. norm_qN. lra.
    + replace ((1 + k * 2) mod 2)%N with 1%N by lia.
      replace ((1 + k * 2) / 2)%N with k in ih1, ih2 by lia.
      cbn [N.eqb Pos.eqb z13 z10 z12]. rewrite qN_add, qN_mul. norm_qN. lra.
  - cbn [z13 z10 z12].
    rewrite qN_mul, qN_sub in ih1, ih2 by lia. norm_qN. lra.
  - cbn [z13 z10 z12].
    rewrite qN_add, qN_mul, qN_sub in ih1, ih2 by lia. norm_qN. lra.
Qed.

Fixpoint vCount (u : list Word) : nat :=
  match u with
  | [] => 0
  | V :: u' => 1 + vCount u'
  | _ :: u' => vCount u'
  end.

Lemma z13_mul_pow_vCount (u : list Word) :
    (z13 u * qpow2 (vCount u) == qpow2 (dCount u))%Q.
Proof.
  induction u as [| w u ih].
  - cbn [z13 vCount dCount]. rewrite qpow2_0. lra.
  - destruct w.
    + cbn [z13 vCount dCount]. rewrite qpow2_1_add. lra.
    + cbn [z13 vCount dCount]. rewrite qpow2_1_add. lra.
    + cbn [z13 vCount dCount]. rewrite qpow2_1_add. lra.
Qed.

Definition checkZ13Pow (u : list Word) (L target : nat) : bool :=
  Nat.eqb (dCount u + L) (vCount u + target).

Lemma checkZ13Pow_sound (u : list Word) (L target : nat)
    (h : checkZ13Pow u L target = true) :
    (z13 u * qpow2 L == qpow2 target)%Q.
Proof.
  unfold checkZ13Pow in h.
  apply Nat.eqb_eq in h.
  pose proof (z13_mul_pow_vCount u) as h_vc.
  pose proof (qpow2_pos (vCount u)) as h_pos.
  assert (h_pow : (qpow2 (dCount u) * qpow2 L == qpow2 (vCount u) * qpow2 target)%Q).
  { rewrite <- !qpow2_add, h. reflexivity. }
  nra.
Qed.

Fixpoint zWNat (u : list Word) : N * N :=
  match u with
  | [] => (0%N, 0%N)
  | V :: u' =>
    let p := zWNat u' in
    ((4 * snd p)%N, (2 * snd p)%N)
  | K :: u' =>
    let p := zWNat u' in
    let p4 := (4 ^ (N.of_nat (length u')))%N in
    ((6 * p4 + 8 * fst p)%N, (4 * p4 + 4 * fst p)%N)
  | Q_w :: u' =>
    let p := zWNat u' in
    let p4 := (4 ^ (N.of_nat (length u')))%N in
    ((6 * p4 + 8 * fst p)%N, (3 * p4 + 4 * fst p)%N)
  end.

Lemma pow4_S_N (k : nat) : (4 ^ (N.of_nat (S k)) = 4 * 4 ^ (N.of_nat k))%N.
Proof.
  rewrite Nat2N.inj_succ, N.pow_succ_r'. reflexivity.
Qed.

Lemma zWNat_sound (u : list Word) :
    (zW u * qN (4 ^ (N.of_nat (length u)))%N == qN (fst (zWNat u)))%Q /\
    (zW_V u * qN (4 ^ (N.of_nat (length u)))%N == qN (snd (zWNat u)))%Q.
Proof.
  induction u as [| w u [hW hWV]].
  - cbn [zWNat length fst snd zW zW_V zWPair]. norm_qN. lra.
  - cbn [length]. rewrite pow4_S_N, qN_mul. norm_qN.
    destruct w.
    + cbn [zWNat fst snd]. rewrite zW_cons_V, zW_V_cons_V, !qN_mul. norm_qN. lra.
    + cbn [zWNat fst snd]. rewrite zW_cons_K, zW_V_cons_K, !qN_add, !qN_mul. norm_qN. lra.
    + cbn [zWNat fst snd]. rewrite zW_cons_Q, zW_V_cons_Q, !qN_add, !qN_mul. norm_qN. lra.
Qed.

Lemma le_of_mul_pow4_le {x y : Rat} {n : nat}
    (h : (x * qN (4 ^ (N.of_nat n))%N <= y * qN (4 ^ (N.of_nat n))%N)%Q) :
    (x <= y)%Q.
Proof.
  assert (hp : (0 < 4 ^ (N.of_nat n))%N) by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
  apply qN_lt_iff in hp. norm_qN.
  nra.
Qed.

Definition checkZWLe (u : list Word) (num den : N) : bool :=
  (fst (zWNat u) * den <=? num * 4 ^ (N.of_nat (length u)))%N.

Lemma checkZWLe_sound (u : list Word) (num den : N)
    (h : checkZWLe u num den = true) :
    (zW u * qN den <= qN num)%Q.
Proof.
  unfold checkZWLe in h.
  apply N.leb_le, qN_le_iff in h.
  rewrite !qN_mul in h.
  pose proof (proj1 (zWNat_sound u)) as hW.
  apply (le_of_mul_pow4_le (n := length u)).
  nra.
Qed.

Definition checkZWVLe (u : list Word) (num den : N) : bool :=
  (snd (zWNat u) * den <=? num * 4 ^ (N.of_nat (length u)))%N.

Lemma checkZWVLe_sound (u : list Word) (num den : N)
    (h : checkZWVLe u num den = true) :
    (zW_V u * qN den <= qN num)%Q.
Proof.
  unfold checkZWVLe in h.
  apply N.leb_le, qN_le_iff in h.
  rewrite !qN_mul in h.
  pose proof (proj2 (zWNat_sound u)) as hWV.
  apply (le_of_mul_pow4_le (n := length u)).
  nra.
Qed.

Lemma z10_le_pow_len (u : list Word) :
    (z10 u <= qpow2 (length u) - 1)%Q.
Proof.
  induction u as [| w u ih].
  - cbn [z10 length]. rewrite qpow2_0. lra.
  - cbn [length]. rewrite qpow2_S.
    pose proof (qpow2_ge_1 (length u)) as hpos.
    destruct w; cbn [z10]; lra.
Qed.

Open Scope word_scope.


(* Section 5: Concrete Trajectory Constants and Initial Rounds *)

Definition u_0 : list Word := [K; K; K; K; V; K; Q; Q].
Definition tags_0 : list nat := [3; 3; 3; 3; 2; 5].
Definition da_0 : list Word := [Q; K; K; Q].
Definition n_0 : nat := 0.
Definition u_1 : list Word := [V; K; Q; Q; Q; Q; V; V; Q; K; K; Q].
Definition tags_1 : list nat := [1; 5; 5; 0; 0; 3; 3; 5].
Definition da_1 : list Word := [Q; K; Q; Q; Q; K; Q; Q; Q; Q].
Definition n_1 : nat := 0.
Definition u_2 : list Word := [V; K; V; V; V; V; V; K; Q; V; Q; K; Q; Q; Q; K; Q; Q; Q; Q].
Definition tags_2 : list nat := [1; 0; 0; 0; 0; 1; 3; 0; 4; 5; 4; 5; 5].
Definition da_2 : list Word := [Q; K; Q; Q; K; K; K; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_2 : nat := 0.
Definition u_3 : list Word := [V; K; V; V; V; V; V; K; V; Q; V; V; V; V; V; V; Q; K; Q; Q; K; K; K; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_3 : list nat := [1; 0; 0; 0; 0; 1; 0; 3; 0; 0; 0; 0; 0; 0; 3; 3; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_3 : list Word := [Q; K; Q; Q; K; K; Q; Q; Q; K; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_3 : nat := 0.
Definition u_4 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; Q; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; K; K; Q; Q; Q; K; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_4 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 3; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 4; 5; 5; 3; 5; 3; 4; 5; 5].
Definition da_4 : list Word := [Q; K; Q; Q; Q; Q; K; Q; K; K; K; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_4 : nat := 0.
Definition u_5 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; Q; V; K; V; V; K; V; V; V; K; V; V; V; V; Q; V; Q; V; V; V; Q; K; Q; Q; Q; Q; K; Q; K; K; K; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_5 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 3; 1; 0; 1; 0; 0; 1; 0; 0; 0; 0; 3; 0; 3; 0; 0; 0; 3; 3; 5; 3; 3; 5; 4; 3; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_5 : list Word := [Q; K; Q; Q; K; K; Q; K; K; Q; K; K; K; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_5 : nat := 0.
Definition u_6 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; K; K; V; V; K; V; V; V; K; V; V; V; V; V; K; V; K; V; V; V; K; Q; V; Q; Q; V; V; K; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; K; K; Q; K; K; Q; K; K; K; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_6 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 5; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 2; 0; 0; 1; 3; 0; 3; 3; 0; 1; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 3; 4; 4; 4; 3; 3; 4; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_6 : list Word := [Q; K; Q; Q; K; Q; K; K; K; Q; K; K; K; Q; K; Q; K; K; K; K; Q; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_6 : nat := 0.
Definition u_7 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; Q; V; V; V; K; V; Q; V; K; Q; V; K; V; V; K; V; V; K; V; V; V; K; V; K; V; V; V; K; Q; V; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; K; Q; K; K; K; Q; K; K; K; Q; K; Q; K; K; K; K; Q; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_7 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 3; 0; 0; 1; 0; 3; 0; 5; 2; 0; 1; 0; 1; 0; 0; 1; 2; 0; 0; 1; 3; 0; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 3; 3; 5; 3; 4; 5; 4; 4; 3; 3; 3; 4; 5; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_7 : list Word := [Q; K; Q; Q; Q; Q; Q; Q; K; Q; K; Q; Q; Q; Q; Q; K; Q; K; Q; K; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_7 : nat := 0.
Definition u_8 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; Q; V; V; K; V; V; K; V; V; V; K; V; Q; V; V; V; K; V; Q; V; V; K; V; V; K; V; V; V; K; V; K; K; V; Q; V; V; V; V; K; Q; Q; V; V; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; Q; Q; Q; Q; K; Q; K; Q; Q; Q; Q; Q; K; Q; K; Q; K; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_8 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 3; 0; 1; 0; 1; 0; 0; 1; 0; 3; 0; 0; 1; 0; 3; 0; 1; 0; 1; 0; 0; 1; 0; 5; 0; 3; 0; 0; 0; 1; 4; 0; 0; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 4; 3; 5; 5; 5; 3; 3; 3; 3; 3; 3; 5; 3; 5; 4; 4; 5; 3; 5; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_8 : list Word := [Q; K; Q; Q; Q; K; Q; K; Q; K; K; Q; K; Q; Q; Q; Q; K; Q; K; K; Q; K; Q; K; K; K; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_8 : nat := 0.
Definition u_9 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; K; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; K; V; K; V; V; K; V; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; Q; K; K; K; Q; Q; V; Q; V; V; V; V; Q; V; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; Q; K; Q; K; Q; K; K; Q; K; Q; Q; Q; Q; K; Q; K; K; Q; K; Q; K; K; K; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_9 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 2; 0; 1; 0; 0; 1; 0; 1; 0; 1; 0; 1; 2; 0; 1; 0; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 0; 0; 3; 3; 3; 3; 5; 0; 3; 0; 0; 0; 0; 3; 0; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 4; 3; 4; 5; 4; 3; 5; 5; 4; 3; 4; 4; 3; 3; 3; 3; 3; 3; 3; 4; 5; 4; 4; 5; 3; 5; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_9 : list Word := [Q; K; Q; Q; Q; K; Q; K; K; K; K; K; K; K; Q; Q; Q; Q; Q; Q; Q; K; Q; Q; K; Q; K; Q; Q; K; Q; K; K; Q; Q; Q; K; K; K; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_9 : nat := 0.
Definition u_10 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; K; V; Q; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; K; V; Q; V; V; K; V; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; V; K; Q; K; Q; V; V; K; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; K; V; V; V; K; V; V; K; Q; K; Q; K; K; Q; V; V; V; V; V; Q; V; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; Q; K; Q; K; K; K; K; K; K; K; Q; Q; Q; Q; Q; Q; Q; K; Q; Q; K; Q; K; Q; Q; K; Q; K; K; Q; Q; Q; K; K; K; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_10 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 3; 0; 1; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 3; 0; 1; 0; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 0; 0; 1; 3; 4; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 0; 1; 0; 0; 1; 0; 1; 3; 4; 3; 4; 0; 0; 0; 0; 0; 3; 0; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 4; 3; 4; 4; 3; 3; 3; 4; 5; 3; 3; 3; 4; 5; 4; 3; 5; 4; 3; 3; 3; 3; 4; 3; 4; 3; 3; 3; 4; 5; 4; 4; 5; 3; 5; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_10 : list Word := [Q; K; Q; Q; Q; K; Q; K; K; Q; K; K; Q; Q; Q; Q; Q; Q; K; K; K; Q; K; K; K; Q; Q; K; Q; Q; K; K; K; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; K; Q; K; Q; Q; Q; Q; K; K; Q; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_10 : nat := 0.
Definition u_11 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; K; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; K; V; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; V; K; V; Q; V; V; K; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; K; V; V; V; K; V; V; K; V; Q; V; K; V; V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; Q; Q; V; V; Q; Q; K; V; V; V; K; V; V; K; K; Q; K; V; K; V; K; K; K; V; V; V; V; V; Q; V; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; Q; K; Q; K; K; Q; K; K; Q; Q; Q; Q; Q; Q; K; K; K; Q; K; K; K; Q; Q; K; Q; Q; K; K; K; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; K; Q; K; Q; Q; Q; Q; K; K; Q; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_11 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 2; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 2; 0; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 0; 0; 1; 0; 3; 0; 1; 0; 0; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 0; 1; 0; 0; 1; 0; 1; 0; 3; 1; 0; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 4; 0; 0; 3; 5; 0; 0; 1; 0; 0; 5; 3; 3; 1; 0; 5; 3; 0; 0; 0; 0; 0; 3; 0; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 4; 3; 4; 3; 4; 4; 5; 3; 3; 4; 3; 4; 3; 3; 3; 5; 4; 4; 3; 4; 3; 4; 5; 4; 3; 5; 4; 3; 5; 5; 3; 4; 3; 3; 3; 3; 4; 5; 4; 4; 5; 3; 5; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_11 : list Word := [Q; K; Q; Q; Q; K; Q; K; K; K; Q; Q; K; Q; Q; Q; Q; K; Q; Q; K; K; Q; K; K; Q; Q; K; K; K; Q; K; K; K; Q; Q; Q; Q; K; Q; K; K; Q; K; K; Q; K; K; K; Q; Q; K; Q; K; Q; K; K; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; K; Q; K; Q; Q; Q; Q; K; K; Q; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_11 : nat := 0.
Definition u_12 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; Q; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; Q; V; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; V; K; V; V; K; V; K; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; K; V; V; V; K; V; V; K; V; V; K; K; V; V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; Q; Q; K; V; V; V; Q; V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; K; V; V; V; Q; Q; V; K; V; K; K; Q; V; V; V; K; V; K; V; V; V; K; V; V; K; V; V; Q; V; K; Q; K; K; V; V; V; V; V; Q; V; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; Q; K; Q; K; K; K; Q; Q; K; Q; Q; Q; Q; K; Q; Q; K; K; Q; K; K; Q; Q; K; K; K; Q; K; K; K; Q; Q; Q; Q; K; Q; K; K; Q; K; K; Q; K; K; K; Q; Q; K; Q; K; Q; K; K; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; K; Q; K; Q; Q; Q; Q; K; K; Q; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition tags_12 : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 3; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 3; 0; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 0; 0; 1; 0; 1; 2; 0; 0; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 0; 1; 0; 0; 1; 0; 1; 0; 0; 5; 0; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 4; 3; 0; 0; 0; 3; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 2; 0; 0; 0; 4; 1; 2; 4; 0; 0; 1; 2; 0; 0; 1; 0; 1; 0; 0; 3; 0; 5; 3; 3; 0; 0; 0; 0; 0; 3; 0; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 4; 3; 4; 3; 5; 5; 5; 5; 4; 5; 3; 4; 3; 5; 3; 3; 4; 3; 3; 3; 5; 5; 4; 3; 4; 3; 4; 3; 3; 3; 5; 4; 4; 3; 4; 3; 4; 5; 4; 3; 5; 4; 3; 3; 3; 3; 4; 3; 4; 3; 3; 3; 4; 5; 4; 4; 5; 3; 5; 5; 3; 4; 5; 3; 4; 5; 5].
Definition da_12 : list Word := [Q; K; Q; Q; Q; K; Q; K; K; K; K; Q; Q; K; K; K; K; Q; Q; Q; K; Q; Q; K; K; K; Q; K; K; Q; Q; K; Q; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; K; Q; Q; K; K; K; Q; K; K; K; Q; Q; Q; Q; K; K; K; Q; K; Q; K; Q; K; K; Q; K; K; K; Q; Q; K; Q; K; Q; K; K; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; K; Q; Q; Q; Q; Q; Q; K; Q; Q; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition n_12 : nat := 0.
Definition u_13 : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; V; K; V; V; K; V; Q; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; K; V; V; V; K; V; V; K; V; V; V; V; V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; V; K; V; V; V; K; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; Q; V; V; V; V; V; K; V; Q; V; V; V; V; K; V; Q; V; V; V; K; V; V; K; V; V; V; K; V; V; Q; Q; V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; K; V; V; V; V; V; V; Q; V; K; V; Q; Q; V; K; Q; K; V; V; V; K; V; K; V; K; K; Q; V; V; V; K; V; K; V; V; V; K; V; V; K; K; Q; K; V; K; V; K; K; Q; V; V; V; V; V; Q; V; V; Q; V; V; Q; V; V; V; Q; K; Q; Q; Q; K; Q; K; K; K; K; Q; Q; K; K; K; K; Q; Q; Q; K; Q; Q; K; K; K; Q; K; K; Q; Q; K; Q; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; K; Q; Q; K; K; K; Q; K; K; K; Q; Q; Q; Q; K; K; K; Q; K; Q; K; Q; K; K; Q; K; K; K; Q; Q; K; Q; K; Q; K; K; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; K; Q; Q; Q; Q; Q; Q; K; Q; Q; K; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].

Definition head_w : list Word := [V; K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; K; V].
Definition tags_head : list nat := [1; 0; 0; 0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0; 0; 1; 0; 1; 0; 1; 0; 1; 0].
Definition v_head : list Word := [K; V; V; V; V; V; K; V; V; K; V; V; V; V; V; V; K; V; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; K; V; V].
Definition a_head : N := 536870911%N.
Definition b_head : N := 65984224292%N.
Definition A_top : N := 128875438%N.

Definition s_base : list Word := [V; V; V; V; V; Q; V; V; Q; V; V; Q; V; V; V].
Definition s_full : list Word := s_base ++ [Q; K; Q; Q; Q; K; Q; K].
Definition tags_s : list nat := [0; 0; 0; 0; 0; 3; 0; 0; 3; 0; 0; 3; 0; 0; 0; 3; 4; 4; 3; 4].
Definition v_s : list Word := [V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V].

Definition top_base : list Word := [K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; Q; Q; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; Q].
Definition top_full : list Word := top_base ++ [].
Definition tags_top : list nat := [4; 5; 4; 4; 5; 3; 5; 5; 3; 4; 5; 3; 4; 5; 5].

Definition p_init : list Word := [V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; V; K; V; V; K; V; Q; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; V; K; V; V; V; K; V; V; K; V; V; V; V; V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; V; K; V; V; V; V; K; V; V; V; K; V; V; V; V; V; V; K; V; V; V; K; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; Q; V; V; V; V; V; K; V; Q; V; V; V; V; K; V; Q; V; V; V; K; V; V; K; V; V; V; K; V; V; Q; Q; V; V; V; V; V; K; V; V; K; V; V; K; V; V; V; K; V; V; K; V; K; V; V; V; V; V; V; Q; V; K; V; Q; Q; V; K; Q; K; V; V; V; K; V; K; V; K; K; Q; V; V; V; K; V; K; V; V; V; K; V; V; K; K; Q; K; V; K; V; K; K; Q].
Definition ds_core_init : list Word := [K; K; Q; Q; K; K; K; K; Q; Q; Q; K; Q; Q; K; K; K; Q; K; K; Q; Q; K; Q; K; K; K; K; Q; Q; Q; K; Q; K; Q; Q; Q; K; Q; K; Q; Q; K; K; K; Q; K; K; K; Q; Q; Q; Q; K; K; K; Q; K; Q; K; Q; K; K; Q; K; K; K; Q; Q; K; Q; K; Q; K; K; Q; K; K; Q; Q; Q; K; Q; K; Q; Q; K; Q; Q; Q; Q; Q; Q; K; Q; Q; K; K; K; K].
Definition A_core_init : N := 69234923593231798136558728972%N.
(* Initial 4347 steps from c0 to zCf (zTs u_0 0inf) *)

Lemma init_to_u0 : c0 -->* zCf (zTs u_0 0inf%sym).
Proof.
  unfold u_0; cbn [zTs]; unfold zCf, pref_cap, V_u, K_u, Q_u.
  solve_init.
Qed.

(* 13 finite rounds u_0 -> u_13 *)

Lemma step_0 : Step u_0 u_1. Proof. exact (checkStep_sound n_0 tags_0 u_0 da_0 u_1 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_1 : Step u_1 u_2. Proof. exact (checkStep_sound n_1 tags_1 u_1 da_1 u_2 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_2 : Step u_2 u_3. Proof. exact (checkStep_sound n_2 tags_2 u_2 da_2 u_3 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_3 : Step u_3 u_4. Proof. exact (checkStep_sound n_3 tags_3 u_3 da_3 u_4 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_4 : Step u_4 u_5. Proof. exact (checkStep_sound n_4 tags_4 u_4 da_4 u_5 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_5 : Step u_5 u_6. Proof. exact (checkStep_sound n_5 tags_5 u_5 da_5 u_6 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_6 : Step u_6 u_7. Proof. exact (checkStep_sound n_6 tags_6 u_6 da_6 u_7 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_7 : Step u_7 u_8. Proof. exact (checkStep_sound n_7 tags_7 u_7 da_7 u_8 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_8 : Step u_8 u_9. Proof. exact (checkStep_sound n_8 tags_8 u_8 da_8 u_9 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_9 : Step u_9 u_10. Proof. exact (checkStep_sound n_9 tags_9 u_9 da_9 u_10 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_10 : Step u_10 u_11. Proof. exact (checkStep_sound n_10 tags_10 u_10 da_10 u_11 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_11 : Step u_11 u_12. Proof. exact (checkStep_sound n_11 tags_11 u_11 da_11 u_12 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_12 : Step u_12 u_13. Proof. exact (checkStep_sound n_12 tags_12 u_12 da_12 u_13 ltac:(vm_compute; reflexivity)). Qed.

Lemma rounds_0_13 : Rounds u_0 u_13.
Proof.
  exact
    (Rounds_next step_0 (Rounds_next step_1 (Rounds_next step_2 (Rounds_next step_3
      (Rounds_next step_4 (Rounds_next step_5 (Rounds_next step_6 (Rounds_next step_7
        (Rounds_next step_8 (Rounds_next step_9 (Rounds_next step_10
          (Rounds_next step_11 (Rounds_next step_12 (Rounds_refl u_13)))))))))))))).
Qed.

(* Invariant Good u *)

Definition Good (u : list Word) : Prop :=
  exists (p_w ds_core : list Word) (A_core : N) (m : nat),
    u = head_w ++ p_w ++ s_base ++ [Q; K; Q; Q; Q; K; Q; K; K] ++ ds_core ++ top_base /\
    (exists p_tail, p_w = V :: p_tail) /\
    m = 1 + length ds_core /\
    11 <= m /\
    zDg A_core (m - 1) ds_core /\
    (A_core * 512 <= 35 * 2 ^ (N.of_nat (m - 1)))%N /\
    (z13 p_w * qpow2 m == 512)%Q /\
    (zW p_w <= 29#4)%Q.

Lemma good_u13 : Good u_13.
Proof.
  exists p_init, ds_core_init, A_core_init, 101.
  split; [vm_compute; reflexivity |].
  split; [exists (List.tl p_init); reflexivity |].
  split; [vm_compute; reflexivity |].
  split; [lia |].
  split; [exact (checkDg_sound ds_core_init A_core_init ltac:(vm_compute; reflexivity)) |].
  split; [vm_compute; discriminate |].
  split.
  - pose proof (checkZ13Pow_sound p_init 101 9 ltac:(vm_compute; reflexivity)) as h.
    change (qpow2 9) with 512%Q in h. exact h.
  - pose proof (checkZWLe_sound p_init 29%N 4%N ltac:(vm_compute; reflexivity)) as h.
    norm_qN. lra.
Qed.

(* Fixed-piece Scan lemmas *)

Lemma Scan_head : Scan 0%N 126%N head_w a_head b_head v_head 0.
Proof.
  pose proof (checkAffineScan_sound tags_head 0%N 0%N 0%N 126%N head_w 0%N a_head 0%N b_head v_head 0 0%N 0%N ltac:(vm_compute; reflexivity)) as h.
  cbn [N.mul N.add] in h. exact h.
Qed.

Lemma v_head_eq : V :: v_head = head_w ++ [V].
Proof. vm_compute; reflexivity. Qed.

Lemma Scan_s (ap bp : N) (hbp : (3 <= bp)%N) :
    Scan ap bp s_full (2 * ap + 2)%N (1024 * (bp - 3) + 908)%N v_s 3.
Proof.
  pose proof (checkAffineScan_sound tags_s 1%N 0%N 1%N 3%N s_full 2%N 2%N 1024%N 908%N v_s 3 ap (bp - 3)%N ltac:(vm_compute; reflexivity)) as h.
  replace (1 * ap + 0)%N with ap in h by lia.
  replace (1 * (bp - 3) + 3)%N with bp in h by lia.
  exact h.
Qed.

Lemma Scan_top (b_top : N) (hb : (2 <= b_top)%N) :
    Scan (2 ^ 21)%N b_top top_full 0%N (512 * (b_top - 2) + 93)%N s_base 12.
Proof.
  pose proof (checkAffineScan_sound tags_top 0%N (2 ^ 21)%N 1%N 2%N top_full 0%N 0%N 512%N 93%N s_base 12 0%N (b_top - 2)%N ltac:(vm_compute; reflexivity)) as h.
  replace (0 * 0 + 2 ^ 21)%N with (2 ^ 21)%N in h by lia.
  replace (1 * (b_top - 2) + 2)%N with b_top in h by lia.
  replace (0 * 0 + 0)%N with 0%N in h by lia.
  exact h.
Qed.

Lemma Parse_VV_inv {a a' : N} {g : nat} {u : list Word} (h : Parse a (V :: V :: u) a' g) :
    Parse (1 + a * 2)%N (V :: u) a' g.
Proof.
  inversion h; subst; [assumption | contradiction | contradiction].
Qed.

Lemma Parse_VQ_inv {a a' : N} {g : nat} {u : list Word} (h : Parse a (V :: Q :: u) a' g) :
    Parse (1 + a * 2)%N (Q :: u) a' g.
Proof.
  inversion h; subst; [assumption | contradiction | contradiction].
Qed.

Lemma Parse_VK_inv {a a' : N} {g : nat} {u : list Word} (h : Parse a (V :: K :: u) a' g) :
    Parse a u a' g \/ Parse (1 + a * 2)%N (K :: u) a' g.
Proof.
  inversion h; subst; [right; assumption | left; assumption | contradiction | contradiction].
Qed.

Lemma Parse_dV_inv {a a' : N} {g : nat} {w0 : Word} {u : list Word}
    (hw0 : w0 <> V) (h : Parse a (w0 :: V :: u) a' g) :
    exists q1, (a + dVal w0 = q1 * 2)%N /\ Parse q1 (V :: u) a' g.
Proof.
  inversion h; subst; [congruence | eauto | congruence].
Qed.

Lemma Parse_dd_inv {a a' : N} {g : nat} {w0 w1 : Word} {u : list Word}
    (hw0 : w0 <> V) (hw1 : w1 <> V) (h : Parse a (w0 :: w1 :: u) a' g) :
    (exists q1, (a + dVal w0 = q1 * 2)%N /\ Parse q1 (w1 :: u) a' g) \/
    (exists q2 g', g = 1 + g' /\ ((a + dVal w0) / 2 + dVal w1 = 1 + q2 * 2)%N /\ Parse q2 u a' g').
Proof.
  inversion h; subst.
  - congruence.
  - congruence.
  - left; eauto.
  - right; eauto 6.
Qed.

Lemma Parse_s_split {ap a_end : N} {g_all : nat} {rest : list Word}
    (h : Parse ap (s_full ++ K :: rest) a_end g_all) :
    exists g_mid, Parse (2 * (ap + 1))%N (K :: rest) a_end g_mid.
Proof.
  unfold s_full, s_base in h. cbn [List.app] in h.
  apply Parse_VV_inv in h.
  apply Parse_VV_inv in h.
  apply Parse_VV_inv in h.
  apply Parse_VV_inv in h.
  apply Parse_VQ_inv in h.
  destruct (Parse_dV_inv Q_neq_V h) as [q1_1 [hq1_1 h1]].
  assert (hq1_1_eq : q1_1 = (16 + ap * 16)%N) by (cbn [dVal] in hq1_1; lia). subst q1_1.
  apply Parse_VV_inv in h1.
  apply Parse_VQ_inv in h1.
  destruct (Parse_dV_inv Q_neq_V h1) as [q1_2 [hq1_2 h2]].
  assert (hq1_2_eq : q1_2 = (34 + ap * 32)%N) by (cbn [dVal] in hq1_2; lia). subst q1_2.
  apply Parse_VV_inv in h2.
  apply Parse_VQ_inv in h2.
  destruct (Parse_dV_inv Q_neq_V h2) as [q1_3 [hq1_3 h3]].
  assert (hq1_3_eq : q1_3 = (70 + ap * 64)%N) by (cbn [dVal] in hq1_3; lia). subst q1_3.
  apply Parse_VV_inv in h3.
  apply Parse_VV_inv in h3.
  apply Parse_VQ_inv in h3.
  destruct (Parse_dd_inv Q_neq_V K_neq_V h3) as [[q1_4 [hq1_4 h4]] | [q2_4 [g4 [_ [hq2_4 _]]]]];
    [| cbn [dVal] in hq2_4; lia].
  assert (hq1_4_eq : q1_4 = (284 + ap * 256)%N) by (cbn [dVal] in hq1_4; lia). subst q1_4.
  destruct (Parse_dd_inv K_neq_V Q_neq_V h4) as [[q1_5 [hq1_5 h5]] | [q2_5 [g5 [_ [hq2_5 h5]]]]].
  - assert (hq1_5_eq : q1_5 = (142 + ap * 128)%N) by (cbn [dVal] in hq1_5; lia). subst q1_5.
    destruct (Parse_dd_inv Q_neq_V Q_neq_V h5) as [[q1_6 [hq1_6 _]] | [q2_6 [g6 [_ [hq2_6 _]]]]];
      cbn [dVal] in *; lia.
  - assert (hq2_5_eq : q2_5 = (71 + ap * 64)%N) by (cbn [dVal] in hq2_5; lia). subst q2_5.
    destruct (Parse_dd_inv Q_neq_V Q_neq_V h5) as [[q1_7 [hq1_7 h7]] | [q2_7 [g7 [_ [hq2_7 h7]]]]].
    + assert (hq1_7_eq : q1_7 = (36 + ap * 32)%N) by (cbn [dVal] in hq1_7; lia). subst q1_7.
      destruct (Parse_dd_inv Q_neq_V K_neq_V h7) as [[q1_8 [hq1_8 _]] | [q2_8 [g8 [_ [hq2_8 _]]]]];
        cbn [dVal] in *; lia.
    + assert (hq2_7_eq : q2_7 = (18 + ap * 16)%N) by (cbn [dVal] in hq2_7; lia). subst q2_7.
      destruct (Parse_dd_inv K_neq_V Q_neq_V h7) as [[q1_9 [hq1_9 h9]] | [q2_9 [g9 [_ [hq2_9 _]]]]];
        [| cbn [dVal] in hq2_9; lia].
      assert (hq1_9_eq : q1_9 = (9 + ap * 8)%N) by (cbn [dVal] in hq1_9; lia). subst q1_9.
      destruct (Parse_dd_inv Q_neq_V K_neq_V h9) as [[q1_10 [hq1_10 h10]] | [q2_10 [g10 [_ [hq2_10 h10]]]]].
      * assert (hq1_10_eq : q1_10 = (5 + ap * 4)%N) by (cbn [dVal] in hq1_10; lia). subst q1_10.
        destruct (Parse_dd_inv K_neq_V K_neq_V h10) as [[q1_11 [hq1_11 _]] | [q2_11 [g11 [_ [hq2_11 _]]]]];
          cbn [dVal] in *; lia.
      * assert (hq2_10_eq : q2_10 = (2 * (ap + 1))%N) by (cbn [dVal] in hq2_10; lia). subst q2_10.
        exists g10. exact h10.
Qed.

(* Section 6: Main Invariant Closure and Goal Proof *)

Lemma zDg_top : zDg A_top 27 top_base.
Proof. exact (checkDg_sound top_base A_top ltac:(vm_compute; reflexivity)). Qed.

Lemma zDg_bot : zDg 93%N 9 [Q; K; Q; Q; Q; K; Q; K; K].
Proof. exact (checkDg_sound [Q; K; Q; Q; Q; K; Q; K; K] 93%N ltac:(vm_compute; reflexivity)). Qed.

Lemma zDg_mid {A_core : N} {m : nat} {ds_core : list Word}
    (hm : 11 <= m) (hD : zDg A_core (m - 1) ds_core)
    (hA_core : (A_core * 512 <= 35 * 2 ^ (N.of_nat (m - 1)))%N) :
    exists A_mid : N,
      zDg A_mid m ([K] ++ ds_core) /\
      (A_mid <= 35 * 2 ^ (N.of_nat (m - 9)))%N.
Proof.
  assert (h_bs : zDg 0%N 1 [K])
    by exact (checkDg_sound [K] 0%N ltac:(vm_compute; reflexivity)).
  pose proof (zDg_append h_bs hD) as h1.
  replace (1 + (m - 1)) with m in h1 by lia.
  assert (h_pow1 : (2 ^ (N.of_nat (m - 1)) = 256 * 2 ^ (N.of_nat (m - 9)))%N).
  { replace (m - 1) with (8 + (m - 9)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 8)%N with 256%N. reflexivity. }
  exists (0 + A_core * 2 ^ N.of_nat 1)%N.
  split; [exact h1 |].
  change (2 ^ N.of_nat 1)%N with 2%N.
  lia.
Qed.

Lemma force_a_top {p_w ds_mid : list Word} {ap A_mid a_top : N} {gp m g_mid : nat}
    (hm : 11 <= m)
    (hP_p : Parse a_head p_w ap gp)
    (hz13 : (z13 p_w * qpow2 m == 512)%Q)
    (hzW : (zW p_w <= 29#4)%Q)
    (hD_mid : zDg A_mid m ds_mid)
    (hA_hi : (A_mid <= 35 * 2 ^ (N.of_nat (m - 9)))%N)
    (hP_mid : Parse (2 * (ap + 1))%N ds_mid a_top g_mid) :
    a_top = (2 ^ 21)%N.
Proof.
  destruct (Parse_la hP_p) as [hla_lo hla_hi].
  pose proof (z12_nonneg p_w) as hz12.
  pose proof (z10_z12_le_zW p_w) as hz10_le.
  assert (h_diff_hi : ((qN ap + 1) * z13 p_w - (qN a_head + 1) < 15)%Q) by lra.
  pose proof (qpow2_pos m) as h_powm_pos.
  assert (h_mul_lo : ((qN a_head + 1) * qpow2 m <= (qN ap + 1) * (z13 p_w * qpow2 m))%Q)
    by (clear - hla_lo h_powm_pos; nra).
  assert (h_mul_hi : ((qN ap + 1) * (z13 p_w * qpow2 m) < ((qN a_head + 1) + 15) * qpow2 m)%Q)
    by (clear - h_diff_hi h_powm_pos; nra).
  rewrite hz13 in h_mul_lo, h_mul_hi.
  assert (ha_val : (a_head + 1 = 2 ^ (N.of_nat 29))%N) by (vm_compute; reflexivity).
  assert (h_lo_qN : (qN ((a_head + 1) * 2 ^ (N.of_nat m))%N <= qN ((ap + 1) * 512)%N)%Q).
  { rewrite !qN_mul, !qN_add, !qN_pow2. norm_qN. lra. }
  apply qN_le_iff in h_lo_qN.
  assert (h_hi_qN : (qN ((ap + 1) * 512)%N < qN (((a_head + 1) + 15) * 2 ^ (N.of_nat m))%N)%Q).
  { rewrite !qN_mul, !qN_add, !qN_pow2. norm_qN. lra. }
  apply qN_lt_iff in h_hi_qN.
  rewrite ha_val in h_lo_qN, h_hi_qN.
  replace ((ap + 1) * 512)%N with (2 * (ap + 1) * 256)%N in h_lo_qN, h_hi_qN by lia.
  assert (h_split1 : (2 ^ (N.of_nat 29) * 2 ^ (N.of_nat m) = (2 ^ 21 * 2 ^ (N.of_nat m)) * 256)%N).
  { change (2 ^ N.of_nat 29)%N with (2 ^ 21 * 256)%N. lia. }
  assert (h_split2 : ((2 ^ (N.of_nat 29) + 15) * 2 ^ (N.of_nat m) =
                      (2 ^ 21 * 2 ^ (N.of_nat m) + 15 * 2 ^ (N.of_nat (m - 8))) * 256)%N).
  { rewrite !N.mul_add_distr_r, h_split1. f_equal.
    replace m with (8 + (m - 8)) at 1 by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 8)%N with 256%N. lia. }
  rewrite h_split1 in h_lo_qN.
  rewrite h_split2 in h_hi_qN.
  assert (hap_lo : (2 ^ 21 * 2 ^ (N.of_nat m) <= 2 * (ap + 1))%N) by lia.
  assert (hap_hi : (2 * (ap + 1) < 2 ^ 21 * 2 ^ (N.of_nat m) + 15 * 2 ^ (N.of_nat (m - 8)))%N) by lia.
  assert (h_pow_m8 : (2 ^ (N.of_nat (m - 8)) = 2 * 2 ^ (N.of_nat (m - 9)))%N).
  { replace (m - 8) with (1 + (m - 9)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 1)%N with 2%N. reflexivity. }
  assert (h_pow_m : (2 ^ (N.of_nat m) = 512 * 2 ^ (N.of_nat (m - 9)))%N).
  { replace m with (9 + (m - 9)) at 1 by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 9)%N with 512%N. reflexivity. }
  assert (h_pow_m9_ge : (4 <= 2 ^ (N.of_nat (m - 9)))%N).
  { change 4%N with (2 ^ (N.of_nat 2))%N.
    apply N.pow_le_mono_r; lia. }
  destruct (Parse_zDg_a hP_mid hD_mid) as [h_atop_lo h_atop_hi].
  assert (h_sum_lo : (2 ^ 21 * 2 ^ (N.of_nat m) <= 2 * (ap + 1) + A_mid)%N) by lia.
  assert (h_sum_hi : (2 * (ap + 1) + A_mid < (2 ^ 21 + 1) * 2 ^ (N.of_nat m))%N).
  { replace ((2 ^ 21 + 1) * 2 ^ (N.of_nat m))%N
      with (2 ^ 21 * 2 ^ (N.of_nat m) + 512 * 2 ^ (N.of_nat (m - 9)))%N
      by (rewrite h_pow_m; lia).
    lia. }
  assert (h_pos_m : (0 < 2 ^ (N.of_nat m))%N) by exact (zPp_N (N.of_nat m)).
  assert (h_lt1 : (a_top * 2 ^ (N.of_nat m) < (2 ^ 21 + 1) * 2 ^ (N.of_nat m))%N) by lia.
  assert (h_lt2 : (2 ^ 21 * 2 ^ (N.of_nat m) < (a_top + 1) * 2 ^ (N.of_nat m))%N) by lia.
  clear - h_lt1 h_lt2 h_pos_m.
  nia.
Qed.

Lemma bound_b_mid0 {p_w v_p ds_mid : list Word}
    {ap bp A_mid b_mid0 : N} {gp m : nat}
    (hm : 11 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hbp : (3 <= bp)%N)
    (hz13 : (z13 p_w * qpow2 m == 512)%Q)
    (hzW : (zW p_w <= 29#4)%Q)
    (hb_mid0 : b_mid0 = (1024 * (bp - 3) + 908)%N)
    (hD_mid : zDg A_mid m ds_mid) :
    (2 + 4 * z10 ds_mid < qN b_mid0)%Q.
Proof.
  pose proof (proj2 (Scan_delta hS_p)) as h_delta_p.
  pose proof (z10_z12_le_four_zW_V v_p) as h_4wv_p.
  pose proof (Scan_zW_contract hS_p) as h_cw_p.
  pose proof (proj2 (cPar_bounds b_head)) as hc_bh.
  assert (h_wv_p_lt : (zW_V v_p < 7)%Q) by lra.
  pose proof (z13_Scan hS_p) as h_z13_p.
  pose proof (qpow2_ge_1 (3 * gp)) as h_pow_gp_ge1.
  pose proof (z13_pos v_p) as h_z13_vp_pos.
  assert (h_z13_vp_le : (z13 v_p <= z13 p_w)%Q)
    by (clear - h_z13_p h_pow_gp_ge1 h_z13_vp_pos; nra).
  assert (h_bh_big : (qpow2 30 + 30 < qN b_head)%Q) by (vm_compute; reflexivity).
  assert (h_bp2_pos : (0 <= qN bp - 2)%Q).
  { assert (h2 : (qN 2 <= qN bp)%Q) by (apply qN_le_iff; lia).
    norm_qN. lra. }
  assert (h_prod_p : (qpow2 30 < (qN bp - 2) * z13 p_w)%Q)
    by (clear - h_delta_p h_4wv_p h_wv_p_lt h_bh_big h_bp2_pos h_z13_vp_le; nra).
  pose proof (qpow2_pos m) as h_powm_pos.
  assert (h_mul_m : (qpow2 30 * qpow2 m < (qN bp - 2) * (z13 p_w * qpow2 m))%Q)
    by (clear - h_prod_p h_powm_pos; nra).
  rewrite hz13 in h_mul_m.
  assert (h_pow30 : (qpow2 30 == qpow2 21 * 512)%Q) by (vm_compute; reflexivity).
  rewrite h_pow30 in h_mul_m.
  assert (h_bp2_gt : (qpow2 21 * qpow2 m < qN bp - 2)%Q) by lra.
  assert (h_bmid0_r : (qN b_mid0 == 1024 * (qN bp - 3) + 908)%Q).
  { rewrite hb_mid0, qN_add, qN_mul, qN_sub by lia. norm_qN. lra. }
  pose proof (proj2 (zDg_z13_z10 hD_mid)) as h_z10_mid.
  assert (h_pow21_val : (qpow2 21 == 2097152)%Q) by (vm_compute; reflexivity).
  pose proof (qpow2_ge_1 m) as h_powm_ge1.
  rewrite h_z10_mid, h_bmid0_r.
  rewrite h_pow21_val in h_bp2_gt.
  lra.
Qed.

Lemma bound_zW_p' {p_w v_p ds_mid v_mid : list Word}
    {ap bp A_mid b_mid0 b_top : N} {gp m g_mid : nat}
    (hm : 11 <= m)
    (hS_p : Scan a_head b_head p_w ap bp v_p gp)
    (hz13 : (z13 p_w * qpow2 m == 512)%Q)
    (hzW : (zW p_w <= 29#4)%Q)
    (hD_mid : zDg A_mid m ds_mid)
    (hS_mid : Scan (2 * (ap + 1))%N b_mid0 ds_mid (2 ^ 21)%N b_top v_mid g_mid) :
    (zW_V (v_p ++ v_s ++ v_mid) <= 29#4)%Q.
Proof.
  pose proof (Scan_zW_contract hS_p) as h_cw_p.
  assert (hc_bh : cPar b_head = (2#7)%Q) by (vm_compute; reflexivity).
  rewrite hc_bh in h_cw_p.
  assert (hA : (zW_V v_p <= 13#2)%Q) by lra.
  pose proof (z13_Scan hS_p) as h_z13_p.
  assert (h_z13_vs : (z13 v_s == 1#1024)%Q) by (vm_compute; reflexivity).
  assert (h_wv_vs : (zW_V v_s <= 9#8)%Q).
  { pose proof (checkZWVLe_sound v_s 9%N 8%N ltac:(vm_compute; reflexivity)) as h.
    norm_qN. lra. }
  pose proof (qpow2_mono hm) as h_powm_ge11.
  assert (h_z13_p_le : (z13 p_w <= 1#4)%Q).
  { pose proof (z13_pos p_w) as h_pos_p.
    change (qpow2 11) with 2048%Q in h_powm_ge11.
    clear - hz13 h_powm_ge11 h_pos_p. nra. }
  pose proof (qpow2_ge_1 (3 * gp)) as h_pow_gp_ge1.
  pose proof (z13_pos v_p) as h_z13_vp_pos.
  assert (h_z13_vp_le : (z13 v_p <= 1#4)%Q)
    by (clear - h_z13_p h_z13_p_le h_pow_gp_ge1 h_z13_vp_pos; nra).
  pose proof (zW_V_nonneg v_s) as h_wv_vs_nn.
  assert (hB : (z13 v_p * zW_V v_s <= 9#32)%Q)
    by (clear - h_z13_vp_le h_wv_vs h_wv_vs_nn h_z13_vp_pos; nra).
  pose proof (zDg_Scan_dCount hS_mid hD_mid) as h_dc_eq.
  pose proof (dCount_bound_WV v_mid) as h_wv_mid_dc.
  assert (h_dc_le_m : dCount v_mid <= m) by lia.
  pose proof (qpow2_mono h_dc_le_m) as h_pow_dc_le.
  assert (h_powm_ge2048 : (2048 <= qpow2 m)%Q).
  { change 2048%Q with (qpow2 11). exact h_powm_ge11. }
  assert (h_wv_mid_le : (zW_V v_mid <= (7#8) * qpow2 m)%Q) by lra.
  assert (h_vp_m : (z13 v_p * qpow2 m <= 512)%Q).
  { assert (h_eq : (z13 v_p * qpow2 m * qpow2 (3 * gp) == 512)%Q).
    { rewrite <- hz13, <- h_z13_p. lra. }
    pose proof (qpow2_pos m) as hm_pos.
    clear - h_eq h_pow_gp_ge1 h_z13_vp_pos hm_pos. nra. }
  assert (h_prod_ps : (z13 (v_p ++ v_s) * qpow2 m <= 1#2)%Q).
  { rewrite z13_append, h_z13_vs. lra. }
  pose proof (z13_pos (v_p ++ v_s)) as h_z13_ps_pos.
  assert (hC : (z13 (v_p ++ v_s) * zW_V v_mid <= 7#16)%Q).
  { pose proof (zW_V_nonneg v_mid) as h_wv_mid_nn.
    clear - h_prod_ps h_wv_mid_le h_wv_mid_nn h_z13_ps_pos. nra. }
  replace (v_p ++ v_s ++ v_mid)
    with ((v_p ++ v_s) ++ v_mid)
    by (rewrite <- app_assoc; reflexivity).
  pose proof (zW_V_append v_p v_s) as h_app1.
  pose proof (zW_V_append (v_p ++ v_s) v_mid) as h_app2.
  lra.
Qed.

Lemma bound_b_end_zDg {w_all v_w : list Word} {b_top : N} {g_w k : nat}
    (hk : 1 <= k)
    (hb_top : (2 <= b_top)%N)
    (hS_w : Scan a_head b_head w_all (2 ^ 21)%N b_top v_w g_w)
    (hz13_vw : (z13 v_w * qpow2 k == 1)%Q)
    (hWV_vw : (zW_V v_w <= 29#4)%Q) :
    exists (A_core' : N) (ds_core' : list Word),
      zDg A_core' (k + 9) ds_core' /\
      length ds_core' = k + 9 /\
      (A_core' * 512 <= 35 * 2 ^ (N.of_nat (k + 9)))%N /\
      zDg (512 * (b_top - 2) + 93)%N (k + 45)
          ([Q; K; Q; Q; Q; K; Q; K; K] ++ ds_core' ++ top_base).
Proof.
  destruct (Scan_delta hS_w) as [hd_lo hd_hi].
  pose proof (z10_z12_le_four_zW_V v_w) as h_4wv.
  assert (hd_hi' : ((qN b_head - 2) - (qN b_top - 2) * z13 v_w <= 29)%Q) by lra.
  pose proof (qpow2_pos k) as h_powk_pos.
  assert (h_mul_lo : (((qN b_head - 2) - 29) * qpow2 k <= (qN b_top - 2) * (z13 v_w * qpow2 k))%Q)
    by (clear - hd_hi' h_powk_pos; nra).
  assert (h_mul_hi : ((qN b_top - 2) * (z13 v_w * qpow2 k) <= (qN b_head - 1) * qpow2 k)%Q)
    by (clear - hd_lo h_powk_pos; nra).
  rewrite hz13_vw in h_mul_lo, h_mul_hi.
  assert (hbh_r : (qN b_head - 2 == qN A_top * 512 + 34)%Q) by (vm_compute; reflexivity).
  assert (hbh_1_r : (qN b_head - 1 == qN A_top * 512 + 35)%Q) by (vm_compute; reflexivity).
  rewrite hbh_r in h_mul_lo.
  rewrite hbh_1_r in h_mul_hi.
  set (b_end := (512 * (b_top - 2) + 93)%N).
  assert (hb_end_r : (qN b_end == 512 * (qN b_top - 2) + 93)%Q).
  { unfold b_end.
    rewrite qN_add, qN_mul, qN_sub by lia.
    norm_qN. lra. }
  assert (h_pow_k18 : (qpow2 (k + 18) == 262144 * qpow2 k)%Q).
  { rewrite qpow2_add. change (qpow2 18) with 262144%Q. lra. }
  assert (h_powk_ge2 : (2 <= qpow2 k)%Q).
  { change 2%Q with (qpow2 1). exact (qpow2_mono hk). }
  assert (h_bend_lo_r : (qN (A_top * 2 ^ (N.of_nat (k + 18)))%N < qN b_end)%Q).
  { rewrite qN_mul, qN_pow2, hb_end_r, h_pow_k18. lra. }
  assert (h_bend_mid_r : (qN b_end <= qN (A_top * 2 ^ (N.of_nat (k + 18)) + 512 * 35 * 2 ^ (N.of_nat k) + 93)%N)%Q).
  { rewrite !qN_add, !qN_mul, !qN_pow2, hb_end_r, h_pow_k18. norm_qN. lra. }
  assert (h_bend_hi_r : (qN b_end < qN ((A_top + 1) * 2 ^ (N.of_nat (k + 18)))%N)%Q).
  { rewrite qN_mul, qN_add, qN_pow2, hb_end_r, h_pow_k18. norm_qN. lra. }
  apply qN_lt_iff in h_bend_lo_r.
  apply qN_le_iff in h_bend_mid_r.
  apply qN_lt_iff in h_bend_hi_r.
  assert (h_pow_k18_eq : (2 ^ (N.of_nat (k + 18)) = 512 * 2 ^ (N.of_nat (k + 9)))%N).
  { replace (k + 18) with (9 + (k + 9)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 9)%N with 512%N. reflexivity. }
  rewrite h_pow_k18_eq in h_bend_lo_r, h_bend_mid_r, h_bend_hi_r.
  set (P9 := (2 ^ (N.of_nat (k + 9)))%N) in *.
  set (Pk := (2 ^ (N.of_nat k))%N) in *.
  assert (h_P9_eq : (P9 = 512 * Pk)%N).
  { unfold P9, Pk. replace (k + 9) with (9 + k) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 9)%N with 512%N. reflexivity. }
  set (Q512 := (b_end / 512)%N).
  assert (h_b_end_eq : (b_end = 512 * Q512 + 93)%N) by (unfold Q512, b_end; lia).
  assert (h_Q512_lo : (A_top * P9 <= Q512)%N) by lia.
  assert (h_Q512_mid : (Q512 <= A_top * P9 + 35 * Pk)%N) by lia.
  assert (h_Q512_hi : (Q512 < (A_top + 1) * P9)%N) by lia.
  set (A_core' := (Q512 - A_top * P9)%N).
  assert (h_Acore'_lt : (A_core' < P9)%N) by (unfold A_core'; lia).
  assert (h_Acore'_512 : (A_core' * 512 <= 35 * P9)%N) by (unfold A_core'; lia).
  destruct (zDg_exists (k + 9) A_core' h_Acore'_lt) as [ds_core' hD_core'].
  pose proof (zDg_len hD_core') as h_len_core'.
  pose proof (zDg_append zDg_bot hD_core') as h_bot_mid.
  pose proof (zDg_append h_bot_mid zDg_top) as h_all.
  replace ((9 + (k + 9)) + 27) with (k + 45) in h_all by lia.
  assert (h_val_all : ((93 + A_core' * 2 ^ N.of_nat 9) + A_top * 2 ^ (N.of_nat (9 + (k + 9))) = b_end)%N).
  { rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 9)%N with 512%N.
    change (2 ^ N.of_nat (k + 9))%N with P9.
    unfold A_core'. lia. }
  rewrite h_val_all in h_all.
  rewrite <- !app_assoc in h_all.
  exists A_core', ds_core'.
  exact (conj hD_core' (conj h_len_core' (conj h_Acore'_512 h_all))).
Qed.

Lemma Good_step {u : list Word} (hG : Good u) :
    exists u', Step u u' /\ Good u'.
Proof.
  destruct hG as [p_w [ds_core [A_core [m [-> [[p_tail hp_start] [hm_def [hm [hD_core [hA_core [hz13 hzW]]]]]]]]]]].
  assert (hP_p_ex : exists ap gp, Parse a_head p_w ap gp).
  { rewrite hp_start. exact (Parse_V_start a_head p_tail). }
  destruct hP_p_ex as [ap [gp hP_p]].
  assert (hb_head_ok : (2 + 4 * z10 p_w < qN b_head)%Q).
  { pose proof (z12_nonneg p_w) as hz12.
    pose proof (z10_z12_le_zW p_w) as hz10_le.
    assert (hbh_gt : (31 < qN b_head)%Q) by (vm_compute; reflexivity).
    lra. }
  destruct (Scan_of_Parse hP_p b_head hb_head_ok) as [bp [v_p [hS_p hbp]]].
  pose proof (Scan_s ap bp hbp) as hS_s.
  replace (2 * ap + 2)%N with (2 * (ap + 1))%N in hS_s by lia.
  set (b_mid0 := (1024 * (bp - 3) + 908)%N).
  set (ds_mid := [K] ++ ds_core).
  destruct (zDg_mid hm hD_core hA_core) as [A_mid [hD_mid hA_hi]].
  change ([K] ++ ds_core) with ds_mid in hD_mid.
  assert (hP_s_all : exists a_top g_all, Parse ap (s_full ++ ds_mid) a_top g_all).
  { change (s_full ++ ds_mid) with (V :: (List.tl s_full ++ ds_mid)).
    exact (Parse_V_start ap _). }
  destruct hP_s_all as [a_top [g_all hP_all]].
  destruct (Parse_s_split hP_all) as [g_mid hP_mid].
  pose proof (force_a_top hm hP_p hz13 hzW hD_mid hA_hi hP_mid) as hatop_eq.
  subst a_top.
  pose proof (bound_b_mid0 hm hS_p hbp hz13 hzW eq_refl hD_mid) as hb_mid0_ok.
  destruct (Scan_of_Parse hP_mid b_mid0 hb_mid0_ok) as [b_top [v_mid [hS_mid hb_top_ge3]]].
  assert (hb_top : (2 <= b_top)%N) by lia.
  pose proof (Scan_top b_top hb_top) as hS_top.
  set (w_all := p_w ++ s_full ++ ds_mid).
  set (v_w := v_p ++ v_s ++ v_mid).
  set (g_w := gp + 3 + g_mid).
  assert (hS_w : Scan a_head b_head w_all (2 ^ 21)%N b_top v_w g_w).
  { pose proof (Scan_append (Scan_append hS_p hS_s) hS_mid) as h234.
    unfold w_all, v_w, g_w.
    rewrite <- !app_assoc in h234.
    exact h234. }
  assert (h_u_rep0 :
      (head_w ++ p_w ++ s_base ++ [Q; K; Q; Q; Q; K; Q; K; K] ++ ds_core ++ top_base) ++ repeat K 0 =
      head_w ++ w_all ++ top_full).
  { unfold w_all, s_full, ds_mid, top_full.
    cbn [repeat].
    rewrite !app_nil_r, <- !app_assoc. reflexivity. }
  assert (hS_full :
      Scan 0%N 126%N ((head_w ++ p_w ++ s_base ++ [Q; K; Q; Q; Q; K; Q; K; K] ++ ds_core ++ top_base) ++ repeat K 0)
           0%N (512 * (b_top - 2) + 93)%N (v_head ++ v_w ++ s_base) (0 + g_w + 12)).
  { rewrite h_u_rep0.
    pose proof (Scan_append (Scan_append Scan_head hS_w) hS_top) as h125.
    rewrite <- !app_assoc in h125.
    exact h125. }
  set (k := 1 + 3 * gp + 3 * g_mid).
  assert (hk : 1 <= k) by lia.
  pose proof (bound_zW_p' hm hS_p hz13 hzW hD_mid hS_mid) as hWV_vw.
  assert (hz13_vw : (z13 v_w * qpow2 k == 1)%Q).
  { pose proof (z13_Scan hS_w) as h_z13_w.
    assert (h_w_eq : (z13 w_all == 256)%Q).
    { unfold w_all. rewrite !z13_append.
      assert (h_s : (z13 s_full == 1#2)%Q) by (vm_compute; reflexivity).
      pose proof (proj1 (zDg_z13_z10 hD_mid)) as h_mid.
      rewrite h_s, h_mid.
      lra. }
    rewrite h_w_eq in h_z13_w.
    assert (h_3gw : 3 * g_w = k + 8) by (unfold g_w, k; lia).
    rewrite h_3gw, qpow2_add in h_z13_w.
    change (qpow2 8) with 256%Q in h_z13_w.
    lra. }
  destruct (bound_b_end_zDg hk hb_top hS_w hz13_vw hWV_vw)
    as [A_core' [ds_core' [hD_core' [hlen_core' [hA_core' hD_bend]]]]].
  set (da := [Q; K; Q; Q; Q; K; Q; K; K] ++ ds_core' ++ top_base).
  set (u' := V :: ((v_head ++ v_w ++ s_base) ++ da)).
  exists u'. split.
  - exists 0, (512 * (b_top - 2) + 93)%N, (v_head ++ v_w ++ s_base), da, (k + 45), (0 + g_w + 12).
    exact (conj hS_full (conj hD_bend eq_refl)).
  - exists (V :: v_w), ds_core', A_core', (k + 10).
    split.
    + unfold u', da.
      rewrite <- !app_assoc, app_comm_cons, v_head_eq, <- !app_assoc.
      reflexivity.
    + split; [exists v_w; reflexivity |].
      split; [lia |].
      split; [lia |].
      split; [replace (k + 10 - 1) with (k + 9) by lia; exact hD_core' |].
      split; [replace (k + 10 - 1) with (k + 9) by lia; exact hA_core' |].
      split.
      * cbn [z13].
        replace (k + 10) with (k + (1 + 9)) by lia.
        rewrite !qpow2_add.
        change (qpow2 1) with 2%Q.
        change (qpow2 9) with 512%Q.
        clear - hz13_vw. nra.
      * rewrite zW_cons_V. exact hWV_vw.
Qed.

Close Scope word_scope.

Lemma nonhalt : ~ halts tm c0.
Proof.
  apply (multistep_nonhalt tm c0 (zCf (zTs u_13 0inf%sym))
           (etrans init_to_u0 (Rounds_exec rounds_0_13))).
  apply (progress_nonhalt_cond tm (list Word) u_13 (fun u => zCf (zTs u 0inf%sym)) Good).
  - intros u hG.
    destruct (Good_step hG) as [u' [hStep hG']].
    exists u'. split; [exact (Step_exec hStep) | exact hG'].
  - exact good_u13.
Qed.
