(* 1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RB--- never halts. *)

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
  (TM_from_str "1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RB---").

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
Definition pref28 : list Sym :=
  [1; 1; 0; 0; 1; 1; 0; 1; 1; 0; 0; 1; 1; 0; 0; 1; 1; 0; 0; 0; 0; 1; 1; 0; 0; 1; 1; 0]%sym.

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
  | ch => C
  | ca => B
  end.

Definition zCR (w : side) (c : Call) (r : side) : Q * tape :=
  ([1]%sym *> r) {{zCs c}}> w.

Definition zCL (w : side) (r : side) : Q * tape :=
  r <{{D}} ([0]%sym *> w).

Definition zCf (w : side) : Q * tape :=
  0inf%sym <{{D}} ([0]%sym *> pref28 *> w).

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


(* Turnaround zP0..zP14 *)
Definition tr1 : list Sym := [0;1;1;1;0;1;1;1;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr2 : list Sym := [0;1;0;1;0;1;1;1;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr3 : list Sym := [0;1;1;1;0;1;0;1;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr4 : list Sym := [0;1;0;1;0;1;0;1;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr5 : list Sym := [0;1;1;1;0;1;1;1;1;1;0;1;0;1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr6 : list Sym := [0;1;0;1;0;1;1;1;1;1;0;1;0;1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr7 : list Sym := [0;1;1;1;0;1;0;1;1;1;0;1;0;1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr8 : list Sym := [0;1;0;1;0;1;0;1;1;1;0;1;0;1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0;1]%sym.
Definition tr9 : list Sym := [0;1;1;1;0;1;1;1;1;1;0;1;0;0;1;0;1;0;1;1;1;0;1;0;0;1;0;1;0;1]%sym.
Definition tr10 : list Sym := [0;1;0;1;0;1;1;1;1;1;0;1;0;0;1;0;1;0;1;1;1;0;1;0;0;1;0;1;0;1]%sym.
Definition tr11 : list Sym := [0;1;1;1;0;1;0;1;1;1;0;1;0;0;1;0;1;0;1;1;1;0;1;0;0;1;0;1;0;1]%sym.
Definition tr12 : list Sym := [0;1;0;1;0;1;0;1;1;1;0;1;0;0;1;0;1;0;1;1;1;0;1;0;0;1;0;1;0;1]%sym.
Definition tr13 : list Sym := [0;1;1;0;1;0;1;0;1;0;1;1;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1]%sym.
Definition tr14 : list Sym := [0;1;0;0;1;0;1;0;1;0;1;1;1;0;1;0;1;0;1;0;1;0;1;0;0;1;0;1;0;1]%sym.

Lemma zP0 (w : side) : zCf w -->+ zCR w ca (tr1 *> 0inf%sym).
Proof. unfold zCf, zCR, zCs, pref28, tr1. cbn [List.app Str_app]. fast_start_progress. Qed.

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

Lemma zP14 (w : side) : zCL w (tr14 *> 0inf%sym) -->+ zCf ([1; 1; 0]%sym *> w).
Proof. unfold zCL, zCf, tr14, pref28. cbn [List.app Str_app]. fast_start_progress. Qed.

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
    Scan 0%N 14%N (u ++ repeat K n) 0%N b' v g /\
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


Lemma Side_turnaround {w w' : side} (h : Side ([ca] ^^ 14) w w') :
    zCf w -->+ zCf ([1; 1; 0]%sym *> w').
Proof.
  cbn in h.
  inversion h as [| ? ? ? w1 ? hc1 h1]; subst.
  inversion h1 as [| ? ? ? w2 ? hc2 h2]; subst.
  inversion h2 as [| ? ? ? w3 ? hc3 h3]; subst.
  inversion h3 as [| ? ? ? w4 ? hc4 h4]; subst.
  inversion h4 as [| ? ? ? w5 ? hc5 h5]; subst.
  inversion h5 as [| ? ? ? w6 ? hc6 h6]; subst.
  inversion h6 as [| ? ? ? w7 ? hc7 h7]; subst.
  inversion h7 as [| ? ? ? w8 ? hc8 h8]; subst.
  inversion h8 as [| ? ? ? w9 ? hc9 h9]; subst.
  inversion h9 as [| ? ? ? w10 ? hc10 h10]; subst.
  inversion h10 as [| ? ? ? w11 ? hc11 h11]; subst.
  inversion h11 as [| ? ? ? w12 ? hc12 h12]; subst.
  inversion h12 as [| ? ? ? w13 ? hc13 h13]; subst.
  inversion h13 as [| ? ? ? w14 ? hc14 h14]; subst.
  inversion h14; subst.
  exact (ptrans (zP0 w)
    (ptrans (hc1 (tr1 *> 0inf%sym))
      (ptrans (zP1 w1)
        (ptrans (hc2 (tr2 *> 0inf%sym))
          (ptrans (zP2 w2)
            (ptrans (hc3 (tr3 *> 0inf%sym))
              (ptrans (zP3 w3)
                (ptrans (hc4 (tr4 *> 0inf%sym))
                  (ptrans (zP4 w4)
                    (ptrans (hc5 (tr5 *> 0inf%sym))
                      (ptrans (zP5 w5)
                        (ptrans (hc6 (tr6 *> 0inf%sym))
                          (ptrans (zP6 w6)
                            (ptrans (hc7 (tr7 *> 0inf%sym))
                              (ptrans (zP7 w7)
                                (ptrans (hc8 (tr8 *> 0inf%sym))
                                  (ptrans (zP8 w8)
                                    (ptrans (hc9 (tr9 *> 0inf%sym))
                                      (ptrans (zP9 w9)
                                        (ptrans (hc10 (tr10 *> 0inf%sym))
                                          (ptrans (zP10 w10)
                                            (ptrans (hc11 (tr11 *> 0inf%sym))
                                              (ptrans (zP11 w11)
                                                (ptrans (hc12 (tr12 *> 0inf%sym))
                                                  (ptrans (zP12 w12)
                                                    (ptrans (hc13 (tr13 *> 0inf%sym))
                                                      (ptrans (zP13 w13)
                                                        (ptrans (hc14 (tr14 *> 0inf%sym)) (zP14 w'))))))))))))))))))))))))))))).
Qed.

Lemma Step_exec {u u' : list Word} (h : Step u u') :
    zCf (zTs u 0inf%sym) -->+ zCf (zTs u' 0inf%sym).
Proof.
  destruct h as [n [b' [v [da [H [g [hScan [hDg ->]]]]]]]].
  pose proof (Seg_of_Scan hScan) as hSeg.
  cbn [N.to_nat lpow List.app] in hSeg.
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
  match evalAffineScan ts 0%N 0%N 0%N 14%N (u ++ repeat K n) with
  | Some (0%N, 0%N, 0%N, b', v, _) => checkDg b' da && list_word_eqb u' (V :: (v ++ da))
  | _ => false
  end.

Lemma checkStep_sound (n : nat) (ts : list nat) (u da u' : list Word)
    (h : checkStep n ts u da u' = true) : Step u u'.
Proof.
  unfold checkStep in h.
  destruct (evalAffineScan ts 0%N 0%N 0%N 14%N (u ++ repeat K n))
    as [[[[[[ma' ca'] mb'] b'] v] g] |] eqn:hrec; [| discriminate].
  destruct ma'; [| discriminate].
  destruct ca'; [| discriminate].
  destruct mb'; [| discriminate].
  apply Bool.andb_true_iff in h as [hDg hu'].
  apply list_word_eqb_eq in hu'.
  pose proof (evalAffineScan_sound ts 0%N 0%N 0%N 14%N (u ++ repeat K n) 0%N 0%N 0%N b' v g 0%N 0%N hrec) as hScan.
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
  if (b mod 2 =? 1)%N then (2#16)%Q else (3#16)%Q.

Lemma cPar_bounds (b : N) : ((2#16) <= cPar b)%Q /\ (cPar b <= (3#16))%Q.
Proof.
  unfold cPar. destruct (b mod 2 =? 1)%N; lra.
Qed.

Lemma cPar_even (k : N) : cPar (k * 2)%N = (3#16)%Q.
Proof.
  unfold cPar. replace ((k * 2) mod 2)%N with 0%N by lia. reflexivity.
Qed.

Lemma cPar_odd (k : N) : cPar (1 + k * 2)%N = (2#16)%Q.
Proof.
  unfold cPar. replace ((1 + k * 2) mod 2)%N with 1%N by lia. reflexivity.
Qed.

Lemma Scan_zW_contract {a b a' b' : N} {g : nat} {u v : list Word}
    (h : Scan a b u a' b' v g) :
    (zW_V v <= (15#16) * zW u + cPar b)%Q.
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


Definition u_0 : list Word := [K;K;K;Q].
Definition tags_0 : list nat := [3;3;4].
Definition da_0 : list Word := [K;K;Q].
Definition n_0 : nat := 0.
Definition u_1 : list Word := [V;K;Q;V;K;K;Q].
Definition tags_1 : list nat := [0;5;2;4].
Definition da_1 : list Word := [K;K;K;K;K;Q;Q].
Definition n_1 : nat := 0.
Definition u_2 : list Word := [V;V;V;Q;V;V;K;K;K;K;K;Q;Q].
Definition tags_2 : list nat := [0;0;0;3;0;0;5;3;4;5].
Definition da_2 : list Word := [Q;Q;Q;Q;K;Q;Q;Q;K;Q].
Definition n_2 : nat := 0.
Definition u_3 : list Word := [V;V;V;V;K;V;V;V;Q;V;V;Q;Q;Q;Q;K;Q;Q;Q;K;Q].
Definition tags_3 : list nat := [0;0;0;1;0;0;0;3;0;0;4;3;4;5;3;5].
Definition da_3 : list Word := [Q;K;Q;Q;K;Q;K;Q;Q;Q;Q;K;Q].
Definition n_3 : nat := 0.
Definition u_4 : list Word := [V;V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;Q;V;Q;K;Q;Q;K;Q;K;Q;Q;Q;Q;K;Q].
Definition tags_4 : list nat := [0;0;0;1;0;0;0;1;0;0;1;0;0;3;0;4;5;4;4;5;3;5].
Definition da_4 : list Word := [Q;K;K;Q;K;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition n_4 : nat := 0.
Definition u_5 : list Word := [V;V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;V;K;V;V;V;V;V;V;Q;V;Q;K;K;Q;K;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition tags_5 : list nat := [0;0;0;1;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;0;3;0;4;4;3;4;4;3;5;4;5;3;5].
Definition da_5 : list Word := [Q;K;Q;Q;K;Q;K;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition n_5 : nat := 0.
Definition u_6 : list Word := [V;V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;V;K;V;V;V;V;V;V;V;K;V;V;V;K;V;V;K;V;V;V;Q;V;Q;K;Q;Q;K;Q;K;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition tags_6 : list nat := [0;0;0;1;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;3;0;4;5;4;3;5;5;4;4;3;5;4;5;3;5].
Definition da_6 : list Word := [Q;K;Q;Q;K;Q;K;K;K;Q;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition n_6 : nat := 0.
Definition u_7 : list Word := [V;V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;V;K;V;V;V;V;V;V;V;K;V;V;V;K;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;Q;V;Q;K;Q;Q;K;Q;K;K;K;Q;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition tags_7 : list nat := [0;0;0;1;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;3;0;4;5;4;3;3;3;5;3;4;4;5;5;4;4;3;5;4;5;3;5].
Definition da_7 : list Word := [Q;K;Q;Q;K;Q;K;K;Q;Q;K;K;Q;Q;K;Q;Q;K;Q;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition n_7 : nat := 0.
Definition u_8 : list Word := [V;V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;V;K;V;V;V;V;V;V;V;K;V;V;V;K;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;K;Q;V;Q;V;V;V;V;V;V;K;V;V;V;Q;V;Q;K;Q;Q;K;Q;K;K;Q;Q;K;K;Q;Q;K;Q;Q;K;Q;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition tags_8 : list nat := [0;0;0;1;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;1;0;0;0;0;5;3;0;3;0;0;0;0;0;1;0;0;0;3;0;4;5;4;3;4;4;3;5;3;5;3;5;3;4;4;5;5;4;4;3;5;4;5;3;5].
Definition da_8 : list Word := [Q;K;Q;Q;K;Q;K;K;K;K;Q;Q;K;Q;K;Q;Q;Q;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition n_8 : nat := 0.
Definition u_9 : list Word := [V;V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;V;K;V;V;V;V;V;V;V;K;V;V;V;K;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;V;V;Q;V;K;V;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;K;V;Q;V;Q;V;Q;V;V;V;V;V;V;K;V;V;V;Q;V;Q;K;Q;Q;K;Q;K;K;K;K;Q;Q;K;Q;K;Q;Q;Q;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;K;Q;K;Q;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition head41 : list Word := [V;V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;V;K;V;V;V;V;V;V;V;K;V;V;V;K;V;V;K;V;V;V;V;K;V;V;V].
Definition tags_head41 : list nat := [0;0;0;1;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;0;1;0;0;1;0;1;0;0;0;1;0;0;0].
Definition v_head41 : list Word := [V;V;V;K;V;V;V;V;K;V;V;V;K;V;V;V;K;V;V;V;V;V;V;V;K;V;V;V;K;V;V;K;V;V;V;V;K;V;V;V;V].
Definition a_41 : N := 33554431%N.
Definition b_41 : N := 397770042%N.
Definition A_top24 : N := 12430313%N.
Definition s12 : list Word := [V;V;V;V;V;V;K;V;V;V;Q;V].
Definition s18 : list Word := s12 ++ [Q;K;Q;Q;K;Q].
Definition tags_s18 : list nat := [0;0;0;0;0;1;0;0;0;3;0;4;5;4].
Definition v_s18 : list Word := [V;V;V;V;V;K;V;V;V;V;K;V;V;V;V].
Definition top22 : list Word := [K;Q;K;Q;Q;Q;Q;Q;K;Q;K;Q;K;Q;Q;K;Q;Q;Q;Q;K;Q].
Definition tags_top22 : list nat := [4;4;5;5;4;4;3;5;4;5;3;5].
Definition p_41_init : list Word := [V;K;V;V;V;V;K;V;V;V;V;K;V;V;V;V;V;V;Q;V;K;V;V;V;V;V;K;V;V;V;V;K;V;V;V;V;K;V;V;K;V;Q;V;Q;V;Q].
Definition ds_core_init : list Word := [K;K;Q;Q;K;Q;K;Q;Q;Q;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;Q;Q;K;Q].
Definition A_core_init : N := 47935404%N.

(* Initial 568 steps from c0 to zCf (zTs u_0 0inf) *)

Lemma init_to_u0 : c0 -->* zCf (zTs u_0 0inf%sym).
Proof.
  unfold u_0; cbn [zTs]; unfold zCf, pref28, V_u, K_u, Q_u.
  solve_init.
Qed.

(* 9 finite rounds u_0 -> u_9 *)

Lemma step_0 : Step u_0 u_1. Proof. exact (checkStep_sound n_0 tags_0 u_0 da_0 u_1 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_1 : Step u_1 u_2. Proof. exact (checkStep_sound n_1 tags_1 u_1 da_1 u_2 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_2 : Step u_2 u_3. Proof. exact (checkStep_sound n_2 tags_2 u_2 da_2 u_3 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_3 : Step u_3 u_4. Proof. exact (checkStep_sound n_3 tags_3 u_3 da_3 u_4 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_4 : Step u_4 u_5. Proof. exact (checkStep_sound n_4 tags_4 u_4 da_4 u_5 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_5 : Step u_5 u_6. Proof. exact (checkStep_sound n_5 tags_5 u_5 da_5 u_6 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_6 : Step u_6 u_7. Proof. exact (checkStep_sound n_6 tags_6 u_6 da_6 u_7 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_7 : Step u_7 u_8. Proof. exact (checkStep_sound n_7 tags_7 u_7 da_7 u_8 ltac:(vm_compute; reflexivity)). Qed.
Lemma step_8 : Step u_8 u_9. Proof. exact (checkStep_sound n_8 tags_8 u_8 da_8 u_9 ltac:(vm_compute; reflexivity)). Qed.

Lemma rounds_0_9 : Rounds u_0 u_9.
Proof.
  exact
    (Rounds_next step_0 (Rounds_next step_1 (Rounds_next step_2 (Rounds_next step_3
      (Rounds_next step_4 (Rounds_next step_5 (Rounds_next step_6 (Rounds_next step_7
        (Rounds_next step_8 (Rounds_refl u_9)))))))))).
Qed.

(* Invariant Good u (5-piece decomposition) *)

Definition Good (u : list Word) : Prop :=
  exists (p_41 ds_core : list Word) (A_core : N) (m : nat),
    u = head41 ++ p_41 ++ s12 ++ [Q; K; Q; Q; K; Q; K; K] ++ ds_core ++ [Q; K] ++ top22 /\
    (exists p_tail, p_41 = V :: p_tail) /\
    m = 4 + length ds_core /\
    12 <= m /\
    zDg A_core (m - 4) ds_core /\
    (A_core * 32 <= 25 * 2 ^ (N.of_nat (m - 4)))%N /\
    (z13 p_41 * qpow2 m == 256)%Q /\
    (zW p_41 <= 21#4)%Q.

Lemma good_u9 : Good u_9.
Proof.
  exists p_41_init, ds_core_init, A_core_init, 30.
  split; [vm_compute; reflexivity |].
  split; [exists (List.tl p_41_init); reflexivity |].
  split; [vm_compute; reflexivity |].
  split; [lia |].
  split; [exact (checkDg_sound ds_core_init A_core_init ltac:(vm_compute; reflexivity)) |].
  split; [vm_compute; discriminate |].
  split.
  - pose proof (checkZ13Pow_sound p_41_init 30 8 ltac:(vm_compute; reflexivity)) as h.
    change (qpow2 8) with 256%Q in h. exact h.
  - pose proof (checkZWLe_sound p_41_init 21%N 4%N ltac:(vm_compute; reflexivity)) as h.
    norm_qN. lra.
Qed.

(* Fixed-piece Scan lemmas *)

Lemma Scan_head41 : Scan 0%N 14%N head41 a_41 b_41 v_head41 0.
Proof.
  pose proof (checkAffineScan_sound tags_head41 0%N 0%N 0%N 14%N head41 0%N a_41 0%N b_41 v_head41 0 0%N 0%N ltac:(vm_compute; reflexivity)) as h.
  cbn [N.mul N.add] in h. exact h.
Qed.

Lemma v_head41_eq : V :: v_head41 = head41 ++ [V].
Proof. vm_compute; reflexivity. Qed.

Lemma Scan_s18 (ap bp : N) (hbp : (3 <= bp)%N) :
    Scan ap bp s18 (4 * ap + 4)%N (2048 * (bp - 3) + 1972)%N v_s18 3.
Proof.
  pose proof (checkAffineScan_sound tags_s18 1%N 0%N 1%N 3%N s18 4%N 4%N 2048%N 1972%N v_s18 3 ap (bp - 3)%N ltac:(vm_compute; reflexivity)) as h.
  replace (1 * ap + 0)%N with ap in h by lia.
  replace (1 * (bp - 3) + 3)%N with bp in h by lia.
  exact h.
Qed.

Lemma Scan_top22 (b_top22 : N) (hb : (2 <= b_top22)%N) :
    Scan (2 ^ 19)%N b_top22 top22 0%N (256 * (b_top22 - 2) + 45)%N s12 10.
Proof.
  pose proof (checkAffineScan_sound tags_top22 0%N (2 ^ 19)%N 1%N 2%N top22 0%N 0%N 256%N 45%N s12 10 0%N (b_top22 - 2)%N ltac:(vm_compute; reflexivity)) as h.
  replace (0 * 0 + 2 ^ 19)%N with (2 ^ 19)%N in h by lia.
  replace (1 * (b_top22 - 2) + 2)%N with b_top22 in h by lia.
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

Lemma Parse_s18_split {ap a_end : N} {g_all : nat} {rest : list Word}
    (h : Parse ap (s18 ++ K :: rest) a_end g_all) :
    exists g_mid, Parse (4 * (ap + 1))%N (K :: rest) a_end g_mid.
Proof.
  unfold s18, s12 in h. cbn [List.app] in h.
  apply Parse_VV_inv in h.
  apply Parse_VV_inv in h.
  apply Parse_VV_inv in h.
  apply Parse_VV_inv in h.
  apply Parse_VV_inv in h.
  destruct (Parse_VK_inv h) as [h1 | h1].
  - apply Parse_VV_inv in h1.
    apply Parse_VV_inv in h1.
    apply Parse_VQ_inv in h1.
    destruct (Parse_dV_inv Q_neq_V h1) as [q1_10 [hq1_10 h10]].
    assert (hq1_10_eq : q1_10 = (128 + ap * 128)%N) by (cbn [dVal] in hq1_10; lia).
    subst q1_10.
    apply Parse_VQ_inv in h10.
    destruct (Parse_dd_inv Q_neq_V K_neq_V h10) as [[q1_12 [hq1_12 h12]] | [q2_12 [g12 [_ [hq2_12 h12]]]]].
    + assert (hq1_12_eq : q1_12 = (129 + ap * 128)%N) by (cbn [dVal] in hq1_12; lia).
      subst q1_12.
      destruct (Parse_dd_inv K_neq_V Q_neq_V h12) as [[q1_13 [hq1_13 _]] | [q2_13 [g13 [_ [hq2_13 h15]]]]].
      * cbn [dVal] in hq1_13; lia.
      * assert (hq2_13_eq : q2_13 = (32 + ap * 32)%N) by (cbn [dVal] in hq2_13; lia).
        subst q2_13.
        destruct (Parse_dd_inv Q_neq_V K_neq_V h15) as [[q1_15 [hq1_15 _]] | [q2_15 [g15 [_ [hq2_15 _]]]]];
          cbn [dVal] in *; lia.
    + assert (hq2_12_eq : q2_12 = (64 + ap * 64)%N) by (cbn [dVal] in hq2_12; lia).
      subst q2_12.
      destruct (Parse_dd_inv Q_neq_V Q_neq_V h12) as [[q1_14 [hq1_14 _]] | [q2_14 [g14 [_ [hq2_14 h16]]]]].
      * cbn [dVal] in hq1_14; lia.
      * assert (hq2_14_eq : q2_14 = (16 + ap * 16)%N) by (cbn [dVal] in hq2_14; lia).
        subst q2_14.
        destruct (Parse_dd_inv K_neq_V Q_neq_V h16) as [[q1_16 [hq1_16 h17]] | [q2_16 [g_mid [_ [hq2_16 h18]]]]].
        -- assert (hq1_16_eq : q1_16 = (8 + ap * 8)%N) by (cbn [dVal] in hq1_16; lia).
           subst q1_16.
           destruct (Parse_dd_inv Q_neq_V K_neq_V h17) as [[q1_17 [hq1_17 _]] | [q2_17 [g17 [_ [hq2_17 _]]]]];
             cbn [dVal] in *; lia.
        -- assert (h_end : q2_16 = (4 * (ap + 1))%N) by (cbn [dVal] in hq2_16; lia).
           subst q2_16. exists g_mid. exact h18.
  - destruct (Parse_dV_inv K_neq_V h1) as [q1_6 [hq1_6 _]].
    cbn [dVal] in hq1_6; lia.
Qed.

(* Section 6: Main Invariant Closure and Goal Proof *)

Lemma zDg_top24 : zDg A_top24 24 ([Q; K] ++ top22).
Proof. exact (checkDg_sound ([Q; K] ++ top22) A_top24 ltac:(vm_compute; reflexivity)). Qed.

Lemma zDg_bot8 : zDg 45%N 8 [Q; K; Q; Q; K; Q; K; K].
Proof. exact (checkDg_sound [Q; K; Q; Q; K; Q; K; K] 45%N ltac:(vm_compute; reflexivity)). Qed.

Lemma zDg_mid {A_core : N} {m : nat} {ds_core : list Word}
    (hm : 12 <= m) (hD : zDg A_core (m - 4) ds_core)
    (hA_core : (A_core * 32 <= 25 * 2 ^ (N.of_nat (m - 4)))%N) :
    exists A_mid : N,
      zDg A_mid m ([K; K] ++ ds_core ++ [Q; K]) /\
      (2 <= A_mid)%N /\
      (A_mid <= 2 + 57 * 2 ^ (N.of_nat (m - 7)))%N.
Proof.
  assert (h_kk : zDg 0%N 2 [K; K])
    by exact (checkDg_sound [K; K] 0%N ltac:(vm_compute; reflexivity)).
  assert (h_qk : zDg 1%N 2 [Q; K])
    by exact (checkDg_sound [Q; K] 1%N ltac:(vm_compute; reflexivity)).
  pose proof (zDg_append h_kk hD) as h1.
  pose proof (zDg_append h1 h_qk) as h2.
  replace (2 + (m - 4)) with (m - 2) in h2 by lia.
  replace ((m - 2) + 2) with m in h2 by lia.
  rewrite <- app_assoc in h2.
  assert (h_pow1 : (2 ^ (N.of_nat (m - 4)) = 8 * 2 ^ (N.of_nat (m - 7)))%N).
  { replace (m - 4) with (3 + (m - 7)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 3)%N with 8%N. reflexivity. }
  assert (h_pow2 : (2 ^ (N.of_nat (m - 2)) = 32 * 2 ^ (N.of_nat (m - 7)))%N).
  { replace (m - 2) with (5 + (m - 7)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 5)%N with 32%N. reflexivity. }
  pose proof (zPp_N (N.of_nat (m - 7))) as h_pos_m7.
  exists ((0 + A_core * 2 ^ N.of_nat 2) + 1 * 2 ^ (N.of_nat (m - 2)))%N.
  split; [exact h2 |].
  change (2 ^ N.of_nat 2)%N with 4%N.
  split; lia.
Qed.

Lemma force_a19 {p_41 ds_mid : list Word} {ap A_mid a_top : N} {gp m g_mid : nat}
    (hm : 12 <= m)
    (hP_p : Parse a_41 p_41 ap gp)
    (hz13 : (z13 p_41 * qpow2 m == 256)%Q)
    (hzW : (zW p_41 <= 21#4)%Q)
    (hD_mid : zDg A_mid m ds_mid)
    (hA_lo : (2 <= A_mid)%N)
    (hA_hi : (A_mid <= 2 + 57 * 2 ^ (N.of_nat (m - 7)))%N)
    (hP_mid : Parse (4 * (ap + 1))%N ds_mid a_top g_mid) :
    a_top = (2 ^ 19)%N.
Proof.
  destruct (Parse_la hP_p) as [hla_lo hla_hi].
  pose proof (z12_nonneg p_41) as hz12.
  pose proof (z10_z12_le_zW p_41) as hz10_le.
  assert (h_diff_hi : ((qN ap + 1) * z13 p_41 - (qN a_41 + 1) < 11)%Q) by lra.
  pose proof (qpow2_pos m) as h_powm_pos.
  assert (h_mul_lo : ((qN a_41 + 1) * qpow2 m <= (qN ap + 1) * (z13 p_41 * qpow2 m))%Q)
    by (clear - hla_lo h_powm_pos; nra).
  assert (h_mul_hi : ((qN ap + 1) * (z13 p_41 * qpow2 m) < ((qN a_41 + 1) + 11) * qpow2 m)%Q)
    by (clear - h_diff_hi h_powm_pos; nra).
  rewrite hz13 in h_mul_lo, h_mul_hi.
  assert (ha41_val : (a_41 + 1 = 2 ^ (N.of_nat 25))%N) by (vm_compute; reflexivity).
  assert (h_lo_qN : (qN ((a_41 + 1) * 2 ^ (N.of_nat m))%N <= qN ((ap + 1) * 256)%N)%Q).
  { rewrite !qN_mul, !qN_add, !qN_pow2. norm_qN. lra. }
  apply qN_le_iff in h_lo_qN.
  assert (h_hi_qN : (qN ((ap + 1) * 256)%N < qN (((a_41 + 1) + 11) * 2 ^ (N.of_nat m))%N)%Q).
  { rewrite !qN_mul, !qN_add, !qN_pow2. norm_qN. lra. }
  apply qN_lt_iff in h_hi_qN.
  rewrite ha41_val in h_lo_qN, h_hi_qN.
  replace ((ap + 1) * 256)%N with (4 * (ap + 1) * 64)%N in h_lo_qN, h_hi_qN by lia.
  assert (h_split1 : (2 ^ (N.of_nat 25) * 2 ^ (N.of_nat m) = (2 ^ 19 * 2 ^ (N.of_nat m)) * 64)%N).
  { change (2 ^ N.of_nat 25)%N with (2 ^ 19 * 64)%N. lia. }
  assert (h_split2 : ((2 ^ (N.of_nat 25) + 11) * 2 ^ (N.of_nat m) =
                      (2 ^ 19 * 2 ^ (N.of_nat m) + 11 * 2 ^ (N.of_nat (m - 6))) * 64)%N).
  { rewrite !N.mul_add_distr_r, h_split1. f_equal.
    replace m with (6 + (m - 6)) at 1 by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 6)%N with 64%N. lia. }
  rewrite h_split1 in h_lo_qN.
  rewrite h_split2 in h_hi_qN.
  assert (hap_lo : (2 ^ 19 * 2 ^ (N.of_nat m) <= 4 * (ap + 1))%N) by lia.
  assert (hap_hi : (4 * (ap + 1) < 2 ^ 19 * 2 ^ (N.of_nat m) + 11 * 2 ^ (N.of_nat (m - 6)))%N) by lia.
  assert (h_pow_m6 : (2 ^ (N.of_nat (m - 6)) = 2 * 2 ^ (N.of_nat (m - 7)))%N).
  { replace (m - 6) with (1 + (m - 7)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 1)%N with 2%N. reflexivity. }
  assert (h_pow_m : (2 ^ (N.of_nat m) = 128 * 2 ^ (N.of_nat (m - 7)))%N).
  { replace m with (7 + (m - 7)) at 1 by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 7)%N with 128%N. reflexivity. }
  assert (h_pow_m7_ge : (32 <= 2 ^ (N.of_nat (m - 7)))%N).
  { change 32%N with (2 ^ (N.of_nat 5))%N.
    apply N.pow_le_mono_r; lia. }
  destruct (Parse_zDg_a hP_mid hD_mid) as [h_atop_lo h_atop_hi].
  assert (h_sum_lo : (2 ^ 19 * 2 ^ (N.of_nat m) < 4 * (ap + 1) + A_mid)%N) by lia.
  assert (h_sum_hi : (4 * (ap + 1) + A_mid < (2 ^ 19 + 1) * 2 ^ (N.of_nat m))%N).
  { replace ((2 ^ 19 + 1) * 2 ^ (N.of_nat m))%N
      with (2 ^ 19 * 2 ^ (N.of_nat m) + 128 * 2 ^ (N.of_nat (m - 7)))%N
      by (rewrite h_pow_m; lia).
    lia. }
  assert (h_pos_m : (0 < 2 ^ (N.of_nat m))%N) by exact (zPp_N (N.of_nat m)).
  assert (h_lt1 : (a_top * 2 ^ (N.of_nat m) < (2 ^ 19 + 1) * 2 ^ (N.of_nat m))%N) by lia.
  assert (h_lt2 : (2 ^ 19 * 2 ^ (N.of_nat m) < (a_top + 1) * 2 ^ (N.of_nat m))%N) by lia.
  clear - h_lt1 h_lt2 h_pos_m.
  nia.
Qed.

Lemma bound_b_mid0 {p_41 v_p ds_mid : list Word}
    {ap bp A_mid b_mid0 : N} {gp m : nat}
    (hm : 12 <= m)
    (hS_p : Scan a_41 b_41 p_41 ap bp v_p gp)
    (hbp : (3 <= bp)%N)
    (hz13 : (z13 p_41 * qpow2 m == 256)%Q)
    (hzW : (zW p_41 <= 21#4)%Q)
    (hb_mid0 : b_mid0 = (2048 * (bp - 3) + 1972)%N)
    (hD_mid : zDg A_mid m ds_mid) :
    (2 + 4 * z10 ds_mid < qN b_mid0)%Q.
Proof.
  pose proof (proj2 (Scan_delta hS_p)) as h_delta_p.
  pose proof (z10_z12_le_four_zW_V v_p) as h_4wv_p.
  pose proof (Scan_zW_contract hS_p) as h_cw_p.
  pose proof (proj2 (cPar_bounds b_41)) as hc_b41.
  assert (h_wv_p_lt : (zW_V v_p < 6)%Q) by lra.
  pose proof (z13_Scan hS_p) as h_z13_p.
  pose proof (qpow2_ge_1 (3 * gp)) as h_pow_gp_ge1.
  pose proof (z13_pos v_p) as h_z13_vp_pos.
  assert (h_z13_vp_le : (z13 v_p <= z13 p_41)%Q)
    by (clear - h_z13_p h_pow_gp_ge1 h_z13_vp_pos; nra).
  assert (h_b41_big : (qpow2 28 + 26 < qN b_41)%Q) by (vm_compute; reflexivity).
  assert (h_bp2_pos : (0 <= qN bp - 2)%Q).
  { assert (h2 : (qN 2 <= qN bp)%Q) by (apply qN_le_iff; lia).
    norm_qN. lra. }
  assert (h_prod_p : (qpow2 28 < (qN bp - 2) * z13 p_41)%Q)
    by (clear - h_delta_p h_4wv_p h_wv_p_lt h_b41_big h_bp2_pos h_z13_vp_le; nra).
  pose proof (qpow2_pos m) as h_powm_pos.
  assert (h_mul_m : (qpow2 28 * qpow2 m < (qN bp - 2) * (z13 p_41 * qpow2 m))%Q)
    by (clear - h_prod_p h_powm_pos; nra).
  rewrite hz13 in h_mul_m.
  assert (h_pow28 : (qpow2 28 == qpow2 20 * 256)%Q) by (vm_compute; reflexivity).
  rewrite h_pow28 in h_mul_m.
  assert (h_bp2_gt : (qpow2 20 * qpow2 m < qN bp - 2)%Q) by lra.
  assert (h_bmid0_r : (qN b_mid0 == 2048 * (qN bp - 3) + 1972)%Q).
  { rewrite hb_mid0, qN_add, qN_mul, qN_sub by lia. norm_qN. lra. }
  pose proof (proj2 (zDg_z13_z10 hD_mid)) as h_z10_mid.
  assert (h_pow20_val : (qpow2 20 == 1048576)%Q) by (vm_compute; reflexivity).
  pose proof (qpow2_ge_1 m) as h_powm_ge1.
  rewrite h_z10_mid, h_bmid0_r.
  rewrite h_pow20_val in h_bp2_gt.
  lra.
Qed.

Lemma bound_zW_p41' {p_41 v_p ds_mid v_mid : list Word}
    {ap bp A_mid b_mid0 b_top22 : N} {gp m g_mid : nat}
    (hm : 12 <= m)
    (hS_p : Scan a_41 b_41 p_41 ap bp v_p gp)
    (hz13 : (z13 p_41 * qpow2 m == 256)%Q)
    (hzW : (zW p_41 <= 21#4)%Q)
    (hD_mid : zDg A_mid m ds_mid)
    (hS_mid : Scan (4 * (ap + 1))%N b_mid0 ds_mid (2 ^ 19)%N b_top22 v_mid g_mid) :
    (zW_V (v_p ++ v_s18 ++ v_mid) <= 21#4)%Q.
Proof.
  pose proof (Scan_zW_contract hS_p) as h_cw_p.
  assert (hc_b41 : cPar b_41 = (3#16)%Q) by (vm_compute; reflexivity).
  rewrite hc_b41 in h_cw_p.
  assert (hA : (zW_V v_p <= 327#64)%Q) by lra.
  pose proof (z13_Scan hS_p) as h_z13_p.
  assert (h_z13_s18 : (z13 v_s18 == 1#2048)%Q) by (vm_compute; reflexivity).
  assert (h_wv_s18 : (zW_V v_s18 <= 9#256)%Q) by (vm_compute; discriminate).
  pose proof (qpow2_mono hm) as h_powm_ge12.
  assert (h_z13_p_le : (z13 p_41 <= 1#16)%Q).
  { pose proof (z13_pos p_41) as h_pos_p.
    change (qpow2 12) with 4096%Q in h_powm_ge12.
    clear - hz13 h_powm_ge12 h_pos_p. nra. }
  pose proof (qpow2_ge_1 (3 * gp)) as h_pow_gp_ge1.
  pose proof (z13_pos v_p) as h_z13_vp_pos.
  assert (h_z13_vp_le : (z13 v_p <= 1#16)%Q)
    by (clear - h_z13_p h_z13_p_le h_pow_gp_ge1 h_z13_vp_pos; nra).
  pose proof (zW_V_nonneg v_s18) as h_wv_s18_nn.
  assert (hB : (z13 v_p * zW_V v_s18 <= 9#4096)%Q)
    by (clear - h_z13_vp_le h_wv_s18 h_wv_s18_nn h_z13_vp_pos; nra).
  pose proof (zDg_Scan_dCount hS_mid hD_mid) as h_dc_eq.
  pose proof (proj2 (dCount_bound v_mid)) as h_wv_mid_dc.
  assert (h_dc_le_m : dCount v_mid <= m) by lia.
  pose proof (qpow2_mono h_dc_le_m) as h_pow_dc_le.
  assert (h_wv_mid_le : (zW_V v_mid <= qpow2 m)%Q) by lra.
  assert (h_vp_m : (z13 v_p * qpow2 m <= 256)%Q).
  { assert (h_eq : (z13 v_p * qpow2 m * qpow2 (3 * gp) == 256)%Q).
    { rewrite <- hz13, <- h_z13_p. lra. }
    pose proof (qpow2_pos m) as hm_pos.
    clear - h_eq h_pow_gp_ge1 h_z13_vp_pos hm_pos. nra. }
  assert (h_prod_ps : (z13 (v_p ++ v_s18) * qpow2 m <= 1#8)%Q).
  { rewrite z13_append, h_z13_s18. lra. }
  pose proof (z13_pos (v_p ++ v_s18)) as h_z13_ps_pos.
  assert (hC : (z13 (v_p ++ v_s18) * zW_V v_mid <= 1#8)%Q).
  { pose proof (zW_V_nonneg v_mid) as h_wv_mid_nn.
    clear - h_prod_ps h_wv_mid_le h_wv_mid_nn h_z13_ps_pos. nra. }
  replace (v_p ++ v_s18 ++ v_mid)
    with ((v_p ++ v_s18) ++ v_mid)
    by (rewrite <- app_assoc; reflexivity).
  pose proof (zW_V_append v_p v_s18) as h_app1.
  pose proof (zW_V_append (v_p ++ v_s18) v_mid) as h_app2.
  lra.
Qed.

Lemma bound_b_end_zDg {w_41 v_w41 : list Word} {b_top22 : N} {g_w41 k : nat}
    (hk : 3 <= k)
    (hb_top22 : (2 <= b_top22)%N)
    (hS_w : Scan a_41 b_41 w_41 (2 ^ 19)%N b_top22 v_w41 g_w41)
    (hz13_vw : (z13 v_w41 * qpow2 k == 1)%Q)
    (hWV_vw : (zW_V v_w41 <= 21#4)%Q) :
    exists (A_core' : N) (ds_core' : list Word),
      zDg A_core' (k + 5) ds_core' /\
      length ds_core' = k + 5 /\
      (A_core' * 32 <= 25 * 2 ^ (N.of_nat (k + 5)))%N /\
      zDg (256 * (b_top22 - 2) + 45)%N (k + 37)
          ([Q; K; Q; Q; K; Q; K; K] ++ ds_core' ++ [Q; K] ++ top22).
Proof.
  destruct (Scan_delta hS_w) as [hd_lo hd_hi].
  pose proof (z10_z12_le_four_zW_V v_w41) as h_4wv.
  assert (hd_hi' : ((qN b_41 - 2) - (qN b_top22 - 2) * z13 v_w41 <= 21)%Q) by lra.
  pose proof (qpow2_pos k) as h_powk_pos.
  assert (h_mul_lo : (((qN b_41 - 2) - 21) * qpow2 k <= (qN b_top22 - 2) * (z13 v_w41 * qpow2 k))%Q)
    by (clear - hd_hi' h_powk_pos; nra).
  assert (h_mul_hi : ((qN b_top22 - 2) * (z13 v_w41 * qpow2 k) <= (qN b_41 - 1) * qpow2 k)%Q)
    by (clear - hd_lo h_powk_pos; nra).
  rewrite hz13_vw in h_mul_lo, h_mul_hi.
  assert (hb41_r : (qN b_41 - 2 == qN A_top24 * 32 + 24)%Q) by (vm_compute; reflexivity).
  assert (hb41_1_r : (qN b_41 - 1 == qN A_top24 * 32 + 25)%Q) by (vm_compute; reflexivity).
  rewrite hb41_r in h_mul_lo.
  rewrite hb41_1_r in h_mul_hi.
  set (b_end := (256 * (b_top22 - 2) + 45)%N).
  assert (hb_end_r : (qN b_end == 256 * (qN b_top22 - 2) + 45)%Q).
  { unfold b_end.
    rewrite qN_add, qN_mul, qN_sub by lia.
    norm_qN. lra. }
  assert (h_pow_k13 : (qpow2 (k + 13) == 8192 * qpow2 k)%Q).
  { rewrite qpow2_add. change (qpow2 13) with 8192%Q. lra. }
  pose proof (qpow2_ge_1 k) as h_powk_ge1.
  assert (h_bend_lo_r : (qN (A_top24 * 2 ^ (N.of_nat (k + 13)))%N < qN b_end)%Q).
  { rewrite qN_mul, qN_pow2, hb_end_r, h_pow_k13. lra. }
  assert (h_bend_mid_r : (qN b_end <= qN (A_top24 * 2 ^ (N.of_nat (k + 13)) + 256 * 25 * 2 ^ (N.of_nat k) + 45)%N)%Q).
  { rewrite !qN_add, !qN_mul, !qN_pow2, hb_end_r, h_pow_k13. norm_qN. lra. }
  assert (h_bend_hi_r : (qN b_end < qN ((A_top24 + 1) * 2 ^ (N.of_nat (k + 13)))%N)%Q).
  { rewrite qN_mul, qN_add, qN_pow2, hb_end_r, h_pow_k13. norm_qN. lra. }
  apply qN_lt_iff in h_bend_lo_r.
  apply qN_le_iff in h_bend_mid_r.
  apply qN_lt_iff in h_bend_hi_r.
  assert (h_pow_k13_eq : (2 ^ (N.of_nat (k + 13)) = 256 * 2 ^ (N.of_nat (k + 5)))%N).
  { replace (k + 13) with (8 + (k + 5)) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 8)%N with 256%N. reflexivity. }
  rewrite h_pow_k13_eq in h_bend_lo_r, h_bend_mid_r, h_bend_hi_r.
  set (P5 := (2 ^ (N.of_nat (k + 5)))%N) in *.
  set (Pk := (2 ^ (N.of_nat k))%N) in *.
  assert (h_P5_eq : (P5 = 32 * Pk)%N).
  { unfold P5, Pk. replace (k + 5) with (5 + k) by lia.
    rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 5)%N with 32%N. reflexivity. }
  set (Q256 := (b_end / 256)%N).
  assert (h_b_end_eq : (b_end = 256 * Q256 + 45)%N) by (unfold Q256, b_end; lia).
  assert (h_Q256_lo : (A_top24 * P5 <= Q256)%N) by lia.
  assert (h_Q256_mid : (Q256 <= A_top24 * P5 + 25 * Pk)%N) by lia.
  assert (h_Q256_hi : (Q256 < (A_top24 + 1) * P5)%N) by lia.
  set (A_core' := (Q256 - A_top24 * P5)%N).
  assert (h_Acore'_lt : (A_core' < P5)%N) by (unfold A_core'; lia).
  assert (h_Acore'_32 : (A_core' * 32 <= 25 * P5)%N) by (unfold A_core'; lia).
  destruct (zDg_exists (k + 5) A_core' h_Acore'_lt) as [ds_core' hD_core'].
  pose proof (zDg_len hD_core') as h_len_core'.
  pose proof (zDg_append zDg_bot8 hD_core') as h_bot_mid.
  pose proof (zDg_append h_bot_mid zDg_top24) as h_all.
  replace ((8 + (k + 5)) + 24) with (k + 37) in h_all by lia.
  assert (h_val_all : ((45 + A_core' * 2 ^ N.of_nat 8) + A_top24 * 2 ^ (N.of_nat (8 + (k + 5))) = b_end)%N).
  { rewrite Nat2N.inj_add, N.pow_add_r.
    change (2 ^ N.of_nat 8)%N with 256%N.
    change (2 ^ N.of_nat (k + 5))%N with P5.
    unfold A_core'. lia. }
  rewrite h_val_all in h_all.
  rewrite <- !app_assoc in h_all.
  exists A_core', ds_core'.
  exact (conj hD_core' (conj h_len_core' (conj h_Acore'_32 h_all))).
Qed.

Lemma Good_step {u : list Word} (hG : Good u) :
    exists u', Step u u' /\ Good u'.
Proof.
  destruct hG as [p_41 [ds_core [A_core [m [-> [[p_tail hp_start] [hm_def [hm [hD_core [hA_core [hz13 hzW]]]]]]]]]]].
  assert (hP_p_ex : exists ap gp, Parse a_41 p_41 ap gp).
  { rewrite hp_start. exact (Parse_V_start a_41 p_tail). }
  destruct hP_p_ex as [ap [gp hP_p]].
  assert (hb_41_ok : (2 + 4 * z10 p_41 < qN b_41)%Q).
  { pose proof (z12_nonneg p_41) as hz12.
    pose proof (z10_z12_le_zW p_41) as hz10_le.
    assert (hb41_gt : (25 < qN b_41)%Q) by (vm_compute; reflexivity).
    lra. }
  destruct (Scan_of_Parse hP_p b_41 hb_41_ok) as [bp [v_p [hS_p hbp]]].
  pose proof (Scan_s18 ap bp hbp) as hS_s18.
  set (b_mid0 := (2048 * (bp - 3) + 1972)%N).
  set (ds_mid := [K; K] ++ ds_core ++ [Q; K]).
  destruct (zDg_mid hm hD_core hA_core) as [A_mid [hD_mid [hA_lo hA_hi]]].
  change ([K; K] ++ ds_core ++ [Q; K]) with ds_mid in hD_mid.
  assert (hP_s18_all : exists a_top g_all, Parse ap (s18 ++ ds_mid) a_top g_all).
  { change (s18 ++ ds_mid) with (V :: (List.tl s18 ++ ds_mid)).
    exact (Parse_V_start ap _). }
  destruct hP_s18_all as [a_top [g_all hP_all]].
  destruct (Parse_s18_split hP_all) as [g_mid hP_mid].
  pose proof (force_a19 hm hP_p hz13 hzW hD_mid hA_lo hA_hi hP_mid) as hatop_eq.
  subst a_top.
  pose proof (bound_b_mid0 hm hS_p hbp hz13 hzW eq_refl hD_mid) as hb_mid0_ok.
  destruct (Scan_of_Parse hP_mid b_mid0 hb_mid0_ok) as [b_top22 [v_mid [hS_mid hb_top22_ge3]]].
  assert (hb_top22 : (2 <= b_top22)%N) by lia.
  pose proof (Scan_top22 b_top22 hb_top22) as hS_top22.
  set (w_41 := p_41 ++ s18 ++ ds_mid).
  set (v_w41 := v_p ++ v_s18 ++ v_mid).
  set (g_w41 := gp + 3 + g_mid).
  replace (4 * ap + 4)%N with (4 * (ap + 1))%N in hS_s18 by lia.
  assert (hS_w41 : Scan a_41 b_41 w_41 (2 ^ 19)%N b_top22 v_w41 g_w41).
  { pose proof (Scan_append (Scan_append hS_p hS_s18) hS_mid) as h234.
    unfold w_41, v_w41, g_w41.
    rewrite <- !app_assoc in h234.
    exact h234. }
  assert (h_u_rep0 :
      (head41 ++ p_41 ++ s12 ++ [Q; K; Q; Q; K; Q; K; K] ++ ds_core ++ [Q; K] ++ top22) ++ repeat K 0 =
      head41 ++ w_41 ++ top22).
  { unfold w_41, s18, ds_mid.
    cbn [repeat].
    rewrite app_nil_r, <- !app_assoc. reflexivity. }
  assert (hS_full :
      Scan 0%N 14%N ((head41 ++ p_41 ++ s12 ++ [Q; K; Q; Q; K; Q; K; K] ++ ds_core ++ [Q; K] ++ top22) ++ repeat K 0)
           0%N (256 * (b_top22 - 2) + 45)%N (v_head41 ++ v_w41 ++ s12) (0 + g_w41 + 10)).
  { rewrite h_u_rep0.
    pose proof (Scan_append (Scan_append Scan_head41 hS_w41) hS_top22) as h125.
    rewrite <- !app_assoc in h125.
    exact h125. }
  set (k := 3 + 3 * gp + 3 * g_mid).
  assert (hk : 3 <= k) by lia.
  pose proof (bound_zW_p41' hm hS_p hz13 hzW hD_mid hS_mid) as hWV_vw.
  assert (hz13_vw : (z13 v_w41 * qpow2 k == 1)%Q).
  { pose proof (z13_Scan hS_w41) as h_z13_w.
    assert (h_w_eq : (z13 w_41 == 64)%Q).
    { unfold w_41. rewrite !z13_append.
      assert (h_s18 : (z13 s18 == 1#4)%Q) by (vm_compute; reflexivity).
      pose proof (proj1 (zDg_z13_z10 hD_mid)) as h_mid.
      rewrite h_s18, h_mid.
      lra. }
    rewrite h_w_eq in h_z13_w.
    assert (h_3gw : 3 * g_w41 = k + 6) by (unfold g_w41, k; lia).
    rewrite h_3gw, qpow2_add in h_z13_w.
    change (qpow2 6) with 64%Q in h_z13_w.
    lra. }
  destruct (bound_b_end_zDg hk hb_top22 hS_w41 hz13_vw hWV_vw)
    as [A_core' [ds_core' [hD_core' [hlen_core' [hA_core' hD_bend]]]]].
  set (da := [Q; K; Q; Q; K; Q; K; K] ++ ds_core' ++ [Q; K] ++ top22).
  set (u' := V :: ((v_head41 ++ v_w41 ++ s12) ++ da)).
  exists u'. split.
  - exists 0, (256 * (b_top22 - 2) + 45)%N, (v_head41 ++ v_w41 ++ s12), da, (k + 37), (0 + g_w41 + 10).
    exact (conj hS_full (conj hD_bend eq_refl)).
  - exists (V :: v_w41), ds_core', A_core', (k + 9).
    split.
    + unfold u', da.
      rewrite <- !app_assoc, app_comm_cons, v_head41_eq, <- !app_assoc.
      reflexivity.
    + split; [exists v_w41; reflexivity |].
      split; [lia |].
      split; [lia |].
      split; [replace (k + 9 - 4) with (k + 5) by lia; exact hD_core' |].
      split; [replace (k + 9 - 4) with (k + 5) by lia; exact hA_core' |].
      split.
      * cbn [z13].
        replace (k + 9) with (k + (1 + 8)) by lia.
        rewrite !qpow2_add.
        change (qpow2 1) with 2%Q.
        change (qpow2 8) with 256%Q.
        clear - hz13_vw. nra.
      * rewrite zW_cons_V. exact hWV_vw.
Qed.

Close Scope word_scope.

Lemma nonhalt : ~ halts tm c0.
Proof.
  apply (multistep_nonhalt tm c0 (zCf (zTs u_9 0inf%sym))
           (etrans init_to_u0 (Rounds_exec rounds_0_9))).
  apply (progress_nonhalt_cond tm (list Word) u_9 (fun u => zCf (zTs u 0inf%sym)) Good).
  - intros u hG.
    destruct (Good_step hG) as [u' [hStep hG']].
    exists u'. split; [exact (Step_exec hStep) | exact hG'].
  - exact good_u9.
Qed.
