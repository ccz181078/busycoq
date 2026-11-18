(** * BB(6) Holdout 608:#585 / 797:#771: 1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD *)

From Coq Require Import Lists.List Arith Lia String.
From BusyCoq Require Import Individual62 Longitudinal.
Import ListNotations.

Definition tm : TM := TM_from_str "1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD".

Module M585.

Local Close Scope sym_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition tm0 : TM := Eval compute in tm.

Lemma tm0_eq : tm = tm0.
Proof. reflexivity. Qed.

Notation z0 := (const S0).

(** Right half-tape unit block [X = [1; 1; 0; 1]]. *)
Definition X : list Sym := [S1; S1; S0; S1].

(** Left half-tape unit block [Dr = [1; 1; 0; 0]] (head-adjacent symbol first). *)
Definition Dr : list Sym := [S1; S1; S0; S0].

(** Right-side boundary bounce signal: enter right in [C], exit left in [B]. *)
Definition hf : list (DH0 * DH0) := [((C, []), (B, []))].

(** Left-side dual bounce signal: enter left in [B], exit right in [C]. *)
Definition hfb : list (DH0 * DH0) := [((B, []), (C, []))].

(** Right-side [m]-call wall: [m] consecutive [C]/[B] bounces prepend [[0; 0]]. *)
Definition Wall (m : nat) (r : side) : Prop :=
  sideRLs tm0 (hf ^^ m) r ([S0; S0] *> r).

(** ** Section 1: Stream / Power / Left-Bounce Glue Helpers *)

Lemma even_or_odd (m : nat) : exists k, m = 2 * k \/ m = 2 * k + 1.
Proof.
  exists (Nat.div2 m). apply div2_zify.
Qed.

Lemma lpow_1 {T : Type} (w : list T) : w ^^ 1 = w.
Proof.
  cbn. apply app_nil_r.
Qed.

Lemma lpow_succ_l {T : Type} (w : list T) (n : nat) :
  w ^^ (n + 1) = w ++ w ^^ n.
Proof.
  replace (n + 1) with (S n) by lia. reflexivity.
Qed.

Lemma lpow_succ_r {T : Type} (w : list T) (n : nat) :
  w ^^ (n + 1) = w ^^ n ++ w.
Proof.
  rewrite lpow_add, lpow_1. reflexivity.
Qed.

Lemma lb_append_pow_one (w : list Sym) (s : side) :
  (w ^^ 1) *> s = w *> s.
Proof.
  rewrite lpow_1. reflexivity.
Qed.

Lemma lb_append_pow_add (w : list Sym) (m n : nat) (s : side) :
  (w ^^ (m + n)) *> s = (w ^^ m) *> ((w ^^ n) *> s).
Proof.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma lb_append_pow_succ (w : list Sym) (n : nat) (s : side) :
  (w ^^ (n + 1)) *> s = w *> ((w ^^ n) *> s).
Proof.
  rewrite lpow_succ_l, Str_app_assoc. reflexivity.
Qed.

Lemma lb_append_pow_succ' (w : list Sym) (n : nat) (s : side) :
  (w ^^ (n + 1)) *> s = (w ^^ n) *> (w *> s).
Proof.
  rewrite lpow_succ_r, Str_app_assoc. reflexivity.
Qed.

Lemma lb_append_00_z0 : [S0; S0] *> z0 = z0.
Proof.
  cbn [Str_app]. rewrite <- const_unfold, <- const_unfold. reflexivity.
Qed.

(** Direct multi-visit left-boundary reflection on [M] (avoids [flip_involutive]
    and therefore avoids [functional_extensionality]). *)
Inductive sideLRs (M : TM) : list (DH0 * DH0) -> side -> side -> Prop :=
| sideLRs_O (l : side) : sideLRs M [] l l
| sideLRs_S (h1 h2 : DH0) (l1 l2 l3 : side) (ls : list (DH0 * DH0)) :
    sideLR M h1 h2 l1 l2 ->
    sideLRs M ls l2 l3 ->
    sideLRs M ((h1, h2) :: ls) l1 l3.

Lemma sideLRs_single {M : TM} {h1 h2 : DH0} {l1 l2 : side}
    (H : sideLR M h1 h2 l1 l2) : sideLRs M [(h1, h2)] l1 l2.
Proof.
  exact (sideLRs_S M h1 h2 l1 l2 l2 [] H (sideLRs_O M l2)).
Qed.

Lemma sideLRs_trans {M : TM} {ls1 ls2 : list (DH0 * DH0)} {l1 l2 l3 : side}
    (H1 : sideLRs M ls1 l1 l2) (H2 : sideLRs M ls2 l2 l3) :
    sideLRs M (ls1 ++ ls2) l1 l3.
Proof.
  induction H1 as [l | h1 h2 la lb lc ls Hstep Hrest IH].
  - exact H2.
  - exact (sideLRs_S M h1 h2 la lb _ _ Hstep (IH H2)).
Qed.

Lemma sideLRs_trans_add {M : TM} {h : list (DH0 * DH0)} {n1 n2 : nat}
    {l1 l2 l3 : side}
    (H1 : sideLRs M (h ^^ n1) l1 l3) (H2 : sideLRs M (h ^^ n2) l3 l2) :
    sideLRs M (h ^^ (n1 + n2)) l1 l2.
Proof.
  rewrite lpow_add. exact (sideLRs_trans H1 H2).
Qed.

Lemma sideLRs_trans_succ {M : TM} {h : list (DH0 * DH0)} {n : nat}
    {l1 l2 l3 : side}
    (H1 : sideLRs M (h ^^ n) l1 l3) (H2 : sideLRs M h l3 l2) :
    sideLRs M (h ^^ (n + 1)) l1 l2.
Proof.
  rewrite lpow_add, lpow_1. exact (sideLRs_trans H1 H2).
Qed.

Lemma sideRLs_single {M : TM} {h1 h2 : DH0} {r1 r2 : side}
    (H : sideRL M h1 h2 r1 r2) : sideRLs M [(h1, h2)] r1 r2.
Proof.
  exact (sideRLseq_S M h1 h2 r1 r2 r2 [] H (sideRLseq_O M r2)).
Qed.

Lemma sideRLs_elim_single {M : TM} {hR hL : DH0} {r r' : side}
    (H : sideRLs M [(hR, hL)] r r') (l : side) :
    l {{{ (hR, R) }}} r -[ M ]->+ l {{{ (hL, L) }}} r'.
Proof.
  inversion H as [| ? ? ? r_mid ? ? Hstep Hrest]; subst; clear H.
  inversion Hrest; subst; clear Hrest.
  exact (Hstep l).
Qed.

Lemma sideRLs_trans_succ {M : TM} {h : list (DH0 * DH0)} {n : nat}
    {r1 r2 r3 : side}
    (H1 : sideRLs M (h ^^ n) r1 r3) (H2 : sideRLs M h r3 r2) :
    sideRLs M (h ^^ (n + 1)) r1 r2.
Proof.
  rewrite lpow_add, lpow_1. exact (sideRLs_trans H1 H2).
Qed.

(** Glue left-boundary [sideLRs] with right-boundary [sideRLs] into [-[ M ]->+]. *)
Lemma sideLRs_sideRLs_concat {M : TM} {h1 h2 : DH0}
    {ls : list (DH0 * DH0)} {l1 l2 r1 r2 : side}
    (HL : sideLRs M ls l1 l2)
    (HR : sideRLs M (lrcons h1 ls h2) r1 r2) :
    l1 {{{ (h1, R) }}} r1 -[ M ]->+ l2 {{{ (h2, L) }}} r2.
Proof.
  revert h1 h2 r1 r2 HR.
  induction HL as [l | a b l1 l_mid l2 ls Hleft Hrest IH]; intros h1 h2 r1 r2 HR.
  - cbn [lrcons] in HR.
    exact (sideRLs_elim_single HR l).
  - cbn [lrcons] in HR.
    inversion HR as [| ? ? ? r_mid ? ? Hright HrestR]; subst; clear HR.
    eapply progress_trans; [exact (Hright l1) |].
    eapply progress_trans; [exact (Hleft r_mid) |].
    exact (IH b h2 r_mid r2 HrestR).
Qed.

(** Equal-count ping-pong glue between [sideRLs] and [sideLRs] into [-[ M ]->*]. *)
Lemma sideLRs_sideRLs_concat_1 {M : TM} {hR hL : DH0} {n : nat}
    {l1 l2 r1 r2 : side}
    (HR : sideRLs M ([(hR, hL)] ^^ n) r1 r2)
    (HL : sideLRs M ([(hL, hR)] ^^ n) l1 l2) :
    l1 {{{ (hR, R) }}} r1 -[ M ]->* l2 {{{ (hR, R) }}} r2.
Proof.
  revert l1 l2 r1 r2 HR HL.
  induction n as [| n IH]; intros l1 l2 r1 r2 HR HL.
  - cbn [lpow] in HR, HL.
    inversion HR; subst; clear HR.
    inversion HL; subst; clear HL.
    apply evstep_refl.
  - cbn [lpow app] in HR, HL.
    inversion HR as [| ? ? ? r_mid ? ? Hright HrestR]; subst; clear HR.
    inversion HL as [| ? ? ? l_mid ? ? Hleft HrestL]; subst; clear HL.
    eapply evstep_trans; [apply progress_evstep; exact (Hright l1) |].
    eapply evstep_trans; [apply progress_evstep; exact (Hleft r_mid) |].
    exact (IH l_mid l2 r_mid r2 HrestR HrestL).
Qed.

Lemma wall_zero_z0 : Wall 0 z0.
Proof.
  unfold Wall. rewrite lb_append_00_z0. constructor.
Qed.

(** Micro-stepping tactic for concrete bounded transitions on [tm0]. *)
Ltac bb_steps :=
  unfold X, Dr, to_DH_config, c0, tape0;
  cbn [lpow app Str_app];
  simpl_tape;
  step1s.

(** ** Section 2: Fundamental Shift Lemmas & 2D Space-Time Tiles ([segRLs]) *)

Lemma step_C_X_one (l r : side) :
  l {{C}}> (X *> r) -[ tm0 ]->* (Dr *> l) {{C}}> r.
Proof. bb_steps. Qed.

Lemma shift_C_X (n : nat) (l r : side) :
  l {{C}}> ((X ^^ n) *> r) -[ tm0 ]->* ((Dr ^^ n) *> l) {{C}}> r.
Proof.
  revert l.
  induction n as [| n IH]; intro l.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S n) with (n + 1) by lia.
    rewrite lb_append_pow_succ.
    eapply evstep_trans; [apply step_C_X_one |].
    pose proof (IH (Dr *> l)) as H.
    rewrite <- lb_append_pow_succ' in H.
    exact H.
Qed.

Lemma step_B_Dr_one (l r : side) :
  (Dr *> l) <{{B}} r -[ tm0 ]->* l <{{B}} (X *> r).
Proof. bb_steps. Qed.

Lemma shift_B_Dr (n : nat) (l r : side) :
  ((Dr ^^ n) *> l) <{{B}} r -[ tm0 ]->* l <{{B}} ((X ^^ n) *> r).
Proof.
  revert r.
  induction n as [| n IH]; intro r.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S n) with (n + 1) by lia.
    rewrite lb_append_pow_succ.
    eapply evstep_trans; [apply step_B_Dr_one |].
    pose proof (IH (X *> r)) as H.
    rewrite <- lb_append_pow_succ' in H.
    exact H.
Qed.

Lemma seg_X : segRLs tm0 hf hf X X.
Proof.
  unfold hf.
  change [((C, @nil Sym), (B, @nil Sym))] with
    (lrcons (C, @nil Sym) [] (B, @nil Sym) ++ []).
  eapply segRLs_lrcons with (w3 := Dr) (w4 := Dr) (w5 := X).
  - intros l r. cbn [to_DH_config Str_app]. apply step_C_X_one.
  - intros l r. cbn [to_DH_config Str_app]. apply step_B_Dr_one.
  - constructor.
  - constructor.
Qed.

Lemma seg_X_pow (n : nat) : segRLs tm0 hf hf (X ^^ n) (X ^^ n).
Proof.
  induction n as [| n IH].
  - cbn [lpow]. apply segRLs_nil.
  - cbn [lpow]. exact (segRLs_concat seg_X IH).
Qed.

Lemma seg_X_pow_iter (k n : nat) :
  segRLs tm0 (hf ^^ k) (hf ^^ k) (X ^^ n) (X ^^ n).
Proof.
  induction k as [| k IH].
  - cbn [lpow]. constructor.
  - cbn [lpow]. exact (segRLs_trans (seg_X_pow n) IH).
Qed.

Lemma seg_0X_rr : segRR tm0 (C, []) (C, []) ([S0] ++ X) [S1; S1; S0; S1; S1].
Proof. intros l r. bb_steps. Qed.

Lemma seg_0X_lr :
  segLR tm0 (B, []) (C, []) [S1; S1; S0; S1; S1] [S1; S1; S0; S0; S1].
Proof. intros l r. bb_steps. Qed.

Lemma seg_0X_ll :
  segLL tm0 (B, []) (B, []) [S1; S1; S0; S0; S1] ([S0] ++ X).
Proof. intros l r. bb_steps. Qed.

(** Doubling tile: [[0] ++ X] converts 1 left [hf] call into 2 right [hf] calls. *)
Lemma seg_0X : segRLs tm0 hf (hf ^^ 2) ([S0] ++ X) ([S0] ++ X).
Proof.
  exact (segRLs_1_2 seg_0X_rr seg_0X_lr seg_0X_ll).
Qed.

Lemma seg_0X_iter (a : nat) :
  segRLs tm0 (hf ^^ a) (hf ^^ (2 * a)) ([S0] ++ X) ([S0] ++ X).
Proof.
  induction a as [| a IH].
  - cbn [Nat.mul lpow]. constructor.
  - replace (S a) with (1 + a) by lia.
    replace (2 * (1 + a)) with (2 + 2 * a) by lia.
    rewrite (lpow_add _ 1 a), (lpow_add _ 2 (2 * a)), lpow_1.
    exact (segRLs_trans seg_0X IH).
Qed.

(** ** Section 3: Shifting [[0; 0]] Left Across [X] & [Wall] Constructors *)

Lemma sideRL_X_00 (r : side) :
  sideRL tm0 (C, []) (B, []) (X *> ([S0; S0] *> r)) ([S0; S0] *> (X *> r)).
Proof. intro l. bb_steps. Qed.

Lemma sideRL_X_pow_00 (k : nat) (r : side) :
  sideRL tm0 (C, []) (B, [])
    ((X ^^ (k + 1)) *> ([S0; S0] *> r))
    ((X ^^ k) *> ([S0; S0] *> (X *> r))).
Proof.
  intro l. unfold to_DH_config. cbn [Str_app].
  rewrite lb_append_pow_succ'.
  eapply evstep_progress_trans; [apply shift_C_X |].
  eapply progress_evstep_trans; [apply (sideRL_X_00 r) |].
  apply shift_B_Dr.
Qed.

Lemma sideRL_0X_00 (r : side) :
  sideRL tm0 (C, []) (F, [])
    ([S0] *> (X *> ([S0; S0] *> r)))
    ([S1; S0; S1] *> (X *> r)).
Proof. intro l. bb_steps. Qed.

Lemma sideRL_0X2_00 (r : side) :
  sideRL tm0 (C, []) (B, [])
    ([S0] *> ((X ^^ 2) *> ([S0; S0] *> r)))
    ([S0; S0] *> ([S0] *> ((X ^^ 2) *> r))).
Proof.
  intro l.
  change (X ^^ 2) with (X ++ X).
  repeat rewrite Str_app_assoc.
  bb_steps.
Qed.

(** One [hf] call across [[0] *> X^(k+3) *> [0;0]] shifts [[0;0]] left by 2 [X] blocks. *)
Lemma sideRLs_0X_shift2 (k : nat) (r : side) :
  sideRLs tm0 hf
    ([S0] *> ((X ^^ (k + 3)) *> ([S0; S0] *> r)))
    ([S0] *> ((X ^^ (k + 1)) *> ([S0; S0] *> ((X ^^ 2) *> r)))).
Proof.
  pose proof (sideRLs_single (sideRL_X_pow_00 (k + 1) r)) as H1.
  replace (k + 1 + 1) with (k + 2) in H1 by lia.
  pose proof (sideRLs_single (sideRL_X_pow_00 k (X *> r))) as H2.
  assert (H12 : sideRLs tm0 (hf ^^ 2)
      ((X ^^ (k + 2)) *> ([S0; S0] *> r))
      ((X ^^ k) *> ([S0; S0] *> ((X ^^ 2) *> r)))).
  { change (hf ^^ 2) with (hf ++ hf).
    change (X ^^ 2) with (X ++ X).
    rewrite Str_app_assoc.
    exact (sideRLs_trans H1 H2). }
  pose proof (segRLs_sideRLs_concat seg_0X H12) as Hres.
  rewrite Str_app_assoc, <- lb_append_pow_succ in Hres.
  rewrite Str_app_assoc, <- lb_append_pow_succ in Hres.
  replace (k + 2 + 1) with (k + 3) in Hres by lia.
  exact Hres.
Qed.

Lemma sideRLs_0X_shift2_iter (b : nat) :
  forall (k : nat) (r : side),
    sideRLs tm0 (hf ^^ b)
      ([S0] *> ((X ^^ (2 * b + k + 1)) *> ([S0; S0] *> r)))
      ([S0] *> ((X ^^ (k + 1)) *> ([S0; S0] *> ((X ^^ (2 * b)) *> r)))).
Proof.
  induction b as [| b IH]; intros k r.
  - cbn [Nat.mul Nat.add lpow Str_app]. constructor.
  - pose proof (sideRLs_0X_shift2 (2 * b + k) r) as Hstep.
    replace (2 * S b + k + 1) with (2 * b + k + 3) by lia.
    cbn [lpow].
    eapply sideRLs_trans; [exact Hstep |].
    pose proof (IH k ((X ^^ 2) *> r)) as Hrest.
    rewrite <- lb_append_pow_add in Hrest.
    replace (2 * b + 2) with (2 * S b) in Hrest by lia.
    exact Hrest.
Qed.

Lemma sideRLs_0X_finish_even (b : nat) (r : side) :
  sideRLs tm0 (hf ^^ (b + 1))
    ([S0] *> ((X ^^ (2 * b + 2)) *> ([S0; S0] *> r)))
    ([S0; S0] *> ([S0] *> ((X ^^ (2 * b + 2)) *> r))).
Proof.
  pose proof (sideRLs_0X_shift2_iter b 1 r) as H1.
  pose proof (sideRLs_single (sideRL_0X2_00 ((X ^^ (2 * b)) *> r))) as H2.
  pose proof (sideRLs_trans_succ H1 H2) as H12.
  rewrite <- lb_append_pow_add in H12.
  replace (2 * b + 1 + 1) with (2 * b + 2) in H12 by lia.
  replace (2 + 2 * b) with (2 * b + 2) in H12 by lia.
  exact H12.
Qed.

Lemma sideRLs_0X_finish_odd (b : nat) (r : side) :
  sideRLs tm0 (hf ^^ b ++ [((C, []), (F, []))])
    ([S0] *> ((X ^^ (2 * b + 1)) *> ([S0; S0] *> r)))
    ([S1; S0; S1] *> ((X ^^ (2 * b + 1)) *> r)).
Proof.
  pose proof (sideRLs_0X_shift2_iter b 0 r) as H1.
  replace (2 * b + 0 + 1) with (2 * b + 1) in H1 by lia.
  replace (0 + 1) with 1 in H1 by lia.
  rewrite lb_append_pow_one in H1.
  pose proof (sideRLs_single (sideRL_0X_00 ((X ^^ (2 * b)) *> r))) as H2.
  pose proof (sideRLs_trans H1 H2) as H12.
  rewrite <- lb_append_pow_succ in H12.
  exact H12.
Qed.

(** Even wall-building step: if [Wall m r], [n >= 2], and [m + n = 2 * k],
    then [Wall k ([0] *> X^n *> r)]. *)
Lemma wall_cons_even {m n k : nat} {r : side}
    (Hw : Wall m r) (Hn : n >= 2) (Hsum : m + n = 2 * k) :
    Wall k ([S0] *> ((X ^^ n) *> r)).
Proof.
  unfold Wall in Hw |- *.
  destruct (even_or_odd m) as [a [Hm | Hm]]; subst m.
  - destruct (even_or_odd (n - 2)) as [b [Hb | Hb]]; [| lia].
    assert (Hn_eq : n = 2 * b + 2) by lia.
    assert (Hk_eq : k = a + (b + 1)) by lia.
    subst n k.
    pose proof (segRLs_concat (seg_0X_iter a) (seg_X_pow_iter (2 * a) (2 * b + 1))) as Htile.
    pose proof (segRLs_sideRLs_concat Htile Hw) as H1.
    repeat rewrite Str_app_assoc in H1.
    repeat rewrite <- lb_append_pow_succ in H1.
    replace (2 * b + 1 + 1) with (2 * b + 2) in H1 by lia.
    exact (sideRLs_trans_add _ _ _ _ _ _ _ H1 (sideRLs_0X_finish_even b r)).
  - destruct (even_or_odd (n - 3)) as [b [Hb | Hb]]; [| lia].
    assert (Hn_eq : n = 2 * b + 3) by lia.
    assert (Hk_eq : k = (a + 1) + (b + 1)) by lia.
    subst n k.
    rewrite lpow_add, lpow_1 in Hw.
    destruct (sideRLs_split Hw) as [r_mid [Hw1 Hw2]].
    pose proof (segRLs_concat (seg_0X_iter a) (seg_X_pow_iter (2 * a) (2 * b + 2))) as HtileA.
    pose proof (segRLs_sideRLs_concat HtileA Hw1) as HA.
    repeat rewrite Str_app_assoc in HA.
    repeat rewrite <- lb_append_pow_succ in HA.
    replace (2 * b + 2 + 1) with (2 * b + 3) in HA by lia.
    pose proof (segRLs_sideRLs_concat (seg_X_pow (2 * b + 2)) Hw2) as HB1.
    pose proof (sideRLs_single (sideRL_X_pow_00 (2 * b + 1) r)) as HB2.
    replace (2 * b + 1 + 1) with (2 * b + 2) in HB2 by lia.
    assert (HB12 : sideRLs tm0 (hf ^^ 2)
        ((X ^^ (2 * b + 2)) *> r_mid)
        ((X ^^ (2 * b + 1)) *> ([S0; S0] *> (X *> r)))).
    { change (hf ^^ 2) with (hf ++ hf). exact (sideRLs_trans HB1 HB2). }
    pose proof (segRLs_sideRLs_concat seg_0X HB12) as HB.
    repeat rewrite Str_app_assoc in HB.
    repeat rewrite <- lb_append_pow_succ in HB.
    replace (2 * b + 2 + 1) with (2 * b + 3) in HB by lia.
    replace (2 * b + 1 + 1) with (2 * b + 2) in HB by lia.
    pose proof (sideRLs_0X_finish_even b (X *> r)) as HC.
    rewrite <- lb_append_pow_succ' in HC.
    replace (2 * b + 2 + 1) with (2 * b + 3) in HC by lia.
    exact (sideRLs_trans_add _ _ _ _ _ _ _ (sideRLs_trans_succ HA HB) HC).
Qed.

(** Odd wall-building step: if [Wall m r], [n >= 2], and [m + n = 2 * k + 1],
    then [k] [hf] calls followed by one [(C, F)] call rewrite
    [[0] *> X^n *> r] to [[1; 0; 1] *> X^n *> r]. *)
Lemma wall_cons_odd {m n k : nat} {r : side}
    (Hw : Wall m r) (Hn : n >= 2) (Hsum : m + n = 2 * k + 1) :
    sideRLs tm0 (hf ^^ k ++ [((C, []), (F, []))])
      ([S0] *> ((X ^^ n) *> r))
      ([S1; S0; S1] *> ((X ^^ n) *> r)).
Proof.
  unfold Wall in Hw.
  destruct (even_or_odd m) as [a [Hm | Hm]]; subst m.
  - destruct (even_or_odd (n - 1)) as [b [Hb | Hb]]; [| lia].
    assert (Hn_eq : n = 2 * b + 1) by lia.
    assert (Hk_eq : k = a + b) by lia.
    subst n k.
    pose proof (segRLs_concat (seg_0X_iter a) (seg_X_pow_iter (2 * a) (2 * b))) as Htile.
    pose proof (segRLs_sideRLs_concat Htile Hw) as H1.
    repeat rewrite Str_app_assoc in H1.
    repeat rewrite <- lb_append_pow_succ in H1.
    pose proof (sideRLs_0X_finish_odd b r) as H2.
    pose proof (sideRLs_trans H1 H2) as Hres.
    rewrite app_assoc, <- lpow_add in Hres.
    exact Hres.
  - destruct (even_or_odd (n - 2)) as [b [Hb | Hb]]; [| lia].
    assert (Hn_eq : n = 2 * b + 2) by lia.
    assert (Hk_eq : k = (a + 1) + b) by lia.
    subst n k.
    rewrite lpow_add, lpow_1 in Hw.
    destruct (sideRLs_split Hw) as [r_mid [Hw1 Hw2]].
    pose proof (segRLs_concat (seg_0X_iter a) (seg_X_pow_iter (2 * a) (2 * b + 1))) as HtileA.
    pose proof (segRLs_sideRLs_concat HtileA Hw1) as HA.
    repeat rewrite Str_app_assoc in HA.
    repeat rewrite <- lb_append_pow_succ in HA.
    replace (2 * b + 1 + 1) with (2 * b + 2) in HA by lia.
    pose proof (segRLs_sideRLs_concat (seg_X_pow (2 * b + 1)) Hw2) as HB1.
    pose proof (sideRLs_single (sideRL_X_pow_00 (2 * b) r)) as HB2.
    assert (HB12 : sideRLs tm0 (hf ^^ 2)
        ((X ^^ (2 * b + 1)) *> r_mid)
        ((X ^^ (2 * b)) *> ([S0; S0] *> (X *> r)))).
    { change (hf ^^ 2) with (hf ++ hf). exact (sideRLs_trans HB1 HB2). }
    pose proof (segRLs_sideRLs_concat seg_0X HB12) as HB.
    repeat rewrite Str_app_assoc in HB.
    repeat rewrite <- lb_append_pow_succ in HB.
    replace (2 * b + 1 + 1) with (2 * b + 2) in HB by lia.
    pose proof (sideRLs_0X_finish_odd b (X *> r)) as HC.
    rewrite <- lb_append_pow_succ' in HC.
    replace (2 * b + 1 + 1) with (2 * b + 2) in HC by lia.
    pose proof (sideRLs_trans (sideRLs_trans_succ HA HB) HC) as Hres.
    rewrite app_assoc, <- lpow_add in Hres.
    exact Hres.
Qed.

(** ** Section 4: Left-Boundary Period-3 Counters ([sideLRs tm0]) *)

Lemma lb_phase0_base (r : side) :
  (Dr *> ([S1] *> z0)) <{{B}} r -[ tm0 ]->+
    ([S1; S1; S0; S1; S1; S1] *> z0) {{C}}> r.
Proof. bb_steps. Qed.

Lemma lb_phase1_base (r : side) :
  ([S1; S1; S0; S1; S1; S1] *> z0) <{{B}} r -[ tm0 ]->+
    (Dr *> ([S1; S1] *> z0)) {{C}}> r.
Proof. bb_steps. Qed.

Lemma lb_phase2_base (r : side) :
  (Dr *> ([S1; S1] *> z0)) <{{B}} r -[ tm0 ]->+
    ((Dr ^^ 2) *> ([S1] *> z0)) {{C}}> r.
Proof.
  change (Dr ^^ 2) with (Dr ++ Dr).
  rewrite Str_app_assoc.
  bb_steps.
Qed.

Lemma left_p0 (k : nat) :
  sideLR tm0 (B, []) (C, [])
    ((Dr ^^ (k + 1)) *> ([S1] *> z0))
    ((Dr ^^ k) *> ([S1; S1; S0; S1; S1; S1] *> z0)).
Proof.
  intro r. unfold to_DH_config. cbn [Str_app].
  rewrite lb_append_pow_succ'.
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_evstep_trans; [apply lb_phase0_base |].
  apply shift_C_X.
Qed.

Lemma left_p1 (k : nat) :
  sideLR tm0 (B, []) (C, [])
    ((Dr ^^ k) *> ([S1; S1; S0; S1; S1; S1] *> z0))
    ((Dr ^^ (k + 1)) *> ([S1; S1] *> z0)).
Proof.
  intro r. unfold to_DH_config. cbn [Str_app].
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_evstep_trans; [apply lb_phase1_base |].
  rewrite lb_append_pow_succ'.
  apply shift_C_X.
Qed.

Lemma left_p2 (k : nat) :
  sideLR tm0 (B, []) (C, [])
    ((Dr ^^ (k + 1)) *> ([S1; S1] *> z0))
    ((Dr ^^ (k + 2)) *> ([S1] *> z0)).
Proof.
  intro r. unfold to_DH_config. cbn [Str_app].
  rewrite lb_append_pow_succ'.
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_evstep_trans; [apply lb_phase2_base |].
  pose proof (shift_C_X k ((Dr ^^ 2) *> ([S1] *> z0)) r) as Ht.
  rewrite <- lb_append_pow_add in Ht.
  exact Ht.
Qed.

Lemma left_plain_3 (k : nat) :
  sideLRs tm0 (hfb ^^ 3)
    ((Dr ^^ (k + 1)) *> ([S1] *> z0))
    ((Dr ^^ (k + 2)) *> ([S1] *> z0)).
Proof.
  exact (sideLRs_S tm0 _ _ _ _ _ _ (left_p0 k)
    (sideLRs_S tm0 _ _ _ _ _ _ (left_p1 k) (sideLRs_single (left_p2 k)))).
Qed.

Lemma left_plain_3j (j : nat) :
  forall k : nat,
    sideLRs tm0 (hfb ^^ (3 * j))
      ((Dr ^^ (k + 1)) *> ([S1] *> z0))
      ((Dr ^^ (k + j + 1)) *> ([S1] *> z0)).
Proof.
  induction j as [| j IH]; intro k.
  - cbn [Nat.mul lpow]. replace (k + 0 + 1) with (k + 1) by lia. constructor.
  - replace (3 * S j) with (3 + 3 * j) by lia.
    pose proof (left_plain_3 k) as H1.
    pose proof (IH (k + 1)) as H2.
    replace (k + 1 + 1) with (k + 2) in H2 by lia.
    replace (k + 1 + j + 1) with (k + S j + 1) in H2 by lia.
    exact (sideLRs_trans_add H1 H2).
Qed.

(** [[1; 0; 0]] separator counter (universal left tail [l]). *)

Lemma lb_100_p0_base (l r : side) :
  (Dr *> ([S1; S0; S0] *> l)) <{{B}} r -[ tm0 ]->+
    ([S1; S1; S0; S1; S1; S1; S0] *> l) {{C}}> r.
Proof. bb_steps. Qed.

Lemma lb_100_p1_base (l r : side) :
  ([S1; S1; S0; S1; S1; S1; S0] *> l) <{{B}} r -[ tm0 ]->+
    (Dr *> ([S1; S1; S0] *> l)) {{C}}> r.
Proof. bb_steps. Qed.

Lemma lb_100_p2_step_base (l r : side) :
  ([S1; S1; S0] *> (Dr *> l)) <{{B}} r -[ tm0 ]->+
    (Dr *> ([S1; S0; S0] *> l)) {{C}}> r.
Proof. bb_steps. Qed.

Lemma lb_100_p2_base_def (r : side) :
  ([S1; S1; S0; S1] *> z0) <{{B}} r -[ tm0 ]->+
    ((Dr ^^ 2) *> ([S1] *> z0)) {{C}}> r.
Proof.
  change (Dr ^^ 2) with (Dr ++ Dr).
  rewrite Str_app_assoc.
  bb_steps.
Qed.

Lemma left100_p0 (k : nat) (l : side) :
  sideLR tm0 (B, []) (C, [])
    ((Dr ^^ (k + 1)) *> ([S1; S0; S0] *> l))
    ((Dr ^^ k) *> ([S1; S1; S0; S1; S1; S1; S0] *> l)).
Proof.
  intro r. unfold to_DH_config. cbn [Str_app].
  rewrite lb_append_pow_succ'.
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_evstep_trans; [apply lb_100_p0_base |].
  apply shift_C_X.
Qed.

Lemma left100_p1 (k : nat) (l : side) :
  sideLR tm0 (B, []) (C, [])
    ((Dr ^^ k) *> ([S1; S1; S0; S1; S1; S1; S0] *> l))
    ((Dr ^^ (k + 1)) *> ([S1; S1; S0] *> l)).
Proof.
  intro r. unfold to_DH_config. cbn [Str_app].
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_evstep_trans; [apply lb_100_p1_base |].
  rewrite lb_append_pow_succ'.
  apply shift_C_X.
Qed.

Lemma left100_p2_step (k : nat) (l : side) :
  sideLR tm0 (B, []) (C, [])
    ((Dr ^^ (k + 1)) *> ([S1; S1; S0] *> (Dr *> l)))
    ((Dr ^^ (k + 2)) *> ([S1; S0; S0] *> l)).
Proof.
  intro r. unfold to_DH_config. cbn [Str_app].
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_evstep_trans; [apply lb_100_p2_step_base |].
  pose proof (shift_C_X (k + 1) (Dr *> ([S1; S0; S0] *> l)) r) as Ht.
  rewrite <- lb_append_pow_succ' in Ht.
  replace (k + 1 + 1) with (k + 2) in Ht by lia.
  exact Ht.
Qed.

Lemma left100_p2_base (k : nat) :
  sideLR tm0 (B, []) (C, [])
    ((Dr ^^ (k + 1)) *> ([S1; S1; S0; S1] *> z0))
    ((Dr ^^ (k + 3)) *> ([S1] *> z0)).
Proof.
  intro r. unfold to_DH_config. cbn [Str_app].
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_evstep_trans; [apply lb_100_p2_base_def |].
  pose proof (shift_C_X (k + 1) ((Dr ^^ 2) *> ([S1] *> z0)) r) as Ht.
  rewrite <- lb_append_pow_add in Ht.
  replace (k + 1 + 2) with (k + 3) in Ht by lia.
  exact Ht.
Qed.

Lemma left100_3_step (k : nat) (l : side) :
  sideLRs tm0 (hfb ^^ 3)
    ((Dr ^^ (k + 1)) *> ([S1; S0; S0] *> (Dr *> l)))
    ((Dr ^^ (k + 2)) *> ([S1; S0; S0] *> l)).
Proof.
  exact (sideLRs_S tm0 _ _ _ _ _ _ (left100_p0 k (Dr *> l))
    (sideLRs_S tm0 _ _ _ _ _ _ (left100_p1 k (Dr *> l))
      (sideLRs_single (left100_p2_step k l)))).
Qed.

Lemma left100_3_base (k : nat) :
  sideLRs tm0 (hfb ^^ 3)
    ((Dr ^^ (k + 1)) *> ([S1; S0; S0] *> ([S1] *> z0)))
    ((Dr ^^ (k + 3)) *> ([S1] *> z0)).
Proof.
  exact (sideLRs_S tm0 _ _ _ _ _ _ (left100_p0 k ([S1] *> z0))
    (sideLRs_S tm0 _ _ _ _ _ _ (left100_p1 k ([S1] *> z0))
      (sideLRs_single (left100_p2_base k)))).
Qed.

Lemma left100_3t (t : nat) :
  forall (k : nat) (l : side),
    sideLRs tm0 (hfb ^^ (3 * t))
      ((Dr ^^ (k + 1)) *> ([S1; S0; S0] *> ((Dr ^^ t) *> l)))
      ((Dr ^^ (k + t + 1)) *> ([S1; S0; S0] *> l)).
Proof.
  induction t as [| t IH]; intros k l.
  - cbn [Nat.mul lpow Str_app]. replace (k + 0 + 1) with (k + 1) by lia. constructor.
  - replace (S t) with (t + 1) by lia.
    replace (3 * (t + 1)) with (3 + 3 * t) by lia.
    rewrite (lb_append_pow_succ Dr t l).
    pose proof (left100_3_step k ((Dr ^^ t) *> l)) as H1.
    pose proof (IH (k + 1) l) as H2.
    replace (k + 1 + 1) with (k + 2) in H2 by lia.
    replace (k + 1 + t + 1) with (k + (t + 1) + 1) in H2 by lia.
    exact (sideLRs_trans_add H1 H2).
Qed.

(** ** Section 5: Drains After [[0; 0] *> r] Returns *)

Lemma step_B_default_entry (r : side) :
  z0 <{{B}} r -[ tm0 ]->+ ([S1] *> z0) {{C}}> r.
Proof. bb_steps. Qed.

Lemma step_C_00_Dr (l r : side) :
  (Dr *> l) {{C}}> ([S0; S0] *> r) -[ tm0 ]->+ l <{{B}} ([S0; S0] *> (X *> r)).
Proof. bb_steps. Qed.

Lemma step_B_11_default (r : side) :
  ([S1; S1] *> z0) <{{B}} r -[ tm0 ]->+ z0 <{{B}} ([S0; S0] *> r).
Proof. bb_steps. Qed.

Lemma step_B_1101_default (r : side) :
  ([S1; S1; S0; S1] *> z0) <{{B}} r -[ tm0 ]->+ z0 <{{B}} ([S0; S0] *> (X *> r)).
Proof. bb_steps. Qed.

Lemma step_B_00_def (r : side) :
  z0 <{{B}} ([S0; S0] *> r) -[ tm0 ]->+ z0 <{{B}} (X *> r).
Proof. bb_steps. Qed.

Lemma step_B_X_00_def (r : side) :
  z0 <{{B}} (X *> ([S0; S0] *> r)) -[ tm0 ]->+
    z0 <{{B}} (X *> ([S0] *> (X *> r))).
Proof. bb_steps. Qed.

Lemma step_B_X2_00_def (r : side) :
  z0 <{{B}} ((X ^^ 2) *> ([S0; S0] *> r)) -[ tm0 ]->+
    z0 <{{B}} ((X ^^ 4) *> r).
Proof.
  change (X ^^ 2) with (X ++ X).
  change (X ^^ 4) with (X ++ X ++ X ++ X).
  repeat rewrite Str_app_assoc.
  bb_steps.
Qed.

Lemma step_F_exit_entry (l r : side) :
  (Dr *> l) <{{F}} ([S1; S0; S1] *> r) -[ tm0 ]->+
    (Dr *> ([S1; S0; S0] *> l)) {{C}}> r.
Proof. bb_steps. Qed.

Lemma drain_A2 (u : nat) (r : side) :
  ((Dr ^^ u) *> ([S1; S1; S0; S1; S1; S1] *> z0)) <{{B}} ([S0; S0] *> r) -[ tm0 ]->+
    z0 <{{B}} ((X ^^ (u + 1)) *> ([S0; S0] *> (X *> r))).
Proof.
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply lb_phase1_base |].
  eapply evstep_progress_trans; [apply shift_C_X |].
  rewrite <- (lb_append_pow_succ' Dr u), (lb_append_pow_succ Dr u).
  eapply progress_trans; [apply step_C_00_Dr |].
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply step_B_11_default |].
  rewrite (lb_append_pow_succ X u).
  apply step_B_00_def.
Qed.

Lemma drain_X_00_step (k : nat) (r : side) :
  z0 <{{B}} ((X ^^ (k + 3)) *> ([S0; S0] *> r)) -[ tm0 ]->+
    z0 <{{B}} ((X ^^ (k + 1)) *> ([S0; S0] *> ((X ^^ 3) *> r))).
Proof.
  eapply progress_trans; [apply step_B_default_entry |].
  eapply evstep_progress_trans; [apply shift_C_X |].
  replace (k + 3) with ((k + 2) + 1) by lia.
  rewrite (lb_append_pow_succ Dr (k + 2)).
  eapply progress_trans; [apply step_C_00_Dr |].
  replace (k + 2) with ((k + 1) + 1) by lia.
  rewrite (lb_append_pow_succ' Dr (k + 1)).
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply lb_phase0_base |].
  eapply evstep_progress_trans; [apply shift_C_X |].
  rewrite (lb_append_pow_succ Dr k).
  eapply progress_trans; [apply step_C_00_Dr |].
  pose proof (drain_A2 k (X *> (X *> r))) as H4.
  change (X ^^ 3) with (X ++ X ++ X).
  repeat rewrite Str_app_assoc.
  exact H4.
Qed.

Lemma drain_X_00_odd (m : nat) :
  forall r : side,
    z0 <{{B}} ((X ^^ (2 * m + 1)) *> ([S0; S0] *> r)) -[ tm0 ]->+
      z0 <{{B}} (X *> ([S0] *> ((X ^^ (3 * m + 1)) *> r))).
Proof.
  induction m as [| m IH]; intro r.
  - cbn [Nat.mul Nat.add]. repeat rewrite lb_append_pow_one. apply step_B_X_00_def.
  - replace (2 * S m + 1) with (2 * m + 3) by lia.
    eapply progress_trans; [apply drain_X_00_step |].
    pose proof (IH ((X ^^ 3) *> r)) as Hrest.
    rewrite <- lb_append_pow_add in Hrest.
    replace (3 * m + 1 + 3) with (3 * S m + 1) in Hrest by lia.
    exact Hrest.
Qed.

Lemma drain_X_00_even (m : nat) :
  forall r : side,
    z0 <{{B}} ((X ^^ (2 * m + 2)) *> ([S0; S0] *> r)) -[ tm0 ]->+
      z0 <{{B}} ((X ^^ (3 * m + 4)) *> r).
Proof.
  induction m as [| m IH]; intro r.
  - cbn [Nat.mul Nat.add]. apply step_B_X2_00_def.
  - replace (2 * S m + 2) with ((2 * m + 1) + 3) by lia.
    eapply progress_trans; [apply drain_X_00_step |].
    replace (2 * m + 1 + 1) with (2 * m + 2) by lia.
    pose proof (IH ((X ^^ 3) *> r)) as Hrest.
    rewrite <- lb_append_pow_add in Hrest.
    replace (3 * m + 4 + 3) with (3 * S m + 4) in Hrest by lia.
    exact Hrest.
Qed.

Lemma drain_B1_step (a : nat) (l r : side) :
  ((Dr ^^ (a + 2)) *> ([S1; S1; S0; S1; S1; S1; S0] *> (Dr *> l))) <{{B}} ([S0; S0] *> r)
    -[ tm0 ]->+
  ((Dr ^^ a) *> ([S1; S1; S0; S1; S1; S1; S0] *> l)) <{{B}} ([S0; S0] *> ((X ^^ 3) *> r)).
Proof.
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply lb_100_p1_base |].
  eapply evstep_progress_trans; [apply shift_C_X |].
  rewrite <- (lb_append_pow_succ' Dr (a + 2)), (lb_append_pow_succ Dr (a + 2)).
  eapply progress_trans; [apply step_C_00_Dr |].
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply lb_100_p2_step_base |].
  eapply evstep_progress_trans; [apply shift_C_X |].
  rewrite <- (lb_append_pow_succ' Dr (a + 2)), (lb_append_pow_succ Dr (a + 2)).
  eapply progress_trans; [apply step_C_00_Dr |].
  replace (a + 2) with ((a + 1) + 1) by lia.
  rewrite (lb_append_pow_succ' Dr (a + 1)).
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply lb_100_p0_base |].
  eapply evstep_progress_trans; [apply shift_C_X |].
  rewrite (lb_append_pow_succ Dr a).
  pose proof (step_C_00_Dr ((Dr ^^ a) *> ([S1; S1; S0; S1; S1; S1; S0] *> l)) (X *> (X *> r))) as Hfin.
  change (X ^^ 3) with (X ++ X ++ X).
  repeat rewrite Str_app_assoc.
  exact Hfin.
Qed.

Lemma drain_B1_base (a : nat) (r : side) :
  ((Dr ^^ a) *> ([S1; S1; S0; S1; S1; S1; S0] *> ([S1] *> z0))) <{{B}} ([S0; S0] *> r)
    -[ tm0 ]->+
  z0 <{{B}} ((X ^^ (a + 2)) *> ([S0; S0] *> (X *> r))).
Proof.
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply lb_100_p1_base |].
  eapply evstep_progress_trans; [apply shift_C_X |].
  rewrite <- (lb_append_pow_succ' Dr a), (lb_append_pow_succ Dr a).
  change ([S1; S1; S0] *> ([S1] *> z0)) with ([S1; S1; S0; S1] *> z0).
  eapply progress_trans; [apply step_C_00_Dr |].
  eapply evstep_progress_trans; [apply shift_B_Dr |].
  eapply progress_trans; [apply step_B_1101_default |].
  replace (a + 2) with ((a + 1) + 1) by lia.
  rewrite (lb_append_pow_succ X (a + 1)), (lb_append_pow_succ X a).
  apply step_B_00_def.
Qed.

Lemma drain_B1_iter (b : nat) :
  forall (k : nat) (r : side),
    ((Dr ^^ (2 * b + k)) *> ([S1; S1; S0; S1; S1; S1; S0] *> ((Dr ^^ b) *> ([S1] *> z0))))
      <{{B}} ([S0; S0] *> r) -[ tm0 ]->*
    ((Dr ^^ k) *> ([S1; S1; S0; S1; S1; S1; S0] *> ([S1] *> z0)))
      <{{B}} ([S0; S0] *> ((X ^^ (3 * b)) *> r)).
Proof.
  induction b as [| b IH]; intros k r.
  - cbn [Nat.mul Nat.add lpow Str_app]. apply evstep_refl.
  - replace (S b) with (b + 1) by lia.
    replace (2 * (b + 1) + k) with ((2 * b + k) + 2) by lia.
    rewrite (lb_append_pow_succ Dr b).
    eapply evstep_trans; [apply progress_evstep; apply drain_B1_step |].
    pose proof (IH k ((X ^^ 3) *> r)) as Hrest.
    rewrite <- lb_append_pow_add in Hrest.
    replace (3 * b + 3) with (3 * (b + 1)) in Hrest by lia.
    exact Hrest.
Qed.

Lemma drain_B1_full (k b : nat) (r : side) :
  ((Dr ^^ (2 * b + (2 * k + 1))) *> ([S1; S1; S0; S1; S1; S1; S0] *> ((Dr ^^ b) *> ([S1] *> z0))))
    <{{B}} ([S0; S0] *> r) -[ tm0 ]->+
  z0 <{{B}} (X *> ([S0] *> ((X ^^ (3 * (k + b + 1) + 2)) *> r))).
Proof.
  eapply evstep_progress_trans; [apply drain_B1_iter |].
  eapply progress_trans; [apply drain_B1_base |].
  replace ((2 * k + 1) + 2) with (2 * (k + 1) + 1) by lia.
  pose proof (drain_X_00_odd (k + 1) (X *> ((X ^^ (3 * b)) *> r))) as H2.
  assert (Hexp : (X ^^ (3 * (k + 1) + 1)) *> (X *> ((X ^^ (3 * b)) *> r)) =
      (X ^^ (3 * (k + b + 1) + 2)) *> r).
  { rewrite <- (lb_append_pow_succ X (3 * b) r), <- lb_append_pow_add.
    f_equal. f_equal. lia. }
  rewrite Hexp in H2.
  exact H2.
Qed.

(** ** Section 6: Closed Two-State Invariant [Inv] & Progress Theorem *)

Inductive Inv : Q * tape -> Prop :=
| Inv_normal (d a : nat) (r : side) :
    d >= 1 -> a >= 1 -> Wall (3 * d - 1) r ->
    Inv (z0 <{{B}} ((X ^^ a) *> r))
| Inv_merging (d q : nat) (r : side) :
    d >= 1 -> Wall (3 * d - 1) r ->
    Inv (z0 <{{B}} (X *> ([S0] *> ((X ^^ (3 * q + 2)) *> r)))).

Lemma step_normal {d a : nat} {r : side}
    (Hd : d >= 1) (Ha : a >= 1) (Hw : Wall (3 * d - 1) r) :
    exists c', Inv c' /\ (z0 <{{B}} ((X ^^ a) *> r)) -[ tm0 ]->+ c'.
Proof.
  assert (H1 : (z0 <{{B}} ((X ^^ a) *> r)) -[ tm0 ]->+
      (((Dr ^^ a) *> ([S1] *> z0)) {{C}}> r)).
  { eapply progress_evstep_trans; [apply step_B_default_entry | apply shift_C_X]. }
  assert (Hm_ne : 3 * d - 1 <> 0) by lia.
  pose proof (left_plain_3j (d - 1) (a - 1)) as Hl1.
  pose proof (sideLRs_single (left_p0 (a - 1 + (d - 1)))) as Hl2.
  assert (Hl : sideLRs tm0 (hfb ^^ (3 * d - 1 - 1))
      ((Dr ^^ a) *> ([S1] *> z0))
      ((Dr ^^ (a + d - 2)) *> ([S1; S1; S0; S1; S1; S1] *> z0))).
  { pose proof (sideLRs_trans_succ Hl1 Hl2) as Hcomb.
    replace (3 * (d - 1) + 1) with (3 * d - 1 - 1) in Hcomb by lia.
    replace (a - 1 + 1) with a in Hcomb by lia.
    replace (a - 1 + (d - 1)) with (a + d - 2) in Hcomb by lia.
    exact Hcomb. }
  assert (Hr : sideRLs tm0 (lrcons (C, []) (hfb ^^ (3 * d - 1 - 1)) (B, []))
      r ([S0; S0] *> r)).
  { unfold hfb. rewrite lrcons_lpow1 by exact Hm_ne. exact Hw. }
  pose proof (sideLRs_sideRLs_concat Hl Hr) as Hglue.
  cbn [to_DH_config Str_app] in Hglue.
  pose proof (progress_trans _ _ _ _ H1 Hglue) as Hmid.
  pose proof (progress_trans _ _ _ _ Hmid (drain_A2 (a + d - 2) r)) as Hreach.
  destruct (even_or_odd (a + d - 2)) as [k [Hk | Hk]].
  - replace (a + d - 2 + 1) with (2 * k + 1) in Hreach by lia.
    pose proof (drain_X_00_odd k (X *> r)) as Hfin.
    rewrite <- lb_append_pow_succ' in Hfin.
    replace (3 * k + 1 + 1) with (3 * k + 2) in Hfin by lia.
    eexists. split.
    + exact (Inv_merging d k r Hd Hw).
    + exact (progress_trans _ _ _ _ Hreach Hfin).
  - replace (a + d - 2 + 1) with (2 * k + 2) in Hreach by lia.
    pose proof (drain_X_00_even k (X *> r)) as Hfin.
    rewrite <- lb_append_pow_succ' in Hfin.
    replace (3 * k + 4 + 1) with (3 * k + 5) in Hfin by lia.
    eexists. split.
    + apply (Inv_normal d (3 * k + 5) r Hd); [lia | exact Hw].
    + exact (progress_trans _ _ _ _ Hreach Hfin).
Qed.

Lemma step_merging {d q : nat} {r : side}
    (Hd : d >= 1) (Hw : Wall (3 * d - 1) r) :
    exists c', Inv c' /\
      (z0 <{{B}} (X *> ([S0] *> ((X ^^ (3 * q + 2)) *> r)))) -[ tm0 ]->+ c'.
Proof.
  destruct (even_or_odd (d + q)) as [s [Hs | Hs]].
  - assert (Hs1 : s >= 1) by lia.
    assert (Hsum : (3 * d - 1) + (3 * q + 2) = 2 * (3 * s) + 1) by lia.
    assert (Hn2 : 3 * q + 2 >= 2) by lia.
    pose proof (wall_cons_odd Hw Hn2 Hsum) as Hodd.
    destruct (sideRLs_split Hodd) as [r_mid [Hr1 Hr2]].
    assert (Hentry : (z0 <{{B}} (X *> ([S0] *> ((X ^^ (3 * q + 2)) *> r)))) -[ tm0 ]->+
        ((Dr *> ([S1] *> z0)) {{C}}> ([S0] *> ((X ^^ (3 * q + 2)) *> r)))).
    { eapply progress_evstep_trans; [apply step_B_default_entry | apply step_C_X_one]. }
    pose proof (left_plain_3j s 0) as Hl_ping.
    assert (Hping : ((Dr *> ([S1] *> z0)) {{C}}> ([S0] *> ((X ^^ (3 * q + 2)) *> r)))
        -[ tm0 ]->* (((Dr ^^ (s + 1)) *> ([S1] *> z0)) {{C}}> r_mid)).
    { pose proof (sideLRs_sideRLs_concat_1 Hr1 Hl_ping) as Hp.
      cbn [to_DH_config Str_app] in Hp.
      replace (0 + 1) with 1 in Hp by lia.
      replace (0 + s + 1) with (s + 1) in Hp by lia.
      rewrite lb_append_pow_one in Hp.
      exact Hp. }
    pose proof (sideRLs_elim_single Hr2 ((Dr ^^ (s + 1)) *> ([S1] *> z0))) as Hf_exit.
    cbn [to_DH_config Str_app] in Hf_exit.
    assert (HF : (((Dr ^^ (s + 1)) *> ([S1] *> z0)) <{{F}}
        ([S1; S0; S1] *> ((X ^^ (3 * q + 2)) *> r))) -[ tm0 ]->+
        (((Dr ^^ (3 * q + 3)) *> ([S1; S0; S0] *> ((Dr ^^ s) *> ([S1] *> z0)))) {{C}}> r)).
    { rewrite (lb_append_pow_succ Dr s).
      eapply progress_evstep_trans; [apply step_F_exit_entry |].
      pose proof (shift_C_X (3 * q + 2)
        (Dr *> ([S1; S0; S0] *> ((Dr ^^ s) *> ([S1] *> z0)))) r) as Hsh.
      rewrite <- (lb_append_pow_succ' Dr (3 * q + 2)) in Hsh.
      replace (3 * q + 2 + 1) with (3 * q + 3) in Hsh by lia.
      exact Hsh. }
    pose proof (progress_trans _ _ _ _
      (progress_evstep_trans _ _ _ _ Hentry Hping)
      (progress_trans _ _ _ _ Hf_exit HF)) as Hpre.
    assert (Hm_ne : 3 * d - 1 <> 0) by lia.
    assert (Hr_wall : sideRLs tm0 (lrcons (C, []) (hfb ^^ (3 * d - 1 - 1)) (B, []))
        r ([S0; S0] *> r)).
    { unfold hfb. rewrite lrcons_lpow1 by exact Hm_ne. exact Hw. }
    destruct (le_lt_dec (d - 1) s) as [Hle | Hgt].
    + set (t := d - 1).
      set (b := s - t).
      assert (Hs_eq : s = t + b) by lia.
      pose proof (left100_3t t (3 * q + 2) ((Dr ^^ b) *> ([S1] *> z0))) as H3t.
      pose proof (sideLRs_single (left100_p0 (3 * q + 2 + t) ((Dr ^^ b) *> ([S1] *> z0)))) as H1p.
      assert (Hleft : sideLRs tm0 (hfb ^^ (3 * d - 1 - 1))
          ((Dr ^^ (3 * q + 3)) *> ([S1; S0; S0] *> ((Dr ^^ s) *> ([S1] *> z0))))
          ((Dr ^^ (3 * q + 2 + t)) *> ([S1; S1; S0; S1; S1; S1; S0] *> ((Dr ^^ b) *> ([S1] *> z0))))).
      { pose proof (sideLRs_trans_succ H3t H1p) as Hcomb.
        replace (3 * t + 1) with (3 * d - 1 - 1) in Hcomb by lia.
        rewrite <- lb_append_pow_add, <- Hs_eq in Hcomb.
        replace (3 * q + 2 + 1) with (3 * q + 3) in Hcomb by lia.
        exact Hcomb. }
      pose proof (sideLRs_sideRLs_concat Hleft Hr_wall) as Hglue.
      cbn [to_DH_config Str_app] in Hglue.
      set (k := q + s - b).
      replace (3 * q + 2 + t) with (2 * b + (2 * k + 1)) in Hglue by lia.
      pose proof (drain_B1_full k b r) as Hdrain.
      replace (k + b + 1) with (q + s + 1) in Hdrain by lia.
      eexists. split.
      * exact (Inv_merging d (q + s + 1) r Hd Hw).
      * exact (progress_trans _ _ _ _ (progress_trans _ _ _ _ Hpre Hglue) Hdrain).
    + set (j := (d - 1) - (s + 1)).
      assert (Hds : d - 1 = s + 1 + j) by lia.
      pose proof (left100_3t s (3 * q + 2) ([S1] *> z0)) as H3s.
      pose proof (left100_3_base (3 * q + 2 + s)) as Hbase.
      pose proof (left_plain_3j j (3 * q + 4 + s)) as Hplain.
      pose proof (sideLRs_single (left_p0 (3 * q + 4 + s + j))) as Hp0.
      assert (Hleft : sideLRs tm0 (hfb ^^ (3 * d - 1 - 1))
          ((Dr ^^ (3 * q + 3)) *> ([S1; S0; S0] *> ((Dr ^^ s) *> ([S1] *> z0))))
          ((Dr ^^ (3 * q + 4 + s + j)) *> ([S1; S1; S0; S1; S1; S1] *> z0))).
      { pose proof (sideLRs_trans_add H3s Hbase) as H12.
        replace (3 * q + 2 + s + 3) with (3 * q + 4 + s + 1) in H12 by lia.
        pose proof (sideLRs_trans_add H12 Hplain) as H123.
        pose proof (sideLRs_trans_succ H123 Hp0) as H1234.
        replace (3 * s + 3 + 3 * j + 1) with (3 * d - 1 - 1) in H1234 by lia.
        replace (3 * q + 2 + 1) with (3 * q + 3) in H1234 by lia.
        exact H1234. }
      pose proof (sideLRs_sideRLs_concat Hleft Hr_wall) as Hglue.
      cbn [to_DH_config Str_app] in Hglue.
      replace (3 * q + 4 + s + j) with (2 * (q + s + 1)) in Hglue by lia.
      pose proof (drain_A2 (2 * (q + s + 1)) r) as Hdrain.
      pose proof (drain_X_00_odd (q + s + 1) (X *> r)) as Hfin.
      rewrite <- lb_append_pow_succ' in Hfin.
      replace (3 * (q + s + 1) + 1 + 1) with (3 * (q + s + 1) + 2) in Hfin by lia.
      eexists. split.
      * exact (Inv_merging d (q + s + 1) r Hd Hw).
      * exact (progress_trans _ _ _ _
          (progress_trans _ _ _ _ Hpre Hglue)
          (progress_trans _ _ _ _ Hdrain Hfin)).
  - set (r' := [S0] *> ((X ^^ (3 * q + 2)) *> r)).
    assert (Hsum : (3 * d - 1) + (3 * q + 2) = 2 * (3 * (s + 1) - 1)) by lia.
    assert (Hn2 : 3 * q + 2 >= 2) by lia.
    pose proof (wall_cons_even Hw Hn2 Hsum) as Hw'.
    fold r' in Hw' |- *.
    rewrite <- (lb_append_pow_one X r').
    apply (step_normal (d := s + 1) (a := 1) (r := r')); [lia | lia | exact Hw'].
Qed.

Lemma inv_progress (c : Q * tape) (Hc : Inv c) :
  exists c', Inv c' /\ c -[ tm0 ]->+ c'.
Proof.
  destruct Hc as [d a r Hd Ha Hw | d q r Hd Hw].
  - exact (step_normal Hd Ha Hw).
  - exact (step_merging Hd Hw).
Qed.

(** ** Section 7: Blank-Tape Reachability ([c0 -[ tm0 ]->* Inv]) *)

Lemma init_to_X2 :
  c0 -[ tm0 ]->* (z0 <{{B}} ((X ^^ 2) *> z0)).
Proof.
  change (X ^^ 2) with (X ++ X).
  rewrite Str_app_assoc.
  bb_steps.
Qed.

Lemma init_reaches_inv :
  exists c_init, c0 -[ tm0 ]->* c_init /\ Inv c_init.
Proof.
  assert (H1 : (z0 <{{B}} ((X ^^ 2) *> z0)) -[ tm0 ]->+
      (z0 <{{B}} ((X ^^ 4) *> z0))).
  { pose proof (step_B_X2_00_def z0) as H.
    rewrite lb_append_00_z0 in H. exact H. }
  assert (H2 : (z0 <{{B}} ((X ^^ 4) *> z0)) -[ tm0 ]->+
      (z0 <{{B}} ((X ^^ 7) *> z0))).
  { pose proof (drain_X_00_even 1 z0) as H.
    cbn [Nat.mul Nat.add] in H.
    rewrite lb_append_00_z0 in H. exact H. }
  assert (H3 : (z0 <{{B}} ((X ^^ 7) *> z0)) -[ tm0 ]->+
      (z0 <{{B}} (X *> ([S0] *> ((X ^^ 10) *> z0))))).
  { pose proof (drain_X_00_odd 3 z0) as H.
    cbn [Nat.mul Nat.add] in H.
    rewrite lb_append_00_z0 in H. exact H. }
  assert (Hw5 : Wall 5 ([S0] *> ((X ^^ 10) *> z0))).
  { apply (wall_cons_even wall_zero_z0); lia. }
  assert (Hinv : Inv (z0 <{{B}} ((X ^^ 1) *> ([S0] *> ((X ^^ 10) *> z0))))).
  { apply (Inv_normal 2 1 ([S0] *> ((X ^^ 10) *> z0))); [lia | lia | exact Hw5]. }
  rewrite lb_append_pow_one in Hinv.
  exists (z0 <{{B}} (X *> ([S0] *> ((X ^^ 10) *> z0)))).
  split.
  - eapply evstep_trans; [exact init_to_X2 |].
    apply progress_evstep.
    exact (progress_trans _ _ _ _ H1 (progress_trans _ _ _ _ H2 H3)).
  - exact Hinv.
Qed.

End M585.

Theorem nonhalt : ~ halts tm c0.
Proof.
  rewrite M585.tm0_eq.
  destruct M585.init_reaches_inv as [c_init [Hinit Hinv]].
  eapply multistep_nonhalt; [exact Hinit |].
  eapply progress_nonhalt; [exact M585.inv_progress | exact Hinv].
Qed.
