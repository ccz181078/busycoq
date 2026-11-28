(** Soundness of the composition of a node with a child block. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
Import ListNotations.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Map Walk.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Ints HLines HCore.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

(** A pair of letters as a map on (a,b). *)
Definition st_b (e K a b : Z) : Z := 4 * b - e * (a + b) - K.
Definition st_a (e K K2 a b : Z) : Z := a + b + K2 - st_b e K a b.

Lemma pairU a b ra rb : phi ra = a mod 4 -> phi rb = b mod 4 ->
  b mod 2 = 1 -> 5 <= b -> b + 1 <= a -> 4 * b > a + b + 30 -> (a - b + 5) mod 4 = 2 ->
  Rch a b (st_a 1 18 10 a b) (st_b 1 18 a b) /\
  phi (ra_next (ra_next ra rb 1) (rb_next ra rb 1) 0) = st_a 1 18 10 a b mod 4 /\
  phi (rb_next (ra_next ra rb 1) (rb_next ra rb 1) 0) = st_b 1 18 a b mod 4.
Proof.
  intros Ha Hb H1 H2 H3 H4 H5. destruct (res_U ra rb a b Ha Hb) as [E1 E2].
  destruct (res_D _ _ _ _ E1 E2) as [E3 E4]. unfold st_a, st_b. repeat split.
  - eapply Rch_trans; [apply letterU; assumption|].
    replace (a + b + 10 - (4 * b - 1 * (a + b) - 18)) with (2 * (a - b + 11) + 6) by ring.
    replace (4 * b - 1 * (a + b) - 18) with (2 * b - 4 - (a - b + 11) - 3) by ring.
    apply letterD. lia.
  - rewrite E3. f_equal. ring.
  - rewrite E4. f_equal. ring.
Qed.
Lemma pairV a b ra rb : phi ra = a mod 4 -> phi rb = b mod 4 ->
  b mod 2 = 1 -> 5 <= b -> b + 1 <= a -> 4 * b > a + b + 30 -> (a - b + 5) mod 4 <> 2 ->
  Rch a b (st_a 1 30 14 a b) (st_b 1 30 a b) /\
  phi (ra_next (ra_next ra rb 2) (rb_next ra rb 2) 0) = st_a 1 30 14 a b mod 4 /\
  phi (rb_next (ra_next ra rb 2) (rb_next ra rb 2) 0) = st_b 1 30 a b mod 4.
Proof.
  intros Ha Hb H1 H2 H3 H4 H5. destruct (res_V ra rb a b Ha Hb) as [E1 E2].
  destruct (res_D _ _ _ _ E1 E2) as [E3 E4]. unfold st_a, st_b. repeat split.
  - eapply Rch_trans; [apply letterV; assumption|].
    replace (a + b + 14 - (4 * b - 1 * (a + b) - 30)) with (2 * (a - b + 19) + 6) by ring.
    replace (4 * b - 1 * (a + b) - 30) with (2 * b - 8 - (a - b + 19) - 3) by ring.
    apply letterD. lia.
  - rewrite E3. f_equal. ring.
  - rewrite E4. f_equal. ring.
Qed.
Lemma pairDD a b ra rb : phi ra = a mod 4 -> phi rb = b mod 4 ->
  a + 3 < b -> (2 * a + 6) + 3 < b - a - 3 ->
  Rch a b (st_a 3 12 6 a b) (st_b 3 12 a b) /\
  phi (ra_next (ra_next ra rb 0) (rb_next ra rb 0) 0) = st_a 3 12 6 a b mod 4 /\
  phi (rb_next (ra_next ra rb 0) (rb_next ra rb 0) 0) = st_b 3 12 a b mod 4.
Proof.
  intros Ha Hb H1 H2. destruct (res_D ra rb a b Ha Hb) as [E1 E2].
  destruct (res_D _ _ _ _ E1 E2) as [E3 E4]. unfold st_a, st_b. repeat split.
  - eapply Rch_trans; [apply letterD; assumption|].
    replace (a + b + 6 - (4 * b - 3 * (a + b) - 12)) with (2 * (2 * a + 6) + 6) by ring.
    replace (4 * b - 3 * (a + b) - 12) with (b - a - 3 - (2 * a + 6) - 3) by ring.
    apply letterD. lia.
  - rewrite E3. f_equal. ring.
  - rewrite E4. f_equal. ring.
Qed.

(** A pulled line. *)
Lemma pull_line_spec sg e_ Wq r' yfx x z :
  line_ok x -> (phi e_ = 1 \/ phi e_ = 3) -> phi Wq <= 288230376151711744 -> phi r' <= phi Wq -> phi Wq - phi r' < 4294967296 ->
  phi yfx < 288230376151711744 -> pull_line sg e_ Wq r' yfx x = Some z ->
  line_ok z /\ phi (lt z) = (phi (lt x) + phi e_ * TT) / 4 /\
  exists f, phi (lt x) * (phi Wq - phi r') < TT * (f + 1) /\ TT * f <= phi (lt x) * (phi Wq - phi r') /\ 0 <= f <= 4294967296 /\
    phi (lv z) - VO = phi (lv x) - VO + f + (if sg then 9 else - 8) + phi e_ * phi Wq - phi yfx.
Proof.
  intros [Lt Lv] He Bq Rq Dq By H. unfold pull_line in H. cbv zeta in H.
  set (t' := lt x) in *.
  assert (Dm : phi (Wq - r')%uint63 = phi Wq - phi r') by pv.
  assert (Mt : phi (t' * (Wq - r'))%uint63 = phi t' * (phi Wq - phi r')).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Dm; reflexivity|].
    assert (0 <= phi t') by (pose proof (phi_bd63 t'); lia).
    assert (0 <= phi t' * (phi Wq - phi r')) by (apply Z.mul_nonneg_nonneg; lia).
    assert (phi t' * (phi Wq - phi r') <= TT * 4294967296) by (apply Z.mul_le_mono_nonneg; lia). lia. }
  set (m := phi t' * (phi Wq - phi r')) in *.
  assert (M0 : 0 <= m <= TT * 4294967296).
  { pose proof (phi_bd63 t'). unfold m. split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]. }
  set (f := ((t' * (Wq - r')) >> 30)%uint63) in *.
  assert (Ef : phi f = m / TT) by (unfold f; rewrite phi_lsr30, Mt; reflexivity).
  assert (Bf : 0 <= phi f <= 4294967296) by (rewrite Ef; Z.div_mod_to_equations; lia).
  assert (Eew : 0 <= phi e_ * phi Wq <= 864691128455135232).
  { destruct He as [He|He]; rewrite He; pose proof (phi_bd63 Wq); lia. }
  assert (Evv : phi (if sg then (lv x + f + 9 + e_ * Wq)%uint63 else (lv x + f + e_ * Wq)%uint63) =
     phi (lv x) + phi f + (if sg then 9 else 0) + phi e_ * phi Wq).
  { destruct sg; cbv iota; [pv|]. replace (phi (lv x) + phi f + 0 + phi e_ * phi Wq) with (phi (lv x) + phi f + phi e_ * phi Wq) by ring. pv. }
  assert (Esb : phi (if sg then yfx else (yfx + 8)%uint63) = phi yfx + (if sg then 0 else 8)).
  { destruct sg; cbv iota; [lia|pv]. }
  set (vv := if sg then (lv x + f + 9 + e_ * Wq)%uint63 else (lv x + f + e_ * Wq)%uint63) in *.
  set (sb := if sg then yfx else (yfx + 8)%uint63) in *.
  destruct ((sb <=? vv)%uint63 && ((vv - sb) <? 4611686018427387904)%uint63) eqn:C; [|discriminate].
  apply andb_prop in C. destruct C as [C1 C2]. apply leb_true in C1. apply ltb_true in C2.
  change (phi 4611686018427387904%uint63) with 4611686018427387904 in C2.
  injection H as <-. cbn [lt lv].
  assert (Ez : phi (vv - sb)%uint63 = phi vv - phi sb) by pv.
  assert (Et : phi (t' + e_ * TONE)%uint63 = phi t' + phi e_ * TT).
  { pose proof (phi_bd63 t'). apply phi_of_cg; [cgs; unfold cg; reflexivity|destruct He as [He|He]; rewrite He; lia]. }
  split; [|split; [|exists (phi f); repeat split]].
  - unfold line_ok; cbn [lt lv]. rewrite phi_lsr2, Et. split; [|rewrite Ez in *; lia].
    pose proof (phi_bd63 t'). destruct He as [He|He]; rewrite He; Z.div_mod_to_equations; lia.
  - rewrite phi_lsr2, Et. reflexivity.
  - rewrite Ef. pose proof (fl_hi m). lia.
  - rewrite Ef. apply (fl_lo m).
  - lia.
  - lia.
  - rewrite Ez, Evv, Esb. destruct sg; ring.
Qed.

Lemma div4 x : 4 * (x / 4) <= x < 4 * (x / 4) + 4.
Proof. Z.div_mod_to_equations; lia. Qed.
Lemma div2 x : 2 * (x / 2) <= x < 2 * (x / 2) + 2.
Proof. Z.div_mod_to_equations; lia. Qed.

Lemma maxv_ub l : forall m, Forall line_ok l -> phi m <= 2305843009213693952 -> phi (maxv l m) <= 2305843009213693952.
Proof.
  induction l as [|x t IH]; intros m H Hm; [exact Hm|].
  inversion H as [|? ? [_ Lv] H2]; subst. cbn [maxv]. apply IH; [exact H2|]. rewrite phi_max.
  assert (A : phi (absv (lv x)) <= 2305843009213693952).
  { unfold absv. destruct (VOFF <=? lv x)%uint63 eqn:C.
    - apply leb_true in C. change (phi VOFF) with VO in C. assert (F : phi (lv x - VOFF)%uint63 = phi (lv x) - VO) by pv. rewrite F. lia.
    - apply leb_false in C. change (phi VOFF) with VO in C. assert (F : phi (VOFF - lv x)%uint63 = VO - phi (lv x)) by pv. rewrite F. pose proof (phi_bd63 (lv x)). lia. }
  lia.
Qed.

(** A pulled line implies the child's line at the child's state. *)
Lemma lo_pulled sg_e Wq r' yfx x z r y e K K2 b S g W2 :
  line_ok x -> phi sg_e = e -> (e = 1 \/ e = 3) -> phi Wq <= 288230376151711744 -> phi r' <= phi Wq -> phi Wq - phi r' < 4294967296 ->
  phi yfx = y * PP -> 0 <= y -> y * PP < 288230376151711744 -> 0 <= K -> 0 <= K2 -> 4 * phi Wq <= r <= 4 * phi Wq + 3 -> 1 <= g ->
  PP * S <= W2 * g -> W2 <= r + 2147483648 ->
  (Z.abs (phi (lv x) - VO) + Z.abs (phi r')) * 3 + PP * (4 * y + K + K2) <= 13 * g ->
  pull_line true sg_e Wq r' yfx x = Some z ->
  lo_l r z b S g -> lo_l (phi r') x (4 * (b + g * y) - e * (S + y) - K) (S + y + K2) (4 * g - e).
Proof.
  intros Lx He He' BW Rq Dq Hy Y0 Yb HK HK2 Hq Hg HS HW Hb P Hl.
  destruct (pull_line_spec true sg_e Wq r' yfx x z Lx (ltac:(rewrite He; lia)) BW Rq Dq ltac:(lia) P) as (Lz & Et & f & F1 & F2 & F3 & Ev).
  destruct Lx as [Lt Lv]. destruct Lz as [Lzt Lzv].
  rewrite He in Et, Ev. rewrite Hy in Ev.
  pose proof (div4 (phi (lt x) + e * TT)) as D. rewrite <- Et in D. pose proof (phi_bd63 (lt x)). pose proof (phi_bd63 (lt z)).
  apply (pull_lo (phi (lt x)) (phi (lv x) - VO) (phi r') (phi (lt z)) (phi (lv z) - VO) r y e K K2 (phi Wq) f (phi (lt x) + e * TT - 4 * phi (lt z)) b S g W2); try lia.
  exact Hl.
Qed.
Lemma hi_pulled sg_e Wq r' yfx x z r y e K K2 b S g W1 :
  line_ok x -> phi sg_e = e -> (e = 1 \/ e = 3) -> phi Wq <= 288230376151711744 -> phi r' <= phi Wq -> phi Wq - phi r' < 4294967296 ->
  phi yfx = y * PP -> 0 <= y -> y * PP < 288230376151711744 -> 0 <= K -> 0 <= K2 -> 4 * phi Wq <= r <= 4 * phi Wq + 3 -> 1 <= g ->
  W1 * g <= PP * S -> r - 2147483648 <= W1 ->
  (Z.abs (phi (lv x) - VO) + Z.abs (phi r')) * 3 <= 13 * g ->
  pull_line false sg_e Wq r' yfx x = Some z ->
  hi_l r z b S g -> hi_l (phi r') x (4 * (b + g * y) - e * (S + y) - K) (S + y + K2) (4 * g - e).
Proof.
  intros Lx He He' BW Rq Dq Hy Y0 Yb HK HK2 Hq Hg HS HW Hb P Hl.
  destruct (pull_line_spec false sg_e Wq r' yfx x z Lx (ltac:(rewrite He; lia)) BW Rq Dq ltac:(lia) P) as (Lz & Et & f & F1 & F2 & F3 & Ev).
  destruct Lx as [Lt Lv]. destruct Lz as [Lzt Lzv].
  rewrite He in Et, Ev. rewrite Hy in Ev.
  pose proof (div4 (phi (lt x) + e * TT)) as D. rewrite <- Et in D. pose proof (phi_bd63 (lt x)). pose proof (phi_bd63 (lt z)).
  apply (pull_hi (phi (lt x)) (phi (lv x) - VO) (phi r') (phi (lt z)) (phi (lv z) - VO) r y e K K2 (phi Wq) f (phi (lt x) + e * TT - 4 * phi (lt z)) b S g W1); try lia.
  exact Hl.
Qed.

Lemma kind_cases ra rb : phi (kind_of ra rb) = 1 \/ phi (kind_of ra rb) = 2.
Proof. unfold kind_of. destruct (((ra + 8 + 5 - rb) land 3) =? 2)%uint63; [left|right]; reflexivity. Qed.
Lemma In_Forall' {A} (P : A -> Prop) l x : Forall P l -> In x l -> P x.
Proof. intros H. rewrite Forall_forall in H. apply H. Qed.
Lemma In_Forall {A} (P : A -> Prop) l x : Forall P l -> In x l -> P x.
Proof. intros H. rewrite Forall_forall in H. apply H. Qed.

(** The child's lines at the child's state, from the pulled lines. *)
Lemma absorb_sound b ch dl e : ent_ok b -> ent_ok ch -> absorb b ch dl = Some e ->
  ent_ok e /\ ec e = ec b /\ era e = era b /\ erb e = erb b /\ ez e = ez b /\ ed2 e = ed2 b /\ eW e = eW b.
Proof.
  intros [Bd Sem] [BdC SemC] H. unfold absorb in H. cbv zeta in H.
  destruct Bd as (BL & BU & BW & BW1 & BW2 & BY & BY4 & BL2 & Bc & BD & BG & BWa & BWb).
  destruct BdC as (CL & CU & CW & CW1 & CW2 & CY & CY4 & CL2 & Cc & CD & CG & CWa & CWb).
  assert (BY4' : exists k, phi (eY b) = 4 * k) by (exists (phi (eY b) / 4); pose proof (div4 (phi (eY b))); clear -H0 BY4; Z.div_mod_to_equations; lia).
  assert (CY4' : exists k, phi (eY ch) = 4 * k) by (exists (phi (eY ch) / 4); pose proof (div4 (phi (eY ch))); clear -H0 CY4; Z.div_mod_to_equations; lia).
  destruct BY4' as [ky Ky]. destruct CY4' as [kc Kc]. clear BY4 CY4.
  set (kind := if dl then 0%uint63 else kind_of (era b) (erb b)) in *.
  set (e_ := if dl then 3%uint63 else 1%uint63) in *.
  set (K2 := if dl then 6%uint63 else if (kind =? 1)%uint63 then 10%uint63 else 14%uint63) in *.
  set (ra1 := ra_next (era b) (erb b) kind) in *.
  set (rb1 := rb_next (era b) (erb b) kind) in *.
  set (Wq := (eW b >> 2)%uint63) in *.
  set (yfx := (eY b << 28)%uint63) in *.
  set (Y' := (eY b + eY ch)%uint63) in *.
  destruct ((ec ch =? ec b + K2)%uint63 && (era ch =? ra_next ra1 rb1 0)%uint63 && (erb ch =? rb_next ra1 rb1 0)%uint63
     && (ez ch =? ez b)%uint63 && (ed2 ch =? ed2 b)%uint63 && (dl || ((erb b land 1) =? 1)%uint63)
     && (eW ch =? eW1 ch)%uint63 && (eW ch <=? Wq)%uint63 && ((Wq - eW ch) <? 4294967296)%uint63 && (Y' <? 1073741824)%uint63 && (16 <=? eW2 ch)%uint63) eqn:G; [|discriminate].
  repeat (apply andb_prop in G; destruct G as [G ?]).
  rename G into G1. rename H0 into G11. rename H1 into G10. rename H2 into G9. rename H3 into G8. rename H4 into G7.
  rename H5 into G6. rename H6 into G5. rename H7 into G4. rename H8 into G3. rename H9 into G2.
  apply Uint63.eqb_spec in G1, G2, G3, G4, G5, G7.
  apply leb_true in G8. apply ltb_true in G9. apply ltb_true in G10. apply leb_true in G11.
  change (phi 4294967296%uint63) with 4294967296 in G9. change (phi 1073741824%uint63) with TT in G10. change (phi 16%uint63) with 16 in G11.
  assert (Ee : (dl = true /\ phi e_ = 3) \/ (dl = false /\ phi e_ = 1)) by (unfold e_; destruct dl; [left|right]; split; reflexivity).
  assert (Ee' : phi e_ = 1 \/ phi e_ = 3) by (destruct Ee as [[_ X]|[_ X]]; [right|left]; exact X).
  assert (BW0 : 0 <= phi (eW b)) by (pose proof (phi_bd63 (eW b)); clear H; lia).
  assert (BWq : 0 <= phi Wq <= 288230376151711744 /\ 4 * phi Wq <= phi (eW b) <= 4 * phi Wq + 3).
  { assert (EWq : phi Wq = phi (eW b) / 4) by (unfold Wq; apply phi_lsr2). pose proof (div4 (phi (eW b))) as D. rewrite <- EWq in D. clear EWq. pose proof (phi_bd63 Wq). lia. }
  assert (BY0 : 0 <= phi (eY b)) by (pose proof (phi_bd63 (eY b)); lia).
  assert (CY0 : 0 <= phi (eY ch)) by (pose proof (phi_bd63 (eY ch)); lia).
  assert (CL0 : 0 <= phi (elast ch)) by (pose proof (phi_bd63 (elast ch)); lia).
  assert (Eyf : phi yfx = phi (eY b) * PP) by (unfold yfx; apply phi_lsl28; lia).
  assert (EY' : phi Y' = phi (eY b) + phi (eY ch)) by (unfold Y'; pv).
  rewrite EY' in G10.
  assert (ElY : phi (eY b + elast ch)%uint63 = phi (eY b) + phi (elast ch)) by pv.
  assert (El28 : phi ((eY b + elast ch) << 28)%uint63 = (phi (eY b) + phi (elast ch)) * PP) by (rewrite <- ElY; apply phi_lsl28; lia).
  (** the lines of the pair *)
  set (l1 := ((eW b + 3) >> 2)%uint63) in *. set (l3 := ((3 * eW b + 3) >> 2)%uint63) in *. set (l2 := (eW b >> 1)%uint63) in *.
  assert (Bl1 : 0 <= phi l1 <= 288230376151711745 /\ phi (eW b) <= 4 * phi l1).
  { assert (Lim1 : phi l1 = (phi (eW b) + 3) / 4) by (unfold l1; rewrite phi_lsr2; f_equal; pv).
    pose proof (div4 (phi (eW b) + 3)) as D. rewrite <- Lim1 in D. clear Lim1. pose proof (phi_bd63 l1). lia. }
  assert (Bl3 : 0 <= phi l3 <= 864691128455135233 /\ 3 * phi (eW b) <= 4 * phi l3).
  { assert (Lim3 : phi l3 = (3 * phi (eW b) + 3) / 4) by (unfold l3; rewrite phi_lsr2; f_equal; pv).
    pose proof (div4 (3 * phi (eW b) + 3)) as D. rewrite <- Lim3 in D. clear Lim3. pose proof (phi_bd63 l3). lia. }
  assert (Bl2 : 0 <= phi l2 <= 576460752303423488 /\ 4 * phi l2 <= 2 * phi (eW b)).
  { assert (Lim2 : phi l2 = phi (eW b) / 2) by (unfold l2; rewrite lsr_spec; reflexivity).
    pose proof (div2 (phi (eW b))) as D. rewrite <- Lim2 in D. clear Lim2. pose proof (phi_bd63 l2). lia. }
  assert (El1v : phi (l1 + VOFF - yfx + 8)%uint63 = phi l1 + VO - phi (eY b) * PP + 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Eyf; reflexivity|lia]. }
  assert (El3v : phi (l3 + VOFF - yfx + 8)%uint63 = phi l3 + VO - phi (eY b) * PP + 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Eyf; reflexivity|lia]. }
  assert (El2v : phi (l2 + VOFF - ((eY b + elast ch) << 28) - 8)%uint63 = phi l2 + VO - (phi (eY b) + phi (elast ch)) * PP - 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite El28; reflexivity|lia]. }
  destruct (pulls true e_ Wq (eW ch) yfx (elo ch) _) as [lo|] eqn:PL; [|discriminate].
  destruct (pulls false e_ Wq (eW ch) yfx (ehi ch) _) as [hi|] eqn:PU; [|discriminate].
  destruct (pulls_spec _ _ _ _ _ _ _ _ PL) as (PL1 & PL2 & PL3).
  destruct (pulls_spec _ _ _ _ _ _ _ _ PU) as (PU1 & PU2 & PU3).
  destruct (maxv_spec (ehi ch) 0%uint63) as [Mv1 Mv2].
  destruct (maxv_spec (elo ch) (maxv (ehi ch) 0%uint63)) as [Mv3 Mv4].
  set (vm := maxv (elo ch) (maxv (ehi ch) 0%uint63)) in *.
  assert (Bvm : 0 <= phi vm) by (pose proof (phi_bd63 vm); lia).
  assert (Ec5 : (ec ch = (ec b + K2)%uint63)) by exact G1.
  set (gneed := (ONE * (eY b + 64) + vm + eW ch + eW2 ch)%uint63) in *.
  set (Gm := max_ (max_ (eGm b) gneed) ((eGm ch >> 2) + 2)%uint63) in *.
  set (dlast1 := (eY b + edlast ch)%uint63) in *.
  destruct ((gneed <? 2305843009213693952)%uint63 && (Gm <? 2305843009213693952)%uint63 && (dlast1 <? 2147483648)%uint63
         && (negb (edet ch) || negb (edet b) || (edres b =? edres ch)%uint63)) eqn:G12; [|discriminate].
  repeat (apply andb_prop in G12; destruct G12 as [G12 ?]).
  rename G12 into G13. rename H0 into G16. rename H1 into G15. rename H2 into G14.
  apply ltb_true in G13, G14, G15.
  change (phi 2305843009213693952%uint63) with 2305843009213693952 in G13, G14. change (phi 2147483648%uint63) with 2147483648 in G15.
  assert (Egn : phi gneed = PP * (phi (eY b) + 64) + phi vm + phi (eW ch) + phi (eW2 ch)).
  { assert (Mub : phi vm <= 2305843009213693952).
    { unfold vm. apply maxv_ub; [exact CL|apply maxv_ub; [exact CU|vm_compute; intro X0; discriminate X0]]. }
    unfold gneed. apply phi_of_cg; [cgs; unfold cg; reflexivity|]. pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia. }
  assert (EdlL : phi dlast1 = phi (eY b) + phi (edlast ch)) by (unfold dlast1; pv).
  assert (BG0 : 0 <= phi (eGm ch)) by (pose proof (phi_bd63 (eGm ch)); lia).
  assert (GcD : 4 * phi (eGm ch >> 2)%uint63 <= phi (eGm ch) < 4 * phi (eGm ch >> 2)%uint63 + 4 /\ 0 <= phi (eGm ch >> 2)%uint63 < 2305843009213693952).
  { assert (Ee4 : phi (eGm ch >> 2)%uint63 = phi (eGm ch) / 4) by apply phi_lsr2. pose proof (div4 (phi (eGm ch))) as D. rewrite <- Ee4 in D. clear Ee4. pose proof (phi_bd63 (eGm ch >> 2)%uint63). lia. }
  assert (EGm : phi Gm = Z.max (Z.max (phi (eGm b)) (phi gneed)) (phi (eGm ch >> 2)%uint63 + 2)).
  { unfold Gm. rewrite !phi_max. f_equal. pv. }
  assert (EW14 : phi (4 * eW1 ch)%uint63 = 4 * phi (eW1 ch)) by pv.
  assert (EW24 : phi (4 * eW2 ch - 64)%uint63 = 4 * phi (eW2 ch) - 64) by pv.
  assert (G9' : phi Wq - phi (eW ch) < 4294967296) by (assert (Dm : phi (Wq - eW ch)%uint63 = phi Wq - phi (eW ch)) by pv; lia).
  assert (EWc : phi (eW ch) = phi (eW1 ch)) by (rewrite G7; reflexivity).
  (** the pair of letters *)
  assert (Pr : exists eZ KZ K2Z, phi e_ = eZ /\ phi K2 = K2Z /\ 0 <= KZ <= 30 /\ 0 <= K2Z <= 14 /\ (eZ = 1 \/ eZ = 3) /\
     forall at_ bt, phi (era b) = at_ mod 4 -> phi (erb b) = bt mod 4 ->
       (if dl then at_ + 3 < bt /\ (2 * at_ + 6) + 3 < bt - at_ - 3
        else bt mod 2 = 1 /\ 5 <= bt /\ bt + 1 <= at_ /\ 4 * bt > at_ + bt + 30) ->
       Rch at_ bt (st_a eZ KZ K2Z at_ bt) (st_b eZ KZ at_ bt) /\
       phi (ra_next ra1 rb1 0) = st_a eZ KZ K2Z at_ bt mod 4 /\ phi (rb_next ra1 rb1 0) = st_b eZ KZ at_ bt mod 4).
  { destruct dl.
    - exists 3, 12, 6. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      intros at_ bt Ra Rb [Gg1 Gg2]. apply pairDD; assumption.
    - destruct (Z.eq_dec (phi kind) 1) as [Kk|Kk].
      + assert (Kk' : kind = 1%uint63) by (apply to_Z_inj; exact Kk).
        exists 1, 18, 10. split; [reflexivity|]. split; [unfold K2; rewrite Kk'; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
        intros at_ bt Ra Rb (Gg1 & Gg2 & Gg3 & Gg4).
        destruct (res_kind (era b) (erb b) at_ bt Ra Rb) as [[_ K5]|[K4 _]]; [|exfalso; change (kind_of (era b) (erb b)) with kind in K4; lia].
        unfold ra1, rb1. rewrite Kk'. apply pairU; assumption.
      + assert (Kk2 : phi kind = 2) by (pose proof (kind_cases (era b) (erb b)) as Kc'; change (kind_of (era b) (erb b)) with kind in Kc'; lia).
        assert (Kk' : kind = 2%uint63) by (apply to_Z_inj; exact Kk2).
        exists 1, 30, 14. split; [reflexivity|]. split; [unfold K2; rewrite Kk'; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
        intros at_ bt Ra Rb (Gg1 & Gg2 & Gg3 & Gg4).
        destruct (res_kind (era b) (erb b) at_ bt Ra Rb) as [[K4 _]|[_ K5]]; [exfalso; change (kind_of (era b) (erb b)) with kind in K4; lia|].
        unfold ra1, rb1. rewrite Kk'. apply pairV; assumption. }
  destruct Pr as (eZ & KZ & K2Z & Ee1 & Ek2 & Bk & Bk2 & Eee & Pair).
  assert (Ee2' : eZ = 1 \/ eZ = 3) by exact Eee.
  assert (Eec : phi (ec b + K2)%uint63 = phi (ec b) + K2Z) by (rewrite <- Ek2; pv).
  (** lines are fine *)
  assert (LoOK : forall z, In z lo -> line_ok z).
  { intros z Hz. destruct (PL3 z Hz) as [Ha|(x & Hx & Hp)].
    - apply in_app_or in Ha. destruct Ha as [Ha|Ha]; [|eapply In_Forall; [exact BL|exact Ha]].
      destruct dl.
      + destruct Ha as [<-|[]]. unfold line_ok; cbn [lt lv]. rewrite El3v. split; [vm_compute; intro X0; discriminate X0|lia].
      + destruct Ha as [<-|[<-|[]]]; unfold line_ok; cbn [lt lv].
        * rewrite El1v. split; [vm_compute; intro X0; discriminate X0|lia].
        * split; [vm_compute; intro X0; discriminate X0|vm_compute; reflexivity].
    - exact (proj1 (pull_line_spec true e_ Wq (eW ch) yfx x z (In_Forall _ _ _ CL Hx) Ee' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hp)). }
  assert (HiOK : forall z, In z hi -> line_ok z).
  { intros z Hz. destruct (PU3 z Hz) as [Ha|(x & Hx & Hp)].
    - apply in_app_or in Ha. destruct Ha as [Ha|Ha]; [|eapply In_Forall; [exact BU|exact Ha]].
      destruct dl.
      + destruct Ha.
      + destruct Ha as [<-|[]]. unfold line_ok; cbn [lt lv]. rewrite El2v. split; [vm_compute; intro X0; discriminate X0|lia].
    - exact (proj1 (pull_line_spec false e_ Wq (eW ch) yfx x z (In_Forall _ _ _ CU Hx) Ee' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hp)). }
  injection H as <-. split; [|repeat split].
  split.
  - (* bounds *)
    unfold ent_bd; cbn [elo ehi eW eW1 eW2 eY elast edet edlast edres eGm ec].
    rewrite phi_max, phi_min, EW14, EW24, EY', ElY. repeat split.
    + apply Forall_forall. exact LoOK.
    + apply Forall_forall. exact HiOK.
    + exact BW.
    + lia.
    + lia.
    + lia.
    + rewrite Ky, Kc. replace (4 * ky + 4 * kc) with (0 + (ky + kc) * 4) by ring. rewrite Z.mod_add by lia. reflexivity.
    + lia.
    + lia.
    + destruct (edet ch); [rewrite phi_max|]; lia.
    + lia.
    + lia.
    + lia.
  - (* meaning *)
    intros B a b0 g HS Ha Hb Hg HG Hreg HPre HDet. cbn [ec era erb ez ed2 eW eW1 eW2 elo ehi eY elast edet edlast edres eGm] in *.
    rewrite ElY in HPre. rewrite EY'. rewrite EGm in HG.
    unfold reg in Hreg. cbn [eW eW1 eW2 elo ehi] in Hreg.
    destruct Hreg as (RL & RU & R1 & R2). rewrite Forall_forall in RL, RU.
    rewrite phi_max, EW14 in R1. rewrite phi_min, EW24 in R2.
    assert (R1a : phi (eW1 b) * g <= PP * (a + b0)).
    { eapply Z.le_trans; [|exact R1]. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (R1b : (4 * phi (eW1 ch)) * g <= PP * (a + b0)).
    { eapply Z.le_trans; [|exact R1]. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (R2a : PP * (a + b0) <= phi (eW2 b) * g).
    { eapply Z.le_trans; [exact R2|]. apply Z.mul_le_mono_nonneg_r; lia. }
    assert (R2b : PP * (a + b0) <= (4 * phi (eW2 ch) - 64) * g).
    { eapply Z.le_trans; [exact R2|]. apply Z.mul_le_mono_nonneg_r; lia. }
    clear R1 R2.
    set (S := a + b0) in *. set (y := phi (eY b)) in *.
    assert (Gg : phi (eGm b) <= g /\ phi gneed <= g /\ phi (eGm ch >> 2)%uint63 + 2 <= g) by lia.
    clear HG. destruct Gg as (Gg1 & Gg2 & Gg3). rewrite Egn in Gg2.
    assert (HR : Rch (phi (ez b)) B (phi (ez b)) (B + y)).
    { apply (Sem B a b0 g); try assumption.
      - unfold reg. repeat split; try assumption.
        + apply Forall_forall. intros x Hx. apply RL. apply PL1. apply in_or_app. right. exact Hx.
        + apply Forall_forall. intros x Hx. apply RU. apply PU1. apply in_or_app. right. exact Hx.
      - eapply PreH_mono; [|exact HPre]. lia.
      - intros E1. rewrite E1 in HDet. cbn [orb] in HDet. specialize (HDet eq_refl).
        destruct (edet ch) eqn:Ed.
        + rewrite E1 in G16. cbn [negb orb] in G16. apply Uint63.eqb_spec in G16. rewrite G16.
          intros t Ht Hm. apply HDet; [rewrite phi_max; lia|exact Hm].
        + intros t Ht Hm. apply HDet; [lia|exact Hm]. }
    (** facts from the lines of the pair *)
    assert (Sg0 : 0 <= S).
    { pose proof (phi_bd63 (eW1 b)). assert (0 <= phi (eW1 b) * g) by (apply Z.mul_nonneg_nonneg; lia). lia. }
    assert (GgP : PP * (y + 64) <= g).
    { pose proof (phi_bd63 vm). pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia. }
    assert (LL : if dl then 32 * g <= PP * (4 * (b0 + g * y) - 3 * S)
                 else 32 * g <= PP * (4 * (b0 + g * y) - 1 * S) /\ 16 * g <= PP * b0).
    { destruct dl.
      - assert (Rl : lo_l (phi (eW b)) (mkLine (3 * Q1)%uint63 (l3 + VOFF - yfx + 8)%uint63) b0 S g).
        { apply RL. apply PL1. apply in_or_app. left. left. reflexivity. }
        unfold lo_l in Rl. cbn [lt lv] in Rl. rewrite El3v in Rl. change (phi (3 * Q1)%uint63) with (3 * 268435456) in Rl.
        apply (line_lo1 3 (phi (eW b)) y b0 S g (phi l3)); [|lia|lia].
        replace (phi l3 - y * PP + 8) with (phi l3 + VO - y * PP + 8 - VO) by ring. exact Rl.
      - assert (Rl : lo_l (phi (eW b)) (mkLine Q1 (l1 + VOFF - yfx + 8)%uint63) b0 S g).
        { apply RL. apply PL1. apply in_or_app. left. left. reflexivity. }
        assert (Rl0 : lo_l (phi (eW b)) (mkLine 0%uint63 (VOFF + 16)%uint63) b0 S g).
        { apply RL. apply PL1. apply in_or_app. left. right. left. reflexivity. }
        unfold lo_l in Rl, Rl0. cbn [lt lv] in Rl, Rl0. rewrite El1v in Rl. change (phi Q1) with (1 * 268435456) in Rl.
        change (phi 0%uint63) with 0 in Rl0. change (phi (VOFF + 16)%uint63 - VO) with 16 in Rl0. unfold lo_z in Rl0.
        split; [|lia].
        apply (line_lo1 1 (phi (eW b)) y b0 S g (phi l1)); [|lia|lia].
        replace (phi l1 - y * PP + 8) with (phi l1 + VO - y * PP + 8 - VO) by ring. exact Rl. }
    assert (HH : dl = false -> 32 * g <= PP * (2 * S - 4 * (b0 + g * (y + phi (elast ch))))).
    { intros Df. rewrite Df in *.
      assert (Rl : hi_l (phi (eW b)) (mkLine (2 * Q1)%uint63 (l2 + VOFF - ((eY b + elast ch) << 28) - 8)%uint63) b0 S g).
      { apply RU. apply PU1. apply in_or_app. left. left. reflexivity. }
      unfold hi_l in Rl. cbn [lt lv] in Rl. rewrite El2v in Rl. change (phi (2 * Q1)%uint63) with (2 * 268435456) in Rl.
      apply (line_hi1 2 (phi (eW b)) (y + phi (elast ch)) b0 S g (phi l2)); [|lia|lia].
      replace (phi l2 - (y + phi (elast ch)) * PP - 8) with (phi l2 + VO - (y + phi (elast ch)) * PP - 8 - VO) by ring. exact Rl. }
    (** the state at any visited offset *)
    assert (Gd : forall t, y <= t <= y + phi (elast ch) ->
       if dl then (a - (g - 1) * t) + 3 < b0 + g * t /\ (2 * (a - (g - 1) * t) + 6) + 3 < (b0 + g * t) - (a - (g - 1) * t) - 3
       else 5 <= b0 + g * t /\ b0 + g * t + 1 <= a - (g - 1) * t /\ 4 * (b0 + g * t) > (a - (g - 1) * t) + (b0 + g * t) + 30).
    { intros t Ht. destruct dl.
      - apply (guards_pairDD a b0 g S y t eq_refl Hg GgP ltac:(lia) ltac:(lia) ltac:(exact LL) Sg0).
      - destruct LL as [L1 L2]. apply (guards_pairUV a b0 g S y t (y + phi (elast ch)) eq_refl Hg GgP L2 ltac:(lia) ltac:(lia) (HH eq_refl) ltac:(lia)). }
    assert (Ka : forall t, t mod 4 = 0 -> phi (era b) = (a - (g - 1) * t) mod 4) by (intros t Ht; rewrite res_at by exact Ht; symmetry; exact Ha).
    assert (Kb : forall t, t mod 4 = 0 -> phi (erb b) = (b0 + g * t) mod 4) by (intros t Ht; rewrite resb_at by exact Ht; symmetry; exact Hb).
    assert (Odd : dl = false -> forall t, t mod 4 = 0 -> (b0 + g * t) mod 2 = 1).
    { intros Df t Ht. rewrite Df in G6. cbn [orb] in G6. apply eqb_true in G6. rewrite phi_land1 in G6. change (phi 1%uint63) with 1 in G6.
      pose proof (Kb t Ht) as Kbt. rewrite Kbt in G6. revert G6. clear -Ht. intros G6. Z.div_mod_to_equations. lia. }
    assert (W : forall t, y <= t <= y + phi (elast ch) -> t mod 4 = 0 ->
        Rch (a - (g - 1) * t) (b0 + g * t) (st_a eZ KZ K2Z (a - (g - 1) * t) (b0 + g * t)) (st_b eZ KZ (a - (g - 1) * t) (b0 + g * t)) /\
        phi (ra_next ra1 rb1 0) = st_a eZ KZ K2Z (a - (g - 1) * t) (b0 + g * t) mod 4 /\ phi (rb_next ra1 rb1 0) = st_b eZ KZ (a - (g - 1) * t) (b0 + g * t) mod 4).
    { intros t Ht Hm. apply Pair; [apply Ka; exact Hm|apply Kb; exact Hm|].
      pose proof (Gd t Ht) as Gt. destruct dl; [exact Gt|]. destruct Gt as (G1a & G1b & G1c). repeat split; try assumption. apply Odd; [reflexivity|exact Hm]. }
    clear Ha Hb.
    set (at0 := a - (g - 1) * y). set (bt0 := b0 + g * y).
    set (a2 := st_a eZ KZ K2Z at0 bt0). set (b2 := st_b eZ KZ at0 bt0). set (g2 := 4 * g - eZ).
    assert (Sum0 : at0 + bt0 = S + y) by (unfold at0, bt0, S; ring).
    assert (Eb2 : b2 = 4 * (b0 + g * y) - eZ * (S + y) - KZ) by (unfold b2, st_b; rewrite Sum0; unfold bt0; ring).
    assert (Es2 : a2 + b2 = S + y + K2Z) by (unfold a2, st_a; fold b2; lia).
    assert (Y4 : y mod 4 = 0).
    { rewrite Ky. replace (4 * ky) with (0 + ky * 4) by ring. rewrite Z.mod_add by lia. reflexivity. }
    destruct (W y ltac:(lia) Y4) as (W1_ & W2_ & W3_). fold at0 bt0 a2 b2 in W1_, W2_, W3_.
    assert (HC : Rch (phi (ez ch)) (B + y) (phi (ez ch)) (B + y + phi (eY ch))).
    { apply (SemC (B + y) a2 b2 g2).
      - rewrite Es2. rewrite G1. rewrite Eec. unfold S in *. lia.
      - rewrite G2. symmetry. exact W2_.
      - rewrite G3. symmetry. exact W3_.
      - unfold g2. lia.
      - unfold g2. lia.
      - (* region *)
        rewrite Es2, Eb2. unfold reg. repeat split.
        + apply Forall_forall. intros x Hx.
          destruct (PL2 x Hx) as (z & Hp & Hz).
          eapply (lo_pulled e_ Wq (eW ch) yfx x z (phi (eW b)) y eZ KZ K2Z b0 S g (phi (eW2 b))); try lia.
          * eapply In_Forall; [exact CL|exact Hx].
          * pose proof (Mv4 x Hx). pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia.
          * exact Hp.
          * apply RL. exact Hz.
        + apply Forall_forall. intros x Hx.
          destruct (PU2 x Hx) as (z & Hp & Hz).
          eapply (hi_pulled e_ Wq (eW ch) yfx x z (phi (eW b)) y eZ KZ K2Z b0 S g (phi (eW1 b))); try lia.
          * eapply In_Forall; [exact CU|exact Hx].
          * pose proof (Mv2 x Hx). pose proof (phi_bd63 (eW ch)). pose proof (phi_bd63 (eW2 ch)). lia.
          * exact Hp.
          * apply RU. exact Hz.
        + unfold g2. apply (range_lo _ (4 * phi (eW1 ch))); try lia. pose proof (phi_bd63 (eW1 ch)). lia.
        + unfold g2. pose proof (phi_bd63 (eW2 ch)). pose proof (phi_bd63 vm). pose proof (phi_bd63 (eW ch)). apply (range_hi _ (4 * phi (eW2 ch) - 64)); lia.
      - (* the prefix *)
        rewrite G4. intros y' Hy' Hm.
        assert (Ht4 : (y + y') mod 4 = 0).
        { rewrite Z.add_mod by lia. rewrite Y4, Hm. reflexivity. }
        pose proof (HPre (y + y') ltac:(lia) Ht4) as P1.
        destruct (W (y + y') ltac:(lia) Ht4) as (P2 & _ & _).
        replace (B + y + y') with (B + (y + y')) by ring.
        eapply Rch_trans; [exact P1|].
        replace (a2 - (g2 - 1) * y') with (st_a eZ KZ K2Z (a - (g - 1) * (y + y')) (b0 + g * (y + y'))) by (unfold a2, st_a, b2, st_b, g2, at0, bt0; ring).
        replace (b2 + g2 * y') with (st_b eZ KZ (a - (g - 1) * (y + y')) (b0 + g * (y + y'))) by (unfold b2, st_b, g2, at0, bt0; ring).
        exact P2.
      - (* the detour *)
        intros E1. rewrite E1 in HDet. rewrite orb_true_r in HDet. specialize (HDet eq_refl). rewrite G4, G5.
        cbv iota in HDet. rewrite phi_max in HDet.
        intros y' Hy' Hm.
        replace (B + y + y') with (B + (y + y')) by ring.
        apply HDet; [lia|]. rewrite Z.add_mod by lia. rewrite Y4. rewrite Z.add_0_l, Z.mod_mod by lia. exact Hm. }
    rewrite G4 in HC. eapply Rch_trans; [exact HR|].
    replace (B + (y + phi (eY ch))) with (B + y + phi (eY ch)) by ring. exact HC.
Qed.
