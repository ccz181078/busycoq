(** Block lemmas for [halts]: a block lemma says that for every state in a region of (b,S,g), all sweeps of a word prefix run through
    to an exact offset. Regions are exact integer inequalities; the fixed-point point (beta,W) only chooses what to try. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
Import ListNotations.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Map Walk.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Ints HLines.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Definition Rch (a b a' b' : Z) : Prop := exists n r, Reach a b a' b' n r.
Lemma Rch_refl a b : Rch a b a b.
Proof. exists 0, 0. constructor. Qed.
Lemma Rch_trans a b a1 b1 a2 b2 : Rch a b a1 b1 -> Rch a1 b1 a2 b2 -> Rch a b a2 b2.
Proof. intros (n & r & H1) (m & s & H2). exists (n + m), (r + s). eapply Reach_trans; eauto. Qed.
Lemma Rch_step a b a1 b1 r : aStep a b = Some (a1, b1, r) -> Rch a b a1 b1.
Proof. intros H. exists 1, (r + 0). replace 1 with (1 + 0) by ring. econstructor; [exact H|constructor]. Qed.

(** ** The letters *)
Lemma letterD a b : a + 3 < b -> Rch a b (2 * a + 6) (b - a - 3).
Proof. intros H. eapply Rch_step. apply L_D. exact H. Qed.
Lemma letterU a b : b mod 2 = 1 -> (a - b + 5) mod 4 = 2 -> 5 <= b -> b + 1 <= a -> Rch a b (a - b + 11) (2 * b - 4).
Proof.
  intros H1 H2 H3 H4. eapply Rch_step. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [lia|]. destruct (Z.eqb_spec b 3) as [|_]; [lia|].
  rewrite H1. rewrite Z.eqb_refl. destruct (Z.eqb_spec b (a + 1)) as [|_]; [lia|].
  rewrite H2. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma letterV a b : b mod 2 = 1 -> (a - b + 5) mod 4 <> 2 -> 5 <= b -> b + 1 <= a -> Rch a b (a - b + 19) (2 * b - 8).
Proof.
  intros H1 H2 H3 H4. eapply Rch_step. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [lia|]. destruct (Z.eqb_spec b 3) as [|_]; [lia|].
  rewrite H1. rewrite Z.eqb_refl. destruct (Z.eqb_spec b (a + 1)) as [|_]; [lia|].
  destruct (Z.eqb_spec ((a - b + 5) mod 4) 2) as [|_]; [lia|]. reflexivity.
Qed.
Lemma letterW a b : b mod 2 = 0 -> b < a + 3 -> (a - b) mod 4 = 2 -> Rch a b 6 (a + b + 7).
Proof.
  intros H1 H2 H3. eapply Rch_step. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [subst b; discriminate|]. destruct (Z.eqb_spec b 3) as [|_]; [subst b; discriminate|].
  rewrite H1. change (0 =? 1) with false. rewrite H3. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma letterX a b : b mod 2 = 0 -> b < a + 3 -> (a - b) mod 4 <> 2 -> Rch a b 22 (a + b - 2).
Proof.
  intros H1 H2 H3. eapply Rch_step. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [|_]; [subst b; discriminate|]. destruct (Z.eqb_spec b 3) as [|_]; [subst b; discriminate|].
  rewrite H1. change (0 =? 1) with false.
  destruct (Z.eqb_spec ((a - b) mod 4) 2) as [|_]; [lia|]. reflexivity.
Qed.

(** ** Data *)
Record Line := mkLine { lt : int; lv : int }.
Record Ent := mkEnt {
  ec : int; era : int; erb : int; ez : int; ed2 : int;
  eW : int; eW1 : int; eW2 : int; elo : list Line; ehi : list Line;
  eY : int; elast : int; edet : bool; edlast : int; edres : int; eGm : int }.
Record Env := mkEnv { vz : int; vhas : bool; vd2 : int }.

Definition VOFF : int := 2305843009213693952.
Definition ONE : int := 268435456.
Definition TONE : int := 1073741824.
Definition Q1 : int := 268435456.

(** ** Meaning *)
Definition lo_l (r : Z) (x : Line) (b S g : Z) : Prop := lo_z (phi (lt x)) (phi (lv x) - VO) r b S g.
Definition hi_l (r : Z) (x : Line) (b S g : Z) : Prop := hi_z (phi (lt x)) (phi (lv x) - VO) r b S g.

Definition reg (e : Ent) (b S g : Z) : Prop :=
  Forall (fun x => lo_l (phi (eW e)) x b S g) (elo e) /\ Forall (fun x => hi_l (phi (eW e)) x b S g) (ehi e) /\
  phi (eW1 e) * g <= PP * S /\ PP * S <= phi (eW2 e) * g.

Definition PreH (a0 B a b g Ym : Z) : Prop :=
  forall y, 0 <= y <= Ym -> y mod 4 = 0 -> Rch a0 (B + y) (a - (g - 1) * y) (b + g * y).
Definition DetH (dz a0 B d2 dl dres : Z) : Prop :=
  forall y, 0 <= y <= dl -> y mod 4 = dres -> Rch dz (B + y) a0 (B + y + d2).

Definition line_ok (x : Line) : Prop := phi (lt x) <= TT /\ phi (lv x) < 4611686018427387904.

Definition ent_bd (e : Ent) : Prop :=
  Forall line_ok (elo e) /\ Forall line_ok (ehi e) /\
  phi (eW e) <= 1152921504606846976 /\ phi (eW1 e) <= 1152921504606846976 /\ phi (eW2 e) <= 2305843009213693952 /\
  phi (eY e) < TT /\ phi (eY e) mod 4 = 0 /\ phi (elast e) <= phi (eY e) /\ phi (ec e) < 1099511627776 /\
  phi (edlast e) < 2147483648 /\ phi (eGm e) < 2305843009213693952 /\
  phi (eW e) - 2147483648 <= phi (eW1 e) /\ phi (eW2 e) <= phi (eW e) + 2147483648.

Definition E_sem (e : Ent) : Prop :=
  forall B a b g,
    a + b = B + phi (ec e) -> a mod 4 = phi (era e) -> b mod 4 = phi (erb e) ->
    1 <= g -> phi (eGm e) <= g -> reg e b (a + b) g ->
    PreH (phi (ez e)) B a b g (phi (elast e)) ->
    (edet e = true -> DetH (28 - phi (ez e)) (phi (ez e)) B (phi (ed2 e)) (phi (edlast e)) (phi (edres e))) ->
    Rch (phi (ez e)) B (phi (ez e)) (B + phi (eY e)).

Definition ent_ok (e : Ent) : Prop := ent_bd e /\ E_sem e.

(** ** Helpers on ints *)
Definition max_ (a b : int) : int := if (a <? b)%uint63 then b else a.
Definition min_ (a b : int) : int := if (b <? a)%uint63 then b else a.
Lemma phi_max a b : phi (max_ a b) = Z.max (phi a) (phi b).
Proof.
  unfold max_. destruct (a <? b)%uint63 eqn:C.
  - apply ltb_true in C. lia.
  - apply ltb_false in C. lia.
Qed.
Lemma phi_min a b : phi (min_ a b) = Z.min (phi a) (phi b).
Proof.
  unfold min_. destruct (b <? a)%uint63 eqn:C.
  - apply ltb_true in C. lia.
  - apply ltb_false in C. lia.
Qed.
Lemma phi_land3 x : phi (x land 3)%uint63 = phi x mod 4.
Proof. rewrite land_spec'. change (phi 3%uint63) with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma phi_land1 x : phi (x land 1)%uint63 = phi x mod 2.
Proof. rewrite land_spec'. change (phi 1%uint63) with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma phi_lsr30 x : phi (x >> 30)%uint63 = phi x / TT.
Proof. rewrite lsr_spec. reflexivity. Qed.
Lemma phi_lsr2 x : phi (x >> 2)%uint63 = phi x / 4.
Proof. rewrite lsr_spec. reflexivity. Qed.
Lemma phi_lsl28 x : phi x < 34359738368 -> phi (x << 28)%uint63 = phi x * PP.
Proof.
  intros H. apply phi_lsl; [reflexivity|]. pose proof (phi_bd63 x). lia.
Qed.

(** ** Residues *)
Definition kind_of (ra rb : int) : int := if (((ra + 8 + 5 - rb) land 3) =? 2)%uint63 then 1%uint63 else 2%uint63.
Definition ra_next (a b k : int) : int :=
  if (k =? 0)%uint63 then ((2 * a + 6) land 3)%uint63 else if (k =? 1)%uint63 then ((a + 4 - b + 11) land 3)%uint63 else ((a + 4 - b + 19) land 3)%uint63.
Definition rb_next (a b k : int) : int :=
  if (k =? 0)%uint63 then ((b + 8 - a - 3) land 3)%uint63 else if (k =? 1)%uint63 then ((2 * b + 4 - 4) land 3)%uint63 else ((2 * b + 8 - 8) land 3)%uint63.
Definition kcost (k : int) : int := if (k =? 0)%uint63 then 3%uint63 else if (k =? 1)%uint63 then 7%uint63 else 11%uint63.

Section Res.
Variables (ra rb : int) (a b : Z).
Hypotheses (Ha : phi ra = a mod 4) (Hb : phi rb = b mod 4).
Lemma Bra : 0 <= phi ra < 4. Proof. rewrite Ha. apply Z.mod_pos_bound. reflexivity. Qed.
Lemma Brb : 0 <= phi rb < 4. Proof. rewrite Hb. apply Z.mod_pos_bound. reflexivity. Qed.

Lemma res_kind : ((phi (kind_of ra rb) = 1 /\ (a - b + 5) mod 4 = 2) \/ (phi (kind_of ra rb) = 2 /\ (a - b + 5) mod 4 <> 2)).
Proof.
  unfold kind_of. assert (E : phi ((ra + 8 + 5 - rb) land 3)%uint63 = (a - b + 5) mod 4).
  { pose proof Bra as B1. pose proof Brb as B2. rewrite phi_land3. assert (F : phi (ra + 8 + 5 - rb)%uint63 = phi ra + 8 + 5 - phi rb) by pv. rewrite F, Ha, Hb.
    Z.div_mod_to_equations. lia. }
  destruct (((ra + 8 + 5 - rb) land 3) =? 2)%uint63 eqn:C.
  - left. apply eqb_true in C. rewrite E in C. split; [reflexivity|exact C].
  - right. split; [reflexivity|]. intros X. rewrite <- E in X.
    assert (Y : ((ra + 8 + 5 - rb) land 3)%uint63 = 2%uint63) by (apply to_Z_inj; exact X).
    rewrite Y in C. discriminate.
Qed.

Lemma res_D : phi (ra_next ra rb 0) = (2 * a + 6) mod 4 /\ phi (rb_next ra rb 0) = (b - a - 3) mod 4.
Proof.
  pose proof Bra as B1. pose proof Brb as B2. unfold ra_next, rb_next. change (0 =? 0)%uint63 with true. cbv iota beta. split; rewrite phi_land3.
  - assert (F : phi (2 * ra + 6)%uint63 = 2 * phi ra + 6) by pv. rewrite F, Ha. Z.div_mod_to_equations. lia.
  - assert (F : phi (rb + 8 - ra - 3)%uint63 = phi rb + 8 - phi ra - 3) by pv. rewrite F, Ha, Hb. Z.div_mod_to_equations. lia.
Qed.
Lemma res_U : phi (ra_next ra rb 1) = (a - b + 11) mod 4 /\ phi (rb_next ra rb 1) = (2 * b - 4) mod 4.
Proof.
  pose proof Bra as B1. pose proof Brb as B2. unfold ra_next, rb_next. change (1 =? 0)%uint63 with false. change (1 =? 1)%uint63 with true. cbv iota beta. split; rewrite phi_land3.
  - assert (F : phi (ra + 4 - rb + 11)%uint63 = phi ra + 4 - phi rb + 11) by pv. rewrite F, Ha, Hb. Z.div_mod_to_equations. lia.
  - assert (F : phi (2 * rb + 4 - 4)%uint63 = 2 * phi rb + 4 - 4) by pv. rewrite F, Hb. Z.div_mod_to_equations. lia.
Qed.
Lemma res_V : phi (ra_next ra rb 2) = (a - b + 19) mod 4 /\ phi (rb_next ra rb 2) = (2 * b - 8) mod 4.
Proof.
  pose proof Bra as B1. pose proof Brb as B2. unfold ra_next, rb_next. change (2 =? 0)%uint63 with false. change (2 =? 1)%uint63 with false. cbv iota beta. split; rewrite phi_land3.
  - assert (F : phi (ra + 4 - rb + 19)%uint63 = phi ra + 4 - phi rb + 19) by pv. rewrite F, Ha, Hb. Z.div_mod_to_equations. lia.
  - assert (F : phi (2 * rb + 8 - 8)%uint63 = 2 * phi rb + 8 - 8) by pv. rewrite F, Hb. Z.div_mod_to_equations. lia.
Qed.
End Res.

(** The state at offset y keeps its residues when y is a multiple of 4. *)
Lemma res_at a g y : y mod 4 = 0 -> (a - (g - 1) * y) mod 4 = a mod 4.
Proof.
  intros H. assert (E : y = 4 * (y / 4)) by (Z.div_mod_to_equations; lia).
  rewrite E. replace (a - (g - 1) * (4 * (y / 4))) with (a + (- (g - 1) * (y / 4)) * 4) by ring. apply Z.mod_add. lia.
Qed.
Lemma resb_at b g y : y mod 4 = 0 -> (b + g * y) mod 4 = b mod 4.
Proof.
  intros H. assert (E : y = 4 * (y / 4)) by (Z.div_mod_to_equations; lia).
  rewrite E. replace (b + g * (4 * (y / 4))) with (b + (g * (y / 4)) * 4) by ring. apply Z.mod_add. lia.
Qed.

(** ** Rounds *)
Lemma rounds_rch a0 B D (n : nat) :
  (forall t, 0 <= t < Z.of_nat n -> Rch a0 (B + t * D) a0 (B + (t + 1) * D)) ->
  Rch a0 B a0 (B + Z.of_nat n * D).
Proof.
  induction n as [|n IH]; intros H.
  { change (Z.of_nat 0) with 0. replace (B + 0 * D) with B by ring. apply Rch_refl. }
  eapply Rch_trans; [apply IH; intros t Ht; apply H; lia|].
  specialize (H (Z.of_nat n) ltac:(lia)).
  replace (B + Z.of_nat (S n) * D) with (B + (Z.of_nat n + 1) * D) by lia. exact H.
Qed.

(** A word of one letter and a terminal letter from (a,b): reset value and start. *)
Lemma terminal a b : b mod 2 = 0 -> b < a + 3 ->
  ((a - b) mod 4 = 2 /\ Rch a b 6 (a + b + 7)) \/ ((a - b) mod 4 <> 2 /\ Rch a b 22 (a + b - 2)).
Proof.
  intros H1 H2. destruct (Z.eq_dec ((a - b) mod 4) 2) as [E|E].
  - left. split; [exact E|]. apply letterW; assumption.
  - right. split; [exact E|]. apply letterX; assumption.
Qed.

(** ** Stops: section 1 and section 3 of a node *)
Definition stop_rounds (b : Ent) (v : Env) (dl : bool) (beta : int) : option Ent :=
  let y := eY b in
  let ra := era b in let rb := erb b in
  let kind := if dl then 0%uint63 else kind_of ra rb in
  let cc := (ec b + kcost kind)%uint63 in
  let rae := ra_next ra rb kind in let rbe := rb_next ra rb kind in
  let e_ := if dl then 3%uint63 else 1%uint63 in
  let Wp := eW b in
  let lim := ((e_ * Wp) >> 2)%uint63 in
  if negb (((rbe land 1) =? 0)%uint63) || (negb dl && negb (((rb land 1) =? 1)%uint63)) || (cc <? 8)%uint63 || (1099511627776 <=? cc)%uint63
     || negb ((ez b =? vz v)%uint63) || negb ((ed2 b =? vd2 v)%uint63) then None else
  let isw := (((rae + 4 - rbe) land 3) =? 2)%uint63 in
  let z := if isw then 6%uint63 else 22%uint63 in
  let D1 := if isw then (cc + 7)%uint63 else (cc - 2)%uint63 in
  let direct := (z =? vz v)%uint63 && ((D1 land 3) =? 0)%uint63 in
  let det := negb direct && vhas v && (z + vz v =? 28)%uint63 && (((D1 + vd2 v) land 3) =? 0)%uint63 && (vd2 v <? 1099511627776)%uint63 in
  if direct || det then
    let DD := if direct then D1 else (D1 + vd2 v)%uint63 in
    let gapn := (lim + VOFF - beta - (y << 28) - 9)%uint63 in
    if (gapn <? VOFF)%uint63 then None else
    let T := (((gapn - VOFF) >> 28) / DD + 1)%uint63 in
    if (2097152 <=? T)%uint63 || (T =? 0)%uint63 then None else
    let ylast := (y + (T - 1) * DD)%uint63 in
    let Y' := (ylast + DD)%uint63 in
    if (1073741824 <=? Y')%uint63 then None else
    let hl := mkLine ((e_ * Q1)%uint63) (lim + VOFF - (ylast << 28) - 8)%uint63 in
    let lo1 := if dl then mkLine (2 * Q1)%uint63 (((2 * Wp + 3) >> 2) + VOFF - (y << 28) + 8)%uint63
               else mkLine 0%uint63 (VOFF + 16)%uint63 in
    let gneed := (ONE * (ylast + 64))%uint63 in
    let Gm := max_ (eGm b) gneed in
    if direct then
      Some (mkEnt (ec b) ra rb (ez b) (ed2 b) Wp (eW1 b) (eW2 b) (lo1 :: elo b) (hl :: ehi b) Y' ylast (edet b) (edlast b) (edres b) Gm)
    else
      let dr := (D1 land 3)%uint63 in
      if negb (edet b) || (edres b =? dr)%uint63 then
        Some (mkEnt (ec b) ra rb (ez b) (ed2 b) Wp (eW1 b) (eW2 b) (lo1 :: elo b) (hl :: ehi b) Y' ylast true (max_ (edlast b) (ylast + D1)%uint63) dr Gm)
      else None
  else None.

(** What the two new lines give, as facts about the state. *)
Lemma line_hi1 (e_ : Z) r ylast b S g lim : hi_z (e_ * 268435456) (lim - ylast * PP - 8) r b S g -> 1 <= g -> 4 * lim <= e_ * r ->
  32 * g <= PP * (e_ * S - 4 * (b + g * ylast)).
Proof.
  intros H G L. eapply (hi_guard e_ (lim - ylast * PP - 8) r ylast 8); [exact H|lia|lia].
Qed.
Lemma line_lo1 (e_ : Z) r y b S g lim : lo_z (e_ * 268435456) (lim - y * PP + 8) r b S g -> 1 <= g -> e_ * r <= 4 * lim ->
  32 * g <= PP * (4 * (b + g * y) - e_ * S).
Proof.
  intros H G L. eapply (lo_guard e_ (lim - y * PP + 8) r y 8); [exact H|lia|lia].
Qed.

(** One round of a stop after a u or v letter, or a D letter. *)
Lemma round_UV a b k D1 ra1 rb1 z : (k = 7 \/ k = 11) ->
  (k = 7 -> (a - b + 5) mod 4 = 2 /\ ra1 = (a - b + 11) mod 4 /\ rb1 = (2 * b - 4) mod 4) ->
  (k = 11 -> (a - b + 5) mod 4 <> 2 /\ ra1 = (a - b + 19) mod 4 /\ rb1 = (2 * b - 8) mod 4) ->
  b mod 2 = 1 -> 5 <= b -> b + 1 <= a -> 4 * b < a + b + 18 -> rb1 mod 2 = 0 ->
  (((ra1 + 4 - rb1) mod 4 = 2 /\ z = 6 /\ D1 = k + 7) \/ ((ra1 + 4 - rb1) mod 4 <> 2 /\ z = 22 /\ D1 = k - 2)) ->
  Rch a b z (a + b + D1).
Proof.
  intros Hk Hu Hv Odd B5 Ba Bs Ev Ht.
  destruct Hk as [ -> | -> ].
  - destruct (Hu eq_refl) as (H1 & H2 & H3).
    assert (R1 : Rch a b (a - b + 11) (2 * b - 4)) by (apply letterU; assumption).
    assert (E1 : (2 * b - 4) mod 2 = 0) by (Z.div_mod_to_equations; lia).
    assert (T : (a - b + 11 - (2 * b - 4)) mod 4 = (ra1 + 4 - rb1) mod 4) by (subst ra1 rb1; Z.div_mod_to_equations; lia).
    destruct (terminal (a - b + 11) (2 * b - 4) E1 ltac:(lia)) as [(C & R2)|(C & R2)]; eapply Rch_trans; [exact R1| |exact R1|].
    + destruct Ht as [(Hc0 & -> & ->)|(Hc0 & Hc1 & Hc2)]; [|congruence]. replace (a + b + (7 + 7)) with (a - b + 11 + (2 * b - 4) + 7) by ring. exact R2.
    + destruct Ht as [(Hc0 & Hc1 & Hc2)|(Hc0 & -> & ->)]; [congruence|]. replace (a + b + (7 - 2)) with (a - b + 11 + (2 * b - 4) - 2) by ring. exact R2.
  - destruct (Hv eq_refl) as (H1 & H2 & H3).
    assert (R1 : Rch a b (a - b + 19) (2 * b - 8)) by (apply letterV; assumption).
    assert (E1 : (2 * b - 8) mod 2 = 0) by (Z.div_mod_to_equations; lia).
    assert (T : (a - b + 19 - (2 * b - 8)) mod 4 = (ra1 + 4 - rb1) mod 4) by (subst ra1 rb1; Z.div_mod_to_equations; lia).
    destruct (terminal (a - b + 19) (2 * b - 8) E1 ltac:(lia)) as [(C & R2)|(C & R2)]; eapply Rch_trans; [exact R1| |exact R1|].
    + destruct Ht as [(Hc0 & -> & ->)|(Hc0 & Hc1 & Hc2)]; [|congruence]. replace (a + b + (11 + 7)) with (a - b + 19 + (2 * b - 8) + 7) by ring. exact R2.
    + destruct Ht as [(Hc0 & Hc1 & Hc2)|(Hc0 & -> & ->)]; [congruence|]. replace (a + b + (11 - 2)) with (a - b + 19 + (2 * b - 8) - 2) by ring. exact R2.
Qed.

Lemma round_D a b D1 ra1 rb1 z :
  ra1 = (2 * a + 6) mod 4 -> rb1 = (b - a - 3) mod 4 -> a + 3 < b -> 4 * b < 3 * (a + b) + 12 -> rb1 mod 2 = 0 ->
  (((ra1 + 4 - rb1) mod 4 = 2 /\ z = 6 /\ D1 = 10) \/ ((ra1 + 4 - rb1) mod 4 <> 2 /\ z = 22 /\ D1 = 1)) ->
  Rch a b z (a + b + D1).
Proof.
  intros H2 H3 G1 G2 Ev Ht.
  assert (R1 : Rch a b (2 * a + 6) (b - a - 3)) by (apply letterD; lia).
  assert (E1 : (b - a - 3) mod 2 = 0) by (subst rb1; Z.div_mod_to_equations; lia).
  assert (T : (2 * a + 6 - (b - a - 3)) mod 4 = (ra1 + 4 - rb1) mod 4) by (subst ra1 rb1; Z.div_mod_to_equations; lia).
  destruct (terminal (2 * a + 6) (b - a - 3) E1 ltac:(lia)) as [(C & R2)|(C & R2)]; eapply Rch_trans; [exact R1| |exact R1|].
  - destruct Ht as [(Hc0 & -> & ->)|(Hc0 & Hc1 & Hc2)]; [|congruence]. replace (a + b + 10) with (2 * a + 6 + (b - a - 3) + 7) by ring. exact R2.
  - destruct Ht as [(Hc0 & Hc1 & Hc2)|(Hc0 & -> & ->)]; [congruence|]. replace (a + b + 1) with (2 * a + 6 + (b - a - 3) - 2) by ring. exact R2.
Qed.

(** Guards of the rounds, from the lines. *)
Lemma guards_UV (a b g S yt ylast : Z)
  (HS : a + b = S) (Hg : 1 <= g) (Gn : PP * (ylast + 64) <= g)
  (Hy : 0 <= yt <= ylast)
  (Hl : 32 * g <= PP * (S - 4 * (b + g * ylast)))
  (L0 : 16 * g <= PP * b)
  (at_ := a - (g - 1) * yt) (bt := b + g * yt) :
  5 <= bt /\ bt + 1 <= at_ /\ 4 * bt < at_ + bt + 18.
Proof.
  subst at_ bt.
  assert (M1 : g * yt <= g * ylast) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M0 : 0 <= g * yt) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Y0 : 0 <= ylast) by lia.
  assert (B1 : 1024 <= b) by lia.
  assert (C : 2048 <= S - 4 * (b + g * ylast)) by lia.
  replace ((a - (g - 1) * yt)) with (a - g * yt + yt) by ring.
  lia.
Qed.
Lemma guards_D (a b g S y yt ylast : Z)
  (HS : a + b = S) (Hg : 1 <= g) (Gn : PP * (ylast + 64) <= g)
  (Hy : y <= yt <= ylast) (Hy0 : 0 <= y)
  (Hl : 32 * g <= PP * (3 * S - 4 * (b + g * ylast)))
  (L0 : 32 * g <= PP * (4 * (b + g * y) - 2 * S))
  (at_ := a - (g - 1) * yt) (bt := b + g * yt) :
  at_ + 3 < bt /\ 4 * bt < 3 * (at_ + bt) + 12.
Proof.
  subst at_ bt.
  assert (M1 : g * yt <= g * ylast) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M2 : g * y <= g * yt) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M3 : g * 1 <= g * g) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (Y0 : 0 <= ylast) by lia.
  assert (C : 32 * (ylast + 64) <= 4 * (b + g * y) - 2 * S) by lia.
  assert (C2 : 0 <= 3 * S - 4 * (b + g * ylast)) by lia.
  assert (Y1 : yt <= g * yt).
  { replace yt with (1 * yt) at 1 by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  replace ((a - (g - 1) * yt)) with (a - g * yt + yt) by ring.
  lia.
Qed.

Lemma Forall_cons_iff {A} (P : A -> Prop) x l : Forall P (x :: l) -> P x /\ Forall P l.
Proof. intros H. inversion H; subst. auto. Qed.

Lemma PreH_mono a0 B a b g Y1 Y2 : Y1 <= Y2 -> PreH a0 B a b g Y2 -> PreH a0 B a b g Y1.
Proof. intros L H y Hy Hm. apply H; [lia|exact Hm]. Qed.

Lemma stop_sound b v dl beta e : ent_ok b -> phi (vz v) = 6 \/ phi (vz v) = 22 -> stop_rounds b v dl beta = Some e ->
  ent_ok e /\ ec e = ec b /\ era e = era b /\ erb e = erb b /\ ez e = ez b /\ ed2 e = ed2 b /\ eW e = eW b /\
  eW1 e = eW1 b /\ eW2 e = eW2 b.
Proof.
  intros [Bd Sem] Hz H. unfold stop_rounds in H. cbv zeta in H.
  destruct Bd as (BL & BU & BW & BW1 & BW2 & BY & BY4 & BL2 & Bc & BD & BG & BWa & BWb).
  set (kind := if dl then 0%uint63 else kind_of (era b) (erb b)) in *.
  set (cc := (ec b + kcost kind)%uint63) in *.
  set (rae := ra_next (era b) (erb b) kind) in *.
  set (rbe := rb_next (era b) (erb b) kind) in *.
  set (e_ := if dl then 3%uint63 else 1%uint63) in *.
  destruct (negb ((rbe land 1) =? 0)%uint63 || (negb dl && negb ((erb b land 1) =? 1)%uint63) || (cc <? 8)%uint63 || (1099511627776 <=? cc)%uint63
     || negb ((ez b =? vz v)%uint63) || negb ((ed2 b =? vd2 v)%uint63)) eqn:G1; [discriminate|].
  repeat (apply orb_false_iff in G1; destruct G1 as [G1 ?]).
  rename H0 into G6. rename H1 into G5. rename H2 into G4. rename H3 into G3. rename H4 into G2.
  apply negb_false_iff in G1. apply negb_false_iff in G5. apply negb_false_iff in G6.
  apply ltb_false in G3. apply leb_false in G4. change (phi 8%uint63) with 8 in G3. change (phi 1099511627776%uint63) with 1099511627776 in G4.
  apply Uint63.eqb_spec in G5. apply Uint63.eqb_spec in G6.
  set (isw := ((rae + 4 - rbe) land 3 =? 2)%uint63) in *.
  set (z := if isw then 6%uint63 else 22%uint63) in *.
  set (D1 := if isw then (cc + 7)%uint63 else (cc - 2)%uint63) in *.
  set (direct := (z =? vz v)%uint63 && ((D1 land 3) =? 0)%uint63) in *.
  set (det := negb direct && vhas v && (z + vz v =? 28)%uint63 && (((D1 + vd2 v) land 3) =? 0)%uint63 && (vd2 v <? 1099511627776)%uint63) in *.
  destruct (direct || det) eqn:G7; [|discriminate].
  set (DD := if direct then D1 else (D1 + vd2 v)%uint63) in *.
  set (gapn := (((e_ * eW b) >> 2) + VOFF - beta - (eY b << 28) - 9)%uint63) in *.
  destruct (gapn <? VOFF)%uint63 eqn:G8; [discriminate|].
  set (T := (((gapn - VOFF) >> 28) / DD + 1)%uint63) in *.
  destruct ((2097152 <=? T)%uint63 || (T =? 0)%uint63) eqn:G9; [discriminate|].
  apply orb_false_iff in G9. destruct G9 as [G9 G10]. apply leb_false in G9. change (phi 2097152%uint63) with 2097152 in G9.
  assert (T1 : 1 <= phi T).
  { pose proof (phi_bd63 T). destruct (Z.eq_dec (phi T) 0) as [E|E]; [|lia].
    assert (TZ : T = 0%uint63) by (apply to_Z_inj; exact E). rewrite TZ in G10. discriminate. }
  clearbody T.
  set (ylast := (eY b + (T - 1) * DD)%uint63) in *.
  destruct (1073741824 <=? (ylast + DD))%uint63 eqn:G11; [discriminate|]. apply leb_false in G11. change (phi 1073741824%uint63) with TT in G11.
  (** values *)
  assert (Ee : phi e_ = 1 \/ phi e_ = 3) by (unfold e_; destruct dl; [right|left]; reflexivity).
  assert (Ek : phi (kcost kind) = 3 \/ phi (kcost kind) = 7 \/ phi (kcost kind) = 11).
  { unfold kcost. destruct (kind =? 0)%uint63; [left; reflexivity|]. destruct (kind =? 1)%uint63; [right; left; reflexivity|right; right; reflexivity]. }
  assert (Ecc : phi cc = phi (ec b) + phi (kcost kind)) by (unfold cc; pv).
  assert (ED1 : (isw = true /\ phi D1 = phi cc + 7) \/ (isw = false /\ phi D1 = phi cc - 2)).
  { unfold D1. destruct isw; [left; split; [reflexivity|pv]|right; split; [reflexivity|pv]]. }
  assert (Bd2 : det = true -> phi (vd2 v) < 1099511627776).
  { unfold det. intros X. apply andb_prop in X. destruct X as [_ X]. exact (ltb_true _ _ X). }
  assert (EDD : (direct = true /\ phi DD = phi D1) \/ (direct = false /\ det = true /\ phi DD = phi D1 + phi (vd2 v))).
  { unfold DD. destruct direct; [left; split; reflexivity|]. cbn [orb] in G7. rewrite G7. right. repeat split. specialize (Bd2 G7). pv. }
  assert (BD1 : 1 <= phi D1 < 1099511627776 + 8) by (destruct ED1 as [[_ X]|[_ X]]; lia).
  assert (BDD : 1 <= phi DD < 2199023255552 + 8) by (pose proof (phi_bd63 (vd2 v)); destruct EDD as [[_ X]|(_ & Hd & X)]; [lia|specialize (Bd2 Hd); lia]).
  assert (Ey : phi ylast = phi (eY b) + (phi T - 1) * phi DD).
  { unfold ylast. apply phi_of_cg; [cgs; assert (F : phi (T - 1)%uint63 = phi T - 1) by pv; unfold cg; rewrite F; reflexivity|].
    assert (0 <= (phi T - 1) * phi DD <= 2097152 * 2199023255560) by nia.
    pose proof (phi_bd63 (eY b)). lia. }
  assert (EY' : phi (ylast + DD)%uint63 = phi ylast + phi DD).
  { assert (0 <= (phi T - 1) * phi DD <= 2097152 * 2199023255560) by nia. pose proof (phi_bd63 (eY b)). pv. }
  rewrite EY' in G11.
  assert (By0 : 0 <= phi (eY b)) by (pose proof (phi_bd63 (eY b)); lia).
  assert (Byl : phi (eY b) <= phi ylast < TT) by (assert (0 <= (phi T - 1) * phi DD) by nia; lia).
  assert (El28 : phi (ylast << 28)%uint63 = phi ylast * PP) by (apply phi_lsl28; lia).
  assert (Ey28 : phi (eY b << 28)%uint63 = phi (eY b) * PP) by (apply phi_lsl28; lia).
  assert (BW0 : 0 <= phi (eW b)) by (pose proof (phi_bd63 (eW b)); lia).
  assert (Elim : phi ((e_ * eW b) >> 2)%uint63 = (phi e_ * phi (eW b)) / 4).
  { rewrite phi_lsr2. f_equal. assert (X : 0 <= phi e_ * phi (eW b) <= 3 * 1152921504606846976) by nia.
    apply phi_of_cg; [cgs|lia]. }
  set (lim := ((e_ * eW b) >> 2)%uint63) in *.
  assert (Blim : 0 <= phi lim <= 864691128455135232 /\ 4 * phi lim <= phi e_ * phi (eW b)).
  { rewrite Elim. assert (X : 0 <= phi e_ * phi (eW b) <= 3 * 1152921504606846976) by nia. Z.div_mod_to_equations. lia. }
  assert (Ehv : phi (lim + VOFF - (ylast << 28) - 8)%uint63 = phi lim + VO - phi ylast * PP - 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite El28; reflexivity|]. change (phi VOFF) with VO. nia. }
  assert (Edv : phi ((2 * eW b + 3) >> 2)%uint63 = (2 * phi (eW b) + 3) / 4).
  { rewrite phi_lsr2. f_equal. pv. }
  set (lim2 := ((2 * eW b + 3) >> 2)%uint63) in *.
  assert (Blim2 : 0 <= phi lim2 <= 576460752303423489 /\ 2 * phi (eW b) <= 4 * phi lim2).
  { rewrite Edv. Z.div_mod_to_equations. lia. }
  assert (Elv : phi (lim2 + VOFF - (eY b << 28) + 8)%uint63 = phi lim2 + VO - phi (eY b) * PP + 8).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Ey28; reflexivity|]. change (phi VOFF) with VO. nia. }
  assert (Eg : phi (ONE * (ylast + 64))%uint63 = PP * (phi ylast + 64)).
  { apply phi_of_cg; [cgs; unfold cg; reflexivity|lia]. }
  assert (DD4 : phi DD mod 4 = 0).
  { destruct EDD as [[Hd X]|(Hd & Hd2 & X)].
    - unfold direct in Hd. apply andb_prop in Hd. destruct Hd as [_ Hd]. apply eqb_true in Hd. rewrite phi_land3 in Hd. rewrite X. exact Hd.
    - pose proof (Bd2 Hd2) as Bx. unfold det in Hd2. apply andb_prop in Hd2. destruct Hd2 as [Hd2 _]. apply andb_prop in Hd2. destruct Hd2 as [_ Hd2].
      apply eqb_true in Hd2. rewrite phi_land3 in Hd2.
      assert (F : phi (D1 + vd2 v)%uint63 = phi D1 + phi (vd2 v)) by pv. rewrite F in Hd2. rewrite X. exact Hd2. }
  assert (Eylm : (phi ylast + phi DD) mod 4 = 0).
  { rewrite Ey. assert (Y4 : phi (eY b) = 4 * (phi (eY b) / 4)) by (Z.div_mod_to_equations; lia).
    assert (D4 : phi DD = 4 * (phi DD / 4)) by (Z.div_mod_to_equations; lia).
    rewrite Y4, D4. set (p := phi (eY b) / 4). set (q := phi DD / 4).
    replace (4 * p + (phi T - 1) * (4 * q) + 4 * q) with (0 + (p + (phi T - 1) * q + q) * 4) by ring. rewrite Z.mod_add by lia. reflexivity. }
  assert (Main : forall (detf : bool) (dlast dres : int),
     phi (edlast b) <= phi dlast < 2147483648 ->
     (edet b = true -> detf = true /\ dres = edres b) ->
     (direct = false -> detf = true /\ phi dres = phi D1 mod 4 /\ phi ylast + phi D1 <= phi dlast) ->
     ent_ok (mkEnt (ec b) (era b) (erb b) (ez b) (ed2 b) (eW b) (eW1 b) (eW2 b)
       ((if dl then mkLine (2 * Q1)%uint63 (lim2 + VOFF - (eY b << 28) + 8)%uint63 else mkLine 0%uint63 (VOFF + 16)%uint63) :: elo b)
       (mkLine (e_ * Q1)%uint63 (lim + VOFF - (ylast << 28) - 8)%uint63 :: ehi b) (ylast + DD)%uint63 ylast detf dlast dres (max_ (eGm b) (ONE * (ylast + 64))%uint63))).
  { intros detf dlast dres Hdl Hd1 Hd2_. split.
    - (* bounds *)
      unfold ent_bd. cbn [elo ehi eW eW1 eW2 eY elast edlast eGm ec]. rewrite EY', phi_max, Eg. repeat split; try lia.
      + constructor; [|exact BL]. destruct dl; unfold line_ok; cbn [lt lv].
        * change (phi (2 * Q1)%uint63) with 536870912. rewrite Elv. split; [lia|]. lia.
        * change (phi 0%uint63) with 0. change (phi (VOFF + 16)%uint63) with (VO + 16). split; lia.
      + constructor; [|exact BU]. unfold line_ok; cbn [lt lv]. rewrite Ehv. split.
        * assert (Q : phi (e_ * Q1)%uint63 = phi e_ * 268435456) by (destruct Ee as [X|X]; pv). rewrite Q. lia.
        * lia.
    - (* meaning *)
      intros B a b0 g HS Ha Hb Hg HG Hreg HPre HDet. cbn [ec era erb ez ed2 eW eW1 eW2 elo ehi eY elast edet edlast edres eGm] in *.
      rewrite phi_max, Eg in HG. destruct Hreg as (RL & RU & R1 & R2).
      apply Forall_cons_iff in RL. destruct RL as [Rlo RL]. apply Forall_cons_iff in RU. destruct RU as [Rhi RU].
      set (S := a + b0) in *.
      assert (HR : Rch (phi (ez b)) B (phi (ez b)) (B + phi (eY b))).
      { apply (Sem B a b0 g); try assumption; try lia.
        - unfold reg. repeat split; assumption.
        - eapply PreH_mono; [|exact HPre]. lia.
        - intros E1. destruct (Hd1 E1) as [E2 ->]. specialize (HDet E2). intros y Hy Hm. apply HDet; [lia|exact Hm]. }
      assert (Hhi : 32 * g <= PP * (phi e_ * S - 4 * (b0 + g * phi ylast))).
      { unfold hi_l in Rhi. cbn [lt lv] in Rhi. rewrite Ehv in Rhi.
        assert (Q : phi (e_ * Q1)%uint63 = phi e_ * 268435456) by (destruct Ee as [X|X]; pv). rewrite Q in Rhi.
        apply (line_hi1 (phi e_) (phi (eW b)) (phi ylast) b0 S g (phi lim)); [|lia|lia].
        replace (phi lim - phi ylast * PP - 8) with (phi lim + VO - phi ylast * PP - 8 - VO) by ring. exact Rhi. }
      assert (Round : forall t, 0 <= t < phi T ->
        Rch (phi (ez b)) (B + phi (eY b) + t * phi DD) (phi (ez b)) (B + phi (eY b) + (t + 1) * phi DD)).
      { intros t Ht. set (yt := phi (eY b) + t * phi DD).
        assert (Yt : phi (eY b) <= yt <= phi ylast).
        { unfold yt. rewrite Ey. assert (0 <= t * phi DD) by (apply Z.mul_nonneg_nonneg; lia). assert (t * phi DD <= (phi T - 1) * phi DD) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
        assert (Yt4 : yt mod 4 = 0).
        { unfold yt. assert (Y4 : phi (eY b) = 4 * (phi (eY b) / 4)) by (Z.div_mod_to_equations; lia).
          assert (D4 : phi DD = 4 * (phi DD / 4)) by (Z.div_mod_to_equations; lia).
          rewrite Y4, D4. set (p := phi (eY b) / 4). set (q := phi DD / 4).
          replace (4 * p + t * (4 * q)) with (0 + (p + t * q) * 4) by ring. rewrite Z.mod_add by lia. reflexivity. }
        assert (HP : Rch (phi (ez b)) (B + yt) (a - (g - 1) * yt) (b0 + g * yt)) by (apply HPre; [lia|exact Yt4]).
        set (at_ := a - (g - 1) * yt) in *. set (bt := b0 + g * yt) in *.
        assert (Sum_ : at_ + bt = B + yt + phi (ec b)).
        { unfold at_, bt. replace (a - (g - 1) * yt + (b0 + g * yt)) with (S + yt) by (unfold S; ring). rewrite HS. ring. }
        assert (Ra : phi (era b) = at_ mod 4) by (unfold at_; rewrite res_at by exact Yt4; symmetry; exact Ha).
        assert (Rb : phi (erb b) = bt mod 4) by (unfold bt; rewrite resb_at by exact Yt4; symmetry; exact Hb).
        assert (Wd : Rch at_ bt (phi z) (B + yt + phi D1)).
        { assert (Risw : ((phi rae + 4 - phi rbe) mod 4 = 2 /\ isw = true) \/ ((phi rae + 4 - phi rbe) mod 4 <> 2 /\ isw = false)).
          { assert (BA : 0 <= phi rae < 4 /\ 0 <= phi rbe < 4).
            { unfold rae, rbe, ra_next, rb_next. destruct (kind =? 0)%uint63; [|destruct (kind =? 1)%uint63]; rewrite !phi_land3; split; apply Z.mod_pos_bound; reflexivity. }
            assert (F : phi (rae + 4 - rbe)%uint63 = phi rae + 4 - phi rbe) by pv.
            assert (F2 : phi ((rae + 4 - rbe) land 3)%uint63 = (phi rae + 4 - phi rbe) mod 4) by (rewrite phi_land3, F; reflexivity).
            destruct isw eqn:Ci.
            - left. split; [|reflexivity]. unfold isw in Ci. apply eqb_true in Ci. rewrite F2 in Ci. exact Ci.
            - right. split; [|reflexivity]. intros X. rewrite <- F2 in X.
              assert (Y : ((rae + 4 - rbe) land 3)%uint63 = 2%uint63) by (apply to_Z_inj; exact X).
              unfold isw in Ci. rewrite Y in Ci. discriminate. }
          assert (Zc : (isw = true /\ phi z = 6) \/ (isw = false /\ phi z = 22)) by (unfold z; destruct isw; [left|right]; split; reflexivity).
          assert (Ev : phi rbe mod 2 = 0).
          { apply eqb_true in G1. rewrite phi_land1 in G1. exact G1. }
          destruct dl.
          - (* letter D *)
            assert (Ec3 : phi (kcost kind) = 3) by reflexivity.
            destruct (res_D (era b) (erb b) at_ bt Ra Rb) as [E1 E2]. change (ra_next (era b) (erb b) 0%uint63) with rae in E1. change (rb_next (era b) (erb b) 0%uint63) with rbe in E2.
            assert (HL : 32 * g <= PP * (4 * (b0 + g * phi (eY b)) - 2 * S)).
            { unfold lo_l in Rlo. cbn [lt lv] in Rlo. rewrite Elv in Rlo.
              apply (line_lo1 2 (phi (eW b)) (phi (eY b)) b0 S g (phi lim2)); [|lia|lia].
              change (2 * 268435456) with (phi (2 * Q1)%uint63).
              replace (phi lim2 - phi (eY b) * PP + 8) with (phi lim2 + VO - phi (eY b) * PP + 8 - VO) by ring. exact Rlo. }
            assert (E3 : phi e_ = 3) by reflexivity. rewrite E3 in Hhi.
            destruct (guards_D a b0 g S (phi (eY b)) yt (phi ylast) eq_refl Hg ltac:(lia) ltac:(lia) ltac:(lia) Hhi HL) as [Gd1 Gd2].
            fold at_ bt in Gd1, Gd2.
            replace (B + yt + phi D1) with (at_ + bt + (phi D1 - phi (ec b))) by lia.
            apply (round_D at_ bt (phi D1 - phi (ec b)) (phi rae) (phi rbe) (phi z)); try assumption.
            destruct ED1 as [[C X]|[C X]]; destruct Risw as [[C1 C2]|[C1 C2]]; destruct Zc as [[C3 C4]|[C3 C4]]; try congruence.
            + left. repeat split; try assumption. lia.
            + right. repeat split; try assumption. lia.
          - (* letter u or v *)
            assert (Ev2 : bt mod 2 = 1).
            { apply andb_false_iff in G2. destruct G2 as [G2|G2]; [discriminate|]. apply negb_false_iff in G2. apply eqb_true in G2.
              rewrite phi_land1, Rb in G2. change (phi 1%uint63) with 1 in G2. Z.div_mod_to_equations. lia. }
            assert (L0 : 16 * g <= PP * b0).
            { unfold lo_l in Rlo. cbn [lt lv] in Rlo. change (phi 0%uint63) with 0 in Rlo. change (phi (VOFF + 16)%uint63 - VO) with 16 in Rlo.
              unfold lo_z in Rlo. lia. }
            assert (E1_ : phi e_ = 1) by reflexivity. rewrite E1_ in Hhi.
            destruct (guards_UV a b0 g S yt (phi ylast) eq_refl Hg ltac:(lia) ltac:(lia) ltac:(lia) L0) as (Gu1 & Gu2 & Gu3).
            fold at_ bt in Gu1, Gu2, Gu3.
            destruct (res_kind (era b) (erb b) at_ bt Ra Rb) as [[K1 K2]|[K1 K2]].
            + assert (Kk : kind = 1%uint63) by (apply to_Z_inj; exact K1).
              destruct (res_U (era b) (erb b) at_ bt Ra Rb) as [E1 E2].
              assert (Ec7 : phi (kcost kind) = 7) by (rewrite Kk; reflexivity).
              assert (E1' : phi rae = (at_ - bt + 11) mod 4) by (unfold rae; rewrite Kk; exact E1).
              assert (E2' : phi rbe = (2 * bt - 4) mod 4) by (unfold rbe; rewrite Kk; exact E2).
              replace (B + yt + phi D1) with (at_ + bt + (phi D1 - phi (ec b))) by lia.
              apply (round_UV at_ bt 7 (phi D1 - phi (ec b)) (phi rae) (phi rbe) (phi z)); try assumption.
              * left; reflexivity.
              * intros _. repeat split; assumption.
              * intros X; discriminate.
              * destruct ED1 as [[C X]|[C X]]; destruct Risw as [[C1 C2]|[C1 C2]]; destruct Zc as [[C3 C4]|[C3 C4]]; try congruence.
                -- left. repeat split; try assumption. lia.
                -- right. repeat split; try assumption. lia.
            + assert (Kk : kind = 2%uint63) by (apply to_Z_inj; exact K1).
              destruct (res_V (era b) (erb b) at_ bt Ra Rb) as [E1 E2].
              assert (Ec7 : phi (kcost kind) = 11) by (rewrite Kk; reflexivity).
              assert (E1' : phi rae = (at_ - bt + 19) mod 4) by (unfold rae; rewrite Kk; exact E1).
              assert (E2' : phi rbe = (2 * bt - 8) mod 4) by (unfold rbe; rewrite Kk; exact E2).
              replace (B + yt + phi D1) with (at_ + bt + (phi D1 - phi (ec b))) by lia.
              apply (round_UV at_ bt 11 (phi D1 - phi (ec b)) (phi rae) (phi rbe) (phi z)); try assumption.
              * right; reflexivity.
              * intros X; discriminate.
              * intros _. repeat split; assumption.
              * destruct ED1 as [[C X]|[C X]]; destruct Risw as [[C1 C2]|[C1 C2]]; destruct Zc as [[C3 C4]|[C3 C4]]; try congruence.
                -- left. repeat split; try assumption. lia.
                -- right. repeat split; try assumption. lia. }
        replace (B + phi (eY b) + t * phi DD) with (B + yt) by (unfold yt; ring).
        replace (B + phi (eY b) + (t + 1) * phi DD) with (B + yt + phi DD) by (unfold yt; ring).
        eapply Rch_trans; [exact HP|]. eapply Rch_trans; [exact Wd|].
        destruct EDD as [[Hd X]|(Hd & Hd2 & X)].
        - unfold direct in Hd. apply andb_prop in Hd. destruct Hd as [Hd _]. apply Uint63.eqb_spec in Hd.
          rewrite Hd, <- G5. rewrite X. apply Rch_refl.
        - pose proof (Hd2_ Hd) as DD_. destruct DD_ as (D1_ & D2_ & D3_). specialize (HDet D1_).
          assert (Zz : phi z = 28 - phi (ez b)).
          { unfold det in Hd2. apply andb_prop in Hd2. destruct Hd2 as [Hd2 _]. apply andb_prop in Hd2. destruct Hd2 as [Hd2 _]. apply andb_prop in Hd2. destruct Hd2 as [_ Hd2].
            apply eqb_true in Hd2. rewrite G5. assert (F : phi (z + vz v)%uint63 = phi z + phi (vz v)).
            { assert (Hz' : phi z <= 22) by (unfold z; destruct isw; cbv; discriminate). pv. }
            rewrite F in Hd2. change (phi 28%uint63) with 28 in Hd2. lia. }
          assert (M4 : (yt + phi D1) mod 4 = phi D1 mod 4) by (rewrite Z.add_mod by lia; rewrite Yt4; rewrite Z.add_0_l, Z.mod_mod by lia; reflexivity).
          pose proof (HDet (yt + phi D1) ltac:(lia) ltac:(rewrite M4; symmetry; exact D2_)) as HD.
          rewrite Zz. replace (B + yt + phi D1) with (B + (yt + phi D1)) by ring.
          replace (B + yt + phi DD) with (B + (yt + phi D1) + phi (ed2 b)) by (rewrite X; rewrite G6; ring).
          exact HD. }
      assert (RR_ : Rch (phi (ez b)) (B + phi (eY b)) (phi (ez b)) (B + phi (eY b) + Z.of_nat (Z.to_nat (phi T)) * phi DD)).
      { apply rounds_rch. intros t Ht. rewrite Z2Nat.id in Ht by lia. apply Round. exact Ht. }
      rewrite Z2Nat.id in RR_ by lia.
      rewrite EY', Ey. eapply Rch_trans; [exact HR|].
      replace (B + (phi (eY b) + (phi T - 1) * phi DD + phi DD)) with (B + phi (eY b) + phi T * phi DD) by ring. exact RR_. }
  destruct direct eqn:Dr.
  - injection H as <-. split; [|repeat split].
    apply Main; [lia|intros X; split; [exact X|reflexivity]|intros X; discriminate].
  - destruct (negb (edet b) || (edres b =? (D1 land 3))%uint63) eqn:Cd; [|discriminate].
    injection H as <-. split; [|repeat split].
    assert (Hdet : det = true) by (cbn [orb] in G7; exact G7).
    assert (D1DD : phi D1 <= phi DD) by (destruct EDD as [[C _]|(_ & _ & X)]; [discriminate|pose proof (phi_bd63 (vd2 v)); lia]).
    assert (EyD : phi (ylast + D1)%uint63 = phi ylast + phi D1) by pv.
    apply Main.
    + rewrite phi_max, EyD. lia.
    + intros E1. rewrite E1 in Cd. cbn [negb orb] in Cd. apply Uint63.eqb_spec in Cd. split; [reflexivity|symmetry; exact Cd].
    + intros _. split; [reflexivity|]. rewrite phi_land3. split; [reflexivity|]. rewrite phi_max, EyD. lia.
Qed.

(** ** Children: sections 2 and 4 of a node *)
Definition pull_line (sg : bool) (e_ Wq r' yfx : int) (x : Line) : option Line :=
  let t' := lt x in
  let f := ((t' * (Wq - r')) >> 30)%uint63 in
  let vv := if sg then (lv x + f + 9 + e_ * Wq)%uint63 else (lv x + f + e_ * Wq)%uint63 in
  let sb := if sg then yfx else (yfx + 8)%uint63 in
  if (sb <=? vv)%uint63 && ((vv - sb) <? 4611686018427387904)%uint63 then
    Some (mkLine ((t' + e_ * TONE) >> 2)%uint63 (vv - sb)%uint63)
  else None.
Fixpoint pulls (sg : bool) (e_ Wq r' yfx : int) (l acc : list Line) : option (list Line) :=
  match l with
  | [] => Some acc
  | x :: t =>
    match pull_line sg e_ Wq r' yfx x with
    | Some y => pulls sg e_ Wq r' yfx t (y :: acc)
    | None => None
    end
  end.
Lemma pulls_spec sg e_ Wq r' yfx l : forall acc res, pulls sg e_ Wq r' yfx l acc = Some res ->
  (forall z, In z acc -> In z res) /\ (forall x, In x l -> exists y, pull_line sg e_ Wq r' yfx x = Some y /\ In y res) /\
  (forall z, In z res -> In z acc \/ exists x, In x l /\ pull_line sg e_ Wq r' yfx x = Some z).
Proof.
  induction l as [|x t IH]; intros acc res H.
  - cbn in H. injection H as <-. repeat split; [auto|intros x []|left; assumption].
  - cbn in H. destruct (pull_line sg e_ Wq r' yfx x) as [y|] eqn:P; [|discriminate].
    destruct (IH _ _ H) as (H1 & H2 & H3). repeat split.
    + intros z Hz. apply H1. right. exact Hz.
    + intros x' [<-|Hx].
      * exists y. split; [exact P|]. apply H1. left. reflexivity.
      * apply H2. exact Hx.
    + intros z Hz. destruct (H3 z Hz) as [[<-|Ha]|(x' & Hx & Hp)].
      * right. exists x. split; [left; reflexivity|exact P].
      * left. exact Ha.
      * right. exists x'. split; [right; exact Hx|exact Hp].
Qed.

Definition absv (u : int) : int := if (VOFF <=? u)%uint63 then (u - VOFF)%uint63 else (VOFF - u)%uint63.
Fixpoint maxv (l : list Line) (m : int) : int :=
  match l with [] => m | x :: t => maxv t (max_ m (absv (lv x))) end.
Lemma maxv_spec l : forall m, phi m <= phi (maxv l m) /\ (forall x, In x l -> Z.abs (phi (lv x) - VO) <= phi (maxv l m)).
Proof.
  induction l as [|x t IH]; intros m.
  - split; [cbn; lia|intros x []].
  - cbn [maxv]. destruct (IH (max_ m (absv (lv x)))) as [H1 H2]. rewrite phi_max in H1.
    assert (A : Z.abs (phi (lv x) - VO) = phi (absv (lv x))).
    { unfold absv. destruct (VOFF <=? lv x)%uint63 eqn:C.
      - apply leb_true in C. change (phi VOFF) with VO in C. assert (F : phi (lv x - VOFF)%uint63 = phi (lv x) - VO).
        { pv. }
        rewrite F. lia.
      - apply leb_false in C. change (phi VOFF) with VO in C. assert (F : phi (VOFF - lv x)%uint63 = VO - phi (lv x)).
        { pv. }
        rewrite F. lia. }
    split; [lia|]. intros x' [<-|Hx]; [lia|apply H2; exact Hx].
Qed.

Definition absorb (b ch : Ent) (dl : bool) : option Ent :=
  let y := eY b in
  let ra := era b in let rb := erb b in
  let kind := if dl then 0%uint63 else kind_of ra rb in
  let e_ := if dl then 3%uint63 else 1%uint63 in
  let K2 := if dl then 6%uint63 else if (kind =? 1)%uint63 then 10%uint63 else 14%uint63 in
  let ra1 := ra_next ra rb kind in let rb1 := rb_next ra rb kind in
  let Wp := eW b in let Wq := (Wp >> 2)%uint63 in
  let r' := eW ch in
  let yfx := (y << 28)%uint63 in
  let Y' := (y + eY ch)%uint63 in
  if (ec ch =? ec b + K2)%uint63 && (era ch =? ra_next ra1 rb1 0)%uint63 && (erb ch =? rb_next ra1 rb1 0)%uint63
     && (ez ch =? ez b)%uint63 && (ed2 ch =? ed2 b)%uint63 && (dl || ((rb land 1) =? 1)%uint63)
     && (r' =? eW1 ch)%uint63 && (r' <=? Wq)%uint63 && ((Wq - r') <? 4294967296)%uint63 && (Y' <? 1073741824)%uint63 && (16 <=? eW2 ch)%uint63 then
    let lo0 := if dl then [mkLine (3 * Q1)%uint63 (((3 * Wp + 3) >> 2) + VOFF - yfx + 8)%uint63]
               else [mkLine Q1 (((Wp + 3) >> 2) + VOFF - yfx + 8)%uint63; mkLine 0%uint63 (VOFF + 16)%uint63] in
    let hi0 := if dl then [] else [mkLine (2 * Q1)%uint63 ((Wp >> 1) + VOFF - ((y + elast ch) << 28) - 8)%uint63] in
    match pulls true e_ Wq r' yfx (elo ch) (lo0 ++ elo b), pulls false e_ Wq r' yfx (ehi ch) (hi0 ++ ehi b) with
    | Some lo, Some hi =>
      let vm := maxv (elo ch) (maxv (ehi ch) 0%uint63) in
      let gneed := (ONE * (y + 64) + vm + r' + eW2 ch)%uint63 in
      let Gm := max_ (max_ (eGm b) gneed) ((eGm ch >> 2) + 2)%uint63 in
      let dlast1 := (y + edlast ch)%uint63 in
      if (gneed <? 2305843009213693952)%uint63 && (Gm <? 2305843009213693952)%uint63 && (dlast1 <? 2147483648)%uint63
         && (negb (edet ch) || negb (edet b) || (edres b =? edres ch)%uint63) then
        Some (mkEnt (ec b) ra rb (ez b) (ed2 b) Wp
                (max_ (eW1 b) (4 * eW1 ch)%uint63) (min_ (eW2 b) (4 * eW2 ch - 64)%uint63) lo hi
                Y' (y + elast ch)%uint63 (edet b || edet ch)
                (if edet ch then max_ (edlast b) dlast1 else edlast b) (if edet ch then edres ch else edres b) Gm)
      else None
    | _, _ => None
    end
  else None.

(** Guards of a pair of letters *)
Lemma guards_pairUV (a b g S y yt ylast : Z)
  (HS : a + b = S) (Hg : 1 <= g) (Gn : PP * (y + 64) <= g) (G16 : 16 * g <= PP * b)
  (Hy : y <= yt <= ylast) (Hy0 : 0 <= y)
  (Hl : 32 * g <= PP * (2 * S - 4 * (b + g * ylast)))
  (L0 : 32 * g <= PP * (4 * (b + g * y) - S))
  (at_ := a - (g - 1) * yt) (bt := b + g * yt) :
  5 <= bt /\ bt + 1 <= at_ /\ 4 * bt > (at_ + bt) + 30.
Proof.
  subst at_ bt.
  assert (M1 : g * yt <= g * ylast) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M2 : g * y <= g * yt) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M0 : 0 <= g * y) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B1 : 1024 <= b) by lia.
  assert (C1 : 32 <= 2 * S - 4 * (b + g * ylast)) by lia.
  assert (C2 : 32 * (y + 64) <= 4 * (b + g * y) - S) by lia.
  assert (Y1 : yt - y <= g * (yt - y)).
  { replace (yt - y) with (1 * (yt - y)) at 1 by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  replace ((a - (g - 1) * yt)) with (a - g * yt + yt) by ring.
  lia.
Qed.
Lemma guards_pairDD (a b g S y yt : Z)
  (HS : a + b = S) (Hg : 1 <= g) (Gn : PP * (y + 64) <= g)
  (Hy : y <= yt) (Hy0 : 0 <= y)
  (L0 : 32 * g <= PP * (4 * (b + g * y) - 3 * S)) (HS0 : 0 <= S)
  (at_ := a - (g - 1) * yt) (bt := b + g * yt) :
  at_ + 3 < bt /\ (2 * at_ + 6) + 3 < bt - at_ - 3.
Proof.
  subst at_ bt.
  assert (M2 : g * y <= g * yt) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (C2 : 32 * (y + 64) <= 4 * (b + g * y) - 3 * S) by lia.
  assert (Y1 : yt - y <= g * (yt - y)).
  { replace (yt - y) with (1 * (yt - y)) at 1 by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  replace ((a - (g - 1) * yt)) with (a - g * yt + yt) by ring.
  lia.
Qed.
