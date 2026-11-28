(** The exact part of the checker for [halts]: nodes high in the tree, stops there, and applying block lemmas. All values exact. *)
From Coq Require Import ZArith Lia Uint63 List Bool PArray.
Import ListNotations.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Map Num Walk.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Ints HLines HCore HAbs HBand.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Record Lv := mkLv { la : W; lb : W; lg : W; lbase : W; lthr : W; lc : W }.

Definition lv_fits (L : Lv) : bool := fits (la L) && fits (lb L) && fits (lg L) && fits (lbase L) && fits (lthr L) && fits (lc L).

Definition lv_ok (a0 : Z) (L : Lv) : Prop :=
  lv_fits L = true /\ 1 <= val (lg L) /\ 0 <= val (lthr L) /\ val (la L) + val (lb L) = val (lbase L) + val (lc L) /\
  forall y, 0 <= y -> y mod 4 = 0 -> val (lthr L) <= val (la L) - (val (lg L) - 1) * y ->
    Rch a0 (val (lbase L) + y) (val (la L) - (val (lg L) - 1) * y) (val (lb L) + val (lg L) * y).

Ltac fits_all :=
  repeat match goal with
  | H : fits ?x = true |- _ => apply fits_spec in H
  end.

Lemma lv_bounds L : lv_fits L = true ->
  -P118 <= val (la L) < P118 /\ -P118 <= val (lb L) < P118 /\ -P118 <= val (lg L) < P118 /\ -P118 <= val (lbase L) < P118 /\
  -P118 <= val (lthr L) < P118 /\ -P118 <= val (lc L) < P118.
Proof.
  unfold lv_fits. intros H. repeat (apply andb_prop in H; destruct H as [H ?]). fits_all. lia.
Qed.

(** Value of a level at a start B, if the level is still good there. *)
Definition eval (L : Lv) (B : W) : option (W * W) :=
  let y := sub B (lbase L) in
  match mul_nn (sub (lg L) (wc 1)) y, mul_nn (lg L) y with
  | Some p, Some q =>
    let a := sub (la L) p in let b := add (lb L) q in
    if fits p && fits q && fits a && fits b && leb (lthr L) a then Some (a, b) else None
  | _, _ => None
  end.

Lemma eval_spec L B a b : lv_fits L = true -> 1 <= val (lg L) -> fits B = true -> eval L B = Some (a, b) ->
  fits a = true /\ fits b = true /\ val a = val (la L) - (val (lg L) - 1) * (val B - val (lbase L)) /\
  val b = val (lb L) + val (lg L) * (val B - val (lbase L)) /\ val (lthr L) <= val a.
Proof.
  intros HL Hg HB H. unfold eval in H. cbv zeta in H. destruct (lv_bounds L HL) as (B1 & B2 & B3 & B4 & B5 & B6).
  apply fits_spec in HB as HB'.
  destruct (mul_nn (sub (lg L) (wc 1)) (sub B (lbase L))) as [p|] eqn:M1; [|discriminate].
  destruct (mul_nn (lg L) (sub B (lbase L))) as [q|] eqn:M2; [|discriminate].
  destruct (fits p && fits q && fits (sub (la L) p) && fits (add (lb L) q) && leb (lthr L) (sub (la L) p)) eqn:C; [|discriminate].
  injection H as <- <-. apply andb_prop in C. destruct C as [C C5]. apply andb_prop in C. destruct C as [C C4]. apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
  destruct (mul_nn_spec _ _ _ M1) as [E1 _]. destruct (mul_nn_spec _ _ _ M2) as [E2 _].
  apply fits_spec in C1, C2. apply leb_spec_W in C5.
  assert (Vy : val (sub B (lbase L)) = val B - val (lbase L)) by (apply val_sub; lia).
  assert (Vg : val (sub (lg L) (wc 1)) = val (lg L) - 1) by (rewrite val_sub by (rewrite val_wc; change (phi 1%uint63) with 1; lia); rewrite val_wc; reflexivity).
  rewrite Vy in E1, E2. rewrite Vg in E1.
  assert (Va : val (sub (la L) p) = val (la L) - val p) by (apply val_sub; lia).
  assert (Vb : val (add (lb L) q) = val (lb L) + val q) by (apply val_add; lia).
  split; [exact C3|]. split; [exact C4|]. split; [|split].
  - rewrite Va, E1. reflexivity.
  - rewrite Vb, E2. reflexivity.
  - exact C5.
Qed.

(** ** Letters at a level *)
Definition childD (L : Lv) (a b B : W) : Lv :=
  mkLv (add (add a a) (wc 6)) (sub (sub b a) (wc 3)) (sub (add (lg L) (lg L)) (wc 1)) B
       (if eqb (lg L) (wc 1) then wc 0 else add (add (lthr L) (lthr L)) (wc 6)) (add (lc L) (wc 3)).
Definition childU (L : Lv) (a b B : W) : Lv :=
  mkLv (add (sub a b) (wc 11)) (sub (add b b) (wc 4)) (add (lg L) (lg L)) B (wc 12) (add (lc L) (wc 7)).
Definition childV (L : Lv) (a b B : W) : Lv :=
  mkLv (add (sub a b) (wc 19)) (sub (add b b) (wc 8)) (add (lg L) (lg L)) B (wc 20) (add (lc L) (wc 11)).

(** Exact small steps, in clean contexts. *)
Lemma val_add_c x k : fits x = true -> phi k < 1099511627776 -> val (add x (wc k)) = val x + phi k.
Proof. intros F K. apply fits_spec in F. pose proof (phi_bd63 k). rewrite val_add; rewrite val_wc; lia. Qed.
Lemma val_sub_c x k : fits x = true -> phi k < 1099511627776 -> val (sub x (wc k)) = val x - phi k.
Proof. intros F K. apply fits_spec in F. pose proof (phi_bd63 k). rewrite val_sub; rewrite val_wc; lia. Qed.
Lemma val_add2 x y : fits x = true -> fits y = true -> val (add x y) = val x + val y.
Proof. intros F G. apply fits_spec in F, G. apply val_add. lia. Qed.
Lemma val_sub2 x y : fits x = true -> fits y = true -> val (sub x y) = val x - val y.
Proof. intros F G. apply fits_spec in F, G. apply val_sub. lia. Qed.
Lemma val_dbl_add a k : fits a = true -> phi k < 1099511627776 -> val (add (add a a) (wc k)) = 2 * val a + phi k.
Proof.
  intros F K. pose proof (val_add2 a a F F) as E. apply fits_spec in F. pose proof (phi_bd63 k).
  rewrite val_add; rewrite ?val_wc, ?E; lia.
Qed.
Lemma val_dbl_sub a k : fits a = true -> phi k < 1099511627776 -> val (sub (add a a) (wc k)) = 2 * val a - phi k.
Proof.
  intros F K. pose proof (val_add2 a a F F) as E. apply fits_spec in F. pose proof (phi_bd63 k).
  rewrite val_sub; rewrite ?val_wc, ?E; lia.
Qed.
Lemma val_sub_sub_c x y k : fits x = true -> fits y = true -> phi k < 1099511627776 -> val (sub (sub x y) (wc k)) = val x - val y - phi k.
Proof.
  intros F G K. pose proof (val_sub2 x y F G) as E. apply fits_spec in F, G. pose proof (phi_bd63 k).
  rewrite val_sub; rewrite ?val_wc, ?E; lia.
Qed.
Lemma val_sub_add_c x y k : fits x = true -> fits y = true -> phi k < 1099511627776 -> val (add (sub x y) (wc k)) = val x - val y + phi k.
Proof.
  intros F G K. pose proof (val_sub2 x y F G) as E. apply fits_spec in F, G. pose proof (phi_bd63 k).
  rewrite val_add; rewrite ?val_wc, ?E; lia.
Qed.
Lemma mod0_ex x : x mod 4 = 0 -> exists k, x = 4 * k.
Proof. intros H. exists (x / 4). Z.div_mod_to_equations. lia. Qed.
Lemma ex_mod0 k : (4 * k) mod 4 = 0.
Proof. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.
Lemma low2_mod (x : W) : phi (low2 x) = val x mod 4.
Proof. apply phi_low2. Qed.

Lemma Rch_at a0 L B a b : lv_ok a0 L -> fits B = true -> val (lbase L) <= val B -> (val B - val (lbase L)) mod 4 = 0 -> eval L B = Some (a, b) ->
  Rch a0 (val B) (val a) (val b).
Proof.
  intros [HF [Hg [Ht [Hs HR]]]] HB Hl Hm He. destruct (eval_spec L B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  rewrite Va, Vb. replace (val B) with (val (lbase L) + (val B - val (lbase L))) at 1 by ring.
  apply HR; [lia|exact Hm|]. rewrite <- Va. exact Vt.
Qed.

(** The common shape of a child. *)
Lemma lv_at a0 L B a b y : lv_ok a0 L -> fits B = true -> val (lbase L) <= val B -> (val B - val (lbase L)) mod 4 = 0 -> eval L B = Some (a, b) ->
  0 <= y -> y mod 4 = 0 -> val (lthr L) <= val a - (val (lg L) - 1) * y ->
  Rch a0 (val B + y) (val a - (val (lg L) - 1) * y) (val b + val (lg L) * y).
Proof.
  intros [HF [Hg [Ht [Hs HR]]]] HB Hl Hm He Y0 Hmy Hth. destruct (eval_spec L B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  destruct (mod0_ex _ Hm) as [k Ek]. destruct (mod0_ex _ Hmy) as [j Ej]. clear Hm Hmy.
  assert (Eb : val B = val (lbase L) + 4 * k) by lia.
  pose proof (HR (4 * k + 4 * j) ltac:(lia)) as R.
  replace (4 * k + 4 * j) with (4 * (k + j)) in R by ring. specialize (R (ex_mod0 _)).
  rewrite Va in *. rewrite Vb. rewrite Ek in *. subst y.
  replace (val (la L) - (val (lg L) - 1) * (4 * k) - (val (lg L) - 1) * (4 * j)) with (val (la L) - (val (lg L) - 1) * (4 * (k + j))) in * by ring.
  specialize (R Hth).
  replace (val B + 4 * j) with (val (lbase L) + 4 * (k + j)) by lia.
  replace (val (lb L) + val (lg L) * (4 * k) + val (lg L) * (4 * j)) with (val (lb L) + val (lg L) * (4 * (k + j))) by ring.
  exact R.
Qed.

Lemma lvD a0 L B a b : lv_ok a0 L -> fits B = true -> val (lbase L) <= val B -> (val B - val (lbase L)) mod 4 = 0 -> eval L B = Some (a, b) ->
  val a + 3 < val b -> lv_fits (childD L a b B) = true -> lv_ok a0 (childD L a b B).
Proof.
  intros HL HB Hl Hm He Hlt Hf. pose proof HL as [HF [Hg [Ht [Hs HR]]]].
  destruct (eval_spec L B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  destruct (lv_bounds L HF) as (B1 & B2 & B3 & B4 & B5 & B6).
  unfold lv_fits in HF. apply andb_prop in HF. destruct HF as [HF Fc]. apply andb_prop in HF. destruct HF as [HF Fth]. apply andb_prop in HF. destruct HF as [HF Fbs]. apply andb_prop in HF. destruct HF as [HF Fg]. apply andb_prop in HF. destruct HF as [Fla Flb].
  assert (V1 : val (add (add a a) (wc 6)) = 2 * val a + 6) by (rewrite val_dbl_add by (exact Fa || (vm_compute; reflexivity)); reflexivity).
  assert (V2 : val (sub (sub b a) (wc 3)) = val b - val a - 3) by (rewrite val_sub_sub_c by (exact Fa || exact Fb || (vm_compute; reflexivity)); reflexivity).
  assert (V3 : val (sub (add (lg L) (lg L)) (wc 1)) = 2 * val (lg L) - 1) by (rewrite val_dbl_sub by (exact Fg || (vm_compute; reflexivity)); reflexivity).
  assert (V4 : val (add (lc L) (wc 3)) = val (lc L) + 3) by (rewrite val_add_c by (exact Fc || (vm_compute; reflexivity)); reflexivity).
  assert (V5 : (eqb (lg L) (wc 1) = true /\ val (lg L) = 1 /\ val (if eqb (lg L) (wc 1) then wc 0 else add (add (lthr L) (lthr L)) (wc 6)) = 0) \/
                (val (if eqb (lg L) (wc 1) then wc 0 else add (add (lthr L) (lthr L)) (wc 6)) = 2 * val (lthr L) + 6)).
  { destruct (eqb (lg L) (wc 1)) eqn:Eg.
    - left. split; [reflexivity|]. apply eqb_spec_W in Eg. rewrite val_wc in Eg. split; [exact Eg|reflexivity].
    - right. rewrite val_dbl_add by (exact Fth || (vm_compute; reflexivity)). reflexivity. }
  split; [exact Hf|]. unfold childD; cbn [la lb lg lbase lthr lc]. rewrite V1, V2, V3, V4.
  split; [|split; [|split]].
  - lia.
  - destruct V5 as [(_ & _ & X)|X]; rewrite X; lia.
  - rewrite Va, Vb. replace (2 * (val (la L) - (val (lg L) - 1) * (val B - val (lbase L))) + 6 + (val (lb L) + val (lg L) * (val B - val (lbase L)) - (val (la L) - (val (lg L) - 1) * (val B - val (lbase L))) - 3))
      with (val (la L) + val (lb L) + (val B - val (lbase L)) + 3) by ring. rewrite Hs. lia.
  - intros y Hy Hmy Hth.
    assert (Tr : val (lthr L) <= val a - (val (lg L) - 1) * y).
    { destruct V5 as [(_ & E1 & X)|X].
      - rewrite E1. replace (val a - (1 - 1) * y) with (val a) by ring. exact Vt.
      - rewrite X in Hth. lia. }
    pose proof (lv_at a0 L B a b y HL HB Hl Hm He Hy Hmy Tr) as R.
    eapply Rch_trans; [exact R|].
    replace (2 * val a + 6 - (2 * val (lg L) - 1 - 1) * y) with (2 * (val a - (val (lg L) - 1) * y) + 6) by ring.
    replace (val b - val a - 3 + (2 * val (lg L) - 1) * y) with (val b + val (lg L) * y - (val a - (val (lg L) - 1) * y) - 3) by ring.
    apply letterD.
    assert (0 <= (2 * val (lg L) - 1) * y) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

Lemma lvUV a0 L B a b (isu : bool) : lv_ok a0 L -> fits B = true -> val (lbase L) <= val B -> (val B - val (lbase L)) mod 4 = 0 -> eval L B = Some (a, b) ->
  val b mod 2 = 1 -> 5 <= val b -> val b + 1 <= val a -> (val (lg L) = 1 \/ val (lthr L) <= val b + 1) ->
  (isu = true -> (val a - val b + 5) mod 4 = 2) -> (isu = false -> (val a - val b + 5) mod 4 <> 2) ->
  lv_fits (if isu then childU L a b B else childV L a b B) = true -> lv_ok a0 (if isu then childU L a b B else childV L a b B).
Proof.
  intros HL HB Hl Hm He Odd B5 Bab Thr Hu Hv Hf. pose proof HL as [HF [Hg [Ht [Hs HR]]]].
  destruct (eval_spec L B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  unfold lv_fits in HF. apply andb_prop in HF. destruct HF as [HF Fc]. apply andb_prop in HF. destruct HF as [HF Fth]. apply andb_prop in HF. destruct HF as [HF Fbs]. apply andb_prop in HF. destruct HF as [HF Fg]. apply andb_prop in HF. destruct HF as [Fla Flb].
  assert (Sum_ : val a + val b = val B + val (lc L)).
  { rewrite Va, Vb. replace (val (la L) - (val (lg L) - 1) * (val B - val (lbase L)) + (val (lb L) + val (lg L) * (val B - val (lbase L))))
      with (val (la L) + val (lb L) + (val B - val (lbase L))) by ring. rewrite Hs. ring. }
  assert (Vg : val (add (lg L) (lg L)) = 2 * val (lg L)) by (rewrite val_add2 by exact Fg; ring).
  clear HR.
  destruct isu; [specialize (Hu eq_refl)|specialize (Hv eq_refl)]; split; try exact Hf; unfold childU, childV; cbn [la lb lg lbase lthr lc];
    rewrite Vg.
  - assert (V1 : val (add (sub a b) (wc 11)) = val a - val b + 11) by (rewrite val_sub_add_c by (exact Fa || exact Fb || (vm_compute; reflexivity)); reflexivity).
    assert (V2 : val (sub (add b b) (wc 4)) = 2 * val b - 4) by (rewrite val_dbl_sub by (exact Fb || (vm_compute; reflexivity)); reflexivity).
    assert (V4 : val (add (lc L) (wc 7)) = val (lc L) + 7) by (rewrite val_add_c by (exact Fc || (vm_compute; reflexivity)); reflexivity).
    rewrite V1, V2, V4. change (val (wc 12)) with 12.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros y Hy Hmy Hth. destruct (mod0_ex _ Hmy) as [j Ej].
    assert (Gy : 0 <= val (lg L) * y) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Tr : val (lthr L) <= val a - (val (lg L) - 1) * y).
    { destruct Thr as [E1|E1].
      - rewrite E1. replace (val a - (1 - 1) * y) with (val a) by ring. exact Vt.
      - lia. }
    pose proof (lv_at a0 L B a b y HL HB Hl Hm He Hy Hmy Tr) as R.
    eapply Rch_trans; [exact R|].
    replace (val a - val b + 11 - (2 * val (lg L) - 1) * y) with (val a - (val (lg L) - 1) * y - (val b + val (lg L) * y) + 11) by ring.
    replace (2 * val b - 4 + 2 * val (lg L) * y) with (2 * (val b + val (lg L) * y) - 4) by ring.
    apply letterU; [| |lia|lia].
    + rewrite Ej. replace (val b + val (lg L) * (4 * j)) with (val b + (2 * (val (lg L) * j)) * 2) by ring. rewrite Z.mod_add by lia. exact Odd.
    + rewrite Ej. replace (val a - (val (lg L) - 1) * (4 * j) - (val b + val (lg L) * (4 * j)) + 5) with (val a - val b + 5 + (- (2 * val (lg L) - 1) * j) * 4) by ring.
      rewrite Z.mod_add by lia. exact Hu.
  - assert (V1 : val (add (sub a b) (wc 19)) = val a - val b + 19) by (rewrite val_sub_add_c by (exact Fa || exact Fb || (vm_compute; reflexivity)); reflexivity).
    assert (V2 : val (sub (add b b) (wc 8)) = 2 * val b - 8) by (rewrite val_dbl_sub by (exact Fb || (vm_compute; reflexivity)); reflexivity).
    assert (V4 : val (add (lc L) (wc 11)) = val (lc L) + 11) by (rewrite val_add_c by (exact Fc || (vm_compute; reflexivity)); reflexivity).
    rewrite V1, V2, V4. change (val (wc 20)) with 20.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros y Hy Hmy Hth. destruct (mod0_ex _ Hmy) as [j Ej].
    assert (Gy : 0 <= val (lg L) * y) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Tr : val (lthr L) <= val a - (val (lg L) - 1) * y).
    { destruct Thr as [E1|E1].
      - rewrite E1. replace (val a - (1 - 1) * y) with (val a) by ring. exact Vt.
      - lia. }
    pose proof (lv_at a0 L B a b y HL HB Hl Hm He Hy Hmy Tr) as R.
    eapply Rch_trans; [exact R|].
    replace (val a - val b + 19 - (2 * val (lg L) - 1) * y) with (val a - (val (lg L) - 1) * y - (val b + val (lg L) * y) + 19) by ring.
    replace (2 * val b - 8 + 2 * val (lg L) * y) with (2 * (val b + val (lg L) * y) - 8) by ring.
    apply letterV; [| |lia|lia].
    + rewrite Ej. replace (val b + val (lg L) * (4 * j)) with (val b + (2 * (val (lg L) * j)) * 2) by ring. rewrite Z.mod_add by lia. exact Odd.
    + rewrite Ej. replace (val a - (val (lg L) - 1) * (4 * j) - (val b + val (lg L) * (4 * j)) + 5) with (val a - val b + 5 + (- (2 * val (lg L) - 1) * j) * 4) by ring.
      rewrite Z.mod_add by lia. exact Hv.
Qed.

(** ** Words that end in a reset *)
Record Term := mkT { tL : Lv; tna : int; tok : bool }.
Definition tD (t : Term) : W := if (tna t =? 6)%uint63 then add (lc (tL t)) (wc 7) else sub (lc (tL t)) (wc 2).
Definition term_of (L : Lv) : Term :=
  mkT L (if (low2 (sub (la L) (lb L)) =? 2)%uint63 then 6%uint63 else 22%uint63) true.
Definition noterm : Term := mkT (mkLv (wc 0) (wc 0) (wc 1) (wc 0) (wc 0) (wc 0)) 0%uint63 false.

Definition term_sem (z : Z) (t : Term) : Prop :=
  tok t = true -> lv_ok z (tL t) /\ (phi (tna t) = 6 \/ phi (tna t) = 22) /\ fits (tD t) = true /\
    forall y, 0 <= y -> y mod 4 = 0 -> val (lthr (tL t)) <= val (la (tL t)) - (val (lg (tL t)) - 1) * y ->
      val (lb (tL t)) + val (lg (tL t)) * y < val (la (tL t)) - (val (lg (tL t)) - 1) * y + 3 ->
      Rch z (val (lbase (tL t)) + y) (phi (tna t)) (val (lbase (tL t)) + y + val (tD t)).

Lemma term_of_ok z L : lv_ok z L -> val (lb L) mod 2 = 0 -> fits (add (lc L) (wc 7)) = true -> fits (sub (lc L) (wc 2)) = true -> term_sem z (term_of L).
Proof.
  intros HL Ev F7 F2 _. pose proof HL as [HF [Hg [Ht [Hs HR]]]].
  pose proof (lv_bounds L HF) as (B1 & B2 & B3 & B4 & B5 & B6).
  unfold lv_fits in HF. apply andb_prop in HF. destruct HF as [HF Fc]. apply andb_prop in HF. destruct HF as [HF Fth]. apply andb_prop in HF. destruct HF as [HF Fbs]. apply andb_prop in HF. destruct HF as [HF Fg]. apply andb_prop in HF. destruct HF as [Fla Flb].
  assert (Vs : val (sub (la L) (lb L)) = val (la L) - val (lb L)) by (apply val_sub2; assumption).
  unfold term_of, tD; cbn [tL tna tok]. split; [exact HL|].
  destruct (low2 (sub (la L) (lb L)) =? 2)%uint63 eqn:C.
  - split; [left; reflexivity|]. split; [exact F7|].
    change (6 =? 6)%uint63 with true. cbv iota. intros y Hy Hm Hth Hlt.
    rewrite val_add_c by (exact Fc || (vm_compute; reflexivity)). change (phi 7%uint63) with 7.
    apply eqb_true in C. rewrite low2_mod, Vs in C. change (phi 2%uint63) with 2 in C.
    pose proof (HR y Hy Hm Hth) as R. eapply Rch_trans; [exact R|].
    destruct (mod0_ex _ Hm) as [j Ej]. subst y.
    replace (val (lbase L) + 4 * j + (val (lc L) + 7)) with ((val (la L) - (val (lg L) - 1) * (4 * j)) + (val (lb L) + val (lg L) * (4 * j)) + 7) by lia.
    change (phi 6%uint63) with 6. apply letterW; [| exact Hlt |].
    + replace (val (lb L) + val (lg L) * (4 * j)) with (val (lb L) + (2 * (val (lg L) * j)) * 2) by ring. rewrite Z.mod_add by lia. exact Ev.
    + replace (val (la L) - (val (lg L) - 1) * (4 * j) - (val (lb L) + val (lg L) * (4 * j))) with (val (la L) - val (lb L) + (- (2 * val (lg L) - 1) * j) * 4) by ring.
      rewrite Z.mod_add by lia. exact C.
  - split; [right; reflexivity|]. split; [exact F2|].
    change (22 =? 6)%uint63 with false. cbv iota. intros y Hy Hm Hth Hlt.
    rewrite val_sub_c by (exact Fc || (vm_compute; reflexivity)). change (phi 2%uint63) with 2.
    assert (C' : (val (la L) - val (lb L)) mod 4 <> 2).
    { intros X. rewrite <- Vs, <- low2_mod in X. assert (Y : low2 (sub (la L) (lb L)) = 2%uint63) by (apply to_Z_inj; exact X). rewrite Y in C. discriminate. }
    pose proof (HR y Hy Hm Hth) as R. eapply Rch_trans; [exact R|].
    destruct (mod0_ex _ Hm) as [j Ej]. subst y.
    replace (val (lbase L) + 4 * j + (val (lc L) - 2)) with ((val (la L) - (val (lg L) - 1) * (4 * j)) + (val (lb L) + val (lg L) * (4 * j)) - 2) by lia.
    change (phi 22%uint63) with 22. apply letterX; [| exact Hlt |].
    + replace (val (lb L) + val (lg L) * (4 * j)) with (val (lb L) + (2 * (val (lg L) * j)) * 2) by ring. rewrite Z.mod_add by lia. exact Ev.
    + replace (val (la L) - (val (lg L) - 1) * (4 * j) - (val (lb L) + val (lg L) * (4 * j))) with (val (la L) - val (lb L) + (- (2 * val (lg L) - 1) * j) * 4) by ring.
      rewrite Z.mod_add by lia. exact C'.
Qed.

(** A level moved to its state at a later start. *)
Definition rebase (L : Lv) (a b B : W) : Lv := mkLv a b (lg L) B (lthr L) (lc L).
Lemma rebase_ok z L B a b : lv_ok z L -> fits B = true -> val (lbase L) <= val B -> (val B - val (lbase L)) mod 4 = 0 -> eval L B = Some (a, b) ->
  lv_ok z (rebase L a b B).
Proof.
  intros HL HB Hl Hm He. pose proof HL as [HF [Hg [Ht [Hs HR]]]].
  destruct (eval_spec L B a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  unfold lv_fits in HF. apply andb_prop in HF. destruct HF as [HF Fc]. apply andb_prop in HF. destruct HF as [HF Fth]. apply andb_prop in HF. destruct HF as [HF Fbs]. apply andb_prop in HF. destruct HF as [HF Fg]. apply andb_prop in HF. destruct HF as [Fla Flb].
  split; [unfold lv_fits, rebase; cbn [la lb lg lbase lthr lc]; rewrite Fa, Fb, Fg, HB, Fth, Fc; reflexivity|].
  unfold rebase; cbn [la lb lg lbase lthr lc]. split; [exact Hg|]. split; [exact Ht|]. split.
  - rewrite Va, Vb. replace (val (la L) - (val (lg L) - 1) * (val B - val (lbase L)) + (val (lb L) + val (lg L) * (val B - val (lbase L))))
      with (val (la L) + val (lb L) + (val B - val (lbase L))) by ring. rewrite Hs. ring.
  - intros y Hy Hm2 Hth. apply (lv_at z L B a b y HL HB Hl Hm He Hy Hm2 Hth).
Qed.

(** ** How many rounds: a suggestion, checked *)
Definition maxq (a b g thr D : W) : W :=
  let gap := sub (add a (wc 2)) b in let m := sub (add g g) (wc 1) in let h := sub g (wc 1) in
  match mul_nn m D with
  | None => wc 0
  | Some md =>
    let q0 := if ltb gap md then wc 0 else adiv gap md in
    match mul_nn md q0, mul_nn D q0 with
    | Some p, Some yq =>
      match mul_nn h yq with
      | Some hy =>
        if fits p && fits hy && fits q0 && fits yq && leb (wc 0) q0 && leb p gap && leb (add (lthr (mkLv a b g a thr a)) hy) a then q0 else wc 0
      | None => wc 0
      end
    | _, _ => wc 0
    end
  end.

Lemma maxq_spec a b g thr D t : fits a = true -> fits b = true -> fits g = true -> fits thr = true -> 1 <= val g -> 0 <= val D ->
  val thr <= val a -> val b < val a + 3 -> 0 <= t <= val (maxq a b g thr D) ->
  val thr <= val a - (val g - 1) * (t * val D) /\ val b + val g * (t * val D) < val a - (val g - 1) * (t * val D) + 3.
Proof.
  intros Fa Fb Fg Ft Hg HD Vt Vl Ht. unfold maxq in Ht. cbv zeta in Ht. cbn [lthr] in Ht.
  assert (Zero : t = 0 -> val thr <= val a - (val g - 1) * (t * val D) /\ val b + val g * (t * val D) < val a - (val g - 1) * (t * val D) + 3).
  { intros ->. rewrite Z.mul_0_l, !Z.mul_0_r. lia. }
  assert (W0 : val (wc 0) = 0) by reflexivity.
  destruct (mul_nn (sub (add g g) (wc 1)) D) as [md|] eqn:M1; [|apply Zero; rewrite W0 in Ht; lia].
  set (q0 := if ltb (sub (add a (wc 2)) b) md then wc 0 else adiv (sub (add a (wc 2)) b) md) in *.
  destruct (mul_nn md q0) as [p|] eqn:M2; [|apply Zero; rewrite W0 in Ht; lia].
  destruct (mul_nn D q0) as [yq|] eqn:M3; [|apply Zero; rewrite W0 in Ht; lia].
  destruct (mul_nn (sub g (wc 1)) yq) as [hy|] eqn:M4; [|apply Zero; rewrite W0 in Ht; lia].
  destruct (fits p && fits hy && fits q0 && fits yq && leb (wc 0) q0 && leb p (sub (add a (wc 2)) b) && leb (add thr hy) a) eqn:C; [|apply Zero; rewrite W0 in Ht; lia].
  apply andb_prop in C. destruct C as [C C7]. apply andb_prop in C. destruct C as [C C6]. apply andb_prop in C. destruct C as [C C5]. apply andb_prop in C. destruct C as [C C4].
  apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
  destruct (mul_nn_spec _ _ _ M1) as [E1 _]. destruct (mul_nn_spec _ _ _ M2) as [E2 _]. destruct (mul_nn_spec _ _ _ M3) as [E3 _]. destruct (mul_nn_spec _ _ _ M4) as [E4 _].
  apply leb_spec_W in C5, C6, C7. rewrite W0 in C5.
  rewrite val_dbl_sub in E1 by (exact Fg || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in E1.
  rewrite val_sub_c in E4 by (exact Fg || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in E4.
  assert (Vgap : val (sub (add a (wc 2)) b) = val a + 2 - val b).
  { assert (X : val (add a (wc 2)) = val a + 2) by (rewrite val_add_c by (exact Fa || (vm_compute; reflexivity)); reflexivity).
    rewrite val_sub; rewrite ?X; apply fits_spec in Fa, Fb; lia. }
  rewrite Vgap in C6.
  assert (Vth : val (add thr hy) = val thr + val hy) by (apply val_add2; assumption).
  rewrite Vth in C7.
  assert (M5 : t * val D <= val q0 * val D) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (M6 : (val g - 1) * (t * val D) <= (val g - 1) * (val D * val q0)).
  { apply Z.mul_le_mono_nonneg_l; [lia|]. rewrite Z.mul_comm with (n := val D). exact M5. }
  assert (M7 : (2 * val g - 1) * (t * val D) <= (2 * val g - 1) * (val D * val q0)).
  { apply Z.mul_le_mono_nonneg_l; [lia|]. rewrite Z.mul_comm with (n := val D). exact M5. }
  rewrite E1 in E2. rewrite E3 in E4.
  assert (E2' : val p = (2 * val g - 1) * (val D * val q0)) by (rewrite E2; ring).
  split; [lia|].
  assert (X : val a - (val g - 1) * (t * val D) + 3 - (val b + val g * (t * val D)) = val a + 3 - val b - (2 * val g - 1) * (t * val D)) by ring.
  lia.
Qed.

(** ** The state of a run *)
Record St := mkSt { sz : int; sB : W; sstat : int; sha : W; sd6 : Term; sd22 : Term; sm : Mem; sY : W }.
Definition set_stat (s : St) (k : int) : St := mkSt (sz s) (sB s) k (sha s) (sd6 s) (sd22 s) (sm s) (sY s).
Definition set_B (s : St) (B : W) (k : int) : St := mkSt (sz s) B k (sha s) (sd6 s) (sd22 s) (sm s) (sY s).
Definition set_hop (s : St) (z : int) (B : W) (k : int) : St := mkSt z B k (sha s) (sd6 s) (sd22 s) (sm s) (sY s).
Definition set_mem (s : St) (m : Mem) : St := mkSt (sz s) (sB s) (sstat s) (sha s) (sd6 s) (sd22 s) m (sY s).

Definition st_ok (A0 B0 : Z) (s : St) : Prop :=
  Rch A0 B0 (phi (sz s)) (val (sB s)) /\ fits (sB s) = true /\ (phi (sz s) = 6 \/ phi (sz s) = 22) /\ mem_ok (sm s) /\
  term_sem 6 (sd6 s) /\ term_sem 22 (sd22 s) /\ (sstat s = 3%uint63 -> Rch A0 B0 (val (sha s)) (val (sha s) + 3)).

(** The number of rounds that fit before the end Y: between 1 and q+1, or none. *)
Definition pick (B Y D q : W) : option (W * W) :=
  let T := add q (wc 1) in
  match mul_nn D T with
  | Some y =>
    if fits T && fits y && fits (add B y) && leb (add B y) Y then Some (T, y)
    else
      let T2 := adiv (sub Y B) D in
      match mul_nn D T2 with
      | Some y2 => if fits T2 && fits y2 && fits (add B y2) && leb (wc 1) T2 && leb T2 T && leb (add B y2) Y then Some (T2, y2) else None
      | None => None
      end
  | None => None
  end.
Lemma pick_spec B Y D q T y : fits q = true -> 0 <= val q -> pick B Y D q = Some (T, y) ->
  fits T = true /\ fits y = true /\ fits (add B y) = true /\ val y = val D * val T /\ 1 <= val T <= val q + 1.
Proof.
  intros Fq Hq H. unfold pick in H. cbv zeta in H.
  assert (VT : val (add q (wc 1)) = val q + 1) by (rewrite val_add_c by (exact Fq || (vm_compute; reflexivity)); reflexivity).
  destruct (mul_nn D (add q (wc 1))) as [y1|] eqn:M; [|discriminate].
  destruct (mul_nn_spec _ _ _ M) as [E _].
  destruct (fits (add q (wc 1)) && fits y1 && fits (add B y1) && leb (add B y1) Y) eqn:C.
  - injection H as <- <-. repeat (apply andb_prop in C; destruct C as [C ?]).
    split; [exact C|]. split; [assumption|]. split; [assumption|]. split; [exact E|lia].
  - destruct (mul_nn D (adiv (sub Y B) D)) as [y2|] eqn:M2; [|discriminate].
    destruct (mul_nn_spec _ _ _ M2) as [E2 _].
    destruct (fits (adiv (sub Y B) D) && fits y2 && fits (add B y2) && leb (wc 1) (adiv (sub Y B) D) && leb (adiv (sub Y B) D) (add q (wc 1)) && leb (add B y2) Y) eqn:C2; [|discriminate].
    injection H as <- <-. repeat (apply andb_prop in C2; destruct C2 as [C2 ?]).
    match goal with H1 : leb (wc 1) _ = true |- _ => apply leb_spec_W in H1; rewrite val_wc in H1; change (phi 1%uint63) with 1 in H1 end.
    match goal with H1 : leb _ (add q (wc 1)) = true |- _ => apply leb_spec_W in H1; rewrite VT in H1 end.
    split; [exact C2|]. split; [assumption|]. split; [assumption|]. split; [exact E2|lia].
Qed.

Lemma T_nat (T : Z) : 1 <= T -> Z.of_nat (Z.to_nat T) = T.
Proof. intros. apply Z2Nat.id. lia. Qed.

(** Direct rounds: the word returns to its own reset value. *)
Lemma direct_rounds z t T D :
  term_sem z t -> tok t = true -> phi (tna t) = z -> val (tD t) = D -> D mod 4 = 0 -> 1 <= T -> 0 <= D ->
  (forall k, 0 <= k < T -> val (lthr (tL t)) <= val (la (tL t)) - (val (lg (tL t)) - 1) * (k * D) /\
     val (lb (tL t)) + val (lg (tL t)) * (k * D) < val (la (tL t)) - (val (lg (tL t)) - 1) * (k * D) + 3) ->
  Rch z (val (lbase (tL t))) z (val (lbase (tL t)) + T * D).
Proof.
  intros Hs Ht Hz HD Hm HT Hd Hk.
  destruct (Hs Ht) as (_ & _ & _ & R).
  destruct (mod0_ex _ Hm) as [j Ej].
  rewrite <- (T_nat T HT). apply rounds_rch. intros k Hk'. rewrite Z2Nat.id in Hk' by lia.
  assert (Bk : 0 <= k * D) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M : (k * D) mod 4 = 0) by (rewrite Ej; replace (k * (4 * j)) with (4 * (k * j)) by ring; apply ex_mod0).
  destruct (Hk k Hk') as [H1 H2].
  pose proof (R (k * D) Bk M H1 H2) as X. rewrite Hz, HD in X.
  replace (val (lbase (tL t)) + (k + 1) * D) with (val (lbase (tL t)) + k * D + D) by ring. exact X.
Qed.

(** Rounds through a detour word. *)
Lemma det_rounds z z1 t d T D1 D2 yd :
  term_sem z t -> tok t = true -> phi (tna t) = z1 -> val (tD t) = D1 ->
  term_sem z1 d -> tok d = true -> phi (tna d) = z -> val (tD d) = D2 ->
  val (lbase (tL d)) + yd = val (lbase (tL t)) + D1 -> 0 <= yd -> yd mod 4 = 0 ->
  (D1 + D2) mod 4 = 0 -> 1 <= T -> 0 <= D1 + D2 ->
  (forall k, 0 <= k < T ->
     (val (lthr (tL t)) <= val (la (tL t)) - (val (lg (tL t)) - 1) * (k * (D1 + D2)) /\
       val (lb (tL t)) + val (lg (tL t)) * (k * (D1 + D2)) < val (la (tL t)) - (val (lg (tL t)) - 1) * (k * (D1 + D2)) + 3) /\
     (val (lthr (tL d)) <= val (la (tL d)) - (val (lg (tL d)) - 1) * (yd + k * (D1 + D2)) /\
       val (lb (tL d)) + val (lg (tL d)) * (yd + k * (D1 + D2)) < val (la (tL d)) - (val (lg (tL d)) - 1) * (yd + k * (D1 + D2)) + 3)) ->
  Rch z (val (lbase (tL t))) z (val (lbase (tL t)) + T * (D1 + D2)).
Proof.
  intros Hs Ht Hz HD Hs2 Ht2 Hz2 HD2 Eb Y0 Ym Hm HT Hd Hk.
  destruct (Hs Ht) as (_ & _ & _ & R). destruct (Hs2 Ht2) as (_ & _ & _ & R2).
  destruct (mod0_ex _ Hm) as [j Ej]. destruct (mod0_ex _ Ym) as [i Ei].
  rewrite <- (T_nat T HT). apply rounds_rch. intros k Hk'. rewrite Z2Nat.id in Hk' by lia.
  assert (Bk : 0 <= k * (D1 + D2)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M : (k * (D1 + D2)) mod 4 = 0) by (rewrite Ej; replace (k * (4 * j)) with (4 * (k * j)) by ring; apply ex_mod0).
  assert (M2 : (yd + k * (D1 + D2)) mod 4 = 0) by (rewrite Ej, Ei; replace (4 * i + k * (4 * j)) with (4 * (i + k * j)) by ring; apply ex_mod0).
  destruct (Hk k Hk') as [[H1 H2] [H3 H4]].
  pose proof (R (k * (D1 + D2)) Bk M H1 H2) as X. rewrite Hz, HD in X.
  pose proof (R2 (yd + k * (D1 + D2)) ltac:(lia) M2 H3 H4) as X2. rewrite Hz2, HD2 in X2.
  replace (val (lbase (tL d)) + (yd + k * (D1 + D2))) with (val (lbase (tL t)) + k * (D1 + D2) + D1) in X2 by lia.
  eapply Rch_trans; [exact X|].
  replace (val (lbase (tL t)) + (k + 1) * (D1 + D2)) with (val (lbase (tL t)) + k * (D1 + D2) + D1 + D2) by ring. exact X2.
Qed.

Lemma ltb_false_W x y : ltb x y = false -> val y <= val x.
Proof.
  intros H. destruct (Z.le_gt_cases (val y) (val x)) as [X|X]; [exact X|].
  assert (ltb x y = true) by (apply ltb_spec_W; lia). congruence.
Qed.
Lemma eqb_false_W x y : eqb x y = false -> val x <> val y.
Proof. intros H X. apply eqb_spec_W in X. congruence. Qed.

(** ** Whole words, for a detour *)
Definition root (z : int) (B : W) : Lv := mkLv (wc z) B (wc 1) B (wc 0) (wc z).
Lemma root_ok z B : fits B = true -> (phi z = 6 \/ phi z = 22) -> lv_ok (phi z) (root z B).
Proof.
  intros HB Hz. assert (Fz : fits (wc z) = true).
  { destruct Hz as [E|E]; assert (X : z = (if (z =? 6)%uint63 then 6%uint63 else 22%uint63)) by (apply to_Z_inj; destruct (z =? 6)%uint63 eqn:C; [apply Uint63.eqb_spec in C; rewrite C; reflexivity|]; rewrite E; try reflexivity; apply Uint63.eqb_false_spec in C; exfalso; apply C; apply to_Z_inj; rewrite E; reflexivity); rewrite X; destruct (z =? 6)%uint63; reflexivity. }
  unfold lv_ok, root, lv_fits; cbn [la lb lg lbase lthr lc]. rewrite Fz, HB. change (fits (wc 1)) with true. change (fits (wc 0)) with true.
  split; [reflexivity|]. change (val (wc 1)) with 1. change (val (wc 0)) with 0. rewrite val_wc.
  split; [lia|]. split; [lia|]. split; [lia|]. intros y _ _ _.
  replace (phi z - (1 - 1) * y) with (phi z) by ring. replace (val B + 1 * y) with (val B + y) by ring. apply Rch_refl.
Qed.

Fixpoint walk (f : nat) (L : Lv) : Term :=
  match f with
  | O => noterm
  | S f =>
    match eval L (lbase L) with
    | None => noterm
    | Some (a, b) =>
      if ltb (add a (wc 3)) b then
        let c := childD L a b (lbase L) in
        if lv_fits c then walk f c else noterm
      else if ltb b (wc 5) || negb (lv_fits (rebase L a b (lbase L))) || eqb (add a (wc 3)) b then noterm
      else if ((low2 b) land 1 =? 1)%uint63 then
        if eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg L) (wc 1) || leb (lthr L) (add b (wc 1))) then noterm
        else
          let isu := (low2 (add (sub a b) (wc 5)) =? 2)%uint63 in
          let c := if isu then childU L a b (lbase L) else childV L a b (lbase L) in
          if lv_fits c then walk f c else noterm
      else
        let L' := rebase L a b (lbase L) in
        if fits (add (lc L) (wc 7)) && fits (sub (lc L) (wc 2)) && (ltb b (add a (wc 3))) then term_of L' else noterm
    end
  end.

Lemma low2_odd (b : W) : ((low2 b) land 1 =? 1)%uint63 = true -> val b mod 2 = 1.
Proof.
  intros H. apply eqb_true in H. rewrite phi_land1, low2_mod in H. change (phi 1%uint63) with 1 in H.
  revert H. generalize (val b). clear b. intros z H. Z.div_mod_to_equations. lia.
Qed.
Lemma low2_even (b : W) : ((low2 b) land 1 =? 1)%uint63 = false -> val b mod 2 = 0.
Proof.
  intros H. rewrite <- not_true_iff_false in H.
  assert (A : phi ((low2 b) land 1)%uint63 <> 1).
  { intros X. apply H. rewrite Uint63.eqb_spec. apply to_Z_inj. exact X. }
  rewrite phi_land1, low2_mod in A. revert A. generalize (val b). clear b H. intros z A. Z.div_mod_to_equations. lia.
Qed.
Lemma low2_u (a b : W) : fits a = true -> fits b = true -> (low2 (add (sub a b) (wc 5)) =? 2)%uint63 = true -> (val a - val b + 5) mod 4 = 2.
Proof. intros Fa Fb H. apply eqb_true in H. rewrite low2_mod, val_sub_add_c in H by (exact Fa || exact Fb || (vm_compute; reflexivity)). exact H. Qed.
Lemma low2_v (a b : W) : fits a = true -> fits b = true -> (low2 (add (sub a b) (wc 5)) =? 2)%uint63 = false -> (val a - val b + 5) mod 4 <> 2.
Proof.
  intros Fa Fb H X. rewrite <- not_true_iff_false in H. apply H. rewrite Uint63.eqb_spec. apply to_Z_inj.
  rewrite low2_mod, val_sub_add_c by (exact Fa || exact Fb || (vm_compute; reflexivity)). exact X.
Qed.

Lemma walk_sound f z : forall L, lv_ok z L -> term_sem z (walk f L).
Proof.
  induction f as [|f IH]; intros L HL.
  { intros H. discriminate. }
  cbn [walk]. pose proof HL as [HF [Hg [Ht [Hs HR]]]].
  assert (HB : fits (lbase L) = true).
  { unfold lv_fits in HF. repeat (apply andb_prop in HF; destruct HF as [HF ?]). assumption. }
  destruct (eval L (lbase L)) as [[a b]|] eqn:He; [|intros H; discriminate].
  destruct (eval_spec L (lbase L) a b HF Hg HB He) as (Fa & Fb & Va & Vb & Vt).
  assert (M0 : (val (lbase L) - val (lbase L)) mod 4 = 0) by (rewrite Z.sub_diag; reflexivity).
  assert (V3 : val (add a (wc 3)) = val a + 3) by (rewrite val_add_c by (exact Fa || (vm_compute; reflexivity)); reflexivity).
  destruct (ltb (add a (wc 3)) b) eqn:C1.
  { destruct (lv_fits (childD L a b (lbase L))) eqn:Fc; [|intros H; discriminate].
    apply IH. apply (lvD z L (lbase L) a b HL HB ltac:(lia) M0 He); [|exact Fc]. apply ltb_spec_W in C1. lia. }
  destruct (ltb b (wc 5) || negb (lv_fits (rebase L a b (lbase L))) || eqb (add a (wc 3)) b) eqn:C2; [intros H; discriminate|].
  apply orb_false_iff in C2. destruct C2 as [C2 _]. apply orb_false_iff in C2. destruct C2 as [C2 C3].
  destruct ((low2 b) land 1 =? 1)%uint63 eqn:Od.
  - destruct (eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg L) (wc 1) || leb (lthr L) (add b (wc 1)))) eqn:C4; [intros H; discriminate|].
    apply orb_false_iff in C4. destruct C4 as [C4 C6]. apply orb_false_iff in C4. destruct C4 as [_ C5].
    apply negb_false_iff in C5, C6. apply leb_spec_W in C5. rewrite val_add_c in C5 by (exact Fb || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in C5.
    assert (B5 : 5 <= val b) by (pose proof (ltb_false_W _ _ C2) as X; rewrite val_wc in X; exact X).
    destruct (lv_fits (if (low2 (add (sub a b) (wc 5)) =? 2)%uint63 then childU L a b (lbase L) else childV L a b (lbase L))) eqn:Fc; [|intros H; discriminate].
    apply IH. apply (lvUV z L (lbase L) a b _ HL HB ltac:(lia) M0 He); try assumption.
    + apply low2_odd. exact Od.
    + apply orb_prop in C6. destruct C6 as [C6|C6].
      * left. apply eqb_spec_W in C6. rewrite C6. reflexivity.
      * right. apply leb_spec_W in C6. rewrite val_add_c in C6 by (exact Fb || (vm_compute; reflexivity)). exact C6.
    + apply low2_u; assumption.
    + apply low2_v; assumption.
  - destruct (fits (add (lc L) (wc 7)) && fits (sub (lc L) (wc 2)) && (ltb b (add a (wc 3)))) eqn:C4; [|intros H; discriminate].
    apply andb_prop in C4. destruct C4 as [C4 _]. apply andb_prop in C4. destruct C4 as [F7 F2].
    apply term_of_ok; [apply (rebase_ok z L (lbase L) a b HL HB ltac:(lia) M0 He)|apply low2_even; exact Od|exact F7|exact F2].
Qed.

(** ** A stop high in the tree *)
Definition det_of (s : St) (z : int) : Term := if (z =? 6)%uint63 then sd6 s else sd22 s.
Definition put_det (s : St) (z : int) (t : Term) : St :=
  if (z =? 6)%uint63 then mkSt (sz s) (sB s) (sstat s) (sha s) t (sd22 s) (sm s) (sY s)
  else mkSt (sz s) (sB s) (sstat s) (sha s) (sd6 s) t (sm s) (sY s).
Definition Wfuel : nat := Nat.pow 2 12.

Definition det_usable (t : Term) (B1 : W) : option (W * W) :=
  if tok t && leb (lbase (tL t)) B1 && (low2 (lbase (tL t)) =? low2 B1)%uint63 then
    match eval (tL t) B1 with
    | Some (a, b) => if ltb b (add a (wc 3)) then Some (a, b) else None
    | None => None
    end
  else None.

Definition get_det (s : St) (z : int) (B1 : W) : St * Term * option (W * W) :=
  let t := det_of s z in
  match det_usable t B1 with
  | Some ab => (s, t, Some ab)
  | None =>
    let t2 := walk Wfuel (root z B1) in
    let s2 := put_det s z t2 in
    (s2, t2, det_usable t2 B1)
  end.

Definition do_stop (s : St) (L : Lv) : St :=
  let t := term_of L in
  let z := sz s in let B := sB s in let Y := sY s in
  let D1 := tD t in let B1 := add B D1 in let z1 := tna t in
  let a := la L in let b := lb L in let g := lg L in let thr := lthr L in
  if negb (fits B1) || negb (leb (wc 1) D1) then set_stat s 4 else
  if (z1 =? z)%uint63 && (low2 D1 =? 0)%uint63 then
    match pick B Y D1 (maxq a b g thr D1) with
    | Some (T, yT) =>
      let Bn := add B yT in
      set_B s Bn (if eqb Bn Y then 1%uint63 else 0%uint63)
    | None => set_hop s z1 B1 2
    end
  else
    let '(s0, d, oab) := get_det s z1 B1 in
    match oab with
    | Some (ad, bd) =>
      let Dt := add D1 (tD d) in
      if (tna d =? z)%uint63 && (low2 Dt =? 0)%uint63 && fits Dt && leb (wc 1) Dt then
        let q1 := maxq a b g thr Dt in
        let q2 := maxq ad bd (lg (tL d)) (lthr (tL d)) Dt in
        match pick B Y Dt (if ltb q1 q2 then q1 else q2) with
        | Some (T, yT) =>
          let Bn := add B yT in
          set_B s0 Bn (if eqb Bn Y then 1%uint63 else 0%uint63)
        | None => set_hop s0 z1 B1 2
        end
      else set_hop s0 z1 B1 2
    | None => set_hop s0 z1 B1 2
    end.

(** ** A block from above: all exact checks *)
Definition blen (x : int) : int := (63 - head0 x)%uint63.
Definition fxdiv (x g : W) : int :=
  (* a suggestion only: about x * 2^28 / g; here both are below 2^100 *)
  let gh := hi g in let gl := lo g in
  let s := if (gh =? 0)%uint63 then 0%uint63 else blen gh in
  let gt := if (gh =? 0)%uint63 then (gl >> 1)%uint63 else ((gh << (62 - s)) + (gl >> (1 + s)))%uint63 in
  (* numerator x * 2^28 / 2^(1+s) as two words *)
  let xh := hi x in let xl := lo x in
  let e := (1 + s)%uint63 in
  if (e <=? 28)%uint63 then
    let k := (28 - e)%uint63 in
    let l := (xl << k)%uint63 in
    let h := ((xh << k) + (xl >> (63 - k)))%uint63 in
    if (h <? gt)%uint63 then fst (diveucl_21 h l gt) else 0%uint63
  else
    let k := (e - 28)%uint63 in
    let l := ((xl >> k) + (xh << (63 - k)))%uint63 in
    let h := (xh >> k)%uint63 in
    if (h <? gt)%uint63 then fst (diveucl_21 h l gt) else 0%uint63.

Definition env_of (s : St) : Env * Term :=
  let z := sz s in
  let t := if (z =? 22)%uint63 then sd6 s else sd22 s in
  if tok t && (tna t =? z)%uint63 && leb (lbase (tL t)) (sB s) && (hi (tD t) =? 0)%uint63 then (mkEnv z true (lo (tD t)), t)
  else (mkEnv z false 0%uint63, t).

Definition TONEW : W := wc 268435456.
Definition bfuel : nat := 64.

(** Is the exact point in the region of the lemma? *)
Definition reg_exact (e : Ent) (bl bh wl wh : int) : bool :=
  (eW e =? eW1 e)%uint63 && (eW1 e <=? wl)%uint63 && (wl <=? wh)%uint63 && (wh <=? eW2 e)%uint63 &&
  lo_ok (elo e) (wh - eW1 e)%uint63 bl && hi_ok (ehi e) (wl - eW1 e)%uint63 bh.

Definition try_block (c : Lv) (s : St) : Mem * option St :=
  let B := sB s in let b := lb c in let a := la c in let g := lg c in let m := sm s in
  if negb (leb (wc 281474976710656) g) || negb (eqb (lbase c) B) || negb (((low2 b) land 1 =? 1)%uint63)
     || negb ((hi (lc c) =? 0)%uint63) then (m, None) else
  let S := add a b in
  if negb (leb (wc 0) b) || negb (leb S (mkW 8589934592 0)) || negb (leb (wc 0) S) || negb (leb b S) || negb (leb (wc 1) g) || negb (lv_fits c) then (m, None) else
  let w := fxdiv S g in let bt := fxdiv b g in
  if (288230376151711744 <=? w)%uint63 || (w <? 1099511627776)%uint63 || (bt <? 64)%uint63 || (1152921504606846976 <=? bt)%uint63 then (m, None) else
  let wl := (w - 2)%uint63 in let wh := (w + 2)%uint63 in let bl := (bt - 2)%uint63 in let bh := (bt + 2)%uint63 in
  let S28 := mulk 268435456 S in let b28 := mulk 268435456 b in
  match mul_nn (wc wl) g, mul_nn (wc wh) g, mul_nn (wc bl) g, mul_nn (wc bh) g with
  | Some p1, Some p2, Some p3, Some p4 =>
    if leb p1 S28 && leb S28 p2 && leb p3 b28 && leb b28 p4 then
      let '(v, t) := env_of s in
      let x := mkCtx (lo (lc c)) (low2 a) (low2 b) in
      let '(m1, oe) := bn bfuel m v x bt w in
      match oe with
      | None => (m1, None)
      | Some e =>
        let last := wc (elast e) in
        let Bn := add B (wc (eY e)) in
        if keyok v x e && negb (eY e =? 0)%uint63 && reg_exact e bl bh wl wh && leb (wc (eGm e)) g && fits Bn && leb Bn (sY s) && fits (add B (wc (edlast e))) then
          match mul_nn (sub g (wc 1)) last with
          | Some h =>
            if leb (add (lthr c) h) a && fits h && fits (add (lthr c) h) then
              let dok := negb (edet e) ||
                 (vhas v && (low2 (add (sub B (lbase (tL t))) (wc (edres e))) =? 0)%uint63 &&
                  match eval (tL t) (add B (wc (edlast e))) with
                  | Some (ad, bd) => ltb bd (add ad (wc 3))
                  | None => false
                  end) in
              if dok then (m1, Some (mkSt (sz s) Bn (if eqb Bn (sY s) then 1%uint63 else 0%uint63) (sha s) (sd6 s) (sd22 s) m1 (sY s))) else (m1, None)
            else (m1, None)
          | None => (m1, None)
          end
        else (m1, None)
      end
    else (m, None)
  | _, _, _, _ => (m, None)
  end.


(** ** Soundness of a stop *)
Lemma maxq_ok a b g thr D : fits (maxq a b g thr D) = true /\ 0 <= val (maxq a b g thr D).
Proof.
  unfold maxq. cbv zeta. cbn [lthr].
  assert (W0 : fits (wc 0) = true /\ 0 <= val (wc 0)) by (split; [reflexivity|vm_compute; intro X; discriminate X]).
  destruct (mul_nn (sub (add g g) (wc 1)) D) as [md|]; [|exact W0].
  destruct (mul_nn md _) as [p|]; [|exact W0].
  destruct (mul_nn D _) as [yq|]; [|exact W0].
  destruct (mul_nn (sub g (wc 1)) yq) as [hy|]; [|exact W0].
  match goal with |- context [if ?c then _ else _] => destruct c eqn:C end; [|exact W0].
  apply andb_prop in C. destruct C as [C _]. apply andb_prop in C. destruct C as [C _]. apply andb_prop in C. destruct C as [C C5]. apply andb_prop in C. destruct C as [C _]. apply andb_prop in C. destruct C as [_ C3].
  apply leb_spec_W in C5. rewrite val_wc in C5. change (phi 0%uint63) with 0 in C5. split; assumption.
Qed.

Lemma put_det_ok A0 B0 s z t : st_ok A0 B0 s -> (phi z = 6 \/ phi z = 22) -> term_sem (phi z) t -> st_ok A0 B0 (put_det s z t).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hz Ht. unfold put_det.
  destruct (z =? 6)%uint63 eqn:C.
  - apply eqb_true in C. change (phi 6%uint63) with 6 in C. rewrite C in Ht. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj Ht (conj H6 H7)))))).
  - assert (Zz : phi z = 22).
    { destruct Hz as [E|E]; [|exact E]. exfalso. assert (X : z = 6%uint63) by (apply to_Z_inj; exact E). rewrite X in C. discriminate. }
    rewrite Zz in Ht. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj Ht H7)))))).
Qed.

Lemma low2_eq_mod (x y : W) : (low2 x =? low2 y)%uint63 = true -> (val y - val x) mod 4 = 0.
Proof.
  intros H. apply eqb_true in H. rewrite !low2_mod in H. rewrite Zminus_mod, <- H, Z.sub_diag. reflexivity.
Qed.

Lemma det_usable_spec z t B1 ad bd : term_sem z t -> fits B1 = true -> det_usable t B1 = Some (ad, bd) ->
  tok t = true /\ val (lbase (tL t)) <= val B1 /\ (val B1 - val (lbase (tL t))) mod 4 = 0 /\ eval (tL t) B1 = Some (ad, bd) /\ val bd < val ad + 3.
Proof.
  intros Hs HB H. unfold det_usable in H.
  destruct (tok t && leb (lbase (tL t)) B1 && (low2 (lbase (tL t)) =? low2 B1)%uint63) eqn:C; [|discriminate].
  apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
  apply leb_spec_W in C2. apply low2_eq_mod in C3.
  destruct (eval (tL t) B1) as [[a b]|] eqn:E; [|discriminate].
  destruct (ltb b (add a (wc 3))) eqn:L; [|discriminate]. injection H as <- <-.
  destruct (Hs C1) as ([HF [Hg _]] & _).
  destruct (eval_spec _ _ _ _ HF Hg HB E) as (Fa & _).
  apply ltb_spec_W in L. rewrite val_add_c in L by (exact Fa || (vm_compute; reflexivity)). change (phi 3%uint63) with 3 in L.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [reflexivity|exact L].
Qed.

Lemma get_det_sound A0 B0 s z B1 s0 d oab : st_ok A0 B0 s -> (phi z = 6 \/ phi z = 22) -> fits B1 = true ->
  get_det s z B1 = (s0, d, oab) ->
  st_ok A0 B0 s0 /\ sz s0 = sz s /\ sB s0 = sB s /\ sY s0 = sY s /\ sstat s0 = sstat s /\ sha s0 = sha s /\ sm s0 = sm s /\ term_sem (phi z) d /\
  forall ad bd, oab = Some (ad, bd) -> tok d = true /\ val (lbase (tL d)) <= val B1 /\ (val B1 - val (lbase (tL d))) mod 4 = 0 /\ eval (tL d) B1 = Some (ad, bd) /\ val bd < val ad + 3.
Proof.
  intros Hs Hz HB H. unfold get_det in H. cbv zeta in H.
  assert (Ht : term_sem (phi z) (det_of s z)).
  { destruct Hs as (_ & _ & _ & _ & H5 & H6 & _). unfold det_of. destruct (z =? 6)%uint63 eqn:C.
    - apply eqb_true in C. change (phi 6%uint63) with 6 in C. rewrite C. exact H5.
    - assert (Zz : phi z = 22).
      { destruct Hz as [E|E]; [|exact E]. exfalso. assert (X : z = 6%uint63) by (apply to_Z_inj; exact E). rewrite X in C. discriminate. }
      rewrite Zz. exact H6. }
  destruct (det_usable (det_of s z) B1) as [[a b]|] eqn:U.
  - injection H as <- <- <-.
    split; [exact Hs|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Ht|].
    intros ad bd E. injection E as <- <-. exact (det_usable_spec _ _ _ _ _ Ht HB U).
  - pose proof (walk_sound Wfuel (phi z) (root z B1) (root_ok z B1 HB Hz)) as Hw. revert H Hw.
    generalize (walk Wfuel (root z B1)). intros t2 H Hw. injection H as <- <- <-.
    assert (F : forall X, X = put_det s z t2 -> sz X = sz s /\ sB X = sB s /\ sY X = sY s /\ sstat X = sstat s /\ sha X = sha s /\ sm X = sm s).
    { intros X ->. unfold put_det. destruct (z =? 6)%uint63; exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))). }
    destruct (F _ eq_refl) as (F1 & F2 & F3 & F4 & F5 & F6).
    split; [apply put_det_ok; assumption|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact Hw|].
    intros ad bd E. exact (det_usable_spec _ _ _ _ _ Hw HB E).
Qed.

Definition post (z0 : int) (B : W) (s : St) : Prop :=
  sstat s = 0%uint63 -> sz s = z0 /\ val B <= val (sB s) /\ (val (sB s) - val B) mod 4 = 0.

Lemma post_stat z0 B s : (sstat s =? 0)%uint63 = false -> post z0 B s.
Proof. intros H X. rewrite X in H. discriminate. Qed.

Lemma st_ok_stat A0 B0 s k : st_ok A0 B0 s -> (k =? 3)%uint63 = false -> st_ok A0 B0 (set_stat s k).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & _) K. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  intros X. cbn [sstat set_stat] in X. rewrite X in K. discriminate.
Qed.
Lemma st_ok_hop A0 B0 s z1 B1 k : st_ok A0 B0 s -> Rch (phi (sz s)) (val (sB s)) (phi z1) (val B1) -> fits B1 = true -> (phi z1 = 6 \/ phi z1 = 22) ->
  (k =? 3)%uint63 = false -> st_ok A0 B0 (set_hop s z1 B1 k).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & _) R F Z K. split; [eapply Rch_trans; [exact H1|exact R]|]. split; [exact F|]. split; [exact Z|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  intros X. cbn [sstat set_hop] in X. rewrite X in K. discriminate.
Qed.
Lemma st_ok_mem A0 B0 s m : st_ok A0 B0 s -> mem_ok m -> st_ok A0 B0 (set_mem s m).
Proof. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) M. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact M|]. split; [exact H5|]. split; [exact H6|]. exact H7. Qed.

(** A step forward to Bn, the state ready to go on. *)
Lemma adv_ok A0 B0 s Bn Y : st_ok A0 B0 s -> Rch (phi (sz s)) (val (sB s)) (phi (sz s)) (val Bn) -> fits Bn = true ->
  val (sB s) <= val Bn -> (val Bn - val (sB s)) mod 4 = 0 ->
  st_ok A0 B0 (set_B s Bn (if eqb Bn Y then 1%uint63 else 0%uint63)) /\ post (sz s) (sB s) (set_B s Bn (if eqb Bn Y then 1%uint63 else 0%uint63)).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & _) R F L M. split.
  - split; [eapply Rch_trans; [exact H1|exact R]|]. split; [exact F|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    intros X. cbn [sstat set_B] in X. destruct (eqb Bn Y) in X; assert (Y3 : phi 3%uint63 = 3) by reflexivity; rewrite <- X in Y3; discriminate.
  - intros _. cbn [sz sB set_B]. split; [reflexivity|]. split; assumption.
Qed.

Lemma add_rounds (B y D T : W) (F : fits (add B y) = true) (FB : fits B = true) (Fy : fits y = true) (E : val y = val D * val T) :
  val (add B y) = val B + val T * val D /\ (0 <= val D -> 1 <= val T -> val B <= val (add B y)) /\ (val D mod 4 = 0 -> (val (add B y) - val B) mod 4 = 0).
Proof.
  assert (V : val (add B y) = val B + val y) by (apply val_add2; assumption).
  rewrite V, E. split; [ring|]. split.
  - intros D0 T1. assert (0 <= val D * val T) by (apply Z.mul_nonneg_nonneg; lia). lia.
  - intros M. destruct (mod0_ex _ M) as [j Ej]. rewrite Ej.
    replace (val B + 4 * j * val T - val B) with (4 * (j * val T)) by ring. apply ex_mod0.
Qed.

Lemma do_stop_sound A0 B0 s L :
  st_ok A0 B0 s -> lv_ok (phi (sz s)) L -> lbase L = sB s -> val (lthr L) <= val (la L) -> val (lb L) < val (la L) + 3 -> val (lb L) mod 2 = 0 ->
  fits (add (lc L) (wc 7)) = true -> fits (sub (lc L) (wc 2)) = true ->
  st_ok A0 B0 (do_stop s L) /\ post (sz s) (sB s) (do_stop s L).
Proof.
  intros Hs HL HbL Hta Hlt Hev F7 F2. unfold do_stop. cbv zeta.
  assert (Ht : term_sem (phi (sz s)) (term_of L)) by (apply term_of_ok; assumption).
  destruct (Ht eq_refl) as (_ & Hz1 & FD & Rw). change (tL (term_of L)) with L in Rw.
  pose proof Hs as (S1 & SB & Sz & Sm & S5 & S6 & S7).
  pose proof HL as [HF [Hg [Hth [Hsum HR]]]].
  generalize HF; intros HF'.
  unfold lv_fits in HF'. apply andb_prop in HF'. destruct HF' as [HF' Fc]. apply andb_prop in HF'. destruct HF' as [HF' Fth]. apply andb_prop in HF'. destruct HF' as [HF' Fbs]. apply andb_prop in HF'. destruct HF' as [HF' Fg]. apply andb_prop in HF'. destruct HF' as [Fa Fb].
  set (t := term_of L) in *. set (D1 := tD t) in *. set (z1 := tna t) in *.
  destruct (negb (fits (add (sB s) D1)) || negb (leb (wc 1) D1)) eqn:G0.
  { split; [apply st_ok_stat; [exact Hs|reflexivity]|apply post_stat; reflexivity]. }
  apply orb_false_iff in G0. destruct G0 as [G0 G1]. apply negb_false_iff in G0, G1. apply leb_spec_W in G1. rewrite val_wc in G1. change (phi 1%uint63) with 1 in G1.
  assert (VB1 : val (add (sB s) D1) = val (sB s) + val D1) by (apply val_add2; assumption).
  assert (Word : Rch (phi (sz s)) (val (sB s)) (phi z1) (val (add (sB s) D1))).
  { pose proof (Rw 0 ltac:(lia) ltac:(reflexivity)) as X. rewrite !Z.mul_0_r, !Z.sub_0_r, !Z.add_0_r in X.
    rewrite HbL in X. rewrite VB1. apply X; [|exact Hlt]. exact Hta. }
  assert (Hop : forall s0, st_ok A0 B0 s0 -> sz s0 = sz s -> sB s0 = sB s -> st_ok A0 B0 (set_hop s0 z1 (add (sB s) D1) 2) /\ post (sz s) (sB s) (set_hop s0 z1 (add (sB s) D1) 2)).
  { intros s0 H0 E1 E2. split; [apply st_ok_hop; [exact H0| rewrite E1, E2; exact Word|exact G0|exact Hz1|reflexivity]|apply post_stat; reflexivity]. }
  destruct ((z1 =? sz s)%uint63 && (low2 D1 =? 0)%uint63) eqn:Dir.
  - apply andb_prop in Dir. destruct Dir as [Ez Em]. apply eqb_true in Ez, Em. rewrite low2_mod in Em. change (phi 0%uint63) with 0 in Em.
    pose proof (maxq_ok (la L) (lb L) (lg L) (lthr L) D1) as [Fq Hq].
    destruct (pick (sB s) (sY s) D1 (maxq (la L) (lb L) (lg L) (lthr L) D1)) as [[T yT]|] eqn:Pk; [|apply Hop; [exact Hs|reflexivity|reflexivity]].
    destruct (pick_spec _ _ _ _ _ _ Fq Hq Pk) as (FT & Fy & FBn & Ey & BT).
    destruct (add_rounds (sB s) yT D1 T FBn SB Fy Ey) as (V1 & V2 & V3).
    apply adv_ok; [exact Hs| |exact FBn|apply V2; clear - G1 BT; lia|apply V3; exact Em].
    rewrite V1. rewrite <- HbL.
    apply (direct_rounds (phi (sz s)) t (val T) (val D1) Ht eq_refl Ez eq_refl Em ltac:(clear - BT; lia) ltac:(clear - G1; lia)).
    intros k Hk.
    assert (Kq : 0 <= k <= val (maxq (la L) (lb L) (lg L) (lthr L) D1)) by (clear - Hk BT; lia).
    exact (maxq_spec (la L) (lb L) (lg L) (lthr L) D1 k Fa Fb Fg Fth Hg ltac:(clear - G1; lia) Hta Hlt Kq).
  - destruct (get_det s z1 (add (sB s) D1)) as [[s0 d] oab] eqn:Gd.
    destruct (get_det_sound _ _ _ _ _ _ _ _ Hs Hz1 G0 Gd) as (H0 & E1 & E2 & E3 & E4 & E5 & E6 & Hd & Hab).
    destruct oab as [[ad bd]|]; [|apply Hop; assumption].
    destruct (Hab ad bd eq_refl) as (Td & Bl & Bm & Ed & Lt). clear Hab.
    destruct (Hd Td) as (HLd & Zd & FDd & _).
    destruct ((tna d =? sz s)%uint63 && (low2 (add D1 (tD d)) =? 0)%uint63 && fits (add D1 (tD d)) && leb (wc 1) (add D1 (tD d))) eqn:C; [|apply Hop; assumption].
    apply andb_prop in C. destruct C as [C C4]. apply andb_prop in C. destruct C as [C FDt]. apply andb_prop in C. destruct C as [Ezd Em].
    apply eqb_true in Ezd, Em. rewrite low2_mod in Em. change (phi 0%uint63) with 0 in Em.
    apply leb_spec_W in C4. rewrite val_wc in C4. change (phi 1%uint63) with 1 in C4.
    assert (VDt : val (add D1 (tD d)) = val D1 + val (tD d)) by (apply val_add2; assumption).
    pose proof HLd as [HFd [Hgd [Hthd [_ _]]]].
    generalize HFd; intros HF'.
    unfold lv_fits in HF'. apply andb_prop in HF'. destruct HF' as [HF' _]. apply andb_prop in HF'. destruct HF' as [HF' Ftd]. apply andb_prop in HF'. destruct HF' as [HF' _]. apply andb_prop in HF'. destruct HF' as [HF' Fgd]. apply andb_prop in HF'. destruct HF' as [_ _].
    destruct (eval_spec _ _ _ _ HFd Hgd G0 Ed) as (Fad & Fbd & Vad & Vbd & Vtd).
    set (Dt := add D1 (tD d)) in *.
    pose proof (maxq_ok (la L) (lb L) (lg L) (lthr L) Dt) as [Fq1 Hq1].
    pose proof (maxq_ok ad bd (lg (tL d)) (lthr (tL d)) Dt) as [Fq2 Hq2].
    set (q1 := maxq (la L) (lb L) (lg L) (lthr L) Dt) in *.
    set (q2 := maxq ad bd (lg (tL d)) (lthr (tL d)) Dt) in *.
    assert (Qm : fits (if ltb q1 q2 then q1 else q2) = true /\ 0 <= val (if ltb q1 q2 then q1 else q2) /\ val (if ltb q1 q2 then q1 else q2) <= val q1 /\ val (if ltb q1 q2 then q1 else q2) <= val q2).
    { destruct (ltb q1 q2) eqn:Lq.
      - apply ltb_spec_W in Lq. split; [exact Fq1|]. clear - Hq1 Lq. lia.
      - apply ltb_false_W in Lq. split; [exact Fq2|]. clear - Hq2 Lq. lia. }
    destruct Qm as (Fqm & Hqm & Qm1 & Qm2).
    destruct (pick (sB s) (sY s) Dt (if ltb q1 q2 then q1 else q2)) as [[T yT]|] eqn:Pk; [|apply Hop; assumption].
    destruct (pick_spec _ _ _ _ _ _ Fqm Hqm Pk) as (FT & Fy & FBn & Ey & BT).
    destruct (add_rounds (sB s) yT Dt T FBn SB Fy Ey) as (V1 & V2 & V3).
    pose proof (adv_ok A0 B0 s0 (add (sB s) yT) (sY s) H0) as Adv. rewrite E1, E2 in Adv.
    apply Adv; [| exact FBn|apply V2; clear - C4 BT; lia|apply V3; exact Em].
    rewrite V1, VDt. rewrite <- HbL.
    set (yd := val (add (sB s) D1) - val (lbase (tL d))).
    apply (det_rounds (phi (sz s)) (phi z1) t d (val T) (val D1) (val (tD d)) yd Ht eq_refl eq_refl eq_refl Hd Td Ezd eq_refl).
    + unfold yd. rewrite VB1. change (val (lbase (tL t))) with (val (lbase L)). rewrite HbL. ring.
    + unfold yd. clear - Bl. lia.
    + exact Bm.
    + rewrite <- VDt. exact Em.
    + clear - BT. lia.
    + clear - C4 VDt. lia.
    + intros k Hk. rewrite <- VDt. fold Dt. set (K := k * val Dt).
      split.
      * subst K. assert (Kq : 0 <= k <= val q1) by (clear - Hk BT Qm1; lia).
        exact (maxq_spec (la L) (lb L) (lg L) (lthr L) Dt k Fa Fb Fg Fth Hg ltac:(clear - C4; lia) Hta Hlt Kq).
      * assert (Kq : 0 <= k <= val q2) by (clear - Hk BT Qm2; lia).
        pose proof (maxq_spec ad bd (lg (tL d)) (lthr (tL d)) Dt k Fad Fbd Fgd Ftd Hgd ltac:(clear - C4; lia) Vtd Lt Kq) as [Q1 Q2].
        fold K in Q1, Q2.
        replace (val (la (tL d)) - (val (lg (tL d)) - 1) * (yd + K)) with (val ad - (val (lg (tL d)) - 1) * K) by (rewrite Vad; fold yd; ring).
        replace (val (lb (tL d)) + val (lg (tL d)) * (yd + K)) with (val bd + val (lg (tL d)) * K) by (rewrite Vbd; fold yd; ring).
        split; assumption.
Qed.

(** ** One slow sweep, by the map itself *)
Fixpoint zsweep (f : nat) (a b : Z) : option (Z * Z) :=
  match f with
  | O => None
  | S f =>
    match aStep a b with
    | None => None
    | Some (a1, b1, _) => if (a1 =? 6) || (a1 =? 22) then Some (a1, b1) else zsweep f a1 b1
    end
  end.
Lemma zsweep_sound f : forall a b a1 b1, zsweep f a b = Some (a1, b1) -> Rch a b a1 b1 /\ (a1 = 6 \/ a1 = 22).
Proof.
  induction f as [|f IH]; intros a b a1 b1 H; [discriminate|].
  cbn [zsweep] in H. destruct (aStep a b) as [[[a2 b2] r]|] eqn:E; [|discriminate].
  destruct ((a2 =? 6) || (a2 =? 22)) eqn:C.
  - injection H as <- <-. split; [eapply Rch_step; exact E|]. apply orb_prop in C. destruct C as [C|C]; apply Z.eqb_eq in C; [left|right]; exact C.
  - destruct (IH _ _ _ _ H) as [H1 H2]. split; [|exact H2]. eapply Rch_trans; [eapply Rch_step; exact E|exact H1].
Qed.
Definition w_of_z (z : Z) : W := mkW (of_Z (z / P63)) (of_Z (z mod P63)).
Definition slow_sweep (s : St) : St :=
  match zsweep Wfuel (phi (sz s)) (val (sB s)) with
  | Some (a1, b1) =>
    let B1 := w_of_z b1 in
    if (val B1 =? b1) && fits B1 then set_hop s (of_Z a1) B1 2 else set_stat s 4
  | None => set_stat s 4
  end.

(** ** The recursion over the top of the tree *)
Fixpoint node (f : nat) (L : Lv) (s : St) : St :=
  match f with
  | O => set_stat s 2
  | S f =>
    let run_child := fun (c : Lv) (s : St) =>
      if lv_fits c then
        let '(m, os) := try_block c s in
        match os with
        | Some s1 => s1
        | None => node f c (set_mem s m)
        end
      else slow_sweep s in
    match eval L (sB s) with
    | None => s
    | Some (a, b) =>
      let B := sB s in
      let a3 := add a (wc 3) in
      if ltb a3 b then
        let s1 := run_child (childD L a b B) s in
        if (sstat s1 =? 0)%uint63 then node f L s1 else s1
      else if eqb a3 b then mkSt (sz s) B 3 a (sd6 s) (sd22 s) (sm s) (sY s)
      else if ltb b (wc 5) then slow_sweep s
      else if ((low2 b) land 1 =? 1)%uint63 then
        if eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg L) (wc 1) || leb (lthr L) (add b (wc 1))) then slow_sweep s
        else
          let isu := (low2 (add (sub a b) (wc 5)) =? 2)%uint63 in
          let s1 := run_child (if isu then childU L a b B else childV L a b B) s in
          if (sstat s1 =? 0)%uint63 then node f L s1 else s1
      else
        let L' := rebase L a b B in
        if lv_fits L' && fits (add (lc L) (wc 7)) && fits (sub (lc L) (wc 2)) then
          let s1 := do_stop s L' in
          if (sstat s1 =? 0)%uint63 then node f L s1 else s1
        else slow_sweep s
    end
  end.

Definition Nfuel : nat := Nat.pow 2 12.
Fixpoint top (f : nat) (s : St) : St :=
  match f with
  | O => s
  | S f =>
    let s1 := node Nfuel (root (sz s) (sB s)) (set_stat s 0) in
    if (sstat s1 =? 2)%uint63 then
      if leb (sY s1) (sB s1) then s1 else top f s1
    else s1
  end.

Definition start (z : int) (B Y : W) : St := mkSt z B 0 (wc 0) noterm noterm (mem0 0%uint63) Y.
Definition Tfuel : nat := Nat.pow 2 16.
(** Fuels are unary, so a long job takes the inner loop many times. *)
Fixpoint top2 (f : nat) (s : St) : St :=
  match f with
  | O => s
  | S f =>
    let s1 := top Tfuel s in
    if (sstat s1 =? 2)%uint63 && ltb (sB s1) (sY s1) then top2 f s1 else s1
  end.
Definition run (z : int) (B Y : W) : St := top2 Tfuel (start z B Y).
Definition run_seg (z : int) (B : W) (z1 : int) (Y : W) : bool :=
  let s := run z B Y in (sz s =? z1)%uint63 && eqb (sB s) Y.

Definition zw (x : Z) : W := w_of_z x.
Definition result (s : St) := (phi (sstat s), phi (sz s), val (sB s), val (sha s), phi (mn (sm s))).

(** ** The region test, exact: a box around the point inside every line *)
Lemma lo_pure t d f r wh g b S be V : 0 <= t -> 0 <= g -> r + d = wh -> t * d < TT * f + TT -> V + f + 2 <= be ->
  PP * S <= wh * g -> be * g <= PP * b -> lo_z t V r b S g.
Proof.
  intros Ht Hg Ed Hf Hv H1 H2. unfold lo_z. subst wh.
  assert (A : t * (PP * S) <= t * ((r + d) * g)) by (apply Z.mul_le_mono_nonneg_l; assumption).
  assert (B : (t * d) * g <= (TT * f + TT) * g) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (C : (V + f + 1) * g <= be * g) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.
Lemma hi_pure t d f r wl g b S be V : 0 <= t -> 0 <= g -> r + d = wl -> TT * f <= t * d -> be + 1 <= V + f ->
  wl * g <= PP * S -> PP * b <= be * g -> hi_z t V r b S g.
Proof.
  intros Ht Hg Ed Hf Hv H1 H2. unfold hi_z. subst wl.
  assert (A : t * ((r + d) * g) <= t * (PP * S)) by (apply Z.mul_le_mono_nonneg_l; assumption).
  assert (B : (TT * f) * g <= (t * d) * g) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (C : be * g <= (V + f - 1) * g) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Lemma line_val (x : Line) (dW : int) : line_ok x -> phi dW <= 2147483648 ->
  phi ((lt x * dW) >> 30)%uint63 = (phi (lt x) * phi dW) / TT /\ 0 <= (phi (lt x) * phi dW) / TT <= 2147483648 /\
  TT * ((phi (lt x) * phi dW) / TT) <= phi (lt x) * phi dW < TT * ((phi (lt x) * phi dW) / TT) + TT.
Proof.
  intros [H1 H2] Hd. pose proof (phi_bd63 (lt x)) as Bt. pose proof (phi_bd63 dW) as Bd.
  assert (P : 0 <= phi (lt x) * phi dW <= TT * 2147483648).
  { split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]. }
  assert (E : phi (lt x * dW)%uint63 = phi (lt x) * phi dW) by (apply phi_of_cg; [apply cg_mul; apply cg_refl|lia]).
  rewrite phi_lsr30, E. split; [reflexivity|].
  generalize (phi (lt x) * phi dW) P. intros m Pm. clear - Pm.
  pose proof (fl_lo m) as L. pose proof (fl_hi m) as U. split; [|lia]. split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma lo_ok_sound (l : list Line) dW be r wh g b S : Forall line_ok l -> lo_ok l dW be = true -> phi dW <= 2147483648 -> phi be < 2305843009213693952 ->
  r + phi dW = wh -> 0 <= g -> PP * S <= wh * g -> phi be * g <= PP * b -> Forall (fun x => lo_l r x b S g) l.
Proof.
  intros Hl. induction Hl as [|x l Hx Hl IH]; intros H Hd Hb Er Hg H1 H2; [constructor|].
  cbn [lo_ok] in H. apply andb_prop in H. destruct H as [H Ht]. constructor; [|apply IH; assumption].
  destruct (line_val x dW Hx Hd) as (Ef & Bf & Fl & Fu). pose proof Hx as [_ Hv].
  set (f := (phi (lt x) * phi dW) / TT) in *. pose proof (phi_bd63 (lv x)) as Bv. pose proof (phi_bd63 (lt x)) as Bt. pose proof (phi_bd63 be) as Bb.
  apply leb_true in H.
  assert (E1 : phi (lv x + ((lt x * dW) >> 30) + 2)%uint63 = phi (lv x) + f + 2).
  { apply phi_of_cg; [apply cg_add; [apply cg_add; [apply cg_refl|unfold cg; rewrite Ef; reflexivity]|apply cg_refl]|change (phi 2%uint63) with 2; lia]. }
  assert (E2 : phi (be + VOFF)%uint63 = phi be + VO).
  { apply phi_of_cg; [apply cg_add; apply cg_refl|change (phi VOFF) with VO; lia]. }
  rewrite E1, E2 in H. unfold lo_l.
  apply (lo_pure (phi (lt x)) (phi dW) f r wh g b S (phi be) (phi (lv x) - VO)); try lia.
Qed.
Lemma hi_ok_sound (l : list Line) dW be r wl g b S : Forall line_ok l -> hi_ok l dW be = true -> phi dW <= 2147483648 -> phi be < 2305843009213693952 ->
  r + phi dW = wl -> 0 <= g -> wl * g <= PP * S -> PP * b <= phi be * g -> Forall (fun x => hi_l r x b S g) l.
Proof.
  intros Hl. induction Hl as [|x l Hx Hl IH]; intros H Hd Hb Er Hg H1 H2; [constructor|].
  cbn [hi_ok] in H. apply andb_prop in H. destruct H as [H Ht]. constructor; [|apply IH; assumption].
  destruct (line_val x dW Hx Hd) as (Ef & Bf & Fl & Fu). pose proof Hx as [_ Hv].
  set (f := (phi (lt x) * phi dW) / TT) in *. pose proof (phi_bd63 (lv x)) as Bv. pose proof (phi_bd63 (lt x)) as Bt. pose proof (phi_bd63 be) as Bb.
  apply leb_true in H.
  assert (E1 : phi (lv x + ((lt x * dW) >> 30))%uint63 = phi (lv x) + f).
  { apply phi_of_cg; [apply cg_add; [apply cg_refl|unfold cg; rewrite Ef; reflexivity]|lia]. }
  assert (E2 : phi (be + VOFF + 1)%uint63 = phi be + VO + 1).
  { apply phi_of_cg; [apply cg_add; [apply cg_add; apply cg_refl|apply cg_refl]|change (phi VOFF) with VO; change (phi 1%uint63) with 1; lia]. }
  rewrite E1, E2 in H. unfold hi_l.
  apply (hi_pure (phi (lt x)) (phi dW) f r wl g b S (phi be) (phi (lv x) - VO)); try lia.
Qed.

Lemma reg_exact_sound e bl bh wl wh b S g : ent_bd e -> reg_exact e bl bh wl wh = true -> 1 <= g ->
  phi bl < 2305843009213693952 -> phi bh < 2305843009213693952 ->
  phi wl * g <= PP * S -> PP * S <= phi wh * g -> phi bl * g <= PP * b -> PP * b <= phi bh * g -> reg e b S g.
Proof.
  intros Hb H Hg Bl Bh H1 H2 H3 H4. unfold reg_exact in H.
  apply andb_prop in H. destruct H as [H Hh]. apply andb_prop in H. destruct H as [H Hl]. apply andb_prop in H. destruct H as [H C4]. apply andb_prop in H. destruct H as [H C3]. apply andb_prop in H. destruct H as [C1 C2].
  apply eqb_true in C1. apply leb_true in C2, C3, C4.
  destruct Hb as (L1 & L2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rg).
  assert (Dh : phi (wh - eW1 e)%uint63 = phi wh - phi (eW1 e)) by (rewrite sub_spec, wB63; apply Z.mod_small; pose proof (phi_bd63 wh); lia).
  assert (Dl : phi (wl - eW1 e)%uint63 = phi wl - phi (eW1 e)) by (rewrite sub_spec, wB63; apply Z.mod_small; pose proof (phi_bd63 wl); lia).
  split; [|split; [|split]].
  - apply (lo_ok_sound _ _ _ _ (phi wh) _ _ _ L1 Hl); try lia.
  - apply (hi_ok_sound _ _ _ _ (phi wl) _ _ _ L2 Hh); try lia.
  - eapply Z.le_trans; [|exact H1]. apply Z.mul_le_mono_nonneg_r; lia.
  - eapply Z.le_trans; [exact H2|]. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

(** ** What the environment of a block gives *)
Lemma val_hi0 (x : W) : hi x = 0%uint63 -> val x = phi (lo x).
Proof. intros H. unfold val. rewrite H. change (sg 0%uint63) with 0. ring. Qed.

Lemma z_cases (z : int) : phi z = 6 \/ phi z = 22 -> (z =? 22)%uint63 = true /\ phi z = 22 \/ (z =? 22)%uint63 = false /\ phi z = 6.
Proof.
  intros [E|E].
  - right. split; [|exact E]. assert (X : z = 6%uint63) by (apply to_Z_inj; exact E). rewrite X. reflexivity.
  - left. split; [|exact E]. assert (X : z = 22%uint63) by (apply to_Z_inj; exact E). rewrite X. reflexivity.
Qed.

Lemma env_of_spec A0 B0 s v t : st_ok A0 B0 s -> env_of s = (v, t) ->
  vz v = sz s /\ term_sem (28 - phi (sz s)) t /\
  (vhas v = true -> tok t = true /\ phi (tna t) = phi (sz s) /\ val (lbase (tL t)) <= val (sB s) /\ val (tD t) = phi (vd2 v)).
Proof.
  intros (_ & _ & Sz & _ & S5 & S6 & _) H. unfold env_of in H. cbv zeta in H.
  assert (Ht : term_sem (28 - phi (sz s)) (if (sz s =? 22)%uint63 then sd6 s else sd22 s)).
  { destruct (z_cases _ Sz) as [[C E]|[C E]]; rewrite C, E; [exact S5|exact S6]. }
  destruct (tok _ && _ && _ && _) eqn:C in H.
  - injection H as <- <-. split; [reflexivity|]. split; [exact Ht|]. intros _.
    apply andb_prop in C. destruct C as [C C4]. apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
    apply eqb_true in C2. apply leb_spec_W in C3. apply Uint63.eqb_spec in C4.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. apply val_hi0. exact C4.
  - injection H as <- <-. split; [reflexivity|]. split; [exact Ht|]. intros X. discriminate X.
Qed.

Lemma mod_comb x y r : (x + r) mod 4 = 0 -> y mod 4 = r -> (x + y) mod 4 = 0.
Proof. intros H1 H2. subst r. rewrite Z.add_mod in H1 by lia. rewrite Z.mod_mod in H1 by lia. rewrite <- Z.add_mod in H1 by lia. rewrite Z.add_mod by lia. rewrite Z.add_mod in H1 by lia. exact H1. Qed.

Lemma det_hyp z t B d2 dl dres By ad bd :
  term_sem (28 - z) t -> tok t = true -> phi (tna t) = z -> val (lbase (tL t)) <= val B -> val (tD t) = d2 ->
  (val B - val (lbase (tL t)) + dres) mod 4 = 0 -> 0 <= dl -> val By = val B + dl -> fits By = true ->
  eval (tL t) By = Some (ad, bd) -> val bd < val ad + 3 -> DetH (28 - z) z (val B) d2 dl dres.
Proof.
  intros Hs Tt Hz Hb Hd Hm Dl VBy FBy He Lt y Hy Hyr.
  destruct (Hs Tt) as ([HF [Hg [_ [_ _]]]] & _ & _ & R).
  destruct (eval_spec _ _ _ _ HF Hg FBy He) as (_ & _ & Va & Vb & Vt).
  set (y1 := val B - val (lbase (tL t)) + y).
  set (ym := val By - val (lbase (tL t))) in *.
  assert (Y0 : 0 <= y1) by (unfold y1; clear - Hb Hy; lia).
  assert (Ylt : y1 <= ym) by (unfold y1, ym; clear - Hy VBy; lia).
  assert (M : y1 mod 4 = 0) by (unfold y1; exact (mod_comb _ _ _ Hm Hyr)).
  assert (P1 : (val (lg (tL t)) - 1) * y1 <= (val (lg (tL t)) - 1) * ym) by (apply Z.mul_le_mono_nonneg_l; [clear - Hg; lia|exact Ylt]).
  assert (P2 : val (lg (tL t)) * y1 <= val (lg (tL t)) * ym) by (apply Z.mul_le_mono_nonneg_l; [clear - Hg; lia|exact Ylt]).
  pose proof (R y1 Y0 M ltac:(clear - P1 Va Vt; lia) ltac:(clear - P1 P2 Va Vb Lt; lia)) as X.
  rewrite Hz, Hd in X.
  replace (val B + y) with (val (lbase (tL t)) + y1) by (unfold y1; ring).
  exact X.
Qed.

(** One application of a block lemma, all premises in integers. *)
Lemma apply_ent z c e :
  lv_ok z c -> ent_ok e -> phi (ez e) = z -> phi (ec e) = val (lc c) -> phi (era e) = val (la c) mod 4 -> phi (erb e) = val (lb c) mod 4 ->
  phi (eGm e) <= val (lg c) -> reg e (val (lb c)) (val (la c) + val (lb c)) (val (lg c)) ->
  val (lthr c) + (val (lg c) - 1) * phi (elast e) <= val (la c) ->
  (edet e = true -> DetH (28 - z) z (val (lbase c)) (phi (ed2 e)) (phi (edlast e)) (phi (edres e))) ->
  Rch z (val (lbase c)) z (val (lbase c) + phi (eY e)).
Proof.
  intros [_ [Hg [Hth [Hs HR]]]] [Hb Hsem] Hz Hc Hra Hrb Hgm Hreg Hth2 Hdet.
  pose proof (Hsem (val (lbase c)) (val (la c)) (val (lb c)) (val (lg c))) as X. rewrite Hz in X. apply X; try assumption.
  - rewrite Hs, Hc. reflexivity.
  - symmetry. exact Hra.
  - symmetry. exact Hrb.
  - intros y Hy Hm. apply HR; [clear - Hy; lia|exact Hm|].
    assert (P : (val (lg c) - 1) * y <= (val (lg c) - 1) * phi (elast e)) by (apply Z.mul_le_mono_nonneg_l; [clear - Hg; lia|apply Hy]).
    clear - P Hth2. lia.
Qed.

Lemma sub2_val x : 2 <= phi x -> phi (x - 2)%uint63 = phi x - 2.
Proof. intros H. rewrite sub_spec, wB63. change (phi 2%uint63) with 2. apply Z.mod_small. pose proof (phi_bd63 x). lia. Qed.
Lemma add2_val x : phi x < 2305843009213693952 -> phi (x + 2)%uint63 = phi x + 2.
Proof. intros H. rewrite add_spec, wB63. change (phi 2%uint63) with 2. apply Z.mod_small. pose proof (phi_bd63 x). lia. Qed.

Lemma low2_det (B L : W) (r : int) : fits B = true -> -P118 <= val L < P118 -> (low2 (add (sub B L) (wc r)) =? 0)%uint63 = true -> (val B - val L + phi r) mod 4 = 0.
Proof.
  intros F BL H. apply eqb_true in H. rewrite low2_mod in H. change (phi 0%uint63) with 0 in H. apply fits_spec in F.
  pose proof (phi_bd63 r) as Br.
  assert (V1 : val (sub B L) = val B - val L) by (apply val_sub; clear - F BL; lia).
  assert (V2 : val (add (sub B L) (wc r)) = val B - val L + phi r) by (rewrite val_add; rewrite V1, val_wc; [reflexivity|clear - F BL Br; lia]).
  rewrite V2 in H. exact H.
Qed.

Tactic Notation "ifb" hyp(H) ident(name) := match type of H with (if ?c then _ else _) = _ => destruct c eqn:name end.
Ltac no H := injection H as <- <-; split; [assumption|intros ? X; discriminate X].

Lemma try_block_sound A0 B0 c s m os :
  st_ok A0 B0 s -> lv_ok (phi (sz s)) c -> lbase c = sB s -> try_block c s = (m, os) ->
  mem_ok m /\ forall s1, os = Some s1 -> st_ok A0 B0 s1 /\ post (sz s) (sB s) s1.
Proof.
  intros Hs Hc Eb H. pose proof Hs as (S1 & SB & Sz & Sm & S5 & S6 & S7).
  pose proof Hc as [HF [Hg [Hth [Hsum HR]]]].
  generalize HF; intros HF'. unfold lv_fits in HF'. apply andb_prop in HF'. destruct HF' as [HF' Fc]. apply andb_prop in HF'. destruct HF' as [HF' Fth]. apply andb_prop in HF'. destruct HF' as [HF' _]. apply andb_prop in HF'. destruct HF' as [HF' Fg]. apply andb_prop in HF'. destruct HF' as [Fa Fb].
  unfold try_block in H. cbv zeta in H.
  ifb H C1; [no H|].
  apply orb_false_iff in C1. destruct C1 as [C1 C1d]. apply orb_false_iff in C1. destruct C1 as [C1 _]. apply orb_false_iff in C1. destruct C1 as [_ _].
  apply negb_false_iff in C1d. apply Uint63.eqb_spec in C1d.
  assert (VS : val (add (la c) (lb c)) = val (la c) + val (lb c)) by (apply val_add2; assumption).
  set (S := add (la c) (lb c)) in *.
  ifb H C2; [no H|].
  apply orb_false_iff in C2. destruct C2 as [C2 _]. apply orb_false_iff in C2. destruct C2 as [C2 _]. apply orb_false_iff in C2. destruct C2 as [C2 C2d]. apply orb_false_iff in C2. destruct C2 as [C2 C2c]. apply orb_false_iff in C2. destruct C2 as [C2a C2b].
  apply negb_false_iff in C2a, C2b, C2c, C2d. apply leb_spec_W in C2a, C2b, C2c, C2d.
  change (val (wc 0)) with 0 in C2a, C2c.
  assert (E96 : val (mkW 8589934592 0) = 79228162514264337593543950336) by reflexivity. rewrite E96 in C2b. clear E96.
  assert (VS28 : val (mulk 268435456 S) = PP * val S).
  { rewrite val_mulk; change (phi 268435456%uint63) with 268435456; [reflexivity|clear - C2b C2c; lia]. }
  assert (Vb28 : val (mulk 268435456 (lb c)) = PP * val (lb c)).
  { rewrite val_mulk; change (phi 268435456%uint63) with 268435456; [reflexivity|clear - C2a C2b C2d; lia]. }
  generalize (fxdiv S (lg c)) H. intros w H'. clear H. rename H' into H.
  generalize (fxdiv (lb c) (lg c)) H. intros bt H'. clear H. rename H' into H.
  ifb H C3; [no H|].
  apply orb_false_iff in C3. destruct C3 as [C3 C3d]. apply orb_false_iff in C3. destruct C3 as [C3 C3c]. apply orb_false_iff in C3. destruct C3 as [C3a C3b].
  apply leb_false in C3a, C3d. apply ltb_false in C3b, C3c.
  change (phi 288230376151711744%uint63) with 288230376151711744 in C3a.
  change (phi 1099511627776%uint63) with 1099511627776 in C3b.
  change (phi 64%uint63) with 64 in C3c.
  change (phi 1152921504606846976%uint63) with 1152921504606846976 in C3d.
  assert (Ewl : phi (w - 2)%uint63 = phi w - 2) by (apply sub2_val; clear - C3b; lia).
  assert (Ewh : phi (w + 2)%uint63 = phi w + 2) by (apply add2_val; clear - C3a; lia).
  assert (Ebl : phi (bt - 2)%uint63 = phi bt - 2) by (apply sub2_val; clear - C3c; lia).
  assert (Ebh : phi (bt + 2)%uint63 = phi bt + 2) by (apply add2_val; clear - C3d; lia).
  generalize (w - 2)%uint63 (w + 2)%uint63 (bt - 2)%uint63 (bt + 2)%uint63 Ewl Ewh Ebl Ebh H. clear Ewl Ewh Ebl Ebh H. intros wl wh bl bh Ewl Ewh Ebl Ebh H.
  destruct (mul_nn (wc wl) (lg c)) as [p1|] eqn:M1; [|cbv beta iota in H; no H].
  destruct (mul_nn (wc wh) (lg c)) as [p2|] eqn:M2; [|cbv beta iota in H; no H].
  destruct (mul_nn (wc bl) (lg c)) as [p3|] eqn:M3; [|cbv beta iota in H; no H].
  destruct (mul_nn (wc bh) (lg c)) as [p4|] eqn:M4; [|cbv beta iota in H; no H].
  cbv beta iota in H.
  ifb H C4; [|no H].
  destruct (mul_nn_spec _ _ _ M1) as [Ep1 _]. destruct (mul_nn_spec _ _ _ M2) as [Ep2 _]. destruct (mul_nn_spec _ _ _ M3) as [Ep3 _]. destruct (mul_nn_spec _ _ _ M4) as [Ep4 _].
  rewrite val_wc in Ep1, Ep2, Ep3, Ep4. clear M1 M2 M3 M4.
  apply andb_prop in C4. destruct C4 as [C4 C4d]. apply andb_prop in C4. destruct C4 as [C4 C4c]. apply andb_prop in C4. destruct C4 as [C4a C4b].
  apply leb_spec_W in C4a, C4b, C4c, C4d. rewrite VS28, Ep1 in C4a. rewrite VS28, Ep2 in C4b. rewrite Vb28, Ep3 in C4c. rewrite Vb28, Ep4 in C4d. rewrite VS in C4a, C4b.
  clear VS28 Vb28 Ep1 Ep2 Ep3 Ep4.
  destruct (env_of s) as [v t] eqn:Ev. cbv beta iota in H.
  destruct (env_of_spec _ _ _ _ _ Hs Ev) as (Vz & Ht & Hhas).
  assert (Hzv : phi (vz v) = 6 \/ phi (vz v) = 22) by (rewrite Vz; exact Sz).
  pose proof (bn_sound bfuel (sm s) v (mkCtx (lo (lc c)) (low2 (la c)) (low2 (lb c))) bt w Hzv Sm) as Rk.
  destruct (bn bfuel (sm s) v (mkCtx (lo (lc c)) (low2 (la c)) (low2 (lb c))) bt w) as [m1 oe] eqn:Bn. clear Bn.
  destruct Rk as [Mm1 He]. cbn [fst snd] in Mm1, He. cbv beta iota in H.
  destruct oe as [e|]; [|no H].
  specialize (He e eq_refl). cbv beta iota in H.
  ifb H C5; [|no H].
  destruct (mul_nn (sub (lg c) (wc 1)) (wc (elast e))) as [h|] eqn:M5; [|no H].
  destruct (mul_nn_spec _ _ _ M5) as [Eh _]. clear M5.
  rewrite val_wc in Eh. rewrite val_sub_c in Eh by (exact Fg || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in Eh.
  ifb H C6; [|no H].
  ifb H C7; [|no H].
  injection H as <- <-. split; [exact Mm1|]. intros s1 E. injection E as <-.
  pose proof He as [Hbd _]. pose proof Hbd as (_ & _ & _ & _ & _ & BY & MY & _ & _ & BDL & _).
  apply andb_prop in C5. destruct C5 as [C5 FDL]. apply andb_prop in C5. destruct C5 as [C5 _]. apply andb_prop in C5. destruct C5 as [C5 FBn]. apply andb_prop in C5. destruct C5 as [C5 CGm]. apply andb_prop in C5. destruct C5 as [C5 Creg]. apply andb_prop in C5. destruct C5 as [Ck _].
  unfold keyok in Ck. apply andb_prop in Ck. destruct Ck as [Ck Kd2]. apply andb_prop in Ck. destruct Ck as [Ck Kz]. apply andb_prop in Ck. destruct Ck as [Ck Krb]. apply andb_prop in Ck. destruct Ck as [Kc Kra].
  cbn [xc xra xrb] in Kc, Kra, Krb. apply eqb_true in Kc, Kra, Krb, Kz, Kd2. rewrite low2_mod in Kra, Krb.
  apply leb_spec_W in CGm. rewrite val_wc in CGm.
  apply andb_prop in C6. destruct C6 as [C6 Fth2]. apply andb_prop in C6. destruct C6 as [C6 Fh].
  apply leb_spec_W in C6. rewrite (val_add2 _ _ Fth Fh), Eh in C6.
  assert (Vbn : val (add (sB s) (wc (eY e))) = val (sB s) + phi (eY e)).
  { apply val_add_c; [exact SB|clear - BY; lia]. }
  assert (Rb : Rch (phi (sz s)) (val (lbase c)) (phi (sz s)) (val (lbase c) + phi (eY e))).
  { apply (apply_ent (phi (sz s)) c e Hc He).
    - rewrite Kz, Vz. reflexivity.
    - rewrite Kc. symmetry. apply val_hi0. exact C1d.
    - exact Kra.
    - exact Krb.
    - exact CGm.
    - apply (reg_exact_sound e bl bh wl wh); try assumption; clear - C3c C3d Ebl Ebh; lia.
    - exact C6.
    - intros Ed. rewrite Ed in C7. cbn [negb orb] in C7.
      apply andb_prop in C7. destruct C7 as [C7 C7e]. apply andb_prop in C7. destruct C7 as [C7h C7m].
      destruct (Hhas C7h) as (Tt & Tz & Tb & Td).
      destruct (Ht Tt) as ([HFt [Hgt _]] & _ & _ & _).
      destruct (eval (tL t) (add (sB s) (wc (edlast e)))) as [[ad bd]|] eqn:Ee; [|discriminate C7e].
      apply ltb_spec_W in C7e.
      assert (Fad : fits ad = true).
      { destruct (eval_spec _ _ _ _ HFt Hgt FDL Ee) as (X & _). exact X. }
      rewrite val_add_c in C7e by (exact Fad || (vm_compute; reflexivity)). change (phi 3%uint63) with 3 in C7e.
      rewrite Eb. apply (det_hyp (phi (sz s)) t (sB s) (phi (ed2 e)) (phi (edlast e)) (phi (edres e)) (add (sB s) (wc (edlast e))) ad bd Ht Tt Tz Tb).
      + rewrite Td, Kd2. reflexivity.
      + destruct (lv_bounds _ HFt) as (_ & _ & _ & Bbs & _ & _). exact (low2_det _ _ _ SB Bbs C7m).
      + exact (proj1 (phi_bd63 (edlast e))).
      + apply val_add_c; [exact SB|clear - BDL; lia].
      + exact FDL.
      + exact Ee.
      + exact C7e. }
  rewrite Eb in Rb. rewrite <- Vbn in Rb.
  pose proof (phi_bd63 (eY e)) as BY0.
  assert (MY2 : (val (add (sB s) (wc (eY e))) - val (sB s)) mod 4 = 0).
  { rewrite Vbn. replace (val (sB s) + phi (eY e) - val (sB s)) with (phi (eY e)) by ring. exact MY. }
  destruct (adv_ok A0 B0 s (add (sB s) (wc (eY e))) (sY s) Hs Rb FBn ltac:(clear - Vbn BY0; lia) MY2) as [Ok Po].
  split.
  - exact (st_ok_mem _ _ _ m1 Ok Mm1).
  - exact Po.
Qed.

(** ** The recursion *)
Lemma slow_sweep_sound A0 B0 s : st_ok A0 B0 s -> st_ok A0 B0 (slow_sweep s) /\ post (sz s) (sB s) (slow_sweep s).
Proof.
  intros Hs. unfold slow_sweep. generalize (zsweep_sound Wfuel (phi (sz s)) (val (sB s))). intros Hz.
  destruct (zsweep Wfuel (phi (sz s)) (val (sB s))) as [[a1 b1]|]; [|split; [apply st_ok_stat; [exact Hs|reflexivity]|apply post_stat; reflexivity]].
  destruct (Hz _ _ eq_refl) as [R Ha]. clear Hz.
  destruct ((val (w_of_z b1) =? b1) && fits (w_of_z b1)) eqn:C; [|split; [apply st_ok_stat; [exact Hs|reflexivity]|apply post_stat; reflexivity]].
  apply andb_prop in C. destruct C as [C F]. apply Z.eqb_eq in C.
  assert (Pa : phi (of_Z a1) = a1) by (destruct Ha as [-> | ->]; reflexivity).
  split; [|apply post_stat; reflexivity].
  apply st_ok_hop; [exact Hs| rewrite Pa, C; exact R|exact F|rewrite Pa; exact Ha|reflexivity].
Qed.

Definition inv (L : Lv) (s : St) : Prop :=
  lv_ok (phi (sz s)) L /\ val (lbase L) <= val (sB s) /\ (val (sB s) - val (lbase L)) mod 4 = 0.

Lemma mod_add0 x y : x mod 4 = 0 -> y mod 4 = 0 -> (x + y) mod 4 = 0.
Proof. intros H1 H2. rewrite Z.add_mod, H1, H2 by lia. reflexivity. Qed.

Lemma post_trans z0 B s1 s2 : sstat s1 = 0%uint63 -> post z0 B s1 -> post (sz s1) (sB s1) s2 -> post z0 B s2.
Proof.
  intros E P1 P2 X. destruct (P1 E) as (E1 & L1 & M1). destruct (P2 X) as (E2 & L2 & M2).
  split; [rewrite E2; exact E1|]. split; [clear - L1 L2; lia|].
  replace (val (sB s2) - val B) with ((val (sB s2) - val (sB s1)) + (val (sB s1) - val B)) by ring. apply mod_add0; assumption.
Qed.

Section Node.
Variables (A0 B0 : Z) (f : nat).
Hypothesis IH : forall L s, st_ok A0 B0 s -> inv L s -> st_ok A0 B0 (node f L s) /\ post (sz s) (sB s) (node f L s).

Lemma child_sound c s : st_ok A0 B0 s -> lbase c = sB s -> (lv_fits c = true -> lv_ok (phi (sz s)) c) ->
  let X := (if lv_fits c then
      let '(m, os) := try_block c s in
      match os with
      | Some s1 => s1
      | None => node f c (set_mem s m)
      end
    else slow_sweep s) in
  st_ok A0 B0 X /\ post (sz s) (sB s) X.
Proof.
  intros Hs Eb Hc. cbv zeta. destruct (lv_fits c) eqn:F; [|apply slow_sweep_sound; exact Hs].
  specialize (Hc eq_refl).
  destruct (try_block c s) as [m os] eqn:T. destruct (try_block_sound _ _ _ _ _ _ Hs Hc Eb T) as [Hm Ho].
  destruct os as [s1|]; [exact (Ho s1 eq_refl)|].
  apply (IH c (set_mem s m)); [apply st_ok_mem; assumption|].
  split; [exact Hc|]. cbn [sB set_mem]. rewrite Eb. split; [clear; lia|]. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma cont_sound L s s1 : st_ok A0 B0 s -> inv L s -> st_ok A0 B0 s1 -> post (sz s) (sB s) s1 ->
  let X := if (sstat s1 =? 0)%uint63 then node f L s1 else s1 in
  st_ok A0 B0 X /\ post (sz s) (sB s) X.
Proof.
  intros Hs [HL [Hl Hm]] H1 P1. cbv zeta. destruct (sstat s1 =? 0)%uint63 eqn:C; [|split; assumption].
  apply Uint63.eqb_spec in C. destruct (P1 C) as (E & L1 & M1).
  assert (I1 : inv L s1).
  { split; [rewrite E; exact HL|]. split; [clear - Hl L1; lia|].
    replace (val (sB s1) - val (lbase L)) with ((val (sB s1) - val (sB s)) + (val (sB s) - val (lbase L))) by ring. apply mod_add0; assumption. }
  destruct (IH L s1 H1 I1) as [R1 R2]. split; [exact R1|]. eapply post_trans; [exact C|exact P1|exact R2].
Qed.
End Node.

Lemma stay_post z0 B s : sz s = z0 -> sB s = B -> post z0 B s.
Proof. intros <- <- _. split; [reflexivity|]. split; [lia|]. rewrite Z.sub_diag. reflexivity. Qed.

Theorem node_sound A0 B0 f : forall L s, st_ok A0 B0 s -> inv L s -> st_ok A0 B0 (node f L s) /\ post (sz s) (sB s) (node f L s).
Proof.
  induction f as [|f IH]; intros L s Hs HI.
  { cbn [node]. split; [apply st_ok_stat; [exact Hs|reflexivity]|apply post_stat; reflexivity]. }
  cbn [node]. pose proof HI as [HL [Hl Hm]]. pose proof HL as [HF [Hg [Hth [Hsum HR]]]].
  pose proof Hs as (S1 & SB & Sz & Sm & S5 & S6 & S7).
  destruct (eval L (sB s)) as [[a b]|] eqn:He; [|split; [exact Hs|apply stay_post; reflexivity]].
  destruct (eval_spec _ _ _ _ HF Hg SB He) as (Fa & Fb & Va & Vb & Vt).
  assert (V3 : val (add a (wc 3)) = val a + 3) by (rewrite val_add_c by (exact Fa || (vm_compute; reflexivity)); reflexivity).
  assert (Rstep : forall s1, st_ok A0 B0 s1 /\ post (sz s) (sB s) s1 ->
     st_ok A0 B0 (if (sstat s1 =? 0)%uint63 then node f L s1 else s1) /\ post (sz s) (sB s) (if (sstat s1 =? 0)%uint63 then node f L s1 else s1)).
  { intros s1 [H1 P1]. exact (cont_sound A0 B0 f IH L s s1 Hs HI H1 P1). }
  destruct (ltb (add a (wc 3)) b) eqn:C1.
  { apply Rstep. apply (child_sound A0 B0 f IH); [exact Hs|reflexivity|].
    intros F. apply (lvD _ L (sB s) a b HL SB Hl Hm He); [|exact F]. apply ltb_spec_W in C1. clear - C1 V3. lia. }
  apply ltb_false_W in C1.
  destruct (eqb (add a (wc 3)) b) eqn:C2.
  { apply eqb_spec_W in C2. rewrite V3 in C2. split; [|apply post_stat; reflexivity].
    assert (R : Rch A0 B0 (val a) (val a + 3)).
    { rewrite C2. eapply Rch_trans; [exact S1|]. exact (Rch_at _ L _ _ _ HL SB Hl Hm He). }
    exact (conj S1 (conj SB (conj Sz (conj Sm (conj S5 (conj S6 (fun _ => R))))))). }
  apply eqb_false_W in C2. rewrite V3 in C2.
  destruct (ltb b (wc 5)) eqn:C3; [apply slow_sweep_sound; exact Hs|].
  apply ltb_false_W in C3. rewrite val_wc in C3. change (phi 5%uint63) with 5 in C3.
  destruct ((low2 b) land 1 =? 1)%uint63 eqn:Od.
  - destruct (eqb (add a (wc 1)) b || negb (leb (add b (wc 1)) a) || negb (eqb (lg L) (wc 1) || leb (lthr L) (add b (wc 1)))) eqn:C4; [apply slow_sweep_sound; exact Hs|].
    apply orb_false_iff in C4. destruct C4 as [C4 C6]. apply orb_false_iff in C4. destruct C4 as [_ C5].
    apply negb_false_iff in C5, C6. apply leb_spec_W in C5. rewrite val_add_c in C5 by (exact Fb || (vm_compute; reflexivity)). change (phi 1%uint63) with 1 in C5.
    apply Rstep. apply (child_sound A0 B0 f IH); [exact Hs|destruct (low2 (add (sub a b) (wc 5)) =? 2)%uint63; reflexivity|].
    intros F. apply (lvUV _ L (sB s) a b _ HL SB Hl Hm He); try assumption.
    + apply low2_odd. exact Od.
    + apply orb_prop in C6. destruct C6 as [C6|C6].
      * left. apply eqb_spec_W in C6. rewrite C6. reflexivity.
      * right. apply leb_spec_W in C6. rewrite val_add_c in C6 by (exact Fb || (vm_compute; reflexivity)). exact C6.
    + apply low2_u; assumption.
    + apply low2_v; assumption.
  - destruct (lv_fits (rebase L a b (sB s)) && fits (add (lc L) (wc 7)) && fits (sub (lc L) (wc 2))) eqn:C4; [|apply slow_sweep_sound; exact Hs].
    apply andb_prop in C4. destruct C4 as [C4 F2]. apply andb_prop in C4. destruct C4 as [_ F7].
    apply Rstep. apply do_stop_sound.
    + exact Hs.
    + exact (rebase_ok _ L (sB s) a b HL SB Hl Hm He).
    + reflexivity.
    + exact Vt.
    + cbn [lb la rebase]. clear - C1 C2 V3. lia.
    + apply low2_even. exact Od.
    + exact F7.
    + exact F2.
Qed.

Lemma top_sound A0 B0 f : forall s, st_ok A0 B0 s -> st_ok A0 B0 (top f s).
Proof.
  induction f as [|f IH]; intros s Hs; [exact Hs|]. cbn [top].
  pose proof Hs as (_ & SB & Sz & _).
  assert (I : inv (root (sz s) (sB s)) (set_stat s 0)).
  { split; [exact (root_ok _ _ SB Sz)|]. cbn [sB set_stat lbase root]. split; [clear; lia|]. rewrite Z.sub_diag. reflexivity. }
  destruct (node_sound A0 B0 Nfuel _ _ (st_ok_stat _ _ s 0%uint63 Hs eq_refl) I) as [R _].
  destruct (sstat (node Nfuel (root (sz s) (sB s)) (set_stat s 0)) =? 2)%uint63; [|exact R].
  destruct (leb _ _); [exact R|apply IH; exact R].
Qed.

Lemma top2_sound A0 B0 f : forall s, st_ok A0 B0 s -> st_ok A0 B0 (top2 f s).
Proof.
  induction f as [|f IH]; intros s Hs; [exact Hs|]. cbn [top2].
  pose proof (top_sound A0 B0 Tfuel s Hs) as R.
  destruct ((sstat (top Tfuel s) =? 2)%uint63 && ltb (sB (top Tfuel s)) (sY (top Tfuel s))); [apply IH; exact R|exact R].
Qed.

Lemma start_ok z B Y : (phi z = 6 \/ phi z = 22) -> fits B = true -> st_ok (phi z) (val B) (start z B Y).
Proof.
  intros Hz F. refine (conj (Rch_refl _ _) (conj F (conj Hz (conj (mem0_ok _) (conj _ (conj _ _)))))).
  - intros X. discriminate X.
  - intros X. discriminate X.
  - intros X. assert (E : (sstat (start z B Y) =? 3)%uint63 = false) by reflexivity. rewrite X in E. discriminate E.
Qed.

(** ** What a run proves *)
Definition good (z : int) (B : W) : bool := ((z =? 6)%uint63 || (z =? 22)%uint63) && fits B.
Lemma good_spec z B : good z B = true -> (phi z = 6 \/ phi z = 22) /\ fits B = true.
Proof.
  unfold good. intros H. apply andb_prop in H. destruct H as [H F]. split; [|exact F].
  apply orb_prop in H. destruct H as [H|H]; apply eqb_true in H; [left|right]; exact H.
Qed.

Theorem run_seg_sound z B z1 Y : good z B = true -> run_seg z B z1 Y = true -> Rch (phi z) (val B) (phi z1) (val Y).
Proof.
  intros G H. destruct (good_spec _ _ G) as [Hz F].
  pose proof (top2_sound _ _ Tfuel _ (start_ok z B Y Hz F)) as (S1 & _).
  unfold run_seg, run in H. cbv zeta in H. apply andb_prop in H. destruct H as [E1 E2].
  apply eqb_true in E1. apply eqb_spec_W in E2. rewrite E1, E2 in S1. exact S1.
Qed.

Definition run_halt (z : int) (B Y : W) : bool := (sstat (run z B Y) =? 3)%uint63.
Theorem run_halt_sound z B Y : good z B = true -> run_halt z B Y = true -> Rch (phi z) (val B) (val (sha (run z B Y))) (val (sha (run z B Y)) + 3).
Proof.
  intros G H. destruct (good_spec _ _ G) as [Hz F].
  pose proof (top2_sound _ _ Tfuel _ (start_ok z B Y Hz F)) as (_ & _ & _ & _ & _ & _ & S7).
  apply S7. apply Uint63.eqb_spec in H. exact H.
Qed.

Definition run_halt_at (z : int) (B Y a : W) : bool :=
  let s := run z B Y in (sstat s =? 3)%uint63 && eqb (sha s) a.
Theorem run_halt_at_sound z B Y a : good z B = true -> run_halt_at z B Y a = true -> Rch (phi z) (val B) (val a) (val a + 3).
Proof.
  intros G H. unfold run_halt_at in H. cbv zeta in H. apply andb_prop in H. destruct H as [H E].
  apply eqb_spec_W in E. rewrite <- E. apply run_halt_sound; [exact G|exact H].
Qed.
