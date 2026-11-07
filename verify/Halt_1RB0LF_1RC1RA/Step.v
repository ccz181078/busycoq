(** One letter along an affine level, and its soundness. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Num Big Map Walk.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Lemma L_u a b : 5 <= b -> b <= a - 1 -> b mod 2 = 1 -> (a-b+5) mod 4 = 2 ->
  aStep a b = Some (a-b+11, 2*b-4, 4*b*(a+b)-11*a+29*b+13).
Proof.
  intros H1 H2 H3 H4. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1); [lia|]. destruct (Z.eqb_spec b 3); [lia|].
  rewrite H3. rewrite Z.eqb_refl. destruct (Z.eqb_spec b (a+1)); [lia|].
  rewrite H4. reflexivity.
Qed.
Lemma L_v a b : 5 <= b -> b <= a - 1 -> b mod 2 = 1 -> (a-b+5) mod 4 <> 2 ->
  aStep a b = Some (a-b+19, 2*b-8, 4*b*(a+b)-19*a+37*b-29).
Proof.
  intros H1 H2 H3 H4. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1); [lia|]. destruct (Z.eqb_spec b 3); [lia|].
  rewrite H3. rewrite Z.eqb_refl. destruct (Z.eqb_spec b (a+1)); [lia|].
  destruct (Z.eqb_spec ((a-b+5) mod 4) 2); [lia|]. reflexivity.
Qed.
Lemma L_w a b : 2 <= b -> b <= a + 2 -> b mod 2 <> 1 -> (a-b) mod 4 = 2 ->
  aStep a b = Some (6, a+b+7, 2*a*a+6*b*b+39*a-9*b+378).
Proof.
  intros H1 H2 H3 H4. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [E|]. { subst b. change (1 mod 2) with 1 in H3. lia. }
  destruct (Z.eqb_spec b 3) as [E|]. { subst b. change (3 mod 2) with 1 in H3. lia. }
  destruct (Z.eqb_spec (b mod 2) 1); [lia|]. rewrite H4. reflexivity.
Qed.
Lemma L_x a b : 2 <= b -> b <= a + 2 -> b mod 2 <> 1 -> (a-b) mod 4 <> 2 ->
  aStep a b = Some (22, a+b-2, 2*a*a+6*b*b+39*a-9*b+274).
Proof.
  intros H1 H2 H3 H4. rewrite L_tail by lia.
  destruct (Z.eqb_spec b 1) as [E|]. { subst b. change (1 mod 2) with 1 in H3. lia. }
  destruct (Z.eqb_spec b 3) as [E|]. { subst b. change (3 mod 2) with 1 in H3. lia. }
  destruct (Z.eqb_spec (b mod 2) 1); [lia|].
  destruct (Z.eqb_spec ((a-b) mod 4) 2); [lia|]. reflexivity.
Qed.

Lemma aff4 v g y : y mod 4 = 0 -> (v + g * y) mod 4 = v mod 4.
Proof.
  intros H. assert (E : y = (y / 4) * 4) by (Z.div_mod_to_equations; lia).
  rewrite E. replace (v + g * (y / 4 * 4)) with (v + (g * (y/4)) * 4) by ring. apply Z.mod_add. lia.
Qed.
Lemma aff2 v g y : y mod 4 = 0 -> (v + g * y) mod 2 = v mod 2.
Proof.
  intros H. assert (E : y = (y / 4) * 4) by (Z.div_mod_to_equations; lia).
  rewrite E. replace (v + g * (y / 4 * 4)) with (v + (g * (y/4) * 2) * 2) by ring. apply Z.mod_add. lia.
Qed.

Lemma Reach_conv a b a1 b1 n r a2 b2 n2 r2 : Reach a b a1 b1 n r -> a1 = a2 -> b1 = b2 -> n = n2 -> r = r2 -> Reach a b a2 b2 n2 r2.
Proof. intros H -> -> -> ->. exact H. Qed.

Inductive SR := SNext (L : Lev) | STerm (S : Sum) | SConc | SHaltA | SFail.

Definition odd4 (r : int) : bool := (r =? 1)%uint63 || (r =? 3)%uint63.
Lemma odd4_spec x : odd4 (low2 x) = true <-> val x mod 2 = 1.
Proof.
  unfold odd4. rewrite orb_true_iff, !Uint63.eqb_spec. pose proof (phi_low2 x) as E. split.
  - intros [H|H]; rewrite H in E; [change (phi 1%uint63) with 1 in E|change (phi 3%uint63) with 3 in E]; Z.div_mod_to_equations; lia.
  - intros H. assert (E' : phi (low2 x) = 1 \/ phi (low2 x) = 3) by (rewrite E; Z.div_mod_to_equations; lia).
    destruct E' as [E'|E']; [left|right]; apply to_Z_inj; rewrite E'; reflexivity.
Qed.
Lemma low2_eq2 x : (low2 x =? 2)%uint63 = true <-> val x mod 4 = 2.
Proof.
  rewrite Uint63.eqb_spec. rewrite <- phi_low2. split.
  - intros ->. reflexivity.
  - intros H. apply to_Z_inj. rewrite H. reflexivity.
Qed.

Definition stepA (B : W) (L : Lev) : SR :=
  let a := la L in let ga := lga L in let c := lc L in
  let b := sub (add B c) a in
  let gb := sub (wc 1) ga in
  let d := sub (sub b a) (wc 3) in
  if negb (fits b && fits gb) then SFail else
  if eqb d (wc 0) then SHaltA else
  if is_neg d then
    if odd4 (low2 b) then
      let g1 := sub b (wc 5) in
      let g2 := sub (sub a (wc 1)) b in
      if is_neg g1 || is_neg g2 then SConc else
      let h := bnd (bnd (lhi L) B g1 gb) B g2 (sub ga gb) in
      let k := mulk 4 c in
      match mulq b k, mulq gb k with
      | Some p0, Some p1 =>
        let L' :=
          if (low2 (add (sub a b) (wc 5)) =? 2)%uint63 then
            mkLev (add (sub a b) (wc 11)) (sub ga gb) (add c (wc 7)) B h (add (lU0 L) b) (add (lU1 L) gb)
              (add (sub (add (add (lW0 L) p0) (mulk 29 b)) (mulk 11 a)) (wc 13))
              (sub (add (lW1 L) (add p1 (mulk 29 gb))) (mulk 11 ga)) (add (llen L) (wc 1))
          else
            mkLev (add (sub a b) (wc 19)) (sub ga gb) (add c (wc 11)) B h (add (lU0 L) b) (add (lU1 L) gb)
              (sub (sub (add (add (lW0 L) p0) (mulk 37 b)) (mulk 19 a)) (wc 29))
              (sub (add (lW1 L) (add p1 (mulk 37 gb))) (mulk 19 ga)) (add (llen L) (wc 1)) in
        if lev_fits L' then SNext L' else SFail
      | _, _ => SFail
      end
    else
      let g1 := sub b (wc 2) in
      let g2 := sub (add a (wc 2)) b in
      if is_neg g1 || is_neg g2 then SConc else
      let h := bnd (bnd (lhi L) B g1 gb) B g2 (sub ga gb) in
      let W0 := sub (add (lW0 L) (mulk 39 a)) (mulk 9 b) in
      let W1 := sub (add (lW1 L) (mulk 39 ga)) (mulk 9 gb) in
      if fits W0 && fits W1 then
      if (low2 (sub a b) =? 2)%uint63 then
        STerm (mkSum B h (add c (wc 7)) (wc 6) (add (llen L) (wc 1)) (lU0 L) (lU1 L) (add W0 (wc 378)) W1 a ga b gb 2 6)
      else
        STerm (mkSum B h (sub c (wc 2)) (wc 22) (add (llen L) (wc 1)) (lU0 L) (lU1 L) (add W0 (wc 274)) W1 a ga b gb 2 6)
      else SFail
  else
    let h := bnd (lhi L) B (sub d (wc 1)) (sub gb ga) in
    let L' := mkLev (add (add a a) (wc 6)) (add ga ga) (add c (wc 3)) B h (lU0 L) (lU1 L)
                (add (sub (lW0 L) (mulk 30 a)) (wc 18)) (sub (lW1 L) (mulk 30 ga)) (add (llen L) (wc 1)) in
    if lev_fits L' then SNext L' else SFail.

(** Rewriting values of arithmetic on [W] down to Z, with range side conditions discharged from the context. *)
Create HintDb lits.
Lemma phi30 : phi 30%uint63 = 30. Proof. reflexivity. Qed.
Lemma phi29 : phi 29%uint63 = 29. Proof. reflexivity. Qed.
Lemma phi37 : phi 37%uint63 = 37. Proof. reflexivity. Qed.
Lemma phi11 : phi 11%uint63 = 11. Proof. reflexivity. Qed.
Lemma phi19 : phi 19%uint63 = 19. Proof. reflexivity. Qed.
Lemma phi39 : phi 39%uint63 = 39. Proof. reflexivity. Qed.
Lemma phi9 : phi 9%uint63 = 9. Proof. reflexivity. Qed.
Lemma phi4 : phi 4%uint63 = 4. Proof. reflexivity. Qed.
Lemma phi0 : phi 0%uint63 = 0. Proof. reflexivity. Qed.
Lemma phi1 : phi 1%uint63 = 1. Proof. reflexivity. Qed.
Lemma phi2 : phi 2%uint63 = 2. Proof. reflexivity. Qed.
Lemma phi3 : phi 3%uint63 = 3. Proof. reflexivity. Qed.
Lemma phi5 : phi 5%uint63 = 5. Proof. reflexivity. Qed.
Lemma phi6 : phi 6%uint63 = 6. Proof. reflexivity. Qed.
Lemma phi7 : phi 7%uint63 = 7. Proof. reflexivity. Qed.
Lemma phi13 : phi 13%uint63 = 13. Proof. reflexivity. Qed.
Lemma phi18 : phi 18%uint63 = 18. Proof. reflexivity. Qed.
Lemma phi22 : phi 22%uint63 = 22. Proof. reflexivity. Qed.
Lemma phi378 : phi 378%uint63 = 378. Proof. reflexivity. Qed.
Lemma phi274 : phi 274%uint63 = 274. Proof. reflexivity. Qed.
#[export] Hint Rewrite phi30 phi29 phi37 phi11 phi19 phi39 phi9 phi4 phi0 phi1 phi2 phi3 phi5 phi6 phi7 phi13 phi18 phi22 phi378 phi274 : lits.

Ltac vs :=
  repeat (first
    [ rewrite val_wc
    | rewrite val_add by (vs; lia)
    | rewrite val_sub by (vs; lia)
    | rewrite val_mulk by (vs; lia) ]);
  autorewrite with lits.

Ltac fitsb H :=
  let H1 := fresh "F" in
  repeat (apply andb_prop in H; destruct H as [H H1]; apply fits_spec in H1);
  apply fits_spec in H.

Lemma is_neg_false x : is_neg x = false -> 0 <= val x.
Proof.
  intros H. destruct (Z.le_gt_cases 0 (val x)) as [G|G]; [exact G|]. apply is_neg_spec in G. congruence.
Qed.
Lemma eqb_false x y : eqb x y = false -> val x <> val y.
Proof. intros H E. apply eqb_spec_W in E. congruence. Qed.

Section StepSound.
Variables (a0 : Z) (B : W) (L : Lev).
Hypothesis HL : lev_ok a0 L.
Hypothesis HB : val (lbase L) = val B.
Hypothesis HBh : val B <= val (lhi L).
Hypothesis HBf : fits B = true.

Lemma some_eq (x y z x' y' z' : Z): x = x' -> y = y' -> z = z' -> Some (x,y,z) = Some (x',y',z').
Proof. intros -> -> ->. reflexivity. Qed.

Lemma extend L' : lev_fits L' = true -> val (lbase L') = val B -> val (lhi L') <= val (lhi L) ->
  val (llen L') = val (llen L) + 1 ->
  (forall y, 0 <= y <= val (lhi L') - val B -> y mod 4 = 0 ->
     aStep (Aat L y) (val B + y + val (lc L) - Aat L y) =
       Some (Aat L' y, val B + y + val (lc L') - Aat L' y, Rat L' (val B + y) y - Rat L (val B + y) y)) ->
  lev_ok a0 L'.
Proof.
  intros Hf Hb Hh Hn Hs. split; [exact Hf|]. destruct HL as [_ HR].
  intros B' HB' Hm. rewrite Hb in *. set (y := B' - val B) in *.
  assert (EB : B' = val B + y) by (subst y; lia).
  pose proof (HR B') as R0. rewrite HB in R0. fold y in R0.
  specialize (R0 ltac:(lia) Hm).
  pose proof (Hs y ltac:(lia) Hm) as S.
  rewrite EB in R0. rewrite EB.
  pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R0 S) as R1.
  eapply Reach_conv; [exact R1|reflexivity|reflexivity|lia|ring].
Qed.

Local Ltac getfits :=
  destruct HL as [Hf HR]; unfold lev_fits in Hf; pose proof HBf as FB; apply fits_spec in FB;
  repeat (apply andb_prop in Hf; destruct Hf as [Hf ?]);
  repeat match goal with H : fits _ = true |- _ => apply fits_spec in H end.

Local Ltac common_setup :=
  pose proof HL as HL'; getfits;
  unfold stepA; cbv zeta;
  assert (Vb : val (sub (add B (lc L)) (la L)) = val B + val (lc L) - val (la L)) by (vs; lia);
  assert (Vg : val (sub (wc 1) (lga L)) = 1 - val (lga L)) by (vs; lia);
  set (a := la L) in *; set (ga := lga L) in *; set (c := lc L) in *;
  set (b := sub (add B c) a) in *; set (gb := sub (wc 1) ga) in *;
  assert (Vd : val (sub (sub b a) (wc 3)) = val b - val a - 3) by (vs; lia);
  set (d := sub (sub b a) (wc 3)) in *;
  destruct (fits b) eqn:Fb; [|cbn [andb negb]; discriminate];
  destruct (fits gb) eqn:Fgb; [|cbn [andb negb]; discriminate]; cbn [andb negb];
  apply fits_spec in Fb; apply fits_spec in Fgb;
  destruct (eqb d (wc 0)) eqn:E0; [discriminate|];
  apply eqb_false in E0; rewrite val_wc, phi0 in E0.

Local Ltac common_setup_h :=
  pose proof HL as HL'; getfits;
  unfold stepA; cbv zeta;
  assert (Vb : val (sub (add B (lc L)) (la L)) = val B + val (lc L) - val (la L)) by (vs; lia);
  assert (Vg : val (sub (wc 1) (lga L)) = 1 - val (lga L)) by (vs; lia);
  set (a := la L) in *; set (ga := lga L) in *; set (c := lc L) in *;
  set (b := sub (add B c) a) in *; set (gb := sub (wc 1) ga) in *;
  assert (Vd : val (sub (sub b a) (wc 3)) = val b - val a - 3) by (vs; lia);
  set (d := sub (sub b a) (wc 3)) in *;
  destruct (fits b) eqn:Fb; [|cbn [andb negb]; discriminate];
  destruct (fits gb) eqn:Fgb; [|cbn [andb negb]; discriminate]; cbn [andb negb];
  destruct (eqb d (wc 0)) eqn:E0;
  [ intros _; apply eqb_spec_W in E0; rewrite val_wc, phi0 in E0; lia
  | repeat match goal with
           | |- context [if ?x then _ else _] => destruct x
           | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
           end; discriminate ].

Local Ltac fits_list FL :=
  repeat (apply andb_prop in FL; destruct FL as [FL ?]);
  repeat match goal with H : fits _ = true |- _ => apply fits_spec in H end.

Lemma step_next L' : stepA B L = SNext L' ->
  lev_ok a0 L' /\ val (lbase L') = val B /\ val B <= val (lhi L').
Proof.
  common_setup.
  destruct (is_neg d) eqn:Nd.
  - apply is_neg_spec in Nd.
    destruct (odd4 (low2 b)) eqn:Odd; [|destruct (is_neg (sub b (wc 2)) || is_neg (sub (add a (wc 2)) b)); [discriminate|]; destruct (fits (sub (add (lW0 L) (mulk 39 a)) (mulk 9 b)) && fits (sub (add (lW1 L) (mulk 39 ga)) (mulk 9 gb))); [destruct ((low2 (sub a b) =? 2)%uint63); discriminate|discriminate]].
    apply odd4_spec in Odd.
    destruct (is_neg (sub b (wc 5))) eqn:N1; [cbn [orb]; discriminate|].
    destruct (is_neg (sub (sub a (wc 1)) b)) eqn:N2; [cbn [orb]; discriminate|]. cbn [orb].
    apply is_neg_false in N1. apply is_neg_false in N2.
    assert (V1 : val (sub b (wc 5)) = val b - 5) by (vs; lia). rewrite V1 in N1.
    assert (V2 : val (sub (sub a (wc 1)) b) = val a - 1 - val b) by (vs; lia). rewrite V2 in N2.
    assert (V3 : val (sub ga gb) = val ga - val gb) by (vs; lia).
    assert (V4 : val (mulk 4 c) = 4 * val c) by (vs; lia).
    set (g1 := sub b (wc 5)) in *. set (g2 := sub (sub a (wc 1)) b) in *.
    set (sl := sub ga gb) in *.
    set (h1 := bnd (lhi L) B g1 gb).
    destruct (bnd_spec (lhi L) B g1 gb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Bh1 Gh1].
    fold h1 in Bh1, Gh1.
    destruct (bnd_spec h1 B g2 sl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Bh2 Gh2].
    set (h := bnd h1 B g2 sl) in *.
    destruct (mulq b (mulk 4 c)) as [p0|] eqn:M0; [|discriminate].
    destruct (mulq gb (mulk 4 c)) as [p1|] eqn:M1; [|discriminate].
    destruct (mulq_spec _ _ _ M0) as [Ep0 Bp0]. destruct (mulq_spec _ _ _ M1) as [Ep1 Bp1].
    rewrite V4 in Ep0, Ep1.
    assert (V5 : val (add (sub a b) (wc 5)) = val a - val b + 5) by (vs; lia).
    assert (Vu0 : val (add (lU0 L) b) = val (lU0 L) + val b) by (vs; lia).
    assert (Vu1 : val (add (lU1 L) gb) = val (lU1 L) + val gb) by (vs; lia).
    assert (Vn : val (add (llen L) (wc 1)) = val (llen L) + 1) by (vs; lia).
    destruct (low2 (add (sub a b) (wc 5)) =? 2)%uint63 eqn:Sel.
    + apply low2_eq2 in Sel. rewrite V5 in Sel.
      match goal with |- context [lev_fits ?X] => set (L1 := X) end.
      destruct (lev_fits L1) eqn:FL; [|discriminate].
      intros Hs. injection Hs as <-.
      split; [|split; [reflexivity|exact (proj1 Bh2)]].
      assert (VA : val (add (sub a b) (wc 11)) = val a - val b + 11) by (vs; lia).
      assert (VC : val (add c (wc 7)) = val c + 7) by (vs; lia).
      assert (VW0 : val (add (sub (add (add (lW0 L) p0) (mulk 29 b)) (mulk 11 a)) (wc 13)) = val (lW0 L) + val p0 + 29 * val b - 11 * val a + 13) by (vs; lia).
      assert (VW1 : val (sub (add (lW1 L) (add p1 (mulk 29 gb))) (mulk 11 ga)) = val (lW1 L) + (val p1 + 29 * val gb) - 11 * val ga) by (vs; lia).
      apply extend; [exact FL|reflexivity|cbn [lhi L1]; lia|exact Vn|].
      intros y Hy Hm. cbn [lhi L1] in Hy.
      assert (EA : Aat L y = val a + val ga * y) by reflexivity.
      assert (EB : val B + y + val c - Aat L y = val b + val gb * y) by (rewrite EA, Vb, Vg; ring).
      fold c. rewrite EB, EA.
      pose proof (Gh1 y ltac:(lia)) as G1. pose proof (Gh2 y ltac:(lia)) as G2. rewrite V1 in G1. rewrite V2, V3 in G2.
      rewrite L_u; [|lia|lia| |].
      * unfold Aat, Rat. cbn [la lga lc lU0 lU1 lW0 lW1 L1]. rewrite VA, VC, VW0, VW1, Vu0, Vu1, V3, Ep0, Ep1, Vb, Vg.
        apply some_eq; ring.
      * rewrite aff2 by exact Hm. exact Odd.
      * replace (val a + val ga * y - (val b + val gb * y) + 5) with ((val a - val b + 5) + (val ga - val gb) * y) by ring.
        rewrite aff4 by exact Hm. exact Sel.
    + assert (Sel' : val (add (sub a b) (wc 5)) mod 4 <> 2).
      { intros X. apply low2_eq2 in X. congruence. }
      rewrite V5 in Sel'.
      match goal with |- context [lev_fits ?X] => set (L1 := X) end.
      destruct (lev_fits L1) eqn:FL; [|discriminate].
      intros Hs. injection Hs as <-.
      split; [|split; [reflexivity|exact (proj1 Bh2)]].
      assert (VA : val (add (sub a b) (wc 19)) = val a - val b + 19) by (vs; lia).
      assert (VC : val (add c (wc 11)) = val c + 11) by (vs; lia).
      assert (VW0 : val (sub (sub (add (add (lW0 L) p0) (mulk 37 b)) (mulk 19 a)) (wc 29)) = val (lW0 L) + val p0 + 37 * val b - 19 * val a - 29) by (vs; lia).
      assert (VW1 : val (sub (add (lW1 L) (add p1 (mulk 37 gb))) (mulk 19 ga)) = val (lW1 L) + (val p1 + 37 * val gb) - 19 * val ga) by (vs; lia).
      apply extend; [exact FL|reflexivity|cbn [lhi L1]; lia|exact Vn|].
      intros y Hy Hm. cbn [lhi L1] in Hy.
      assert (EA : Aat L y = val a + val ga * y) by reflexivity.
      assert (EB : val B + y + val c - Aat L y = val b + val gb * y) by (rewrite EA, Vb, Vg; ring).
      fold c. rewrite EB, EA.
      pose proof (Gh1 y ltac:(lia)) as G1. pose proof (Gh2 y ltac:(lia)) as G2. rewrite V1 in G1. rewrite V2, V3 in G2.
      rewrite L_v; [|lia|lia| |].
      * unfold Aat, Rat. cbn [la lga lc lU0 lU1 lW0 lW1 L1]. rewrite VA, VC, VW0, VW1, Vu0, Vu1, V3, Ep0, Ep1, Vb, Vg.
        apply some_eq; ring.
      * rewrite aff2 by exact Hm. exact Odd.
      * replace (val a + val ga * y - (val b + val gb * y) + 5) with ((val a - val b + 5) + (val ga - val gb) * y) by ring.
        rewrite aff4 by exact Hm. exact Sel'.
  - apply is_neg_false in Nd.
    assert (V1 : val (sub d (wc 1)) = val d - 1) by (vs; lia).
    assert (V3 : val (sub gb ga) = val gb - val ga) by (vs; lia).
    assert (VA : val (add (add a a) (wc 6)) = 2 * val a + 6) by (vs; lia).
    assert (VG : val (add ga ga) = 2 * val ga) by (vs; lia).
    assert (VC : val (add c (wc 3)) = val c + 3) by (vs; lia).
    assert (VW0 : val (add (sub (lW0 L) (mulk 30 a)) (wc 18)) = val (lW0 L) - 30 * val a + 18) by (vs; lia).
    assert (VW1 : val (sub (lW1 L) (mulk 30 ga)) = val (lW1 L) - 30 * val ga) by (vs; lia).
    assert (Vn : val (add (llen L) (wc 1)) = val (llen L) + 1) by (vs; lia).
    destruct (bnd_spec (lhi L) B (sub d (wc 1)) (sub gb ga) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Bh Gh].
    set (h := bnd (lhi L) B (sub d (wc 1)) (sub gb ga)) in *.
    match goal with |- context [lev_fits ?X] => set (L1 := X) end.
    destruct (lev_fits L1) eqn:FL; [|discriminate].
    intros Hs. injection Hs as <-.
    split; [|split; [reflexivity|exact (proj1 Bh)]].
    apply extend; [exact FL|reflexivity|cbn [lhi L1]; lia|exact Vn|].
    intros y Hy Hm. cbn [lhi L1] in Hy.
    assert (EA : Aat L y = val a + val ga * y) by reflexivity.
    assert (EB : val B + y + val c - Aat L y = val b + val gb * y) by (rewrite EA, Vb, Vg; ring).
    fold c. rewrite EB, EA.
    pose proof (Gh y ltac:(lia)) as G. rewrite V1, V3, Vd, Vg in G. rewrite Vg.
    rewrite L_D by (rewrite Vb in *; lia).
    unfold Aat, Rat. cbn [la lga lc lU0 lU1 lW0 lW1 L1]. rewrite VA, VG, VC, VW0, VW1, Vb.
    apply some_eq; ring.
Qed.

Lemma step_halt : stepA B L = SHaltA -> val B + val (lc L) - val (la L) = val (la L) + 3.
Proof.
  common_setup_h.
Qed.

Lemma step_term S : stepA B L = STerm S ->
  sum_ok a0 S /\ val (sbase S) = val B /\ val B <= val (shi S).
Proof.
  common_setup.
  destruct (is_neg d) eqn:Nd; cycle 1.
  { match goal with |- context [lev_fits ?X] => destruct (lev_fits X); discriminate end. }
  apply is_neg_spec in Nd.
  destruct (odd4 (low2 b)) eqn:Odd.
  { destruct (is_neg (sub b (wc 5)) || is_neg (sub (sub a (wc 1)) b)); [discriminate|].
    destruct (mulq b (mulk 4 c)); [|discriminate]. destruct (mulq gb (mulk 4 c)); [|discriminate].
    match goal with |- context [lev_fits ?X] => destruct (lev_fits X); discriminate end. }
  assert (Ev : val b mod 2 <> 1). { intros X. apply odd4_spec in X. congruence. }
  destruct (is_neg (sub b (wc 2))) eqn:N1; [cbn [orb]; discriminate|].
  destruct (is_neg (sub (add a (wc 2)) b)) eqn:N2; [cbn [orb]; discriminate|]. cbn [orb].
  apply is_neg_false in N1. apply is_neg_false in N2.
  assert (V1 : val (sub b (wc 2)) = val b - 2) by (vs; lia). rewrite V1 in N1.
  assert (V2 : val (sub (add a (wc 2)) b) = val a + 2 - val b) by (vs; lia). rewrite V2 in N2.
  assert (V3 : val (sub ga gb) = val ga - val gb) by (vs; lia).
  set (g1 := sub b (wc 2)) in *. set (g2 := sub (add a (wc 2)) b) in *. set (sl := sub ga gb) in *.
  set (h1 := bnd (lhi L) B g1 gb).
  destruct (bnd_spec (lhi L) B g1 gb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Bh1 Gh1].
  fold h1 in Bh1, Gh1.
  destruct (bnd_spec h1 B g2 sl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Bh2 Gh2].
  set (h := bnd h1 B g2 sl) in *.
  assert (VW0 : val (sub (add (lW0 L) (mulk 39 a)) (mulk 9 b)) = val (lW0 L) + 39 * val a - 9 * val b) by (vs; lia).
  assert (VW1 : val (sub (add (lW1 L) (mulk 39 ga)) (mulk 9 gb)) = val (lW1 L) + 39 * val ga - 9 * val gb) by (vs; lia).
  set (W0 := sub (add (lW0 L) (mulk 39 a)) (mulk 9 b)) in *.
  set (W1 := sub (add (lW1 L) (mulk 39 ga)) (mulk 9 gb)) in *.
  destruct (fits W0) eqn:FW0; [|cbn [andb]; discriminate].
  destruct (fits W1) eqn:FW1; [|cbn [andb]; discriminate]. cbn [andb].
  apply fits_spec in FW0. apply fits_spec in FW1.
  assert (Vn : val (add (llen L) (wc 1)) = val (llen L) + 1) by (vs; lia).
  destruct HL' as [_ HRR].
  destruct (low2 (sub a b) =? 2)%uint63 eqn:Sel.
  - apply low2_eq2 in Sel.
    assert (V5 : val (sub a b) = val a - val b) by (vs; lia). rewrite V5 in Sel.
    assert (VW0' : val (add W0 (wc 378)) = val W0 + 378) by (vs; lia).
    assert (VC : val (add c (wc 7)) = val c + 7) by (vs; lia).
    intros Hs. injection Hs as <-.
    split; [|split; [reflexivity|cbn [shi]; lia]].
    intros B' HB' Hm. cbn [sbase shi] in HB', Hm. set (y := B' - val B) in *.
    pose proof (HRR B') as R0. rewrite HB in R0. fold y in R0. specialize (R0 ltac:(lia) Hm).
    assert (EA : Aat L y = val a + val ga * y) by reflexivity.
    assert (EB : B' + val c - Aat L y = val b + val gb * y) by (rewrite EA, Vb, Vg; subst y; ring).
    fold c in R0. rewrite EB, EA in R0.
    pose proof (Gh1 y ltac:(lia)) as G1. pose proof (Gh2 y ltac:(lia)) as G2. rewrite V1 in G1. rewrite V2, V3 in G2.
    assert (St : aStep (val a + val ga * y) (val b + val gb * y) = Some (6, val a + val ga * y + (val b + val gb * y) + 7,
       2 * (val a + val ga * y) * (val a + val ga * y) + 6 * (val b + val gb * y) * (val b + val gb * y) + 39 * (val a + val ga * y) - 9 * (val b + val gb * y) + 378)).
    { apply L_w; [lia|lia| |].
      - rewrite aff2 by exact Hm. exact Ev.
      - replace (val a + val ga * y - (val b + val gb * y)) with ((val a - val b) + (val ga - val gb) * y) by ring.
        rewrite aff4 by exact Hm. exact Sel. }
    pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R0 St) as R1.
    eapply Reach_conv; [exact R1| | | |].
    + cbn [sna0]. rewrite val_wc. autorewrite with lits. reflexivity.
    + cbn [sdelta]. rewrite VC, Vb, Vg. subst y. ring.
    + cbn [slen]. rewrite Vn. reflexivity.
    + unfold sum_cost, Rat. cbn [sbase sU0 sU1 sW0 sW1 sae sgae sbe sgbe sca scb]. rewrite VW0', VW0, VW1, Vb, Vg.
      autorewrite with lits. subst y. ring.
  - assert (Sel' : val (sub a b) mod 4 <> 2).
    { intros X. apply low2_eq2 in X. congruence. }
    assert (V5 : val (sub a b) = val a - val b) by (vs; lia). rewrite V5 in Sel'.
    assert (VW0' : val (add W0 (wc 274)) = val W0 + 274) by (vs; lia).
    assert (VC : val (sub c (wc 2)) = val c - 2) by (vs; lia).
    intros Hs. injection Hs as <-.
    split; [|split; [reflexivity|cbn [shi]; lia]].
    intros B' HB' Hm. cbn [sbase shi] in HB', Hm. set (y := B' - val B) in *.
    pose proof (HRR B') as R0. rewrite HB in R0. fold y in R0. specialize (R0 ltac:(lia) Hm).
    assert (EA : Aat L y = val a + val ga * y) by reflexivity.
    assert (EB : B' + val c - Aat L y = val b + val gb * y) by (rewrite EA, Vb, Vg; subst y; ring).
    fold c in R0. rewrite EB, EA in R0.
    pose proof (Gh1 y ltac:(lia)) as G1. pose proof (Gh2 y ltac:(lia)) as G2. rewrite V1 in G1. rewrite V2, V3 in G2.
    assert (St : aStep (val a + val ga * y) (val b + val gb * y) = Some (22, val a + val ga * y + (val b + val gb * y) - 2,
       2 * (val a + val ga * y) * (val a + val ga * y) + 6 * (val b + val gb * y) * (val b + val gb * y) + 39 * (val a + val ga * y) - 9 * (val b + val gb * y) + 274)).
    { apply L_x; [lia|lia| |].
      - rewrite aff2 by exact Hm. exact Ev.
      - replace (val a + val ga * y - (val b + val gb * y)) with ((val a - val b) + (val ga - val gb) * y) by ring.
        rewrite aff4 by exact Hm. exact Sel'. }
    pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R0 St) as R1.
    eapply Reach_conv; [exact R1| | | |].
    + cbn [sna0]. rewrite val_wc. autorewrite with lits. reflexivity.
    + cbn [sdelta]. rewrite VC, Vb, Vg. subst y. ring.
    + cbn [slen]. rewrite Vn. reflexivity.
    + unfold sum_cost, Rat. cbn [sbase sU0 sU1 sW0 sW1 sae sgae sbe sgbe sca scb]. rewrite VW0', VW0, VW1, Vb, Vg.
      autorewrite with lits. subst y. ring.
Qed.
End StepSound.

Lemma step_next' a0 B L L' : lev_ok a0 L -> val (lbase L) = val B -> val B <= val (lhi L) -> fits B = true -> stepA B L = SNext L' ->
  lev_ok a0 L' /\ val (lbase L') = val B /\ val B <= val (lhi L').
Proof. intros; eapply step_next; eauto. Qed.
Lemma step_term' a0 B L T : lev_ok a0 L -> val (lbase L) = val B -> val B <= val (lhi L) -> fits B = true -> stepA B L = STerm T ->
  sum_ok a0 T /\ val (sbase T) = val B /\ val B <= val (shi T).
Proof. intros; eapply step_term; eauto. Qed.
Lemma step_halt' a0 B L : lev_ok a0 L -> val (lbase L) = val B -> val B <= val (lhi L) -> fits B = true -> stepA B L = SHaltA ->
  val B + val (lc L) - val (la L) = val (la L) + 3.
Proof. intros; eapply step_halt; eauto. Qed.
