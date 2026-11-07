(** Whole sweeps: the deep part of a word, where only one start is valid, and the per-slot cache of levels. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Num Big Map Walk Step.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Lemma phi354 : phi 354%uint63 = 354. Proof. reflexivity. Qed.
Lemma phi250 : phi 250%uint63 = 250. Proof. reflexivity. Qed.
Lemma phi63 : phi 63%uint63 = 63. Proof. reflexivity. Qed.
Lemma phi774 : phi 774%uint63 = 774. Proof. reflexivity. Qed.
Lemma phi136 : phi 136%uint63 = 136. Proof. reflexivity. Qed.
Lemma phi174 : phi 174%uint63 = 174. Proof. reflexivity. Qed.
Lemma phi8 : phi 8%uint63 = 8. Proof. reflexivity. Qed.
#[export] Hint Rewrite phi354 phi250 phi63 phi774 phi136 phi174 phi8 : lits.

Inductive Out := OSum (S : Sum) | OHalt (a b U W n : W) | OFail.
Inductive CR := CNext (a b U W n : W) | CTerm (S : Sum) | CHalt | CFailC.

Definition term1 (B na0 b' n U W' : W) (ca : int) (ae : W) (cb : int) (be : W) : Sum :=
  mkSum B B (sub b' B) na0 n U (wc 0) W' (wc 0) ae (wc 0) be (wc 0) ca cb.

Definition cfits (a b U W n : W) : bool := fits a && fits b && fits U && fits W && fits n.

Definition stepC (B a b U W n : W) : CR :=
  let d := sub (sub b a) (wc 3) in
  let n1 := add n (wc 1) in
  if eqb d (wc 0) then CHalt else
  if is_neg d then
    if eqb b (wc 1) then
      if (low2 a =? 2)%uint63 then CTerm (term1 B (wc 6) (add a (wc 7)) n1 U (add (add W (mulk 39 a)) (wc 354)) 2 a 0 (wc 0))
      else CTerm (term1 B (wc 22) (sub a (wc 2)) n1 U (add (add W (mulk 39 a)) (wc 250)) 2 a 0 (wc 0))
    else if eqb b (wc 3) then
      if (low2 a =? 2)%uint63 then CTerm (term1 B (wc 6) (add a (wc 13)) n1 U (add (add W (mulk 63 a)) (wc 774)) 2 a 0 (wc 0))
      else if cfits (add a (wc 8)) (wc 2) U (add (add W a) (wc 136)) n1 then CNext (add a (wc 8)) (wc 2) U (add (add W a) (wc 136)) n1 else CFailC
    else if odd4 (low2 b) then
      if eqb b (add a (wc 1)) then CTerm (term1 B (wc 6) (add (add a b) (wc 2)) n1 U (add (add W (mulk 30 a)) (wc 174)) 8 a 0 (wc 0))
      else
        match mulq b (mulk 4 (sub (add a b) B)) with
        | Some p =>
          if (low2 (add (sub a b) (wc 5)) =? 2)%uint63 then
            let a' := add (sub a b) (wc 11) in let b' := sub (add b b) (wc 4) in
            let U' := add U b in let W' := add (sub (add (add W p) (mulk 29 b)) (mulk 11 a)) (wc 13) in
            if cfits a' b' U' W' n1 then CNext a' b' U' W' n1 else CFailC
          else
            let a' := add (sub a b) (wc 19) in let b' := sub (add b b) (wc 8) in
            let U' := add U b in let W' := sub (sub (add (add W p) (mulk 37 b)) (mulk 19 a)) (wc 29) in
            if cfits a' b' U' W' n1 then CNext a' b' U' W' n1 else CFailC
        | None => CFailC
        end
    else
      let W' := sub (add W (mulk 39 a)) (mulk 9 b) in
      if (low2 (sub a b) =? 2)%uint63 then
        CTerm (term1 B (wc 6) (add (add a b) (wc 7)) n1 U (add W' (wc 378)) 2 a 6 b)
      else
        CTerm (term1 B (wc 22) (sub (add a b) (wc 2)) n1 U (add W' (wc 274)) 2 a 6 b)
  else
    let a' := add (add a a) (wc 6) in let W' := add (sub W (mulk 30 a)) (wc 18) in
    if cfits a' d U W' n1 then CNext a' d U W' n1 else CFailC.

Definition is_reset (x : W) : bool := eqb x (wc 6) || eqb x (wc 22).

Definition F_tail : nat := Nat.pow 2 17.

Fixpoint walkC (fuel : nat) (B a b U W n : W) : Out :=
  match fuel with
  | O => OFail
  | S f =>
    match stepC B a b U W n with
    | CNext a' b' U' W' n' =>
      if is_reset a' then OSum (term1 B a' b' n' U' W' 0 (wc 0) 0 (wc 0))
      else walkC f B a' b' U' W' n'
    | CTerm T => OSum T
    | CHalt => OHalt a b U W n
    | CFailC => OFail
    end
  end.

Definition out_ok (a0 : Z) (B : W) (o : Out) : Prop :=
  match o with
  | OSum T => sum_ok a0 T /\ val (sbase T) <= val B <= val (shi T) /\ (val B - val (sbase T)) mod 4 = 0
  | OHalt a b U W n => val b = val a + 3 /\ Reach a0 (val B) (val a) (val b) (val n) (4 * val B * val U + val W)
  | OFail => True
  end.

Lemma term1_ok a0 B a b U W n na0 b' n' r W' ca ae cb be :
  Reach a0 (val B) (val a) (val b) (val n) (4 * val B * val U + val W) ->
  aStep (val a) (val b) = Some (val na0, val b', r) ->
  val n' = val n + 1 ->
  -P125 <= val b' - val B < P125 ->
  r = (val W' - val W) + phi ca * (val ae * val ae) + phi cb * (val be * val be) ->
  val (wc 0) = 0 ->
  out_ok a0 B (OSum (term1 B na0 b' n' U W' ca ae cb be)).
Proof.
  intros R St En Hb Er _. cbn [out_ok]. unfold term1. split; [|cbn [sbase shi]; split; [lia|rewrite Z.sub_diag; reflexivity]].
  intros B' HB' _. cbn [sbase shi] in HB'. assert (B' = val B) by lia. subst B'.
  pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R St) as R1.
  eapply Reach_conv; [exact R1|reflexivity| | |].
  - cbn [sdelta]. rewrite val_sub by exact Hb. ring.
  - cbn [slen]. lia.
  - unfold sum_cost. cbn [sU0 sU1 sW0 sW1 sae sgae sbe sgbe sca scb sbase]. rewrite val_wc. autorewrite with lits.
    rewrite Z.sub_diag. rewrite Er. ring.
Qed.

Local Ltac zm := Z.div_mod_to_equations; lia.

Lemma stepC_sound a0 B a b U W n :
  cfits a b U W n = true -> fits B = true ->
  Reach a0 (val B) (val a) (val b) (val n) (4 * val B * val U + val W) ->
  match stepC B a b U W n with
  | CNext a' b' U' W' n' => cfits a' b' U' W' n' = true /\ Reach a0 (val B) (val a') (val b') (val n') (4 * val B * val U' + val W')
  | CTerm T => out_ok a0 B (OSum T)
  | CHalt => out_ok a0 B (OHalt a b U W n)
  | CFailC => True
  end.
Proof.
  intros Hf HB R. unfold cfits in Hf.
  repeat (apply andb_prop in Hf; destruct Hf as [Hf ?]).
  repeat match goal with H : fits _ = true |- _ => apply fits_spec in H end.
  unfold stepC. cbv zeta.
  assert (Vd : val (sub (sub b a) (wc 3)) = val b - val a - 3) by (vs; lia).
  assert (Vn : val (add n (wc 1)) = val n + 1) by (vs; lia).
  set (d := sub (sub b a) (wc 3)) in *. set (n1 := add n (wc 1)) in *.
  destruct (eqb d (wc 0)) eqn:E0.
  { apply eqb_spec_W in E0. rewrite val_wc, phi0 in E0. cbn [out_ok]. split; [lia|exact R]. }
  apply eqb_false in E0. rewrite val_wc, phi0 in E0.
  destruct (is_neg d) eqn:Nd.
  2:{ apply is_neg_false in Nd.
      assert (St : aStep (val a) (val b) = Some (2 * val a + 6, val b - val a - 3, -30 * val a + 18)) by (apply L_D; lia).
      assert (VA : val (add (add a a) (wc 6)) = 2 * val a + 6) by (vs; lia).
      assert (VW : val (add (sub W (mulk 30 a)) (wc 18)) = val W - 30 * val a + 18) by (vs; lia).
      destruct (cfits (add (add a a) (wc 6)) d U (add (sub W (mulk 30 a)) (wc 18)) n1) eqn:Fx; [|exact I].
      split; [exact Fx|].
      pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R St) as R1.
      eapply Reach_conv; [exact R1|lia|lia|lia|rewrite VW; ring]. }
  apply is_neg_spec in Nd.
  assert (Hlt : val b < val a + 3) by lia.
  pose proof (L_tail _ _ Hlt) as St.
  destruct (eqb b (wc 1)) eqn:E1.
  { apply eqb_spec_W in E1. rewrite val_wc, phi1 in E1. rewrite E1 in St.
    rewrite Z.eqb_refl in St.
    destruct (low2 a =? 2)%uint63 eqn:Sel.
    - apply low2_eq2 in Sel. rewrite Sel, Z.eqb_refl in St.
      eapply term1_ok; [exact R| | | | | ]; try (vs; lia).
      + rewrite E1, St. vs. apply some_eq; reflexivity || lia.
      + vs. ring.
    - assert (Sel' : val a mod 4 <> 2). { intros X. apply low2_eq2 in X. congruence. }
      destruct (Z.eqb_spec (val a mod 4) 2); [lia|].
      eapply term1_ok; [exact R| | | | | ]; try (vs; lia).
      + rewrite E1, St. vs. apply some_eq; reflexivity || lia.
      + vs. ring. }
  apply eqb_false in E1. rewrite val_wc, phi1 in E1.
  destruct (Z.eqb_spec (val b) 1) as [X|_]; [lia|].
  destruct (eqb b (wc 3)) eqn:E3.
  { apply eqb_spec_W in E3. rewrite val_wc, phi3 in E3. rewrite E3 in St.
    rewrite Z.eqb_refl in St.
    destruct (low2 a =? 2)%uint63 eqn:Sel.
    - apply low2_eq2 in Sel. rewrite Sel, Z.eqb_refl in St.
      eapply term1_ok; [exact R| | | | | ]; try (vs; lia).
      + rewrite E3, St. vs. apply some_eq; reflexivity || lia.
      + vs. ring.
    - assert (Sel' : val a mod 4 <> 2). { intros X. apply low2_eq2 in X. congruence. }
      destruct (Z.eqb_spec (val a mod 4) 2); [lia|].
      assert (VA : val (add a (wc 8)) = val a + 8) by (vs; lia).
      assert (VW : val (add (add W a) (wc 136)) = val W + val a + 136) by (vs; lia).
      destruct (cfits (add a (wc 8)) (wc 2) U (add (add W a) (wc 136)) n1) eqn:Fx; [|exact I].
      split; [exact Fx|].
      assert (St' : aStep (val a) (val b) = Some (val a + 8, 2, val a + 136)) by (rewrite E3; exact St).
      pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R St') as R1.
      eapply Reach_conv; [exact R1|lia|vs; reflexivity|lia|rewrite VW; ring]. }
  apply eqb_false in E3. rewrite val_wc, phi3 in E3.
  destruct (Z.eqb_spec (val b) 3) as [X|_]; [lia|].
  destruct (odd4 (low2 b)) eqn:Odd.
  { apply odd4_spec in Odd. rewrite Odd, Z.eqb_refl in St.
    destruct (eqb b (add a (wc 1))) eqn:Et.
    { apply eqb_spec_W in Et. assert (Va1 : val (add a (wc 1)) = val a + 1) by (vs; lia). rewrite Va1 in Et.
      rewrite Et, Z.eqb_refl in St. rewrite <- Et in St.
      eapply term1_ok; [exact R| | | | | ]; try (vs; lia).
      + rewrite St. vs. apply some_eq; reflexivity || lia.
      + vs. ring. }
    apply eqb_false in Et. assert (Va1 : val (add a (wc 1)) = val a + 1) by (vs; lia). rewrite Va1 in Et.
    destruct (Z.eqb_spec (val b) (val a + 1)) as [X|_]; [lia|].
    assert (Vs : val (mulk 4 (sub (add a b) B)) = 4 * (val a + val b - val B)) by (vs; lia).
    destruct (mulq b (mulk 4 (sub (add a b) B))) as [p|] eqn:Mp; [|exact I].
    destruct (mulq_spec _ _ _ Mp) as [Ep Bp]. rewrite Vs in Ep.
    assert (V5 : val (add (sub a b) (wc 5)) = val a - val b + 5) by (vs; lia).
    destruct (low2 (add (sub a b) (wc 5)) =? 2)%uint63 eqn:Sel.
    - apply low2_eq2 in Sel. rewrite V5 in Sel. rewrite Sel, Z.eqb_refl in St.
      assert (VA : val (add (sub a b) (wc 11)) = val a - val b + 11) by (vs; lia).
      assert (VB : val (sub (add b b) (wc 4)) = 2 * val b - 4) by (vs; lia).
      assert (VU : val (add U b) = val U + val b) by (vs; lia).
      assert (VW : val (add (sub (add (add W p) (mulk 29 b)) (mulk 11 a)) (wc 13)) = val W + val p + 29 * val b - 11 * val a + 13) by (vs; lia).
      destruct (cfits (add (sub a b) (wc 11)) (sub (add b b) (wc 4)) (add U b) (add (sub (add (add W p) (mulk 29 b)) (mulk 11 a)) (wc 13)) n1) eqn:Fx; [|exact I].
      split; [exact Fx|].
      pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R St) as R1.
      eapply Reach_conv; [exact R1|lia|lia|lia|rewrite VU, VW, Ep; ring].
    - assert (Sel' : val (add (sub a b) (wc 5)) mod 4 <> 2). { intros X. apply low2_eq2 in X. congruence. }
      rewrite V5 in Sel'. destruct (Z.eqb_spec ((val a - val b + 5) mod 4) 2); [lia|].
      assert (VA : val (add (sub a b) (wc 19)) = val a - val b + 19) by (vs; lia).
      assert (VB : val (sub (add b b) (wc 8)) = 2 * val b - 8) by (vs; lia).
      assert (VU : val (add U b) = val U + val b) by (vs; lia).
      assert (VW : val (sub (sub (add (add W p) (mulk 37 b)) (mulk 19 a)) (wc 29)) = val W + val p + 37 * val b - 19 * val a - 29) by (vs; lia).
      destruct (cfits (add (sub a b) (wc 19)) (sub (add b b) (wc 8)) (add U b) (sub (sub (add (add W p) (mulk 37 b)) (mulk 19 a)) (wc 29)) n1) eqn:Fx; [|exact I].
      split; [exact Fx|].
      pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R St) as R1.
      eapply Reach_conv; [exact R1|lia|lia|lia|rewrite VU, VW, Ep; ring]. }
  assert (Ev : val b mod 2 <> 1). { intros X. apply odd4_spec in X. congruence. }
  destruct (Z.eqb_spec (val b mod 2) 1) as [X|_]; [lia|].
  assert (VW : val (sub (add W (mulk 39 a)) (mulk 9 b)) = val W + 39 * val a - 9 * val b) by (vs; lia).
  set (W' := sub (add W (mulk 39 a)) (mulk 9 b)) in *.
  destruct (low2 (sub a b) =? 2)%uint63 eqn:Sel.
  - apply low2_eq2 in Sel. assert (V5 : val (sub a b) = val a - val b) by (vs; lia). rewrite V5 in Sel. rewrite Sel, Z.eqb_refl in St.
    eapply term1_ok; [exact R| | | | | ]; try (vs; lia).
    + rewrite St. vs. apply some_eq; reflexivity || lia.
    + vs. rewrite VW. ring.
  - assert (Sel' : val (sub a b) mod 4 <> 2). { intros X. apply low2_eq2 in X. congruence. }
    assert (V5 : val (sub a b) = val a - val b) by (vs; lia). rewrite V5 in Sel'.
    destruct (Z.eqb_spec ((val a - val b) mod 4) 2); [lia|].
    eapply term1_ok; [exact R| | | | | ]; try (vs; lia).
    + rewrite St. vs. apply some_eq; reflexivity || lia.
    + vs. rewrite VW. ring.
Qed.

(** A sweep that ended on a non-reset letter whose target happens to be a reset value: valid for this start only. *)
Lemma term0_ok a0 B a b U W n :
  Reach a0 (val B) (val a) (val b) (val n) (4 * val B * val U + val W) ->
  -P125 <= val b - val B < P125 ->
  out_ok a0 B (OSum (term1 B a b n U W 0 (wc 0) 0 (wc 0))).
Proof.
  intros R Hb. cbn [out_ok]. unfold term1. split; [|cbn [sbase shi]; split; [lia|rewrite Z.sub_diag; reflexivity]].
  intros B' HB' _. cbn [sbase shi] in HB'. assert (B' = val B) by lia. subst B'.
  eapply Reach_conv; [exact R|reflexivity| |reflexivity|].
  - cbn [sdelta]. rewrite val_sub by exact Hb. ring.
  - unfold sum_cost. cbn [sU0 sU1 sW0 sW1 sae sgae sbe sgbe sca scb sbase]. rewrite val_wc. autorewrite with lits.
    rewrite Z.sub_diag. ring.
Qed.

Lemma cfits_b a b U W n : cfits a b U W n = true -> -P118 <= val b < P118.
Proof.
  unfold cfits. intros Hf. repeat (apply andb_prop in Hf; destruct Hf as [Hf ?]).
  apply fits_spec. assumption.
Qed.

Lemma walkC_sound a0 B fuel : fits B = true -> forall a b U W n,
  cfits a b U W n = true ->
  Reach a0 (val B) (val a) (val b) (val n) (4 * val B * val U + val W) ->
  out_ok a0 B (walkC fuel B a b U W n).
Proof.
  intros HB. pose proof HB as FB. apply fits_spec in FB.
  induction fuel; intros a b U W n Hf R; [exact I|].
  cbn [walkC]. pose proof (stepC_sound a0 B a b U W n Hf HB R) as H.
  destruct (stepC B a b U W n) as [a' b' U' W' n'|T| |].
  - destruct H as [Hf' R']. destruct (is_reset a').
    + apply term0_ok; [exact R'|]. pose proof (cfits_b _ _ _ _ _ Hf'). lia.
    + apply IHfuel; assumption.
  - exact H.
  - exact H.
  - exact I.
Qed.

(** ** Levels at their own base *)
Lemma lev_at a0 L B : lev_ok a0 L -> val (lbase L) = val B -> val B <= val (lhi L) ->
  Reach a0 (val B) (val (la L)) (val B + val (lc L) - val (la L)) (val (llen L)) (4 * val B * val (lU0 L) + val (lW0 L)).
Proof.
  intros [_ HR] Hb Hh. pose proof (HR (val B)) as R. rewrite Hb in R.
  rewrite Z.sub_diag in R. specialize (R ltac:(lia) eq_refl).
  unfold Aat, Rat in R.
  eapply Reach_conv; [exact R|ring|ring|reflexivity|ring].
Qed.

Definition toC (B : W) (L : Lev) : Out :=
  let b := sub (add B (lc L)) (la L) in
  if cfits (la L) b (lU0 L) (lW0 L) (llen L) then walkC F_tail B (la L) b (lU0 L) (lW0 L) (llen L) else OFail.

Fixpoint walkA (fuel : nat) (B : W) (L : Lev) (stk : list Lev) : list Lev * Out :=
  match fuel with
  | O => (stk, OFail)
  | S f =>
    match stepA B L with
    | SNext L' =>
      if is_reset (la L') then
        let b := sub (add B (lc L')) (la L') in
        if fits b then (stk, OSum (term1 B (la L') b (llen L') (lU0 L') (lW0 L') 0 (wc 0) 0 (wc 0)))
        else (stk, OFail)
      else if leb (lhi L') B then (stk, toC B L')
      else walkA f B L' (L' :: stk)
    | STerm T => (stk, OSum T)
    | SConc => (stk, toC B L)
    | SHaltA =>
      let b := sub (add B (lc L)) (la L) in
      (stk, OHalt (la L) b (lU0 L) (lW0 L) (llen L))
    | SFail => (stk, OFail)
    end
  end.

Lemma lev_bounds L : lev_fits L = true ->
  -P118 <= val (la L) < P118 /\ -P118 <= val (lc L) < P118.
Proof.
  unfold lev_fits. intros Hf. repeat (apply andb_prop in Hf; destruct Hf as [Hf ?]).
  split; apply fits_spec; assumption.
Qed.

Lemma val_b B L : fits B = true -> lev_fits L = true ->
  val (sub (add B (lc L)) (la L)) = val B + val (lc L) - val (la L).
Proof.
  intros H1 H2. apply fits_spec in H1. destruct (lev_bounds L H2). vs. lia.
Qed.

Lemma toC_sound a0 B L : fits B = true -> lev_ok a0 L -> val (lbase L) = val B -> val B <= val (lhi L) ->
  out_ok a0 B (toC B L).
Proof.
  intros HB HL Hb Hh. unfold toC. cbv zeta.
  destruct (cfits (la L) (sub (add B (lc L)) (la L)) (lU0 L) (lW0 L) (llen L)) eqn:F; [|exact I].
  apply walkC_sound; [exact HB|exact F|].
  rewrite val_b by (exact HB || exact (proj1 HL)).
  apply lev_at; assumption.
Qed.

Lemma walkA_sound a0 B fuel : fits B = true -> forall L stk,
  lev_ok a0 L -> val (lbase L) = val B -> val B <= val (lhi L) -> Forall (lev_ok a0) stk ->
  Forall (lev_ok a0) (fst (walkA fuel B L stk)) /\ out_ok a0 B (snd (walkA fuel B L stk)).
Proof.
  intros HB. pose proof HB as FB. apply fits_spec in FB.
  induction fuel; intros L stk HL Hb Hh Hs; [split; [exact Hs|exact I]|].
  cbn [walkA].
  destruct (stepA B L) as [L'|T| | |] eqn:St.
  - destruct (step_next' a0 B L L' HL Hb Hh HB St) as (HL' & Hb' & Hh').
    destruct (is_reset (la L')).
    { cbv zeta. destruct (fits (sub (add B (lc L')) (la L'))) eqn:Fb; [|split; [exact Hs|exact I]].
      split; [exact Hs|]. cbn [snd]. apply term0_ok.
      - rewrite val_b by (exact HB || exact (proj1 HL')). apply lev_at; assumption.
      - apply fits_spec in Fb. lia. }
    destruct (leb (lhi L') B) eqn:Lh.
    { split; [exact Hs|]. cbn [snd]. apply toC_sound; assumption. }
    apply IHfuel; try assumption. constructor; assumption.
  - destruct (step_term' a0 B L T HL Hb Hh HB St) as (HS & Hb' & Hh').
    split; [exact Hs|]. cbn [snd out_ok]. rewrite Hb'. split; [exact HS|]. split; [lia|]. rewrite Z.sub_diag. reflexivity.
  - split; [exact Hs|]. cbn [snd]. apply toC_sound; assumption.
  - split; [exact Hs|]. cbv zeta. cbn [snd out_ok]. rewrite val_b by (exact HB || exact (proj1 HL)).
    split.
    + exact (step_halt' a0 B L HL Hb Hh HB St).
    + apply lev_at; assumption.
  - split; [exact Hs|exact I].
Qed.

(** ** Slots: what is remembered between sweeps from one reset value and one residue class of [B] *)
Record Slot := mkSlot { hA : W; hS : W; hk : W; hW : W; stk : list Lev; ssum : Sum }.

Definition head_ok (a0 : Z) (s : Slot) : Prop :=
  fits (hA s) = true /\ fits (hS s) = true /\ fits (hk s) = true /\ fits (hW s) = true /\
  forall B', val (hS s) < B' -> Reach a0 B' (val (hA s)) (B' - val (hS s)) (val (hk s)) (val (hW s)).

Definition slot_ok (a0 : Z) (s : Slot) : Prop :=
  head_ok a0 s /\ Forall (lev_ok a0) (stk s) /\ sum_ok a0 (ssum s).

Definition empty_sum : Sum :=
  mkSum (wc 1) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) (wc 0) 0 0.
Definition empty_slot (a0 : W) : Slot := mkSlot a0 (wc 0) (wc 0) (wc 0) [] empty_sum.

Lemma empty_ok a0 : fits a0 = true -> slot_ok (val a0) (empty_slot a0).
Proof.
  intros F. split; [|split; [constructor|]].
  - unfold head_ok, empty_slot. cbn [hA hS hk hW]. repeat split; try exact F; try reflexivity.
    intros B' _. rewrite val_wc. autorewrite with lits. rewrite Z.sub_0_r. constructor.
  - intros B' H. exfalso. change (val (sbase (ssum (empty_slot a0)))) with 1 in H. change (val (shi (ssum (empty_slot a0)))) with 0 in H. lia.
Qed.

Definition usable_sum (T : Sum) (B : W) : bool :=
  leb (sbase T) B && leb B (shi T) && (low2 (sbase T) =? low2 B)%uint63.

Definition usable_lev (L : Lev) (B : W) : bool :=
  leb (lbase L) B && leb B (lhi L) && (low2 (lbase L) =? low2 B)%uint63.

Lemma mod4_add x y : x mod 4 = 0 -> y mod 4 = 0 -> (x + y) mod 4 = 0.
Proof. intros H1 H2. rewrite Z.add_mod by lia. rewrite H1, H2. reflexivity. Qed.

Lemma low2_diff x y : (low2 x =? low2 y)%uint63 = true -> (val y - val x) mod 4 = 0.
Proof.
  rewrite Uint63.eqb_spec. intros H. pose proof (phi_low2 x) as A. pose proof (phi_low2 y) as C. rewrite H in A.
  rewrite Zminus_mod. rewrite <- A, <- C. rewrite Z.sub_diag. reflexivity.
Qed.

Fixpoint pop (B : W) (l : list Lev) : list Lev :=
  match l with
  | [] => []
  | L :: t => if usable_lev L B then l else pop B t
  end.

Lemma pop_ok a0 B l : Forall (lev_ok a0) l -> Forall (lev_ok a0) (pop B l).
Proof.
  induction l as [|L t IH]; intros H; [exact H|]. cbn [pop]. inversion H; subst.
  destruct (usable_lev L B); [exact H|apply IH; assumption].
Qed.

(** The run of doublings at the start of a sweep, advanced only as far as this [B] needs. *)
Fixpoint hadv (fuel : nat) (B : W) (s : Slot) : Slot :=
  match fuel with
  | O => s
  | Datatypes.S f =>
    let A := hA s in let Sm := hS s in
    let S' := add (add Sm A) (wc 3) in
    if ltb S' B && negb (is_neg A) then
      let A' := add (add A A) (wc 6) in
      let k' := add (hk s) (wc 1) in
      let H' := add (sub (hW s) (mulk 30 A)) (wc 18) in
      if fits A' && fits S' && fits k' && fits H'
      then hadv f B (mkSlot A' S' k' H' (stk s) (ssum s))
      else s
    else s
  end.

Lemma hadv_ok a0 fuel B : forall s, head_ok a0 s -> head_ok a0 (hadv fuel B s) /\ stk (hadv fuel B s) = stk s /\ ssum (hadv fuel B s) = ssum s.
Proof.
  induction fuel; intros s H; [split; [exact H|split; reflexivity]|].
  cbn [hadv]. cbv zeta.
  destruct H as (FA & FS & Fk & FH & HR).
  destruct (ltb (add (add (hS s) (hA s)) (wc 3)) B) eqn:L; [|split; [unfold head_ok; auto 6|split; reflexivity]].
  destruct (is_neg (hA s)) eqn:NA; [cbn [andb negb]; split; [unfold head_ok; auto 6|split; reflexivity]|]. cbn [andb negb].
  apply is_neg_false in NA.
  destruct (fits (add (add (hA s) (hA s)) (wc 6))) eqn:F1; [|split; [unfold head_ok; auto 6|split; reflexivity]].
  destruct (fits (add (add (hS s) (hA s)) (wc 3))) eqn:F2; [|split; [unfold head_ok; auto 6|split; reflexivity]].
  destruct (fits (add (hk s) (wc 1))) eqn:F3; [|split; [unfold head_ok; auto 6|split; reflexivity]].
  destruct (fits (add (sub (hW s) (mulk 30 (hA s))) (wc 18))) eqn:F4; [|split; [unfold head_ok; auto 6|split; reflexivity]].
  cbn [andb].
  apply fits_spec in FA, FS, Fk, FH.
  assert (VS : val (add (add (hS s) (hA s)) (wc 3)) = val (hS s) + val (hA s) + 3) by (vs; lia).
  assert (VA : val (add (add (hA s) (hA s)) (wc 6)) = 2 * val (hA s) + 6) by (vs; lia).
  assert (Vk : val (add (hk s) (wc 1)) = val (hk s) + 1) by (vs; lia).
  assert (VH : val (add (sub (hW s) (mulk 30 (hA s))) (wc 18)) = val (hW s) - 30 * val (hA s) + 18) by (vs; lia).
  destruct (IHfuel (mkSlot (add (add (hA s) (hA s)) (wc 6)) (add (add (hS s) (hA s)) (wc 3)) (add (hk s) (wc 1))
     (add (sub (hW s) (mulk 30 (hA s))) (wc 18)) (stk s) (ssum s))) as [X [Y Z]].
  { unfold head_ok. cbn [hA hS hk hW]. repeat split; try assumption.
    intros B' HB'. rewrite VS in HB'. rewrite VA, VS, Vk, VH.
    pose proof (HR B' ltac:(lia)) as R.
    assert (St : aStep (val (hA s)) (B' - val (hS s)) = Some (2 * val (hA s) + 6, B' - val (hS s) - val (hA s) - 3, -30 * val (hA s) + 18)) by (apply L_D; lia).
    pose proof (Reach_snoc _ _ _ _ _ _ _ _ _ R St) as R1.
    eapply Reach_conv; [exact R1|reflexivity|ring|reflexivity|ring]. }
  split; [exact X|]. cbn [stk ssum] in Y, Z. split; assumption.
Qed.

Definition rebase (B : W) (L : Lev) : option Lev :=
  let y := sub B (lbase L) in
  match mul_s (lga L) y, mul_s (lU1 L) y, mul_s (lW1 L) y with
  | Some p, Some q, Some r =>
    let L' := mkLev (add (la L) p) (lga L) (lc L) B (lhi L) (add (lU0 L) q) (lU1 L) (add (lW0 L) r) (lW1 L) (llen L) in
    if lev_fits L' then Some L' else None
  | _, _, _ => None
  end.

Lemma lev_more L : lev_fits L = true ->
  -P118 <= val (lbase L) < P118 /\ -P118 <= val (lU0 L) < P118 /\ -P118 <= val (lW0 L) < P118.
Proof.
  unfold lev_fits. intros Hf. repeat (apply andb_prop in Hf; destruct Hf as [Hf ?]).
  pose proof (fits_spec (lbase L) ltac:(assumption)). pose proof (fits_spec (lU0 L) ltac:(assumption)).
  pose proof (fits_spec (lW0 L) ltac:(assumption)). lia.
Qed.

Ltac lb := repeat match goal with H : _ = _ * _ |- _ => clear H end; lia.

Lemma rebase_ok a0 B L L' : fits B = true -> lev_ok a0 L -> usable_lev L B = true -> rebase B L = Some L' ->
  lev_ok a0 L' /\ val (lbase L') = val B /\ val B <= val (lhi L').
Proof.
  intros HB [Hf HR] U. unfold rebase. cbv zeta. pose proof HB as FB. apply fits_spec in FB.
  unfold usable_lev in U. apply andb_prop in U. destruct U as [U U3]. apply andb_prop in U. destruct U as [U1 U2].
  apply leb_spec_W in U1. apply leb_spec_W in U2. apply low2_diff in U3.
  destruct (lev_more L Hf) as (Bb & BU & BW).
  assert (Vy : val (sub B (lbase L)) = val B - val (lbase L)) by (apply val_sub; lia).
  destruct (mul_s (lga L) (sub B (lbase L))) as [p|] eqn:M1; [|discriminate].
  destruct (mul_s (lU1 L) (sub B (lbase L))) as [q|] eqn:M2; [|discriminate].
  destruct (mul_s (lW1 L) (sub B (lbase L))) as [r|] eqn:M3; [|discriminate].
  destruct (mul_s_spec _ _ _ M1) as [Ep Bp]. destruct (mul_s_spec _ _ _ M2) as [Eq Bq]. destruct (mul_s_spec _ _ _ M3) as [Er Br].
  rewrite Vy in Ep, Eq, Er.
  destruct (lev_bounds L Hf) as [Ba Bc].
  match goal with |- context [lev_fits ?X] => set (L1 := X) end.
  destruct (lev_fits L1) eqn:FL; [|discriminate].
  intros H. injection H as <-.
  split; [|split; [reflexivity|exact U2]].
  split; [exact FL|].
  assert (VA : val (add (la L) p) = val (la L) + val p) by (apply val_add; lb).
  assert (VU : val (add (lU0 L) q) = val (lU0 L) + val q) by (apply val_add; lb).
  assert (VW : val (add (lW0 L) r) = val (lW0 L) + val r) by (apply val_add; lb).
  intros B' HB' Hm. cbn [lbase lhi L1] in HB', Hm.
  pose proof (HR B' ltac:(lb)) as R.
  assert (Hm' : (B' - val (lbase L)) mod 4 = 0).
  { replace (B' - val (lbase L)) with ((B' - val B) + (val B - val (lbase L))) by ring. apply mod4_add; assumption. }
  specialize (R Hm').
  unfold Aat, Rat in *. cbn [la lga lc lbase lU0 lU1 lW0 lW1 llen L1]. rewrite VA, VU, VW, Ep, Eq, Er.
  eapply Reach_conv; [exact R|ring|ring|reflexivity|ring].
Qed.

(** ** Preparing a slot for a start [B] *)
Definition cap : W := mkW 18014398509481984%uint63 0%uint63.

Definition head_level (B : W) (s : Slot) : Lev :=
  mkLev (hA s) (wc 0) (sub (hA s) (hS s)) B cap (wc 0) (wc 0) (hW s) (wc 0) (hk s).

Definition F_lev : nat := Nat.pow 2 13.
Definition F_head : nat := 256.

Definition from_head (f1 f2 : nat) (a0 : W) (s : Slot) (B : W) : Slot * list Lev * Out :=
  let s1 := if ltb (hS s) B then s else mkSlot a0 (wc 0) (wc 0) (wc 0) (stk s) (ssum s) in
  let s2 := hadv f1 B s1 in
  let L0 := head_level B s2 in
  if lev_fits L0 && ltb (hS s2) B && leb B cap then
    let (st', o) := walkA f2 B L0 [] in (s2, st', o)
  else (s2, [], OFail).

Definition prep_gen (f1 f2 : nat) (a0 : W) (s : Slot) (B : W) : Slot * Out :=
  let T := ssum s in
  if usable_sum T B then (s, OSum T) else
  let stk1 := pop B (stk s) in
  let '(s3, st3, o) :=
    match stk1 with
    | L :: _ =>
      match rebase B L with
      | Some L' => let (st', o) := walkA f2 B L' stk1 in (s, st', o)
      | None => from_head f1 f2 a0 s B
      end
    | [] => from_head f1 f2 a0 s B
    end in
  match o with
  | OSum T' => (mkSlot (hA s3) (hS s3) (hk s3) (hW s3) st3 T', o)
  | _ => (mkSlot (hA s3) (hS s3) (hk s3) (hW s3) st3 (ssum s), o)
  end.

Definition prep : W -> Slot -> W -> Slot * Out := prep_gen F_head F_lev.

Lemma cap_val : val cap = 332306998946228968225951765070086144 / 2.
Proof. reflexivity. Qed.

Lemma from_head_ok f1 f2 a0 s B : fits a0 = true -> fits B = true -> head_ok (val a0) s ->
  let '(s3, st3, o) := from_head f1 f2 a0 s B in
  head_ok (val a0) s3 /\ Forall (lev_ok (val a0)) st3 /\ out_ok (val a0) B o.
Proof.
  intros Fa HB Hh. unfold from_head. cbv zeta.
  set (s1 := if ltb (hS s) B then s else mkSlot a0 (wc 0) (wc 0) (wc 0) (stk s) (ssum s)).
  assert (H1 : head_ok (val a0) s1).
  { subst s1. destruct (ltb (hS s) B); [exact Hh|].
    unfold head_ok. cbn [hA hS hk hW]. repeat split; try exact Fa; try reflexivity.
    intros B' _. rewrite val_wc. autorewrite with lits. rewrite Z.sub_0_r. constructor. }
  destruct (hadv_ok (val a0) f1 B s1 H1) as [H2 _].
  set (s2 := hadv f1 B s1) in *. clearbody s2.
  destruct (lev_fits (head_level B s2) && ltb (hS s2) B && leb B cap) eqn:C.
  2:{ split; [exact H2|]. split; [constructor|exact I]. }
  apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
  apply ltb_spec_W in C2. apply leb_spec_W in C3.
  assert (HL0 : lev_ok (val a0) (head_level B s2)).
  { split; [exact C1|]. destruct H2 as (FA & FS & Fk & FH & HR).
    apply fits_spec in FA. apply fits_spec in FS.
    assert (Vc : val (sub (hA s2) (hS s2)) = val (hA s2) - val (hS s2)) by (apply val_sub; lia).
    intros B' HB' _. unfold head_level in HB'. cbn [lbase lhi] in HB'.
    pose proof (HR B' ltac:(lia)) as R.
    unfold Aat, Rat, head_level. cbn [la lga lc lbase lU0 lU1 lW0 lW1 llen]. rewrite Vc. rewrite !val_wc. autorewrite with lits.
    eapply Reach_conv; [exact R|ring|ring|reflexivity|ring]. }
  pose proof (walkA_sound (val a0) B f2 HB (head_level B s2) [] HL0 eq_refl) as W.
  specialize (W ltac:(cbn [head_level lhi]; rewrite cap_val in *; lia) (Forall_nil _)).
  destruct (walkA f2 B (head_level B s2) []) as [st' o]. cbn [fst snd] in W.
  split; [exact H2|exact W].
Qed.

Lemma prep_gen_sound f1 f2 a0 s B : fits a0 = true -> fits B = true -> slot_ok (val a0) s ->
  slot_ok (val a0) (fst (prep_gen f1 f2 a0 s B)) /\ out_ok (val a0) B (snd (prep_gen f1 f2 a0 s B)).
Proof.
  intros Fa HB (Hh & Hl & Hs). unfold prep_gen. cbv zeta.
  destruct (usable_sum (ssum s) B) eqn:U.
  { split; [split; auto|]. cbn [snd out_ok]. unfold usable_sum in U.
    apply andb_prop in U. destruct U as [U U3]. apply andb_prop in U. destruct U as [U1 U2].
    apply leb_spec_W in U1. apply leb_spec_W in U2. apply low2_diff in U3.
    split; [exact Hs|]. split; [lia|exact U3]. }
  assert (Main : forall s3 st3 o,
     head_ok (val a0) s3 -> Forall (lev_ok (val a0)) st3 -> out_ok (val a0) B o ->
     slot_ok (val a0) (fst (match o with
       | OSum T' => (mkSlot (hA s3) (hS s3) (hk s3) (hW s3) st3 T', o)
       | _ => (mkSlot (hA s3) (hS s3) (hk s3) (hW s3) st3 (ssum s), o) end))
     /\ out_ok (val a0) B (snd (match o with
       | OSum T' => (mkSlot (hA s3) (hS s3) (hk s3) (hW s3) st3 T', o)
       | _ => (mkSlot (hA s3) (hS s3) (hk s3) (hW s3) st3 (ssum s), o) end))).
  { intros s3 st3 o H3 L3 O3. destruct o as [T'|a b U' W n|]; cbn [fst snd].
    - split; [|exact O3]. split; [exact H3|]. split; [exact L3|exact (proj1 O3)].
    - split; [|exact O3]. split; [exact H3|]. split; [exact L3|exact Hs].
    - split; [|exact O3]. split; [exact H3|]. split; [exact L3|exact Hs]. }
  pose proof (pop_ok (val a0) B (stk s) Hl) as Hp.
  destruct (pop B (stk s)) as [|L tl] eqn:Pop.
  - pose proof (from_head_ok f1 f2 a0 s B Fa HB Hh) as F.
    destruct (from_head f1 f2 a0 s B) as [[s3 st3] o]. destruct F as (F1 & F2 & F3). apply Main; assumption.
  - assert (UL : usable_lev L B = true).
    { clear -Pop. revert Pop. induction (stk s) as [|x t IH]; cbn [pop]; [discriminate|].
      destruct (usable_lev x B) eqn:E; intros P; [injection P as -> _; exact E|exact (IH P)]. }
    destruct (rebase B L) as [L'|] eqn:R.
    + inversion Hp as [|? ? HL0 Ht]; subst.
      destruct (rebase_ok (val a0) B L L' HB HL0 UL R) as (HL' & Hb' & Hh').
      pose proof (walkA_sound (val a0) B f2 HB L' (L :: tl) HL' Hb' Hh' Hp) as W.
      destruct (walkA f2 B L' (L :: tl)) as [st' o]. cbn [fst snd] in W. destruct W as [W1 W2].
      apply Main; assumption.
    + pose proof (from_head_ok f1 f2 a0 s B Fa HB Hh) as F.
      destruct (from_head f1 f2 a0 s B) as [[s3 st3] o]. destruct F as (F1 & F2 & F3). apply Main; assumption.
Qed.

Lemma prep_sound a0 s B : fits a0 = true -> fits B = true -> slot_ok (val a0) s ->
  slot_ok (val a0) (fst (prep a0 s B)) /\ out_ok (val a0) B (snd (prep a0 s B)).
Proof. apply prep_gen_sound. Qed.
