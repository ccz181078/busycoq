Require Import Zify ZifyUint63 Lia PeanoNat ZArith Uint63.
From BusyCoq Require Import LibTactics.

Notation mask := (18014398509481983%uint63).
Notation wB' := (54%uint63).
Notation mask0 := (511%uint63).
Notation hmask := (134217727%uint63).
Notation hwB' := (27%uint63).


Inductive BigUint :=
| BigUintNil
| BigUintCons(a:int)(x:BigUint)
.

Open Scope uint63.

Definition Cons_simpl(a0:int)(a1:BigUint):BigUint :=
match a1 with
| BigUintNil =>
  if a0 =? 0 then BigUintNil else BigUintCons a0 a1
| _ => BigUintCons a0 a1
end.

Fixpoint inc(a:BigUint)(c:int):BigUint :=
if c =? 0 then a else
match a with
| BigUintNil => BigUintCons c BigUintNil
| BigUintCons a0 a1 =>
  let c0 := (a0 land mask) + c in
  let c01 := c0 >> wB' in
  BigUintCons (c0 land mask) (inc a1 c01)
end.

Fixpoint dec(a:BigUint)(c:int):option BigUint :=
if c =? 0 then Some a else
match a with
| BigUintNil => None
| BigUintCons a0 a1 =>
  let c0 := (a0 land mask) - c in
  let c01 := (c0 >> wB') land 1 in
  match dec a1 c01 with
  | None => None
  | Some c1 => Some (Cons_simpl (c0 land mask) c1)
  end
end.

Fixpoint addc(a b:BigUint)(c:int){struct a}:BigUint :=
match a,b with
| BigUintNil,_ => inc b c
| _,BigUintNil => inc a c
| BigUintCons a0 a1,BigUintCons b0 b1 =>
  let c0 := (a0 land mask) + (b0 land mask) + c in
  let c01 := c0 >> wB' in
  BigUintCons (c0 land mask) (addc a1 b1 c01)
end.

Definition add a b := addc a b 0.

Definition succ a := inc a 1.
Definition pred a := dec a 1.

Fixpoint is0(a:BigUint):bool :=
match a with
| BigUintNil => true
| BigUintCons a0 a1 =>
  if (a0 land mask)=?0 then is0 a1 else false
end.

Fixpoint subc(a b:BigUint)(c:int){struct a}:option BigUint :=
match a,b with
| BigUintNil,_ =>
  if (c =? 0) then
    if (is0 b) then Some BigUintNil
    else None
  else None
| _,BigUintNil => dec a c
| BigUintCons a0 a1,BigUintCons b0 b1 =>
  let c0 := (a0 land mask) - (b0 land mask) - c in
  let c01 := (c0 >> wB') land 1 in
  match subc a1 b1 c01 with
  | None => None
  | Some c1 => Some (Cons_simpl (c0 land mask) c1) 
  end
end.

Definition subge a b := subc a b 0.

Definition leb(a b:BigUint):bool :=
match subge b a with
| Some _ => true
| None => false
end.

Definition ltb(a b:BigUint):bool :=
match subge a b with
| Some _ => false
| None => true
end.

Definition min a b := if leb a b then a else b.
Definition max a b := if leb a b then b else a.

Fixpoint eqb(a b:BigUint):bool :=
match a,b with
| BigUintNil,BigUintNil => true
| BigUintCons a0 a1,BigUintCons b0 b1 =>
  if a0 =? b0 then eqb a1 b1 else false
| _,_ => false
end.

Definition sub a b :=
match subc a b 0 with
| Some c => c
| None => BigUintNil
end.

Fixpoint toZ(a:BigUint):Z :=
match a with
| BigUintNil => 0
| BigUintCons a0 a1 =>
  (to_Z (a0 land mask)) + 
  (toZ a1)*(2^54)
end.

Fixpoint Z_lsl a n :=
match n with
| O => a
| S n0 => Z.double (Z_lsl a n0)
end.

Fixpoint toZ'(a:BigUint):Z :=
match a with
| BigUintNil => 0
| BigUintCons a0 a1 =>
  (to_Z (a0 land mask)) + 
  (Z_lsl (toZ a1) 54)
end.

Fixpoint ofPos(a:positive)(c w:int):BigUint :=
match a with
| xI a0 =>
  if w =? wB'-1 then BigUintCons (c+(1<<w)) (ofPos a0 0 0)
  else ofPos a0 (c+(1<<w)) (w+1)
| xO a0 =>
  if w =? wB'-1 then BigUintCons c (ofPos a0 0 0)
  else ofPos a0 c (w+1)
| xH => BigUintCons (c+(1<<w)) BigUintNil
end.

Fixpoint ofZ(a:Z):BigUint :=
match a with
| Zpos a0 => ofPos a0 0 0
| _ => BigUintNil
end.

Fixpoint muladdc(a:BigUint)(b c:int):BigUint :=
match a with
| BigUintNil => (Cons_simpl c BigUintNil)
| BigUintCons a0 a1 =>
  let v := (a0 land mask)*b + c in
  let vH := (v>>wB') in
  let vL := (v land mask) in
  Cons_simpl vL (muladdc a1 b vH)
end.

Definition mulc a b := muladdc a b 0.

Fixpoint divmodc(a:BigUint)(b:int):BigUint*int :=
match a with
| BigUintNil => (BigUintNil,0)
| BigUintCons a0 a1 =>
  let (c0,c1) := divmodc a1 b in
  let a0' := (a0 land mask) + (c1<<wB') in
  (Cons_simpl (a0'/b) c0, a0' mod b)
end.

Fixpoint muladdc2(a:BigUint)(bH bL c:int):BigUint :=
match a with
| BigUintNil => Cons_simpl c BigUintNil
| BigUintCons a0 a1 =>
  let a0' := a0 land mask in
  let aH := (a0'>>hwB') in
  let aL := (a0' land hmask) in
  let v := aL*bH+aH*bL in
  let vH := (v>>hwB') in
  let vL := (v land hmask) in
  let c0 := aL*bL + (vL<<hwB') + c in
  let c01 := aH*bH+vH+(c0>>wB') in
  BigUintCons (c0 land mask) (muladdc2 a1 bH bL c01)
end.

Definition mulc2 a b := if b=?0 then BigUintNil else muladdc2 a (b>>hwB') (b land hmask) 0.

Fixpoint mul_v2(a b:BigUint):BigUint :=
match a with
| BigUintNil => BigUintNil
| BigUintCons a0 a1 =>
  add (Cons_simpl 0 (mul_v2 a1 b)) (mulc2 b (a0 land mask))
end.

Definition mul' a b :=
ofZ ((toZ' a)*(toZ' b)).

Definition mul a b :=
match a with
| BigUintNil => BigUintNil
| BigUintCons a0 BigUintNil =>
  if a0<=?mask0 then mulc b a0
  else mul' a b
| _ =>
  match b with
  | BigUintNil => BigUintNil
  | BigUintCons b0 BigUintNil =>
    if b0<=?mask0 then mulc a b0
    else mul' a b
  | _ => mul' a b
  end
end.

Definition pr_a(a:Z) := a.
Definition pr_b(a:Z) := a.

Definition div' a b :=
  ofZ ((pr_a (toZ' a))/(pr_b (toZ' b))).

Definition div a b :=
match b with
| BigUintNil => BigUintNil
| BigUintCons b0 BigUintNil =>
  if b0<=?mask0 then
    if 1<=?b0 then fst (divmodc a b0)
    else BigUintNil
  else div' a b
| _ => div' a b
end.

Definition div_small a b :=
match b with
| BigUintNil => None
| BigUintCons b0 b =>
  if b0<=?mask0 then
    if 1<=?b0 then Some (fst (divmodc a b0))
    else None
  else None
end.

Lemma mask_spec c:
  ((to_Z (c land mask)) = (to_Z c) mod (2^54))%Z.
Proof.
  rewrite land_spec'.
  rewrite (Z.land_ones _ 54) by lia.
  lia.
Qed.

Lemma mask1_spec c:
  ((to_Z (c land 1)) = (to_Z c) mod (2))%Z.
Proof.
  rewrite land_spec'.
  rewrite (Z.land_ones _ 1) by lia.
  lia.
Qed.

Lemma hmask_spec c:
  ((to_Z (c land hmask)) = (to_Z c) mod (2^27))%Z.
Proof.
  rewrite land_spec'.
  rewrite (Z.land_ones _ 27) by lia.
  lia.
Qed.


Ltac solve_v1 :=
  repeat (rewrite mask_spec ||
  rewrite mask1_spec ||
  rewrite land_spec' ||
  rewrite add_spec ||
  rewrite sub_spec ||
  rewrite mul_spec ||
  rewrite div_spec ||
  rewrite mod_spec ||
  rewrite lsl_spec ||
  rewrite lsr_spec ||
  rewrite leb_spec ||
  cbn[toZ]);
  try lia.

Lemma Z_lsl_spec a n:
  (Z_lsl a n = a*2^(Z.of_nat n))%Z.
Proof.
  induction n; cbn[Z_lsl].
  - lia.
  - rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    lia.
Qed.

Lemma toZ'_spec x:
  toZ' x = toZ x.
Proof.
  induction x; cbn[toZ]; cbn[toZ'].
  - lia.
  - rewrite Z_lsl_spec.
    lia.
Qed.

Lemma inc_spec a c:
  (c <=? mask) = true ->
  (toZ (inc a c) = toZ a + (to_Z c))%Z.
Proof.
  gen c.
  induction a; intros; cbn[inc].
  - destruct (c =? 0) eqn:E; cbn[toZ].
    + lia.
    + rewrite mask_spec.
      lia.
  - destruct (c =? 0) eqn:E; cbn[toZ].
    + lia.
    + rewrite IHa by lia.
      solve_v1.
Qed.

Lemma Cons_simpl_spec a0 a1:
  toZ (Cons_simpl a0 a1) = toZ (BigUintCons a0 a1).
Proof.
  unfold Cons_simpl.
  destruct a1.
  2: lia.
  destruct (a0=?0) eqn:E.
  2: lia.
  cbn[toZ].
  solve_v1.
Qed.

Lemma dec_spec a c:
  (c <=? mask) = true ->
  match dec a c with
  | Some a' => (toZ a' + to_Z c = toZ a)%Z
  | None => (toZ a < to_Z c)%Z
  end.
Proof.
  gen c.
  induction a as [|a0 a1 IHa]; intros; cbn[dec].
  - destruct (c =? 0) eqn:E; cbn[toZ]; lia.
  - destruct (c =? 0) eqn:E; cbn[toZ].
    + lia.
    + match goal with
      | |- match match dec _ ?c with _ => _ end with _ => _ end =>
        specialize (IHa c);
        destruct (dec a1 c) eqn:E0
      end.
      * rewrite Cons_simpl_spec.
        gen IHa.
        solve_v1.
      * gen IHa.
        solve_v1.
Qed.

Lemma toZ_ge0 a:
  (0 <= toZ a)%Z.
Proof.
  induction a; cbn[toZ]; solve_v1.
Qed.

Lemma succ_spec a:
  (toZ (succ a) = toZ a + 1)%Z.
Proof.
  unfold succ.
  rewrite inc_spec; lia.
Qed.

Lemma pred_spec a:
  (match pred a with
  | None => toZ a = 0
  | Some a0 => toZ a0 + 1 = toZ a
  end)%Z.
Proof.
  unfold pred.
  epose proof (dec_spec a 1).
  destruct (dec a 1) eqn:E.
  - lia.
  - epose proof (toZ_ge0 a).
    lia.
Qed.

Lemma addc_spec a b c:
  (c <=? 1) = true ->
  (toZ (addc a b c) = toZ a + toZ b + to_Z c)%Z.
Proof.
  gen b c.
  induction a; intros; cbn[addc]; cbn[toZ].
  - rewrite inc_spec; solve_v1.
  - destruct b.
    + rewrite inc_spec; solve_v1.
    + solve_v1.
      rewrite IHa; solve_v1.
Qed.

Lemma add_spec a b:
  (toZ (add a b) = toZ a + toZ b)%Z.
Proof.
  unfold add.
  rewrite addc_spec; solve_v1.
Qed.

Lemma is0_spec a:
  Bool.reflect (toZ a = Z0) (is0 a).
Proof.
  induction a; cbn[is0]; cbn[toZ].
  - constructor; trivial.
  - destruct ((a land mask)=?0) eqn:E.
    + destruct IHa; constructor.
      * rewrite eqb_spec in E.
        lia.
      * solve_v1.
    + constructor.
      epose proof (toZ_ge0 a0).
      rewrite eqb_false_spec in E.
      remember (a land mask) as a'.
      solve_v1.
Qed.

Lemma subc_spec a b c:
  (c <=? 1) = true ->
  match subc a b c with
  | Some a' => (toZ a' + toZ b + to_Z c = toZ a)%Z
  | None => (toZ a < toZ b + to_Z c)%Z
  end.
Proof.
  gen b c.
  induction a as [|a0 a1 IHa]; intros; cbn[subc]; cbn[toZ].
  - destruct (c=?0) eqn:E.
    + destruct (is0_spec b) as [E0|E0].
      * solve_v1.
      * epose proof (toZ_ge0 b).
        solve_v1.
    + epose proof (toZ_ge0 b).
      solve_v1.
  - destruct b as [|b0 b1].
    + remember (BigUintCons a0 a1) as a'.
      epose proof (dec_spec a' c) as I.
      destruct (dec a' c).
      * subst a'.
        cbn[toZ] in *.
        gen I.
        solve_v1.
      * subst a'.
        cbn[toZ] in *.
        gen I.
        solve_v1.
    + match goal with
      | |- match match subc _ _ ?c with _ => _ end with _ => _ end =>
        specialize (IHa b1 c);
        destruct (subc a1 b1 c) eqn:E0
      end.
      * rewrite Cons_simpl_spec.
        gen IHa.
        solve_v1.
      * gen IHa.
        solve_v1.
Qed.

Lemma subge_spec a b:
  match subge a b with
  | Some a' => (toZ a' + toZ b = toZ a)%Z
  | None => (toZ a < toZ b)%Z
  end.
Proof.
  epose proof (subc_spec a b 0).
  unfold subge.
  destruct (subc a b 0); lia.
Qed.

Lemma leb_spec a b:
  Bool.reflect (toZ a <= toZ b)%Z (leb a b).
Proof.
  unfold leb.
  epose proof (subge_spec b a).
  destruct (subge b a); constructor.
  - epose proof (toZ_ge0 b0); lia.
  - lia.
Qed.

Lemma ltb_spec a b:
  Bool.reflect (toZ a < toZ b)%Z (ltb a b).
Proof.
  unfold ltb.
  epose proof (subge_spec a b).
  destruct (subge a b); constructor.
  - epose proof (toZ_ge0 b0); lia.
  - lia.
Qed.

Lemma min_spec a b:
  (toZ (min a b) = Z.min (toZ a) (toZ b))%Z.
Proof.
  unfold min.
  destruct (leb_spec a b); lia.
Qed.

Lemma max_spec a b:
  (toZ (max a b) = Z.max (toZ a) (toZ b))%Z.
Proof.
  unfold max.
  destruct (leb_spec a b); lia.
Qed.

Lemma eqb_spec a b:
  Bool.reflect (a=b) (eqb a b).
Proof.
  gen b.
  induction a as [|a0 a1 IHa]; intros;
  destruct b as [|b0 b1]; cbn[eqb].
  - constructor; trivial.
  - constructor. congruence.
  - constructor. congruence.
  - destruct (a0 =? b0) eqn:E.
    + rewrite eqb_spec in E.
      subst.
      destruct (IHa b1).
      * subst.
        constructor; trivial.
      * constructor. congruence.
    + rewrite eqb_false_spec in E.
      constructor. congruence.
Qed.

Lemma sub_spec a b:
  (toZ (sub a b) = Z.max 0 (toZ a - toZ b))%Z.
Proof.
  unfold sub.
  epose proof (subc_spec a b 0).
  destruct (subc a b 0).
  - pose proof (toZ_ge0 b0).
    solve_v1.
  - solve_v1.
Qed.

Lemma muladdc_spec a b c:
  (b <=? mask0) = true ->
  (c <=? mask0) = true ->
  (toZ (muladdc a b c) = toZ a * (to_Z b) + (to_Z c))%Z.
Proof.
  gen b c.
  induction a as [|a0 a1 IHa]; intros; cbn[muladdc]; cbn[toZ].
  - rewrite Cons_simpl_spec.
    solve_v1.
  - rewrite Cons_simpl_spec.
    cbn[toZ].
    match goal with
    | |- context[muladdc _ _ ?c] =>
      specialize (IHa b c)
    end.
    remember (a0 land mask) as a0'.
    rewrite Uint63.leb_spec in *.
    assert (to_Z a0'<=to_Z mask)%Z as I1 by (subst a0'; solve_v1).
    assert (to_Z (a0'*b + c) = to_Z a0' * to_Z b + to_Z c)%Z as I2 by (
    unshelve epose proof (Z.mul_le_mono_nonneg _ _ _ _ _ I1 _ H); lia).
    assert (to_Z (a0'*b + c) <= (to_Z mask+1)*to_Z mask0)%Z as I2' by (
    unshelve epose proof (Z.mul_le_mono_nonneg _ _ _ _ _ I1 _ H); lia).
    rewrite IHa by lia.
    solve_v1.
Qed.

Lemma mulc_spec a b:
  (b <=? mask0) = true ->
  (toZ (mulc a b) = toZ a * (to_Z b))%Z.
Proof.
  intros.
  epose proof (muladdc_spec a b 0).
  unfold mulc.
  lia.
Qed.

Lemma divmodc_spec a b:
  (1 <=? b) = true ->
  (b <=? mask0) = true ->
  (let (c0,c1):=(divmodc a b) in
  toZ c0 = toZ a / (to_Z b) /\
  (to_Z c1) = toZ a mod (to_Z b))%Z.
Proof.
  intros Hb0 Hb.
  induction a as [|a0 a1 IHa]; intros; cbn[divmodc]; cbn[toZ].
  - split.
    1: rewrite Zdiv_0_l; lia.
    reflexivity.
  - destruct (divmodc a1 b) as [c0 c1].
    destruct IHa as [I1 I2].
    rewrite Cons_simpl_spec.
    split; solve_v1.
    + rewrite I1,I2.
      rewrite Uint63.leb_spec in *.
      do 2 rewrite (Z.mod_small _ wB) by lia.
      remember (to_Z a0 mod 2^54)%Z as a0'.
      remember (toZ a1) as a1'.
      remember (to_Z b) as b'.
      change (to_Z 54) with 54%Z.
      replace (a0'+a1'*2^54)%Z with (a0'+(a1' mod b')*2^54+(a1'/b'*2^54*b'))%Z by lia.
      rewrite Z.div_add by lia.
      rewrite Z.mod_small.
      1: trivial.
      split.
      2: apply Z.div_lt_upper_bound; lia.
      apply Z.div_pos; lia.
    + rewrite I2.
      rewrite Uint63.leb_spec in *.
      do 2 rewrite (Z.mod_small _ wB) by lia.
      do 2 (rewrite Z.add_mod by lia; symmetry).
      do 2 f_equal.
      do 2 (rewrite Z.mul_mod by lia; symmetry).
      f_equal.
      repeat rewrite Z.mod_mod by lia.
      reflexivity.
Qed.

Ltac rw_mod_small :=
  repeat (
  lia ||
  rewrite (Z.mod_small _ wB) ||
  rewrite Z.pow_add_r).


Lemma ofPos_spec x c i:
  (to_Z i < to_Z wB' ->
  to_Z c < 2^to_Z i ->
  toZ (ofPos x c i) = (Zpos x)*(to_Z (1<<i))+to_Z c)%Z.
Proof.
  gen c i.
  induction x; intros; cbn[ofPos].
  - destruct (i =? wB'-1) eqn:E.
    + cbn[toZ].
      rewrite Uint63.eqb_spec in E.
      subst i.
      rewrite IHx by lia.
      change (54-1) with 53 in *.
      solve_v1.
    + rewrite eqb_false_spec in E.
      epose proof H as I1.
      eapply (Z.pow_lt_mono_r 2) in I1.
      2,3: lia.
      rewrite IHx.
      2: lia.
      * solve_v1.
        rw_mod_small.
      * solve_v1.
        rw_mod_small.
  - destruct (i =? wB'-1) eqn:E.
    + cbn[toZ].
      rewrite Uint63.eqb_spec in E.
      subst i.
      rewrite IHx by lia.
      change (54-1) with 53 in *.
      solve_v1.
    + rewrite eqb_false_spec in E.
      epose proof H as I1.
      eapply (Z.pow_lt_mono_r 2) in I1.
      2,3: lia.
      rewrite IHx.
      2: lia.
      * solve_v1.
        rw_mod_small.
      * solve_v1.
        rw_mod_small.
  - cbn[toZ].
    assert (to_Z i+1<=54)%Z as I1 by lia.
    eapply (Z.pow_le_mono_r 2) in I1.
    2: lia.
    rewrite Z.pow_add_r in I1 by lia.
    solve_v1.
Qed.

Lemma ofZ_spec x:
  (0<=x ->
  toZ (ofZ x) = x)%Z.
Proof.
  intros.
  destruct x; cbn[ofZ].
  - reflexivity.
  - rewrite ofPos_spec; lia.
  - lia.
Qed.

Lemma mul'_spec a b:
  (toZ (mul' a b) = toZ a * toZ b)%Z.
Proof.
  unfold mul'.
  repeat rewrite toZ'_spec.
  epose proof (toZ_ge0 a).
  epose proof (toZ_ge0 b).
  rewrite ofZ_spec; lia.
Qed.

Lemma div'_spec a b:
  (toZ (div' a b) = toZ a / toZ b)%Z.
Proof.
  unfold div'.
  unfold pr_a,pr_b.
  repeat rewrite toZ'_spec.
  epose proof (toZ_ge0 a).
  epose proof (toZ_ge0 b).
  rewrite ofZ_spec.
  1: lia.
  assert (toZ b=0\/1<=toZ b)%Z as [E|E] by lia.
  - rewrite E,Zdiv_0_r; lia.
  - apply Z.div_pos; lia.
Qed.

(*
Lemma mul_v2_spec a b:
  (toZ (mul_v2 a b) = toZ a * toZ b)%Z.
Proof.
Admitted.
 *)
Lemma mul_spec a b:
  (toZ (mul a b) = toZ a * toZ b)%Z.
Proof.
  unfold mul.
  destruct a as [|a0 [|a1 a2]].
  - reflexivity.
  - destruct (a0 <=? mask0) eqn:E.
    + rewrite mulc_spec by lia.
      solve_v1.
      rewrite (Z.mod_small _ (2^54)) by lia.
      lia.
    + apply mul'_spec.
  - destruct b as [|b0 [|b1 b2]].
    + rewrite Z.mul_comm; reflexivity.
    + destruct (b0 <=? mask0) eqn:E.
      * rewrite mulc_spec by lia.
        solve_v1.
        rewrite (Z.mod_small (to_Z b0) (2^54)) by lia.
        lia.
      * apply mul'_spec.
    + apply mul'_spec.
Qed.

Lemma div_spec a b:
  (toZ (div a b) = toZ a / toZ b)%Z.
Proof.
  unfold div.
  destruct b as [|b0 [|b1 b2]].
  - cbn[toZ].
    rewrite Zdiv_0_r; lia.
  - destruct (b0 <=? mask0) eqn:E.
    + destruct (1 <=? b0) eqn:E0.
      * epose proof (divmodc_spec a b0 E0 E) as I1.
        destruct (divmodc a b0) as [c0 c1].
        destruct I1 as [I1 I2].
        unfold fst.
        solve_v1.
        rewrite (Z.mod_small _ (2^54)) by lia.
        rewrite Z.mul_0_l,Z.add_0_r.
        lia.
      * replace b0 with 0 by lia.
        cbn.
        rewrite Zdiv_0_r; lia.
    + apply div'_spec.
  - apply div'_spec.
Qed.



Definition to_nat x := Z.to_nat (toZ x).
Definition of_nat x := ofZ (Z.of_nat x).

Lemma inj_succ a:
  to_nat (succ a) = S (to_nat a).
Proof.
  unfold to_nat.
  rewrite succ_spec.
  epose proof (toZ_ge0 a).
  lia.
Qed.

Lemma inj_pred a:
  match pred a with
  | Some a0 => to_nat a = S (to_nat a0)
  | None => to_nat a = O
  end.
Proof.
  unfold to_nat.
  epose proof (pred_spec a).
  destruct (pred a).
  - epose proof (toZ_ge0 b); lia.
  - lia.
Qed.

Lemma inj_is0 a:
  Bool.reflect (to_nat a = O) (is0 a).
Proof.
  unfold to_nat.
  destruct (is0_spec a); constructor.
  - lia.
  - epose proof (toZ_ge0 a); lia.
Qed.

Open Scope nat.

Lemma inj_add a b:
  to_nat (add a b) = to_nat a + to_nat b.
Proof.
  unfold to_nat.
  rewrite add_spec.
  epose proof (toZ_ge0 a).
  epose proof (toZ_ge0 b).
  lia.
Qed.

Lemma inj_sub a b:
  to_nat (sub a b) = to_nat a - to_nat b.
Proof.
  unfold to_nat.
  rewrite sub_spec.
  epose proof (toZ_ge0 a).
  epose proof (toZ_ge0 b).
  lia.
Qed.

Lemma inj_mul a b:
  to_nat (mul a b) = to_nat a * to_nat b.
Proof.
  unfold to_nat.
  rewrite mul_spec.
  epose proof (toZ_ge0 a).
  epose proof (toZ_ge0 b).
  lia.
Qed.

Lemma inj_div a b:
  to_nat (div a b) = to_nat a / to_nat b.
Proof.
  unfold to_nat.
  rewrite div_spec.
  epose proof (toZ_ge0 a).
  epose proof (toZ_ge0 b).
  rewrite Z2Nat.inj_div; lia.
Qed.

Ltac rw_N' :=
  repeat (
  rewrite inj_succ in * ||
  rewrite inj_add in * ||
  rewrite inj_sub in * ||
  rewrite inj_mul in * ||
  rewrite inj_div in *
  ).

Notation N' := BigUint.

Notation N0 := BigUintNil.
Definition N1 := Eval compute in (succ N0).
Declare Scope N'_scope.
Delimit Scope N'_scope with N'.
Notation "a + b" := (add a b) : N'_scope.
Notation "a - b" := (sub a b) : N'_scope.
Notation "a * b" := (mul a b) : N'_scope.
Notation "a / b" := (div a b) : N'_scope.
Notation "a <=? b" := (leb a b) : N'_scope.
Notation "a <? b" := (ltb a b) : N'_scope.
Notation "a =? b" := (eqb a b) : N'_scope.



