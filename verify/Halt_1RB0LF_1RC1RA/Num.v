(** Two-limb signed integers on Rocq's primitive 63-bit ints, with exact specifications in Z.
    The checker runs on these, in the kernel under native_compute and in OCaml after extraction. *)
From Coq Require Import ZArith Lia Uint63.
Local Open Scope Z_scope.

Record W := mkW { hi : int; lo : int }.

Local Notation phi := Uint63.to_Z.
Notation P63 := 9223372036854775808%Z.
Notation P62 := 4611686018427387904%Z.
Notation P125 := 42535295865117307932921825928971026432%Z.
Notation P120 := 1329227995784915872903807060280344576%Z.

Definition sg (h : int) : Z := if phi h <? P62 then phi h else phi h - P63.
Definition val (x : W) : Z := sg (hi x) * P63 + phi (lo x).

Lemma wB_eq : wB = P63.
Proof. reflexivity. Qed.

Lemma phi_bd (x : int) : 0 <= phi x < P63.
Proof. pose proof (to_Z_bounded x) as H. rewrite wB_eq in H. exact H. Qed.

Lemma sg_bd h : -P62 <= sg h < P62.
Proof. unfold sg. pose proof (phi_bd h). destruct (Z.ltb_spec (phi h) P62); lia. Qed.

Lemma sg_cases h : phi h = sg h \/ phi h = sg h + P63.
Proof. unfold sg. destruct (Z.ltb_spec (phi h) P62); lia. Qed.

Lemma sg_of h z : -P62 <= z < P62 -> phi h = z mod P63 -> sg h = z.
Proof.
  intros Hz H. unfold sg. pose proof (phi_bd h).
  destruct (Z.ltb_spec (phi h) P62); Z.div_mod_to_equations; lia.
Qed.

Lemma lo_bd x : 0 <= phi (lo x) < P63.
Proof. apply phi_bd. Qed.

Lemma val_mk h l z : -P62 <= z < P62 -> phi h = z mod P63 -> val (mkW h l) = z * P63 + phi l.
Proof. intros Hz H. unfold val. cbn [hi lo]. rewrite (sg_of h z Hz H). reflexivity. Qed.

Lemma val_bd x : -P125 <= val x < P125.
Proof. unfold val. pose proof (sg_bd (hi x)). pose proof (lo_bd x). lia. Qed.

Lemma phi_add a b : phi (a + b)%uint63 = (phi a + phi b) mod P63.
Proof. rewrite add_spec, wB_eq. reflexivity. Qed.
Lemma phi_sub a b : phi (a - b)%uint63 = (phi a - phi b) mod P63.
Proof. rewrite sub_spec, wB_eq. reflexivity. Qed.
Lemma phi_one : phi 1%uint63 = 1.
Proof. reflexivity. Qed.

Lemma mod_shift z k : (z + k * P63) mod P63 = z mod P63.
Proof. apply Z.mod_add. lia. Qed.

Lemma hi_add a b c : phi (a + b + c)%uint63 = (sg a + sg b + phi c) mod P63.
Proof.
  rewrite !phi_add. rewrite Z.add_mod_idemp_l by lia.
  destruct (sg_cases a) as [Ha|Ha]; destruct (sg_cases b) as [Hb|Hb]; rewrite Ha, Hb.
  - reflexivity.
  - rewrite <- (mod_shift (sg a + sg b + phi c) 1). f_equal. lia.
  - rewrite <- (mod_shift (sg a + sg b + phi c) 1). f_equal. lia.
  - rewrite <- (mod_shift (sg a + sg b + phi c) 2). f_equal. lia.
Qed.

Lemma hi_sub a b c : phi (a - b - c)%uint63 = (sg a - sg b - phi c) mod P63.
Proof.
  rewrite !phi_sub. rewrite Zminus_mod_idemp_l.
  destruct (sg_cases a) as [Ha|Ha]; destruct (sg_cases b) as [Hb|Hb]; rewrite Ha, Hb.
  - reflexivity.
  - rewrite <- (mod_shift (sg a - sg b - phi c) (-1)). f_equal. lia.
  - rewrite <- (mod_shift (sg a - sg b - phi c) 1). f_equal. lia.
  - reflexivity || (f_equal; lia).
Qed.

(** Addition and subtraction wrap; they are exact when the true result is in range. *)
Definition add (x y : W) : W :=
  let l := (lo x + lo y)%uint63 in
  if (l <? lo x)%uint63 then mkW (hi x + hi y + 1)%uint63 l else mkW (hi x + hi y + 0)%uint63 l.

Definition sub (x y : W) : W :=
  let l := (lo x - lo y)%uint63 in
  if (lo x <? lo y)%uint63 then mkW (hi x - hi y - 1)%uint63 l else mkW (hi x - hi y - 0)%uint63 l.

Lemma val_add x y : -P125 <= val x + val y < P125 -> val (add x y) = val x + val y.
Proof.
  intros R. unfold add. cbv zeta.
  pose proof (lo_bd x) as Lx. pose proof (lo_bd y) as Ly.
  pose proof (phi_add (lo x) (lo y)) as El.
  pose proof (phi_bd (lo x + lo y)%uint63) as Bl.
  unfold val in R.
  destruct ((lo x + lo y) <? lo x)%uint63 eqn:C.
  - apply ltb_spec in C.
    assert (El' : phi (lo x + lo y)%uint63 = phi (lo x) + phi (lo y) - P63).
    { rewrite El in *. Z.div_mod_to_equations. lia. }
    rewrite (val_mk _ _ (sg (hi x) + sg (hi y) + 1)).
    + unfold val. lia.
    + lia.
    + rewrite hi_add, phi_one. reflexivity.
  - assert (El' : phi (lo x + lo y)%uint63 = phi (lo x) + phi (lo y)).
    { assert (C' : phi (lo x) <= phi (lo x + lo y)%uint63).
      { destruct (Z.le_gt_cases (phi (lo x)) (phi (lo x + lo y)%uint63)) as [G|G]; [exact G|].
        apply ltb_spec in G. congruence. }
      rewrite El in *. Z.div_mod_to_equations. lia. }
    rewrite (val_mk _ _ (sg (hi x) + sg (hi y) + 0)).
    + unfold val. lia.
    + lia.
    + rewrite hi_add. reflexivity.
Qed.

Lemma val_sub x y : -P125 <= val x - val y < P125 -> val (sub x y) = val x - val y.
Proof.
  intros R. unfold sub. cbv zeta.
  pose proof (lo_bd x) as Lx. pose proof (lo_bd y) as Ly.
  pose proof (phi_sub (lo x) (lo y)) as El.
  pose proof (phi_bd (lo x - lo y)%uint63) as Bl.
  unfold val in R.
  destruct (lo x <? lo y)%uint63 eqn:C.
  - apply ltb_spec in C.
    assert (El' : phi (lo x - lo y)%uint63 = phi (lo x) - phi (lo y) + P63).
    { rewrite El in *. Z.div_mod_to_equations. lia. }
    rewrite (val_mk _ _ (sg (hi x) - sg (hi y) - 1)).
    + unfold val. lia.
    + lia.
    + rewrite hi_sub, phi_one. reflexivity.
  - assert (El' : phi (lo x - lo y)%uint63 = phi (lo x) - phi (lo y)).
    { assert (C' : phi (lo y) <= phi (lo x)).
      { destruct (Z.le_gt_cases (phi (lo y)) (phi (lo x))) as [G|G]; [exact G|].
        apply ltb_spec in G. congruence. }
      rewrite El in *. Z.div_mod_to_equations. lia. }
    rewrite (val_mk _ _ (sg (hi x) - sg (hi y) - 0)).
    + unfold val. lia.
    + lia.
    + rewrite hi_sub. reflexivity.
Qed.

(** Comparison. *)
Definition flip (h : int) : int := (h + 4611686018427387904)%uint63.
Lemma phi_flip h : phi (flip h) = sg h + P62.
Proof.
  unfold flip. rewrite phi_add. change (phi 4611686018427387904%uint63) with P62.
  pose proof (sg_bd h). destruct (sg_cases h) as [H'|H']; rewrite H'.
  - apply Z.mod_small. lia.
  - replace (sg h + P63 + P62) with (sg h + P62 + 1 * P63) by lia.
    rewrite mod_shift. apply Z.mod_small. lia.
Qed.

Definition ltb (x y : W) : bool :=
  if (hi x =? hi y)%uint63 then (lo x <? lo y)%uint63 else (flip (hi x) <? flip (hi y))%uint63.

Lemma hi_inj a b : sg a = sg b -> a = b.
Proof.
  intros H. apply to_Z_inj. pose proof (phi_bd a). pose proof (phi_bd b).
  destruct (sg_cases a) as [A|A]; destruct (sg_cases b) as [B|B]; lia.
Qed.

Lemma ltb_spec_W x y : ltb x y = true <-> val x < val y.
Proof.
  unfold ltb, val. pose proof (lo_bd x) as Lx. pose proof (lo_bd y) as Ly.
  destruct (hi x =? hi y)%uint63 eqn:E.
  - apply eqb_spec in E. rewrite E. rewrite Uint63.ltb_spec. lia.
  - rewrite Uint63.ltb_spec, !phi_flip.
    assert (N : sg (hi x) <> sg (hi y)).
    { intros N. apply hi_inj in N. rewrite N in E. rewrite eqb_refl in E. discriminate. }
    lia.
Qed.

Definition leb (x y : W) : bool := negb (ltb y x).
Lemma leb_spec_W x y : leb x y = true <-> val x <= val y.
Proof.
  unfold leb. destruct (ltb y x) eqn:E; cbn.
  - apply ltb_spec_W in E. split; [discriminate|lia].
  - split; [|reflexivity]. intros _. destruct (Z.le_gt_cases (val x) (val y)) as [G|G]; [exact G|].
    apply ltb_spec_W in G. congruence.
Qed.

Definition eqb (x y : W) : bool := (hi x =? hi y)%uint63 && (lo x =? lo y)%uint63.
Lemma eqb_spec_W x y : eqb x y = true <-> val x = val y.
Proof.
  unfold eqb, val. rewrite Bool.andb_true_iff, !eqb_spec. pose proof (lo_bd x). pose proof (lo_bd y).
  split.
  - intros [-> ->]. reflexivity.
  - intros E. assert (S : sg (hi x) = sg (hi y)) by lia. split.
    + apply hi_inj. exact S.
    + apply to_Z_inj. lia.
Qed.

(** Low bits. *)
Definition low2 (x : W) : int := (lo x land 3)%uint63.
Lemma phi_low2 x : phi (low2 x) = val x mod 4.
Proof.
  unfold low2. rewrite land_spec'. change (phi 3%uint63) with (Z.ones 2).
  rewrite Z.land_ones by lia. change (2^2) with 4. unfold val.
  replace (sg (hi x) * P63 + phi (lo x)) with (phi (lo x) + (sg (hi x) * 2305843009213693952) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(** Bound checks. Within [fits], the few additions and small multiples in one letter stay in range. *)
Notation P118 := 332306998946228968225951765070086144%Z.
Notation P124 := 21267647932558653966460912964485513216%Z.

Definition fits (x : W) : bool := ((hi x + 36028797018963968) <? 72057594037927936)%uint63.
Lemma fits_spec x : fits x = true -> -P118 <= val x < P118.
Proof.
  unfold fits. rewrite Uint63.ltb_spec, phi_add.
  change (phi 36028797018963968%uint63) with 36028797018963968.
  change (phi 72057594037927936%uint63) with 72057594037927936.
  intros H. unfold val. pose proof (lo_bd x). pose proof (sg_bd (hi x)). pose proof (phi_bd (hi x)).
  destruct (sg_cases (hi x)) as [E|E]; rewrite E in H.
  - destruct (Z.ltb_spec (sg (hi x) + 36028797018963968) P63).
    + rewrite Z.mod_small in H by lia. lia.
    + rewrite <- (mod_shift _ (-1)) in H. rewrite Z.mod_small in H by lia. lia.
  - replace (sg (hi x) + P63 + 36028797018963968) with (sg (hi x) + 36028797018963968 + 1 * P63) in H by lia.
    rewrite mod_shift in H.
    destruct (Z.ltb_spec (sg (hi x) + 36028797018963968) 0).
    + rewrite <- (mod_shift _ 1) in H. rewrite Z.mod_small in H by lia. lia.
    + rewrite Z.mod_small in H by lia. lia.
Qed.

(** Constants: [wc n] has value [n]. *)
Definition wc (n : int) : W := mkW 0%uint63 n.
Lemma val_wc n : val (wc n) = phi n.
Proof. unfold wc, val. cbn [hi lo]. change (sg 0%uint63) with 0. lia. Qed.

Lemma mulc_eq x y : phi x * phi y = phi (fst (mulc x y)) * P63 + phi (snd (mulc x y)).
Proof. rewrite <- wB_eq. apply mulc_spec. Qed.

(** Full product when one factor is below 2^31: two machine multiplications instead of four. *)
Definition P31 : Z := 2147483648.
Definition mulc31 (k b : int) : int * int :=
  let bl := (b land 2147483647)%uint63 in
  let bh := (b >> 31)%uint63 in
  let p0 := (k * bl)%uint63 in
  let t := (k * bh + (p0 >> 31))%uint63 in
  ((t >> 32)%uint63, (((t land 4294967295) << 31) + (p0 land 2147483647))%uint63).

Lemma phi_land_31 x : phi (x land 2147483647)%uint63 = phi x mod 2147483648.
Proof.
  rewrite land_spec'. change (phi 2147483647%uint63) with (Z.ones 31). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma phi_land_32 x : phi (x land 4294967295)%uint63 = phi x mod 4294967296.
Proof.
  rewrite land_spec'. change (phi 4294967295%uint63) with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma phi_lsr_31 x : phi (x >> 31)%uint63 = phi x / 2147483648.
Proof. rewrite lsr_spec. reflexivity. Qed.
Lemma phi_lsr_32 x : phi (x >> 32)%uint63 = phi x / 4294967296.
Proof. rewrite lsr_spec. reflexivity. Qed.
Lemma phi_lsl_31 x : phi x < 4294967296 -> phi (x << 31)%uint63 = phi x * 2147483648.
Proof.
  intros H. rewrite lsl_spec, wB_eq. change (2 ^ phi 31%uint63) with 2147483648.
  pose proof (phi_bd x). apply Z.mod_small. lia.
Qed.

Lemma mulc31_spec k b : phi k < 2147483648 ->
  phi k * phi b = phi (fst (mulc31 k b)) * P63 + phi (snd (mulc31 k b)).
Proof.
  intros Hk. unfold mulc31. cbv zeta. cbn [fst snd].
  pose proof (phi_bd k) as Bk. pose proof (phi_bd b) as Bb.
  set (bl := (b land 2147483647)%uint63). set (bh := (b >> 31)%uint63).
  assert (Ebl : phi bl = phi b mod 2147483648) by apply phi_land_31.
  assert (Ebh : phi bh = phi b / 2147483648) by apply phi_lsr_31.
  assert (Db : phi b = phi bh * 2147483648 + phi bl) by (rewrite Ebl, Ebh; Z.div_mod_to_equations; lia).
  assert (Bbl : 0 <= phi bl < 2147483648) by (rewrite Ebl; Z.div_mod_to_equations; lia).
  assert (Bbh : 0 <= phi bh < 4294967296) by (rewrite Ebh; Z.div_mod_to_equations; lia).
  set (p0 := (k * bl)%uint63).
  assert (Ep0 : phi p0 = phi k * phi bl).
  { unfold p0. rewrite mul_spec, wB_eq. apply Z.mod_small. nia. }
  assert (Ep1 : phi (k * bh)%uint63 = phi k * phi bh).
  { rewrite mul_spec, wB_eq. apply Z.mod_small. nia. }
  assert (Es : phi (p0 >> 31)%uint63 = phi p0 / 2147483648) by apply phi_lsr_31.
  assert (Bp0 : phi p0 / 2147483648 < 2147483648).
  { rewrite Ep0. apply Z.div_lt_upper_bound; nia. }
  assert (Bp0' : 0 <= phi p0 / 2147483648) by (apply Z.div_pos; pose proof (phi_bd p0); lia).
  assert (Bp1 : phi k * phi bh <= (2147483648 - 1) * (4294967296 - 1)) by nia.
  assert (Bp1' : 0 <= phi k * phi bh) by nia.
  set (t := (k * bh + (p0 >> 31))%uint63).
  assert (Et : phi t = phi k * phi bh + phi p0 / 2147483648).
  { unfold t. rewrite phi_add, Ep1, Es. apply Z.mod_small. lia. }
  assert (Eh : phi (t >> 32)%uint63 = phi t / 4294967296) by apply phi_lsr_32.
  assert (Em : phi (t land 4294967295)%uint63 = phi t mod 4294967296) by apply phi_land_32.
  assert (Bm : phi t mod 4294967296 < 4294967296) by (Z.div_mod_to_equations; lia).
  assert (Bm0 : 0 <= phi t mod 4294967296) by (Z.div_mod_to_equations; lia).
  assert (Es1 : phi ((t land 4294967295) << 31)%uint63 = phi t mod 4294967296 * 2147483648).
  { rewrite phi_lsl_31; rewrite ?Em; [reflexivity|lia]. }
  assert (El : phi (p0 land 2147483647)%uint63 = phi p0 mod 2147483648) by apply phi_land_31.
  assert (Bl : 0 <= phi p0 mod 2147483648 < 2147483648) by (Z.div_mod_to_equations; lia).
  rewrite phi_add, Es1, El, Eh. rewrite Z.mod_small by lia.
  assert (Dt : phi t = phi t / 4294967296 * 4294967296 + phi t mod 4294967296) by (Z.div_mod_to_equations; lia).
  assert (Dp : phi p0 = phi p0 / 2147483648 * 2147483648 + phi p0 mod 2147483648) by (Z.div_mod_to_equations; lia).
  rewrite Db. rewrite Z.mul_add_distr_l. rewrite <- Ep0.
  replace (phi k * (phi bh * 2147483648)) with ((phi k * phi bh) * 2147483648) by ring.
  assert (Et' : phi k * phi bh = phi t - phi p0 / 2147483648) by lia.
  rewrite Et'. lia.
Qed.

(** Full product, taking the cheap route when it can. *)
Definition mulc2 (a b : int) : int * int :=
  if (a <? 2147483648)%uint63 then
    if (b <? 2147483648)%uint63 then (0%uint63, (a * b)%uint63) else mulc31 a b
  else if (b <? 2147483648)%uint63 then mulc31 b a
  else mulc a b.

Lemma mulc2_spec a b : phi a * phi b = phi (fst (mulc2 a b)) * P63 + phi (snd (mulc2 a b)).
Proof.
  unfold mulc2. destruct (a <? 2147483648)%uint63 eqn:A.
  { apply Uint63.ltb_spec in A. destruct (b <? 2147483648)%uint63 eqn:B; [|apply mulc31_spec; exact A].
    apply Uint63.ltb_spec in B. cbn [fst snd]. change (phi 2147483648%uint63) with 2147483648 in A, B.
    pose proof (phi_bd a). pose proof (phi_bd b).
    rewrite mul_spec, wB_eq. rewrite Z.mod_small by nia. change (phi 0%uint63) with 0. ring. }
  destruct (b <? 2147483648)%uint63 eqn:B.
  { apply Uint63.ltb_spec in B. rewrite Z.mul_comm. apply mulc31_spec. exact B. }
  apply mulc_eq.
Qed.

(** Product of a one-limb number and a non-negative one, refused when it might not fit. *)
Definition mul1 (x y : W) : option W :=
  if (hi y <? 4611686018427387904)%uint63 then
    let (p0, l0) := mulc2 (lo x) (lo y) in
    let (p1, l1) := mulc2 (lo x) (hi y) in
    let h := (l1 + p0)%uint63 in
    if (p1 =? 0)%uint63 then
      if (h <? l1)%uint63 then None
      else if (h <? 2305843009213693952)%uint63 then Some (mkW h l0) else None
    else None
  else None.

Lemma mul1_spec x y z : hi x = 0%uint63 -> mul1 x y = Some z -> val z = val x * val y /\ 0 <= val z < P124.
Proof.
  intros Hx. unfold mul1.
  destruct (hi y <? 4611686018427387904)%uint63 eqn:Hy; [|discriminate].
  apply Uint63.ltb_spec in Hy. change (phi 4611686018427387904%uint63) with P62 in Hy.
  pose proof (mulc2_spec (lo x) (lo y)) as E0. pose proof (mulc2_spec (lo x) (hi y)) as E1.
  destruct (mulc2 (lo x) (lo y)) as [p0 l0]. destruct (mulc2 (lo x) (hi y)) as [p1 l1].
  cbn [fst snd] in E0, E1.
  destruct (p1 =? 0)%uint63 eqn:Hp; [|discriminate]. apply eqb_spec in Hp. subst p1.
  change (phi 0%uint63) with 0 in E1.
  destruct ((l1 + p0) <? l1)%uint63 eqn:Ho; [discriminate|].
  destruct ((l1 + p0) <? 2305843009213693952)%uint63 eqn:Hb; [|discriminate].
  apply Uint63.ltb_spec in Hb. change (phi 2305843009213693952%uint63) with 2305843009213693952 in Hb.
  intros H. injection H as <-.
  assert (Ho' : phi l1 <= phi (l1 + p0)%uint63).
  { destruct (Z.le_gt_cases (phi l1) (phi (l1 + p0)%uint63)) as [G|G]; [exact G|].
    apply Uint63.ltb_spec in G. congruence. }
  pose proof (phi_add l1 p0) as Eh. pose proof (phi_bd l1). pose proof (phi_bd p0). pose proof (phi_bd l0).
  pose proof (phi_bd (l1 + p0)%uint63).
  assert (Eh' : phi (l1 + p0)%uint63 = phi l1 + phi p0).
  { rewrite Eh in *. Z.div_mod_to_equations. lia. }
  assert (Sy : sg (hi y) = phi (hi y)) by (unfold sg; destruct (Z.ltb_spec (phi (hi y)) P62); lia).
  assert (Sz : sg (l1 + p0)%uint63 = phi (l1 + p0)%uint63) by (unfold sg; destruct (Z.ltb_spec (phi (l1 + p0)%uint63) P62); lia).
  assert (Vx : val x = phi (lo x)) by (unfold val; rewrite Hx; change (sg 0%uint63) with 0; lia).
  assert (Vy : val y = phi (hi y) * P63 + phi (lo y)) by (unfold val; rewrite Sy; lia).
  assert (Vz : val (mkW (l1 + p0)%uint63 l0) = phi (l1 + p0)%uint63 * P63 + phi l0) by (unfold val; cbn [hi lo]; rewrite Sz; reflexivity).
  rewrite Vz, Vx, Vy. split.
  - rewrite Eh'. nia.
  - lia.
Qed.

Definition mul_nn (x y : W) : option W :=
  if (hi x =? 0)%uint63 then mul1 x y
  else if (hi y =? 0)%uint63 then mul1 y x
  else None.

Lemma mul_nn_spec x y z : mul_nn x y = Some z -> val z = val x * val y /\ 0 <= val z < P124.
Proof.
  unfold mul_nn.
  destruct (hi x =? 0)%uint63 eqn:Hx.
  { apply eqb_spec in Hx. apply mul1_spec. exact Hx. }
  destruct (hi y =? 0)%uint63 eqn:Hy; [|discriminate].
  apply eqb_spec in Hy. intros H. destruct (mul1_spec _ _ _ Hy H) as [E B]. split; [lia|exact B].
Qed.

Definition neg (x : W) : W := sub (wc 0%uint63) x.
Lemma val_neg x : -P125 < val x -> val (neg x) = - val x.
Proof.
  intros H. unfold neg. pose proof (val_bd x). rewrite val_sub.
  - rewrite val_wc. change (phi 0%uint63) with 0. lia.
  - rewrite val_wc. change (phi 0%uint63) with 0. lia.
Qed.

(** Signed times non-negative. *)
Definition is_neg (x : W) : bool := ltb x (wc 0%uint63).
Lemma is_neg_spec x : is_neg x = true <-> val x < 0.
Proof. unfold is_neg. rewrite ltb_spec_W, val_wc. reflexivity. Qed.

Definition mul_s (x y : W) : option W :=
  if is_neg x then
    if fits x then
      match mul_nn (neg x) y with Some z => Some (neg z) | None => None end
    else None
  else mul_nn x y.

Lemma mul_s_spec x y z : mul_s x y = Some z -> val z = val x * val y /\ -P124 < val z < P124.
Proof.
  unfold mul_s. destruct (is_neg x) eqn:Hn.
  - apply is_neg_spec in Hn. destruct (fits x) eqn:Hf; [|discriminate].
    apply fits_spec in Hf.
    destruct (mul_nn (neg x) y) as [p|] eqn:Hm; [|discriminate].
    intros H. injection H as <-.
    destruct (mul_nn_spec _ _ _ Hm) as [E B].
    rewrite val_neg in E by lia.
    rewrite val_neg by lia. split; lia.
  - intros H. destruct (mul_nn_spec _ _ _ H) as [E B]. split; lia.
Qed.

(** A small constant times a value in range; wraps, exact when in range. *)
Definition mulk (k : int) (x : W) : W :=
  let (p, l) := mulc2 k (lo x) in mkW (k * hi x + p)%uint63 l.

Lemma val_mulk k x : -P125 <= phi k * val x < P125 -> val (mulk k x) = phi k * val x.
Proof.
  intros R. unfold mulk. pose proof (mulc2_spec k (lo x)) as E.
  destruct (mulc2 k (lo x)) as [p l]. cbn [fst snd] in E.
  pose proof (phi_bd l) as Bl.
  unfold val in R.
  rewrite (val_mk _ _ (phi k * sg (hi x) + phi p)).
  - unfold val. nia.
  - nia.
  - rewrite phi_add, mul_spec, wB_eq. rewrite Z.add_mod_idemp_l by lia.
    destruct (sg_cases (hi x)) as [C|C]; rewrite C.
    + reflexivity.
    + replace (phi k * (sg (hi x) + P63) + phi p) with (phi k * sg (hi x) + phi p + phi k * P63) by ring.
      apply mod_shift.
Qed.

Definition wmin (x y : W) : W := if ltb y x then y else x.
Lemma val_wmin x y : val (wmin x y) = Z.min (val x) (val y).
Proof.
  unfold wmin. destruct (ltb y x) eqn:E.
  - apply ltb_spec_W in E. lia.
  - destruct (Z.le_gt_cases (val x) (val y)) as [G|G]; [lia|]. apply ltb_spec_W in G. congruence.
Qed.

(** Multiplying by a small positive [k]: no signs, one wide product. *)
Definition tight (x : W) : bool := ((hi x + 70368744177664) <? 140737488355328)%uint63.
Lemma tight_spec x : tight x = true -> -(2^109) <= val x < 2^109.
Proof.
  unfold tight. rewrite Uint63.ltb_spec, phi_add.
  change (phi 70368744177664%uint63) with 70368744177664.
  change (phi 140737488355328%uint63) with 140737488355328.
  intros H. unfold val. pose proof (lo_bd x). pose proof (sg_bd (hi x)). pose proof (phi_bd (hi x)).
  assert (B : -70368744177664 <= sg (hi x) < 70368744177664).
  { destruct (sg_cases (hi x)) as [E|E]; rewrite E in H.
    - rewrite Z.mod_small in H by lia. lia.
    - replace (sg (hi x) + P63 + 70368744177664) with (sg (hi x) + 70368744177664 + 1 * P63) in H by lia.
      rewrite mod_shift in H.
      destruct (Z.ltb_spec (sg (hi x) + 70368744177664) 0).
      + rewrite <- (mod_shift _ 1) in H. rewrite Z.mod_small in H by lia. lia.
      + rewrite Z.mod_small in H by lia. lia. }
  change (2^109) with (70368744177664 * P63). lia.
Qed.

Definition mulq (x k : W) : option W :=
  if andb (andb (hi k =? 0)%uint63 (lo k <? 32768)%uint63) (tight x) then Some (mulk (lo k) x) else mul_s x k.

Lemma mulq_spec x k z : mulq x k = Some z -> val z = val x * val k /\ -P124 < val z < P124.
Proof.
  unfold mulq. destruct (andb (andb (hi k =? 0)%uint63 (lo k <? 32768)%uint63) (tight x)) eqn:C; [|apply mul_s_spec].
  apply Bool.andb_true_iff in C. destruct C as [C T]. apply Bool.andb_true_iff in C. destruct C as [H0 L].
  apply Uint63.eqb_spec in H0. apply Uint63.ltb_spec in L. change (phi 32768%uint63) with 32768 in L.
  apply tight_spec in T. change (2^109) with 649037107316853453566312041152512 in T.
  pose proof (phi_bd (lo k)) as Bk.
  assert (Vk : val k = phi (lo k)) by (unfold val; rewrite H0; change (sg 0%uint63) with 0; lia).
  intros Hz. injection Hz as <-.
  assert (R : -P124 < phi (lo k) * val x < P124) by nia.
  rewrite val_mulk by lia. rewrite Vk. split; [ring|lia].
Qed.
