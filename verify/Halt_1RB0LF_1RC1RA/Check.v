(** The checker: phases of the orbit, with jumps, carrying exact application and cost totals. *)
From Coq Require Import ZArith Lia Uint63 List Bool PArith.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Num Big Vec Map Walk Step Sweep.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Record Slots := mkSlots { s60 : Slot; s61 : Slot; s62 : Slot; s63 : Slot; s220 : Slot; s221 : Slot; s222 : Slot; s223 : Slot }.

Definition a0_of (z : bool) : W := if z then wc 22 else wc 6.

Definition get (ss : Slots) (z : bool) (m : int) : Slot :=
  if z then
    if (m =? 0)%uint63 then s220 ss else if (m =? 1)%uint63 then s221 ss else if (m =? 2)%uint63 then s222 ss else s223 ss
  else
    if (m =? 0)%uint63 then s60 ss else if (m =? 1)%uint63 then s61 ss else if (m =? 2)%uint63 then s62 ss else s63 ss.

Definition put (ss : Slots) (z : bool) (m : int) (s : Slot) : Slots :=
  let '(mkSlots a b c d e f g h) := ss in
  if z then
    if (m =? 0)%uint63 then mkSlots a b c d s f g h else if (m =? 1)%uint63 then mkSlots a b c d e s g h
    else if (m =? 2)%uint63 then mkSlots a b c d e f s h else mkSlots a b c d e f g s
  else
    if (m =? 0)%uint63 then mkSlots s b c d e f g h else if (m =? 1)%uint63 then mkSlots a s c d e f g h
    else if (m =? 2)%uint63 then mkSlots a b s d e f g h else mkSlots a b c s e f g h.

Definition slots_ok (ss : Slots) : Prop :=
  slot_ok 6 (s60 ss) /\ slot_ok 6 (s61 ss) /\ slot_ok 6 (s62 ss) /\ slot_ok 6 (s63 ss) /\
  slot_ok 22 (s220 ss) /\ slot_ok 22 (s221 ss) /\ slot_ok 22 (s222 ss) /\ slot_ok 22 (s223 ss).

Definition za (z : bool) : Z := if z then 22 else 6.
Lemma val_a0 z : val (a0_of z) = za z.
Proof. destruct z; reflexivity. Qed.
Lemma fits_a0 z : fits (a0_of z) = true.
Proof. destruct z; reflexivity. Qed.

Lemma get_ok ss z m : slots_ok ss -> slot_ok (za z) (get ss z m).
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold get.
  destruct z; cbn [za]; repeat match goal with |- context [if ?c then _ else _] => destruct c end; assumption.
Qed.

Lemma put_ok ss z m s : slots_ok ss -> slot_ok (za z) s -> slots_ok (put ss z m s).
Proof.
  intros H S. destruct ss as [a b c d e f g h]. destruct H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  cbn [s60 s61 s62 s63 s220 s221 s222 s223] in *. unfold put.
  destruct z; cbn [za] in S; repeat match goal with |- context [if ?c then _ else _] => destruct c end; unfold slots_ok; cbn [s60 s61 s62 s63 s220 s221 s222 s223]; repeat (split; [assumption|]); assumption.
Qed.

Definition empty_slots : Slots :=
  let e6 := empty_slot (wc 6) in let e22 := empty_slot (wc 22) in mkSlots e6 e6 e6 e6 e22 e22 e22 e22.

Lemma empty_slots_ok : slots_ok empty_slots.
Proof.
  pose proof (empty_ok (wc 6) eq_refl) as A. pose proof (empty_ok (wc 22) eq_refl) as C.
  change (val (wc 6)) with 6 in A. change (val (wc 22)) with 22 in C.
  unfold slots_ok, empty_slots. cbn [s60 s61 s62 s63 s220 s221 s222 s223]. repeat (split; [assumption|]); assumption.
Qed.

(** ** Hops: sweeps in a row until the (reset value, residue) comes back *)
Notation Hop := (Sum * W)%type.

Fixpoint seen_mem (z : bool) (m : int) (l : list (bool * int)) : bool :=
  match l with
  | [] => false
  | (z', m') :: t => (Bool.eqb z z' && (m =? m')%uint63) || seen_mem z m t
  end.

Fixpoint hops (n : nat) (ss : Slots) (z0 : bool) (m0 : int) (z : bool) (bb D L : W) (seen : list (bool * int))
  : Slots * list Hop * W * W * bool * Out :=
  match n with
  | O => (ss, [], D, L, false, OFail)
  | S n' =>
    let m := low2 bb in
    if seen_mem z m seen then (ss, [], D, L, false, OFail) else
    let (s', o) := prep (a0_of z) (get ss z m) bb in
    let ss1 := put ss z m s' in
    match o with
    | OSum T =>
      let D1 := add D (sdelta T) in let L1 := add L (slen T) in let bb1 := add bb (sdelta T) in
      if is_reset (sna0 T) && fits (sdelta T) && fits (slen T) && fits D1 && fits L1 && fits bb1 then
        let z' := eqb (sna0 T) (wc 22) in
        if Bool.eqb z' z0 && (low2 bb1 =? m0)%uint63 then (ss1, [(T, bb)], D1, L1, true, o)
        else
          let '(ss2, hs, D2, L2, c, oo) := hops n' ss1 z0 m0 z' bb1 D1 L1 ((z, m) :: seen) in
          (ss2, (T, bb) :: hs, D2, L2, c, oo)
      else (ss1, [], D, L, false, OFail)
    | _ => (ss1, [], D, L, false, o)
    end
  end.

Fixpoint hops_ok (a b : Z) (hs : list Hop) (a' b' : Z) : Prop :=
  match hs with
  | [] => a = a' /\ b = b'
  | (T, bi) :: t =>
    sum_ok a T /\ val bi = b /\ val (sbase T) <= b <= val (shi T) /\ (b - val (sbase T)) mod 4 = 0 /\
    hops_ok (val (sna0 T)) (b + val (sdelta T)) t a' b'
  end.

Fixpoint hs_D (hs : list Hop) : Z := match hs with [] => 0 | (T, _) :: t => val (sdelta T) + hs_D t end.
Fixpoint hs_L (hs : list Hop) : Z := match hs with [] => 0 | (T, _) :: t => val (slen T) + hs_L t end.
Fixpoint hs_cost (hs : list Hop) (s : Z) : Z :=
  match hs with
  | [] => 0
  | (T, bi) :: t => sum_cost T (val bi + s) (val bi - val (sbase T) + s) + hs_cost t s
  end.

Lemma hops_shift a b hs a' b' s : hops_ok a b hs a' b' -> 0 <= s -> s mod 4 = 0 ->
  Forall (fun h : Hop => val (snd h) + s <= val (shi (fst h))) hs ->
  Reach a (b + s) a' (b' + s) (hs_L hs) (hs_cost hs s).
Proof.
  revert a b. induction hs as [|[T bi] t IH]; intros a b H S0 Sm F.
  { destruct H as [-> ->]. constructor. }
  destruct H as (HT & Eb & Hr & Hm & Ht). subst b. inversion F as [|? ? H1 H2]; subst. cbn [fst snd] in H1.
  cbn [hs_L hs_cost].
  pose proof (HT (val bi + s) ltac:(lia)) as R.
  assert (M : (val bi + s - val (sbase T)) mod 4 = 0).
  { replace (val bi + s - val (sbase T)) with ((val bi - val (sbase T)) + s) by ring. apply mod4_add; assumption. }
  specialize (R M).
  pose proof (IH _ _ Ht S0 Sm H2) as R2.
  replace (val bi + s - val (sbase T)) with (val bi - val (sbase T) + s) in R by ring.
  replace (val bi + val (sdelta T) + s) with (val bi + s + val (sdelta T)) in R2 by ring.
  exact (Reach_trans _ _ _ _ _ _ _ _ _ _ R R2).
Qed.

Fixpoint csum (f : Z -> Z) (n : nat) : Z :=
  match n with O => 0 | S n' => csum f n' + f (Z.of_nat n') end.

(** The cycle closes: [n] rounds of it land [n * D] further on. *)
Lemma jump a b hs D n : hops_ok a b hs a (b + D) -> 0 <= D -> D mod 4 = 0 ->
  (forall t, (t < n)%nat -> Forall (fun h : Hop => val (snd h) + Z.of_nat t * D <= val (shi (fst h))) hs) ->
  Reach a b a (b + Z.of_nat n * D) (Z.of_nat n * hs_L hs) (csum (fun t => hs_cost hs (t * D)) n).
Proof.
  intros H D0 Dm F. induction n.
  { cbn [csum]. change (Z.of_nat 0) with 0. replace (b + 0 * D) with b by ring. replace (0 * hs_L hs) with 0 by ring. constructor. }
  cbn [csum].
  specialize (IHn (fun t Ht => F t ltac:(lia))).
  pose proof (F n ltac:(lia)) as Fn.
  pose proof (hops_shift a b hs a (b + D) (Z.of_nat n * D) H ltac:(lia)) as R.
  assert (M : (Z.of_nat n * D) mod 4 = 0).
  { rewrite Z.mul_mod by lia. rewrite Dm. rewrite Z.mul_0_r. reflexivity. }
  specialize (R M Fn).
  pose proof (Reach_trans _ _ _ _ _ _ _ _ _ _ IHn R) as R2.
  eapply Reach_conv; [exact R2|reflexivity| |rewrite Nat2Z.inj_succ; ring|reflexivity].
  rewrite Nat2Z.inj_succ. ring.
Qed.

(** ** Exact sums of t and t^2 *)
Definition zs1 := csum (fun t => t).
Definition zs2 := csum (fun t => t * t).

Lemma zs1_closed n : 2 * zs1 n = Z.of_nat n * (Z.of_nat n - 1).
Proof.
  unfold zs1. induction n; [reflexivity|]. cbn [csum]. rewrite Z.mul_add_distr_l, IHn, Nat2Z.inj_succ. ring.
Qed.
Lemma zs2_closed n : 6 * zs2 n = (Z.of_nat n - 1) * Z.of_nat n * (2 * Z.of_nat n - 1).
Proof.
  unfold zs2. induction n; [reflexivity|]. cbn [csum]. rewrite Z.mul_add_distr_l, IHn, Nat2Z.inj_succ. ring.
Qed.

Lemma csum_poly c0 c1 c2 n :
  csum (fun t => c0 + c1 * t + c2 * (t * t)) n = c0 * Z.of_nat n + c1 * zs1 n + c2 * zs2 n.
Proof.
  unfold zs1, zs2. induction n; [cbn; ring|]. cbn [csum]. rewrite IHn, Nat2Z.inj_succ. ring.
Qed.

Lemma csum_ext f g n : (forall t, f t = g t) -> csum f n = csum g n.
Proof. intros H. induction n; [reflexivity|]. cbn [csum]. rewrite IHn, H. reflexivity. Qed.

Lemma csum_add f g n : csum (fun t => f t + g t) n = csum f n + csum g n.
Proof. induction n; [reflexivity|]. cbn [csum]. rewrite IHn. ring. Qed.

(** Factors whose product is [zs1] and [zs2], chosen by the residue of [T]. *)
Definition tri (T : int) : list int :=
  let T1 := (T - 1)%uint63 in
  if ((T mod 2) =? 0)%uint63 then vmul [(T / 2)%uint63] [T1] else vmul [T] [(T1 / 2)%uint63].

Definition pyr (T : int) : list int :=
  let T1 := (T - 1)%uint63 in
  let T2 := (T + T - 1)%uint63 in
  let r := (T mod 6)%uint63 in
  if (r =? 0)%uint63 then vmul (vmul [T1] [(T / 6)%uint63]) [T2]
  else if (r =? 1)%uint63 then vmul (vmul [(T1 / 6)%uint63] [T]) [T2]
  else if (r =? 2)%uint63 then vmul (vmul [T1] [(T / 2)%uint63]) [(T2 / 3)%uint63]
  else if (r =? 3)%uint63 then vmul (vmul [(T1 / 2)%uint63] [(T / 3)%uint63]) [T2]
  else if (r =? 4)%uint63 then vmul (vmul [(T1 / 3)%uint63] [(T / 2)%uint63]) [T2]
  else vmul (vmul [(T1 / 2)%uint63] [T]) [(T2 / 3)%uint63].

Definition Tmax : Z := 1152921504606846976.

Lemma bval1 x : bval [x] = phi x.
Proof. cbn [bval]. ring. Qed.

Lemma phi_T1 (T : int) : 1 <= phi T <= Tmax -> phi (T - 1)%uint63 = phi T - 1.
Proof. intros H. rewrite Uint63.sub_spec, phi_one. rewrite wB_eq. apply Z.mod_small. unfold Tmax in *. lia. Qed.
Lemma phi_T2 (T : int) : 1 <= phi T <= Tmax -> phi (T + T - 1)%uint63 = 2 * phi T - 1.
Proof.
  intros H. unfold Tmax in *. rewrite Uint63.sub_spec, Uint63.add_spec, phi_one, wB_eq.
  rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. ring.
Qed.
Lemma phi_div (x y : int) : phi (x / y)%uint63 = phi x / phi y.
Proof. apply Uint63.div_spec. Qed.
Lemma phi_mod (x y : int) : phi (x mod y)%uint63 = phi x mod phi y.
Proof. apply Uint63.mod_spec. Qed.
Lemma mul2 : phi 2%uint63 = 2. Proof. reflexivity. Qed.
Lemma mul3 : phi 3%uint63 = 3. Proof. reflexivity. Qed.
Lemma mul6 : phi 6%uint63 = 6. Proof. reflexivity. Qed.

Lemma cong_mul2 x y : cong PM (bval (vmul x y)) (bval x * bval y).
Proof. apply vmul_spec. Qed.

Lemma tri_spec T : 1 <= phi T <= Tmax -> cong PM (bval (tri T)) (zs1 (Z.to_nat (phi T))).
Proof.
  intros HT. unfold tri. cbv zeta.
  pose proof (zs1_closed (Z.to_nat (phi T))) as C. rewrite Z2Nat.id in C by lia.
  set (S1 := zs1 (Z.to_nat (phi T))) in *.
  pose proof (phi_T1 T HT) as E1.
  destruct ((T mod 2) =? 0)%uint63 eqn:P.
  - apply Uint63.eqb_spec in P. apply (f_equal to_Z) in P. rewrite phi_mod, mul2, phi0 in P.
    eapply cong_trans; [apply cong_mul2|]. rewrite !bval1, phi_div, mul2, E1.
    assert (X : phi T / 2 * (phi T - 1) = S1).
    { assert (Q : phi T = 2 * (phi T / 2)) by (Z.div_mod_to_equations; lia). nia. }
    rewrite X. apply cong_refl.
  - assert (P' : phi T mod 2 = 1).
    { assert (N : (T mod 2)%uint63 <> 0%uint63). { intros N. apply Uint63.eqb_spec in N. congruence. }
      assert (N' : phi (T mod 2)%uint63 <> 0). { intros Z0. apply N. apply to_Z_inj. rewrite Z0. reflexivity. }
      rewrite phi_mod, mul2 in N'. Z.div_mod_to_equations. lia. }
    eapply cong_trans; [apply cong_mul2|]. rewrite !bval1, phi_div, mul2, E1.
    assert (X : phi T * ((phi T - 1) / 2) = S1).
    { assert (Q : phi T - 1 = 2 * ((phi T - 1) / 2)) by (Z.div_mod_to_equations; lia). nia. }
    rewrite X. apply cong_refl.
Qed.

Lemma vmul3 x y u : cong PM (bval (vmul (vmul [x] [y]) [u])) (phi x * phi y * phi u).
Proof.
  eapply cong_trans; [apply vmul_spec|]. apply cong_mul; [|rewrite bval1; apply cong_refl].
  eapply cong_trans; [apply vmul_spec|]. rewrite !bval1. apply cong_refl.
Qed.

Lemma pyr_spec T : 1 <= phi T <= Tmax -> cong PM (bval (pyr T)) (zs2 (Z.to_nat (phi T))).
Proof.
  intros HT. unfold pyr. cbv zeta.
  pose proof (zs2_closed (Z.to_nat (phi T))) as C. rewrite Z2Nat.id in C by lia.
  set (S2 := zs2 (Z.to_nat (phi T))) in *.
  pose proof (phi_T1 T HT) as E1. pose proof (phi_T2 T HT) as E2.
  assert (Er : phi (T mod 6)%uint63 = phi T mod 6) by (rewrite phi_mod, mul6; reflexivity).
  set (r := (T mod 6)%uint63) in *.
  set (t := phi T) in *. set (q := t / 6).
  assert (ET : t = 6 * q + phi r) by (rewrite Er; subst q; Z.div_mod_to_equations; lia).
  assert (Br : 0 <= phi r < 6) by (rewrite Er; Z.div_mod_to_equations; lia).
  assert (Fin : forall X, 6 * X = (t - 1) * t * (2 * t - 1) -> X = S2) by (intros X HX; lia).
  destruct (r =? 0)%uint63 eqn:R0.
  { apply Uint63.eqb_spec in R0. rewrite R0 in ET. change (phi 0%uint63) with 0 in ET.
    eapply cong_trans; [apply vmul3|]. rewrite !phi_div, mul6, ?E1, ?E2. fold t.
    replace (t / 6) with q by reflexivity.
    replace ((t - 1) * q * (2 * t - 1)) with S2; [apply cong_refl|]. symmetry. apply Fin. rewrite ET. ring. }
  assert (Nr0 : phi r <> 0). { intros X. assert (r = 0%uint63) by (apply to_Z_inj; exact X). subst r. rewrite H in R0. discriminate. }
  destruct (r =? 1)%uint63 eqn:R1.
  { apply Uint63.eqb_spec in R1. rewrite R1 in ET. change (phi 1%uint63) with 1 in ET.
    eapply cong_trans; [apply vmul3|]. rewrite !phi_div, mul6, ?E1, ?E2. fold t.
    assert (D1 : (t - 1) / 6 = q) by (Z.div_mod_to_equations; lia). rewrite D1.
    replace (q * t * (2 * t - 1)) with S2; [apply cong_refl|]. symmetry. apply Fin. rewrite ET. ring. }
  assert (Nr1 : phi r <> 1). { intros X. assert (r = 1%uint63) by (apply to_Z_inj; exact X). subst r. rewrite H in R1. discriminate. }
  destruct (r =? 2)%uint63 eqn:R2.
  { apply Uint63.eqb_spec in R2. rewrite R2 in ET. change (phi 2%uint63) with 2 in ET.
    eapply cong_trans; [apply vmul3|]. rewrite !phi_div, mul2, mul3, ?E1, ?E2. fold t.
    assert (D1 : t / 2 = 3 * q + 1) by (Z.div_mod_to_equations; lia).
    assert (D2 : (2 * t - 1) / 3 = 4 * q + 1) by (Z.div_mod_to_equations; lia). rewrite D1, D2.
    replace ((t - 1) * (3 * q + 1) * (4 * q + 1)) with S2; [apply cong_refl|]. symmetry. apply Fin. rewrite ET. ring. }
  assert (Nr2 : phi r <> 2). { intros X. assert (r = 2%uint63) by (apply to_Z_inj; exact X). subst r. rewrite H in R2. discriminate. }
  destruct (r =? 3)%uint63 eqn:R3.
  { apply Uint63.eqb_spec in R3. rewrite R3 in ET. change (phi 3%uint63) with 3 in ET.
    eapply cong_trans; [apply vmul3|]. rewrite !phi_div, mul2, mul3, ?E1, ?E2. fold t.
    assert (D1 : (t - 1) / 2 = 3 * q + 1) by (Z.div_mod_to_equations; lia).
    assert (D2 : t / 3 = 2 * q + 1) by (Z.div_mod_to_equations; lia). rewrite D1, D2.
    replace ((3 * q + 1) * (2 * q + 1) * (2 * t - 1)) with S2; [apply cong_refl|]. symmetry. apply Fin. rewrite ET. ring. }
  assert (Nr3 : phi r <> 3). { intros X. assert (r = 3%uint63) by (apply to_Z_inj; exact X). subst r. rewrite H in R3. discriminate. }
  destruct (r =? 4)%uint63 eqn:R4.
  { apply Uint63.eqb_spec in R4. rewrite R4 in ET. change (phi 4%uint63) with 4 in ET.
    eapply cong_trans; [apply vmul3|]. rewrite !phi_div, mul2, mul3, ?E1, ?E2. fold t.
    assert (D1 : (t - 1) / 3 = 2 * q + 1) by (Z.div_mod_to_equations; lia).
    assert (D2 : t / 2 = 3 * q + 2) by (Z.div_mod_to_equations; lia). rewrite D1, D2.
    replace ((2 * q + 1) * (3 * q + 2) * (2 * t - 1)) with S2; [apply cong_refl|]. symmetry. apply Fin. rewrite ET. ring. }
  assert (Nr4 : phi r <> 4). { intros X. assert (r = 4%uint63) by (apply to_Z_inj; exact X). subst r. rewrite H in R4. discriminate. }
  assert (R5 : phi r = 5) by lia. rewrite R5 in ET.
  eapply cong_trans; [apply vmul3|]. rewrite !phi_div, mul2, mul3, ?E1, ?E2. fold t.
  assert (D1 : (t - 1) / 2 = 3 * q + 2) by (Z.div_mod_to_equations; lia).
  assert (D2 : (2 * t - 1) / 3 = 4 * q + 3) by (Z.div_mod_to_equations; lia). rewrite D1, D2.
  replace ((3 * q + 2) * t * (4 * q + 3)) with S2; [apply cong_refl|]. symmetry. apply Fin. rewrite ET. ring.
Qed.

(** ** The cost of one hop over [tk] rounds, in closed form *)
Definition ck (k : int) (v : list int) : list int := if (k =? 0)%uint63 then [] else vmul [k] v.

Lemma ck_spec k v : cong PM (bval (ck k v)) (phi k * bval v).
Proof.
  unfold ck. destruct (k =? 0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst k. change (phi 0%uint63) with 0. apply cong_refl.
  - eapply cong_trans; [apply vmul_spec|]. rewrite bval1. apply cong_refl.
Qed.

Lemma cvadd x y X Y : cong PM (bval x) X -> cong PM (bval y) Y -> cong PM (bval (vadd x y)) (X + Y).
Proof. intros H1 H2. eapply cong_trans; [apply vadd_spec|]. apply cong_add; assumption. Qed.
Lemma cvmul x y X Y : cong PM (bval x) X -> cong PM (bval y) Y -> cong PM (bval (vmul x y)) (X * Y).
Proof. intros H1 H2. eapply cong_trans; [apply vmul_spec|]. apply cong_mul; assumption. Qed.
Lemma cck k x X : cong PM (bval x) X -> cong PM (bval (ck k x)) (phi k * X).
Proof. intros H. eapply cong_trans; [apply ck_spec|]. apply cong_mul; [apply cong_refl|exact H]. Qed.
Lemma cone x : cong PM (bval [x]) (phi x).
Proof. rewrite bval1. apply cong_refl. Qed.

Definition sum_fits (T : Sum) : bool :=
  fits (sbase T) && fits (sU0 T) && fits (sU1 T) && fits (sW0 T) && fits (sW1 T)
  && fits (sae T) && fits (sgae T) && fits (sbe T) && fits (sgbe T).

Definition mulz (x y : W) : option W :=
  if eqb y (wc 0) then Some (wc 0) else if eqb x (wc 0) then Some (wc 0) else mul_s x y.

Lemma mulz_spec x y z : mulz x y = Some z -> val z = val x * val y /\ -P124 < val z < P124.
Proof.
  unfold mulz. destruct (eqb y (wc 0)) eqn:E.
  { intros H. injection H as <-. apply eqb_spec_W in E. rewrite E. rewrite val_wc. change (phi 0%uint63) with 0. lia. }
  destruct (eqb x (wc 0)) eqn:E1.
  { intros H. injection H as <-. apply eqb_spec_W in E1. rewrite E1. rewrite val_wc. change (phi 0%uint63) with 0. lia. }
  apply mul_s_spec.
Qed.

Definition hop_cost (T : Sum) (bi D : W) (tk : int) : option (list int) :=
  if sum_fits T && fits bi && fits D then
    let y0 := sub bi (sbase T) in
    match mulz (sU1 T) y0, mulz (sW1 T) y0, mulz (sgae T) y0, mulz (sgbe T) y0 with
    | Some p1, Some p2, Some p3, Some p4 =>
      let U0' := add (sU0 T) p1 in let W0' := add (sW0 T) p2 in
      let ae' := add (sae T) p3 in let be' := add (sbe T) p4 in
      if fits U0' && fits W0' && fits ae' && fits be' then
        let B4 := of_W (mulk 4 bi) in
        let c0 := vadd (vmul B4 (of_W U0')) (vadd (of_W W0')
                    (vadd (ck (sca T) (vmul (of_W ae') (of_W ae'))) (ck (scb T) (vmul (of_W be') (of_W be'))))) in
        if (tk =? 1)%uint63 then Some c0
        else
          let v1 := vmul (of_W ae') (of_W (sgae T)) in
          let v2 := vmul (of_W be') (of_W (sgbe T)) in
          let c1 := vmul (of_W D) (vadd (vmul B4 (of_W (sU1 T))) (vadd (of_W (mulk 4 U0')) (vadd (of_W (sW1 T))
                      (vadd (ck (sca T) (vadd v1 v1)) (ck (scb T) (vadd v2 v2)))))) in
          let c2 := vmul (vmul (of_W D) (of_W D)) (vadd (of_W (mulk 4 (sU1 T)))
                      (vadd (ck (sca T) (vmul (of_W (sgae T)) (of_W (sgae T)))) (ck (scb T) (vmul (of_W (sgbe T)) (of_W (sgbe T)))))) in
          Some (vadd (vmul [tk] c0) (vadd (vmul (tri tk) c1) (vmul (pyr tk) c2)))
      else None
    | _, _, _, _ => None
    end
  else None.

Definition hop_sum (T : Sum) (bi D : Z) (n : nat) : Z :=
  csum (fun t => sum_cost T (bi + t * D) (bi - val (sbase T) + t * D)) n.

Lemma hop_cost_spec T bi D tk v : 1 <= phi tk <= Tmax -> hop_cost T bi D tk = Some v ->
  cong PM (bval v) (hop_sum T (val bi) (val D) (Z.to_nat (phi tk))).
Proof.
  intros Ht. unfold hop_cost.
  destruct (sum_fits T && fits bi && fits D) eqn:Hf; [|discriminate].
  apply andb_prop in Hf. destruct Hf as [Hf FD]. apply andb_prop in Hf. destruct Hf as [Hf Fb].
  unfold sum_fits in Hf. repeat (apply andb_prop in Hf; destruct Hf as [Hf ?]).
  repeat match goal with H : fits _ = true |- _ => apply fits_spec in H end.
  cbv zeta.
  assert (Vy : val (sub bi (sbase T)) = val bi - val (sbase T)) by (apply val_sub; lia).
  set (y0 := sub bi (sbase T)) in *.
  destruct (mulz (sU1 T) y0) as [p1|] eqn:M1; [|discriminate].
  destruct (mulz (sW1 T) y0) as [p2|] eqn:M2; [|discriminate].
  destruct (mulz (sgae T) y0) as [p3|] eqn:M3; [|discriminate].
  destruct (mulz (sgbe T) y0) as [p4|] eqn:M4; [|discriminate].
  destruct (mulz_spec _ _ _ M1) as [E1 B1]. destruct (mulz_spec _ _ _ M2) as [E2 B2].
  destruct (mulz_spec _ _ _ M3) as [E3 B3]. destruct (mulz_spec _ _ _ M4) as [E4 B4].
  rewrite Vy in E1, E2, E3, E4.
  assert (VU : val (add (sU0 T) p1) = val (sU0 T) + val p1) by (apply val_add; lb).
  assert (VW : val (add (sW0 T) p2) = val (sW0 T) + val p2) by (apply val_add; lb).
  assert (VA : val (add (sae T) p3) = val (sae T) + val p3) by (apply val_add; lb).
  assert (VB : val (add (sbe T) p4) = val (sbe T) + val p4) by (apply val_add; lb).
  set (U0' := add (sU0 T) p1) in *. set (W0' := add (sW0 T) p2) in *.
  set (ae' := add (sae T) p3) in *. set (be' := add (sbe T) p4) in *.
  destruct (fits U0' && fits W0' && fits ae' && fits be') eqn:Hg; [|discriminate].
  repeat (apply andb_prop in Hg; destruct Hg as [Hg ?]).
  repeat match goal with H : fits _ = true |- _ => apply fits_spec in H end.
  assert (V4 : val (mulk 4 bi) = 4 * val bi) by (clear E1 E2 E3 E4; vs; lia).
  assert (V4U : val (mulk 4 U0') = 4 * val U0') by (clear E1 E2 E3 E4; vs; lia).
  assert (V4U1 : val (mulk 4 (sU1 T)) = 4 * val (sU1 T)) by (clear E1 E2 E3 E4; vs; lia).
  set (Y := val bi - val (sbase T)) in *.
  (* the polynomial in t *)
  set (c0z := 4 * val bi * val U0' + val W0' + phi (sca T) * (val ae' * val ae') + phi (scb T) * (val be' * val be')).
  set (c1z := val D * (4 * val bi * val (sU1 T) + 4 * val U0' + val (sW1 T)
                 + phi (sca T) * (2 * (val ae' * val (sgae T))) + phi (scb T) * (2 * (val be' * val (sgbe T))))).
  set (c2z := val D * val D * (4 * val (sU1 T) + phi (sca T) * (val (sgae T) * val (sgae T)) + phi (scb T) * (val (sgbe T) * val (sgbe T)))).
  assert (Poly : forall n, hop_sum T (val bi) (val D) n = c0z * Z.of_nat n + c1z * zs1 n + c2z * zs2 n).
  { intros n. rewrite <- csum_poly. unfold hop_sum. apply csum_ext. intros t.
    unfold sum_cost, c0z, c1z, c2z. rewrite VU, VW, VA, VB, E1, E2, E3, E4. fold Y. ring. }
  assert (C0 : cong PM (bval (vadd (vmul (of_W (mulk 4 bi)) (of_W U0')) (vadd (of_W W0')
                    (vadd (ck (sca T) (vmul (of_W ae') (of_W ae'))) (ck (scb T) (vmul (of_W be') (of_W be'))))))) c0z).
  { pose proof (cvadd _ _ _ _ (cvmul _ _ _ _ (of_W_spec (mulk 4 bi)) (of_W_spec U0'))
        (cvadd _ _ _ _ (of_W_spec W0') (cvadd _ _ _ _ (cck (sca T) _ _ (cvmul _ _ _ _ (of_W_spec ae') (of_W_spec ae')))
           (cck (scb T) _ _ (cvmul _ _ _ _ (of_W_spec be') (of_W_spec be')))))) as P.
    eapply cong_trans; [exact P|]. rewrite V4. unfold c0z. replace (4 * val bi * val U0' + (val W0' + (phi (sca T) * (val ae' * val ae') + phi (scb T) * (val be' * val be'))))
      with (4 * val bi * val U0' + val W0' + phi (sca T) * (val ae' * val ae') + phi (scb T) * (val be' * val be')) by ring. apply cong_refl. }
  destruct (tk =? 1)%uint63 eqn:T1.
  { intros Hv. injection Hv as <-. apply Uint63.eqb_spec in T1. subst tk.
    change (Z.to_nat (phi 1%uint63)) with 1%nat. rewrite Poly. 
    change (zs1 1) with 0. change (zs2 1) with 0. change (Z.of_nat 1) with 1.
    replace (c0z * 1 + c1z * 0 + c2z * 0) with c0z by ring. exact C0. }
  intros Hv. injection Hv as <-.
  rewrite Poly.
  pose proof (Z2Nat.id (phi tk) ltac:(clear - Ht; lia)) as Zt.
  rewrite Zt.
  set (v1 := vmul (of_W ae') (of_W (sgae T))). set (v2 := vmul (of_W be') (of_W (sgbe T))).
  assert (C1 : cong PM (bval (vmul (of_W D) (vadd (vmul (of_W (mulk 4 bi)) (of_W (sU1 T))) (vadd (of_W (mulk 4 U0')) (vadd (of_W (sW1 T))
                      (vadd (ck (sca T) (vadd v1 v1)) (ck (scb T) (vadd v2 v2)))))))) c1z).
  { pose proof (cvmul _ _ _ _ (of_W_spec ae') (of_W_spec (sgae T))) as W1. fold v1 in W1.
    pose proof (cvmul _ _ _ _ (of_W_spec be') (of_W_spec (sgbe T))) as W2. fold v2 in W2.
    pose proof (cvmul _ _ _ _ (of_W_spec D) (cvadd _ _ _ _ (cvmul _ _ _ _ (of_W_spec (mulk 4 bi)) (of_W_spec (sU1 T)))
        (cvadd _ _ _ _ (of_W_spec (mulk 4 U0')) (cvadd _ _ _ _ (of_W_spec (sW1 T))
           (cvadd _ _ _ _ (cck (sca T) _ _ (cvadd _ _ _ _ W1 W1)) (cck (scb T) _ _ (cvadd _ _ _ _ W2 W2))))))) as P.
    eapply cong_trans; [exact P|]. rewrite V4, V4U. unfold c1z.
    match goal with |- cong _ ?x ?y => replace x with y by ring end. apply cong_refl. }
  assert (C2 : cong PM (bval (vmul (vmul (of_W D) (of_W D)) (vadd (of_W (mulk 4 (sU1 T)))
                      (vadd (ck (sca T) (vmul (of_W (sgae T)) (of_W (sgae T)))) (ck (scb T) (vmul (of_W (sgbe T)) (of_W (sgbe T)))))))) c2z).
  { pose proof (cvmul _ _ _ _ (cvmul _ _ _ _ (of_W_spec D) (of_W_spec D)) (cvadd _ _ _ _ (of_W_spec (mulk 4 (sU1 T)))
        (cvadd _ _ _ _ (cck (sca T) _ _ (cvmul _ _ _ _ (of_W_spec (sgae T)) (of_W_spec (sgae T))))
           (cck (scb T) _ _ (cvmul _ _ _ _ (of_W_spec (sgbe T)) (of_W_spec (sgbe T))))))) as P.
    eapply cong_trans; [exact P|]. rewrite V4U1. unfold c2z.
    match goal with |- cong _ ?x ?y => replace x with y by ring end. apply cong_refl. }
  pose proof (cvadd _ _ _ _ (cvmul _ _ _ _ (cone tk) C0) (cvadd _ _ _ _ (cvmul _ _ _ _ (tri_spec tk Ht) C1) (cvmul _ _ _ _ (pyr_spec tk Ht) C2))) as P.
  eapply cong_trans; [exact P|].
  match goal with |- cong _ ?x ?y => replace x with y by ring end. apply cong_refl.
Qed.

(** ** The same sum, the fast way, for few rounds: one term at a time, in place *)
Definition term_add (acc : V) (B4 U Wc : W) (ca : int) (A : W) (cb : int) (Bb : W) : option V :=
  if is_neg B4 || is_neg U || is_neg A || is_neg Bb || negb (ca <? 16)%uint63 || negb (cb <? 16)%uint63 then None else
  let a1 := vaddWW acc B4 U in
  let a2 := vaddW a1 Wc in
  let a3 := if (ca =? 0)%uint63 then a2 else vaddWW a2 (mulk ca A) A in
  let a4 := if (cb =? 0)%uint63 then a3 else vaddWW a3 (mulk cb Bb) Bb in
  Some a4.

Lemma term_add_spec acc B4 U Wc ca A cb Bb v :
  -P118 <= val A < P118 -> -P118 <= val Bb < P118 -> term_add acc B4 U Wc ca A cb Bb = Some v ->
  cong PM (vval v) (vval acc + (val B4 * val U + val Wc + phi ca * (val A * val A) + phi cb * (val Bb * val Bb))).
Proof.
  intros BA BB. unfold term_add.
  destruct (is_neg B4) eqn:N1; [cbn [orb]; discriminate|]. cbn [orb].
  destruct (is_neg U) eqn:N2; [cbn [orb]; discriminate|]. cbn [orb].
  destruct (is_neg A) eqn:N3; [cbn [orb]; discriminate|]. cbn [orb].
  destruct (is_neg Bb) eqn:N4; [cbn [orb]; discriminate|]. cbn [orb].
  destruct (ca <? 16)%uint63 eqn:C1; [|cbn [orb negb]; discriminate]. cbn [orb negb].
  destruct (cb <? 16)%uint63 eqn:C2; [|cbn [orb negb]; discriminate]. cbn [orb negb].
  apply is_neg_false in N1, N2, N3, N4. apply Uint63.ltb_spec in C1, C2.
  change (phi 16%uint63) with 16 in C1, C2.
  pose proof (phi_bd ca). pose proof (phi_bd cb).
  intros Hs. injection Hs as <-.
  pose proof (vaddWW_spec acc B4 U N1 N2) as X1.
  pose proof (vaddW_spec (vaddWW acc B4 U) Wc) as X2.
  set (a1 := vaddWW acc B4 U) in *. set (a2 := vaddW a1 Wc) in *.
  assert (X12 : cong PM (vval a2) (vval acc + val B4 * val U + val Wc)).
  { eapply cong_trans; [exact X2|]. apply cong_add; [exact X1|apply cong_refl]. }
  assert (Ma : val (mulk ca A) = phi ca * val A) by (apply val_mulk; nia).
  assert (Mb : val (mulk cb Bb) = phi cb * val Bb) by (apply val_mulk; nia).
  assert (X3 : cong PM (vval (if (ca =? 0)%uint63 then a2 else vaddWW a2 (mulk ca A) A)) (vval acc + val B4 * val U + val Wc + phi ca * (val A * val A))).
  { destruct (ca =? 0)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst ca. change (phi 0%uint63) with 0. eapply cong_trans; [exact X12|]. exists 0. ring.
    - eapply cong_trans; [apply vaddWW_spec; [rewrite Ma; nia|exact N3]|]. rewrite Ma.
      replace (phi ca * val A * val A) with (phi ca * (val A * val A)) by ring. apply cong_add; [exact X12|apply cong_refl]. }
  set (a3 := if (ca =? 0)%uint63 then a2 else vaddWW a2 (mulk ca A) A) in *.
  destruct (cb =? 0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst cb. change (phi 0%uint63) with 0. eapply cong_trans; [exact X3|]. exists 0. ring.
  - eapply cong_trans; [apply vaddWW_spec; [rewrite Mb; nia|exact N4]|]. rewrite Mb.
    eapply cong_trans; [apply cong_add; [exact X3|apply cong_refl]|]. exists 0. ring.
Qed.

Fixpoint cost_iter (f : nat) (cnt : int) (acc : V) (B4 U Wc A Bb dB4 dU dW dA dBb : W) (ca cb : int) : option V :=
  if (cnt =? 0)%uint63 then Some acc else
  match f with
  | O => None
  | S f' =>
    if fits A && fits Bb then
      match term_add acc B4 U Wc ca A cb Bb with
      | Some acc' =>
        let B4' := add B4 dB4 in let U' := add U dU in let Wc' := add Wc dW in let A' := add A dA in let Bb' := add Bb dBb in
        if fits B4' && fits U' && fits Wc' && fits A' && fits Bb' then
          cost_iter f' (cnt - 1)%uint63 acc' B4' U' Wc' A' Bb' dB4 dU dW dA dBb ca cb
        else None
      | None => None
      end
    else None
  end.

Definition poly_t (B4 U Wc A Bb dB4 dU dW dA dBb : Z) (ca cb : Z) (t : Z) : Z :=
  (B4 + t * dB4) * (U + t * dU) + (Wc + t * dW) + ca * ((A + t * dA) * (A + t * dA)) + cb * ((Bb + t * dBb) * (Bb + t * dBb)).

Lemma poly0 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2 :
  poly_t c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2 0 = c0 * c1 + c2 + k1 * (c3 * c3) + k2 * (c4 * c4).
Proof. unfold poly_t. ring. Qed.

Lemma cost_iter_spec f : forall cnt acc B4 U Wc A Bb dB4 dU dW dA dBb ca cb v,
  fits B4 = true -> fits U = true -> fits Wc = true -> fits dB4 = true -> fits dU = true -> fits dW = true -> fits dA = true -> fits dBb = true ->
  cost_iter f cnt acc B4 U Wc A Bb dB4 dU dW dA dBb ca cb = Some v ->
  cong PM (vval v) (vval acc + csum (poly_t (val B4) (val U) (val Wc) (val A) (val Bb) (val dB4) (val dU) (val dW) (val dA) (val dBb) (phi ca) (phi cb)) (Z.to_nat (phi cnt))).
Proof.
  induction f; intros cnt acc B4 U Wc A Bb dB4 dU dW dA dBb ca cb v F1 F2 F3 F4 F5 F6 F7 F8 H.
  { cbn [cost_iter] in H. destruct (cnt =? 0)%uint63 eqn:E; [|discriminate]. injection H as <-.
    apply Uint63.eqb_spec in E. subst cnt. change (phi 0%uint63) with 0. cbn. exists 0. ring. }
  cbn [cost_iter] in H. destruct (cnt =? 0)%uint63 eqn:E.
  { injection H as <-. apply Uint63.eqb_spec in E. subst cnt. change (phi 0%uint63) with 0. cbn. exists 0. ring. }
  destruct (fits A) eqn:FA; [|cbn [andb] in H; discriminate].
  destruct (fits Bb) eqn:FB; [|cbn [andb] in H; discriminate]. cbn [andb] in H.
  destruct (term_add acc B4 U Wc ca A cb Bb) as [acc'|] eqn:Ht; [|discriminate].
  destruct (fits (add B4 dB4)) eqn:G1; [|cbn [andb] in H; discriminate].
  destruct (fits (add U dU)) eqn:G2; [|cbn [andb] in H; discriminate].
  destruct (fits (add Wc dW)) eqn:G3; [|cbn [andb] in H; discriminate].
  destruct (fits (add A dA)) eqn:G4; [|cbn [andb] in H; discriminate].
  destruct (fits (add Bb dBb)) eqn:G5; [|cbn [andb] in H; discriminate]. cbn [andb] in H.
  pose proof (IHf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G1 G2 G3 F4 F5 F6 F7 F8 H) as R.
  pose proof FA as BA. pose proof FB as BB. apply fits_spec in BA, BB.
  pose proof (term_add_spec _ _ _ _ _ _ _ _ _ BA BB Ht) as T.
  apply fits_spec in F1, F2, F3, F4, F5, F6, F7, F8.
  assert (V1 : val (add B4 dB4) = val B4 + val dB4) by (apply val_add; lia).
  assert (V2 : val (add U dU) = val U + val dU) by (apply val_add; lia).
  assert (V3 : val (add Wc dW) = val Wc + val dW) by (apply val_add; lia).
  assert (V4 : val (add A dA) = val A + val dA) by (apply val_add; lia).
  assert (V5 : val (add Bb dBb) = val Bb + val dBb) by (apply val_add; lia).
  rewrite V1, V2, V3, V4, V5 in R.
  assert (N0 : phi cnt <> 0).
  { intros X. assert (cnt = 0%uint63) by (apply to_Z_inj; exact X). subst cnt. rewrite Uint63.eqb_refl in E. discriminate. }
  pose proof (phi_bd cnt).
  assert (P : phi (cnt - 1)%uint63 = phi cnt - 1).
  { rewrite Uint63.sub_spec, phi_one, wB_eq. apply Z.mod_small. lia. }
  rewrite P in R.
  eapply cong_trans; [exact R|].
  (* peel the first term off the sum *)
  assert (Peel : forall n c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2,
    csum (poly_t c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2) (S n)
    = poly_t c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2 0
      + csum (poly_t (c0 + d0) (c1 + d1) (c2 + d2) (c3 + d3) (c4 + d4) d0 d1 d2 d3 d4 k1 k2) n).
  { intros n c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2. induction n.
    - cbn [csum]. change (Z.of_nat 0) with 0. ring.
    - change (csum (poly_t c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2) (S (S n)))
        with (csum (poly_t c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2) (S n) + poly_t c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 k1 k2 (Z.of_nat (S n))).
      rewrite IHn. cbn [csum]. unfold poly_t. rewrite Nat2Z.inj_succ. ring. }
  replace (Z.to_nat (phi cnt)) with (S (Z.to_nat (phi cnt - 1))) by lia.
  rewrite Peel.
  rewrite poly0. destruct T as [k Ek]. rewrite Ek. exists k. ring.
Qed.

Notation Fsmall := 5%nat.

Definition hop_add (T : Sum) (bi D : W) (tk : int) (acc : V) : option V :=
  if (tk <=? 4)%uint63 then
    if sum_fits T && fits bi && fits D then
      let y0 := sub bi (sbase T) in
      match mulz (sU1 T) y0, mulz (sW1 T) y0, mulz (sgae T) y0, mulz (sgbe T) y0 with
      | Some p1, Some p2, Some p3, Some p4 =>
        let D1 := if (tk =? 1)%uint63 then wc 0 else D in
        match mulz (sU1 T) D1, mulz (sW1 T) D1, mulz (sgae T) D1, mulz (sgbe T) D1 with
        | Some d1, Some d2, Some d3, Some d4 =>
          let B4 := mulk 4 bi in let dB4 := mulk 4 D1 in
          let U0' := add (sU0 T) p1 in let W0' := add (sW0 T) p2 in
          if fits B4 && fits dB4 && fits U0' && fits W0' && fits d1 && fits d2 && fits d3 && fits d4 then
            (* the cost in [t] needs the product 4 * (B + t D) * (U + t (U1 D)), which poly_t has *)
            cost_iter Fsmall tk acc B4 U0' W0' (add (sae T) p3) (add (sbe T) p4) dB4 d1 d2 d3 d4 (sca T) (scb T)
          else None
        | _, _, _, _ => None
        end
      | _, _, _, _ => None
      end
    else None
  else
    match hop_cost T bi D tk with
    | Some v => Some (vplus acc (of_list v))
    | None => None
    end.

Lemma hop_sum_one T bi D : hop_sum T bi D 1 = hop_sum T bi 0 1.
Proof. unfold hop_sum. cbn [csum]. change (Z.of_nat 0) with 0. replace (0 * D) with 0 by ring. replace (0 * 0) with 0 by ring. reflexivity. Qed.

Lemma hop_add_spec T bi D tk acc v : 1 <= phi tk <= Tmax -> hop_add T bi D tk acc = Some v ->
  cong PM (vval v) (vval acc + hop_sum T (val bi) (val D) (Z.to_nat (phi tk))).
Proof.
  intros Ht. unfold hop_add.
  destruct (tk <=? 4)%uint63 eqn:Sm.
  2:{ destruct (hop_cost T bi D tk) as [w|] eqn:Hc; [|discriminate]. intros H. injection H as <-.
      eapply cong_trans; [apply vplus_spec|]. apply cong_add; [apply cong_refl|].
      eapply cong_trans; [apply of_list_spec|]. apply (hop_cost_spec _ _ _ _ _ Ht Hc). }
  destruct (sum_fits T && fits bi && fits D) eqn:Hf; [|discriminate].
  apply andb_prop in Hf. destruct Hf as [Hf FD]. apply andb_prop in Hf. destruct Hf as [Hf Fb].
  unfold sum_fits in Hf. repeat (apply andb_prop in Hf; destruct Hf as [Hf ?]).
  repeat match goal with H : fits _ = true |- _ => apply fits_spec in H end.
  cbv zeta.
  assert (Vy : val (sub bi (sbase T)) = val bi - val (sbase T)) by (apply val_sub; lia).
  set (y0 := sub bi (sbase T)) in *.
  destruct (mulz (sU1 T) y0) as [p1|] eqn:M1; [|discriminate].
  destruct (mulz (sW1 T) y0) as [p2|] eqn:M2; [|discriminate].
  destruct (mulz (sgae T) y0) as [p3|] eqn:M3; [|discriminate].
  destruct (mulz (sgbe T) y0) as [p4|] eqn:M4; [|discriminate].
  destruct (mulz_spec _ _ _ M1) as [E1 B1]. destruct (mulz_spec _ _ _ M2) as [E2 B2].
  destruct (mulz_spec _ _ _ M3) as [E3 B3]. destruct (mulz_spec _ _ _ M4) as [E4 B4].
  rewrite Vy in E1, E2, E3, E4.
  set (D1 := if (tk =? 1)%uint63 then wc 0 else D).
  assert (SD : hop_sum T (val bi) (val D) (Z.to_nat (phi tk)) = hop_sum T (val bi) (val D1) (Z.to_nat (phi tk))).
  { unfold D1. destruct (tk =? 1)%uint63 eqn:T1; [|reflexivity].
    apply Uint63.eqb_spec in T1. subst tk. change (Z.to_nat (phi 1%uint63)) with 1%nat. rewrite val_wc. change (phi 0%uint63) with 0.
    apply hop_sum_one. }
  assert (BD1 : -P118 <= val D1 < P118).
  { unfold D1. destruct (tk =? 1)%uint63; [rewrite val_wc; change (phi 0%uint63) with 0; clear; lia|assumption]. }
  destruct (mulz (sU1 T) D1) as [d1|] eqn:N1; [|discriminate].
  destruct (mulz (sW1 T) D1) as [d2|] eqn:N2; [|discriminate].
  destruct (mulz (sgae T) D1) as [d3|] eqn:N3; [|discriminate].
  destruct (mulz (sgbe T) D1) as [d4|] eqn:N4; [|discriminate].
  destruct (mulz_spec _ _ _ N1) as [G1 C1]. destruct (mulz_spec _ _ _ N2) as [G2 C2].
  destruct (mulz_spec _ _ _ N3) as [G3 C3]. destruct (mulz_spec _ _ _ N4) as [G4 C4].
  destruct (fits (mulk 4 bi) && fits (mulk 4 D1) && fits (add (sU0 T) p1) && fits (add (sW0 T) p2) && fits d1 && fits d2 && fits d3 && fits d4) eqn:Hg; [|discriminate].
  pose proof Hg as Hg'.
  repeat (apply andb_prop in Hg'; destruct Hg' as [Hg' ?]).
  intros Hc.
  pose proof Hc as R. eapply cost_iter_spec in R; try assumption.
  eapply cong_trans; [exact R|]. rewrite SD. apply cong_add; [apply cong_refl|].
  assert (V4 : val (mulk 4 bi) = 4 * val bi) by (clear E1 E2 E3 E4 G1 G2 G3 G4; vs; lia).
  assert (V4D : val (mulk 4 D1) = 4 * val D1) by (clear E1 E2 E3 E4 G1 G2 G3 G4; vs; lia).
  assert (VU : val (add (sU0 T) p1) = val (sU0 T) + val p1) by (apply val_add; lb).
  assert (VW : val (add (sW0 T) p2) = val (sW0 T) + val p2) by (apply val_add; lb).
  assert (VA : val (add (sae T) p3) = val (sae T) + val p3) by (apply val_add; lb).
  assert (VB : val (add (sbe T) p4) = val (sbe T) + val p4) by (apply val_add; lb).
  rewrite V4, V4D, VU, VW, VA, VB, G1, G2, G3, G4, E1, E2, E3, E4.
  replace (hop_sum T (val bi) (val D1) (Z.to_nat (phi tk))) with
    (csum (poly_t (4 * val bi) (val (sU0 T) + val (sU1 T) * (val bi - val (sbase T))) (val (sW0 T) + val (sW1 T) * (val bi - val (sbase T)))
        (val (sae T) + val (sgae T) * (val bi - val (sbase T))) (val (sbe T) + val (sgbe T) * (val bi - val (sbase T)))
        (4 * val D1) (val (sU1 T) * val D1) (val (sW1 T) * val D1) (val (sgae T) * val D1) (val (sgbe T) * val D1) (phi (sca T)) (phi (scb T))) (Z.to_nat (phi tk))).
  { apply cong_refl. }
  unfold hop_sum. apply csum_ext. intros t. unfold poly_t, sum_cost. ring.
Qed.

Fixpoint cost_all (hs : list Hop) (D : W) (tk : int) (acc : V) : option V :=
  match hs with
  | [] => Some acc
  | (T, bi) :: t =>
    match hop_add T bi D tk acc with
    | Some v => cost_all t D tk v
    | None => None
    end
  end.

Lemma cost_all_spec hs D tk acc R v : 1 <= phi tk <= Tmax -> cong PM (vval acc) R -> cost_all hs D tk acc = Some v ->
  cong PM (vval v) (R + csum (fun t => hs_cost hs (t * val D)) (Z.to_nat (phi tk))).
Proof.
  intros Ht. revert acc R. induction hs as [|[T bi] t IH]; intros acc R Ha H.
  { cbn [cost_all] in H. injection H as <-.
    assert (Zr : forall n, csum (fun t0 => hs_cost [] (t0 * val D)) n = 0).
    { intros n. induction n; [reflexivity|]. change (csum (fun t0 => hs_cost [] (t0 * val D)) (S n)) with (csum (fun t0 => hs_cost [] (t0 * val D)) n + 0). rewrite IHn. reflexivity. }
    rewrite Zr, Z.add_0_r. exact Ha. }
  cbn [cost_all] in H. destruct (hop_add T bi D tk acc) as [w|] eqn:Hc; [|discriminate].
  pose proof (hop_add_spec _ _ _ _ _ _ Ht Hc) as Cw.
  assert (Cw' : cong PM (vval w) (R + hop_sum T (val bi) (val D) (Z.to_nat (phi tk)))).
  { eapply cong_trans; [exact Cw|]. apply cong_add; [exact Ha|apply cong_refl]. }
  pose proof (IH _ _ Cw' H) as Rr.
  eapply cong_trans; [exact Rr|].
  cbn [hs_cost]. rewrite csum_add. unfold hop_sum.
  match goal with |- cong _ ?x ?y => replace x with y; [apply cong_refl|] end.
  rewrite Z.add_assoc. reflexivity.
Qed.

(** ** One phase of the orbit *)
Record St := mkSt { sz : bool; sB : W; sl : Slots; sapps : W; sacc : V; sstat : int; sha : W }.

Definition wdiv (n d : W) : W := if ltb n d then wc 0 else adiv n d.

Fixpoint min_take (hs : list Hop) (D acc : W) : W :=
  match hs with
  | [] => acc
  | (T, bi) :: t => min_take t D (wmin acc (wdiv (sub (shi T) bi) D))
  end.

Definition take_of (hs : list Hop) (D B Y : W) : W :=
  let T := add (min_take hs D (wc 1152921504606846975)) (wc 1) in
  match mul_nn T D with
  | Some q => if leb (add B q) Y then T else wmin T (wdiv (sub Y B) D)
  | None => wmin T (wdiv (sub Y B) D)
  end.

Definition valid_take (hs : list Hop) (D B Y tk : W) : bool :=
  (hi tk =? 0)%uint63 && (1 <=? lo tk)%uint63 && (lo tk <=? 1152921504606846976)%uint63 && negb (is_neg D) &&
  match mul_nn tk D, mul_nn (wc (lo tk - 1)%uint63) D with
  | Some q, Some p =>
    fits q && leb (add B q) Y && fits p
    && forallb (fun h : Hop => fits (snd h) && fits (shi (fst h)) && leb (add (snd h) p) (shi (fst h))) hs
  | _, _ => false
  end.

Definition phase (Y : W) (st : St) : St :=
  if negb (sstat st =? 0)%uint63 || leb Y (sB st) then st else
  let z := sz st in let B := sB st in let apps := sapps st in let acc := sacc st in
  let '(ss1, hs, D, L, closed, oo) := hops 8 (sl st) z (low2 B) z B (wc 0) (wc 0) [] in
  match hs with
  | [] =>
    match oo with
    | OHalt a _ U W n =>
      if fits n && fits (add apps n) && negb (is_neg U) && negb (is_neg B) then
        mkSt z B ss1 (add apps n) (vaddW (vaddWW acc (mulk 4 B) U) W) 2 a
      else mkSt z B ss1 apps acc 1 B
    | _ => mkSt z B ss1 apps acc 1 B
    end
  | (T1, B1) :: _ =>
    let tk := take_of hs D B Y in
    if closed && valid_take hs D B Y tk then
      match cost_all hs D (lo tk) acc, mul_nn tk L, mul_nn tk D with
      | Some acc', Some dL, Some q =>
        if fits (add apps dL) && fits (add B q) then mkSt z (add B q) ss1 (add apps dL) acc' 0 B
        else mkSt z B ss1 apps acc 1 B
      | _, _, _ => mkSt z B ss1 apps acc 1 B
      end
    else
      match hop_add T1 B1 (wc 0) 1 vzero with
      | Some v =>
        let B' := add B (sdelta T1) in let apps' := add apps (slen T1) in
        if fits B' && fits apps' then mkSt (eqb (sna0 T1) (wc 22)) B' ss1 apps' (vplus acc v) 0 B
        else mkSt z B ss1 apps acc 1 B
      | None => mkSt z B ss1 apps acc 1 B
      end
  end.

Fixpoint rep (p : positive) (Y : W) (s : St) : St :=
  if negb (sstat s =? 0)%uint63 || leb Y (sB s) then s else
  match p with
  | xH => phase Y s
  | xO p' => rep p' Y (rep p' Y s)
  | xI p' => rep p' Y (rep p' Y (phase Y s))
  end.

(** ** Soundness *)
Lemma is_reset_za x : is_reset x = true -> za (eqb x (wc 22)) = val x.
Proof.
  unfold is_reset. rewrite orb_true_iff. rewrite !eqb_spec_W, !val_wc. autorewrite with lits.
  intros Hx. destruct (eqb x (wc 22)) eqn:E.
  - apply eqb_spec_W in E. rewrite val_wc in E. autorewrite with lits in E. rewrite E. reflexivity.
  - apply eqb_false in E. rewrite val_wc in E. autorewrite with lits in E. cbn [za]. lia.
Qed.

(** The empty result of a hop chain. *)
Ltac nofail :=
  split; [assumption|]; split; [assumption|]; split; [assumption|];
  split; [cbn [hs_D]; lia|]; split; [cbn [hs_L]; lia|];
  split; [eexists; split; [split; [reflexivity|cbn [hs_D]; lia]|discriminate]|];
  split; [intros _; exact I|]; split; [discriminate|constructor].
Ltac nofail_o Po :=
  split; [assumption|]; split; [assumption|]; split; [assumption|];
  split; [cbn [hs_D]; lia|]; split; [cbn [hs_L]; lia|];
  split; [eexists; split; [split; [reflexivity|cbn [hs_D]; lia]|discriminate]|];
  split; [intros _; exact Po|]; split; [discriminate|constructor].

Lemma hops_sound n : forall ss z0 m0 z bb D L seen,
  slots_ok ss -> fits bb = true -> fits D = true -> fits L = true ->
  let '(ss', hs, D', L', c, oo) := hops n ss z0 m0 z bb D L seen in
  slots_ok ss' /\ fits D' = true /\ fits L' = true /\
  val D' = val D + hs_D hs /\ val L' = val L + hs_L hs /\
  (exists a', hops_ok (za z) (val bb) hs a' (val bb + hs_D hs) /\
     (c = true -> a' = za z0 /\ (val bb + hs_D hs) mod 4 = phi m0)) /\
  (hs = [] -> out_ok (za z) bb oo) /\
  (c = true -> hs <> []) /\
  Forall (fun h : Hop => is_reset (sna0 (fst h)) = true /\ fits (sdelta (fst h)) = true /\ fits (slen (fst h)) = true /\ fits (snd h) = true) hs.
Proof.
  induction n; intros ss z0 m0 z bb D L seen Hs Hb HD HL.
  { cbn [hops]. nofail. }
  cbn [hops]. cbv zeta.
  destruct (seen_mem z (low2 bb) seen).
  { nofail. }
  pose proof (prep_sound (a0_of z) (get ss z (low2 bb)) bb (fits_a0 z) Hb) as P.
  rewrite val_a0 in P. specialize (P (get_ok ss z _ Hs)).
  destruct (prep (a0_of z) (get ss z (low2 bb)) bb) as [s' o]. cbn [fst snd] in P. destruct P as [Ps Po].
  pose proof (put_ok ss z (low2 bb) s' Hs Ps) as Hs1.
  destruct o as [T|a b U W m|].
  2:{ nofail_o Po. }
  2:{ nofail_o Po. }
  destruct Po as (HT & Hr & Hm).
  destruct (is_reset (sna0 T)) eqn:Rs; [|cbn [andb]; nofail].
  destruct (fits (sdelta T)) eqn:Fd; [|cbn [andb]; nofail].
  destruct (fits (slen T)) eqn:Fn; [|cbn [andb]; nofail].
  destruct (fits (add D (sdelta T))) eqn:FD1; [|cbn [andb]; nofail].
  destruct (fits (add L (slen T))) eqn:FL1; [|cbn [andb]; nofail].
  destruct (fits (add bb (sdelta T))) eqn:Fb1; [|cbn [andb]; nofail].
  cbn [andb].
  pose proof Fd as Bd. pose proof Fn as Bn. pose proof HD as BD. pose proof HL as BL. pose proof Hb as Bb.
  apply fits_spec in Bd, Bn, BD, BL, Bb.
  assert (VD : val (add D (sdelta T)) = val D + val (sdelta T)) by (apply val_add; lia).
  assert (VL : val (add L (slen T)) = val L + val (slen T)) by (apply val_add; lia).
  assert (Vb : val (add bb (sdelta T)) = val bb + val (sdelta T)) by (apply val_add; lia).
  pose proof (is_reset_za _ Rs) as Za.
  destruct (Bool.eqb (eqb (sna0 T) (wc 22)) z0 && (low2 (add bb (sdelta T)) =? m0)%uint63) eqn:Cl.
  { apply andb_prop in Cl. destruct Cl as [C1 C2]. apply eqb_prop in C1. apply Uint63.eqb_spec in C2.
    cbn [hs_D hs_L].
    split; [assumption|]; split; [assumption|]; split; [assumption|].
    split; [rewrite Z.add_0_r; exact VD|]. split; [rewrite Z.add_0_r; exact VL|].
    split.
    { exists (val (sna0 T)). split.
      - cbn [hops_ok]. split; [exact HT|]. split; [reflexivity|]. split; [exact Hr|]. split; [exact Hm|].
        split; [reflexivity|rewrite Z.add_0_r; reflexivity].
      - intros _. split; [rewrite <- Za, C1; reflexivity|]. rewrite Z.add_0_r, <- Vb, <- phi_low2, C2. reflexivity. }
    split; [discriminate|]. split; [discriminate|].
    constructor; [|constructor]. cbn [fst snd]. repeat split; assumption. }
  pose proof (IHn (put ss z (low2 bb) s') z0 m0 (eqb (sna0 T) (wc 22)) (add bb (sdelta T)) (add D (sdelta T)) (add L (slen T)) ((z, low2 bb) :: seen) Hs1 Fb1 FD1 FL1) as IH.
  destruct (hops n (put ss z (low2 bb) s') z0 m0 (eqb (sna0 T) (wc 22)) (add bb (sdelta T)) (add D (sdelta T)) (add L (slen T)) ((z, low2 bb) :: seen)) as [[[[[ss2 hs] D2] L2] c] oo].
  destruct IH as (I1 & I2 & I3 & I4 & I5 & (a' & I6 & I7) & I8 & I9 & I10).
  rewrite Vb in I6, I7. rewrite VD in I4. rewrite VL in I5. rewrite Za in I6.
  split; [assumption|]; split; [assumption|]; split; [assumption|].
  split; [cbn [hs_D]; lia|]. split; [cbn [hs_L]; lia|].
  split.
  { exists a'. split.
    - cbn [hops_ok hs_D]. split; [exact HT|]. split; [reflexivity|]. split; [exact Hr|]. split; [exact Hm|].
      replace (val bb + (val (sdelta T) + hs_D hs)) with (val bb + val (sdelta T) + hs_D hs) by ring. exact I6.
    - intros Hc. destruct (I7 Hc) as [X1 X2]. split; [exact X1|]. cbn [hs_D].
      replace (val bb + (val (sdelta T) + hs_D hs)) with (val bb + val (sdelta T) + hs_D hs) by ring. exact X2. }
  split; [discriminate|]. split; [discriminate|].
  constructor; [|exact I10]. cbn [fst snd]. repeat split; assumption.
Qed.

Definition st_ok (A0 B0 : Z) (st : St) : Prop :=
  ((sstat st = 0%uint63) -> slots_ok (sl st) /\ fits (sB st) = true /\ fits (sapps st) = true /\
     exists R, Reach A0 B0 (za (sz st)) (val (sB st)) (val (sapps st)) R /\ cong PM (vval (sacc st)) R) /\
  ((sstat st = 2%uint63) ->
     exists R, Reach A0 B0 (val (sha st)) (val (sha st) + 3) (val (sapps st)) R /\ cong PM (vval (sacc st)) R).

Lemma st_fail A0 B0 z B ss apps acc a : st_ok A0 B0 (mkSt z B ss apps acc 1 a).
Proof. split; cbn [sstat]; intros H; apply (f_equal to_Z) in H; discriminate. Qed.

Lemma phase_sound A0 B0 Y st : st_ok A0 B0 st -> st_ok A0 B0 (phase Y st).
Proof.
  intros Hst. unfold phase.
  destruct (negb (sstat st =? 0)%uint63 || leb Y (sB st)) eqn:Done; [exact Hst|].
  apply orb_false_iff in Done. destruct Done as [S0 _].
  apply negb_false_iff, Uint63.eqb_spec in S0.
  destruct Hst as [H0 _]. destruct (H0 S0) as (Hs & FB & Fa & R & HR & HC). clear H0.
  destruct st as [z B ss apps acc stt ha]. cbn [sz sB sl sapps sacc sstat sha] in *. subst stt.
  pose proof (hops_sound 8 ss z (low2 B) z B (wc 0) (wc 0) [] Hs FB eq_refl eq_refl) as G.
  destruct (hops 8 ss z (low2 B) z B (wc 0) (wc 0) []) as [[[[[ss1 hs] D] L] c] oo].
  destruct G as (G1 & G2 & G3 & G4 & G5 & (a' & G6 & G7) & G8 & G9 & G10).
  rewrite val_wc, phi0 in G4, G5. rewrite Z.add_0_l in G4, G5.
  pose proof FB as BB. pose proof Fa as Ba. apply fits_spec in BB, Ba.
  destruct hs as [|[T1 B1] hs'].
  { specialize (G8 eq_refl). destruct oo as [T|a b U W n|]; try exact (st_fail A0 B0 z B ss1 apps acc B).
    destruct G8 as [E8 R8].
    destruct (fits n) eqn:Fn; [|exact (st_fail A0 B0 z B ss1 apps acc B)].
    destruct (fits (add apps n)) eqn:Fan; [|exact (st_fail A0 B0 z B ss1 apps acc B)].
    destruct (is_neg U) eqn:NU; [exact (st_fail A0 B0 z B ss1 apps acc B)|].
    destruct (is_neg B) eqn:NB; [exact (st_fail A0 B0 z B ss1 apps acc B)|]. cbn [andb negb].
    apply is_neg_false in NU, NB.
    pose proof Fn as Bn. apply fits_spec in Bn.
    assert (Va : val (add apps n) = val apps + val n) by (apply val_add; lia).
    split; cbn [sstat sha sapps sacc]; intros Hx.
    - apply (f_equal to_Z) in Hx. discriminate.
    - exists (R + (4 * val B * val U + val W)). split.
      + rewrite Va. rewrite E8 in R8. exact (Reach_trans _ _ _ _ _ _ _ _ _ _ HR R8).
      + assert (V4 : val (mulk 4 B) = 4 * val B) by (vs; lia).
        eapply cong_trans; [apply vaddW_spec|].
        replace (R + (4 * val B * val U + val W)) with ((R + 4 * val B * val U) + val W) by ring.
        apply cong_add; [|apply cong_refl].
        eapply cong_trans; [apply vaddWW_spec; [rewrite V4; lia|exact NU]|]. rewrite V4.
        replace (R + 4 * val B * val U) with (R + 4 * val B * val U) by ring.
        apply cong_add; [exact HC|apply cong_refl]. }
  cbv beta iota zeta.
  match goal with |- context [take_of ?h ?d ?b ?y] => generalize (take_of h d b y) as tk end. intros tk.
  match goal with |- context [if c && ?v then _ else _] => destruct (c && v) eqn:Jump end.
  - apply andb_prop in Jump. destruct Jump as [Cc Vt]. subst c.
    destruct (G7 eq_refl) as [Ae Me]. subst a'. 
    unfold valid_take in Vt.
    apply andb_prop in Vt. destruct Vt as [Vt Mm].
    apply andb_prop in Vt. destruct Vt as [Vt D0].
    apply andb_prop in Vt. destruct Vt as [Vt T2'].
    apply andb_prop in Vt. destruct Vt as [Vt T1'].
    apply Uint63.eqb_spec in Vt.
    apply negb_true_iff, is_neg_false in D0.
    apply Uint63.leb_spec in T1'. apply Uint63.leb_spec in T2'.
    destruct (mul_nn tk D) as [q|] eqn:Mq; [|discriminate].
    destruct (mul_nn (wc (lo tk - 1)%uint63) D) as [p|] eqn:Mp; [|discriminate].
    apply andb_prop in Mm. destruct Mm as [Mm Fall].
    apply andb_prop in Mm. destruct Mm as [Mm Fp].
    apply andb_prop in Mm. destruct Mm as [Fq Lq].
    change (phi 1%uint63) with 1 in T1'. change (phi 1152921504606846976%uint63) with Tmax in T2'.
    assert (Htk : 1 <= phi (lo tk) <= Tmax) by lia.
    assert (Vtk : val tk = phi (lo tk)).
    { unfold val. rewrite Vt. change (sg 0%uint63) with 0. lia. }
    destruct (mul_nn_spec _ _ _ Mq) as [Eq Bq]. destruct (mul_nn_spec _ _ _ Mp) as [Ep Bp].
    rewrite Vtk in Eq.
    rewrite val_wc, phi_T1 in Ep by exact Htk.
    match goal with |- context [cost_all ?h ?d ?t ?a] => destruct (cost_all h d t a) as [acc'|] eqn:Mc end; [|exact (st_fail A0 B0 z B ss1 apps acc B)].
    destruct (mul_nn tk L) as [dL|] eqn:MdL; [|exact (st_fail A0 B0 z B ss1 apps acc B)].
    destruct (mul_nn_spec _ _ _ MdL) as [EdL BdL]. rewrite Vtk in EdL.
    destruct (fits (add apps dL) && fits (add B q)) eqn:Fz; [|exact (st_fail A0 B0 z B ss1 apps acc B)].
    apply andb_prop in Fz. destruct Fz as [Fz1 Fz2].
    pose proof Fq as Bq'. apply fits_spec in Bq'.
    assert (VB' : val (add B q) = val B + val q) by (apply val_add; clear -BB Bq'; lia).
    assert (Vapps : val (add apps dL) = val apps + val dL) by (apply val_add; clear -Ba BdL; lia).
    assert (Dm : val D mod 4 = 0).
    { rewrite G4. rewrite phi_low2 in Me. 
      assert (X : (val B + hs_D ((T1, B1) :: hs') - val B) mod 4 = 0).
      { rewrite Zminus_mod, Me, Z.sub_diag. reflexivity. }
      replace (val B + hs_D ((T1, B1) :: hs') - val B) with (hs_D ((T1, B1) :: hs')) in X by ring. exact X. }
    assert (Gg : hops_ok (za z) (val B) ((T1, B1) :: hs') (za z) (val B + val D)) by (rewrite G4; exact G6).
    set (nn := Z.to_nat (phi (lo tk))).
    assert (Enn : Z.of_nat nn = phi (lo tk)) by (apply Z2Nat.id; lia).
    assert (Rng : forall t, (t < nn)%nat -> Forall (fun h : Hop => val (snd h) + Z.of_nat t * val D <= val (shi (fst h))) ((T1, B1) :: hs')).
    { intros t Ht.
      pose proof (proj1 (forallb_forall _ _) Fall) as Fa2.
      apply Forall_forall. intros h Hin. pose proof (Fa2 h Hin) as Fh.
      apply andb_prop in Fh. destruct Fh as [Fh Lh].
      apply andb_prop in Fh. destruct Fh as [Fh Fs].
      apply leb_spec_W in Lh.
      apply fits_spec in Fs. apply fits_spec in Fh.
      pose proof (fits_spec p Fp) as Bp2.
      rewrite val_add in Lh by lb.
      assert (Tt : Z.of_nat t <= phi (lo tk) - 1) by (clear -Ht Enn; lia).
      assert (Mt : Z.of_nat t * val D <= (phi (lo tk) - 1) * val D) by (apply Z.mul_le_mono_nonneg_r; assumption).
      rewrite Ep in Lh. clear -Lh Mt. lia. }
    pose proof (jump (za z) (val B) ((T1, B1) :: hs') (val D) nn Gg D0 Dm Rng) as Rj.
    pose proof (cost_all_spec _ _ _ _ _ _ Htk HC Mc) as Cc.
    split; cbn [sstat]; intros Hx.
    + split; [exact G1|]. split; [exact Fz2|]. split; [exact Fz1|].
      cbn [sz sB sapps sacc]. exists (R + csum (fun t => hs_cost ((T1, B1) :: hs') (t * val D)) nn). split; [|exact Cc].
      rewrite Enn in Rj. rewrite <- G5 in Rj.
      eapply Reach_conv; [exact (Reach_trans _ _ _ _ _ _ _ _ _ _ HR Rj)|reflexivity| |lia|reflexivity].
      rewrite VB', Eq. reflexivity.
    + apply (f_equal to_Z) in Hx. discriminate.
  - destruct (hop_add T1 B1 (wc 0) 1 vzero) as [v|] eqn:Hv; [|exact (st_fail A0 B0 z B ss1 apps acc B)].
    destruct (fits (add B (sdelta T1)) && fits (add apps (slen T1))) eqn:Fz; [|exact (st_fail A0 B0 z B ss1 apps acc B)].
    apply andb_prop in Fz. destruct Fz as [Fz1 Fz2].
    inversion G10 as [|? ? Hh _]; subst. cbn [fst snd] in Hh. destruct Hh as (Rs & Fd & Fn & Fb1).
    pose proof Fd as Bd. pose proof Fn as Bn. apply fits_spec in Bd, Bn.
    assert (VB' : val (add B (sdelta T1)) = val B + val (sdelta T1)) by (apply val_add; lia).
    assert (Vapps : val (add apps (slen T1)) = val apps + val (slen T1)) by (apply val_add; lia).
    destruct G6 as (Hsum & Eb & Hr & Hm & _).
    pose proof (hop_add_spec T1 B1 (wc 0) 1%uint63 vzero v ltac:(cbv; split; discriminate) Hv) as Cv.
    change (Z.to_nat (phi 1%uint63)) with 1%nat in Cv. unfold hop_sum in Cv. cbn [csum] in Cv.
    rewrite val_wc, phi0 in Cv. change (Z.of_nat 0) with 0 in Cv. rewrite Eb in Cv.
    replace (val B + 0 * 0) with (val B) in Cv by ring.
    replace (val B - val (sbase T1) + 0 * 0) with (val B - val (sbase T1)) in Cv by ring.
    rewrite vval_zero, Z.add_0_l, Z.add_0_l in Cv.
    pose proof (Hsum (val B) Hr Hm) as R1.
    split; cbn [sstat]; intros Hx.
    + split; [exact G1|]. split; [exact Fz1|]. split; [exact Fz2|].
      cbn [sz sB sapps sacc]. exists (R + sum_cost T1 (val B) (val B - val (sbase T1))). split.
      * rewrite is_reset_za by exact Rs. rewrite VB', Vapps. exact (Reach_trans _ _ _ _ _ _ _ _ _ _ HR R1).
      * eapply cong_trans; [apply vplus_spec|]. apply cong_add; assumption.
    + apply (f_equal to_Z) in Hx. discriminate.
Qed.

Lemma rep_sound A0 B0 p Y : forall st, st_ok A0 B0 st -> st_ok A0 B0 (rep p Y st).
Proof.
  induction p as [p IH|p IH|]; intros st H; cbn [rep];
  (destruct (negb (sstat st =? 0)%uint63 || leb Y (sB st)); [exact H|]).
  - apply IH, IH, phase_sound, H.
  - apply IH, IH, H.
  - apply phase_sound, H.
Qed.

(** ** Checking stretches of the orbit *)
Definition start (z : bool) (B : W) : St := mkSt z B empty_slots (wc 0) vzero 0 (wc 0).

Lemma start_ok z B : fits B = true -> st_ok (za z) (val B) (start z B).
Proof.
  intros F. unfold start. split; cbn [sstat]; intros Hx.
  - cbn [sl sB sapps sacc sz]. split; [exact empty_slots_ok|]. split; [exact F|]. split; [reflexivity|].
    exists 0. split; [change (val (wc 0)) with 0; constructor|]. rewrite vval_zero. apply cong_refl.
  - apply (f_equal to_Z) in Hx. discriminate.
Qed.

Definition pfuel : positive := 4611686018427387904%positive.

Definition eqbool (x y : bool) : bool := Bool.eqb x y.

Definition check_seg_gen (p : positive) (z : bool) (B : W) (z1 : bool) (Y : W) : option (W * V) :=
  if fits B && fits Y then
    let st := rep p Y (start z B) in
    if (sstat st =? 0)%uint63 && eqb (sB st) Y && eqbool (sz st) z1 then Some (sapps st, sacc st) else None
  else None.

Theorem check_seg_gen_sound p z B z1 Y n acc : check_seg_gen p z B z1 Y = Some (n, acc) ->
  exists R, Reach (za z) (val B) (za z1) (val Y) (val n) R /\ cong PM (vval acc) R.
Proof.
  unfold check_seg_gen. destruct (fits B) eqn:FB; [|discriminate]. destruct (fits Y) eqn:FY; [|discriminate]. cbn [andb]. cbv zeta.
  pose proof (rep_sound _ _ p Y _ (start_ok z B FB)) as H.
  generalize dependent (rep p Y (start z B)). intros st H.
  destruct (sstat st =? 0)%uint63 eqn:S0; [|discriminate].
  destruct (eqb (sB st) Y) eqn:EB; [|discriminate].
  destruct (eqbool (sz st) z1) eqn:Ez; [|discriminate].
  cbn [andb]. intros Hx. injection Hx as <- <-.
  apply Uint63.eqb_spec in S0. destruct H as [H _]. destruct (H S0) as (_ & _ & _ & R & HR & HC).
  apply eqb_spec_W in EB. apply eqb_prop in Ez.
  exists R. rewrite EB, Ez in HR. split; assumption.
Qed.

Definition w_cap : W := mkW 18014398509481984%uint63 0%uint63.

Definition check_final_gen (p : positive) (z : bool) (B : W) : option (W * W * V) :=
  if fits B then
    let st := rep p w_cap (start z B) in
    if (sstat st =? 2)%uint63 then Some (sha st, sapps st, sacc st) else None
  else None.

Theorem check_final_gen_sound p z B a n acc : check_final_gen p z B = Some (a, n, acc) ->
  exists R, Reach (za z) (val B) (val a) (val a + 3) (val n) R /\ cong PM (vval acc) R.
Proof.
  unfold check_final_gen. destruct (fits B) eqn:FB; [|discriminate]. cbv zeta.
  pose proof (rep_sound _ _ p w_cap _ (start_ok z B FB)) as H.
  generalize dependent (rep p w_cap (start z B)). intros st H.
  destruct (sstat st =? 2)%uint63 eqn:S2; [|discriminate].
  intros Hx. injection Hx as <- <- <-.
  apply Uint63.eqb_spec in S2. destruct H as [_ H]. exact (H S2).
Qed.

(** [check_seg z B z1 Y] runs from the reset state [(z,B)] and must land exactly on [(z1,Y)]. *)
Definition check_seg : bool -> W -> bool -> W -> option (W * V) := check_seg_gen pfuel.
(** [check_final z B] runs from [(z,B)] to the halt form. *)
Definition check_final : bool -> W -> option (W * W * V) := check_final_gen pfuel.

Theorem check_seg_sound z B z1 Y n acc : check_seg z B z1 Y = Some (n, acc) ->
  exists R, Reach (za z) (val B) (za z1) (val Y) (val n) R /\ cong PM (vval acc) R.
Proof. apply check_seg_gen_sound. Qed.
Theorem check_final_sound z B a n acc : check_final z B = Some (a, n, acc) ->
  exists R, Reach (za z) (val B) (val a) (val a + 3) (val n) R /\ cong PM (vval acc) R.
Proof. apply check_final_gen_sound. Qed.
