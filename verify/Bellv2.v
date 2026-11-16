(* 1RB0RB_1LC1RF_0RD0LB_0RA1LE_1LD---_0RB0RC halts (a BB(6) holdout).

   Thomas Reus found the halt and the machine's Bell map ("vampire-like in base 3"):
   https://github.com/thomasreus-bb/Halt-found-1RB0RB_1LC1RF_0RD0LB_0RA1LE_1LD---_0RB0RC
   This file proves it from the transition table alone.

   Bell configurations, with B = 01011 and W a finite word (101 words occur):
     Bl n W m  =  0^inf <D 110 10 1^n W B^m 0^inf
   A Bell step sends n = 3q + r to 4q + e and (W, m) to (W', m + dm - 2), where (W', dm, e) depends only
   on (W, min(m,3), r).  The table's 287 entries, and the halting entry, are lemmas proved by symbolic
   execution (Spec).

   Steps are shift-invariant: if 2^d steps take n to n', they take n + k 3^(2^d) to n' + k 4^(2^d) for
   every k (Jn, Jn_split).  A divide-and-conquer over busycoq's BigInt composes them (Main).  Quotients
   come from untrusted code and every split a = q p + r is re-checked with the verified multiplication
   (BigArith).  The final lemma runs 298,793,334 Bell steps from Bl 4 [] 1, which c0 reaches, and ends on
   a halting entry: W = 00, n = 2 mod 3, m >= 3.

   Trust: Print Assumptions halt lists only the Uint63/PArray primitives of the Rocq standard library
   and their specifications, the same list as BigInt's mul_bigint_correct.  The last step is a
   native_cast_no_check, as in Bellv1.v.  Compiling takes about 3-4 hours with -native-compiler yes and
   needs about 19 GB of memory.

   AI assistance: this proof, the scripts and the checks were produced with the help of Claude
   (Anthropic). *)
From Coq Require Import ZArith NArith Lia Psatz Bool Lists.List Arith PeanoNat.
From Coq Require Uint63 PrimInt63.
Require Import BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical
  BigInt.BigIntMulNormalize BigInt.BigIntMulOpsProof BigInt.BigIntMulCorrect BigInt.BigIntMulFProof
  BigInt.BigIntMulCompose.

Module BigArith.
Import Uint63.
(* Big-integer operations for the Bell D&C, over busycoq's BigInt (list of 8-digit limbs, 18-bit digits).
   Every list pass is tail-recursive (rev_append).  The "verified" operations are proved correct below;
   the "untrusted" ones only steer the computation (their results are always checked). *)

Import ListNotations.

(* ===================== definitions ===================== *)

Definition c0i : int := Uint63.of_Z 0.
Definition c1i : int := Uint63.of_Z 1.
Definition c2i : int := Uint63.of_Z 2.
Definition c3i : int := Uint63.of_Z 3.
Definition c17i : int := Uint63.of_Z 17.
Definition c18i : int := Uint63.of_Z 18.
Definition c63i : int := Uint63.of_Z 63.
Definition c144i : int := Uint63.of_Z 144.
Definition dbase : int := Uint63.of_Z 262144.
Definition dmask : int := Uint63.of_Z 262143.
Definition two9 : int := Uint63.of_Z 512.
Definition two17 : int := Uint63.of_Z 131072.
Definition two18 : int := Uint63.of_Z 262144.
Definition two36 : int := Uint63.of_Z (2 ^ 36).
Definition two54 : int := Uint63.of_Z (2 ^ 54).
Definition two50 : int := Uint63.of_Z (2 ^ 50).
Definition c4s : int := Uint63.of_Z 4.
Definition c33i : int := Uint63.of_Z 33.
Definition c36i : int := Uint63.of_Z 36.
Definition c54i : int := Uint63.of_Z 54.
Definition m9 : int := Uint63.of_Z 954437177.

Definition i2n (x : int) : nat := Z.to_nat (Uint63.to_Z x).
Definition n2i (n : nat) : int := Uint63.of_Z (Z.of_nat n).

Definition zl : limb8 := zero_limb8.

(* ---------- verified ---------- *)

Definition carry_limb (c : int) : bigint :=
  if Uint63.eqb c zero_digit then [] else [limb8_single_digit c].

Fixpoint add1 (c : int) (ys acc : bigint) : bigint :=
  match ys with
  | [] => rev_append acc (carry_limb c)
  | y :: ys' =>
      if Uint63.eqb c zero_digit then rev_append acc ys
      else let '(b, c') := add_limb8_with_carry y zl c in add1 c' ys' (b :: acc)
  end.

Fixpoint addc (c : int) (xs ys acc : bigint) {struct xs} : bigint :=
  match xs with
  | [] => add1 c ys acc
  | x :: xs' =>
      match ys with
      | [] => add1 c xs acc
      | y :: ys' => let '(b, c') := add_limb8_with_carry x y c in addc c' xs' ys' (b :: acc)
      end
  end.

Definition addb (x y : bigint) : bigint := addc zero_digit x y [].

Fixpoint muldc (m c : int) (xs acc : bigint) : bigint :=
  match xs with
  | [] => rev_append acc (carry_limb c)
  | x :: xs' => let '(b, c') := mul_limb8_digit_with_carry m x c in muldc m c' xs' (b :: acc)
  end.

Definition muld (m : int) (x : bigint) : bigint := muldc m zero_digit x [].

Fixpoint shbits (fuel : nat) (s : int) (x : bigint) : bigint :=
  match fuel with
  | O => x
  | S f =>
      if Uint63.eqb s c0i then x
      else if Uint63.leb s c17i then muld (Uint63.lsl c1i s) x
      else shbits f (Uint63.sub s c17i) (muld two17 x)
  end.

Fixpoint prepend_zeros (k : nat) (x : bigint) : bigint :=
  match k with O => x | S k' => prepend_zeros k' (zl :: x) end.

(* L / 144 = (L / 16) / 9 by a multiply-shift, exact for L < 2^34; untrusted, shl checks it *)
Definition div144 (L : int) : int := Uint63.lsr (Uint63.mul (Uint63.lsr L c4s) m9) c33i.

(* x * 2^L = x * 2^s shifted by k limbs, L = 144 k + s (checked) *)
Definition shl (L : int) (x : bigint) : bigint :=
  match x with
  | [] => []
  | _ =>
      let k := div144 L in
      let s := Uint63.sub L (Uint63.mul k c144i) in
      if Uint63.ltb s c144i && Uint63.ltb k two50 then prepend_zeros (i2n k) (shbits 9 s x)
      else shbits (S (i2n L)) L x
  end.

Definition strip (x : bigint) : bigint := rev_append (drop_zero_prefix (rev_append x [])) [].

Fixpoint limbs_eqb (x y : bigint) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => if limb8_eqb a b then limbs_eqb x' y' else false
  | _, _ => false
  end.

Definition eqv (x y : bigint) : bool := limbs_eqb (strip x) (strip y).

Definition digit_ok (d : int) : bool := Uint63.ltb d dbase.
Definition limb_ok (b : limb8) : bool :=
  digit_ok (d0 b) && digit_ok (d1 b) && digit_ok (d2 b) && digit_ok (d3 b) &&
  digit_ok (d4 b) && digit_ok (d5 b) && digit_ok (d6 b) && digit_ok (d7 b).
Fixpoint canonb (x : bigint) : bool :=
  match x with [] => true | b :: x' => if limb_ok b then canonb x' else false end.

Definition shift18 (z : bigint) : bigint := muld two9 (muld two9 z).
Fixpoint horner (x : bigint) (ds : list int) (acc : bigint) : bigint :=
  match ds with
  | [] => acc
  | d :: ds' => horner x ds' (addb (shift18 acc) (muld d x))
  end.
Definition smul (x y : bigint) : bigint := horner x (bigint_digits_u63_rev y []) [].

Fixpoint takec (k : nat) (x acc : bigint) : bigint :=
  match k, x with
  | S k', y :: x' => takec k' x' (y :: acc)
  | _, _ => rev_append acc []
  end.

Fixpoint ilen_aux (x : bigint) (n : int) : int :=
  match x with [] => n | _ :: x' => ilen_aux x' (Uint63.add n c1i) end.
Definition ilen (x : bigint) : int := ilen_aux x c0i.

Definition small_limbs : int := Uint63.of_Z 8.
Definition cap_limbs : int := Uint63.of_Z 500000.

Fixpoint mulx_fuel (fuel : nat) (x y : bigint) : option bigint :=
  match fuel with
  | O => None
  | S f =>
      let lx := ilen x in let ly := ilen y in
      if Uint63.leb ly small_limbs then Some (smul x y)
      else if Uint63.leb lx small_limbs then Some (smul y x)
      else if Uint63.leb (Uint63.add lx ly) cap_limbs then mul_bigint x y
      else if Uint63.ltb lx ly then mulx_fuel f y x
      else
        let k := i2n (Uint63.lsr lx c1i) in
        match mulx_fuel f (skipn k x) y, mulx_fuel f (takec k x []) y with
        | Some z1, Some z0 => Some (addb (prepend_zeros k z1) z0)
        | _, _ => None
        end
  end.

(* fuel from the inputs, not a closed numeral: the kernel must never be able to unfold the recursion *)
Definition mulx (x y : bigint) : option bigint := mulx_fuel (S (length x + length y)) x y.

(* small values: one machine integer below 2^63 *)
Definition to_u63 (a : bigint) : option int :=
  match strip a with
  | [] => Some c0i
  | [b] =>
      if Uint63.ltb (d3 b) two9 && Uint63.eqb (d4 b) c0i && Uint63.eqb (d5 b) c0i &&
         Uint63.eqb (d6 b) c0i && Uint63.eqb (d7 b) c0i
      then Some (Uint63.add (Uint63.add (d0 b) (Uint63.mul (d1 b) two18))
                            (Uint63.add (Uint63.mul (d2 b) two36) (Uint63.mul (d3 b) two54)))
      else None
  | _ => None
  end.

Definition of_u63 (x : int) : bigint :=
  [Limb8 (PrimInt63.mod x two18) (PrimInt63.mod (Uint63.lsr x c18i) two18)
         (PrimInt63.mod (Uint63.lsr x c36i) two18) (Uint63.lsr x c54i)
         c0i c0i c0i c0i].

(* x mod 3, by digit sums (2^18 = 1 mod 3) *)
Definition m3step (acc d : int) : int := PrimInt63.mod (Uint63.add acc d) c3i.
Definition limb_m3 (acc : int) (b : limb8) : int :=
  m3step (m3step (m3step (m3step (m3step (m3step (m3step (m3step acc
    (d0 b)) (d1 b)) (d2 b)) (d3 b)) (d4 b)) (d5 b)) (d6 b)) (d7 b).
Fixpoint mod3_aux (x : bigint) (acc : int) : int :=
  match x with [] => acc | b :: x' => mod3_aux x' (limb_m3 acc b) end.
Definition mod3 (x : bigint) : int := mod3_aux x c0i.

(* ---------- untrusted ---------- *)

Definition sub_digit (x y b : int) : int * int :=
  let t := Uint63.sub (Uint63.add x dbase) (Uint63.add y b) in
  (Uint63.land t dmask, Uint63.sub c1i (Uint63.lsr t c18i)).

Definition sub_limb (x y : limb8) (b : int) : limb8 * int :=
  let '(z0, b0) := sub_digit (d0 x) (d0 y) b in
  let '(z1, b1) := sub_digit (d1 x) (d1 y) b0 in
  let '(z2, b2) := sub_digit (d2 x) (d2 y) b1 in
  let '(z3, b3) := sub_digit (d3 x) (d3 y) b2 in
  let '(z4, b4) := sub_digit (d4 x) (d4 y) b3 in
  let '(z5, b5) := sub_digit (d5 x) (d5 y) b4 in
  let '(z6, b6) := sub_digit (d6 x) (d6 y) b5 in
  let '(z7, b7) := sub_digit (d7 x) (d7 y) b6 in
  (Limb8 z0 z1 z2 z3 z4 z5 z6 z7, b7).

Fixpoint usubc (b : int) (xs ys acc : bigint) {struct xs} : bigint :=
  match xs with
  | [] => rev_append acc []
  | x :: xs' =>
      match ys with
      | [] => if Uint63.eqb b c0i then rev_append acc xs
              else let '(z, b') := sub_limb x zl b in usubc b' xs' [] (z :: acc)
      | y :: ys' => let '(z, b') := sub_limb x y b in usubc b' xs' ys' (z :: acc)
      end
  end.

(* x - y, meaningful when x >= y *)
Definition usub (x y : bigint) : bigint := strip (usubc c0i x y []).

Definition cmp_int (a b : int) : comparison :=
  if Uint63.ltb a b then Lt else if Uint63.ltb b a then Gt else Eq.

Fixpoint nbits (fuel : nat) (d acc : int) : int :=
  match fuel with
  | O => acc
  | S f => if Uint63.eqb d c0i then acc else nbits f (Uint63.lsr d c1i) (Uint63.add acc c1i)
  end.
Definition digit_bits (d : int) : int := nbits 63 d c0i.

Definition limb_bits (b : limb8) : int :=
  let f (i : Z) (d acc : int) := if Uint63.eqb d c0i then acc else Uint63.add (Uint63.of_Z i) (digit_bits d) in
  f 126%Z (d7 b) (f 108%Z (d6 b) (f 90%Z (d5 b) (f 72%Z (d4 b) (f 54%Z (d3 b) (f 36%Z (d2 b) (f 18%Z (d1 b)
    (f 0%Z (d0 b) c0i))))))).

Definition ubits (x : bigint) : int :=
  let s := strip x in
  match rev_append s [] with
  | [] => c0i
  | b :: _ => Uint63.add (Uint63.mul (Uint63.sub (ilen s) c1i) c144i) (limb_bits b)
  end.

(* floor(x / 2^L) = floor(x * 2^(144-s) / 2^(144(k+1))) *)
Definition shr (L : int) (x : bigint) : bigint :=
  let k0 := div144 L in
  let k := i2n k0 in
  let s := Uint63.sub L (Uint63.mul k0 c144i) in
  if Uint63.eqb s c0i then strip (skipn k x)
  else strip (skipn (S k) (shbits 9 (Uint63.sub c144i s) x)).

Definition lowbits (L : int) (x : bigint) : bigint := usub x (shl L (shr L x)).

Definition umul (x y : bigint) : bigint := match mulx x y with Some z => z | None => [] end.

Definition one_big : bigint := bigint_of_N 1.

(* q <= floor(a/p) when a < 2^Ab and Rc <= 2^Ab/p; short by a few units *)
Definition barrett (Rc : bigint) (P Ab : int) (a : bigint) : bigint :=
  shr (Uint63.add (Uint63.sub Ab P) c1i) (umul (shr (Uint63.sub P c1i) a) Rc).

Fixpoint udivq (fuel : nat) (p Rc : bigint) (P Ab : int) (a : bigint) : bigint :=
  match fuel with
  | O => []
  | S f =>
      let Ba := ubits a in
      if Uint63.leb Ba Ab then barrett Rc P Ab a
      else
        let sh := Uint63.sub Ba Ab in
        let top := shr sh a in
        let q1 := barrett Rc P Ab top in
        let r1 := usub top (umul q1 p) in
        let a' := addb (shl sh r1) (lowbits sh a) in
        addb (shl sh q1) (udivq f p Rc P Ab a')
  end.

Fixpoint newton (fuel : nat) (p : bigint) (Ab : int) (x : bigint) : bigint :=
  match fuel with
  | O => x
  | S f =>
      let e := usub (shl Ab one_big) (umul p x) in
      newton f p Ab (addb x (shr Ab (umul x e)))
  end.

(* ===================== proofs ===================== *)

Local Open Scope Z_scope.

Notation val := bigint_value.
Notation can := canonical_bigint.

Lemma val_nil : val [] = 0.
Proof. reflexivity. Qed.

Lemma limb8_value_zl : limb8_value zl = 0.
Proof. reflexivity. Qed.

Lemma can_nil : can [].
Proof. apply Forall_nil. Qed.

Lemma can_cons b x : canonical_limb8 b -> can x -> can (b :: x).
Proof. intros. apply Forall_cons; assumption. Qed.

Lemma can_inv b x : can (b :: x) -> canonical_limb8 b /\ can x.
Proof. intro H. split; [exact (Forall_inv H)|exact (Forall_inv_tail H)]. Qed.

Lemma val_app xs ys :
  val (xs ++ ys) = val xs + digit_base8_z ^ Z.of_nat (length xs) * val ys.
Proof.
  induction xs as [|b xs IH]; cbn [app length].
  - rewrite val_nil. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring.
  - rewrite !bigint_value_cons, IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma can_app xs ys : can xs -> can ys -> can (xs ++ ys).
Proof. intros. apply Forall_app. auto. Qed.

Lemma can_rev xs : can xs -> can (rev xs).
Proof. apply Forall_rev. Qed.

Lemma val_rev_append acc ys :
  val (rev_append acc ys) = val (rev acc) + digit_base8_z ^ Z.of_nat (length acc) * val ys.
Proof. rewrite rev_append_rev, val_app, length_rev. reflexivity. Qed.

Lemma can_rev_append acc ys : can acc -> can ys -> can (rev_append acc ys).
Proof. intros. rewrite rev_append_rev. apply can_app; [apply can_rev|]; auto. Qed.

Lemma val_rev_cons b acc :
  val (rev (b :: acc)) = val (rev acc) + digit_base8_z ^ Z.of_nat (length acc) * limb8_value b.
Proof.
  cbn [rev]. rewrite val_app, length_rev, bigint_value_cons, val_nil. ring.
Qed.

Lemma pow_succ_len (acc : bigint) b :
  digit_base8_z ^ Z.of_nat (length (b :: acc)) = digit_base8_z ^ Z.of_nat (length acc) * digit_base8_z.
Proof. cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. Qed.

Lemma acc_nil v : val (rev []) + digit_base8_z ^ Z.of_nat (length (@nil limb8)) * v = v.
Proof. cbn [rev length]. rewrite val_nil. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring. Qed.

Lemma carry_limb_ok c :
  canonical_digit c -> can (carry_limb c) /\ val (carry_limb c) = Uint63.to_Z c.
Proof.
  intro Hc. unfold carry_limb.
  destruct (Uint63.eqb c zero_digit) eqn:E.
  - apply Uint63.eqb_correct in E. subst c. split; [apply can_nil|].
    rewrite zero_digit_to_Z. reflexivity.
  - split.
    + apply can_cons; [apply canonical_limb8_single_digit; exact Hc|apply can_nil].
    + rewrite bigint_value_cons, limb8_single_digit_value, val_nil. ring.
Qed.

(* ---------- addition ---------- *)

Lemma add1_ok c ys acc :
  canonical_digit c -> can ys -> can acc ->
  can (add1 c ys acc) /\
  val (add1 c ys acc) =
    val (rev acc) + digit_base8_z ^ Z.of_nat (length acc) * (val ys + Uint63.to_Z c).
Proof.
  revert c acc. induction ys as [|y ys IH]; intros c acc Hc Hys Hacc; cbn [add1].
  - destruct (carry_limb_ok c Hc) as [H1 H2]. split.
    + apply can_rev_append; auto.
    + rewrite val_rev_append, H2, val_nil. ring.
  - destruct (can_inv _ _ Hys) as [Hy Hys'].
    destruct (Uint63.eqb c zero_digit) eqn:E.
    + apply Uint63.eqb_correct in E. subst c. split.
      * apply can_rev_append; auto.
      * rewrite val_rev_append, zero_digit_to_Z. ring.
    + destruct (add_limb8_with_carry y zl c) as [b c'] eqn:Ha. cbv beta iota.
      destruct (add_limb8_with_carry_correct y zl c b c' Hy canonical_zero_limb8 Hc Ha)
        as [Hb [Hc' Hv]].
      destruct (IH c' (b :: acc) Hc' Hys' (can_cons _ _ Hb Hacc)) as [H1 H2].
      split; [exact H1|].
      rewrite H2, val_rev_cons, pow_succ_len, bigint_value_cons.
      rewrite limb8_value_zl in Hv.
      replace (limb8_value b) with (limb8_value y + Uint63.to_Z c - digit_base8_z * Uint63.to_Z c')
        by lia.
      ring.
Qed.

Lemma addc_ok c xs ys acc :
  canonical_digit c -> can xs -> can ys -> can acc ->
  can (addc c xs ys acc) /\
  val (addc c xs ys acc) =
    val (rev acc) + digit_base8_z ^ Z.of_nat (length acc) * (val xs + val ys + Uint63.to_Z c).
Proof.
  revert c ys acc. induction xs as [|x xs IH]; intros c ys acc Hc Hxs Hys Hacc; cbn [addc].
  - destruct (add1_ok c ys acc Hc Hys Hacc) as [H1 H2]. split; [exact H1|].
    rewrite H2, val_nil. ring.
  - destruct ys as [|y ys].
    + destruct (add1_ok c (x :: xs) acc Hc Hxs Hacc) as [H1 H2]. split; [exact H1|].
      rewrite H2, val_nil. ring.
    + destruct (can_inv _ _ Hxs) as [Hx Hxs']. destruct (can_inv _ _ Hys) as [Hy Hys'].
      destruct (add_limb8_with_carry x y c) as [b c'] eqn:Ha. cbv beta iota.
      destruct (add_limb8_with_carry_correct x y c b c' Hx Hy Hc Ha) as [Hb [Hc' Hv]].
      destruct (IH c' ys (b :: acc) Hc' Hxs' Hys' (can_cons _ _ Hb Hacc)) as [H1 H2].
      split; [exact H1|].
      rewrite H2, val_rev_cons, pow_succ_len, !bigint_value_cons.
      replace (limb8_value b)
        with (limb8_value x + limb8_value y + Uint63.to_Z c - digit_base8_z * Uint63.to_Z c')
        by lia.
      ring.
Qed.

Lemma addb_ok x y : can x -> can y -> can (addb x y) /\ val (addb x y) = val x + val y.
Proof.
  intros Hx Hy. unfold addb.
  destruct (addc_ok zero_digit x y [] canonical_zero_digit Hx Hy can_nil) as [H1 H2].
  split; [exact H1|]. rewrite H2, acc_nil, zero_digit_to_Z. ring.
Qed.

(* ---------- digit multiplication and shifts ---------- *)

Lemma muldc_ok m c xs acc :
  canonical_digit m -> canonical_digit c -> can xs -> can acc ->
  can (muldc m c xs acc) /\
  val (muldc m c xs acc) =
    val (rev acc) + digit_base8_z ^ Z.of_nat (length acc) * (Uint63.to_Z m * val xs + Uint63.to_Z c).
Proof.
  intro Hm. revert c acc. induction xs as [|x xs IH]; intros c acc Hc Hxs Hacc; cbn [muldc].
  - destruct (carry_limb_ok c Hc) as [H1 H2]. split.
    + apply can_rev_append; auto.
    + rewrite val_rev_append, H2, val_nil. ring.
  - destruct (can_inv _ _ Hxs) as [Hx Hxs'].
    destruct (mul_limb8_digit_with_carry m x c) as [b c'] eqn:Ha. cbv beta iota.
    destruct (mul_limb8_digit_with_carry_correct m x c b c' Hm Hx Hc Ha) as [Hb [Hc' Hv]].
    destruct (IH c' (b :: acc) Hc' Hxs' (can_cons _ _ Hb Hacc)) as [H1 H2].
    split; [exact H1|].
    rewrite H2, val_rev_cons, pow_succ_len, bigint_value_cons.
    replace (limb8_value b)
      with (Uint63.to_Z m * limb8_value x + Uint63.to_Z c - digit_base8_z * Uint63.to_Z c')
      by lia.
    ring.
Qed.

Lemma muld_ok m x :
  canonical_digit m -> can x -> can (muld m x) /\ val (muld m x) = Uint63.to_Z m * val x.
Proof.
  intros Hm Hx. unfold muld.
  destruct (muldc_ok m zero_digit x [] Hm canonical_zero_digit Hx can_nil) as [H1 H2].
  split; [exact H1|]. rewrite H2, acc_nil, zero_digit_to_Z. ring.
Qed.

Lemma to_Z_c0i : Uint63.to_Z c0i = 0. Proof. reflexivity. Qed.
Lemma to_Z_c17i : Uint63.to_Z c17i = 17. Proof. reflexivity. Qed.
Lemma to_Z_two17 : Uint63.to_Z two17 = 131072. Proof. reflexivity. Qed.
Lemma to_Z_two9 : Uint63.to_Z two9 = 512. Proof. reflexivity. Qed.
Lemma to_Z_c144i : Uint63.to_Z c144i = 144. Proof. reflexivity. Qed.
Lemma wB_eq : Uint63.wB = 9223372036854775808. Proof. reflexivity. Qed.
Lemma pow17 : 2 ^ 17 = 131072. Proof. reflexivity. Qed.

Lemma canonical_digit_small d : 0 <= Uint63.to_Z d <= 262143 -> canonical_digit d.
Proof. unfold canonical_digit, digit_base_z. lia. Qed.

Lemma pow2_le17 s : 0 <= s <= 17 -> 0 < 2 ^ s <= 131072.
Proof.
  intro Hs. rewrite <- pow17. split; [apply Z.pow_pos_nonneg; lia|apply Z.pow_le_mono_r; lia].
Qed.

Lemma lsl1_spec s :
  0 <= Uint63.to_Z s <= 17 -> Uint63.to_Z (Uint63.lsl c1i s) = 2 ^ Uint63.to_Z s.
Proof.
  intro Hs. rewrite Uint63.lsl_spec. change (Uint63.to_Z c1i) with 1. rewrite Z.mul_1_l.
  pose proof (pow2_le17 _ Hs). rewrite wB_eq. apply Z.mod_small. lia.
Qed.

Lemma shbits_ok fuel s x :
  can x -> Uint63.to_Z s <= 17 * Z.of_nat fuel ->
  can (shbits fuel s x) /\ val (shbits fuel s x) = 2 ^ Uint63.to_Z s * val x.
Proof.
  revert s x. induction fuel as [|f IH]; intros s x Hx Hs; cbn [shbits].
  - pose proof (Uint63.to_Z_bounded s) as Hb.
    assert (Hz : Uint63.to_Z s = 0) by lia.
    rewrite Hz. split; [exact Hx|]. ring.
  - pose proof (Uint63.to_Z_bounded s) as Hb.
    destruct (Uint63.eqb s c0i) eqn:E0.
    { apply Uint63.eqb_correct in E0. subst s. rewrite to_Z_c0i. split; [exact Hx|]. ring. }
    assert (Hs0 : Uint63.to_Z s <> 0).
    { intro Hz. apply Uint63.eqb_false_spec in E0. apply E0. apply Uint63.to_Z_inj.
      rewrite Hz. reflexivity. }
    destruct (Uint63.leb s c17i) eqn:E1.
    + apply Uint63.leb_spec in E1. rewrite to_Z_c17i in E1.
      assert (Hl : 0 <= Uint63.to_Z s <= 17) by lia.
      pose proof (lsl1_spec s Hl) as Hsh. pose proof (pow2_le17 _ Hl) as Hp.
      assert (Hd : canonical_digit (Uint63.lsl c1i s)) by (apply canonical_digit_small; lia).
      destruct (muld_ok _ x Hd Hx) as [H1 H2].
      split; [exact H1|]. rewrite H2, Hsh. reflexivity.
    + assert (E1' : Uint63.to_Z s > 17).
      { destruct (Uint63.leb_spec s c17i) as [_ Hi]. rewrite to_Z_c17i in Hi.
        destruct (Z_le_gt_dec (Uint63.to_Z s) 17) as [l|g]; [|exact g].
        specialize (Hi l). congruence. }
      assert (Hsub : Uint63.to_Z (Uint63.sub s c17i) = Uint63.to_Z s - 17).
      { rewrite Uint63.sub_spec, to_Z_c17i, Z.mod_small; lia. }
      assert (Hd : canonical_digit two17) by (apply canonical_digit_small; rewrite to_Z_two17; lia).
      destruct (muld_ok two17 x Hd Hx) as [H1 H2].
      destruct (IH (Uint63.sub s c17i) _ H1 ltac:(rewrite Hsub; lia)) as [H3 H4].
      split; [exact H3|]. rewrite H4, H2, Hsub, to_Z_two17, <- pow17.
      rewrite Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. ring.
Qed.

Lemma prepend_zeros_ok k x :
  can x -> can (prepend_zeros k x) /\ val (prepend_zeros k x) = digit_base8_z ^ Z.of_nat k * val x.
Proof.
  revert x. induction k as [|k IH]; intros x Hx; cbn [prepend_zeros].
  - split; [exact Hx|]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring.
  - destruct (IH (zl :: x) (can_cons _ _ canonical_zero_limb8 Hx)) as [H1 H2].
    split; [exact H1|]. rewrite H2, bigint_value_cons, limb8_value_zl.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma B8_eq : digit_base8_z = 2 ^ 144.
Proof. reflexivity. Qed.

Lemma split144 L k :
  Uint63.ltb (Uint63.sub L (Uint63.mul k c144i)) c144i = true -> Uint63.ltb k two50 = true ->
  Uint63.to_Z L = 144 * Uint63.to_Z k + Uint63.to_Z (Uint63.sub L (Uint63.mul k c144i)).
Proof.
  intros Hs Hk. apply Uint63.ltb_spec in Hs, Hk. rewrite to_Z_c144i in Hs.
  change (Uint63.to_Z two50) with 1125899906842624 in Hk.
  pose proof (Uint63.to_Z_bounded L) as HL. pose proof (Uint63.to_Z_bounded k) as HK.
  rewrite wB_eq in HL, HK.
  assert (E : Uint63.to_Z (Uint63.sub L (Uint63.mul k c144i)) =
              (Uint63.to_Z L - Uint63.to_Z k * 144) mod 9223372036854775808).
  { rewrite Uint63.sub_spec, Uint63.mul_spec, to_Z_c144i, wB_eq.
    rewrite (Z.mod_small (Uint63.to_Z k * 144)) by lia. reflexivity. }
  rewrite E in Hs |- *.
  destruct (Z_lt_le_dec (Uint63.to_Z L - Uint63.to_Z k * 144) 0) as [Hn|Hp].
  - exfalso. rewrite <- (Z_mod_plus_full _ 1) in Hs. rewrite Z.mod_small in Hs by lia. lia.
  - rewrite Z.mod_small by lia. ring.
Qed.

Lemma shl_ok L x :
  can x -> can (shl L x) /\ val (shl L x) = 2 ^ Uint63.to_Z L * val x.
Proof.
  intro Hx. unfold shl. destruct x as [|b x'].
  { split; [apply can_nil|]. rewrite val_nil. ring. }
  cbv zeta.
  destruct (Uint63.ltb (Uint63.sub L (Uint63.mul (div144 L) c144i)) c144i &&
            Uint63.ltb (div144 L) two50) eqn:C.
  - apply andb_true_iff in C. destruct C as [Cs Ck].
    pose proof (split144 L (div144 L) Cs Ck) as EL.
    set (k := div144 L) in *. set (s := Uint63.sub L (Uint63.mul k c144i)) in *.
    apply Uint63.ltb_spec in Cs. rewrite to_Z_c144i in Cs.
    pose proof (Uint63.to_Z_bounded s) as Hsb. pose proof (Uint63.to_Z_bounded k) as Hkb.
    destruct (shbits_ok 9 s (b :: x') Hx ltac:(change (17 * Z.of_nat 9) with 153; lia)) as [H1 H2].
    destruct (prepend_zeros_ok (i2n k) _ H1) as [H3 H4].
    split; [exact H3|]. rewrite H4, H2. unfold i2n. rewrite Z2Nat.id by lia.
    rewrite B8_eq, <- Z.pow_mul_r by lia.
    rewrite Z.mul_assoc, <- Z.pow_add_r by lia.
    rewrite EL. reflexivity.
  - apply shbits_ok; [exact Hx|]. unfold i2n.
    pose proof (Uint63.to_Z_bounded L).
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.

(* ---------- strip, equality, canonicity check ---------- *)

Lemma drop_zero_prefix_val l : val (rev (drop_zero_prefix l)) = val (rev l).
Proof.
  induction l as [|z l IH]; [reflexivity|]. cbn [drop_zero_prefix].
  destruct (limb8_eqb z zero_limb8) eqn:E; [|reflexivity].
  apply limb8_eqb_eq in E. subst z. rewrite IH. cbn [rev].
  rewrite val_app, bigint_value_cons, val_nil.
  change (limb8_value zero_limb8) with (limb8_value zl). rewrite limb8_value_zl. ring.
Qed.

Lemma strip_eq x : strip x = rev (drop_zero_prefix (rev x)).
Proof. unfold strip. rewrite !rev_append_rev, !app_nil_r. reflexivity. Qed.

Lemma strip_ok x : can x -> can (strip x) /\ val (strip x) = val x.
Proof.
  intro Hx. rewrite strip_eq. split.
  - apply can_rev, drop_zero_prefix_canonical, can_rev, Hx.
  - rewrite drop_zero_prefix_val, rev_involutive. reflexivity.
Qed.

Lemma strip_val x : val (strip x) = val x.
Proof. rewrite strip_eq, drop_zero_prefix_val, rev_involutive. reflexivity. Qed.

Lemma limbs_eqb_eq x y : limbs_eqb x y = true -> x = y.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y] H; cbn [limbs_eqb] in H; try discriminate; [reflexivity|].
  destruct (limb8_eqb a b) eqn:E; [|discriminate].
  apply limb8_eqb_eq in E. subst b. f_equal. apply IH, H.
Qed.

Lemma eqv_val x y : eqv x y = true -> val x = val y.
Proof.
  unfold eqv. intro H. apply limbs_eqb_eq in H.
  rewrite <- (strip_val x), <- (strip_val y), H. reflexivity.
Qed.

Lemma digit_ok_spec d : digit_ok d = true -> canonical_digit d.
Proof.
  unfold digit_ok. intro H. apply Uint63.ltb_spec in H. change (Uint63.to_Z dbase) with 262144 in H.
  pose proof (Uint63.to_Z_bounded d). apply canonical_digit_small. lia.
Qed.

Lemma limb_ok_spec b : limb_ok b = true -> canonical_limb8 b.
Proof.
  unfold limb_ok. intro H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7].
  repeat split; apply digit_ok_spec; assumption.
Qed.

Lemma canonb_spec x : canonb x = true -> can x.
Proof.
  induction x as [|b x IH]; cbn [canonb]; intro H; [apply can_nil|].
  destruct (limb_ok b) eqn:E; [|discriminate].
  apply can_cons; [apply limb_ok_spec, E | apply IH, H].
Qed.

(* ---------- schoolbook product ---------- *)

Definition hstep (a : Z) (d : int) : Z := a * 262144 + Uint63.to_Z d.

Lemma pow18_succ n : 2 ^ (18 * Z.of_nat (S n)) = 262144 * 2 ^ (18 * Z.of_nat n).
Proof.
  rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 18) with 262144. ring.
Qed.

Lemma fold_hstep ds a :
  fold_left hstep ds a = a * 2 ^ (18 * Z.of_nat (length ds)) + fold_left hstep ds 0.
Proof.
  revert a. induction ds as [|d ds IH]; intro a; cbn [fold_left length].
  - change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.pow_0_r. ring.
  - rewrite (IH (hstep a d)), (IH (hstep 0 d)), pow18_succ. unfold hstep. ring.
Qed.

Lemma shift18_ok z : can z -> can (shift18 z) /\ val (shift18 z) = 262144 * val z.
Proof.
  intro Hz. unfold shift18.
  assert (Hd : canonical_digit two9) by (apply canonical_digit_small; rewrite to_Z_two9; lia).
  destruct (muld_ok two9 z Hd Hz) as [H1 H2].
  destruct (muld_ok two9 _ Hd H1) as [H3 H4].
  split; [exact H3|]. rewrite H4, H2, to_Z_two9. ring.
Qed.

Lemma horner_ok x ds acc :
  can x -> can acc -> Forall canonical_digit ds ->
  can (horner x ds acc) /\
  val (horner x ds acc) = val acc * 2 ^ (18 * Z.of_nat (length ds)) + val x * fold_left hstep ds 0.
Proof.
  revert acc. induction ds as [|d ds IH]; intros acc Hx Hacc Hds; cbn [horner].
  - split; [exact Hacc|]. cbn [length fold_left]. change (Z.of_nat 0) with 0.
    rewrite Z.mul_0_r, Z.pow_0_r. ring.
  - pose proof (Forall_inv Hds) as Hd. pose proof (Forall_inv_tail Hds) as Hds'.
    destruct (shift18_ok acc Hacc) as [H1 H2].
    destruct (muld_ok d x Hd Hx) as [H3 H4].
    destruct (addb_ok _ _ H1 H3) as [H5 H6].
    destruct (IH _ Hx H5 Hds') as [H7 H8].
    split; [exact H7|]. rewrite H8, H6, H2, H4.
    cbn [fold_left length]. rewrite (fold_hstep ds (hstep 0 d)), pow18_succ. unfold hstep. ring.
Qed.

Lemma fold_hstep_rev l :
  fold_left hstep (rev l) 0 = digits_value (map Uint63.to_Z l).
Proof.
  induction l as [|d l IH]; [reflexivity|].
  cbn [rev map digits_value]. rewrite fold_left_app, IH. cbn [fold_left]. unfold hstep, digit_base_z. ring.
Qed.

Lemma smul_ok x y : can x -> can y -> can (smul x y) /\ val (smul x y) = val x * val y.
Proof.
  intros Hx Hy. unfold smul.
  rewrite bigint_digits_u63_rev_eq_flat, rev_append_rev, app_nil_r.
  assert (Hd : Forall canonical_digit (rev (bigint_digits_u63_flat y))).
  { apply Forall_rev. rewrite <- bigint_digits_u63_eq_flat. apply canonical_bigint_digits_u63, Hy. }
  destruct (horner_ok x _ [] Hx can_nil Hd) as [H1 H2].
  split; [exact H1|]. rewrite H2, val_nil, fold_hstep_rev.
  replace (val y) with (digits_value (map Uint63.to_Z (bigint_digits_u63_flat y))).
  - ring.
  - unfold bigint_value. rewrite bigint_digits_z_eq_flat. reflexivity.
Qed.

(* ---------- general product ---------- *)

Lemma takec_eq k x acc : takec k x acc = rev_append acc (firstn k x).
Proof.
  revert x acc. induction k as [|k IH]; intros [|y x] acc; try reflexivity.
  cbn [takec firstn]. rewrite IH. reflexivity.
Qed.

Lemma can_firstn k x : can x -> can (firstn k x).
Proof.
  revert x. induction k as [|k IH]; intros [|b x] H; cbn [firstn]; try apply can_nil.
  destruct (can_inv _ _ H). apply can_cons; auto.
Qed.

Lemma can_skipn k x : can x -> can (skipn k x).
Proof.
  revert x. induction k as [|k IH]; intros [|b x] H; cbn [skipn]; try exact H; try apply can_nil.
  apply IH. exact (proj2 (can_inv _ _ H)).
Qed.

Lemma mulx_fuel_ok fuel x y z :
  can x -> can y -> mulx_fuel fuel x y = Some z -> can z /\ val z = val x * val y.
Proof.
  revert x y z. induction fuel as [|f IH]; intros x y z Hx Hy H; cbn [mulx_fuel] in H; [discriminate|]. cbv zeta in H.
  destruct (Uint63.leb (ilen y) small_limbs).
  { injection H as <-. apply smul_ok; assumption. }
  destruct (Uint63.leb (ilen x) small_limbs).
  { injection H as <-. destruct (smul_ok y x Hy Hx) as [H1 H2]. split; [exact H1|]. rewrite H2. ring. }
  destruct (Uint63.leb (Uint63.add (ilen x) (ilen y)) cap_limbs).
  { split; [exact (mul_bigint_some_canonical x y z Hx Hy H)|exact (mul_bigint_correct x y z Hx Hy H)]. }
  destruct (Uint63.ltb (ilen x) (ilen y)).
  { destruct (IH y x z Hy Hx H) as [H1 H2]. split; [exact H1|]. rewrite H2. ring. }
  revert H. generalize (i2n (Uint63.lsr (ilen x) c1i)). intros k H.
  assert (Hlo : can (takec k x [])) by (rewrite takec_eq; apply can_firstn, Hx).
  assert (Hhi : can (skipn k x)) by (apply can_skipn, Hx).
  destruct (mulx_fuel f (skipn k x) y) as [z1|] eqn:E1; [|discriminate].
  destruct (mulx_fuel f (takec k x []) y) as [z0|] eqn:E0; [|discriminate].
  injection H as <-.
  destruct (IH _ _ _ Hhi Hy E1) as [Hz1 V1].
  destruct (IH _ _ _ Hlo Hy E0) as [Hz0 V0].
  destruct (prepend_zeros_ok k z1 Hz1) as [Hp Vp].
  destruct (addb_ok _ _ Hp Hz0) as [Ha Va].
  split; [exact Ha|]. rewrite Va, Vp, V1, V0, takec_eq. cbn [rev_append].
  rewrite (bigint_value_firstn_skipn k x).
  destruct (Nat.le_gt_cases k (length x)) as [Hk|Hk].
  - rewrite length_firstn, Nat.min_l by exact Hk. ring.
  - rewrite skipn_all2 by lia. rewrite val_nil. ring.
Qed.

Lemma mulx_ok x y z : can x -> can y -> mulx x y = Some z -> can z /\ val z = val x * val y.
Proof. apply mulx_fuel_ok. Qed.

(* ---------- machine integers ---------- *)

Lemma val_limb x0 x1 x2 x3 x4 x5 x6 x7 :
  limb8_value (Limb8 x0 x1 x2 x3 x4 x5 x6 x7) =
    Uint63.to_Z x0 + 262144 * (Uint63.to_Z x1 + 262144 * (Uint63.to_Z x2 +
    262144 * (Uint63.to_Z x3 + 262144 * (Uint63.to_Z x4 + 262144 * (Uint63.to_Z x5 +
    262144 * (Uint63.to_Z x6 + 262144 * (Uint63.to_Z x7 + 262144 * 0))))))).
Proof. reflexivity. Qed.

Lemma of_u63_ok x : can (of_u63 x) /\ val (of_u63 x) = Uint63.to_Z x.
Proof.
  pose proof (Uint63.to_Z_bounded x) as Hx. rewrite wB_eq in Hx.
  assert (E1 : Uint63.to_Z (PrimInt63.mod x two18) = Uint63.to_Z x mod 262144)
    by (rewrite Uint63.mod_spec; reflexivity).
  assert (E2 : Uint63.to_Z (PrimInt63.mod (Uint63.lsr x c18i) two18) =
               (Uint63.to_Z x / 262144) mod 262144)
    by (rewrite Uint63.mod_spec, Uint63.lsr_spec; reflexivity).
  assert (E3 : Uint63.to_Z (PrimInt63.mod (Uint63.lsr x c36i) two18) =
               (Uint63.to_Z x / 68719476736) mod 262144)
    by (rewrite Uint63.mod_spec, Uint63.lsr_spec; reflexivity).
  assert (E4 : Uint63.to_Z (Uint63.lsr x c54i) = Uint63.to_Z x / 18014398509481984)
    by (rewrite Uint63.lsr_spec; reflexivity).
  set (X := Uint63.to_Z x) in *.
  assert (B1 := Z.mod_pos_bound X 262144 ltac:(lia)).
  assert (B2 := Z.mod_pos_bound (X / 262144) 262144 ltac:(lia)).
  assert (B3 := Z.mod_pos_bound (X / 68719476736) 262144 ltac:(lia)).
  assert (B4 : 0 <= X / 18014398509481984 < 262144).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  pose proof (Z.div_mod X 262144 ltac:(lia)) as D1.
  pose proof (Z.div_mod (X / 262144) 262144 ltac:(lia)) as D2.
  pose proof (Z.div_mod (X / 68719476736) 262144 ltac:(lia)) as D3.
  rewrite Z.div_div in D2 by lia. rewrite Z.div_div in D3 by lia.
  change (262144 * 262144) with 68719476736 in D2.
  change (68719476736 * 262144) with 18014398509481984 in D3.
  unfold of_u63. split.
  - apply can_cons; [|apply can_nil].
    unfold canonical_limb8, canonical_digit, digit_base_z; cbn [d0 d1 d2 d3 d4 d5 d6 d7].
    rewrite E1, E2, E3, E4, to_Z_c0i. lia.
  - rewrite bigint_value_cons, val_nil, val_limb, E1, E2, E3, E4, to_Z_c0i. lia.
Qed.

Lemma to_u63_ok a x : can a -> to_u63 a = Some x -> val a = Uint63.to_Z x.
Proof.
  intros Ha H. unfold to_u63 in H. rewrite <- (strip_val a).
  destruct (strip_ok a Ha) as [Hs _].
  destruct (strip a) as [|b [|b' l]].
  - injection H as <-. reflexivity.
  - destruct (can_inv _ _ Hs) as [Hb _].
    destruct b as [y0 y1 y2 y3 y4 y5 y6 y7]. cbn [d0 d1 d2 d3 d4 d5 d6 d7] in H.
    destruct Hb as [B0 [B1 [B2 [B3 _]]]]. cbn [d0 d1 d2 d3] in B0, B1, B2, B3.
    unfold canonical_digit, digit_base_z in B0, B1, B2, B3.
    destruct (Uint63.ltb y3 two9 && Uint63.eqb y4 c0i && Uint63.eqb y5 c0i &&
              Uint63.eqb y6 c0i && Uint63.eqb y7 c0i) eqn:C; [|discriminate].
    injection H as <-.
    repeat rewrite andb_true_iff in C. destruct C as [[[[C3 C4] C5] C6] C7].
    apply Uint63.eqb_correct in C4, C5, C6, C7. subst y4 y5 y6 y7.
    apply Uint63.ltb_spec in C3. rewrite to_Z_two9 in C3.
    rewrite bigint_value_cons, val_nil, val_limb, to_Z_c0i.
    rewrite !Uint63.add_spec, !Uint63.mul_spec, wB_eq.
    change (Uint63.to_Z two18) with 262144. change (Uint63.to_Z two36) with 68719476736.
    change (Uint63.to_Z two54) with 18014398509481984.
    set (z0 := Uint63.to_Z y0) in *. set (z1 := Uint63.to_Z y1) in *.
    set (z2 := Uint63.to_Z y2) in *. set (z3 := Uint63.to_Z y3) in *.
    rewrite (Z.mod_small (z1 * 262144)) by lia.
    rewrite (Z.mod_small (z2 * 68719476736)) by lia.
    rewrite (Z.mod_small (z3 * 18014398509481984)) by lia.
    rewrite (Z.mod_small (z0 + z1 * 262144)) by lia.
    rewrite (Z.mod_small (z2 * 68719476736 + z3 * 18014398509481984)) by lia.
    rewrite Z.mod_small by lia.
    ring.
  - discriminate.
Qed.

(* ---------- x mod 3 ---------- *)

Lemma m3step_ok acc d :
  0 <= Uint63.to_Z acc < 3 -> canonical_digit d ->
  0 <= Uint63.to_Z (m3step acc d) < 3 /\
  Uint63.to_Z (m3step acc d) = (Uint63.to_Z acc + Uint63.to_Z d) mod 3.
Proof.
  intros Ha Hd. unfold canonical_digit, digit_base_z in Hd. unfold m3step.
  rewrite Uint63.mod_spec, Uint63.add_spec, wB_eq. change (Uint63.to_Z c3i) with 3.
  rewrite (Z.mod_small (_ + _)) by lia.
  split; [apply Z.mod_pos_bound; lia|reflexivity].
Qed.

Lemma limb_m3_ok acc b :
  0 <= Uint63.to_Z acc < 3 -> canonical_limb8 b ->
  0 <= Uint63.to_Z (limb_m3 acc b) < 3 /\
  Uint63.to_Z (limb_m3 acc b) = (Uint63.to_Z acc + limb8_value b) mod 3.
Proof.
  intros Ha Hb. destruct b as [y0 y1 y2 y3 y4 y5 y6 y7].
  destruct Hb as [B0 [B1 [B2 [B3 [B4 [B5 [B6 B7]]]]]]]. cbn [d0 d1 d2 d3 d4 d5 d6 d7] in *.
  unfold limb_m3. cbn [d0 d1 d2 d3 d4 d5 d6 d7].
  destruct (m3step_ok _ _ Ha B0) as [R0 V0].
  destruct (m3step_ok _ _ R0 B1) as [R1 V1].
  destruct (m3step_ok _ _ R1 B2) as [R2 V2].
  destruct (m3step_ok _ _ R2 B3) as [R3 V3].
  destruct (m3step_ok _ _ R3 B4) as [R4 V4].
  destruct (m3step_ok _ _ R4 B5) as [R5 V5].
  destruct (m3step_ok _ _ R5 B6) as [R6 V6].
  destruct (m3step_ok _ _ R6 B7) as [R7 V7].
  split; [exact R7|].
  rewrite V7, V6, V5, V4, V3, V2, V1, V0.
  repeat rewrite Zplus_mod_idemp_l.
  rewrite val_limb.
  set (z0 := Uint63.to_Z y0). set (z1 := Uint63.to_Z y1). set (z2 := Uint63.to_Z y2).
  set (z3 := Uint63.to_Z y3). set (z4 := Uint63.to_Z y4). set (z5 := Uint63.to_Z y5).
  set (z6 := Uint63.to_Z y6). set (z7 := Uint63.to_Z y7). set (A := Uint63.to_Z acc).
  match goal with |- _ = ?r mod 3 =>
    replace r with (A + z0 + z1 + z2 + z3 + z4 + z5 + z6 + z7 +
      (87381 * z1 + 22906492245 * z2 + 6004799503160661 * z3 +
       1574122160956548404565 * z4 + 412646679761793424966374741 * z5 +
       108172851219475575594385340192085 * z6 +
       28356863910078205288614550619314017621 * z7) * 3) by ring
  end.
  rewrite Z_mod_plus_full. Z.div_mod_to_equations. lia.
Qed.

Lemma mod3_aux_ok x acc :
  can x -> 0 <= Uint63.to_Z acc < 3 ->
  Uint63.to_Z (mod3_aux x acc) = (Uint63.to_Z acc + val x) mod 3.
Proof.
  revert acc. induction x as [|b x IH]; intros acc Hx Hacc; cbn [mod3_aux].
  - rewrite val_nil, Z.add_0_r, Z.mod_small by lia. reflexivity.
  - destruct (can_inv _ _ Hx) as [Hb Hx'].
    destruct (limb_m3_ok acc b Hacc Hb) as [R V].
    rewrite (IH _ Hx' R), V, Zplus_mod_idemp_l, bigint_value_cons.
    change digit_base8_z with 22300745198530623141535718272648361505980416.
    set (v := val x). set (A := Uint63.to_Z acc). set (l := limb8_value b).
    replace (A + (l + 22300745198530623141535718272648361505980416 * v))
      with (A + l + v + (7433581732843541047178572757549453835326805 * v) * 3) by ring.
    rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma mod3_ok x : can x -> Uint63.to_Z (mod3 x) = val x mod 3.
Proof.
  intro Hx. unfold mod3. rewrite (mod3_aux_ok x c0i Hx ltac:(rewrite to_Z_c0i; lia)), to_Z_c0i.
  reflexivity.
Qed.
End BigArith.

From BusyCoq Require Import Individual62.
From Coq Require Import Lia List String.

Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC1RF_0RD0LB_0RA1LE_1LD---_0RB0RC").

Module TM1.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P j k (X : side) :=
  0inf <{{D}} [1;1;0] *> [1;0]^^j *> [1]^^k *> X.

Definition B : list Sym := [0;1;0;1;1].

Lemma E_00101011111_3_1 q m :
  P (q*2+1) 1 ([0;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0010101_3_0 q m :
  P (q*2+1) 0 ([0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+2) ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0010101_3_1 q m :
  P (q*2+1) 1 ([0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0010101_3_2 q m :
  P (q*2+1) 2 ([0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_001011111111_3_2 q m :
  P (q*2+1) 2 ([0;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_00101111_3_0 q m :
  P (q*2+1) 0 ([0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+2) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_00101111_3_1 q m :
  P (q*2+1) 1 ([0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_00101111_3_2 q m :
  P (q*2+1) 2 ([0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0010_3_0 q m :
  P (q*2+1) 0 ([0;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+2) ([0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0010_3_1 q m :
  P (q*2+1) 1 ([0;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0010_3_2 q m :
  P (q*2+1) 2 ([0;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0011_3_0 q m :
  P (q*2+1) 0 ([0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+2) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0011_3_1 q m :
  P (q*2+1) 1 ([0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0011_3_2 q m :
  P (q*2+1) 2 ([0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_001_3_0 q m :
  P (q*2+1) 0 ([0;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+2) ([0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_001_3_1 q m :
  P (q*2+1) 1 ([0;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_001_3_2 q m :
  P (q*2+1) 2 ([0;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_00_3_0 q m :
  P (q*2+1) 0 ([0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+2) ([0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_00_3_1 q m :
  P (q*2+1) 1 ([0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_00_3_2 q m :
  halts tm (P (q*2+1) 2 ([0;0] *> B^^(3+m) *> 0inf)).
Proof. unfold P, B. esx. Qed.

Lemma E_0100101011111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010010101_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010010101_3_1 q m :
  P (q*2+1) 1 ([0;1;0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010010101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01001011111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01001011111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01001011111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0100101111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0100101111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0100101111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010010_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010010_3_1 q m :
  P (q*2+1) 1 ([0;1;0;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010010_3_2 q m :
  P (q*2+1) 2 ([0;1;0;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01001_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01001_3_1 q m :
  P (q*2+1) 1 ([0;1;0;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01001_3_2 q m :
  P (q*2+1) 2 ([0;1;0;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0100_3_0 q m :
  P (q*2+1) 0 ([0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0100_3_2 q m :
  P (q*2+1) 2 ([0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101001111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010100_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010100_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010100_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101001111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101001111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101001111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+12) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010100_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010100_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010100_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101010_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101010_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+15) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101010_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+17) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+13) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101010_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+19) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101011111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101011111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+15) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+11) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101010_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+18) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+21) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+18) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+22) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+17) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101011111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+18) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+13) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+9) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01010_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101011111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101011111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101011111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011010101_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011010101_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011010101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101101011111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101101011111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101101011111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011010111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010110101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011010_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011010_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011010_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101101_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101101_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+12) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111010_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111010_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+15) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111010_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+12) ([0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+18) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111011_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111011_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+20) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111011_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+23) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+24) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+19) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+20) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+15) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+12) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01011111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+11) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010111_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101_3_0 q m :
  P (q*2+1) 0 ([0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101_3_1 q m :
  P (q*2+1) 1 ([0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+12) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0101_3_2 q m :
  P (q*2+1) 2 ([0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010_3_0 q m :
  P (q*2+1) 0 ([0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010_3_1 q m :
  P (q*2+1) 1 ([0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_010_3_2 q m :
  P (q*2+1) 2 ([0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0110101011111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0110101011111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011010101_3_0 q m :
  P (q*2+1) 0 ([0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011010101_3_1 q m :
  P (q*2+1) 1 ([0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011010101_3_2 q m :
  P (q*2+1) 2 ([0;1;1;0;1;0;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01101011111111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01101011111111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01101011111111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;0;1;0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;0;1;0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0110101111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0110101111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0110101111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;0;1;0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011010_3_0 q m :
  P (q*2+1) 0 ([0;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011010_3_1 q m :
  P (q*2+1) 1 ([0;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011010_3_2 q m :
  P (q*2+1) 2 ([0;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011011_3_0 q m :
  P (q*2+1) 0 ([0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011011_3_1 q m :
  P (q*2+1) 1 ([0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011011_3_2 q m :
  P (q*2+1) 2 ([0;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01101_3_0 q m :
  P (q*2+1) 0 ([0;1;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01101_3_1 q m :
  P (q*2+1) 1 ([0;1;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01101_3_2 q m :
  P (q*2+1) 2 ([0;1;1;0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111011_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111011_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111011_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111010_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111010_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+13) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111010_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;0;1;0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111011_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111011_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+12) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111011_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111011_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111011_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111011_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111011_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111011_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111011_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111111011_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+9) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111111011_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+16) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111111011_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111011_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+11) ([0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111011_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+18) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111011_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;0;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+21) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111111111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+22) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111111111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+11) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+17) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+13) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+7) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+14) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111_3_0 q m :
  P (q*2+1) 0 ([0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111_3_1 q m :
  P (q*2+1) 1 ([0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+9) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0111_3_2 q m :
  P (q*2+1) 2 ([0;1;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011_0_1 q :
  P (q*2+1) 1 ([0;1;1] *> B^^0 *> 0inf) -->*
  P 1 (q*4+6) ([] *> B^^1 *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011_1_1 q :
  P (q*2+1) 1 ([0;1;1] *> B^^1 *> 0inf) -->*
  P 1 (q*4+6) ([] *> B^^2 *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011_3_0 q m :
  P (q*2+1) 0 ([0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011_3_1 q m :
  P (q*2+1) 1 ([0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+6) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_011_3_2 q m :
  P (q*2+1) 2 ([0;1;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01_3_0 q m :
  P (q*2+1) 0 ([0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01_3_1 q m :
  P (q*2+1) 1 ([0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+10) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_01_3_2 q m :
  P (q*2+1) 2 ([0;1] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;1;1;1] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0_3_0 q m :
  P (q*2+1) 0 ([0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+2) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0_3_1 q m :
  P (q*2+1) 1 ([0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+5) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_0_3_2 q m :
  P (q*2+1) 2 ([0] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([0;1;0;1;0;1;0;0;1;1] *> B^^(1+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_1_0 q :
  P (q*2+1) 0 ([] *> B^^1 *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1] *> B^^0 *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_1_1 q :
  P (q*2+1) 1 ([] *> B^^1 *> 0inf) -->*
  P 1 (q*4+8) ([] *> B^^1 *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_1_2 q :
  P (q*2+1) 2 ([] *> B^^1 *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^2 *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_2_0 q :
  P (q*2+1) 0 ([] *> B^^2 *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1] *> B^^1 *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_2_2 q :
  P (q*2+1) 2 ([] *> B^^2 *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^3 *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_3_0 q m :
  P (q*2+1) 0 ([] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+3) ([0;1;1] *> B^^(2+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_3_1 q m :
  P (q*2+1) 1 ([] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+8) ([] *> B^^(3+m) *> 0inf).
Proof. unfold P, B. es. Qed.

Lemma E_e_3_2 q m :
  P (q*2+1) 2 ([] *> B^^(3+m) *> 0inf) -->*
  P 1 (q*4+4) ([] *> B^^(4+m) *> 0inf).
Proof. unfold P, B. es. Qed.
End TM1.

From Coq Require Import Lia List Arith PeanoNat Bool.
(* Spec layer: Bell configurations, the Bell table as proved lemmas, shift-invariant jumps.
   Independent of any big-integer code. *)
Import ListNotations.
Import TM1.

Module Spec.

Local Open Scope nat_scope.

Definition words : list (list Sym) := [
  [];
  [0%sym];
  [0%sym;0%sym];
  [0%sym;1%sym];
  [0%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym];
  [0%sym;1%sym;1%sym];
  [0%sym;0%sym;1%sym;0%sym];
  [0%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;0%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;0%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym];
  [0%sym;1%sym;0%sym;1%sym;1%sym;0%sym;1%sym;0%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym;1%sym]].

Definition word (w : nat) : list Sym := nth w words [].

Definition w_empty : nat := 0.
Definition w_halt : nat := 2.

Definition entries : list (nat * nat * nat * nat * nat * nat) := [
  (0,1,0,6,1,3);
  (0,1,1,0,2,8);
  (0,1,2,0,3,4);
  (0,2,0,6,1,3);
  (0,2,2,0,3,4);
  (0,3,0,6,1,3);
  (0,3,1,0,2,8);
  (0,3,2,0,3,4);
  (1,3,0,0,2,2);
  (1,3,1,6,1,5);
  (1,3,2,52,0,4);
  (2,3,0,1,2,2);
  (2,3,1,0,2,4);
  (3,3,0,0,2,3);
  (3,3,1,0,2,10);
  (3,3,2,27,2,4);
  (4,3,0,3,2,2);
  (4,3,1,0,2,5);
  (4,3,2,32,2,4);
  (5,3,0,1,2,3);
  (5,3,1,6,1,7);
  (5,3,2,3,2,4);
  (6,0,1,0,3,6);
  (6,1,1,0,3,6);
  (6,3,0,0,2,4);
  (6,3,1,0,3,6);
  (6,3,2,5,3,4);
  (7,3,0,5,2,2);
  (7,3,1,1,2,5);
  (7,3,2,99,2,4);
  (8,3,0,6,2,2);
  (8,3,1,0,2,6);
  (8,3,2,99,2,4);
  (9,3,0,2,2,3);
  (9,3,2,5,2,4);
  (10,3,0,3,2,3);
  (10,3,1,0,2,12);
  (10,3,2,46,2,4);
  (11,3,0,0,2,5);
  (11,3,1,6,1,9);
  (11,3,2,5,2,4);
  (12,3,0,4,2,3);
  (12,3,1,0,2,7);
  (12,3,2,10,2,4);
  (13,3,0,5,2,3);
  (13,3,1,6,1,9);
  (13,3,2,45,1,4);
  (14,3,0,3,2,4);
  (14,3,1,27,2,6);
  (14,3,2,50,2,4);
  (15,3,0,0,2,6);
  (15,3,1,0,2,14);
  (15,3,2,10,2,4);
  (16,3,0,7,2,3);
  (16,3,1,1,2,7);
  (16,3,2,13,2,4);
  (17,3,0,8,2,3);
  (17,3,1,0,2,8);
  (17,3,2,0,3,4);
  (18,3,0,9,2,3);
  (18,3,1,0,2,8);
  (18,3,2,0,3,4);
  (19,3,0,10,2,3);
  (19,3,1,0,2,14);
  (19,3,2,70,2,4);
  (20,3,0,11,2,3);
  (20,3,1,6,1,11);
  (20,3,2,13,2,4);
  (21,3,0,5,2,4);
  (21,3,1,3,2,6);
  (21,3,2,12,2,4);
  (22,3,0,6,2,4);
  (22,3,1,5,3,6);
  (22,3,2,16,3,4);
  (23,3,0,0,2,7);
  (23,3,1,0,3,10);
  (23,3,2,0,3,4);
  (24,3,0,19,2,2);
  (24,3,1,10,2,5);
  (24,3,2,74,2,4);
  (25,3,0,13,2,3);
  (25,3,1,6,1,11);
  (25,3,2,69,1,4);
  (26,3,0,14,2,3);
  (26,3,1,27,2,8);
  (26,3,2,80,2,4);
  (27,3,0,15,2,3);
  (27,3,1,0,2,16);
  (27,3,2,19,2,4);
  (28,3,0,6,2,5);
  (28,3,1,0,2,10);
  (28,3,2,17,2,4);
  (29,3,0,0,2,8);
  (29,3,1,6,1,13);
  (29,3,2,20,2,4);
  (30,3,0,27,2,2);
  (30,3,1,15,2,5);
  (30,3,2,33,3,4);
  (31,3,0,17,2,3);
  (31,3,1,0,2,10);
  (31,3,2,27,2,4);
  (32,3,0,18,2,3);
  (32,3,1,0,2,10);
  (32,3,2,27,2,4);
  (33,3,0,19,2,3);
  (33,3,1,0,2,16);
  (33,3,2,88,2,4);
  (34,3,0,20,2,3);
  (34,3,1,6,1,13);
  (34,3,2,25,2,4);
  (35,3,0,21,2,3);
  (35,3,1,3,2,8);
  (35,3,2,26,2,4);
  (36,3,0,22,2,3);
  (36,3,1,5,3,8);
  (36,3,2,35,3,4);
  (37,3,0,23,2,3);
  (37,3,1,0,3,12);
  (37,3,2,3,3,4);
  (38,3,0,5,2,6);
  (38,3,1,6,1,13);
  (38,3,2,25,2,4);
  (39,3,0,6,2,6);
  (39,3,1,0,3,12);
  (39,3,2,3,3,4);
  (40,3,2,27,2,4);
  (41,3,0,24,2,3);
  (41,3,1,10,2,7);
  (41,3,2,33,2,4);
  (42,3,0,25,2,3);
  (42,3,1,6,1,13);
  (42,3,2,87,1,4);
  (43,3,0,27,2,3);
  (43,3,1,0,2,18);
  (43,3,2,33,2,4);
  (44,3,1,46,2,8);
  (44,3,2,95,2,4);
  (45,3,0,28,2,3);
  (45,3,1,0,2,12);
  (45,3,2,31,2,4);
  (46,3,0,29,2,3);
  (46,3,1,6,1,15);
  (46,3,2,34,2,4);
  (47,3,0,19,2,4);
  (47,3,1,70,2,6);
  (47,3,2,92,2,4);
  (48,3,0,6,2,7);
  (48,3,1,5,3,10);
  (48,3,2,36,2,4);
  (49,3,0,0,2,10);
  (49,3,1,0,3,14);
  (49,3,2,37,2,4);
  (50,3,0,30,2,3);
  (50,3,1,15,2,7);
  (50,3,2,43,2,4);
  (51,3,2,46,2,4);
  (52,3,0,31,2,3);
  (52,3,1,0,2,12);
  (52,3,2,46,2,4);
  (53,3,2,99,2,4);
  (54,3,0,34,2,3);
  (54,3,1,6,1,15);
  (54,3,2,42,2,4);
  (55,3,0,36,2,3);
  (55,3,1,5,3,10);
  (55,3,2,57,3,4);
  (56,3,0,37,2,3);
  (56,3,1,0,3,14);
  (56,3,2,10,3,4);
  (57,3,0,38,2,3);
  (57,3,1,6,1,15);
  (57,3,2,42,2,4);
  (58,3,0,39,2,3);
  (58,3,1,0,3,14);
  (58,3,2,10,3,4);
  (59,3,0,40,2,3);
  (59,3,1,0,2,20);
  (60,3,0,27,2,4);
  (60,3,1,19,2,6);
  (60,3,2,41,2,4);
  (61,3,0,6,2,8);
  (61,3,1,0,2,14);
  (61,3,2,45,2,4);
  (62,3,0,0,2,11);
  (62,3,1,6,1,17);
  (62,3,2,46,2,4);
  (63,3,1,37,2,5);
  (64,3,0,42,2,3);
  (64,3,1,6,1,15);
  (64,3,2,98,1,4);
  (65,3,0,43,2,3);
  (65,3,2,53,2,4);
  (66,3,0,45,2,3);
  (66,3,1,0,2,14);
  (66,3,2,52,2,4);
  (67,3,0,46,2,3);
  (67,3,1,6,1,17);
  (67,3,2,54,2,4);
  (68,3,0,47,2,3);
  (68,3,1,70,2,8);
  (68,3,2,100,2,4);
  (69,3,0,48,2,3);
  (69,3,1,5,3,12);
  (69,3,2,55,2,4);
  (70,3,0,49,2,3);
  (70,3,1,0,3,16);
  (70,3,2,56,2,4);
  (71,3,0,6,2,9);
  (71,3,1,0,3,16);
  (71,3,2,58,2,4);
  (72,3,1,0,2,22);
  (72,3,2,59,2,4);
  (73,3,2,64,2,4);
  (74,3,0,51,2,3);
  (74,3,1,0,2,14);
  (74,3,2,70,2,4);
  (75,3,0,52,2,3);
  (75,3,1,0,2,14);
  (75,3,2,70,2,4);
  (76,3,0,54,2,3);
  (76,3,1,6,1,17);
  (76,3,2,64,2,4);
  (77,3,0,56,2,3);
  (77,3,1,0,3,16);
  (78,3,0,58,2,3);
  (78,3,1,0,3,16);
  (78,3,2,19,3,4);
  (79,3,1,0,2,22);
  (79,3,2,65,2,4);
  (80,3,0,60,2,3);
  (80,3,1,19,2,8);
  (80,3,2,68,2,4);
  (81,3,0,61,2,3);
  (81,3,1,0,2,16);
  (81,3,2,66,2,4);
  (82,3,0,62,2,3);
  (82,3,1,6,1,19);
  (82,3,2,67,2,4);
  (83,3,0,63,2,3);
  (84,3,0,66,2,3);
  (84,3,1,0,2,16);
  (84,3,2,75,2,4);
  (85,3,0,67,2,3);
  (85,3,1,6,1,19);
  (85,3,2,76,2,4);
  (86,3,0,70,2,3);
  (86,3,1,0,3,18);
  (86,3,2,77,2,4);
  (87,3,0,71,2,3);
  (87,3,1,0,3,18);
  (87,3,2,78,2,4);
  (88,3,0,72,2,3);
  (88,3,1,0,2,24);
  (88,3,2,79,2,4);
  (89,3,0,56,2,4);
  (89,3,1,10,3,6);
  (90,3,0,6,2,11);
  (90,3,1,0,2,18);
  (90,3,2,81,2,4);
  (91,3,0,0,2,14);
  (91,3,1,6,1,21);
  (91,3,2,82,2,4);
  (92,3,0,73,2,3);
  (92,3,1,49,2,7);
  (92,3,2,86,2,4);
  (93,3,0,81,2,3);
  (93,3,1,0,2,18);
  (93,3,2,84,2,4);
  (94,3,0,82,2,3);
  (94,3,1,6,1,21);
  (94,3,2,85,2,4);
  (95,3,1,34,2,8);
  (96,3,0,70,2,4);
  (96,3,1,56,2,6);
  (96,3,2,83,2,4);
  (97,3,0,89,2,3);
  (97,3,1,10,3,8);
  (97,3,2,44,3,4);
  (98,3,0,90,2,3);
  (98,3,1,0,2,20);
  (98,3,2,93,2,4);
  (99,3,0,91,2,3);
  (99,3,1,6,1,23);
  (99,3,2,94,2,4);
  (100,3,0,96,2,3);
  (100,3,1,56,2,8);
  (100,3,2,97,2,4)].

Definition tbl_raw (w mc r : nat) : option (nat * nat * nat) :=
  match w with
  | 0 =>
    match mc, r with
    | 1, 0 => Some (6, 1, 3)
    | 1, 1 => Some (0, 2, 8)
    | 1, 2 => Some (0, 3, 4)
    | 2, 0 => Some (6, 1, 3)
    | 2, 2 => Some (0, 3, 4)
    | 3, 0 => Some (6, 1, 3)
    | 3, 1 => Some (0, 2, 8)
    | 3, 2 => Some (0, 3, 4)
    | _, _ => None
    end
  | 1 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 2)
    | 3, 1 => Some (6, 1, 5)
    | 3, 2 => Some (52, 0, 4)
    | _, _ => None
    end
  | 2 =>
    match mc, r with
    | 3, 0 => Some (1, 2, 2)
    | 3, 1 => Some (0, 2, 4)
    | _, _ => None
    end
  | 3 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 3)
    | 3, 1 => Some (0, 2, 10)
    | 3, 2 => Some (27, 2, 4)
    | _, _ => None
    end
  | 4 =>
    match mc, r with
    | 3, 0 => Some (3, 2, 2)
    | 3, 1 => Some (0, 2, 5)
    | 3, 2 => Some (32, 2, 4)
    | _, _ => None
    end
  | 5 =>
    match mc, r with
    | 3, 0 => Some (1, 2, 3)
    | 3, 1 => Some (6, 1, 7)
    | 3, 2 => Some (3, 2, 4)
    | _, _ => None
    end
  | 6 =>
    match mc, r with
    | 0, 1 => Some (0, 3, 6)
    | 1, 1 => Some (0, 3, 6)
    | 3, 0 => Some (0, 2, 4)
    | 3, 1 => Some (0, 3, 6)
    | 3, 2 => Some (5, 3, 4)
    | _, _ => None
    end
  | 7 =>
    match mc, r with
    | 3, 0 => Some (5, 2, 2)
    | 3, 1 => Some (1, 2, 5)
    | 3, 2 => Some (99, 2, 4)
    | _, _ => None
    end
  | 8 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 2)
    | 3, 1 => Some (0, 2, 6)
    | 3, 2 => Some (99, 2, 4)
    | _, _ => None
    end
  | 9 =>
    match mc, r with
    | 3, 0 => Some (2, 2, 3)
    | 3, 2 => Some (5, 2, 4)
    | _, _ => None
    end
  | 10 =>
    match mc, r with
    | 3, 0 => Some (3, 2, 3)
    | 3, 1 => Some (0, 2, 12)
    | 3, 2 => Some (46, 2, 4)
    | _, _ => None
    end
  | 11 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 5)
    | 3, 1 => Some (6, 1, 9)
    | 3, 2 => Some (5, 2, 4)
    | _, _ => None
    end
  | 12 =>
    match mc, r with
    | 3, 0 => Some (4, 2, 3)
    | 3, 1 => Some (0, 2, 7)
    | 3, 2 => Some (10, 2, 4)
    | _, _ => None
    end
  | 13 =>
    match mc, r with
    | 3, 0 => Some (5, 2, 3)
    | 3, 1 => Some (6, 1, 9)
    | 3, 2 => Some (45, 1, 4)
    | _, _ => None
    end
  | 14 =>
    match mc, r with
    | 3, 0 => Some (3, 2, 4)
    | 3, 1 => Some (27, 2, 6)
    | 3, 2 => Some (50, 2, 4)
    | _, _ => None
    end
  | 15 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 6)
    | 3, 1 => Some (0, 2, 14)
    | 3, 2 => Some (10, 2, 4)
    | _, _ => None
    end
  | 16 =>
    match mc, r with
    | 3, 0 => Some (7, 2, 3)
    | 3, 1 => Some (1, 2, 7)
    | 3, 2 => Some (13, 2, 4)
    | _, _ => None
    end
  | 17 =>
    match mc, r with
    | 3, 0 => Some (8, 2, 3)
    | 3, 1 => Some (0, 2, 8)
    | 3, 2 => Some (0, 3, 4)
    | _, _ => None
    end
  | 18 =>
    match mc, r with
    | 3, 0 => Some (9, 2, 3)
    | 3, 1 => Some (0, 2, 8)
    | 3, 2 => Some (0, 3, 4)
    | _, _ => None
    end
  | 19 =>
    match mc, r with
    | 3, 0 => Some (10, 2, 3)
    | 3, 1 => Some (0, 2, 14)
    | 3, 2 => Some (70, 2, 4)
    | _, _ => None
    end
  | 20 =>
    match mc, r with
    | 3, 0 => Some (11, 2, 3)
    | 3, 1 => Some (6, 1, 11)
    | 3, 2 => Some (13, 2, 4)
    | _, _ => None
    end
  | 21 =>
    match mc, r with
    | 3, 0 => Some (5, 2, 4)
    | 3, 1 => Some (3, 2, 6)
    | 3, 2 => Some (12, 2, 4)
    | _, _ => None
    end
  | 22 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 4)
    | 3, 1 => Some (5, 3, 6)
    | 3, 2 => Some (16, 3, 4)
    | _, _ => None
    end
  | 23 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 7)
    | 3, 1 => Some (0, 3, 10)
    | 3, 2 => Some (0, 3, 4)
    | _, _ => None
    end
  | 24 =>
    match mc, r with
    | 3, 0 => Some (19, 2, 2)
    | 3, 1 => Some (10, 2, 5)
    | 3, 2 => Some (74, 2, 4)
    | _, _ => None
    end
  | 25 =>
    match mc, r with
    | 3, 0 => Some (13, 2, 3)
    | 3, 1 => Some (6, 1, 11)
    | 3, 2 => Some (69, 1, 4)
    | _, _ => None
    end
  | 26 =>
    match mc, r with
    | 3, 0 => Some (14, 2, 3)
    | 3, 1 => Some (27, 2, 8)
    | 3, 2 => Some (80, 2, 4)
    | _, _ => None
    end
  | 27 =>
    match mc, r with
    | 3, 0 => Some (15, 2, 3)
    | 3, 1 => Some (0, 2, 16)
    | 3, 2 => Some (19, 2, 4)
    | _, _ => None
    end
  | 28 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 5)
    | 3, 1 => Some (0, 2, 10)
    | 3, 2 => Some (17, 2, 4)
    | _, _ => None
    end
  | 29 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 8)
    | 3, 1 => Some (6, 1, 13)
    | 3, 2 => Some (20, 2, 4)
    | _, _ => None
    end
  | 30 =>
    match mc, r with
    | 3, 0 => Some (27, 2, 2)
    | 3, 1 => Some (15, 2, 5)
    | 3, 2 => Some (33, 3, 4)
    | _, _ => None
    end
  | 31 =>
    match mc, r with
    | 3, 0 => Some (17, 2, 3)
    | 3, 1 => Some (0, 2, 10)
    | 3, 2 => Some (27, 2, 4)
    | _, _ => None
    end
  | 32 =>
    match mc, r with
    | 3, 0 => Some (18, 2, 3)
    | 3, 1 => Some (0, 2, 10)
    | 3, 2 => Some (27, 2, 4)
    | _, _ => None
    end
  | 33 =>
    match mc, r with
    | 3, 0 => Some (19, 2, 3)
    | 3, 1 => Some (0, 2, 16)
    | 3, 2 => Some (88, 2, 4)
    | _, _ => None
    end
  | 34 =>
    match mc, r with
    | 3, 0 => Some (20, 2, 3)
    | 3, 1 => Some (6, 1, 13)
    | 3, 2 => Some (25, 2, 4)
    | _, _ => None
    end
  | 35 =>
    match mc, r with
    | 3, 0 => Some (21, 2, 3)
    | 3, 1 => Some (3, 2, 8)
    | 3, 2 => Some (26, 2, 4)
    | _, _ => None
    end
  | 36 =>
    match mc, r with
    | 3, 0 => Some (22, 2, 3)
    | 3, 1 => Some (5, 3, 8)
    | 3, 2 => Some (35, 3, 4)
    | _, _ => None
    end
  | 37 =>
    match mc, r with
    | 3, 0 => Some (23, 2, 3)
    | 3, 1 => Some (0, 3, 12)
    | 3, 2 => Some (3, 3, 4)
    | _, _ => None
    end
  | 38 =>
    match mc, r with
    | 3, 0 => Some (5, 2, 6)
    | 3, 1 => Some (6, 1, 13)
    | 3, 2 => Some (25, 2, 4)
    | _, _ => None
    end
  | 39 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 6)
    | 3, 1 => Some (0, 3, 12)
    | 3, 2 => Some (3, 3, 4)
    | _, _ => None
    end
  | 40 =>
    match mc, r with
    | 3, 2 => Some (27, 2, 4)
    | _, _ => None
    end
  | 41 =>
    match mc, r with
    | 3, 0 => Some (24, 2, 3)
    | 3, 1 => Some (10, 2, 7)
    | 3, 2 => Some (33, 2, 4)
    | _, _ => None
    end
  | 42 =>
    match mc, r with
    | 3, 0 => Some (25, 2, 3)
    | 3, 1 => Some (6, 1, 13)
    | 3, 2 => Some (87, 1, 4)
    | _, _ => None
    end
  | 43 =>
    match mc, r with
    | 3, 0 => Some (27, 2, 3)
    | 3, 1 => Some (0, 2, 18)
    | 3, 2 => Some (33, 2, 4)
    | _, _ => None
    end
  | 44 =>
    match mc, r with
    | 3, 1 => Some (46, 2, 8)
    | 3, 2 => Some (95, 2, 4)
    | _, _ => None
    end
  | 45 =>
    match mc, r with
    | 3, 0 => Some (28, 2, 3)
    | 3, 1 => Some (0, 2, 12)
    | 3, 2 => Some (31, 2, 4)
    | _, _ => None
    end
  | 46 =>
    match mc, r with
    | 3, 0 => Some (29, 2, 3)
    | 3, 1 => Some (6, 1, 15)
    | 3, 2 => Some (34, 2, 4)
    | _, _ => None
    end
  | 47 =>
    match mc, r with
    | 3, 0 => Some (19, 2, 4)
    | 3, 1 => Some (70, 2, 6)
    | 3, 2 => Some (92, 2, 4)
    | _, _ => None
    end
  | 48 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 7)
    | 3, 1 => Some (5, 3, 10)
    | 3, 2 => Some (36, 2, 4)
    | _, _ => None
    end
  | 49 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 10)
    | 3, 1 => Some (0, 3, 14)
    | 3, 2 => Some (37, 2, 4)
    | _, _ => None
    end
  | 50 =>
    match mc, r with
    | 3, 0 => Some (30, 2, 3)
    | 3, 1 => Some (15, 2, 7)
    | 3, 2 => Some (43, 2, 4)
    | _, _ => None
    end
  | 51 =>
    match mc, r with
    | 3, 2 => Some (46, 2, 4)
    | _, _ => None
    end
  | 52 =>
    match mc, r with
    | 3, 0 => Some (31, 2, 3)
    | 3, 1 => Some (0, 2, 12)
    | 3, 2 => Some (46, 2, 4)
    | _, _ => None
    end
  | 53 =>
    match mc, r with
    | 3, 2 => Some (99, 2, 4)
    | _, _ => None
    end
  | 54 =>
    match mc, r with
    | 3, 0 => Some (34, 2, 3)
    | 3, 1 => Some (6, 1, 15)
    | 3, 2 => Some (42, 2, 4)
    | _, _ => None
    end
  | 55 =>
    match mc, r with
    | 3, 0 => Some (36, 2, 3)
    | 3, 1 => Some (5, 3, 10)
    | 3, 2 => Some (57, 3, 4)
    | _, _ => None
    end
  | 56 =>
    match mc, r with
    | 3, 0 => Some (37, 2, 3)
    | 3, 1 => Some (0, 3, 14)
    | 3, 2 => Some (10, 3, 4)
    | _, _ => None
    end
  | 57 =>
    match mc, r with
    | 3, 0 => Some (38, 2, 3)
    | 3, 1 => Some (6, 1, 15)
    | 3, 2 => Some (42, 2, 4)
    | _, _ => None
    end
  | 58 =>
    match mc, r with
    | 3, 0 => Some (39, 2, 3)
    | 3, 1 => Some (0, 3, 14)
    | 3, 2 => Some (10, 3, 4)
    | _, _ => None
    end
  | 59 =>
    match mc, r with
    | 3, 0 => Some (40, 2, 3)
    | 3, 1 => Some (0, 2, 20)
    | _, _ => None
    end
  | 60 =>
    match mc, r with
    | 3, 0 => Some (27, 2, 4)
    | 3, 1 => Some (19, 2, 6)
    | 3, 2 => Some (41, 2, 4)
    | _, _ => None
    end
  | 61 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 8)
    | 3, 1 => Some (0, 2, 14)
    | 3, 2 => Some (45, 2, 4)
    | _, _ => None
    end
  | 62 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 11)
    | 3, 1 => Some (6, 1, 17)
    | 3, 2 => Some (46, 2, 4)
    | _, _ => None
    end
  | 63 =>
    match mc, r with
    | 3, 1 => Some (37, 2, 5)
    | _, _ => None
    end
  | 64 =>
    match mc, r with
    | 3, 0 => Some (42, 2, 3)
    | 3, 1 => Some (6, 1, 15)
    | 3, 2 => Some (98, 1, 4)
    | _, _ => None
    end
  | 65 =>
    match mc, r with
    | 3, 0 => Some (43, 2, 3)
    | 3, 2 => Some (53, 2, 4)
    | _, _ => None
    end
  | 66 =>
    match mc, r with
    | 3, 0 => Some (45, 2, 3)
    | 3, 1 => Some (0, 2, 14)
    | 3, 2 => Some (52, 2, 4)
    | _, _ => None
    end
  | 67 =>
    match mc, r with
    | 3, 0 => Some (46, 2, 3)
    | 3, 1 => Some (6, 1, 17)
    | 3, 2 => Some (54, 2, 4)
    | _, _ => None
    end
  | 68 =>
    match mc, r with
    | 3, 0 => Some (47, 2, 3)
    | 3, 1 => Some (70, 2, 8)
    | 3, 2 => Some (100, 2, 4)
    | _, _ => None
    end
  | 69 =>
    match mc, r with
    | 3, 0 => Some (48, 2, 3)
    | 3, 1 => Some (5, 3, 12)
    | 3, 2 => Some (55, 2, 4)
    | _, _ => None
    end
  | 70 =>
    match mc, r with
    | 3, 0 => Some (49, 2, 3)
    | 3, 1 => Some (0, 3, 16)
    | 3, 2 => Some (56, 2, 4)
    | _, _ => None
    end
  | 71 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 9)
    | 3, 1 => Some (0, 3, 16)
    | 3, 2 => Some (58, 2, 4)
    | _, _ => None
    end
  | 72 =>
    match mc, r with
    | 3, 1 => Some (0, 2, 22)
    | 3, 2 => Some (59, 2, 4)
    | _, _ => None
    end
  | 73 =>
    match mc, r with
    | 3, 2 => Some (64, 2, 4)
    | _, _ => None
    end
  | 74 =>
    match mc, r with
    | 3, 0 => Some (51, 2, 3)
    | 3, 1 => Some (0, 2, 14)
    | 3, 2 => Some (70, 2, 4)
    | _, _ => None
    end
  | 75 =>
    match mc, r with
    | 3, 0 => Some (52, 2, 3)
    | 3, 1 => Some (0, 2, 14)
    | 3, 2 => Some (70, 2, 4)
    | _, _ => None
    end
  | 76 =>
    match mc, r with
    | 3, 0 => Some (54, 2, 3)
    | 3, 1 => Some (6, 1, 17)
    | 3, 2 => Some (64, 2, 4)
    | _, _ => None
    end
  | 77 =>
    match mc, r with
    | 3, 0 => Some (56, 2, 3)
    | 3, 1 => Some (0, 3, 16)
    | _, _ => None
    end
  | 78 =>
    match mc, r with
    | 3, 0 => Some (58, 2, 3)
    | 3, 1 => Some (0, 3, 16)
    | 3, 2 => Some (19, 3, 4)
    | _, _ => None
    end
  | 79 =>
    match mc, r with
    | 3, 1 => Some (0, 2, 22)
    | 3, 2 => Some (65, 2, 4)
    | _, _ => None
    end
  | 80 =>
    match mc, r with
    | 3, 0 => Some (60, 2, 3)
    | 3, 1 => Some (19, 2, 8)
    | 3, 2 => Some (68, 2, 4)
    | _, _ => None
    end
  | 81 =>
    match mc, r with
    | 3, 0 => Some (61, 2, 3)
    | 3, 1 => Some (0, 2, 16)
    | 3, 2 => Some (66, 2, 4)
    | _, _ => None
    end
  | 82 =>
    match mc, r with
    | 3, 0 => Some (62, 2, 3)
    | 3, 1 => Some (6, 1, 19)
    | 3, 2 => Some (67, 2, 4)
    | _, _ => None
    end
  | 83 =>
    match mc, r with
    | 3, 0 => Some (63, 2, 3)
    | _, _ => None
    end
  | 84 =>
    match mc, r with
    | 3, 0 => Some (66, 2, 3)
    | 3, 1 => Some (0, 2, 16)
    | 3, 2 => Some (75, 2, 4)
    | _, _ => None
    end
  | 85 =>
    match mc, r with
    | 3, 0 => Some (67, 2, 3)
    | 3, 1 => Some (6, 1, 19)
    | 3, 2 => Some (76, 2, 4)
    | _, _ => None
    end
  | 86 =>
    match mc, r with
    | 3, 0 => Some (70, 2, 3)
    | 3, 1 => Some (0, 3, 18)
    | 3, 2 => Some (77, 2, 4)
    | _, _ => None
    end
  | 87 =>
    match mc, r with
    | 3, 0 => Some (71, 2, 3)
    | 3, 1 => Some (0, 3, 18)
    | 3, 2 => Some (78, 2, 4)
    | _, _ => None
    end
  | 88 =>
    match mc, r with
    | 3, 0 => Some (72, 2, 3)
    | 3, 1 => Some (0, 2, 24)
    | 3, 2 => Some (79, 2, 4)
    | _, _ => None
    end
  | 89 =>
    match mc, r with
    | 3, 0 => Some (56, 2, 4)
    | 3, 1 => Some (10, 3, 6)
    | _, _ => None
    end
  | 90 =>
    match mc, r with
    | 3, 0 => Some (6, 2, 11)
    | 3, 1 => Some (0, 2, 18)
    | 3, 2 => Some (81, 2, 4)
    | _, _ => None
    end
  | 91 =>
    match mc, r with
    | 3, 0 => Some (0, 2, 14)
    | 3, 1 => Some (6, 1, 21)
    | 3, 2 => Some (82, 2, 4)
    | _, _ => None
    end
  | 92 =>
    match mc, r with
    | 3, 0 => Some (73, 2, 3)
    | 3, 1 => Some (49, 2, 7)
    | 3, 2 => Some (86, 2, 4)
    | _, _ => None
    end
  | 93 =>
    match mc, r with
    | 3, 0 => Some (81, 2, 3)
    | 3, 1 => Some (0, 2, 18)
    | 3, 2 => Some (84, 2, 4)
    | _, _ => None
    end
  | 94 =>
    match mc, r with
    | 3, 0 => Some (82, 2, 3)
    | 3, 1 => Some (6, 1, 21)
    | 3, 2 => Some (85, 2, 4)
    | _, _ => None
    end
  | 95 =>
    match mc, r with
    | 3, 1 => Some (34, 2, 8)
    | _, _ => None
    end
  | 96 =>
    match mc, r with
    | 3, 0 => Some (70, 2, 4)
    | 3, 1 => Some (56, 2, 6)
    | 3, 2 => Some (83, 2, 4)
    | _, _ => None
    end
  | 97 =>
    match mc, r with
    | 3, 0 => Some (89, 2, 3)
    | 3, 1 => Some (10, 3, 8)
    | 3, 2 => Some (44, 3, 4)
    | _, _ => None
    end
  | 98 =>
    match mc, r with
    | 3, 0 => Some (90, 2, 3)
    | 3, 1 => Some (0, 2, 20)
    | 3, 2 => Some (93, 2, 4)
    | _, _ => None
    end
  | 99 =>
    match mc, r with
    | 3, 0 => Some (91, 2, 3)
    | 3, 1 => Some (6, 1, 23)
    | 3, 2 => Some (94, 2, 4)
    | _, _ => None
    end
  | 100 =>
    match mc, r with
    | 3, 0 => Some (96, 2, 3)
    | 3, 1 => Some (56, 2, 8)
    | 3, 2 => Some (97, 2, 4)
    | _, _ => None
    end
  | _ => None
  end.


Definition nwords : nat := Eval vm_compute in length words.

Definition tbl (w mc r : nat) : option (nat * nat * nat) :=
  if andb (andb (Nat.ltb w nwords) (Nat.ltb mc 4)) (Nat.ltb r 3) then tbl_raw w mc r else None.


(* Bell a w m = D> 0 110 10 1^a W B^m, with W = word w *)
Definition Bl (a w m : nat) := P 1 a (word w *> B^^m *> 0inf).

Lemma Pass j k X : P j (3+k) X -->* P (2+j) k X.
Proof. unfold P. es. Qed.

Lemma Passes q j k X : P j (q*3+k) X -->* P (q*2+j) k X.
Proof. gen j k. ind q Pass. Qed.

(* ---------- the table ---------- *)

Definition eq6 (x y : nat * nat * nat * nat * nat * nat) : bool :=
  let '(a1, a2, a3, a4, a5, a6) := x in
  let '(b1, b2, b3, b4, b5, b6) := y in
  andb (andb (andb (andb (andb (Nat.eqb a1 b1) (Nat.eqb a2 b2)) (Nat.eqb a3 b3)) (Nat.eqb a4 b4)) (Nat.eqb a5 b5)) (Nat.eqb a6 b6).

Definition tbl_check : bool :=
  forallb (fun w => forallb (fun mc => forallb (fun r =>
    match tbl_raw w mc r with
    | None => true
    | Some (w', dmp, e) => existsb (eq6 (w, mc, r, w', dmp, e)) entries
    end) (seq 0 3)) (seq 0 4)) (seq 0 nwords).

Lemma tbl_check_true : tbl_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma eq6_spec x y : eq6 x y = true -> x = y.
Proof.
  destruct x as [[[[[a1 a2] a3] a4] a5] a6], y as [[[[[b1 b2] b3] b4] b5] b6].
  cbn. intro H. repeat rewrite andb_true_iff in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end.
  subst. reflexivity.
Qed.

Lemma tbl_in w mc r w' dmp e :
  tbl w mc r = Some (w', dmp, e) -> In (w, mc, r, w', dmp, e) entries.
Proof.
  unfold tbl. intro H.
  destruct (Nat.ltb w nwords) eqn:Hw; [|discriminate].
  destruct (Nat.ltb mc 4) eqn:Hm; [|discriminate].
  destruct (Nat.ltb r 3) eqn:Hr; [|discriminate].
  cbn in H.
  apply Nat.ltb_lt in Hw, Hm, Hr.
  pose proof tbl_check_true as C. unfold tbl_check in C.
  rewrite forallb_forall in C. specialize (C w).
  rewrite in_seq in C. specialize (C ltac:(lia)).
  rewrite forallb_forall in C. specialize (C mc).
  rewrite in_seq in C. specialize (C ltac:(lia)).
  rewrite forallb_forall in C. specialize (C r).
  rewrite in_seq in C. specialize (C ltac:(lia)).
  rewrite H in C.
  apply existsb_exists in C. destruct C as [y [Hy E]].
  apply eq6_spec in E. subst y. exact Hy.
Qed.

(* ---------- one Bell step per table entry ---------- *)

Definition entry_ok (x : nat * nat * nat * nat * nat * nat) : Prop :=
  let '(w, mc, r, w', dmp, e) := x in
  forall q m, Nat.min m 3 = mc -> Bl (q*3+r) w m -->* Bl (q*4+e) w' (m+dmp-2).

Lemma ok3 w r w' dmp e :
  (forall q m, P (q*2+1) r (word w *> B^^(3+m) *> 0inf) -->*
               P 1 (q*4+e) (word w' *> B^^(1+dmp+m) *> 0inf)) ->
  entry_ok (w, 3, r, w', dmp, e).
Proof.
  intros H q m Hm. unfold Bl.
  replace m with (3 + (m-3)) by lia.
  eapply evstep_trans. { apply (Passes q 1 r). }
  replace (3 + (m-3) + dmp - 2) with (1 + dmp + (m-3)) by lia.
  apply H.
Qed.

Lemma ok_small w mc r w' dmp e :
  mc < 3 ->
  (forall q, P (q*2+1) r (word w *> B^^mc *> 0inf) -->*
             P 1 (q*4+e) (word w' *> B^^(mc+dmp-2) *> 0inf)) ->
  entry_ok (w, mc, r, w', dmp, e).
Proof.
  intros Hmc H q m Hm. unfold Bl.
  assert (m = mc) by lia. subst m.
  eapply evstep_trans. { apply (Passes q 1 r). }
  apply H.
Qed.

(* generated by gen_k.py: one lemma per table entry, from the end lemmas *)

Lemma K_0 : entry_ok (0, 1, 0, 6, 1, 3).
Proof. apply ok_small; [lia|]. exact E_e_1_0. Qed.

Lemma K_1 : entry_ok (0, 1, 1, 0, 2, 8).
Proof. apply ok_small; [lia|]. exact E_e_1_1. Qed.

Lemma K_2 : entry_ok (0, 1, 2, 0, 3, 4).
Proof. apply ok_small; [lia|]. exact E_e_1_2. Qed.

Lemma K_3 : entry_ok (0, 2, 0, 6, 1, 3).
Proof. apply ok_small; [lia|]. exact E_e_2_0. Qed.

Lemma K_4 : entry_ok (0, 2, 2, 0, 3, 4).
Proof. apply ok_small; [lia|]. exact E_e_2_2. Qed.

Lemma K_5 : entry_ok (0, 3, 0, 6, 1, 3).
Proof. apply ok3. exact E_e_3_0. Qed.

Lemma K_6 : entry_ok (0, 3, 1, 0, 2, 8).
Proof. apply ok3. exact E_e_3_1. Qed.

Lemma K_7 : entry_ok (0, 3, 2, 0, 3, 4).
Proof. apply ok3. exact E_e_3_2. Qed.

Lemma K_8 : entry_ok (1, 3, 0, 0, 2, 2).
Proof. apply ok3. exact E_0_3_0. Qed.

Lemma K_9 : entry_ok (1, 3, 1, 6, 1, 5).
Proof. apply ok3. exact E_0_3_1. Qed.

Lemma K_10 : entry_ok (1, 3, 2, 52, 0, 4).
Proof. apply ok3. exact E_0_3_2. Qed.

Lemma K_11 : entry_ok (2, 3, 0, 1, 2, 2).
Proof. apply ok3. exact E_00_3_0. Qed.

Lemma K_12 : entry_ok (2, 3, 1, 0, 2, 4).
Proof. apply ok3. exact E_00_3_1. Qed.

Lemma K_13 : entry_ok (3, 3, 0, 0, 2, 3).
Proof. apply ok3. exact E_01_3_0. Qed.

Lemma K_14 : entry_ok (3, 3, 1, 0, 2, 10).
Proof. apply ok3. exact E_01_3_1. Qed.

Lemma K_15 : entry_ok (3, 3, 2, 27, 2, 4).
Proof. apply ok3. exact E_01_3_2. Qed.

Lemma K_16 : entry_ok (4, 3, 0, 3, 2, 2).
Proof. apply ok3. exact E_001_3_0. Qed.

Lemma K_17 : entry_ok (4, 3, 1, 0, 2, 5).
Proof. apply ok3. exact E_001_3_1. Qed.

Lemma K_18 : entry_ok (4, 3, 2, 32, 2, 4).
Proof. apply ok3. exact E_001_3_2. Qed.

Lemma K_19 : entry_ok (5, 3, 0, 1, 2, 3).
Proof. apply ok3. exact E_010_3_0. Qed.

Lemma K_20 : entry_ok (5, 3, 1, 6, 1, 7).
Proof. apply ok3. exact E_010_3_1. Qed.

Lemma K_21 : entry_ok (5, 3, 2, 3, 2, 4).
Proof. apply ok3. exact E_010_3_2. Qed.

Lemma K_22 : entry_ok (6, 0, 1, 0, 3, 6).
Proof. apply ok_small; [lia|]. exact E_011_0_1. Qed.

Lemma K_23 : entry_ok (6, 1, 1, 0, 3, 6).
Proof. apply ok_small; [lia|]. exact E_011_1_1. Qed.

Lemma K_24 : entry_ok (6, 3, 0, 0, 2, 4).
Proof. apply ok3. exact E_011_3_0. Qed.

Lemma K_25 : entry_ok (6, 3, 1, 0, 3, 6).
Proof. apply ok3. exact E_011_3_1. Qed.

Lemma K_26 : entry_ok (6, 3, 2, 5, 3, 4).
Proof. apply ok3. exact E_011_3_2. Qed.

Lemma K_27 : entry_ok (7, 3, 0, 5, 2, 2).
Proof. apply ok3. exact E_0010_3_0. Qed.

Lemma K_28 : entry_ok (7, 3, 1, 1, 2, 5).
Proof. apply ok3. exact E_0010_3_1. Qed.

Lemma K_29 : entry_ok (7, 3, 2, 99, 2, 4).
Proof. apply ok3. exact E_0010_3_2. Qed.

Lemma K_30 : entry_ok (8, 3, 0, 6, 2, 2).
Proof. apply ok3. exact E_0011_3_0. Qed.

Lemma K_31 : entry_ok (8, 3, 1, 0, 2, 6).
Proof. apply ok3. exact E_0011_3_1. Qed.

Lemma K_32 : entry_ok (8, 3, 2, 99, 2, 4).
Proof. apply ok3. exact E_0011_3_2. Qed.

Lemma K_33 : entry_ok (9, 3, 0, 2, 2, 3).
Proof. apply ok3. exact E_0100_3_0. Qed.

Lemma K_34 : entry_ok (9, 3, 2, 5, 2, 4).
Proof. apply ok3. exact E_0100_3_2. Qed.

Lemma K_35 : entry_ok (10, 3, 0, 3, 2, 3).
Proof. apply ok3. exact E_0101_3_0. Qed.

Lemma K_36 : entry_ok (10, 3, 1, 0, 2, 12).
Proof. apply ok3. exact E_0101_3_1. Qed.

Lemma K_37 : entry_ok (10, 3, 2, 46, 2, 4).
Proof. apply ok3. exact E_0101_3_2. Qed.

Lemma K_38 : entry_ok (11, 3, 0, 0, 2, 5).
Proof. apply ok3. exact E_0111_3_0. Qed.

Lemma K_39 : entry_ok (11, 3, 1, 6, 1, 9).
Proof. apply ok3. exact E_0111_3_1. Qed.

Lemma K_40 : entry_ok (11, 3, 2, 5, 2, 4).
Proof. apply ok3. exact E_0111_3_2. Qed.

Lemma K_41 : entry_ok (12, 3, 0, 4, 2, 3).
Proof. apply ok3. exact E_01001_3_0. Qed.

Lemma K_42 : entry_ok (12, 3, 1, 0, 2, 7).
Proof. apply ok3. exact E_01001_3_1. Qed.

Lemma K_43 : entry_ok (12, 3, 2, 10, 2, 4).
Proof. apply ok3. exact E_01001_3_2. Qed.

Lemma K_44 : entry_ok (13, 3, 0, 5, 2, 3).
Proof. apply ok3. exact E_01010_3_0. Qed.

Lemma K_45 : entry_ok (13, 3, 1, 6, 1, 9).
Proof. apply ok3. exact E_01010_3_1. Qed.

Lemma K_46 : entry_ok (13, 3, 2, 45, 1, 4).
Proof. apply ok3. exact E_01010_3_2. Qed.

Lemma K_47 : entry_ok (14, 3, 0, 3, 2, 4).
Proof. apply ok3. exact E_01101_3_0. Qed.

Lemma K_48 : entry_ok (14, 3, 1, 27, 2, 6).
Proof. apply ok3. exact E_01101_3_1. Qed.

Lemma K_49 : entry_ok (14, 3, 2, 50, 2, 4).
Proof. apply ok3. exact E_01101_3_2. Qed.

Lemma K_50 : entry_ok (15, 3, 0, 0, 2, 6).
Proof. apply ok3. exact E_01111_3_0. Qed.

Lemma K_51 : entry_ok (15, 3, 1, 0, 2, 14).
Proof. apply ok3. exact E_01111_3_1. Qed.

Lemma K_52 : entry_ok (15, 3, 2, 10, 2, 4).
Proof. apply ok3. exact E_01111_3_2. Qed.

Lemma K_53 : entry_ok (16, 3, 0, 7, 2, 3).
Proof. apply ok3. exact E_010010_3_0. Qed.

Lemma K_54 : entry_ok (16, 3, 1, 1, 2, 7).
Proof. apply ok3. exact E_010010_3_1. Qed.

Lemma K_55 : entry_ok (16, 3, 2, 13, 2, 4).
Proof. apply ok3. exact E_010010_3_2. Qed.

Lemma K_56 : entry_ok (17, 3, 0, 8, 2, 3).
Proof. apply ok3. exact E_010011_3_0. Qed.

Lemma K_57 : entry_ok (17, 3, 1, 0, 2, 8).
Proof. apply ok3. exact E_010011_3_1. Qed.

Lemma K_58 : entry_ok (17, 3, 2, 0, 3, 4).
Proof. apply ok3. exact E_010011_3_2. Qed.

Lemma K_59 : entry_ok (18, 3, 0, 9, 2, 3).
Proof. apply ok3. exact E_010100_3_0. Qed.

Lemma K_60 : entry_ok (18, 3, 1, 0, 2, 8).
Proof. apply ok3. exact E_010100_3_1. Qed.

Lemma K_61 : entry_ok (18, 3, 2, 0, 3, 4).
Proof. apply ok3. exact E_010100_3_2. Qed.

Lemma K_62 : entry_ok (19, 3, 0, 10, 2, 3).
Proof. apply ok3. exact E_010101_3_0. Qed.

Lemma K_63 : entry_ok (19, 3, 1, 0, 2, 14).
Proof. apply ok3. exact E_010101_3_1. Qed.

Lemma K_64 : entry_ok (19, 3, 2, 70, 2, 4).
Proof. apply ok3. exact E_010101_3_2. Qed.

Lemma K_65 : entry_ok (20, 3, 0, 11, 2, 3).
Proof. apply ok3. exact E_010111_3_0. Qed.

Lemma K_66 : entry_ok (20, 3, 1, 6, 1, 11).
Proof. apply ok3. exact E_010111_3_1. Qed.

Lemma K_67 : entry_ok (20, 3, 2, 13, 2, 4).
Proof. apply ok3. exact E_010111_3_2. Qed.

Lemma K_68 : entry_ok (21, 3, 0, 5, 2, 4).
Proof. apply ok3. exact E_011010_3_0. Qed.

Lemma K_69 : entry_ok (21, 3, 1, 3, 2, 6).
Proof. apply ok3. exact E_011010_3_1. Qed.

Lemma K_70 : entry_ok (21, 3, 2, 12, 2, 4).
Proof. apply ok3. exact E_011010_3_2. Qed.

Lemma K_71 : entry_ok (22, 3, 0, 6, 2, 4).
Proof. apply ok3. exact E_011011_3_0. Qed.

Lemma K_72 : entry_ok (22, 3, 1, 5, 3, 6).
Proof. apply ok3. exact E_011011_3_1. Qed.

Lemma K_73 : entry_ok (22, 3, 2, 16, 3, 4).
Proof. apply ok3. exact E_011011_3_2. Qed.

Lemma K_74 : entry_ok (23, 3, 0, 0, 2, 7).
Proof. apply ok3. exact E_011111_3_0. Qed.

Lemma K_75 : entry_ok (23, 3, 1, 0, 3, 10).
Proof. apply ok3. exact E_011111_3_1. Qed.

Lemma K_76 : entry_ok (23, 3, 2, 0, 3, 4).
Proof. apply ok3. exact E_011111_3_2. Qed.

Lemma K_77 : entry_ok (24, 3, 0, 19, 2, 2).
Proof. apply ok3. exact E_0010101_3_0. Qed.

Lemma K_78 : entry_ok (24, 3, 1, 10, 2, 5).
Proof. apply ok3. exact E_0010101_3_1. Qed.

Lemma K_79 : entry_ok (24, 3, 2, 74, 2, 4).
Proof. apply ok3. exact E_0010101_3_2. Qed.

Lemma K_80 : entry_ok (25, 3, 0, 13, 2, 3).
Proof. apply ok3. exact E_0101010_3_0. Qed.

Lemma K_81 : entry_ok (25, 3, 1, 6, 1, 11).
Proof. apply ok3. exact E_0101010_3_1. Qed.

Lemma K_82 : entry_ok (25, 3, 2, 69, 1, 4).
Proof. apply ok3. exact E_0101010_3_2. Qed.

Lemma K_83 : entry_ok (26, 3, 0, 14, 2, 3).
Proof. apply ok3. exact E_0101101_3_0. Qed.

Lemma K_84 : entry_ok (26, 3, 1, 27, 2, 8).
Proof. apply ok3. exact E_0101101_3_1. Qed.

Lemma K_85 : entry_ok (26, 3, 2, 80, 2, 4).
Proof. apply ok3. exact E_0101101_3_2. Qed.

Lemma K_86 : entry_ok (27, 3, 0, 15, 2, 3).
Proof. apply ok3. exact E_0101111_3_0. Qed.

Lemma K_87 : entry_ok (27, 3, 1, 0, 2, 16).
Proof. apply ok3. exact E_0101111_3_1. Qed.

Lemma K_88 : entry_ok (27, 3, 2, 19, 2, 4).
Proof. apply ok3. exact E_0101111_3_2. Qed.

Lemma K_89 : entry_ok (28, 3, 0, 6, 2, 5).
Proof. apply ok3. exact E_0111011_3_0. Qed.

Lemma K_90 : entry_ok (28, 3, 1, 0, 2, 10).
Proof. apply ok3. exact E_0111011_3_1. Qed.

Lemma K_91 : entry_ok (28, 3, 2, 17, 2, 4).
Proof. apply ok3. exact E_0111011_3_2. Qed.

Lemma K_92 : entry_ok (29, 3, 0, 0, 2, 8).
Proof. apply ok3. exact E_0111111_3_0. Qed.

Lemma K_93 : entry_ok (29, 3, 1, 6, 1, 13).
Proof. apply ok3. exact E_0111111_3_1. Qed.

Lemma K_94 : entry_ok (29, 3, 2, 20, 2, 4).
Proof. apply ok3. exact E_0111111_3_2. Qed.

Lemma K_95 : entry_ok (30, 3, 0, 27, 2, 2).
Proof. apply ok3. exact E_00101111_3_0. Qed.

Lemma K_96 : entry_ok (30, 3, 1, 15, 2, 5).
Proof. apply ok3. exact E_00101111_3_1. Qed.

Lemma K_97 : entry_ok (30, 3, 2, 33, 3, 4).
Proof. apply ok3. exact E_00101111_3_2. Qed.

Lemma K_98 : entry_ok (31, 3, 0, 17, 2, 3).
Proof. apply ok3. exact E_01010011_3_0. Qed.

Lemma K_99 : entry_ok (31, 3, 1, 0, 2, 10).
Proof. apply ok3. exact E_01010011_3_1. Qed.

Lemma K_100 : entry_ok (31, 3, 2, 27, 2, 4).
Proof. apply ok3. exact E_01010011_3_2. Qed.

Lemma K_101 : entry_ok (32, 3, 0, 18, 2, 3).
Proof. apply ok3. exact E_01010100_3_0. Qed.

Lemma K_102 : entry_ok (32, 3, 1, 0, 2, 10).
Proof. apply ok3. exact E_01010100_3_1. Qed.

Lemma K_103 : entry_ok (32, 3, 2, 27, 2, 4).
Proof. apply ok3. exact E_01010100_3_2. Qed.

Lemma K_104 : entry_ok (33, 3, 0, 19, 2, 3).
Proof. apply ok3. exact E_01010101_3_0. Qed.

Lemma K_105 : entry_ok (33, 3, 1, 0, 2, 16).
Proof. apply ok3. exact E_01010101_3_1. Qed.

Lemma K_106 : entry_ok (33, 3, 2, 88, 2, 4).
Proof. apply ok3. exact E_01010101_3_2. Qed.

Lemma K_107 : entry_ok (34, 3, 0, 20, 2, 3).
Proof. apply ok3. exact E_01010111_3_0. Qed.

Lemma K_108 : entry_ok (34, 3, 1, 6, 1, 13).
Proof. apply ok3. exact E_01010111_3_1. Qed.

Lemma K_109 : entry_ok (34, 3, 2, 25, 2, 4).
Proof. apply ok3. exact E_01010111_3_2. Qed.

Lemma K_110 : entry_ok (35, 3, 0, 21, 2, 3).
Proof. apply ok3. exact E_01011010_3_0. Qed.

Lemma K_111 : entry_ok (35, 3, 1, 3, 2, 8).
Proof. apply ok3. exact E_01011010_3_1. Qed.

Lemma K_112 : entry_ok (35, 3, 2, 26, 2, 4).
Proof. apply ok3. exact E_01011010_3_2. Qed.

Lemma K_113 : entry_ok (36, 3, 0, 22, 2, 3).
Proof. apply ok3. exact E_01011011_3_0. Qed.

Lemma K_114 : entry_ok (36, 3, 1, 5, 3, 8).
Proof. apply ok3. exact E_01011011_3_1. Qed.

Lemma K_115 : entry_ok (36, 3, 2, 35, 3, 4).
Proof. apply ok3. exact E_01011011_3_2. Qed.

Lemma K_116 : entry_ok (37, 3, 0, 23, 2, 3).
Proof. apply ok3. exact E_01011111_3_0. Qed.

Lemma K_117 : entry_ok (37, 3, 1, 0, 3, 12).
Proof. apply ok3. exact E_01011111_3_1. Qed.

Lemma K_118 : entry_ok (37, 3, 2, 3, 3, 4).
Proof. apply ok3. exact E_01011111_3_2. Qed.

Lemma K_119 : entry_ok (38, 3, 0, 5, 2, 6).
Proof. apply ok3. exact E_01111010_3_0. Qed.

Lemma K_120 : entry_ok (38, 3, 1, 6, 1, 13).
Proof. apply ok3. exact E_01111010_3_1. Qed.

Lemma K_121 : entry_ok (38, 3, 2, 25, 2, 4).
Proof. apply ok3. exact E_01111010_3_2. Qed.

Lemma K_122 : entry_ok (39, 3, 0, 6, 2, 6).
Proof. apply ok3. exact E_01111011_3_0. Qed.

Lemma K_123 : entry_ok (39, 3, 1, 0, 3, 12).
Proof. apply ok3. exact E_01111011_3_1. Qed.

Lemma K_124 : entry_ok (39, 3, 2, 3, 3, 4).
Proof. apply ok3. exact E_01111011_3_2. Qed.

Lemma K_125 : entry_ok (40, 3, 2, 27, 2, 4).
Proof. apply ok3. exact E_01111111_3_2. Qed.

Lemma K_126 : entry_ok (41, 3, 0, 24, 2, 3).
Proof. apply ok3. exact E_010010101_3_0. Qed.

Lemma K_127 : entry_ok (41, 3, 1, 10, 2, 7).
Proof. apply ok3. exact E_010010101_3_1. Qed.

Lemma K_128 : entry_ok (41, 3, 2, 33, 2, 4).
Proof. apply ok3. exact E_010010101_3_2. Qed.

Lemma K_129 : entry_ok (42, 3, 0, 25, 2, 3).
Proof. apply ok3. exact E_010101010_3_0. Qed.

Lemma K_130 : entry_ok (42, 3, 1, 6, 1, 13).
Proof. apply ok3. exact E_010101010_3_1. Qed.

Lemma K_131 : entry_ok (42, 3, 2, 87, 1, 4).
Proof. apply ok3. exact E_010101010_3_2. Qed.

Lemma K_132 : entry_ok (43, 3, 0, 27, 2, 3).
Proof. apply ok3. exact E_010101111_3_0. Qed.

Lemma K_133 : entry_ok (43, 3, 1, 0, 2, 18).
Proof. apply ok3. exact E_010101111_3_1. Qed.

Lemma K_134 : entry_ok (43, 3, 2, 33, 2, 4).
Proof. apply ok3. exact E_010101111_3_2. Qed.

Lemma K_135 : entry_ok (44, 3, 1, 46, 2, 8).
Proof. apply ok3. exact E_010110101_3_1. Qed.

Lemma K_136 : entry_ok (44, 3, 2, 95, 2, 4).
Proof. apply ok3. exact E_010110101_3_2. Qed.

Lemma K_137 : entry_ok (45, 3, 0, 28, 2, 3).
Proof. apply ok3. exact E_010111011_3_0. Qed.

Lemma K_138 : entry_ok (45, 3, 1, 0, 2, 12).
Proof. apply ok3. exact E_010111011_3_1. Qed.

Lemma K_139 : entry_ok (45, 3, 2, 31, 2, 4).
Proof. apply ok3. exact E_010111011_3_2. Qed.

Lemma K_140 : entry_ok (46, 3, 0, 29, 2, 3).
Proof. apply ok3. exact E_010111111_3_0. Qed.

Lemma K_141 : entry_ok (46, 3, 1, 6, 1, 15).
Proof. apply ok3. exact E_010111111_3_1. Qed.

Lemma K_142 : entry_ok (46, 3, 2, 34, 2, 4).
Proof. apply ok3. exact E_010111111_3_2. Qed.

Lemma K_143 : entry_ok (47, 3, 0, 19, 2, 4).
Proof. apply ok3. exact E_011010101_3_0. Qed.

Lemma K_144 : entry_ok (47, 3, 1, 70, 2, 6).
Proof. apply ok3. exact E_011010101_3_1. Qed.

Lemma K_145 : entry_ok (47, 3, 2, 92, 2, 4).
Proof. apply ok3. exact E_011010101_3_2. Qed.

Lemma K_146 : entry_ok (48, 3, 0, 6, 2, 7).
Proof. apply ok3. exact E_011111011_3_0. Qed.

Lemma K_147 : entry_ok (48, 3, 1, 5, 3, 10).
Proof. apply ok3. exact E_011111011_3_1. Qed.

Lemma K_148 : entry_ok (48, 3, 2, 36, 2, 4).
Proof. apply ok3. exact E_011111011_3_2. Qed.

Lemma K_149 : entry_ok (49, 3, 0, 0, 2, 10).
Proof. apply ok3. exact E_011111111_3_0. Qed.

Lemma K_150 : entry_ok (49, 3, 1, 0, 3, 14).
Proof. apply ok3. exact E_011111111_3_1. Qed.

Lemma K_151 : entry_ok (49, 3, 2, 37, 2, 4).
Proof. apply ok3. exact E_011111111_3_2. Qed.

Lemma K_152 : entry_ok (50, 3, 0, 30, 2, 3).
Proof. apply ok3. exact E_0100101111_3_0. Qed.

Lemma K_153 : entry_ok (50, 3, 1, 15, 2, 7).
Proof. apply ok3. exact E_0100101111_3_1. Qed.

Lemma K_154 : entry_ok (50, 3, 2, 43, 2, 4).
Proof. apply ok3. exact E_0100101111_3_2. Qed.

Lemma K_155 : entry_ok (51, 3, 2, 46, 2, 4).
Proof. apply ok3. exact E_0101001111_3_2. Qed.

Lemma K_156 : entry_ok (52, 3, 0, 31, 2, 3).
Proof. apply ok3. exact E_0101010011_3_0. Qed.

Lemma K_157 : entry_ok (52, 3, 1, 0, 2, 12).
Proof. apply ok3. exact E_0101010011_3_1. Qed.

Lemma K_158 : entry_ok (52, 3, 2, 46, 2, 4).
Proof. apply ok3. exact E_0101010011_3_2. Qed.

Lemma K_159 : entry_ok (53, 3, 2, 99, 2, 4).
Proof. apply ok3. exact E_0101010101_3_2. Qed.

Lemma K_160 : entry_ok (54, 3, 0, 34, 2, 3).
Proof. apply ok3. exact E_0101010111_3_0. Qed.

Lemma K_161 : entry_ok (54, 3, 1, 6, 1, 15).
Proof. apply ok3. exact E_0101010111_3_1. Qed.

Lemma K_162 : entry_ok (54, 3, 2, 42, 2, 4).
Proof. apply ok3. exact E_0101010111_3_2. Qed.

Lemma K_163 : entry_ok (55, 3, 0, 36, 2, 3).
Proof. apply ok3. exact E_0101011011_3_0. Qed.

Lemma K_164 : entry_ok (55, 3, 1, 5, 3, 10).
Proof. apply ok3. exact E_0101011011_3_1. Qed.

Lemma K_165 : entry_ok (55, 3, 2, 57, 3, 4).
Proof. apply ok3. exact E_0101011011_3_2. Qed.

Lemma K_166 : entry_ok (56, 3, 0, 37, 2, 3).
Proof. apply ok3. exact E_0101011111_3_0. Qed.

Lemma K_167 : entry_ok (56, 3, 1, 0, 3, 14).
Proof. apply ok3. exact E_0101011111_3_1. Qed.

Lemma K_168 : entry_ok (56, 3, 2, 10, 3, 4).
Proof. apply ok3. exact E_0101011111_3_2. Qed.

Lemma K_169 : entry_ok (57, 3, 0, 38, 2, 3).
Proof. apply ok3. exact E_0101111010_3_0. Qed.

Lemma K_170 : entry_ok (57, 3, 1, 6, 1, 15).
Proof. apply ok3. exact E_0101111010_3_1. Qed.

Lemma K_171 : entry_ok (57, 3, 2, 42, 2, 4).
Proof. apply ok3. exact E_0101111010_3_2. Qed.

Lemma K_172 : entry_ok (58, 3, 0, 39, 2, 3).
Proof. apply ok3. exact E_0101111011_3_0. Qed.

Lemma K_173 : entry_ok (58, 3, 1, 0, 3, 14).
Proof. apply ok3. exact E_0101111011_3_1. Qed.

Lemma K_174 : entry_ok (58, 3, 2, 10, 3, 4).
Proof. apply ok3. exact E_0101111011_3_2. Qed.

Lemma K_175 : entry_ok (59, 3, 0, 40, 2, 3).
Proof. apply ok3. exact E_0101111111_3_0. Qed.

Lemma K_176 : entry_ok (59, 3, 1, 0, 2, 20).
Proof. apply ok3. exact E_0101111111_3_1. Qed.

Lemma K_177 : entry_ok (60, 3, 0, 27, 2, 4).
Proof. apply ok3. exact E_0110101111_3_0. Qed.

Lemma K_178 : entry_ok (60, 3, 1, 19, 2, 6).
Proof. apply ok3. exact E_0110101111_3_1. Qed.

Lemma K_179 : entry_ok (60, 3, 2, 41, 2, 4).
Proof. apply ok3. exact E_0110101111_3_2. Qed.

Lemma K_180 : entry_ok (61, 3, 0, 6, 2, 8).
Proof. apply ok3. exact E_0111111011_3_0. Qed.

Lemma K_181 : entry_ok (61, 3, 1, 0, 2, 14).
Proof. apply ok3. exact E_0111111011_3_1. Qed.

Lemma K_182 : entry_ok (61, 3, 2, 45, 2, 4).
Proof. apply ok3. exact E_0111111011_3_2. Qed.

Lemma K_183 : entry_ok (62, 3, 0, 0, 2, 11).
Proof. apply ok3. exact E_0111111111_3_0. Qed.

Lemma K_184 : entry_ok (62, 3, 1, 6, 1, 17).
Proof. apply ok3. exact E_0111111111_3_1. Qed.

Lemma K_185 : entry_ok (62, 3, 2, 46, 2, 4).
Proof. apply ok3. exact E_0111111111_3_2. Qed.

Lemma K_186 : entry_ok (63, 3, 1, 37, 2, 5).
Proof. apply ok3. exact E_00101011111_3_1. Qed.

Lemma K_187 : entry_ok (64, 3, 0, 42, 2, 3).
Proof. apply ok3. exact E_01010101010_3_0. Qed.

Lemma K_188 : entry_ok (64, 3, 1, 6, 1, 15).
Proof. apply ok3. exact E_01010101010_3_1. Qed.

Lemma K_189 : entry_ok (64, 3, 2, 98, 1, 4).
Proof. apply ok3. exact E_01010101010_3_2. Qed.

Lemma K_190 : entry_ok (65, 3, 0, 43, 2, 3).
Proof. apply ok3. exact E_01010101111_3_0. Qed.

Lemma K_191 : entry_ok (65, 3, 2, 53, 2, 4).
Proof. apply ok3. exact E_01010101111_3_2. Qed.

Lemma K_192 : entry_ok (66, 3, 0, 45, 2, 3).
Proof. apply ok3. exact E_01010111011_3_0. Qed.

Lemma K_193 : entry_ok (66, 3, 1, 0, 2, 14).
Proof. apply ok3. exact E_01010111011_3_1. Qed.

Lemma K_194 : entry_ok (66, 3, 2, 52, 2, 4).
Proof. apply ok3. exact E_01010111011_3_2. Qed.

Lemma K_195 : entry_ok (67, 3, 0, 46, 2, 3).
Proof. apply ok3. exact E_01010111111_3_0. Qed.

Lemma K_196 : entry_ok (67, 3, 1, 6, 1, 17).
Proof. apply ok3. exact E_01010111111_3_1. Qed.

Lemma K_197 : entry_ok (67, 3, 2, 54, 2, 4).
Proof. apply ok3. exact E_01010111111_3_2. Qed.

Lemma K_198 : entry_ok (68, 3, 0, 47, 2, 3).
Proof. apply ok3. exact E_01011010101_3_0. Qed.

Lemma K_199 : entry_ok (68, 3, 1, 70, 2, 8).
Proof. apply ok3. exact E_01011010101_3_1. Qed.

Lemma K_200 : entry_ok (68, 3, 2, 100, 2, 4).
Proof. apply ok3. exact E_01011010101_3_2. Qed.

Lemma K_201 : entry_ok (69, 3, 0, 48, 2, 3).
Proof. apply ok3. exact E_01011111011_3_0. Qed.

Lemma K_202 : entry_ok (69, 3, 1, 5, 3, 12).
Proof. apply ok3. exact E_01011111011_3_1. Qed.

Lemma K_203 : entry_ok (69, 3, 2, 55, 2, 4).
Proof. apply ok3. exact E_01011111011_3_2. Qed.

Lemma K_204 : entry_ok (70, 3, 0, 49, 2, 3).
Proof. apply ok3. exact E_01011111111_3_0. Qed.

Lemma K_205 : entry_ok (70, 3, 1, 0, 3, 16).
Proof. apply ok3. exact E_01011111111_3_1. Qed.

Lemma K_206 : entry_ok (70, 3, 2, 56, 2, 4).
Proof. apply ok3. exact E_01011111111_3_2. Qed.

Lemma K_207 : entry_ok (71, 3, 0, 6, 2, 9).
Proof. apply ok3. exact E_01111111011_3_0. Qed.

Lemma K_208 : entry_ok (71, 3, 1, 0, 3, 16).
Proof. apply ok3. exact E_01111111011_3_1. Qed.

Lemma K_209 : entry_ok (71, 3, 2, 58, 2, 4).
Proof. apply ok3. exact E_01111111011_3_2. Qed.

Lemma K_210 : entry_ok (72, 3, 1, 0, 2, 22).
Proof. apply ok3. exact E_01111111111_3_1. Qed.

Lemma K_211 : entry_ok (72, 3, 2, 59, 2, 4).
Proof. apply ok3. exact E_01111111111_3_2. Qed.

Lemma K_212 : entry_ok (73, 3, 2, 64, 2, 4).
Proof. apply ok3. exact E_001011111111_3_2. Qed.

Lemma K_213 : entry_ok (74, 3, 0, 51, 2, 3).
Proof. apply ok3. exact E_010101001111_3_0. Qed.

Lemma K_214 : entry_ok (74, 3, 1, 0, 2, 14).
Proof. apply ok3. exact E_010101001111_3_1. Qed.

Lemma K_215 : entry_ok (74, 3, 2, 70, 2, 4).
Proof. apply ok3. exact E_010101001111_3_2. Qed.

Lemma K_216 : entry_ok (75, 3, 0, 52, 2, 3).
Proof. apply ok3. exact E_010101010011_3_0. Qed.

Lemma K_217 : entry_ok (75, 3, 1, 0, 2, 14).
Proof. apply ok3. exact E_010101010011_3_1. Qed.

Lemma K_218 : entry_ok (75, 3, 2, 70, 2, 4).
Proof. apply ok3. exact E_010101010011_3_2. Qed.

Lemma K_219 : entry_ok (76, 3, 0, 54, 2, 3).
Proof. apply ok3. exact E_010101010111_3_0. Qed.

Lemma K_220 : entry_ok (76, 3, 1, 6, 1, 17).
Proof. apply ok3. exact E_010101010111_3_1. Qed.

Lemma K_221 : entry_ok (76, 3, 2, 64, 2, 4).
Proof. apply ok3. exact E_010101010111_3_2. Qed.

Lemma K_222 : entry_ok (77, 3, 0, 56, 2, 3).
Proof. apply ok3. exact E_010101011111_3_0. Qed.

Lemma K_223 : entry_ok (77, 3, 1, 0, 3, 16).
Proof. apply ok3. exact E_010101011111_3_1. Qed.

Lemma K_224 : entry_ok (78, 3, 0, 58, 2, 3).
Proof. apply ok3. exact E_010101111011_3_0. Qed.

Lemma K_225 : entry_ok (78, 3, 1, 0, 3, 16).
Proof. apply ok3. exact E_010101111011_3_1. Qed.

Lemma K_226 : entry_ok (78, 3, 2, 19, 3, 4).
Proof. apply ok3. exact E_010101111011_3_2. Qed.

Lemma K_227 : entry_ok (79, 3, 1, 0, 2, 22).
Proof. apply ok3. exact E_010101111111_3_1. Qed.

Lemma K_228 : entry_ok (79, 3, 2, 65, 2, 4).
Proof. apply ok3. exact E_010101111111_3_2. Qed.

Lemma K_229 : entry_ok (80, 3, 0, 60, 2, 3).
Proof. apply ok3. exact E_010110101111_3_0. Qed.

Lemma K_230 : entry_ok (80, 3, 1, 19, 2, 8).
Proof. apply ok3. exact E_010110101111_3_1. Qed.

Lemma K_231 : entry_ok (80, 3, 2, 68, 2, 4).
Proof. apply ok3. exact E_010110101111_3_2. Qed.

Lemma K_232 : entry_ok (81, 3, 0, 61, 2, 3).
Proof. apply ok3. exact E_010111111011_3_0. Qed.

Lemma K_233 : entry_ok (81, 3, 1, 0, 2, 16).
Proof. apply ok3. exact E_010111111011_3_1. Qed.

Lemma K_234 : entry_ok (81, 3, 2, 66, 2, 4).
Proof. apply ok3. exact E_010111111011_3_2. Qed.

Lemma K_235 : entry_ok (82, 3, 0, 62, 2, 3).
Proof. apply ok3. exact E_010111111111_3_0. Qed.

Lemma K_236 : entry_ok (82, 3, 1, 6, 1, 19).
Proof. apply ok3. exact E_010111111111_3_1. Qed.

Lemma K_237 : entry_ok (82, 3, 2, 67, 2, 4).
Proof. apply ok3. exact E_010111111111_3_2. Qed.

Lemma K_238 : entry_ok (83, 3, 0, 63, 2, 3).
Proof. apply ok3. exact E_0100101011111_3_0. Qed.

Lemma K_239 : entry_ok (84, 3, 0, 66, 2, 3).
Proof. apply ok3. exact E_0101010111011_3_0. Qed.

Lemma K_240 : entry_ok (84, 3, 1, 0, 2, 16).
Proof. apply ok3. exact E_0101010111011_3_1. Qed.

Lemma K_241 : entry_ok (84, 3, 2, 75, 2, 4).
Proof. apply ok3. exact E_0101010111011_3_2. Qed.

Lemma K_242 : entry_ok (85, 3, 0, 67, 2, 3).
Proof. apply ok3. exact E_0101010111111_3_0. Qed.

Lemma K_243 : entry_ok (85, 3, 1, 6, 1, 19).
Proof. apply ok3. exact E_0101010111111_3_1. Qed.

Lemma K_244 : entry_ok (85, 3, 2, 76, 2, 4).
Proof. apply ok3. exact E_0101010111111_3_2. Qed.

Lemma K_245 : entry_ok (86, 3, 0, 70, 2, 3).
Proof. apply ok3. exact E_0101011111111_3_0. Qed.

Lemma K_246 : entry_ok (86, 3, 1, 0, 3, 18).
Proof. apply ok3. exact E_0101011111111_3_1. Qed.

Lemma K_247 : entry_ok (86, 3, 2, 77, 2, 4).
Proof. apply ok3. exact E_0101011111111_3_2. Qed.

Lemma K_248 : entry_ok (87, 3, 0, 71, 2, 3).
Proof. apply ok3. exact E_0101111111011_3_0. Qed.

Lemma K_249 : entry_ok (87, 3, 1, 0, 3, 18).
Proof. apply ok3. exact E_0101111111011_3_1. Qed.

Lemma K_250 : entry_ok (87, 3, 2, 78, 2, 4).
Proof. apply ok3. exact E_0101111111011_3_2. Qed.

Lemma K_251 : entry_ok (88, 3, 0, 72, 2, 3).
Proof. apply ok3. exact E_0101111111111_3_0. Qed.

Lemma K_252 : entry_ok (88, 3, 1, 0, 2, 24).
Proof. apply ok3. exact E_0101111111111_3_1. Qed.

Lemma K_253 : entry_ok (88, 3, 2, 79, 2, 4).
Proof. apply ok3. exact E_0101111111111_3_2. Qed.

Lemma K_254 : entry_ok (89, 3, 0, 56, 2, 4).
Proof. apply ok3. exact E_0110101011111_3_0. Qed.

Lemma K_255 : entry_ok (89, 3, 1, 10, 3, 6).
Proof. apply ok3. exact E_0110101011111_3_1. Qed.

Lemma K_256 : entry_ok (90, 3, 0, 6, 2, 11).
Proof. apply ok3. exact E_0111111111011_3_0. Qed.

Lemma K_257 : entry_ok (90, 3, 1, 0, 2, 18).
Proof. apply ok3. exact E_0111111111011_3_1. Qed.

Lemma K_258 : entry_ok (90, 3, 2, 81, 2, 4).
Proof. apply ok3. exact E_0111111111011_3_2. Qed.

Lemma K_259 : entry_ok (91, 3, 0, 0, 2, 14).
Proof. apply ok3. exact E_0111111111111_3_0. Qed.

Lemma K_260 : entry_ok (91, 3, 1, 6, 1, 21).
Proof. apply ok3. exact E_0111111111111_3_1. Qed.

Lemma K_261 : entry_ok (91, 3, 2, 82, 2, 4).
Proof. apply ok3. exact E_0111111111111_3_2. Qed.

Lemma K_262 : entry_ok (92, 3, 0, 73, 2, 3).
Proof. apply ok3. exact E_01001011111111_3_0. Qed.

Lemma K_263 : entry_ok (92, 3, 1, 49, 2, 7).
Proof. apply ok3. exact E_01001011111111_3_1. Qed.

Lemma K_264 : entry_ok (92, 3, 2, 86, 2, 4).
Proof. apply ok3. exact E_01001011111111_3_2. Qed.

Lemma K_265 : entry_ok (93, 3, 0, 81, 2, 3).
Proof. apply ok3. exact E_01010111111011_3_0. Qed.

Lemma K_266 : entry_ok (93, 3, 1, 0, 2, 18).
Proof. apply ok3. exact E_01010111111011_3_1. Qed.

Lemma K_267 : entry_ok (93, 3, 2, 84, 2, 4).
Proof. apply ok3. exact E_01010111111011_3_2. Qed.

Lemma K_268 : entry_ok (94, 3, 0, 82, 2, 3).
Proof. apply ok3. exact E_01010111111111_3_0. Qed.

Lemma K_269 : entry_ok (94, 3, 1, 6, 1, 21).
Proof. apply ok3. exact E_01010111111111_3_1. Qed.

Lemma K_270 : entry_ok (94, 3, 2, 85, 2, 4).
Proof. apply ok3. exact E_01010111111111_3_2. Qed.

Lemma K_271 : entry_ok (95, 3, 1, 34, 2, 8).
Proof. apply ok3. exact E_01011010111111_3_1. Qed.

Lemma K_272 : entry_ok (96, 3, 0, 70, 2, 4).
Proof. apply ok3. exact E_01101011111111_3_0. Qed.

Lemma K_273 : entry_ok (96, 3, 1, 56, 2, 6).
Proof. apply ok3. exact E_01101011111111_3_1. Qed.

Lemma K_274 : entry_ok (96, 3, 2, 83, 2, 4).
Proof. apply ok3. exact E_01101011111111_3_2. Qed.

Lemma K_275 : entry_ok (97, 3, 0, 89, 2, 3).
Proof. apply ok3. exact E_010110101011111_3_0. Qed.

Lemma K_276 : entry_ok (97, 3, 1, 10, 3, 8).
Proof. apply ok3. exact E_010110101011111_3_1. Qed.

Lemma K_277 : entry_ok (97, 3, 2, 44, 3, 4).
Proof. apply ok3. exact E_010110101011111_3_2. Qed.

Lemma K_278 : entry_ok (98, 3, 0, 90, 2, 3).
Proof. apply ok3. exact E_010111111111011_3_0. Qed.

Lemma K_279 : entry_ok (98, 3, 1, 0, 2, 20).
Proof. apply ok3. exact E_010111111111011_3_1. Qed.

Lemma K_280 : entry_ok (98, 3, 2, 93, 2, 4).
Proof. apply ok3. exact E_010111111111011_3_2. Qed.

Lemma K_281 : entry_ok (99, 3, 0, 91, 2, 3).
Proof. apply ok3. exact E_010111111111111_3_0. Qed.

Lemma K_282 : entry_ok (99, 3, 1, 6, 1, 23).
Proof. apply ok3. exact E_010111111111111_3_1. Qed.

Lemma K_283 : entry_ok (99, 3, 2, 94, 2, 4).
Proof. apply ok3. exact E_010111111111111_3_2. Qed.

Lemma K_284 : entry_ok (100, 3, 0, 96, 2, 3).
Proof. apply ok3. exact E_0101101011111111_3_0. Qed.

Lemma K_285 : entry_ok (100, 3, 1, 56, 2, 8).
Proof. apply ok3. exact E_0101101011111111_3_1. Qed.

Lemma K_286 : entry_ok (100, 3, 2, 97, 2, 4).
Proof. apply ok3. exact E_0101101011111111_3_2. Qed.

Lemma entries_ok : Forall entry_ok entries.
Proof.
  unfold entries.
  apply Forall_cons; [exact K_0|].
  apply Forall_cons; [exact K_1|].
  apply Forall_cons; [exact K_2|].
  apply Forall_cons; [exact K_3|].
  apply Forall_cons; [exact K_4|].
  apply Forall_cons; [exact K_5|].
  apply Forall_cons; [exact K_6|].
  apply Forall_cons; [exact K_7|].
  apply Forall_cons; [exact K_8|].
  apply Forall_cons; [exact K_9|].
  apply Forall_cons; [exact K_10|].
  apply Forall_cons; [exact K_11|].
  apply Forall_cons; [exact K_12|].
  apply Forall_cons; [exact K_13|].
  apply Forall_cons; [exact K_14|].
  apply Forall_cons; [exact K_15|].
  apply Forall_cons; [exact K_16|].
  apply Forall_cons; [exact K_17|].
  apply Forall_cons; [exact K_18|].
  apply Forall_cons; [exact K_19|].
  apply Forall_cons; [exact K_20|].
  apply Forall_cons; [exact K_21|].
  apply Forall_cons; [exact K_22|].
  apply Forall_cons; [exact K_23|].
  apply Forall_cons; [exact K_24|].
  apply Forall_cons; [exact K_25|].
  apply Forall_cons; [exact K_26|].
  apply Forall_cons; [exact K_27|].
  apply Forall_cons; [exact K_28|].
  apply Forall_cons; [exact K_29|].
  apply Forall_cons; [exact K_30|].
  apply Forall_cons; [exact K_31|].
  apply Forall_cons; [exact K_32|].
  apply Forall_cons; [exact K_33|].
  apply Forall_cons; [exact K_34|].
  apply Forall_cons; [exact K_35|].
  apply Forall_cons; [exact K_36|].
  apply Forall_cons; [exact K_37|].
  apply Forall_cons; [exact K_38|].
  apply Forall_cons; [exact K_39|].
  apply Forall_cons; [exact K_40|].
  apply Forall_cons; [exact K_41|].
  apply Forall_cons; [exact K_42|].
  apply Forall_cons; [exact K_43|].
  apply Forall_cons; [exact K_44|].
  apply Forall_cons; [exact K_45|].
  apply Forall_cons; [exact K_46|].
  apply Forall_cons; [exact K_47|].
  apply Forall_cons; [exact K_48|].
  apply Forall_cons; [exact K_49|].
  apply Forall_cons; [exact K_50|].
  apply Forall_cons; [exact K_51|].
  apply Forall_cons; [exact K_52|].
  apply Forall_cons; [exact K_53|].
  apply Forall_cons; [exact K_54|].
  apply Forall_cons; [exact K_55|].
  apply Forall_cons; [exact K_56|].
  apply Forall_cons; [exact K_57|].
  apply Forall_cons; [exact K_58|].
  apply Forall_cons; [exact K_59|].
  apply Forall_cons; [exact K_60|].
  apply Forall_cons; [exact K_61|].
  apply Forall_cons; [exact K_62|].
  apply Forall_cons; [exact K_63|].
  apply Forall_cons; [exact K_64|].
  apply Forall_cons; [exact K_65|].
  apply Forall_cons; [exact K_66|].
  apply Forall_cons; [exact K_67|].
  apply Forall_cons; [exact K_68|].
  apply Forall_cons; [exact K_69|].
  apply Forall_cons; [exact K_70|].
  apply Forall_cons; [exact K_71|].
  apply Forall_cons; [exact K_72|].
  apply Forall_cons; [exact K_73|].
  apply Forall_cons; [exact K_74|].
  apply Forall_cons; [exact K_75|].
  apply Forall_cons; [exact K_76|].
  apply Forall_cons; [exact K_77|].
  apply Forall_cons; [exact K_78|].
  apply Forall_cons; [exact K_79|].
  apply Forall_cons; [exact K_80|].
  apply Forall_cons; [exact K_81|].
  apply Forall_cons; [exact K_82|].
  apply Forall_cons; [exact K_83|].
  apply Forall_cons; [exact K_84|].
  apply Forall_cons; [exact K_85|].
  apply Forall_cons; [exact K_86|].
  apply Forall_cons; [exact K_87|].
  apply Forall_cons; [exact K_88|].
  apply Forall_cons; [exact K_89|].
  apply Forall_cons; [exact K_90|].
  apply Forall_cons; [exact K_91|].
  apply Forall_cons; [exact K_92|].
  apply Forall_cons; [exact K_93|].
  apply Forall_cons; [exact K_94|].
  apply Forall_cons; [exact K_95|].
  apply Forall_cons; [exact K_96|].
  apply Forall_cons; [exact K_97|].
  apply Forall_cons; [exact K_98|].
  apply Forall_cons; [exact K_99|].
  apply Forall_cons; [exact K_100|].
  apply Forall_cons; [exact K_101|].
  apply Forall_cons; [exact K_102|].
  apply Forall_cons; [exact K_103|].
  apply Forall_cons; [exact K_104|].
  apply Forall_cons; [exact K_105|].
  apply Forall_cons; [exact K_106|].
  apply Forall_cons; [exact K_107|].
  apply Forall_cons; [exact K_108|].
  apply Forall_cons; [exact K_109|].
  apply Forall_cons; [exact K_110|].
  apply Forall_cons; [exact K_111|].
  apply Forall_cons; [exact K_112|].
  apply Forall_cons; [exact K_113|].
  apply Forall_cons; [exact K_114|].
  apply Forall_cons; [exact K_115|].
  apply Forall_cons; [exact K_116|].
  apply Forall_cons; [exact K_117|].
  apply Forall_cons; [exact K_118|].
  apply Forall_cons; [exact K_119|].
  apply Forall_cons; [exact K_120|].
  apply Forall_cons; [exact K_121|].
  apply Forall_cons; [exact K_122|].
  apply Forall_cons; [exact K_123|].
  apply Forall_cons; [exact K_124|].
  apply Forall_cons; [exact K_125|].
  apply Forall_cons; [exact K_126|].
  apply Forall_cons; [exact K_127|].
  apply Forall_cons; [exact K_128|].
  apply Forall_cons; [exact K_129|].
  apply Forall_cons; [exact K_130|].
  apply Forall_cons; [exact K_131|].
  apply Forall_cons; [exact K_132|].
  apply Forall_cons; [exact K_133|].
  apply Forall_cons; [exact K_134|].
  apply Forall_cons; [exact K_135|].
  apply Forall_cons; [exact K_136|].
  apply Forall_cons; [exact K_137|].
  apply Forall_cons; [exact K_138|].
  apply Forall_cons; [exact K_139|].
  apply Forall_cons; [exact K_140|].
  apply Forall_cons; [exact K_141|].
  apply Forall_cons; [exact K_142|].
  apply Forall_cons; [exact K_143|].
  apply Forall_cons; [exact K_144|].
  apply Forall_cons; [exact K_145|].
  apply Forall_cons; [exact K_146|].
  apply Forall_cons; [exact K_147|].
  apply Forall_cons; [exact K_148|].
  apply Forall_cons; [exact K_149|].
  apply Forall_cons; [exact K_150|].
  apply Forall_cons; [exact K_151|].
  apply Forall_cons; [exact K_152|].
  apply Forall_cons; [exact K_153|].
  apply Forall_cons; [exact K_154|].
  apply Forall_cons; [exact K_155|].
  apply Forall_cons; [exact K_156|].
  apply Forall_cons; [exact K_157|].
  apply Forall_cons; [exact K_158|].
  apply Forall_cons; [exact K_159|].
  apply Forall_cons; [exact K_160|].
  apply Forall_cons; [exact K_161|].
  apply Forall_cons; [exact K_162|].
  apply Forall_cons; [exact K_163|].
  apply Forall_cons; [exact K_164|].
  apply Forall_cons; [exact K_165|].
  apply Forall_cons; [exact K_166|].
  apply Forall_cons; [exact K_167|].
  apply Forall_cons; [exact K_168|].
  apply Forall_cons; [exact K_169|].
  apply Forall_cons; [exact K_170|].
  apply Forall_cons; [exact K_171|].
  apply Forall_cons; [exact K_172|].
  apply Forall_cons; [exact K_173|].
  apply Forall_cons; [exact K_174|].
  apply Forall_cons; [exact K_175|].
  apply Forall_cons; [exact K_176|].
  apply Forall_cons; [exact K_177|].
  apply Forall_cons; [exact K_178|].
  apply Forall_cons; [exact K_179|].
  apply Forall_cons; [exact K_180|].
  apply Forall_cons; [exact K_181|].
  apply Forall_cons; [exact K_182|].
  apply Forall_cons; [exact K_183|].
  apply Forall_cons; [exact K_184|].
  apply Forall_cons; [exact K_185|].
  apply Forall_cons; [exact K_186|].
  apply Forall_cons; [exact K_187|].
  apply Forall_cons; [exact K_188|].
  apply Forall_cons; [exact K_189|].
  apply Forall_cons; [exact K_190|].
  apply Forall_cons; [exact K_191|].
  apply Forall_cons; [exact K_192|].
  apply Forall_cons; [exact K_193|].
  apply Forall_cons; [exact K_194|].
  apply Forall_cons; [exact K_195|].
  apply Forall_cons; [exact K_196|].
  apply Forall_cons; [exact K_197|].
  apply Forall_cons; [exact K_198|].
  apply Forall_cons; [exact K_199|].
  apply Forall_cons; [exact K_200|].
  apply Forall_cons; [exact K_201|].
  apply Forall_cons; [exact K_202|].
  apply Forall_cons; [exact K_203|].
  apply Forall_cons; [exact K_204|].
  apply Forall_cons; [exact K_205|].
  apply Forall_cons; [exact K_206|].
  apply Forall_cons; [exact K_207|].
  apply Forall_cons; [exact K_208|].
  apply Forall_cons; [exact K_209|].
  apply Forall_cons; [exact K_210|].
  apply Forall_cons; [exact K_211|].
  apply Forall_cons; [exact K_212|].
  apply Forall_cons; [exact K_213|].
  apply Forall_cons; [exact K_214|].
  apply Forall_cons; [exact K_215|].
  apply Forall_cons; [exact K_216|].
  apply Forall_cons; [exact K_217|].
  apply Forall_cons; [exact K_218|].
  apply Forall_cons; [exact K_219|].
  apply Forall_cons; [exact K_220|].
  apply Forall_cons; [exact K_221|].
  apply Forall_cons; [exact K_222|].
  apply Forall_cons; [exact K_223|].
  apply Forall_cons; [exact K_224|].
  apply Forall_cons; [exact K_225|].
  apply Forall_cons; [exact K_226|].
  apply Forall_cons; [exact K_227|].
  apply Forall_cons; [exact K_228|].
  apply Forall_cons; [exact K_229|].
  apply Forall_cons; [exact K_230|].
  apply Forall_cons; [exact K_231|].
  apply Forall_cons; [exact K_232|].
  apply Forall_cons; [exact K_233|].
  apply Forall_cons; [exact K_234|].
  apply Forall_cons; [exact K_235|].
  apply Forall_cons; [exact K_236|].
  apply Forall_cons; [exact K_237|].
  apply Forall_cons; [exact K_238|].
  apply Forall_cons; [exact K_239|].
  apply Forall_cons; [exact K_240|].
  apply Forall_cons; [exact K_241|].
  apply Forall_cons; [exact K_242|].
  apply Forall_cons; [exact K_243|].
  apply Forall_cons; [exact K_244|].
  apply Forall_cons; [exact K_245|].
  apply Forall_cons; [exact K_246|].
  apply Forall_cons; [exact K_247|].
  apply Forall_cons; [exact K_248|].
  apply Forall_cons; [exact K_249|].
  apply Forall_cons; [exact K_250|].
  apply Forall_cons; [exact K_251|].
  apply Forall_cons; [exact K_252|].
  apply Forall_cons; [exact K_253|].
  apply Forall_cons; [exact K_254|].
  apply Forall_cons; [exact K_255|].
  apply Forall_cons; [exact K_256|].
  apply Forall_cons; [exact K_257|].
  apply Forall_cons; [exact K_258|].
  apply Forall_cons; [exact K_259|].
  apply Forall_cons; [exact K_260|].
  apply Forall_cons; [exact K_261|].
  apply Forall_cons; [exact K_262|].
  apply Forall_cons; [exact K_263|].
  apply Forall_cons; [exact K_264|].
  apply Forall_cons; [exact K_265|].
  apply Forall_cons; [exact K_266|].
  apply Forall_cons; [exact K_267|].
  apply Forall_cons; [exact K_268|].
  apply Forall_cons; [exact K_269|].
  apply Forall_cons; [exact K_270|].
  apply Forall_cons; [exact K_271|].
  apply Forall_cons; [exact K_272|].
  apply Forall_cons; [exact K_273|].
  apply Forall_cons; [exact K_274|].
  apply Forall_cons; [exact K_275|].
  apply Forall_cons; [exact K_276|].
  apply Forall_cons; [exact K_277|].
  apply Forall_cons; [exact K_278|].
  apply Forall_cons; [exact K_279|].
  apply Forall_cons; [exact K_280|].
  apply Forall_cons; [exact K_281|].
  apply Forall_cons; [exact K_282|].
  apply Forall_cons; [exact K_283|].
  apply Forall_cons; [exact K_284|].
  apply Forall_cons; [exact K_285|].
  apply Forall_cons; [exact K_286|].
  apply Forall_nil.
Qed.



Lemma bell_step w mc r w' dmp e q m :
  tbl w mc r = Some (w', dmp, e) -> Nat.min m 3 = mc ->
  Bl (q*3+r) w m -->* Bl (q*4+e) w' (m+dmp-2).
Proof.
  intros H Hm.
  pose proof entries_ok as A. rewrite Forall_forall in A.
  exact (A _ (tbl_in _ _ _ _ _ _ H) q m Hm).
Qed.

(* ---------- shift-invariant jumps ---------- *)

(* j Bell steps from (a, w, m) to (a', w', m'), uniformly in k *)
Definition Jn (j a w m a' w' m' : nat) : Prop :=
  forall k, Bl (a + k * 3^j) w m -->* Bl (a' + k * 4^j) w' m'.

Lemma Jn_refl a w m : Jn 0 a w m a w m.
Proof. intro k. cbn. apply evstep_refl. Qed.

Lemma Jn_step a w m w' dmp e :
  tbl w (Nat.min m 3) (a mod 3) = Some (w', dmp, e) ->
  Jn 1 a w m (a / 3 * 4 + e) w' (m + dmp - 2).
Proof.
  intros H k.
  replace (a + k * 3^1) with ((a / 3 + k) * 3 + a mod 3)
    by (rewrite Nat.pow_1_r; pose proof (Nat.div_mod_eq a 3); lia).
  replace (a / 3 * 4 + e + k * 4^1) with ((a / 3 + k) * 4 + e) by (rewrite Nat.pow_1_r; lia).
  exact (bell_step _ _ _ _ _ _ _ _ H eq_refl).
Qed.

Lemma Jn_trans i j a w m a1 w1 m1 a2 w2 m2 :
  Jn i a w m a1 w1 m1 -> Jn j a1 w1 m1 a2 w2 m2 -> Jn (i + j) a w m a2 w2 m2.
Proof.
  intros H1 H2 k.
  rewrite !Nat.pow_add_r.
  replace (a + k * (3^i * 3^j)) with (a + (k * 3^j) * 3^i) by ring.
  eapply evstep_trans. { apply H1. }
  replace (a1 + k * 3^j * 4^i) with (a1 + (k * 4^i) * 3^j) by ring.
  replace (a2 + k * (4^i * 4^j)) with (a2 + (k * 4^i) * 4^j) by ring.
  apply H2.
Qed.

Lemma Jn_shift j q a w m a' w' m' :
  Jn j a w m a' w' m' -> Jn j (q * 3^j + a) w m (q * 4^j + a') w' m'.
Proof.
  intros H k.
  replace (q * 3^j + a + k * 3^j) with (a + (q + k) * 3^j) by ring.
  replace (q * 4^j + a' + k * 4^j) with (a' + (q + k) * 4^j) by ring.
  apply H.
Qed.

(* the D&C step: split a = q 3^(2j) + r, two jumps of j on the remainder, recombine *)
Lemma Jn_split j q r w m r1 w1 m1 r2 w2 m2 :
  Jn j r w m r1 w1 m1 -> Jn j r1 w1 m1 r2 w2 m2 ->
  Jn (2 * j) (q * 3^(2*j) + r) w m (q * 4^(2*j) + r2) w2 m2.
Proof.
  intros H1 H2. apply Jn_shift.
  replace (2 * j) with (j + j) by lia.
  exact (Jn_trans _ _ _ _ _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma Jn_run j a w m a' w' m' :
  Jn j a w m a' w' m' -> Bl a w m -->* Bl a' w' m'.
Proof. intro H. specialize (H 0). rewrite !Nat.mul_0_l, !Nat.add_0_r in H. exact H. Qed.

(* ---------- the two ends ---------- *)

Lemma start : c0 -->* Bl 4 w_empty 1.
Proof. unfold Bl, word, P, B. cbn. es. Qed.

Lemma halt_end q m : halts tm (Bl (q*3+2) w_halt (3+m)).
Proof.
  unfold Bl.
  eapply halts_evstep. 2: apply (Passes q 1 2).
  exact (E_00_3_2 q m).
Qed.

End Spec.

From Coq Require Import ZArith NArith Arith PeanoNat Lia Bool Lists.List.
Module Main.
Import BigArith.
(* The certified iteration: a divide-and-conquer over Bell steps on big integers, proved to compose
   the table lemmas of Spec, and the final halting theorem. *)
Import ListNotations.
Import TM1 Spec.

Local Open Scope nat_scope.

Definition c4i : Uint63.int := Uint63.of_Z 4.
Definition c64i : Uint63.int := Uint63.of_Z 64.
Definition two61 : Uint63.int := Uint63.of_Z (2 ^ 61).
(* 3 * inv3 = 1 + 2^63: exact division of a multiple of 3 by one multiplication *)
Definition inv3 : Uint63.int := Uint63.of_Z 3074457345618258603.

(* ===================== per-level data ===================== *)

(* lp = 3^(2^d) (verified); the rest only steers the untrusted quotient *)
Record lvl := Lvl { lp : bigint; lP : Uint63.int; lA : Uint63.int; lR : bigint }.

Definition Amax : Uint63.int := Uint63.of_Z 130000000.
Definition pow2i (d : nat) : Uint63.int := Uint63.lsl c1i (n2i d).

Definition mkA (Pb : Uint63.int) (d : nat) : Uint63.int :=
  let a := Uint63.add Pb (pow2i (S d)) in
  Uint63.add (if Uint63.ltb a Amax then a else Amax) c64i.

Definition lvl_first (p : bigint) (d : nat) : lvl :=
  let Pb := ubits p in
  let Ab := mkA Pb d in
  Lvl p Pb Ab (bigint_of_N (N.div (N.shiftl 1 (Z.to_N (Uint63.to_Z Ab))) (bigint_to_N p))).

Definition lvl_next (prev : lvl) (p : bigint) (d : nat) : lvl :=
  let Pb := ubits p in
  let Ab := mkA Pb d in
  let Ap := lA prev in
  let x0 := shr (Uint63.sub (Uint63.add Ap Ap) Ab) (umul (lR prev) (lR prev)) in
  Lvl p Pb Ab (newton 2 p Ab x0).

Fixpoint levels_aux (k d : nat) (prev : lvl) (acc : list lvl) : option (list lvl) :=
  match k with
  | O => Some (rev_append acc [])
  | S k' =>
      match mulx (lp prev) (lp prev) with
      | Some p =>
          let lv := if Nat.leb d 6 then lvl_first p d else lvl_next prev p d in
          levels_aux k' (S d) lv (lv :: acc)
      | None => None
      end
  end.

Definition levels (Dn : nat) : option (list lvl) :=
  let l0 := lvl_first (of_u63 c3i) 0 in levels_aux Dn 1 l0 [l0].

(* ===================== machine-integer leaf ===================== *)

Definition mclass (m : N) : nat := if N.ltb m 3 then N.to_nat m else 3.

Fixpoint run_u63 (j : nat) (x : Uint63.int) (w : nat) (m : N) : option (Uint63.int * nat * N) :=
  match j with
  | O => Some (x, w, m)
  | S j' =>
      if Uint63.ltb x two61 then
        match tbl w (mclass m) (i2n (PrimInt63.mod x c3i)) with
        | Some (w', dmp, e) =>
            run_u63 j'
              (Uint63.add (Uint63.mul (Uint63.mul (Uint63.sub x (PrimInt63.mod x c3i)) inv3) c4i) (n2i e)) w'
              (m + N.of_nat dmp - 2)%N
        | None => None
        end
      else None
  end.

Definition leaf_big (j : nat) (a : bigint) (w : nat) (m : N) : option (bigint * nat * N) :=
  match to_u63 a with
  | Some x =>
      match run_u63 j x w m with
      | Some (x', w', m') => Some (of_u63 x', w', m')
      | None => None
      end
  | None => None
  end.

(* ===================== checked split and the D&C ===================== *)

(* a = q p + r, checked; any q is allowed, a wrong one only fails *)
Definition split_checked (po : option bigint) (q a : bigint) : option (bigint * bigint) :=
  match q with
  | [] => Some ([], a)
  | _ =>
      match po with
      | None => None
      | Some p =>
          if canonb q then
            match mulx q p with
            | Some qp =>
                let r := usub a qp in
                if andb (canonb r) (eqv (addb qp r) a) then Some (q, r) else None
            | None => None
            end
          else None
      end
  end.

(* lower bound for log2(3^(2^d)) *)
Definition Plo (d : nat) : Uint63.int :=
  Uint63.lsr (Uint63.mul (pow2i d) (Uint63.of_Z 103872)) (Uint63.of_Z 16).

Definition hint (Cl : list lvl) (d : nat) (a : bigint) : bigint :=
  if Uint63.leb (ubits a) (Plo d) then []
  else match nth_error Cl d with
       | Some lv => strip (udivq 64 (lp lv) (lR lv) (lP lv) (lA lv) a)
       | None => []
       end.

Definition pd (Cl : list lvl) (d : nat) : option bigint :=
  match nth_error Cl d with Some lv => Some (lp lv) | None => None end.

(* 2^d Bell steps *)
Fixpoint F (Cl : list lvl) (d : nat) (a : bigint) (w : nat) (m : N) {struct d}
    : option (bigint * nat * N) :=
  match d with
  | O => leaf_big 1 a w m
  | S d0 =>
      match (if Nat.leb d 4 then leaf_big (2 ^ d) a w m else None) with
      | Some res => Some res
      | None =>
          if Nat.leb d 3 then None else
          match split_checked (pd Cl d) (hint Cl d a) a with
          | None => None
          | Some (q, r) =>
              match F Cl d0 r w m with
              | None => None
              | Some (r1, w1, m1) =>
                  match F Cl d0 r1 w1 m1 with
                  | None => None
                  | Some (r2, w2, m2) => Some (addb (shl (pow2i (S d)) q) r2, w2, m2)
                  end
              end
          end
      end
  end.

(* n * 2^d Bell steps, binary schedule *)
Fixpoint F0 (Cl : list lvl) (a : bigint) (w : nat) (m : N) (n : positive) (d : nat)
    : option (bigint * nat * N) :=
  match n with
  | xH => F Cl d a w m
  | xI n' =>
      match F Cl d a w m with
      | Some (a', w', m') => F0 Cl a' w' m' n' (S d)
      | None => None
      end
  | xO n' => F0 Cl a w m n' (S d)
  end.

Definition check (Dn : nat) (n : positive) : bool :=
  match levels Dn with
  | Some Cl =>
      match F0 Cl (of_u63 c4i) w_empty 1%N n 0 with
      | Some (a, w, m) => andb (andb (Nat.eqb w w_halt) (N.leb 3 m)) (Uint63.eqb (mod3 a) c2i)
      | None => false
      end
  | None => false
  end.

(* ===================== proofs ===================== *)

Definition nat_of (x : bigint) : nat := Z.to_nat (val x).

Lemma nat_of_spec x : Z.of_nat (nat_of x) = val x.
Proof. unfold nat_of. rewrite Z2Nat.id; [reflexivity|apply bigint_value_nonneg]. Qed.

Lemma i2n_spec x : Z.of_nat (i2n x) = Uint63.to_Z x.
Proof. unfold i2n. rewrite Z2Nat.id; [reflexivity|apply Uint63.to_Z_bounded]. Qed.

Lemma nat_of_u63 x : nat_of (of_u63 x) = i2n x.
Proof. apply Nat2Z.inj. rewrite nat_of_spec, i2n_spec. apply of_u63_ok. Qed.

Lemma nat_of_to_u63 a x : can a -> to_u63 a = Some x -> nat_of a = i2n x.
Proof. intros Ha H. apply Nat2Z.inj. rewrite nat_of_spec, i2n_spec. exact (to_u63_ok a x Ha H). Qed.

(* ---------- table facts ---------- *)

Definition e_small : bool :=
  forallb (fun x => let '(_, _, _, _, _, e) := x in Nat.ltb e 1000) entries.

Lemma e_small_true : e_small = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tbl_e w mc r w' dmp e : tbl w mc r = Some (w', dmp, e) -> e < 1000.
Proof.
  intro H. apply tbl_in in H.
  pose proof e_small_true as C. unfold e_small in C. rewrite forallb_forall in C.
  specialize (C _ H). cbn in C. apply Nat.ltb_lt, C.
Qed.

Lemma mclass_ok m : mclass m = Nat.min (N.to_nat m) 3.
Proof. unfold mclass. destruct (N.ltb_spec m 3); lia. Qed.

Lemma i2n_mod3 x : i2n (PrimInt63.mod x c3i) = i2n x mod 3.
Proof.
  apply Nat2Z.inj. rewrite i2n_spec, Nat2Z.inj_mod, i2n_spec, Uint63.mod_spec. reflexivity.
Qed.

Lemma run_next x e :
  Uint63.ltb x two61 = true -> e < 1000 ->
  i2n (Uint63.add (Uint63.mul (Uint63.mul (Uint63.sub x (PrimInt63.mod x c3i)) inv3) c4i) (n2i e)) =
  i2n x / 3 * 4 + e.
Proof.
  intros Hx He. apply Uint63.ltb_spec in Hx. change (Uint63.to_Z two61) with 2305843009213693952%Z in Hx.
  pose proof (Uint63.to_Z_bounded x) as Hb. change Uint63.wB with 9223372036854775808%Z in Hb.
  assert (Hn : Uint63.to_Z (n2i e) = Z.of_nat e).
  { unfold n2i. rewrite Uint63.of_Z_spec, Z.mod_small; [reflexivity|].
    change Uint63.wB with 9223372036854775808%Z. lia. }
  assert (Hr : Uint63.to_Z (PrimInt63.mod x c3i) = (Uint63.to_Z x mod 3)%Z)
    by (rewrite Uint63.mod_spec; reflexivity).
  pose proof (Z.div_mod (Uint63.to_Z x) 3 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (Uint63.to_Z x) 3 ltac:(lia)) as R.
  assert (Hq : (0 <= Uint63.to_Z x / 3)%Z) by (apply Z.div_pos; lia).
  assert (Hs : Uint63.to_Z (Uint63.sub x (PrimInt63.mod x c3i)) = (3 * (Uint63.to_Z x / 3))%Z).
  { rewrite Uint63.sub_spec, Hr. change Uint63.wB with 9223372036854775808%Z.
    rewrite Z.mod_small by lia. lia. }
  assert (Hm : Uint63.to_Z (Uint63.mul (Uint63.sub x (PrimInt63.mod x c3i)) inv3) =
               (Uint63.to_Z x / 3)%Z).
  { rewrite Uint63.mul_spec, Hs. change (Uint63.to_Z inv3) with 3074457345618258603%Z.
    change Uint63.wB with 9223372036854775808%Z.
    replace (3 * (Uint63.to_Z x / 3) * 3074457345618258603)%Z
      with (Uint63.to_Z x / 3 + (Uint63.to_Z x / 3) * 9223372036854775808)%Z by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  apply Nat2Z.inj. rewrite i2n_spec, Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_div, i2n_spec.
  rewrite Uint63.add_spec, Uint63.mul_spec, Hn, Hm. change (Uint63.to_Z c4i) with 4%Z.
  change Uint63.wB with 9223372036854775808%Z.
  rewrite (Z.mod_small (_ * 4)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma N_step m dmp : N.to_nat (m + N.of_nat dmp - 2) = N.to_nat m + dmp - 2.
Proof. lia. Qed.

(* ---------- leaves ---------- *)

Lemma run_u63_ok j : forall x w m x' w' m',
  run_u63 j x w m = Some (x', w', m') ->
  Jn j (i2n x) w (N.to_nat m) (i2n x') w' (N.to_nat m').
Proof.
  induction j as [|j IH]; intros x w m x' w' m' H; cbn [run_u63] in H.
  - injection H as <- <- <-. apply Jn_refl.
  - destruct (Uint63.ltb x two61) eqn:Hx; [|discriminate].
    destruct (tbl w (mclass m) (i2n (PrimInt63.mod x c3i))) as [[[w1 dmp] e]|] eqn:Ht; [|discriminate].
    apply IH in H.
    rewrite mclass_ok, i2n_mod3 in Ht.
    pose proof (tbl_e _ _ _ _ _ _ Ht) as He.
    pose proof (Jn_step _ _ _ _ _ _ Ht) as J1.
    rewrite (run_next x e Hx He), N_step in H.
    change (S j) with (1 + j). apply (Jn_trans 1 j _ _ _ _ _ _ _ _ _ J1). exact H.
Qed.

Lemma leaf_big_ok j a w m a' w' m' :
  can a -> leaf_big j a w m = Some (a', w', m') ->
  can a' /\ Jn j (nat_of a) w (N.to_nat m) (nat_of a') w' (N.to_nat m').
Proof.
  intros Ha H. unfold leaf_big in H.
  destruct (to_u63 a) as [x|] eqn:Ex; [|discriminate].
  destruct (run_u63 j x w m) as [[[x' w1] m1]|] eqn:Er; [|discriminate].
  injection H as <- <- <-.
  split; [apply of_u63_ok|].
  rewrite (nat_of_to_u63 a x Ha Ex), nat_of_u63.
  exact (run_u63_ok _ _ _ _ _ _ _ Er).
Qed.

(* ---------- levels ---------- *)

Definition lvl_ok (i : nat) (lv : lvl) : Prop :=
  can (lp lv) /\ val (lp lv) = Z.of_nat (3 ^ 2 ^ i).

Definition Cl_ok (Cl : list lvl) : Prop :=
  forall i lv, nth_error Cl i = Some lv -> lvl_ok i lv.

Lemma pow_sq d : 3 ^ 2 ^ d * 3 ^ 2 ^ d = 3 ^ 2 ^ S d.
Proof. rewrite <- Nat.pow_add_r. f_equal. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma Cl_ok_snoc acc lv : Cl_ok (rev acc) -> lvl_ok (length acc) lv -> Cl_ok (rev (lv :: acc)).
Proof.
  intros Hacc Hlv i lw Hi. cbn [rev] in Hi.
  destruct (Nat.lt_ge_cases i (length acc)) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hi by (rewrite length_rev; lia). exact (Hacc i lw Hi).
  - rewrite nth_error_app2 in Hi by (rewrite length_rev; lia).
    rewrite length_rev in Hi.
    destruct (i - length acc) as [|t] eqn:Et.
    + cbn [nth_error] in Hi. injection Hi as <-. replace i with (length acc) by lia. exact Hlv.
    + destruct t; cbn [nth_error] in Hi; discriminate.
Qed.

Lemma lp_choice d p prev : lp (if Nat.leb d 6 then lvl_first p d else lvl_next prev p d) = p.
Proof. destruct (Nat.leb d 6); reflexivity. Qed.

Lemma levels_aux_ok k : forall d prev acc Cl,
  length acc = S d -> lvl_ok d prev -> Cl_ok (rev acc) ->
  levels_aux k (S d) prev acc = Some Cl -> Cl_ok Cl.
Proof.
  induction k as [|k IH]; intros d prev acc Cl Hlen Hprev Hacc H; cbn [levels_aux] in H.
  - injection H as <-. rewrite rev_append_rev, app_nil_r. exact Hacc.
  - destruct (mulx (lp prev) (lp prev)) as [p|] eqn:Em; [|discriminate].
    destruct Hprev as [Hc Hv].
    destruct (mulx_ok _ _ _ Hc Hc Em) as [Hp Vp].
    generalize (lp_choice (S d) p prev). revert H.
    generalize (if Nat.leb (S d) 6 then lvl_first p (S d) else lvl_next prev p (S d)) as lv.
    intros lv H Hlp.
    assert (Hlv : lvl_ok (S d) lv).
    { split; rewrite Hlp; [exact Hp|]. rewrite Vp, Hv, <- Nat2Z.inj_mul, pow_sq. reflexivity. }
    apply (IH (S d) lv (lv :: acc) Cl); [cbn [length]; rewrite Hlen; reflexivity|exact Hlv| |exact H].
    apply Cl_ok_snoc; [exact Hacc|]. rewrite Hlen. exact Hlv.
Qed.

Lemma levels_ok Dn Cl : levels Dn = Some Cl -> Cl_ok Cl.
Proof.
  unfold levels. apply levels_aux_ok; [reflexivity| |].
  - split; cbn [lp lvl_first]; apply of_u63_ok.
  - intros [|i] lv H; cbn in H; [injection H as <-|destruct i; discriminate].
    split; cbn [lp lvl_first]; apply of_u63_ok.
Qed.

Lemma pd_ok Cl d p : Cl_ok Cl -> pd Cl d = Some p -> can p /\ val p = Z.of_nat (3 ^ 2 ^ d).
Proof.
  unfold pd. intros HC H. destruct (nth_error Cl d) as [lv|] eqn:E; [|discriminate].
  injection H as <-. exact (HC d lv E).
Qed.

(* ---------- the split ---------- *)

Lemma split_checked_ok Cl d q0 a q r :
  Cl_ok Cl -> can a -> split_checked (pd Cl d) q0 a = Some (q, r) ->
  can q /\ can r /\ val a = (val q * Z.of_nat (3 ^ 2 ^ d) + val r)%Z.
Proof.
  intros HC Ha H. unfold split_checked in H. destruct q0 as [|b q0].
  { injection H as <- <-. split; [constructor|]. split; [exact Ha|]. cbn. lia. }
  destruct (pd Cl d) as [p|] eqn:Ep; [|discriminate].
  destruct (pd_ok Cl d p HC Ep) as [Hp Vp].
  destruct (canonb (b :: q0)) eqn:Hq; [|discriminate].
  apply canonb_spec in Hq.
  destruct (mulx (b :: q0) p) as [qp|] eqn:Em; [|discriminate].
  destruct (mulx_ok _ _ _ Hq Hp Em) as [Hqp Vqp].
  destruct (andb (canonb (usub a qp)) (eqv (addb qp (usub a qp)) a)) eqn:Hc; [|discriminate].
  apply andb_true_iff in Hc. destruct Hc as [Hr He].
  apply canonb_spec in Hr. injection H as <- <-.
  split; [exact Hq|]. split; [exact Hr|].
  apply eqv_val in He. destruct (addb_ok _ _ Hqp Hr) as [_ Va].
  rewrite <- He, Va, Vqp, Vp. ring.
Qed.

(* ---------- shifts by 2^(2^k) ---------- *)

Lemma pow2i_spec k : k < 63 -> Uint63.to_Z (pow2i k) = (2 ^ Z.of_nat k)%Z.
Proof.
  intro Hk. unfold pow2i, n2i.
  assert (Hn : Uint63.to_Z (Uint63.of_Z (Z.of_nat k)) = Z.of_nat k).
  { rewrite Uint63.of_Z_spec, Z.mod_small; [reflexivity|]. change Uint63.wB with (2 ^ 63)%Z.
    split; [lia|]. apply Z.lt_le_trans with 63%Z; [lia|]. cbn. lia. }
  rewrite Uint63.lsl_spec, Hn. change (Uint63.to_Z c1i) with 1%Z. rewrite Z.mul_1_l.
  change Uint63.wB with (2 ^ 63)%Z.
  apply Z.mod_small. split; [apply Z.pow_nonneg; lia|]. apply Z.pow_lt_mono_r; lia.
Qed.

Lemma four_pow d0 : Z.of_nat (4 ^ (2 * 2 ^ d0)) = (2 ^ Z.of_nat (2 ^ S (S d0)))%Z.
Proof.
  rewrite <- (Nat2Z.inj_pow 2). f_equal.
  change 4 with (2 ^ 2). rewrite <- Nat.pow_mul_r. f_equal; rewrite ?Nat.pow_succ_r'; lia.
Qed.

(* ---------- the D&C ---------- *)

Lemma F_ok Cl d : forall a w m a' w' m',
  Cl_ok Cl -> d < 60 -> can a -> F Cl d a w m = Some (a', w', m') ->
  can a' /\ Jn (2 ^ d) (nat_of a) w (N.to_nat m) (nat_of a') w' (N.to_nat m').
Proof.
  induction d as [|d0 IH]; intros a w m a' w' m' HC Hd Ha H; cbn [F] in H.
  { exact (leaf_big_ok 1 a w m a' w' m' Ha H). }
  destruct (Nat.leb (S d0) 4) eqn:E4;
    [destruct (leaf_big (2 ^ S d0) a w m) as [[[a1 w1] m1]|] eqn:EL|].
  { injection H as <- <- <-. exact (leaf_big_ok _ _ _ _ _ _ _ Ha EL). }
  all: destruct (Nat.leb (S d0) 3); [discriminate|].
  all: destruct (split_checked (pd Cl (S d0)) (hint Cl (S d0) a) a) as [[q r]|] eqn:ES; [|discriminate].
  all: destruct (F Cl d0 r w m) as [[[r1 w1] m1]|] eqn:E1; [|discriminate].
  all: destruct (F Cl d0 r1 w1 m1) as [[[r2 w2] m2]|] eqn:E2; [|discriminate].
  all: injection H as <- <- <-.
  all: destruct (split_checked_ok _ _ _ _ _ _ HC Ha ES) as [Hq [Hr Va]].
  all: destruct (IH _ _ _ _ _ _ HC ltac:(lia) Hr E1) as [Hr1 J1].
  all: destruct (IH _ _ _ _ _ _ HC ltac:(lia) Hr1 E2) as [Hr2 J2].
  all: pose proof (Jn_split _ (nat_of q) _ _ _ _ _ _ _ _ _ J1 J2) as J.
  all: destruct (shl_ok (pow2i (S (S d0))) q Hq) as [Hs Vs].
  all: destruct (addb_ok _ _ Hs Hr2) as [Hout Vout].
  all: split; [exact Hout|].
  all: rewrite Nat.pow_succ_r'.
  all: replace (nat_of a) with (nat_of q * 3 ^ (2 * 2 ^ d0) + nat_of r)
         by (apply Nat2Z.inj; rewrite Nat2Z.inj_add, Nat2Z.inj_mul, !nat_of_spec, Va,
               <- Nat.pow_succ_r'; reflexivity).
  all: replace (nat_of (addb (shl (pow2i (S (S d0))) q) r2))
         with (nat_of q * 4 ^ (2 * 2 ^ d0) + nat_of r2)
         by (apply Nat2Z.inj; rewrite Nat2Z.inj_add, Nat2Z.inj_mul, !nat_of_spec, Vout, Vs,
               pow2i_spec, four_pow, Nat2Z.inj_pow by lia; change (Z.of_nat 2) with 2%Z; ring).
  all: exact J.
Qed.

Lemma F0_ok Cl n : forall d a w m a' w' m',
  Cl_ok Cl -> Pos.size_nat n + d < 60 -> can a -> F0 Cl a w m n d = Some (a', w', m') ->
  can a' /\ Jn (Pos.to_nat n * 2 ^ d) (nat_of a) w (N.to_nat m) (nat_of a') w' (N.to_nat m').
Proof.
  induction n as [n IH|n IH|]; intros d a w m a' w' m' HC Hs Ha H; cbn [F0 Pos.size_nat] in H, Hs.
  - destruct (F Cl d a w m) as [[[a1 w1] m1]|] eqn:E; [|discriminate].
    destruct (F_ok Cl d _ _ _ _ _ _ HC ltac:(lia) Ha E) as [H1 J1].
    destruct (IH (S d) _ _ _ _ _ _ HC ltac:(lia) H1 H) as [H2 J2].
    split; [exact H2|].
    replace (Pos.to_nat n~1 * 2 ^ d) with (2 ^ d + Pos.to_nat n * 2 ^ S d)
      by (rewrite Pos2Nat.inj_xI, Nat.pow_succ_r'; lia).
    apply (Jn_trans _ _ _ _ _ _ _ _ _ _ _ J1). exact J2.
  - destruct (IH (S d) _ _ _ _ _ _ HC ltac:(lia) Ha H) as [H2 J2].
    split; [exact H2|].
    replace (Pos.to_nat n~0 * 2 ^ d) with (Pos.to_nat n * 2 ^ S d)
      by (rewrite Pos2Nat.inj_xO, Nat.pow_succ_r'; lia).
    exact J2.
  - destruct (F_ok Cl d _ _ _ _ _ _ HC ltac:(lia) Ha H) as [H1 J1].
    split; [exact H1|]. rewrite Nat.mul_1_l. exact J1.
Qed.

(* ---------- the end ---------- *)

Lemma check_ok Dn n : Pos.size_nat n < 60 -> check Dn n = true -> halts tm c0.
Proof.
  intros Hs H. unfold check in H.
  destruct (levels Dn) as [Cl|] eqn:EL; [|discriminate].
  pose proof (levels_ok Dn Cl EL) as HC.
  destruct (F0 Cl (of_u63 c4i) w_empty 1%N n 0) as [[[a w] m]|] eqn:EF; [|discriminate].
  repeat rewrite andb_true_iff in H. destruct H as [[Hw Hm] H3].
  apply Nat.eqb_eq in Hw. subst w. apply N.leb_le in Hm.
  apply Uint63.eqb_correct in H3.
  destruct (F0_ok Cl n 0 _ _ _ _ _ _ HC ltac:(lia) (proj1 (of_u63_ok c4i)) EF) as [Ha J].
  apply Jn_run in J. rewrite nat_of_u63 in J. change (i2n c4i) with 4 in J. change (N.to_nat 1) with 1 in J.
  assert (Hmod : nat_of a mod 3 = 2).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_mod, nat_of_spec. change (Z.of_nat 3) with 3%Z.
    rewrite <- (mod3_ok a Ha), H3. reflexivity. }
  eapply halts_evstep; [|eapply evstep_trans; [apply start|exact J]].
  replace (nat_of a) with (nat_of a / 3 * 3 + 2) by (pose proof (Nat.div_mod_eq (nat_of a) 3); lia).
  replace (N.to_nat m) with (3 + (N.to_nat m - 3)) by lia.
  apply halt_end.
Qed.
End Main.

Lemma halt : halts tm c0.
Proof.
  apply (Main.check_ok 25 298793334).
  - vm_compute. lia.
  - native_cast_no_check (eq_refl true).
Qed.
