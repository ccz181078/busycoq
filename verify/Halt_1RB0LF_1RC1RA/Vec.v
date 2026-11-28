(** The running cost total: five limbs, modulo 2^315, with a cheap "add x*y". *)
From Coq Require Import ZArith Lia Uint63 List Bool.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Num Big.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Record V := mkV { v0 : int; v1 : int; v2 : int; v3 : int; v4 : int }.

Definition vval (x : V) : Z := bval [v0 x; v1 x; v2 x; v3 x; v4 x].
Definition vzero : V := mkV 0 0 0 0 0.
Lemma vval_zero : vval vzero = 0.
Proof. reflexivity. Qed.

Definition vlist (x : V) : list int := [v0 x; v1 x; v2 x; v3 x; v4 x].

(** Add with carry, as a sum and a carry-out. *)
Definition adc (a b : int) (c : bool) : int * bool :=
  let s1 := (a + b)%uint63 in
  let s2 := if c then (s1 + 1)%uint63 else s1 in
  (s2, if (s1 <? a)%uint63 then true else if c then (s2 <? s1)%uint63 else false).

Lemma adc_spec a b c : phi a + phi b + b2z c = phi (fst (adc a b c)) + P63 * b2z (snd (adc a b c)).
Proof. exact (add_carry a b c). Qed.

(** x + (r0 + r1 P + r2 P^2 + r3 P^3 + r4 P^4) mod P^5 *)
Definition vadd5 (x : V) (r0 r1 r2 r3 r4 : int) : V :=
  let '(s0, c0) := adc (v0 x) r0 false in
  let '(s1, c1) := adc (v1 x) r1 c0 in
  let '(s2, c2) := adc (v2 x) r2 c1 in
  let '(s3, c3) := adc (v3 x) r3 c2 in
  let (s4, _) := adc (v4 x) r4 c3 in
  mkV s0 s1 s2 s3 s4.

Lemma vadd5_spec x r0 r1 r2 r3 r4 :
  cong PM (vval (vadd5 x r0 r1 r2 r3 r4)) (vval x + (phi r0 + P63 * (phi r1 + P63 * (phi r2 + P63 * (phi r3 + P63 * phi r4))))).
Proof.
  unfold vadd5.
  pose proof (adc_spec (v0 x) r0 false) as E0. destruct (adc (v0 x) r0 false) as [s0 c0]. cbn [fst snd] in E0.
  pose proof (adc_spec (v1 x) r1 c0) as E1. destruct (adc (v1 x) r1 c0) as [s1 c1]. cbn [fst snd] in E1.
  pose proof (adc_spec (v2 x) r2 c1) as E2. destruct (adc (v2 x) r2 c1) as [s2 c2]. cbn [fst snd] in E2.
  pose proof (adc_spec (v3 x) r3 c2) as E3. destruct (adc (v3 x) r3 c2) as [s3 c3]. cbn [fst snd] in E3.
  pose proof (adc_spec (v4 x) r4 c3) as E4. destruct (adc (v4 x) r4 c3) as [s4 c4]. cbn [fst snd] in E4.
  unfold vval. cbn [v0 v1 v2 v3 v4 bval]. cbn [b2z] in E0.
  exists (- b2z c4). cbn [pmod]. lia.
Qed.

(** Adding a signed two-limb value. *)
Definition ones5 : int := 9223372036854775807%uint63.
Definition vaddW (x : V) (w : W) : V :=
  if is_neg w then vadd5 x (lo w) (hi w) ones5 ones5 ones5 else vadd5 x (lo w) (hi w) 0 0 0.

Lemma phi_ones5 : phi ones5 = P63 - 1.
Proof. reflexivity. Qed.

Lemma val_nonneg w : 0 <= val w -> val w = phi (hi w) * P63 + phi (lo w) /\ phi (hi w) < P62.
Proof.
  intros H. unfold val in *. pose proof (lo_bd w). pose proof (sg_bd (hi w)). pose proof (phi_bd (hi w)).
  destruct (sg_cases (hi w)) as [C|C]; rewrite ?C.
  - lia.
  - exfalso. lia.
Qed.

Lemma vaddW_spec x w : cong PM (vval (vaddW x w)) (vval x + val w).
Proof.
  unfold vaddW. destruct (is_neg w) eqn:N.
  - apply is_neg_spec in N. eapply cong_trans; [apply vadd5_spec|]. rewrite phi_ones5.
    unfold val in *. pose proof (lo_bd w). pose proof (sg_bd (hi w)). pose proof (phi_bd (hi w)).
    assert (S : phi (hi w) = sg (hi w) + P63).
    { destruct (sg_cases (hi w)) as [C|C]; [lia|exact C]. }
    rewrite S. exists 1. cbn [pmod]. ring.
  - assert (N' : 0 <= val w).
    { destruct (Z.le_gt_cases 0 (val w)) as [G|G]; [exact G|]. apply is_neg_spec in G. congruence. }
    destruct (val_nonneg w N') as [E _].
    eapply cong_trans; [apply vadd5_spec|]. rewrite E. change (phi 0%uint63) with 0.
    exists 0. ring.
Qed.

(** The product of two non-negative two-limb values, added in. The limbs of the product are not reduced
    first: each partial product goes in where it belongs. *)
Definition b2i (c : bool) : int := if c then 1%uint63 else 0%uint63.
Lemma phi_b2i c : phi (b2i c) = b2z c.
Proof. destruct c; reflexivity. Qed.

Definition vaddWW (x : V) (a b : W) : V :=
  let (h0, l0) := mulc2 (lo a) (lo b) in
  let (h1, l1) := mulc2 (lo a) (hi b) in
  let (h2, l2) := mulc2 (hi a) (lo b) in
  let (h3, l3) := mulc2 (hi a) (hi b) in
  let '(t1, c1) := adc h0 l1 false in
  let '(r1, c2) := adc t1 l2 false in
  let '(t2, c3) := adc h1 h2 c1 in
  let '(r2, c4) := adc t2 l3 c2 in
  let '(t3, c5) := adc h3 0%uint63 c3 in
  let '(r3, c6) := adc t3 0%uint63 c4 in
  vadd5 x l0 r1 r2 r3 (b2i (c5 || c6)).

Lemma vaddWW_spec x a b : 0 <= val a -> 0 <= val b -> cong PM (vval (vaddWW x a b)) (vval x + val a * val b).
Proof.
  intros Ha Hb. destruct (val_nonneg a Ha) as [Ea _]. destruct (val_nonneg b Hb) as [Eb _].
  unfold vaddWW.
  pose proof (mulc2_spec (lo a) (lo b)) as E0. destruct (mulc2 (lo a) (lo b)) as [h0 l0]. cbn [fst snd] in E0.
  pose proof (mulc2_spec (lo a) (hi b)) as E1. destruct (mulc2 (lo a) (hi b)) as [h1 l1]. cbn [fst snd] in E1.
  pose proof (mulc2_spec (hi a) (lo b)) as E2. destruct (mulc2 (hi a) (lo b)) as [h2 l2]. cbn [fst snd] in E2.
  pose proof (mulc2_spec (hi a) (hi b)) as E3. destruct (mulc2 (hi a) (hi b)) as [h3 l3]. cbn [fst snd] in E3.
  pose proof (adc_spec h0 l1 false) as A1. destruct (adc h0 l1 false) as [t1 c1]. cbn [fst snd] in A1.
  pose proof (adc_spec t1 l2 false) as A2. destruct (adc t1 l2 false) as [r1 c2]. cbn [fst snd] in A2.
  pose proof (adc_spec h1 h2 c1) as A3. destruct (adc h1 h2 c1) as [t2 c3]. cbn [fst snd] in A3.
  pose proof (adc_spec t2 l3 c2) as A4. destruct (adc t2 l3 c2) as [r2 c4]. cbn [fst snd] in A4.
  pose proof (adc_spec h3 0%uint63 c3) as A5. destruct (adc h3 0%uint63 c3) as [t3 c5]. cbn [fst snd] in A5.
  pose proof (adc_spec t3 0%uint63 c4) as A6. destruct (adc t3 0%uint63 c4) as [r3 c6]. cbn [fst snd] in A6.
  cbn [b2z] in A1, A2. change (phi 0%uint63) with 0 in A5, A6.
  destruct (vadd5_spec x l0 r1 r2 r3 (b2i (c5 || c6))) as [k K].
  rewrite K. rewrite phi_b2i.
  rewrite Ea, Eb.
  replace ((phi (hi a) * P63 + phi (lo a)) * (phi (hi b) * P63 + phi (lo b)))
    with (phi (hi a) * phi (hi b) * (P63 * P63) + (phi (hi a) * phi (lo b) + phi (lo a) * phi (hi b)) * P63 + phi (lo a) * phi (lo b)) by ring.
  rewrite E0, E1, E2, E3.
  assert (Cc : b2z (c5 || c6) = b2z c5 + b2z c6 \/ (c5 = true /\ c6 = true)).
  { destruct c5, c6; cbn; auto. }
  destruct Cc as [Cc|[-> ->]].
  - exists k. rewrite Cc. cbn [pmod]. lia.
  - (* both carries out is impossible: that would need h3 + 2 > 2^63 *)
    exfalso. cbn [b2z] in A5, A6.
    pose proof (phi_bd h3). pose proof (phi_bd t3). pose proof (phi_bd r3).
    assert (T3 : phi h3 < P63 - 1).
    { pose proof (phi_bd (hi a)). pose proof (phi_bd (hi b)). pose proof (phi_bd l3).
      assert (phi (hi a) * phi (hi b) <= (P63 - 1) * (P63 - 1)) by nia. nia. }
    destruct c3, c4; cbn [b2z] in A5, A6; lia.
Qed.

(** From a list of limbs, keeping five. *)
Definition of_list (l : list int) : V :=
  match l with
  | [] => vzero
  | a :: l1 =>
    match l1 with
    | [] => mkV a 0 0 0 0
    | b :: l2 =>
      match l2 with
      | [] => mkV a b 0 0 0
      | c :: l3 =>
        match l3 with
        | [] => mkV a b c 0 0
        | d :: l4 =>
          match l4 with
          | [] => mkV a b c d 0
          | e :: _ => mkV a b c d e
          end
        end
      end
    end
  end.

Lemma of_list_spec l : cong PM (vval (of_list l)) (bval l).
Proof.
  destruct l as [|a [|b [|c [|d [|e t]]]]]; cbn [of_list]; try (exists 0; reflexivity).
  all: unfold vval; cbn [v0 v1 v2 v3 v4 bval].
  all: try (change (phi 0%uint63) with 0; exists 0; ring).
  exists (- bval t). cbn [pmod]. ring.
Qed.

Definition vplus (x y : V) : V := vadd5 x (v0 y) (v1 y) (v2 y) (v3 y) (v4 y).
Lemma vplus_spec x y : cong PM (vval (vplus x y)) (vval x + vval y).
Proof.
  unfold vplus. eapply cong_trans; [apply vadd5_spec|]. unfold vval. cbn [bval]. exists 0. ring.
Qed.

Definition veqb (x y : V) : bool :=
  (v0 x =? v0 y)%uint63 && (v1 x =? v1 y)%uint63 && (v2 x =? v2 y)%uint63 && (v3 x =? v3 y)%uint63 && (v4 x =? v4 y)%uint63.
Lemma veqb_eq x y : veqb x y = true -> x = y.
Proof.
  destruct x, y. unfold veqb. cbn [v0 v1 v2 v3 v4]. intros H.
  repeat (apply andb_prop in H; destruct H as [H ?]). 
  repeat match goal with H : (_ =? _)%uint63 = true |- _ => apply Uint63.eqb_spec in H; subst end. reflexivity.
Qed.
