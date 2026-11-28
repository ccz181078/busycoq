(** Little-endian lists of 63-bit limbs, with sums and products modulo 2^(63 n).
    The checker carries the raw-step total in these: all that is needed of it is a ring map out of Z. *)
From Coq Require Import ZArith Lia Uint63 List.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Num.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

Fixpoint bval (l : list int) : Z :=
  match l with [] => 0 | x :: t => phi x + P63 * bval t end.

Fixpoint pmod (n : nat) : Z := match n with O => 1 | S n => P63 * pmod n end.

Definition cong (m x y : Z) := exists k, x = y + k * m.
Lemma cong_refl m x : cong m x x.
Proof. exists 0. ring. Qed.
Lemma cong_sym m x y : cong m x y -> cong m y x.
Proof. intros [k ->]. exists (-k). ring. Qed.
Lemma cong_trans m x y z : cong m x y -> cong m y z -> cong m x z.
Proof. intros [k ->] [l ->]. exists (k+l). ring. Qed.
Lemma cong_add m x y u v : cong m x y -> cong m u v -> cong m (x+u) (y+v).
Proof. intros [k ->] [l ->]. exists (k+l). ring. Qed.
Lemma cong_mul m x y u v : cong m x y -> cong m u v -> cong m (x*u) (y*v).
Proof. intros [k ->] [l ->]. exists (k*v+y*l+k*l*m). ring. Qed.
Lemma cong_shift m x y : cong m x y -> cong (P63*m) (P63*x) (P63*y).
Proof. intros [k ->]. exists k. ring. Qed.

(** Sum with carry in. *)
Definition hd0 (l : list int) : int := match l with [] => 0%uint63 | x :: _ => x end.
Definition tl0 (l : list int) : list int := match l with [] => [] | _ :: t => t end.
Lemma bval_ht l : bval l = phi (hd0 l) + P63 * bval (tl0 l).
Proof. destruct l; reflexivity. Qed.

Fixpoint badd (n : nat) (c : bool) (x y : list int) : list int :=
  match n with
  | O => []
  | S n' =>
    match x, y, c with
    | [], [], false => []
    | [], [], true => [1%uint63]
    | _, [], false => x
    | [], _, false => y
    | _, _, _ =>
      let a := hd0 x in
      let s1 := (a + hd0 y)%uint63 in
      let s2 := if c then (s1 + 1)%uint63 else s1 in
      let k := if (s1 <? a)%uint63 then true else if c then (s2 <? s1)%uint63 else false in
      s2 :: badd n' k (tl0 x) (tl0 y)
    end
  end.

Definition b2z (c : bool) : Z := if c then 1 else 0.

Lemma add_carry a b (c : bool) :
  let s1 := (a + b)%uint63 in
  let s2 := if c then (s1 + 1)%uint63 else s1 in
  let k := if (s1 <? a)%uint63 then true else if c then (s2 <? s1)%uint63 else false in
  phi a + phi b + b2z c = phi s2 + P63 * b2z k.
Proof.
  intros s1 s2 k. pose proof (phi_bd a) as Ba. pose proof (phi_bd b) as Bb.
  pose proof (phi_add a b) as E1. fold s1 in E1. pose proof (phi_bd s1) as B1.
  assert (W1 : (s1 <? a)%uint63 = true /\ phi s1 = phi a + phi b - P63 \/ (s1 <? a)%uint63 = false /\ phi s1 = phi a + phi b).
  { destruct (Z.ltb_spec (phi a + phi b) P63) as [G|G].
    - right. assert (E : phi s1 = phi a + phi b) by (rewrite E1; apply Z.mod_small; lia). split; [|exact E].
      destruct (s1 <? a)%uint63 eqn:C; [|reflexivity]. apply Uint63.ltb_spec in C. lia.
    - left. assert (E : phi s1 = phi a + phi b - P63).
      { rewrite E1. Z.div_mod_to_equations. lia. }
      split; [|exact E]. apply Uint63.ltb_spec. lia. }
  subst s2 k. destruct c; cbn [b2z].
  - pose proof (phi_add s1 1%uint63) as E2. rewrite phi_one in E2. pose proof (phi_bd (s1 + 1)%uint63) as B2.
    destruct (Z.ltb_spec (phi s1 + 1) P63) as [G|G].
    + assert (E : phi (s1 + 1)%uint63 = phi s1 + 1) by (rewrite E2; apply Z.mod_small; lia).
      assert (K : ((s1 + 1) <? s1)%uint63 = false).
      { destruct ((s1 + 1) <? s1)%uint63 eqn:C; [|reflexivity]. apply Uint63.ltb_spec in C. lia. }
      rewrite K. destruct W1 as [[-> E3]|[-> E3]]; cbn [b2z]; lia.
    + assert (E : phi (s1 + 1)%uint63 = 0).
      { rewrite E2. replace (phi s1 + 1) with (0 + 1 * P63) by lia. rewrite mod_shift. reflexivity. }
      assert (K : ((s1 + 1) <? s1)%uint63 = true) by (apply Uint63.ltb_spec; lia).
      rewrite K. destruct W1 as [[-> E3]|[-> E3]]; cbn [b2z]; lia.
  - destruct W1 as [[-> E3]|[-> E3]]; cbn [b2z]; lia.
Qed.

Lemma badd_spec n : forall c x y, cong (pmod n) (bval (badd n c x y)) (bval x + bval y + b2z c).
Proof.
  induction n; intros c x y.
  { cbn [badd pmod bval]. exists (-(bval x + bval y + b2z c)). ring. }
  cbn [badd].
  assert (G : cong (pmod (S n)) (bval (let a := hd0 x in
      let s1 := (a + hd0 y)%uint63 in
      let s2 := if c then (s1 + 1)%uint63 else s1 in
      let k := if (s1 <? a)%uint63 then true else if c then (s2 <? s1)%uint63 else false in
      s2 :: badd n k (tl0 x) (tl0 y))) (bval x + bval y + b2z c)).
  { cbv zeta. cbn [bval].
    pose proof (add_carry (hd0 x) (hd0 y) c) as E. cbv zeta in E.
    destruct (IHn (if ((hd0 x + hd0 y) <? hd0 x)%uint63 then true else if c then ((if c then (hd0 x + hd0 y + 1)%uint63 else (hd0 x + hd0 y)%uint63) <? (hd0 x + hd0 y))%uint63 else false) (tl0 x) (tl0 y)) as [k Ek].
    rewrite Ek. rewrite (bval_ht x), (bval_ht y). exists k. cbn [pmod]. rewrite <- ?E. nia. }
  destruct x as [|a x]; destruct y as [|b y]; destruct c; exact G || idtac.
  - exists 0. cbn. reflexivity.
  - exists 0. cbn. reflexivity.
  - exists 0. cbn [bval b2z]. ring.
  - exists 0. cbn [bval b2z]. ring.
Qed.

(** Multiplication by one limb, with carry. *)
Fixpoint bmul1 (n : nat) (m : int) (y : list int) (c : int) : list int :=
  match n with
  | O => []
  | S n' =>
    match y with
    | [] => if (c =? 0)%uint63 then [] else [c]
    | b :: y' =>
      let (p, l) := mulc2 m b in
      let l' := (l + c)%uint63 in
      let p' := if (l' <? l)%uint63 then (p + 1)%uint63 else p in
      l' :: bmul1 n' m y' p'
    end
  end.

Lemma mulc_top m b : phi (fst (mulc2 m b)) < P63 - 1.
Proof.
  pose proof (mulc2_spec m b) as E. pose proof (phi_bd m). pose proof (phi_bd b). pose proof (phi_bd (snd (mulc2 m b))).
  pose proof (phi_bd (fst (mulc2 m b))).
  assert (phi m * phi b <= (P63-1)*(P63-1)) by nia. nia.
Qed.

Lemma bmul1_spec n : forall m y c, cong (pmod n) (bval (bmul1 n m y c)) (phi m * bval y + phi c).
Proof.
  induction n; intros m y c.
  { cbn [bmul1 pmod bval]. exists (-(phi m * bval y + phi c)). ring. }
  destruct y as [|b y]; cbn [bmul1 bval].
  { destruct (c =? 0)%uint63 eqn:E.
    - apply eqb_spec in E. subst c. change (phi 0%uint63) with 0. exists 0. cbn [bval]. ring.
    - exists 0. cbn [bval]. ring. }
  pose proof (mulc2_spec m b) as E. pose proof (mulc_top m b) as T.
  destruct (mulc2 m b) as [p l]. cbn [fst snd] in E, T.
  pose proof (add_carry l c false) as C. cbv zeta in C. cbn [b2z] in C.
  pose proof (phi_bd l). pose proof (phi_bd p).
  destruct ((l + c) <? l)%uint63 eqn:K; cbn [b2z] in C; cbn [bval].
  - assert (P : phi (p + 1)%uint63 = phi p + 1).
    { rewrite phi_add, phi_one. apply Z.mod_small. lia. }
    destruct (IHn m y (p + 1)%uint63) as [k Ek]. rewrite Ek, P. exists k. cbn [pmod]. nia.
  - destruct (IHn m y p) as [k Ek]. rewrite Ek. exists k. cbn [pmod]. nia.
Qed.

Fixpoint bmul (n : nat) (x y : list int) : list int :=
  match n with
  | O => []
  | S n' =>
    match x with
    | [] => []
    | m :: x' =>
      match x' with
      | [] => bmul1 n m y 0%uint63
      | _ => badd n false (if (m =? 0)%uint63 then [] else bmul1 n m y 0%uint63) (0%uint63 :: bmul n' x' y)
      end
    end
  end.

Lemma bmul_spec n : forall x y, cong (pmod n) (bval (bmul n x y)) (bval x * bval y).
Proof.
  induction n; intros x y.
  { cbn [bmul pmod bval]. exists (-(bval x * bval y)). ring. }
  destruct x as [|m x']; cbn [bmul].
  { apply cong_refl. }
  destruct x' as [|m' x''].
  { pose proof (bmul1_spec (S n) m y 0%uint63) as H. change (phi 0%uint63) with 0 in H.
    eapply cong_trans; [exact H|]. cbn [bval]. replace ((phi m + P63 * 0) * bval y) with (phi m * bval y + 0) by ring. apply cong_refl. }
  eapply cong_trans; [apply badd_spec|]. cbn [b2z].
  assert (H1 : cong (pmod (S n)) (bval (if (m =? 0)%uint63 then [] else bmul1 (S n) m y 0%uint63)) (phi m * bval y)).
  { destruct (m =? 0)%uint63 eqn:E.
    - apply eqb_spec in E. subst m. change (phi 0%uint63) with 0. exists 0. cbn [bval]. ring.
    - pose proof (bmul1_spec (S n) m y 0%uint63) as H. change (phi 0%uint63) with 0 in H.
      eapply cong_trans; [exact H|]. replace (phi m * bval y + 0) with (phi m * bval y) by ring. apply cong_refl. }
  destruct H1 as [k1 E1]. destruct (IHn (m' :: x'') y) as [k2 E2].
  rewrite E1. cbn [bval] in *. change (phi 0%uint63) with 0. rewrite E2.
  exists (k1 + k2). cbn [pmod]. ring.
Qed.

(** Into limbs: non-negative values stay short, negative ones are sign-extended to five limbs. *)
Definition NL : nat := 5.
Notation PM := (pmod 5).
Definition ones : int := 9223372036854775807%uint63.
Definition of_W (x : W) : list int :=
  if (hi x =? 0)%uint63 then (if (lo x =? 0)%uint63 then [] else [lo x])
  else if is_neg x then [lo x; hi x; ones; ones; ones] else [lo x; hi x].

Lemma of_W_spec x : cong PM (bval (of_W x)) (val x).
Proof.
  unfold of_W. destruct (hi x =? 0)%uint63 eqn:H0.
  { apply Uint63.eqb_spec in H0. assert (Vx : val x = phi (lo x)).
    { unfold val. rewrite H0. change (sg 0%uint63) with 0. ring. }
    rewrite Vx. destruct (lo x =? 0)%uint63 eqn:L0.
    - apply Uint63.eqb_spec in L0. rewrite L0. exists 0. reflexivity.
    - exists 0. cbn [bval]. ring. }
  destruct (is_neg x) eqn:N.
  - apply is_neg_spec in N. unfold val in *. pose proof (lo_bd x). pose proof (phi_bd (hi x)).
    assert (S : phi (hi x) = sg (hi x) + P63).
    { destruct (sg_cases (hi x)) as [C|C]; [lia|exact C]. }
    cbn [bval]. change (phi ones) with (P63 - 1). rewrite S. exists 1. cbn [pmod]. ring.
  - assert (N' : 0 <= val x).
    { destruct (Z.le_gt_cases 0 (val x)) as [G|G]; [exact G|]. apply is_neg_spec in G. congruence. }
    unfold val in *. pose proof (lo_bd x). pose proof (phi_bd (hi x)).
    assert (S : phi (hi x) = sg (hi x)).
    { destruct (sg_cases (hi x)) as [C|C]; [exact C|]. pose proof (sg_bd (hi x)).  exfalso. unfold sg in *. destruct (Z.ltb_spec (phi (hi x)) P62); lia. }
    cbn [bval]. rewrite S. exists 0. ring.
Qed.

Definition vadd (x y : list int) := badd NL false x y.
Definition vmul (x y : list int) := bmul NL x y.
Lemma vadd_spec x y : cong PM (bval (vadd x y)) (bval x + bval y).
Proof.
  unfold vadd. eapply cong_trans; [apply badd_spec|]. cbn [b2z]. replace (bval x + bval y + 0) with (bval x + bval y) by ring. apply cong_refl.
Qed.
Lemma vmul_spec x y : cong PM (bval (vmul x y)) (bval x * bval y).
Proof. apply bmul_spec. Qed.
