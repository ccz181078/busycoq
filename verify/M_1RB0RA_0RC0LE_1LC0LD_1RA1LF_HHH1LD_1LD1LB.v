(* BB(6) holdout 608:#235 / 797:#318: 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Strings.String Lists.List PeanoNat NArith PArith ZArith ZifyN Lia.

Definition tm : TM := TM_from_str "1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB"%string.

Module Internal.

Import ListNotations.
Local Unset Default Goal Selector.
Local Set Primitive Projections.
Local Close Scope sym_scope.
Local Open Scope string_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.

(* ========================================================================= *)
(* Section 1: TM Helpers, Binary N Arithmetic, LTok & RTok                   *)
(* ========================================================================= *)

Lemma rs_refl (c : Q * tape) : c -[ tm ]->* c.
Proof. apply evstep_refl. Qed.

Lemma rs_trans {c1 c2 c3 : Q * tape} (h1 : c1 -[ tm ]->* c2) (h2 : c2 -[ tm ]->* c3) :
  c1 -[ tm ]->* c3.
Proof. eapply evstep_trans; [exact h1 | exact h2]. Qed.

Lemma evstep_to_halts {c ch : Q * tape} (hev : c -[ tm ]->* ch) (hh : halted tm ch) :
  halts tm c.
Proof.
  induction hev as [c | c c' c'' hstep _ IH].
  - exists 0%nat, c. split; [apply multistep_0 | exact hh].
  - destruct (IH hh) as [n [ch' [hm hch]]].
    exists (S n), ch'. split; [eapply multistep_S; [exact hstep | exact hm] | exact hch].
Qed.

Lemma step_R_R q q' a b sl sr :
  tm (q, a) = Some (b, R, q') ->
  (sl {{q}}> (a >> sr)) -[ tm ]-> ((b >> sl) {{q'}}> sr).
Proof. intro H; exact (step_right H). Qed.

Lemma step_R_L q q' a b sl sr :
  tm (q, a) = Some (b, L, q') ->
  (sl {{q}}> (a >> sr)) -[ tm ]-> (sl <{{q'}} (b >> sr)).
Proof. intro H; exact (step_left H). Qed.

Lemma step_L_R q q' a b sl sr :
  tm (q, a) = Some (b, R, q') ->
  ((a >> sl) <{{q}} sr) -[ tm ]-> ((b >> sl) {{q'}}> sr).
Proof. intro H; exact (step_right H). Qed.

Lemma step_L_L q q' a b sl sr :
  tm (q, a) = Some (b, L, q') ->
  ((a >> sl) <{{q}} sr) -[ tm ]-> (sl <{{q'}} (b >> sr)).
Proof. intro H; exact (step_left H). Qed.

Lemma cfg_L_cons (a : Sym) (q : Q) (sl sr : side) :
  ((a >> sl) <{{q}} sr) = (sl {{q}}> (a >> sr)).
Proof. reflexivity. Qed.

Lemma default_eq_cons_zero : const S0 = S0 >> const S0.
Proof. apply const_unfold. Qed.

Lemma cons_inj {a : Sym} {x y : side} (h : a >> x = a >> y) : x = y.
Proof. exact (f_equal (@Streams.tl Sym) h). Qed.

Ltac tstep1 :=
  eapply evstep_step;
  [ first [ apply step_R_R; reflexivity
          | apply step_R_L; reflexivity
          | apply step_L_R; reflexivity
          | apply step_L_L; reflexivity ]
  | ].

Ltac tsteps :=
  repeat (lazymatch goal with
          | |- ?c -[ tm ]->* ?c => fail
          | _ => progress (try apply evstep_refl; tstep1)
          end);
  apply evstep_refl.

Ltac nind n :=
  pattern n; apply N.peano_ind;
  [ | clear n; intros n IH; replace (N.succ n) with (n + 1) by lia ].

Lemma N_iter_0 {T} (f : T -> T) (x : T) : N.iter 0 f x = x.
Proof. reflexivity. Qed.

Lemma N_iter_succ_r {T} (n : N) (f : T -> T) (x : T) :
  N.iter (n + 1) f x = f (N.iter n f x).
Proof. replace (n + 1) with (N.succ n) by lia. apply N.iter_succ. Qed.

Lemma div2_even (q : N) : (2 * q) / 2 = q. Proof. lia. Qed.
Lemma mod2_even (q : N) : (2 * q) mod 2 = 0. Proof. lia. Qed.
Lemma div2_odd (q : N) : (2 * q + 1) / 2 = q. Proof. lia. Qed.
Lemma mod2_odd (q : N) : (2 * q + 1) mod 2 = 1. Proof. lia. Qed.

Lemma N_iter_1_add {T} (n : N) (f : T -> T) (x : T) :
  N.iter (1 + n) f x = f (N.iter n f x).
Proof. replace (1 + n) with (N.succ n) by lia. apply N.iter_succ. Qed.

Lemma N_iter_add {T} (m n : N) (f : T -> T) (x : T) :
  N.iter (m + n) f x = N.iter m f (N.iter n f x).
Proof.
  nind m; [reflexivity |].
  replace (m + 1 + n) with ((m + n) + 1) by lia.
  rewrite !N_iter_succ_r, IH. reflexivity.
Qed.

Lemma N_iter_snoc {T} (n : N) (f : T -> T) (x : T) :
  N.iter n f (f x) = f (N.iter n f x).
Proof. apply N.iter_swap. Qed.

Lemma pow2_pos (n : N) : 1 <= 2 ^ n.
Proof.
  nind n; [lia |].
  replace (n + 1) with (N.succ n) by lia.
  rewrite N.pow_succ_r'; lia.
Qed.

Lemma pow2_succ (n : N) : 2 ^ (n + 1) = 2 * 2 ^ n.
Proof.
  replace (n + 1) with (N.succ n) by lia.
  apply N.pow_succ_r'.
Qed.

Lemma pow2_mono (a b : N) (hle : a <= b) : 2 ^ a <= 2 ^ b.
Proof. apply N.pow_le_mono_r; lia. Qed.

Definition bitSym (b : bool) : Sym := if b then S1 else S0.

Definition repBit (b : bool) (n : N) (t : side) : side :=
  N.iter n (fun s => bitSym b >> s) t.

Lemma repBit_0 (b : bool) (t : side) : repBit b 0 t = t.
Proof. reflexivity. Qed.

Lemma repBit_succ (b : bool) (n : N) (t : side) :
  repBit b (n + 1) t = bitSym b >> repBit b n t.
Proof. unfold repBit; apply N_iter_succ_r. Qed.

Lemma repBit_add (b : bool) (m n : N) (t : side) :
  repBit b (m + n) t = repBit b m (repBit b n t).
Proof. unfold repBit; apply N_iter_add. Qed.

Lemma repBit_snoc (b : bool) (n : N) (t : side) :
  repBit b n (bitSym b >> t) = bitSym b >> repBit b n t.
Proof. unfold repBit; apply N_iter_snoc. Qed.

Lemma repBit_snoc_false (n : N) (t : side) :
  repBit false n (S0 >> t) = S0 >> repBit false n t.
Proof. exact (repBit_snoc false n t). Qed.

Lemma repBit_snoc_true (n : N) (t : side) :
  repBit true n (S1 >> t) = S1 >> repBit true n t.
Proof. exact (repBit_snoc true n t). Qed.

Lemma repBit_false_default (n : N) : repBit false n (const S0) = const S0.
Proof.
  nind n; [reflexivity |].
  rewrite repBit_succ, IH. symmetry; apply default_eq_cons_zero.
Qed.

Lemma repBit_inj (b : bool) (n : N) {x y : side} :
  repBit b n x = repBit b n y -> x = y.
Proof.
  nind n; [exact (fun h => h) |].
  rewrite !repBit_succ. intro h; apply IH; exact (cons_inj h).
Qed.

Fixpoint encPairsNat (len : nat) (val : N) (sl : side) : side :=
  match len with
  | O => sl
  | S len' => S0 >> (if val mod 2 =? 1 then S0 else S1) >> encPairsNat len' (val / 2) sl
  end.

Definition encPairs (len val : N) (sl : side) : side :=
  encPairsNat (N.to_nat len) val sl.

Lemma encPairs_0 (val : N) (sl : side) : encPairs 0 val sl = sl.
Proof. reflexivity. Qed.

Lemma encPairs_succ (len val : N) (sl : side) :
  encPairs (len + 1) val sl =
    S0 >> (if val mod 2 =? 1 then S0 else S1) >> encPairs len (val / 2) sl.
Proof.
  unfold encPairs.
  replace (N.to_nat (len + 1)) with (S (N.to_nat len)) by lia.
  reflexivity.
Qed.

Lemma N_add_mul_mod2 (a b : N) : (a + 2 * b) mod 2 = a mod 2.
Proof. lia. Qed.

Lemma N_add_mul_div2 (a b : N) : (a + 2 * b) / 2 = a / 2 + b.
Proof. lia. Qed.

Lemma encPairs_add (len1 len2 val1 val2 : N) (sl : side) :
  val1 < 2 ^ len1 ->
  encPairs (len1 + len2) (val1 + val2 * 2 ^ len1) sl =
    encPairs len1 val1 (encPairs len2 val2 sl).
Proof.
  revert val1 sl.
  nind len1.
  - intros val1 sl hlt. change (2 ^ 0) with 1 in hlt.
    assert (val1 = 0) by lia; subst val1.
    replace (0 + len2) with len2 by lia.
    replace (0 + val2 * 2 ^ 0) with val2 by (change (2 ^ 0) with 1; lia).
    reflexivity.
  - intros val1 sl hlt.
    rewrite pow2_succ in hlt |- *.
    replace (len1 + 1 + len2) with ((len1 + len2) + 1) by lia.
    rewrite !encPairs_succ.
    replace (val1 + val2 * (2 * 2 ^ len1)) with (val1 + 2 * (val2 * 2 ^ len1))
      by (set (p := 2 ^ len1); clearbody p; nia).
    rewrite N_add_mul_mod2, N_add_mul_div2.
    f_equal; f_equal.
    apply IH; lia.
Qed.

Lemma encPairs_all_ones (p : N) (sl : side) :
  encPairs p (2 ^ p - 1) sl = repBit false (2 * p) sl.
Proof.
  revert sl; nind p; intro sl; [reflexivity |].
  pose proof (pow2_pos p) as hp.
  rewrite pow2_succ.
  replace (2 * (p + 1)) with (2 + 2 * p) by lia.
  rewrite repBit_add, encPairs_succ.
  assert (hm : (2 * 2 ^ p - 1) mod 2 = 1) by lia.
  assert (hd : (2 * 2 ^ p - 1) / 2 = 2 ^ p - 1) by lia.
  rewrite hm, hd; cbn [N.eqb repBit N.iter Pos.iter bitSym].
  rewrite IH; reflexivity.
Qed.

Lemma encPairs_snoc (len val : N) (bit : bool) (sl : side) (hlt : val < 2 ^ len) :
  encPairs (len + 1) (val + (if bit then 2 ^ len else 0)) sl =
    encPairs len val (S0 >> (if bit then S0 else S1) >> sl).
Proof.
  pose proof (encPairs_add len 1 val (if bit then 1 else 0) sl hlt) as h1.
  destruct bit.
  - replace (val + 1 * 2 ^ len) with (val + 2 ^ len) in h1 by lia.
    rewrite h1; reflexivity.
  - replace (val + 0 * 2 ^ len) with val in h1 by lia.
    replace (val + 0) with val by lia.
    rewrite h1; reflexivity.
Qed.

Lemma encPairs_mod (k v : N) (sl : side) :
  encPairs k (v mod 2 ^ k) sl = encPairs k v sl.
Proof.
  revert v sl; nind k; intros v sl; [reflexivity |].
  rewrite pow2_succ, !encPairs_succ, N.Div0.mod_mul_r.
  rewrite N_add_mul_mod2, N_add_mul_div2.
  assert (h0 : (v mod 2) / 2 = 0) by lia.
  assert (h1 : (v mod 2) mod 2 = v mod 2) by lia.
  rewrite h0, h1, N.add_0_l, IH. reflexivity.
Qed.

Definition maskPow2 (k v : N) : N := N.land v (N.ones k).

Lemma maskPow2_eq_mod (k v : N) : maskPow2 k v = v mod 2 ^ k.
Proof. unfold maskPow2; apply N.land_ones. Qed.

Lemma maskPow2_lt (k v : N) : maskPow2 k v < 2 ^ k.
Proof.
  rewrite maskPow2_eq_mod. pose proof (pow2_pos k).
  apply N.mod_lt; lia.
Qed.

Lemma encPairs_maskPow2 (k v : N) (sl : side) :
  encPairs k (maskPow2 k v) sl = encPairs k v sl.
Proof. rewrite maskPow2_eq_mod; apply encPairs_mod. Qed.

Inductive LTok : Type :=
| Lz (k : N)
| Lo (k : N)
| Lpairs (len val : N).

Fixpoint encL (l : list LTok) : side :=
  match l with
  | [] => const S0
  | Lz k :: ls => repBit false (k + 1) (encL ls)
  | Lo k :: ls => repBit true (k + 1) (encL ls)
  | Lpairs len val :: ls => encPairs len val (encL ls)
  end.

Definition lpushBit (b : bool) (n : N) (l : list LTok) : list LTok :=
  if n =? 0 then l
  else
    let m := n - 1 in
    match b, l with
    | false, [] => []
    | true, [] => [Lo m]
    | false, Lz k :: ls => Lz (k + m + 1) :: ls
    | true, Lo k :: ls => Lo (k + m + 1) :: ls
    | false, ls => Lz m :: ls
    | true, ls => Lo m :: ls
    end.

Lemma encL_lpushBit (b : bool) (n : N) (l : list LTok) :
  encL (lpushBit b n l) = repBit b n (encL l).
Proof.
  unfold lpushBit.
  destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct b, l as [| [k | k | len val] ls]; cbn [encL].
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + rewrite <- repBit_add; f_equal; lia.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + symmetry; apply repBit_false_default.
    + rewrite <- repBit_add; f_equal; lia.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
Qed.

Definition lpush0 (n : N) (l : list LTok) : list LTok :=
  match l with
  | [] => []
  | Lz k :: ls => Lz (k + n) :: ls
  | ls => Lz (n - 1) :: ls
  end.

Lemma encL_lpush0 (n : N) (hn : 1 <= n) (l : list LTok) :
  encL (lpush0 n l) = repBit false n (encL l).
Proof.
  destruct l as [| [k | k | len val] ls]; cbn [lpush0 encL].
  - symmetry; apply repBit_false_default.
  - rewrite <- repBit_add; f_equal; lia.
  - replace (n - 1 + 1) with n by lia; reflexivity.
  - replace (n - 1 + 1) with n by lia; reflexivity.
Qed.

Definition lpush0_1 (l : list LTok) : list LTok :=
  match l with
  | [] => []
  | Lz k :: ls => Lz (k + 1) :: ls
  | ls => Lz 0 :: ls
  end.

Lemma encL_lpush0_1 (l : list LTok) :
  encL (lpush0_1 l) = S0 >> encL l.
Proof.
  destruct l as [| [k | k | len val] ls]; cbn [lpush0_1 encL].
  - apply default_eq_cons_zero.
  - replace (k + 1 + 1) with ((k + 1) + 1) by lia. rewrite repBit_succ; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition lpush1_1 (l : list LTok) : list LTok :=
  match l with
  | Lo k :: ls => Lo (k + 1) :: ls
  | ls => Lo 0 :: ls
  end.

Lemma encL_lpush1_1 (l : list LTok) :
  encL (lpush1_1 l) = S1 >> encL l.
Proof.
  destruct l as [| [k | k | len val] ls]; cbn [lpush1_1 encL].
  - reflexivity.
  - reflexivity.
  - replace (k + 1 + 1) with ((k + 1) + 1) by lia. rewrite repBit_succ; reflexivity.
  - reflexivity.
Qed.

Definition lpush1_2 (l : list LTok) : list LTok :=
  match l with
  | Lo k :: ls => Lo (k + 2) :: ls
  | ls => Lo 1 :: ls
  end.

Lemma encL_lpush1_2 (l : list LTok) :
  encL (lpush1_2 l) = S1 >> S1 >> encL l.
Proof.
  destruct l as [| [k | k | len val] ls]; cbn [lpush1_2 encL].
  - reflexivity.
  - reflexivity.
  - replace (k + 2 + 1) with (2 + (k + 1)) by lia. rewrite repBit_add; reflexivity.
  - reflexivity.
Qed.

Definition lpush1_n (n : N) (l : list LTok) : list LTok :=
  match l with
  | Lo k :: ls => Lo (k + n) :: ls
  | ls => Lo (n - 1) :: ls
  end.

Lemma encL_lpush1_n (n : N) (hn : 1 <= n) (l : list LTok) :
  encL (lpush1_n n l) = repBit true n (encL l).
Proof.
  destruct l as [| [k | k | len val] ls]; cbn [lpush1_n encL].
  - replace (n - 1 + 1) with n by lia; reflexivity.
  - replace (n - 1 + 1) with n by lia; reflexivity.
  - rewrite <- repBit_add; f_equal; lia.
  - replace (n - 1 + 1) with n by lia; reflexivity.
Qed.

Definition lpushPairs (len val : N) (l : list LTok) : list LTok :=
  if len =? 0 then l else Lpairs len val :: l.

Lemma encL_lpushPairs (len val : N) (l : list LTok) :
  encL (lpushPairs len val l) = encPairs len val (encL l).
Proof.
  unfold lpushPairs. destruct (len =? 0) eqn:h0.
  - apply N.eqb_eq in h0; subst len; reflexivity.
  - reflexivity.
Qed.

Record BPopL := mkBPopL { bpl_b : bool; bpl_l : list LTok }.

Fixpoint lpop1 (l : list LTok) : BPopL :=
  match l with
  | [] => mkBPopL false []
  | Lz k :: ls => mkBPopL false (if k =? 0 then ls else Lz (k - 1) :: ls)
  | Lo k :: ls => mkBPopL true (if k =? 0 then ls else Lo (k - 1) :: ls)
  | Lpairs len val :: ls =>
    if len =? 0 then lpop1 ls
    else
      let len1 := len - 1 in
      let rest := if len1 =? 0 then ls else Lpairs len1 (N.div2 val) :: ls in
      if N.odd val then mkBPopL false (lpush0_1 rest) else mkBPopL false (lpush1_1 rest)
  end.

Lemma N_div2_eq (v : N) : N.div2 v = v / 2.
Proof. apply N.div2_div. Qed.

Lemma N_odd_eq (v : N) : N.odd v = (v mod 2 =? 1).
Proof.
  rewrite <- N.bit0_odd, <- N.bit0_mod.
  destruct (N.testbit v 0); reflexivity.
Qed.

Lemma encL_lpop1 (l : list LTok) :
  encL l = bitSym (bpl_b (lpop1 l)) >> encL (bpl_l (lpop1 l)).
Proof.
  induction l as [| [k | k | len val] ls IH]; cbn [lpop1 encL bpl_b bpl_l].
  - apply default_eq_cons_zero.
  - destruct (k =? 0) eqn:hk.
    + apply N.eqb_eq in hk; subst k; reflexivity.
    + apply N.eqb_neq in hk; cbn [encL].
      replace (k + 1) with ((k - 1 + 1) + 1) by lia.
      rewrite repBit_succ; reflexivity.
  - destruct (k =? 0) eqn:hk.
    + apply N.eqb_eq in hk; subst k; reflexivity.
    + apply N.eqb_neq in hk; cbn [encL].
      replace (k + 1) with ((k - 1 + 1) + 1) by lia.
      rewrite repBit_succ; reflexivity.
  - destruct (len =? 0) eqn:hl0.
    + apply N.eqb_eq in hl0; subst len; rewrite encPairs_0; exact IH.
    + apply N.eqb_neq in hl0.
      replace len with ((len - 1) + 1) at 1 by lia.
      rewrite encPairs_succ, N_div2_eq, N_odd_eq.
      set (rest := if len - 1 =? 0 then ls else Lpairs (len - 1) (val / 2) :: ls).
      assert (hrest : encL rest = encPairs (len - 1) (val / 2) (encL ls)).
      { unfold rest; destruct (len - 1 =? 0) eqn:hl1; [apply N.eqb_eq in hl1; rewrite hl1; reflexivity | reflexivity]. }
      destruct (val mod 2 =? 1); cbn [bpl_b bpl_l bitSym];
        [rewrite encL_lpush0_1 | rewrite encL_lpush1_1]; rewrite hrest; reflexivity.
Qed.

Record StepRes (T : Type) := mkStepRes { sr_done : bool; sr_val : T }.
Arguments mkStepRes {T}.
Arguments sr_done {T}.
Arguments sr_val {T}.

Fixpoint runPos {T : Type} (p : positive) (step : T -> StepRes T) (x : T) : StepRes T :=
  match p with
  | xH => step x
  | xO p' =>
    let r1 := runPos p' step x in
    if sr_done r1 then r1 else runPos p' step (sr_val r1)
  | xI p' =>
    let r0 := step x in
    if sr_done r0 then r0 else
      let r1 := runPos p' step (sr_val r0) in
      if sr_done r1 then r1 else runPos p' step (sr_val r1)
  end.

Lemma runPos_rel {T : Type} (R : T -> T -> Prop)
  (htrans : forall x y z, R x y -> R y z -> R x z)
  (step : T -> StepRes T)
  (hstep : forall x, R x (sr_val (step x)))
  (p : positive) :
  forall x : T, R x (sr_val (runPos p step x)).
Proof.
  induction p as [p' IH | p' IH |]; intro x; cbn [runPos].
  - destruct (sr_done (step x)); [apply hstep |].
    destruct (sr_done (runPos p' step (sr_val (step x)))).
    + eapply htrans; [apply hstep | apply IH].
    + eapply htrans; [apply hstep | eapply htrans; [apply IH | apply IH]].
  - destruct (sr_done (runPos p' step x)).
    + apply IH.
    + eapply htrans; [apply IH | apply IH].
  - apply hstep.
Qed.

Record ZRunRes := mkZRun { zr_n : N; zr_l : list LTok }.

Definition lpopZRunStep (st : ZRunRes) : StepRes ZRunRes :=
  let acc := zr_n st in
  let l := zr_l st in
  match l with
  | Lz k :: ls => mkStepRes false (mkZRun (acc + k + 1) ls)
  | Lpairs len val :: ls =>
    if len =? 0 then mkStepRes false (mkZRun acc ls)
    else
      let len1 := len - 1 in
      let rest := if len1 =? 0 then ls else Lpairs len1 (N.div2 val) :: ls in
      if N.odd val then mkStepRes false (mkZRun (acc + 2) rest)
      else mkStepRes true (mkZRun (acc + 1) (lpush1_1 rest))
  | _ => mkStepRes true st
  end.

Definition lpopZRun (l : list LTok) : ZRunRes :=
  sr_val (runPos 4096%positive lpopZRunStep (mkZRun 0 l)).

Lemma lpopZRunStep_sound (st : ZRunRes) :
  repBit false (zr_n st) (encL (zr_l st)) =
    repBit false (zr_n (sr_val (lpopZRunStep st))) (encL (zr_l (sr_val (lpopZRunStep st)))).
Proof.
  destruct st as [acc [| [k | k | len val] ls]]; cbn [lpopZRunStep sr_val zr_n zr_l]; try reflexivity.
  - cbn [encL]. replace (acc + k + 1) with (acc + (k + 1)) by lia.
    rewrite (repBit_add false acc (k + 1)); reflexivity.
  - destruct (len =? 0) eqn:hl0.
    + apply N.eqb_eq in hl0; subst len; cbn [encL sr_val zr_n zr_l]; rewrite encPairs_0; reflexivity.
    + apply N.eqb_neq in hl0.
      rewrite N_div2_eq, N_odd_eq.
      set (rest := if len - 1 =? 0 then ls else Lpairs (len - 1) (val / 2) :: ls).
      assert (hrest : encL rest = encPairs (len - 1) (val / 2) (encL ls)).
      { unfold rest; destruct (len - 1 =? 0) eqn:hl1; [apply N.eqb_eq in hl1; rewrite hl1; reflexivity | reflexivity]. }
      cbn [encL]. replace len with ((len - 1) + 1) at 1 by lia. rewrite encPairs_succ.
      destruct (val mod 2 =? 1); cbn [sr_val zr_n zr_l].
      * rewrite (repBit_add false acc 2), hrest. reflexivity.
      * rewrite encL_lpush1_1, hrest, (repBit_succ false acc), repBit_snoc_false. reflexivity.
Qed.

Lemma encL_lpopZRun (l : list LTok) :
  encL l = repBit false (zr_n (lpopZRun l)) (encL (zr_l (lpopZRun l))).
Proof.
  exact (runPos_rel
           (fun s1 s2 => repBit false (zr_n s1) (encL (zr_l s1)) = repBit false (zr_n s2) (encL (zr_l s2)))
           (fun _ _ _ => @eq_trans side _ _ _) lpopZRunStep lpopZRunStep_sound 4096%positive (mkZRun 0 l)).
Qed.

Definition encW01 (n : N) (sr : side) : side :=
  N.iter n (fun s => S0 >> S1 >> s) sr.

Definition encW0111 (n : N) (sr : side) : side :=
  N.iter n (fun s => S0 >> S1 >> S1 >> S1 >> s) sr.

Lemma encW01_0 (sr : side) : encW01 0 sr = sr.
Proof. reflexivity. Qed.

Lemma encW01_succ (n : N) (sr : side) :
  encW01 (n + 1) sr = S0 >> S1 >> encW01 n sr.
Proof. exact (N_iter_succ_r n (fun s => S0 >> S1 >> s) sr). Qed.

Lemma encW01_add (m n : N) (sr : side) :
  encW01 (m + n) sr = encW01 m (encW01 n sr).
Proof. exact (N_iter_add m n (fun s => S0 >> S1 >> s) sr). Qed.

Lemma encW0111_0 (sr : side) : encW0111 0 sr = sr.
Proof. reflexivity. Qed.

Lemma encW0111_succ (n : N) (sr : side) :
  encW0111 (n + 1) sr = S0 >> S1 >> S1 >> S1 >> encW0111 n sr.
Proof. exact (N_iter_succ_r n (fun s => S0 >> S1 >> S1 >> S1 >> s) sr). Qed.

Lemma encW0111_add (m n : N) (sr : side) :
  encW0111 (m + n) sr = encW0111 m (encW0111 n sr).
Proof. exact (N_iter_add m n (fun s => S0 >> S1 >> S1 >> S1 >> s) sr). Qed.

Inductive RTok : Type :=
| Rz (k : N)
| Ro (k : N)
| Rw01 (k : N)
| Rw0111 (k : N).

Fixpoint encR (r : list RTok) : side :=
  match r with
  | [] => const S0
  | Rz k :: rs => repBit false (k + 1) (encR rs)
  | Ro k :: rs => repBit true (k + 1) (encR rs)
  | Rw01 k :: rs => encW01 (k + 1) (encR rs)
  | Rw0111 k :: rs => encW0111 (k + 1) (encR rs)
  end.

Definition rpushW01 (n : N) (r : list RTok) : list RTok :=
  if n =? 0 then r
  else
    let m := n - 1 in
    match r with
    | Rw01 k :: rs => Rw01 (k + m + 1) :: rs
    | rs => Rw01 m :: rs
    end.

Definition rpushW0111 (n : N) (r : list RTok) : list RTok :=
  if n =? 0 then r
  else
    let m := n - 1 in
    match r with
    | Rw0111 k :: rs => Rw0111 (k + m + 1) :: rs
    | rs => Rw0111 m :: rs
    end.

Lemma encR_rpushW01 (n : N) (r : list RTok) :
  encR (rpushW01 n r) = encW01 n (encR r).
Proof.
  unfold rpushW01. destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct r as [| [k | k | k | k] rs]; cbn [encR].
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + rewrite <- encW01_add; f_equal; lia.
    + replace (n - 1 + 1) with n by lia; reflexivity.
Qed.

Lemma encR_rpushW0111 (n : N) (r : list RTok) :
  encR (rpushW0111 n r) = encW0111 n (encR r).
Proof.
  unfold rpushW0111. destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct r as [| [k | k | k | k] rs]; cbn [encR].
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + rewrite <- encW0111_add; f_equal; lia.
Qed.

Definition rpushBitRaw (b : bool) (n : N) (r : list RTok) : list RTok :=
  if n =? 0 then r
  else
    let m := n - 1 in
    match b, r with
    | false, [] => []
    | true, [] => [Ro m]
    | false, Rz k :: rs => Rz (k + m + 1) :: rs
    | true, Ro k :: rs => Ro (k + m + 1) :: rs
    | false, rs => Rz m :: rs
    | true, rs => Ro m :: rs
    end.

Lemma encR_rpushBitRaw (b : bool) (n : N) (r : list RTok) :
  encR (rpushBitRaw b n r) = repBit b n (encR r).
Proof.
  unfold rpushBitRaw. destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct b, r as [| [k | k | k | k] rs]; cbn [encR].
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + rewrite <- repBit_add; f_equal; lia.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + symmetry; apply repBit_false_default.
    + rewrite <- repBit_add; f_equal; lia.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + replace (n - 1 + 1) with n by lia; reflexivity.
Qed.

Definition rpushBit (b : bool) (n : N) (r : list RTok) : list RTok :=
  if n =? 0 then r
  else if negb b then
    match r with
    | Ro k :: rs =>
      if k =? 0 then rpushBitRaw false (n - 1) (rpushW01 1 rs)
      else if k =? 2 then rpushBitRaw false (n - 1) (rpushW0111 1 rs)
      else rpushBitRaw false n r
    | _ => rpushBitRaw false n r
    end
  else rpushBitRaw true n r.

Lemma encR_rpushBit (b : bool) (n : N) (r : list RTok) :
  encR (rpushBit b n r) = repBit b n (encR r).
Proof.
  unfold rpushBit. destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct b; cbn [negb].
    + apply encR_rpushBitRaw.
    + destruct r as [| [k | k | k | k] rs]; try apply encR_rpushBitRaw.
      destruct (k =? 0) eqn:hk0.
      * apply N.eqb_eq in hk0; subst k.
        rewrite encR_rpushBitRaw, encR_rpushW01; cbn [encR encW01 repBit N.iter Pos.iter bitSym].
        replace n with ((n - 1) + 1) at 2 by lia.
        rewrite repBit_succ, repBit_snoc_false; reflexivity.
      * destruct (k =? 2) eqn:hk2; [| apply encR_rpushBitRaw].
        apply N.eqb_eq in hk2; subst k.
        rewrite encR_rpushBitRaw, encR_rpushW0111; cbn [encR encW0111 repBit N.iter Pos.iter bitSym].
        replace n with ((n - 1) + 1) at 2 by lia.
        rewrite repBit_succ, repBit_snoc_false; reflexivity.
Qed.

Definition rpush0_1 (r : list RTok) : list RTok :=
  match r with
  | [] => []
  | Rz k :: rs => Rz (k + 1) :: rs
  | Ro k :: rs =>
    if k =? 0 then
      match rs with Rw01 w :: rs' => Rw01 (w + 1) :: rs' | _ => Rw01 0 :: rs end
    else if k =? 2 then
      match rs with Rw0111 w :: rs' => Rw0111 (w + 1) :: rs' | _ => Rw0111 0 :: rs end
    else Rz 0 :: Ro k :: rs
  | rs => Rz 0 :: rs
  end.

Lemma encR_rpush0_1 (r : list RTok) :
  encR (rpush0_1 r) = S0 >> encR r.
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpush0_1 encR].
  - apply default_eq_cons_zero.
  - replace (k + 1 + 1) with ((k + 1) + 1) by lia. rewrite repBit_succ; reflexivity.
  - destruct (k =? 0) eqn:hk0.
    + apply N.eqb_eq in hk0; subst k.
      destruct rs as [| [w | w | w | w] rs']; try reflexivity.
      cbn [encR]. replace (w + 1 + 1) with ((w + 1) + 1) by lia. rewrite encW01_succ; reflexivity.
    + destruct (k =? 2) eqn:hk2; [| reflexivity].
      apply N.eqb_eq in hk2; subst k.
      destruct rs as [| [w | w | w | w] rs']; try reflexivity.
      cbn [encR]. replace (w + 1 + 1) with ((w + 1) + 1) by lia. rewrite encW0111_succ; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition rpush0_2 (r : list RTok) : list RTok :=
  match r with
  | [] => []
  | Rz k :: rs => Rz (k + 2) :: rs
  | Ro k :: rs =>
    if k =? 0 then Rz 0 :: (match rs with Rw01 w :: rs' => Rw01 (w + 1) :: rs' | _ => Rw01 0 :: rs end)
    else if k =? 2 then Rz 0 :: (match rs with Rw0111 w :: rs' => Rw0111 (w + 1) :: rs' | _ => Rw0111 0 :: rs end)
    else Rz 1 :: Ro k :: rs
  | rs => Rz 1 :: rs
  end.

Lemma encR_rpush0_2 (r : list RTok) :
  encR (rpush0_2 r) = S0 >> S0 >> encR r.
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpush0_2 encR].
  - rewrite default_eq_cons_zero at 1. rewrite default_eq_cons_zero at 1. reflexivity.
  - replace (k + 2 + 1) with (2 + (k + 1)) by lia. rewrite repBit_add; reflexivity.
  - destruct (k =? 0) eqn:hk0.
    + apply N.eqb_eq in hk0; subst k.
      destruct rs as [| [w | w | w | w] rs']; try reflexivity.
      cbn [encR]. replace (w + 1 + 1) with ((w + 1) + 1) by lia. rewrite encW01_succ; reflexivity.
    + destruct (k =? 2) eqn:hk2; [| reflexivity].
      apply N.eqb_eq in hk2; subst k.
      destruct rs as [| [w | w | w | w] rs']; try reflexivity.
      cbn [encR]. replace (w + 1 + 1) with ((w + 1) + 1) by lia. rewrite encW0111_succ; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition rpush1_1 (r : list RTok) : list RTok :=
  match r with Ro k :: rs => Ro (k + 1) :: rs | rs => Ro 0 :: rs end.

Lemma encR_rpush1_1 (r : list RTok) : encR (rpush1_1 r) = S1 >> encR r.
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpush1_1 encR]; try reflexivity.
  replace (k + 1 + 1) with ((k + 1) + 1) by lia. rewrite repBit_succ; reflexivity.
Qed.

Definition rpush1_2 (r : list RTok) : list RTok :=
  match r with Ro k :: rs => Ro (k + 2) :: rs | rs => Ro 1 :: rs end.

Lemma encR_rpush1_2 (r : list RTok) : encR (rpush1_2 r) = S1 >> S1 >> encR r.
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpush1_2 encR]; try reflexivity.
  replace (k + 2 + 1) with (2 + (k + 1)) by lia. rewrite repBit_add; reflexivity.
Qed.

Definition rpush1_3 (r : list RTok) : list RTok :=
  match r with Ro k :: rs => Ro (k + 3) :: rs | rs => Ro 2 :: rs end.

Lemma encR_rpush1_3 (r : list RTok) : encR (rpush1_3 r) = S1 >> S1 >> S1 >> encR r.
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpush1_3 encR]; try reflexivity.
  replace (k + 3 + 1) with (3 + (k + 1)) by lia. rewrite repBit_add; reflexivity.
Qed.

Definition rpush1_n (n : N) (r : list RTok) : list RTok :=
  match r with Ro k :: rs => Ro (k + n) :: rs | rs => Ro (n - 1) :: rs end.

Lemma encR_rpush1_n (n : N) (hn : 1 <= n) (r : list RTok) :
  encR (rpush1_n n r) = repBit true n (encR r).
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpush1_n encR];
    try (replace (n - 1 + 1) with n by lia; reflexivity).
  rewrite <- repBit_add; f_equal; lia.
Qed.

Definition rpushW0111_1 (r : list RTok) : list RTok :=
  match r with Rw0111 k :: rs => Rw0111 (k + 1) :: rs | rs => Rw0111 0 :: rs end.

Lemma encR_rpushW0111_1 (r : list RTok) :
  encR (rpushW0111_1 r) = S0 >> S1 >> S1 >> S1 >> encR r.
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpushW0111_1 encR]; try reflexivity.
  replace (k + 1 + 1) with ((k + 1) + 1) by lia. rewrite encW0111_succ; reflexivity.
Qed.

Definition rpushBool1 (b : bool) (r : list RTok) : list RTok :=
  if b then rpush1_1 r else rpush0_1 r.

Lemma encR_rpushBool1 (b : bool) (r : list RTok) :
  encR (rpushBool1 b r) = bitSym b >> encR r.
Proof. destruct b; [apply encR_rpush1_1 | apply encR_rpush0_1]. Qed.

Record BPopR := mkBPopR { bpr_b : bool; bpr_r : list RTok }.

Definition rpop1 (r : list RTok) : BPopR :=
  match r with
  | [] => mkBPopR false []
  | Rz k :: rs => mkBPopR false (if k =? 0 then rs else Rz (k - 1) :: rs)
  | Ro k :: rs => mkBPopR true (if k =? 0 then rs else Ro (k - 1) :: rs)
  | Rw01 k :: rs =>
    mkBPopR false (if k =? 0 then rpush1_1 rs else Ro 0 :: Rw01 (k - 1) :: rs)
  | Rw0111 k :: rs =>
    mkBPopR false (if k =? 0 then rpush1_3 rs else Ro 2 :: Rw0111 (k - 1) :: rs)
  end.

Lemma encR_rpop1 (r : list RTok) :
  encR r = bitSym (bpr_b (rpop1 r)) >> encR (bpr_r (rpop1 r)).
Proof.
  destruct r as [| [k | k | k | k] rs]; cbn [rpop1 encR bpr_b bpr_r].
  - apply default_eq_cons_zero.
  - destruct (k =? 0) eqn:hk; [apply N.eqb_eq in hk; subst k; reflexivity |].
    apply N.eqb_neq in hk; cbn [encR].
    replace (k + 1) with ((k - 1 + 1) + 1) by lia. rewrite repBit_succ; reflexivity.
  - destruct (k =? 0) eqn:hk; [apply N.eqb_eq in hk; subst k; reflexivity |].
    apply N.eqb_neq in hk; cbn [encR].
    replace (k + 1) with ((k - 1 + 1) + 1) by lia. rewrite repBit_succ; reflexivity.
  - destruct (k =? 0) eqn:hk.
    + apply N.eqb_eq in hk; subst k; cbn [encW01 N.iter Pos.iter bitSym].
      rewrite encR_rpush1_1; reflexivity.
    + apply N.eqb_neq in hk; cbn [encR].
      replace (k + 1) with ((k - 1 + 1) + 1) by lia. rewrite encW01_succ; reflexivity.
  - destruct (k =? 0) eqn:hk.
    + apply N.eqb_eq in hk; subst k; cbn [encW0111 N.iter Pos.iter bitSym].
      rewrite encR_rpush1_3; reflexivity.
    + apply N.eqb_neq in hk; cbn [encR].
      replace (k + 1) with ((k - 1 + 1) + 1) by lia. rewrite encW0111_succ; reflexivity.
Qed.

(* ========================================================================= *)
(* Section 2: CoreState, stepRLE, Gliders, UList, PsiReach, CoreK, Cascades  *)
(* ========================================================================= *)

Inductive Mode : Type := mA | mB | mC | mD | mE1 | mF.

Inductive CoreState : Type :=
| Crun (m : Mode) (l : list LTok) (r : list RTok)
| Chalt (l : list LTok) (r : list RTok).

Definition encodeCore (s : CoreState) : Q * tape :=
  match s with
  | Crun mA l r => encL l {{A}}> encR r
  | Crun mB l r => encL l {{B}}> encR r
  | Crun mC l r => encL l {{C}}> encR r
  | Crun mD l r => encL l {{D}}> encR r
  | Crun mE1 l r => encL l {{E}}> (S1 >> encR r)
  | Crun mF l r => encL l {{F}}> encR r
  | Chalt l r => encL l {{E}}> (S0 >> encR r)
  end.

Lemma halted_Chalt (l : list LTok) (r : list RTok) :
  halted tm (encodeCore (Chalt l r)).
Proof. reflexivity. Qed.

Lemma entry_steps : c0 -[ tm ]->* encodeCore (Crun mB [Lo 0] []).
Proof.
  unfold c0, tape0, q0, s0; cbn [BB62.q0 BB62.s0].
  replace (const S0 {{S0}} const S0) with (const S0 {{Streams.hd (S0 >> const S0)}} Streams.tl (S0 >> const S0)) by reflexivity.
  cbn [encodeCore encL encR repBit N.iter Pos.iter bitSym].
  tsteps.
Qed.

Lemma sweep_A1 (n : N) (sl sr : side) :
  (sl {{A}}> repBit true n sr) -[ tm ]->* (repBit false n sl {{A}}> sr).
Proof.
  revert sl sr; nind n; intros sl sr; [apply rs_refl |].
  rewrite !repBit_succ; cbn [bitSym].
  tstep1.
  rewrite <- repBit_snoc_false.
  apply IH.
Qed.

Lemma sweep_C0 (n : N) (sl sr : side) :
  (repBit false n sl <{{C}} sr) -[ tm ]->* (sl <{{C}} repBit true n sr).
Proof.
  revert sl sr; nind n; intros sl sr; [apply rs_refl |].
  rewrite !repBit_succ; cbn [bitSym].
  tstep1.
  rewrite <- repBit_snoc_true.
  apply IH.
Qed.

Definition stepRLE (s : CoreState) : CoreState :=
  match s with
  | Chalt l r => Chalt l r
  | Crun m l r =>
    match m with
    | mA =>
      match r with
      | Ro k :: rs => Crun mA (lpush0 (k + 1) l) rs
      | _ =>
        let p := rpop1 r in
        if bpr_b p then Crun mA (lpush0_1 l) (bpr_r p)
        else Crun mB (lpush1_1 l) (bpr_r p)
      end
    | mB =>
      let p := rpop1 r in
      if bpr_b p then
        let r1 := rpush0_1 (bpr_r p) in
        let lp := lpop1 l in
        if bpl_b lp then Crun mE1 (bpl_l lp) r1
        else Chalt (bpl_l lp) r1
      else Crun mC (lpush0_1 l) (bpr_r p)
    | mC =>
      let p := rpop1 r in
      if bpr_b p then
        let lp := lpop1 l in
        Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush0_1 (bpr_r p)))
      else
        let zr := lpopZRun l in
        let lp := lpop1 (zr_l zr) in
        Crun mC (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_n (zr_n zr + 1) (bpr_r p)))
    | mD =>
      let p := rpop1 r in
      if bpr_b p then
        let lp := lpop1 l in
        Crun mF (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (bpr_r p)))
      else Crun mA (lpush1_1 l) (bpr_r p)
    | mE1 =>
      let lp := lpop1 l in
      Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 r))
    | mF =>
      let lp := lpop1 l in
      let rp := rpop1 r in
      if bpr_b rp then Crun mB (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (bpr_r rp)))
      else Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (bpr_r rp)))
    end
  end.

Lemma mA_rpop1_sound (l : list LTok) (r : list RTok) :
  encodeCore (Crun mA l r) -[ tm ]->*
    encodeCore (let p := rpop1 r in
                if bpr_b p then Crun mA (lpush0_1 l) (bpr_r p)
                else Crun mB (lpush1_1 l) (bpr_r p)).
Proof.
  cbn [encodeCore]. rewrite (encR_rpop1 r).
  destruct (bpr_b (rpop1 r)); cbn [encodeCore bitSym].
  - rewrite encL_lpush0_1; tsteps.
  - rewrite encL_lpush1_1; tsteps.
Qed.

Lemma stepRLE_sound (s : CoreState) :
  encodeCore s -[ tm ]->* encodeCore (stepRLE s).
Proof.
  destruct s as [m l r | l r]; [| apply rs_refl].
  destruct m.
  - (* mA *)
    destruct r as [| [k | k | k | k] rs]; try apply mA_rpop1_sound.
    cbn [stepRLE encodeCore encR].
    rewrite encL_lpush0 by lia.
    apply sweep_A1.
  - (* mB *)
    cbn [stepRLE encodeCore]; rewrite (encR_rpop1 r).
    destruct (bpr_b (rpop1 r)); cbn [bitSym].
    + rewrite (encL_lpop1 l).
      destruct (bpl_b (lpop1 l)); cbn [encodeCore bitSym];
        rewrite encR_rpush0_1; tsteps.
    + cbn [encodeCore]; rewrite encL_lpush0_1; tsteps.
  - (* mC *)
    cbn [stepRLE encodeCore]; rewrite (encR_rpop1 r).
    destruct (bpr_b (rpop1 r)); cbn [encodeCore bitSym].
    + rewrite (encL_lpop1 l), encR_rpushBool1, encR_rpush0_1; tsteps.
    + rewrite (encL_lpopZRun l), (encL_lpop1 (zr_l (lpopZRun l))),
              encR_rpushBool1, encR_rpush1_n by lia.
      tstep1.
      eapply rs_trans; [apply sweep_C0 |].
      rewrite repBit_snoc_true, (repBit_succ true), cfg_L_cons; cbn [bitSym].
      apply rs_refl.
  - (* mD *)
    cbn [stepRLE encodeCore]; rewrite (encR_rpop1 r).
    destruct (bpr_b (rpop1 r)); cbn [encodeCore bitSym].
    + rewrite (encL_lpop1 l), encR_rpushBool1, encR_rpush1_1; tsteps.
    + rewrite encL_lpush1_1; tsteps.
  - (* mE1 *)
    cbn [stepRLE encodeCore]; rewrite (encL_lpop1 l), encR_rpushBool1, encR_rpush1_1; tsteps.
  - (* mF *)
    cbn [stepRLE encodeCore]; rewrite (encL_lpop1 l), (encR_rpop1 r).
    destruct (bpr_b (rpop1 r)); cbn [encodeCore bitSym];
      rewrite encR_rpushBool1, encR_rpush1_1; tsteps.
Qed.

Definition stepUntilAD_step (s : CoreState) : StepRes CoreState :=
  match s with
  | Crun mA _ _ | Crun mD _ _ | Chalt _ _ => mkStepRes true s
  | _ => mkStepRes false (stepRLE s)
  end.

Definition stepRLE_until_AD (p : positive) (s : CoreState) : CoreState :=
  sr_val (runPos p stepUntilAD_step s).

Lemma stepRLE_until_AD_sound (p : positive) (s : CoreState) :
  encodeCore s -[ tm ]->* encodeCore (stepRLE_until_AD p s).
Proof.
  refine (runPos_rel (fun s1 s2 => encodeCore s1 -[ tm ]->* encodeCore s2)
            (fun _ _ _ => rs_trans) stepUntilAD_step _ p s).
  intro x; destruct x as [[| | | | |] l r | l r]; cbn [stepUntilAD_step sr_val];
    try apply rs_refl; apply stepRLE_sound.
Qed.

(* Gliders G1, G2, G3 *)
Lemma g1_step (sl sr : side) :
  (sl {{D}}> (S0 >> S0 >> S0 >> S1 >> sr)) -[ tm ]->*
    ((S1 >> S1 >> sl) {{D}}> (S0 >> S0 >> sr)).
Proof. tsteps. Qed.

Lemma g1_run (t : N) (sl sr : side) :
  (sl {{D}}> (S0 >> S0 >> encW01 t sr)) -[ tm ]->*
    ((repBit true (2 * t) sl) {{D}}> (S0 >> S0 >> sr)).
Proof.
  revert sl sr; nind t; intros sl sr; [apply rs_refl |].
  rewrite encW01_succ.
  eapply rs_trans; [apply g1_step |].
  eapply rs_trans; [apply IH |].
  replace (2 * (t + 1)) with (2 * t + 2) by lia.
  rewrite repBit_add; apply rs_refl.
Qed.

Lemma g3_step (sl sr : side) :
  ((S1 >> S1 >> S1 >> S1 >> sl) {{D}}> (S1 >> S1 >> sr)) -[ tm ]->*
    (sl {{D}}> (S1 >> S1 >> S0 >> S1 >> S1 >> S1 >> sr)).
Proof. tsteps. Qed.

Lemma g3_run (t : N) (sl sr : side) :
  ((repBit true (4 * t) sl) {{D}}> (S1 >> S1 >> sr)) -[ tm ]->*
    (sl {{D}}> (S1 >> S1 >> encW0111 t sr)).
Proof.
  revert sl sr; nind t; intros sl sr; [apply rs_refl |].
  replace (4 * (t + 1)) with (4 + 4 * t) by lia.
  rewrite repBit_add; cbn [repBit N.iter Pos.iter bitSym].
  eapply rs_trans; [apply g3_step |].
  eapply rs_trans; [apply IH |].
  replace (encW0111 (t + 1) sr) with (encW0111 t (encW0111 1 sr)) by (symmetry; apply encW0111_add).
  apply rs_refl.
Qed.

Lemma g2_step (sl sr : side) :
  (sl {{A}}> (S1 >> S0 >> S0 >> S1 >> S0 >> S1 >> S1 >> S1 >> sr)) -[ tm ]->*
    ((S1 >> S1 >> S1 >> S1 >> sl) {{A}}> (S1 >> S0 >> S0 >> S1 >> sr)).
Proof. tsteps. Qed.

Lemma g2_run (t : N) (sl sr : side) :
  (sl {{A}}> (S1 >> S0 >> S0 >> S1 >> encW0111 t sr)) -[ tm ]->*
    ((repBit true (4 * t) sl) {{A}}> (S1 >> S0 >> S0 >> S1 >> sr)).
Proof.
  revert sl sr; nind t; intros sl sr; [apply rs_refl |].
  rewrite encW0111_succ.
  eapply rs_trans; [apply g2_step |].
  eapply rs_trans; [apply IH |].
  replace (4 * (t + 1)) with (4 * t + 4) by lia.
  rewrite repBit_add; apply rs_refl.
Qed.

(* UList & ustepCore0 & ustepPsi *)
Inductive UList : Type :=
| Unil
| Ucons (u c : N) (tl : UList).

Definition encUTok (u : N) (rest : side) : side :=
  S0 >> repBit true (2 * u + 1) rest.

Definition repUTok (u n : N) (rest : side) : side :=
  N.iter n (encUTok u) rest.

Lemma repUTok_0 (u : N) (rest : side) : repUTok u 0 rest = rest.
Proof. reflexivity. Qed.

Lemma repUTok_succ (u n : N) (rest : side) :
  repUTok u (n + 1) rest = encUTok u (repUTok u n rest).
Proof. unfold repUTok; apply N_iter_succ_r. Qed.

Lemma repUTok_add (u m n : N) (rest : side) :
  repUTok u (m + n) rest = repUTok u m (repUTok u n rest).
Proof. unfold repUTok; apply N_iter_add. Qed.

Lemma repUTok_snoc (u n : N) (x : side) :
  repUTok u n (encUTok u x) = encUTok u (repUTok u n x).
Proof. unfold repUTok; apply N_iter_snoc. Qed.

Lemma repUTok_zero_eq_encW01 (n : N) (sr : side) :
  repUTok 0 n sr = encW01 n sr.
Proof.
  nind n; [reflexivity |].
  rewrite repUTok_succ, encW01_succ, IH. reflexivity.
Qed.

Lemma repUTok_one_eq_encW0111 (n : N) (sr : side) :
  repUTok 1 n sr = encW0111 n sr.
Proof.
  nind n; [reflexivity |].
  rewrite repUTok_succ, encW0111_succ, IH. reflexivity.
Qed.

Fixpoint encU (us : UList) (rest : side) : side :=
  match us with
  | Unil => rest
  | Ucons u c tl => repUTok u (c + 1) (encU tl rest)
  end.

Definition upush (u n : N) (xs : UList) : UList :=
  if n =? 0 then xs
  else
    let m := n - 1 in
    match xs with
    | Unil => Ucons u m Unil
    | Ucons u' c' tl =>
      if u =? u' then Ucons u (m + 1 + c') tl
      else Ucons u m (Ucons u' c' tl)
    end.

Lemma encU_upush (u n : N) (xs : UList) (rest : side) :
  encU (upush u n xs) rest = repUTok u n (encU xs rest).
Proof.
  unfold upush. destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct xs as [| u' c' tl]; cbn [encU].
    + replace (n - 1 + 1) with n by lia; reflexivity.
    + destruct (u =? u') eqn:heq; cbn [encU].
      * apply N.eqb_eq in heq; subst u'.
        rewrite <- repUTok_add; f_equal; lia.
      * replace (n - 1 + 1) with n by lia; reflexivity.
Qed.

Fixpoint uappend (xs ys : UList) : UList :=
  match xs with
  | Unil => ys
  | Ucons u c tl => upush u (c + 1) (uappend tl ys)
  end.

Lemma encU_uappend (xs ys : UList) (rest : side) :
  encU (uappend xs ys) rest = encU xs (encU ys rest).
Proof.
  induction xs as [| u c tl IH]; [reflexivity |].
  cbn [uappend encU]. rewrite encU_upush, IH. reflexivity.
Qed.

Lemma encU_cons_split (u cx : N) (tl : UList) (rrem : side) :
  encU (Ucons u cx tl) rrem =
    encUTok u (encU (if cx =? 0 then tl else Ucons u (cx - 1) tl) rrem).
Proof.
  cbn [encU]. destruct (cx =? 0) eqn:hc0.
  - apply N.eqb_eq in hc0; subst cx; reflexivity.
  - apply N.eqb_neq in hc0; cbn [encU].
    replace (cx + 1) with ((cx - 1 + 1) + 1) by lia.
    rewrite repUTok_succ; reflexivity.
Qed.

Record UPrefRes := mkUPref { up_u : UList; up_r : list RTok }.

Fixpoint extractUPrefixR (r : list RTok) : UPrefRes :=
  match r with
  | Rw01 k :: rs =>
    let res := extractUPrefixR rs in mkUPref (upush 0 (k + 1) (up_u res)) (up_r res)
  | Rw0111 k :: rs =>
    let res := extractUPrefixR rs in mkUPref (upush 1 (k + 1) (up_u res)) (up_r res)
  | Rz k :: rs =>
    if k =? 0 then
      match rs with
      | Ro c1 :: rs2 =>
        if c1 mod 2 =? 0 then
          let res := extractUPrefixR rs2 in mkUPref (upush (c1 / 2) 1 (up_u res)) (up_r res)
        else mkUPref Unil r
      | _ => mkUPref Unil r
      end
    else mkUPref Unil r
  | _ => mkUPref Unil r
  end.

Lemma encR_extractUPrefixR_len (n : nat) :
  forall r : list RTok, (length r <= n)%nat ->
    encR r = encU (up_u (extractUPrefixR r)) (encR (up_r (extractUPrefixR r))).
Proof.
  induction n as [| n' IH]; intros r hlen.
  - destruct r; [reflexivity | cbn in hlen; lia].
  - destruct r as [| [k | k | k | k] rs]; try reflexivity.
    + cbn [extractUPrefixR]. destruct (k =? 0) eqn:hk0; [| reflexivity].
      apply N.eqb_eq in hk0; subst k.
      destruct rs as [| [c1 | c1 | c1 | c1] rs2]; try reflexivity.
      destruct (c1 mod 2 =? 0) eqn:hm; [| reflexivity].
      apply N.eqb_eq in hm.
      cbn [up_u up_r encR]. rewrite encU_upush, <- IH by (cbn in hlen; lia).
      change (repBit false (0 + 1) (repBit true (c1 + 1) (encR rs2)))
        with (S0 >> repBit true (c1 + 1) (encR rs2)).
      unfold repUTok, encUTok; cbn [N.iter Pos.iter].
      replace (2 * (c1 / 2) + 1) with (c1 + 1) by lia. reflexivity.
    + cbn [extractUPrefixR up_u up_r encR].
      rewrite encU_upush; rewrite <- IH by (cbn in hlen; lia); reflexivity.
    + cbn [extractUPrefixR up_u up_r encR].
      rewrite encU_upush; rewrite <- IH by (cbn in hlen; lia); reflexivity.
Qed.

Lemma encR_extractUPrefixR (r : list RTok) :
  encR r = encU (up_u (extractUPrefixR r)) (encR (up_r (extractUPrefixR r))).
Proof. exact (encR_extractUPrefixR_len (length r) r (Nat.le_refl _)). Qed.

Definition rpushUTokRun (u n : N) (r : list RTok) : list RTok :=
  N.iter n (fun s => rpushBit false 1 (rpushBit true (2 * u + 1) s)) r.

Lemma encR_rpushUTokRun (u n : N) (r : list RTok) :
  encR (rpushUTokRun u n r) = repUTok u n (encR r).
Proof.
  nind n; [reflexivity |].
  unfold rpushUTokRun.
  rewrite (N_iter_succ_r n (fun s => rpushBit false 1 (rpushBit true (2 * u + 1) s)) r).
  rewrite !encR_rpushBit, repUTok_succ, <- IH. reflexivity.
Qed.

Fixpoint restoreUR (us : UList) (r : list RTok) : list RTok :=
  match us with
  | Unil => r
  | Ucons u c tl =>
    let r' := restoreUR tl r in
    if u =? 0 then rpushW01 (c + 1) r'
    else if u =? 1 then rpushW0111 (c + 1) r'
    else rpushUTokRun u (c + 1) r'
  end.

Lemma encR_restoreUR (us : UList) (r : list RTok) :
  encR (restoreUR us r) = encU us (encR r).
Proof.
  induction us as [| u c tl IH]; [reflexivity |].
  cbn [restoreUR encU].
  destruct (u =? 0) eqn:hu0.
  - apply N.eqb_eq in hu0; subst u.
    rewrite encR_rpushW01, IH; reflexivity.
  - destruct (u =? 1) eqn:hu1.
    + apply N.eqb_eq in hu1; subst u.
      rewrite encR_rpushW0111, IH; reflexivity.
    + rewrite encR_rpushUTokRun, IH; reflexivity.
Qed.

(* Micro-sweeps for ustepCore0 *)
Lemma shift_01_step (sl sr : side) :
  ((S0 >> sl) {{A}}> (S0 >> S1 >> sr)) -[ tm ]->*
    ((S0 >> S1 >> sl) {{A}}> (S0 >> sr)).
Proof. tsteps. Qed.

Lemma shift_01_run (n : N) (sl sr : side) :
  ((S0 >> sl) {{A}}> (S0 >> repBit true n sr)) -[ tm ]->*
    ((S0 >> repBit true n sl) {{A}}> (S0 >> sr)).
Proof.
  revert sl sr; nind n; intros sl sr; [apply rs_refl |].
  rewrite !repBit_succ; cbn [bitSym].
  eapply rs_trans; [apply shift_01_step |].
  rewrite <- repBit_snoc_true. apply IH.
Qed.

Lemma eat_zero_step (sl sr : side) :
  (sl {{A}}> (S0 >> encUTok 0 sr)) -[ tm ]->*
    ((S1 >> S1 >> sl) {{A}}> (S0 >> sr)).
Proof. unfold encUTok, repBit; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Lemma eat_zero_run (c : N) (sl sr : side) :
  (sl {{A}}> (S0 >> repUTok 0 c sr)) -[ tm ]->*
    ((repBit true (2 * c) sl) {{A}}> (S0 >> sr)).
Proof.
  revert sl sr; nind c; intros sl sr; [apply rs_refl |].
  rewrite repUTok_succ.
  eapply rs_trans; [apply eat_zero_step |].
  eapply rs_trans; [apply IH |].
  replace (2 * (c + 1)) with (2 * c + 2) by lia.
  rewrite repBit_add; apply rs_refl.
Qed.

Lemma bounce_e_step (sl sr : side) :
  ((repBit true 4 sl) <{{E}} sr) -[ tm ]->* (sl <{{E}} encUTok 1 sr).
Proof. unfold repBit, encUTok; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Lemma bounce_e_quads (m : N) (sl sr : side) :
  ((repBit true (4 * m) sl) <{{E}} sr) -[ tm ]->* (sl <{{E}} repUTok 1 m sr).
Proof.
  revert sl sr; nind m; intros sl sr; [apply rs_refl |].
  replace (4 * (m + 1)) with (4 + 4 * m) by lia.
  rewrite repBit_add.
  eapply rs_trans; [apply bounce_e_step |].
  rewrite repUTok_succ, <- repUTok_snoc. apply IH.
Qed.

Lemma bounce_d_step (sl sy : side) :
  ((repBit true 4 sl) <{{D}} (S1 >> sy)) -[ tm ]->*
    (sl <{{D}} (S1 >> encUTok 1 sy)).
Proof. unfold repBit, encUTok; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Lemma bounce_d_quads (q : N) (sl sy : side) :
  ((repBit true (4 * q) sl) <{{D}} (S1 >> sy)) -[ tm ]->*
    (sl <{{D}} (S1 >> repUTok 1 q sy)).
Proof.
  revert sl sy; nind q; intros sl sy; [apply rs_refl |].
  replace (4 * (q + 1)) with (4 + 4 * q) by lia.
  rewrite repBit_add.
  eapply rs_trans; [apply bounce_d_step |].
  rewrite repUTok_succ, <- repUTok_snoc. apply IH.
Qed.

Definition loopCfg (z1 j : N) (l_sub sx : side) : Q * tape :=
  (repBit true (2 * z1) (S0 >> repBit true (2 * j + 1) l_sub)) {{A}}> (S0 >> sx).

Lemma hit_pos_entry (n x1 : N) (l0 sx : side) :
  ((repBit true n l0) {{A}}> (S0 >> encUTok (x1 + 1) sx)) -[ tm ]->*
    ((repBit true (n + 3) l0) <{{E}} encUTok x1 sx).
Proof.
  replace (n + 3) with (3 + n) by lia.
  rewrite repBit_add; cbn [repBit N.iter Pos.iter bitSym].
  unfold encUTok. replace (2 * (x1 + 1) + 1) with (2 + (2 * x1 + 1)) by lia.
  rewrite repBit_add; cbn [repBit N.iter Pos.iter bitSym].
  tsteps.
Qed.

Lemma odd_mid_bridge (l_j sr : side) :
  ((repBit true 3 (S0 >> l_j)) <{{E}} sr) -[ tm ]->*
    ((S1 >> l_j) <{{D}} (S1 >> encUTok 0 sr)).
Proof. unfold repBit, encUTok; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Lemma odd_exit_even (l_sub sr : side) :
  ((repBit true 2 l_sub) <{{D}} (S1 >> sr)) -[ tm ]->*
    (l_sub <{{B}} repBit true 3 sr).
Proof. unfold repBit; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Lemma odd_exit_odd (l_sub sr : side) :
  ((repBit true 4 l_sub) <{{D}} (S1 >> sr)) -[ tm ]->*
    (l_sub <{{D}} (S1 >> encUTok 1 sr)).
Proof. apply bounce_d_step. Qed.

Lemma odd_z_finish_even (m q x1 : N) (l_sub sx : side) :
  loopCfg (2 * m) (2 * q) l_sub (encUTok (x1 + 1) sx) -[ tm ]->*
    (l_sub <{{B}} repBit true 3 (repUTok 1 q (encUTok 0 (repUTok 1 m (encUTok x1 sx))))).
Proof.
  unfold loopCfg.
  eapply rs_trans; [apply hit_pos_entry |].
  replace (2 * (2 * m) + 3) with (4 * m + 3) by lia.
  rewrite repBit_add.
  eapply rs_trans; [apply bounce_e_quads |].
  eapply rs_trans; [apply odd_mid_bridge |].
  change (S1 >> repBit true (2 * (2 * q) + 1) l_sub) with (repBit true 1 (repBit true (2 * (2 * q) + 1) l_sub)).
  rewrite <- repBit_add. replace (1 + (2 * (2 * q) + 1)) with (4 * q + 2) by lia.
  rewrite repBit_add.
  eapply rs_trans; [apply bounce_d_quads |].
  apply odd_exit_even.
Qed.

Lemma odd_z_finish_odd (m q x1 : N) (l_sub sx : side) :
  loopCfg (2 * m) (2 * q + 1) l_sub (encUTok (x1 + 1) sx) -[ tm ]->*
    (l_sub <{{D}} (S1 >> repUTok 1 (q + 1) (encUTok 0 (repUTok 1 m (encUTok x1 sx))))).
Proof.
  unfold loopCfg.
  eapply rs_trans; [apply hit_pos_entry |].
  replace (2 * (2 * m) + 3) with (4 * m + 3) by lia.
  rewrite repBit_add.
  eapply rs_trans; [apply bounce_e_quads |].
  eapply rs_trans; [apply odd_mid_bridge |].
  change (S1 >> repBit true (2 * (2 * q + 1) + 1) l_sub) with (repBit true 1 (repBit true (2 * (2 * q + 1) + 1) l_sub)).
  rewrite <- repBit_add. replace (1 + (2 * (2 * q + 1) + 1)) with (4 * q + 4) by lia.
  rewrite repBit_add.
  eapply rs_trans; [apply bounce_d_quads |].
  rewrite repUTok_succ.
  apply odd_exit_odd.
Qed.

Lemma even_mid_bridge (l_j sy : side) :
  ((repBit true 5 (S0 >> l_j)) <{{E}} sy) -[ tm ]->*
    ((S0 >> S1 >> l_j) {{A}}> encUTok 1 sy).
Proof. unfold repBit, encUTok; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Lemma even_z_fold (k1 j x1 : N) (l_sub sx : side) :
  loopCfg (2 * k1 + 1) j l_sub (encUTok (x1 + 1) sx) -[ tm ]->*
    loopCfg 0 (j + 2) l_sub (repUTok 1 k1 (encUTok x1 sx)).
Proof.
  unfold loopCfg.
  eapply rs_trans; [apply hit_pos_entry |].
  replace (2 * (2 * k1 + 1) + 3) with (4 * k1 + 5) by lia.
  rewrite repBit_add.
  eapply rs_trans; [apply bounce_e_quads |].
  eapply rs_trans; [apply even_mid_bridge |].
  unfold encUTok at 1.
  eapply rs_trans; [apply (shift_01_run 3) |].
  change (S1 >> repBit true (2 * j + 1) l_sub) with (repBit true 1 (repBit true (2 * j + 1) l_sub)).
  rewrite <- !repBit_add. replace (3 + 1 + (2 * j + 1)) with (2 * (j + 2) + 1) by lia.
  apply rs_refl.
Qed.

Lemma even_z_one_run (c j : N) (l_sub sx : side) :
  loopCfg 1 j l_sub (repUTok 1 c sx) -[ tm ]->* loopCfg 1 (j + 2 * c) l_sub sx.
Proof.
  revert j; nind c; intro j.
  - replace (j + 2 * 0) with j by lia; apply rs_refl.
  - rewrite repUTok_succ.
    pose proof (even_z_fold 0 j 0 l_sub (repUTok 1 c sx)) as hf.
    replace (2 * 0 + 1) with 1 in hf by lia.
    replace (0 + 1) with 1 in hf by lia.
    rewrite repUTok_0 in hf.
    eapply rs_trans; [exact hf |].
    change (loopCfg 0 (j + 2) l_sub (encUTok 0 (repUTok 1 c sx)))
      with ((S0 >> repBit true (2 * (j + 2) + 1) l_sub) {{A}}> (S0 >> encUTok 0 (repUTok 1 c sx))).
    eapply rs_trans; [apply eat_zero_step |].
    replace (j + 2 * (c + 1)) with ((j + 2) + 2 * c) by lia.
    exact (IH (j + 2)).
Qed.

Inductive Core0Res : Type :=
| retB (out : UList)
| retD (out : UList).

Definition core0Finish (m j x1 : N) (rest : UList) : Core0Res :=
  let tail := upush 0 1 (upush 1 m (upush x1 1 rest)) in
  let q := j / 2 in
  if j mod 2 =? 0 then retB (upush 1 q tail)
  else retD (upush 1 (q + 1) tail).

Fixpoint core0Loop (z1 j : N) (us : UList) : option Core0Res :=
  match us with
  | Unil => None
  | Ucons u cx tl =>
    if u =? 0 then core0Loop (z1 + cx + 1) j tl
    else
      let x1 := u - 1 in
      let rest := if cx =? 0 then tl else Ucons u (cx - 1) tl in
      if z1 =? 1 then
        if x1 =? 0 then core0Loop 1 (j + 2 * (cx + 1)) tl
        else Some (core0Finish 0 (j + 2) (x1 - 1) rest)
      else if z1 mod 2 =? 1 then
        let m := z1 / 2 in
        if m =? 0 then None
        else
          let tail := upush 0 2 (upush 1 (m - 1) (upush x1 1 rest)) in
          let j2 := j + 2 in
          let qp := j2 / 2 in
          if j2 mod 2 =? 0 then Some (retB (upush 1 qp tail))
          else Some (retD (upush 1 (qp + 1) tail))
      else Some (core0Finish (z1 / 2) j x1 rest)
  end.

Definition ustepCore0 (us : UList) : option Core0Res :=
  match us with
  | Unil => None
  | Ucons u0 cu tl =>
    if u0 =? 0 then core0Loop cu 0 tl
    else
      let rest := if cu =? 0 then tl else Ucons u0 (cu - 1) tl in
      core0Loop 0 u0 rest
  end.

Definition core0ResCfg (res : Core0Res) (l_sub rrem : side) : Q * tape :=
  match res with
  | retB out => l_sub <{{B}} repBit true 3 (encU out rrem)
  | retD out => l_sub <{{D}} (S1 >> encU out rrem)
  end.

Lemma core0Finish_sound (m j x1 : N) (rest : UList) (l_sub rrem : side) :
  loopCfg (2 * m) j l_sub (encUTok (x1 + 1) (encU rest rrem)) -[ tm ]->*
    core0ResCfg (core0Finish m j x1 rest) l_sub rrem.
Proof.
  unfold core0Finish. destruct (j mod 2 =? 0) eqn:hj.
  - apply N.eqb_eq in hj.
    cbn [core0ResCfg]. rewrite !encU_upush; cbn [repUTok N.iter Pos.iter].
    replace j with (2 * (j / 2)) at 1 by lia.
    apply odd_z_finish_even.
  - apply N.eqb_neq in hj.
    cbn [core0ResCfg]. rewrite !encU_upush; cbn [repUTok N.iter Pos.iter].
    replace j with (2 * (j / 2) + 1) at 1 by lia.
    apply odd_z_finish_odd.
Qed.

Lemma core0Loop_sound (us : UList) :
  forall (z1 j : N) (res : Core0Res),
    core0Loop z1 j us = Some res ->
    forall l_sub rrem,
      loopCfg z1 j l_sub (encU us rrem) -[ tm ]->* core0ResCfg res l_sub rrem.
Proof.
  induction us as [| u cx tl IH]; intros z1 j res h l_sub rrem; [discriminate |].
  cbn [core0Loop] in h.
  destruct (u =? 0) eqn:hu0.
  - apply N.eqb_eq in hu0; subst u.
    cbn [encU]; unfold loopCfg.
    eapply rs_trans; [apply eat_zero_run |].
    rewrite <- repBit_add. replace (2 * (cx + 1) + 2 * z1) with (2 * (z1 + cx + 1)) by lia.
    apply IH; exact h.
  - apply N.eqb_neq in hu0.
    set (x1 := u - 1) in *.
    set (rest := if cx =? 0 then tl else Ucons u (cx - 1) tl) in *.
    rewrite encU_cons_split; fold rest.
    replace u with (x1 + 1) by lia.
    destruct (z1 =? 1) eqn:hz1.
    + apply N.eqb_eq in hz1; subst z1.
      destruct (x1 =? 0) eqn:hx1.
      * apply N.eqb_eq in hx1.
        assert (hu1 : u = 1) by (unfold x1 in hx1; lia). subst u.
        replace (x1 + 1) with 1 by (unfold x1; lia). unfold rest.
        rewrite <- (encU_cons_split 1 cx tl rrem); cbn [encU].
        eapply rs_trans; [apply even_z_one_run | apply IH; exact h].
      * apply N.eqb_neq in hx1. injection h as h; subst res.
        replace (x1 + 1) with ((x1 - 1 + 1) + 1) by lia.
        change 1 with (2 * 0 + 1) at 1.
        eapply rs_trans; [apply even_z_fold |].
        cbn [repUTok N.iter]. exact (core0Finish_sound 0 (j + 2) (x1 - 1) rest l_sub rrem).
    + apply N.eqb_neq in hz1.
      destruct (z1 mod 2 =? 1) eqn:hpar.
      * apply N.eqb_eq in hpar.
        destruct (z1 / 2 =? 0) eqn:hm0; [discriminate |].
        apply N.eqb_neq in hm0.
        replace z1 with (2 * (z1 / 2) + 1) by lia.
        eapply rs_trans; [apply even_z_fold |].
        replace (z1 / 2) with ((z1 / 2 - 1) + 1) at 1 by lia.
        rewrite repUTok_succ.
        change (encUTok 1) with (encUTok (0 + 1)).
        destruct ((j + 2) mod 2 =? 0) eqn:hj2; injection h as h; subst res;
          cbn [core0ResCfg]; rewrite !encU_upush; cbn [repUTok N.iter Pos.iter].
        -- apply N.eqb_eq in hj2.
           replace (j + 2) with (2 * ((j + 2) / 2)) at 1 by lia.
           exact (odd_z_finish_even 0 ((j + 2) / 2) 0 l_sub _).
        -- apply N.eqb_neq in hj2.
           replace (j + 2) with (2 * ((j + 2) / 2) + 1) at 1 by lia.
           exact (odd_z_finish_odd 0 ((j + 2) / 2) 0 l_sub _).
      * apply N.eqb_neq in hpar. injection h as h; subst res.
        replace z1 with (2 * (z1 / 2)) at 1 by lia.
        exact (core0Finish_sound (z1 / 2) j x1 rest l_sub rrem).
Qed.

Lemma ustepCore0_sound (us : UList) (res : Core0Res) (h : ustepCore0 us = Some res) :
  forall l_sub rrem,
    ((S0 >> l_sub) {{A}}> encU us rrem) -[ tm ]->* core0ResCfg res l_sub rrem.
Proof.
  intros l_sub rrem.
  destruct us as [| u0 cu tl]; [discriminate |].
  cbn [ustepCore0] in h.
  destruct (u0 =? 0) eqn:hu0.
  - apply N.eqb_eq in hu0; subst u0.
    cbn [encU]. replace (cu + 1) with (1 + cu) by lia.
    rewrite repUTok_add; cbn [repUTok N.iter Pos.iter encUTok repBit bitSym].
    eapply rs_trans; [apply shift_01_step |].
    eapply rs_trans; [apply eat_zero_run |].
    exact (core0Loop_sound tl cu 0 res h l_sub rrem).
  - rewrite encU_cons_split. unfold encUTok.
    eapply rs_trans; [apply shift_01_run |].
    exact (core0Loop_sound _ 0 u0 res h l_sub rrem).
Qed.

Definition ustepPsi (us : UList) : option UList :=
  match ustepCore0 us with
  | None => None
  | Some (retB out) => Some (upush 0 1 out)
  | Some (retD mid) =>
    match ustepCore0 mid with
    | Some (retD out) => Some out
    | _ => None
    end
  end.

Lemma psi_retB_bridge (sl sx : side) :
  ((S0 >> S0 >> sl) <{{B}} repBit true 3 sx) -[ tm ]->*
    (sl <{{D}} repBit true 3 (encUTok 0 sx)).
Proof. unfold repBit, encUTok; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Lemma psi_retD_mid_bridge (sl sx : side) :
  ((S0 >> S0 >> sl) <{{D}} (S1 >> sx)) -[ tm ]->*
    ((S0 >> S1 >> S0 >> sl) {{A}}> sx).
Proof. tsteps. Qed.

Lemma psi_retD_end_bridge (sl sy : side) :
  ((S1 >> S0 >> sl) <{{D}} (S1 >> sy)) -[ tm ]->*
    (sl <{{D}} repBit true 3 sy).
Proof. unfold repBit; cbn [N.iter Pos.iter bitSym]; tsteps. Qed.

Definition PsiStepSem (u1 u2 : UList) : Prop :=
  forall sl sr : side,
    ((repBit false 3 sl) {{A}}> encU u1 sr) -[ tm ]->* (sl <{{D}} repBit true 3 (encU u2 sr)).

Lemma ustepPsi_sound (u1 u2 : UList) (h : ustepPsi u1 = Some u2) :
  PsiStepSem u1 u2.
Proof.
  intros sl sr; unfold ustepPsi in h.
  cbn [repBit N.iter Pos.iter bitSym].
  destruct (ustepCore0 u1) as [[out | mid] |] eqn:hc1; [| | discriminate].
  - injection h as h; subst u2.
    eapply rs_trans; [exact (ustepCore0_sound u1 (retB out) hc1 (S0 >> S0 >> sl) sr) |].
    cbn [core0ResCfg]. rewrite encU_upush; cbn [repUTok N.iter Pos.iter].
    apply psi_retB_bridge.
  - destruct (ustepCore0 mid) as [[out0 | out] |] eqn:hc2; try discriminate.
    injection h as h; subst u2.
    eapply rs_trans; [exact (ustepCore0_sound u1 (retD mid) hc1 (S0 >> S0 >> sl) sr) |].
    cbn [core0ResCfg].
    eapply rs_trans; [apply psi_retD_mid_bridge |].
    eapply rs_trans; [exact (ustepCore0_sound mid (retD out) hc2 (S1 >> S0 >> sl) sr) |].
    cbn [core0ResCfg]. apply psi_retD_end_bridge.
Qed.

Lemma PsiStepSem_append {u1 u2 : UList} (h : PsiStepSem u1 u2) (tail : UList) :
  PsiStepSem (uappend u1 tail) (uappend u2 tail).
Proof.
  intros sl sr. rewrite !encU_uappend. apply h.
Qed.

Inductive PsiReach : N -> UList -> UList -> Prop :=
| pr_zero : forall u1 u2, (forall sr, encU u1 sr = encU u2 sr) -> PsiReach 0 u1 u2
| pr_succ : forall n u1 u2 u3, PsiStepSem u1 u2 -> PsiReach n u2 u3 -> PsiReach (n + 1) u1 u3.

Lemma PsiReach_refl (u : UList) : PsiReach 0 u u.
Proof. apply pr_zero; reflexivity. Qed.

Lemma PsiReach_step {u1 u2 : UList} (h : PsiStepSem u1 u2) : PsiReach 1 u1 u2.
Proof. change 1 with (0 + 1); eapply pr_succ; [exact h | apply PsiReach_refl]. Qed.

Lemma PsiReach_congr {n : N} {u1 u1' u2 u2' : UList}
  (h1 : forall sr, encU u1 sr = encU u1' sr)
  (h2 : forall sr, encU u2 sr = encU u2' sr)
  (hp : PsiReach n u1 u2) : PsiReach n u1' u2'.
Proof.
  revert u1' u2' h1 h2.
  induction hp as [u1 u2 h0 | n u1 um u2 hs _ IH]; intros u1' u2' h1 h2.
  - apply pr_zero; intro sr; rewrite <- h1, h0, h2; reflexivity.
  - eapply pr_succ.
    + intros sl sr; rewrite <- h1; apply hs.
    + apply IH; [reflexivity | exact h2].
Qed.

Lemma PsiReach_trans {n1 n2 : N} {u1 u2 u3 : UList}
  (h1 : PsiReach n1 u1 u2) (h2 : PsiReach n2 u2 u3) : PsiReach (n1 + n2) u1 u3.
Proof.
  induction h1 as [u1 u2 h0 | n u1 um u2 hs _ IH].
  - replace (0 + n2) with n2 by lia.
    exact (PsiReach_congr (fun sr => eq_sym (h0 sr)) (fun _ => eq_refl) h2).
  - replace (n + 1 + n2) with ((n + n2) + 1) by lia.
    eapply pr_succ; [exact hs | exact (IH h2)].
Qed.

Lemma PsiReach_zero_inv {u1 u2 : UList} (h : PsiReach 0 u1 u2) :
  forall sr, encU u1 sr = encU u2 sr.
Proof.
  inversion h as [? ? h0 heq | n ? ? ? ? ? heq]; [exact h0 | lia].
Qed.

Lemma PsiReach_succ_inv {n : N} {u1 u3 : UList} (h : PsiReach (n + 1) u1 u3) :
  exists u2, PsiStepSem u1 u2 /\ PsiReach n u2 u3.
Proof.
  inversion h as [? ? _ heq | n0 ? u2 ? hs hr heq]; [lia |].
  assert (n0 = n) by lia; subst n0.
  exists u2; split; assumption.
Qed.

Lemma PsiReach_split (a b : N) :
  forall {u1 u3 : UList},
    PsiReach (a + b) u1 u3 -> exists u2, PsiReach a u1 u2 /\ PsiReach b u2 u3.
Proof.
  nind a; intros u1 u3 h.
  - exists u1; split; [apply PsiReach_refl | replace b with (0 + b) by lia; exact h].
  - replace (a + 1 + b) with ((a + b) + 1) in h by lia.
    destruct (PsiReach_succ_inv h) as [um [hs hr]].
    destruct (IH um u3 hr) as [u2 [ha hb]].
    exists u2; split; [eapply pr_succ; [exact hs | exact ha] | exact hb].
Qed.

Lemma PsiReach_append {n : N} {u1 u2 : UList}
  (h : PsiReach n u1 u2) (tail : UList) :
  PsiReach n (uappend u1 tail) (uappend u2 tail).
Proof.
  induction h as [u1 u2 h0 | n u1 um u2 hs _ IH].
  - apply pr_zero; intro sr; rewrite !encU_uappend, h0; reflexivity.
  - eapply pr_succ; [exact (PsiStepSem_append hs tail) | exact IH].
Qed.

Lemma coreK_sound (d : N) :
  forall {u1 u2 : UList},
    PsiReach (2 ^ d) u1 u2 ->
    forall sl sr : side,
      ((repBit false (2 * d + 3) sl) {{A}}> encU u1 sr) -[ tm ]->*
        (sl <{{D}} repBit true (2 * d + 3) (encU u2 sr)).
Proof.
  nind d; intros u1 u2 h sl sr.
  - change (2 ^ 0) with (0 + 1) in h.
    destruct (PsiReach_succ_inv h) as [um [hs h0]].
    pose proof (PsiReach_zero_inv h0 sr) as heq.
    cbn [N.mul N.add] in *. rewrite <- heq. apply hs.
  - rewrite pow2_succ in h.
    replace (2 * 2 ^ d) with (2 ^ d + 2 ^ d) in h by lia.
    destruct (PsiReach_split (2 ^ d) (2 ^ d) h) as [um [h1 h2]].
    replace (2 * (d + 1) + 3) with ((2 * d + 3) + 2) by lia.
    rewrite (repBit_add false (2 * d + 3) 2).
    change (repBit false 2 sl) with (S0 >> S0 >> sl).
    eapply rs_trans; [exact (IH _ _ h1 (S0 >> S0 >> sl) sr) |].
    tstep1.
    eapply rs_trans; [apply sweep_A1 |].
    eapply rs_trans; [exact (IH _ _ h2 (S1 >> S0 >> sl) sr) |].
    replace ((2 * d + 3) + 2) with (2 + (2 * d + 3)) by lia.
    rewrite (repBit_add true 2 (2 * d + 3)).
    change (repBit true 2 (repBit true (2 * d + 3) (encU u2 sr)))
      with (S1 >> S1 >> repBit true (2 * d + 3) (encU u2 sr)).
    tsteps.
Qed.

Lemma mD_pair01_step (m : N) (sl sr : side) :
  ((S0 >> S1 >> sl) {{D}}> repBit true (2 * (m + 1)) sr) -[ tm ]->*
    (sl {{D}}> repBit true (2 * (m + 2)) sr).
Proof.
  replace (2 * (m + 1)) with (1 + (2 * m + 1)) by lia.
  replace (2 * (m + 2)) with (3 + (2 * m + 1)) by lia.
  rewrite (repBit_add true 1 (2 * m + 1)), (repBit_add true 3 (2 * m + 1)).
  change (repBit true 1 (repBit true (2 * m + 1) sr)) with (S1 >> repBit true (2 * m + 1) sr).
  change (repBit true 3 (repBit true (2 * m + 1) sr)) with (S1 >> S1 >> S1 >> repBit true (2 * m + 1) sr).
  tsteps.
Qed.

Lemma mD_pair00_step (m : N) {u1 u2 : UList} (hp : PsiReach (2 ^ m) u1 u2) (sl sr : side) :
  ((S0 >> S0 >> sl) {{D}}> repBit true (2 * (m + 1)) (encU u1 sr)) -[ tm ]->*
    (sl {{D}}> repBit true (2 * (m + 2)) (encU u2 sr)).
Proof.
  replace (2 * (m + 1)) with (1 + (2 * m + 1)) by lia.
  replace (2 * (m + 2)) with (1 + (2 * m + 3)) by lia.
  rewrite (repBit_add true 1 (2 * m + 1)), (repBit_add true 1 (2 * m + 3)).
  change (repBit true 1 (repBit true (2 * m + 1) (encU u1 sr)))
    with (S1 >> repBit true (2 * m + 1) (encU u1 sr)).
  change (repBit true 1 (repBit true (2 * m + 3) (encU u2 sr)))
    with (S1 >> repBit true (2 * m + 3) (encU u2 sr)).
  tstep1; tstep1; tstep1.
  change (S1 >> S1 >> repBit true (2 * m + 1) (encU u1 sr)) with (repBit true 2 (repBit true (2 * m + 1) (encU u1 sr))).
  rewrite <- (repBit_add true 2 (2 * m + 1)). replace (2 + (2 * m + 1)) with (2 * m + 3) by lia.
  eapply rs_trans; [apply sweep_A1 |].
  pose proof (coreK_sound m hp (S1 >> sl) sr) as hck.
  rewrite cfg_L_cons in hck. exact hck.
Qed.

Lemma mD_pairs_sweep_sound (len : N) :
  forall (val m : N) {u1 u2 : UList},
    val < 2 ^ len ->
    PsiReach (val * 2 ^ m) u1 u2 ->
    forall sl sr : side,
      ((encPairs len val sl) {{D}}> repBit true (2 * (m + 1)) (encU u1 sr)) -[ tm ]->*
        (sl {{D}}> repBit true (2 * (m + 1 + len)) (encU u2 sr)).
Proof.
  nind len; intros val m u1 u2 hlt hp sl sr.
  - change (2 ^ 0) with 1 in hlt. assert (val = 0) by lia; subst val.
    cbn [N.mul] in hp. rewrite (PsiReach_zero_inv hp sr), encPairs_0.
    replace (m + 1 + 0) with (m + 1) by lia. apply rs_refl.
  - rewrite pow2_succ in hlt.
    replace (m + 1 + (len + 1)) with ((m + 1) + 1 + len) by lia.
    rewrite encPairs_succ.
    destruct (val mod 2 =? 1) eqn:hmod.
    + apply N.eqb_eq in hmod.
      assert (hmul : val * 2 ^ m = 2 ^ m + (val / 2) * 2 ^ (m + 1)).
      { rewrite pow2_succ. assert (hv : val = 2 * (val / 2) + 1) by lia.
        set (vh := val / 2) in *; clearbody vh; set (pm := 2 ^ m) in *; clearbody pm; subst val; nia. }
      rewrite hmul in hp.
      destruct (PsiReach_split (2 ^ m) ((val / 2) * 2 ^ (m + 1)) hp) as [um [hp1 hp2]].
      eapply rs_trans; [exact (mD_pair00_step m hp1 _ sr) |].
      replace (m + 2) with (m + 1 + 1) by lia.
      exact (IH (val / 2) (m + 1) um u2 ltac:(lia) hp2 sl sr).
    + apply N.eqb_neq in hmod.
      assert (hmul : val * 2 ^ m = (val / 2) * 2 ^ (m + 1)).
      { rewrite pow2_succ. assert (hv : val = 2 * (val / 2)) by lia.
        set (vh := val / 2) in *; clearbody vh; set (pm := 2 ^ m) in *; clearbody pm; subst val; nia. }
      rewrite hmul in hp.
      eapply rs_trans; [apply mD_pair01_step |].
      replace (m + 2) with (m + 1 + 1) by lia.
      exact (IH (val / 2) (m + 1) u1 u2 ltac:(lia) hp sl sr).
Qed.

Lemma mA_cascade_gen (n : N) :
  forall (R_rem : N) {u1 u2 : UList},
    R_rem < 2 ^ n ->
    PsiReach R_rem u1 u2 ->
    forall l0 sr : side,
      ((repBit false (2 * n + 3) l0) {{A}}> encU u1 sr) -[ tm ]->*
        ((S0 >> S0 >> encPairs n (2 ^ n - 1 - R_rem) (S0 >> l0)) {{A}}> encU u2 sr).
Proof.
  nind n; intros R_rem u1 u2 hlt hp l0 sr.
  - change (2 ^ 0) with 1 in hlt. assert (R_rem = 0) by lia; subst R_rem.
    rewrite (PsiReach_zero_inv hp sr), encPairs_0; cbn [N.mul N.add repBit N.iter Pos.iter bitSym].
    apply rs_refl.
  - pose proof (pow2_pos n) as hpos.
    rewrite pow2_succ in hlt |- *.
    replace (2 * (n + 1) + 3) with ((2 * n + 3) + 2) by lia.
    rewrite (repBit_add false (2 * n + 3) 2).
    change (repBit false 2 l0) with (S0 >> S0 >> l0).
    destruct (R_rem <? 2 ^ n) eqn:hlt'.
    + apply N.ltb_lt in hlt'.
      pose proof (IH R_rem u1 u2 hlt' hp (S0 >> S0 >> l0) sr) as ih.
      replace (2 * 2 ^ n - 1 - R_rem) with ((2 ^ n - 1 - R_rem) + 2 ^ n) by lia.
      pose proof (encPairs_snoc n (2 ^ n - 1 - R_rem) true (S0 >> l0) ltac:(lia)) as hsnoc.
      rewrite hsnoc. exact ih.
    + apply N.ltb_ge in hlt'.
      set (R' := R_rem - 2 ^ n).
      assert (hR' : R' < 2 ^ n) by lia.
      replace R_rem with (2 ^ n + R') in hp by lia.
      destruct (PsiReach_split (2 ^ n) R' hp) as [um [hp1 hp2]].
      eapply rs_trans; [exact (coreK_sound n hp1 (S0 >> S0 >> l0) sr) |].
      tstep1.
      eapply rs_trans; [apply sweep_A1 |].
      eapply rs_trans; [exact (IH R' um u2 hR' hp2 (S1 >> S0 >> l0) sr) |].
      replace (2 * 2 ^ n - 1 - R_rem) with ((2 ^ n - 1 - R') + 0) by lia.
      pose proof (encPairs_snoc n (2 ^ n - 1 - R') false (S0 >> l0) ltac:(lia)) as hsnoc.
      rewrite hsnoc. apply rs_refl.
Qed.

Lemma mD_exhaust_cascade_sound (n_bits R_rem : N) {u1 u2 : UList}
  (hlt : R_rem < 2 ^ n_bits) (hp : PsiReach R_rem u1 u2) (sl sr : side) :
  ((S0 >> S0 >> sl) {{D}}> repBit true (2 * n_bits + 2) (encU u1 sr)) -[ tm ]->*
    ((encPairs (n_bits + 2) (1 + 2 * (2 ^ n_bits - 1 - R_rem)) sl) {{A}}> encU u2 sr).
Proof.
  pose proof (pow2_pos n_bits) as hpos.
  replace (2 * n_bits + 2) with (1 + (2 * n_bits + 1)) by lia.
  rewrite (repBit_add true 1 (2 * n_bits + 1)).
  change (repBit true 1 (repBit true (2 * n_bits + 1) (encU u1 sr)))
    with (S1 >> repBit true (2 * n_bits + 1) (encU u1 sr)).
  tstep1; tstep1; tstep1.
  change (S1 >> S1 >> repBit true (2 * n_bits + 1) (encU u1 sr))
    with (repBit true 2 (repBit true (2 * n_bits + 1) (encU u1 sr))).
  rewrite <- (repBit_add true 2 (2 * n_bits + 1)). replace (2 + (2 * n_bits + 1)) with (2 * n_bits + 3) by lia.
  eapply rs_trans; [apply sweep_A1 |].
  eapply rs_trans; [exact (mA_cascade_gen n_bits R_rem hlt hp (S1 >> sl) sr) |].
  pose proof (encPairs_snoc n_bits (2 ^ n_bits - 1 - R_rem) false sl ltac:(lia)) as hsnoc.
  set (v := 2 ^ n_bits - 1 - R_rem) in *.
  clearbody v.
  cbn in hsnoc.
  replace (v + 0) with v in hsnoc by lia.
  replace (n_bits + 2) with ((n_bits + 1) + 1) by (clear; lia).
  rewrite encPairs_succ.
  replace (1 + 2 * v) with (2 * v + 1) by (clear; lia).
  rewrite mod2_odd, div2_odd; cbn [N.eqb]. rewrite hsnoc. apply rs_refl.
Qed.

(* ========================================================================= *)
(* Section 3: Only01, ZChain, Parity Bisimulation, LCellSpec, DValid         *)
(* ========================================================================= *)

Lemma upush_upush_same (u a b : N) (w : UList) :
  upush u a (upush u b w) = upush u (a + b) w.
Proof.
  unfold upush.
  destruct (a =? 0) eqn:ha; [apply N.eqb_eq in ha; subst a; reflexivity |].
  destruct (b =? 0) eqn:hb; [apply N.eqb_eq in hb; subst b; replace (a + 0) with a by lia; rewrite ha; reflexivity |].
  apply N.eqb_neq in ha; apply N.eqb_neq in hb.
  assert (hab : a + b =? 0 = false) by (apply N.eqb_neq; lia).
  rewrite hab.
  destruct w as [| u' c' tl].
  - rewrite N.eqb_refl; f_equal; lia.
  - destruct (u =? u') eqn:hu; rewrite ?N.eqb_refl; f_equal; lia.
Qed.

Lemma uappend_upush (u n : N) (xs ys : UList) :
  uappend (upush u n xs) ys = upush u n (uappend xs ys).
Proof.
  unfold upush at 1.
  destruct (n =? 0) eqn:hn0; [apply N.eqb_eq in hn0; subst n; reflexivity |].
  apply N.eqb_neq in hn0.
  destruct xs as [| u' c' tl].
  - cbn [uappend]. replace (n - 1 + 1) with n by lia; reflexivity.
  - destruct (u =? u') eqn:hu.
    + apply N.eqb_eq in hu; subst u'.
      cbn [uappend]. rewrite upush_upush_same; f_equal; lia.
    + cbn [uappend]. replace (n - 1 + 1) with n by lia; reflexivity.
Qed.

Lemma uappend_assoc (u1 u2 u3 : UList) :
  uappend (uappend u1 u2) u3 = uappend u1 (uappend u2 u3).
Proof.
  induction u1 as [| u c tl IH]; [reflexivity |].
  cbn [uappend]. rewrite uappend_upush, IH; reflexivity.
Qed.

Lemma core0Loop_upush_zero (n : N) (w : UList) (z1 j : N) :
  core0Loop z1 j (upush 0 n w) = core0Loop (z1 + n) j w.
Proof.
  unfold upush. destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; replace (z1 + 0) with z1 by lia; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct w as [| u' c' tl]; [reflexivity |].
    destruct (0 =? u') eqn:hu.
    + apply N.eqb_eq in hu; subst u'; cbn [core0Loop N.eqb]; f_equal; lia.
    + cbn [core0Loop]; change (0 =? 0) with true; cbv iota.
      replace (z1 + (n - 1) + 1) with (z1 + n) by lia; reflexivity.
Qed.

Lemma core0Loop_upush_one (n : N) (w : UList) (j : N) :
  core0Loop 1 j (upush 1 n w) = core0Loop 1 (j + 2 * n) w.
Proof.
  unfold upush. destruct (n =? 0) eqn:hn0.
  - apply N.eqb_eq in hn0; subst n; replace (j + 2 * 0) with j by lia; reflexivity.
  - apply N.eqb_neq in hn0.
    destruct w as [| u' c' tl].
    + cbn [core0Loop N.eqb N.sub]; reflexivity.
    + destruct (1 =? u') eqn:hu.
      * apply N.eqb_eq in hu; subst u'.
        cbn [core0Loop]; change (1 =? 0) with false; change (1 - 1 =? 0) with true; change (1 =? 1) with true; cbv iota.
        f_equal; lia.
      * cbn [core0Loop]; change (1 =? 0) with false; change (1 - 1 =? 0) with true; change (1 =? 1) with true; cbv iota.
        replace (j + 2 * (n - 1 + 1)) with (j + 2 * n) by lia; reflexivity.
Qed.

Lemma ustepCore0_upush_zero (w : UList) :
  ustepCore0 (upush 0 1 w) = core0Loop 0 0 w.
Proof.
  destruct w as [| u' c' tl]; [reflexivity |].
  unfold upush; change (1 =? 0) with false; change (1 - 1) with 0; cbv iota zeta.
  destruct (0 =? u') eqn:hu.
  - apply N.eqb_eq in hu; subst u'; cbn [ustepCore0 core0Loop N.eqb]; f_equal; lia.
  - cbn [ustepCore0 N.eqb]; reflexivity.
Qed.

Lemma ustepCore0_upush_one (w : UList) :
  ustepCore0 (upush 1 1 w) = core0Loop 0 1 w.
Proof.
  destruct w as [| u' c' tl]; [reflexivity |].
  unfold upush; change (1 =? 0) with false; change (1 - 1) with 0; cbv iota zeta.
  destruct (1 =? u') eqn:hu.
  - apply N.eqb_eq in hu; subst u'; cbn [ustepCore0]; change (1 =? 0) with false; cbv iota.
    replace (0 + 1 + c' =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    replace (0 + 1 + c' - 1) with c' by lia; reflexivity.
  - cbn [ustepCore0 N.eqb]; reflexivity.
Qed.

Lemma core0Finish_even_odd (m q x1 : N) (rest : UList) :
  core0Finish m (2 * q) x1 rest = retB (upush 1 q (upush 0 1 (upush 1 m (upush x1 1 rest)))) /\
  core0Finish m (2 * q + 1) x1 rest =
    retD (upush 1 1 (upush 1 q (upush 0 1 (upush 1 m (upush x1 1 rest))))).
Proof.
  unfold core0Finish.
  rewrite mod2_even, div2_even, mod2_odd, div2_odd; cbn [N.eqb].
  split; [reflexivity |].
  rewrite upush_upush_same; do 2 f_equal; clear; lia.
Qed.

Lemma core0Loop_even_odd (w : UList) :
  forall (z1 q : N) (out : UList),
    core0Loop z1 (2 * q) w = Some (retB out) ->
    core0Loop z1 (2 * q + 1) w = Some (retD (upush 1 1 out)).
Proof.
  induction w as [| u cx tl IH]; intros z1 q out h; [discriminate |].
  cbn [core0Loop] in h |- *.
  destruct (u =? 0); [exact (IH _ _ _ h) |].
  destruct (z1 =? 1).
  - destruct (u - 1 =? 0).
    + replace (2 * q + 2 * (cx + 1)) with (2 * (q + cx + 1)) in h by (clear; lia).
      replace (2 * q + 1 + 2 * (cx + 1)) with (2 * (q + cx + 1) + 1) by (clear; lia).
      exact (IH _ _ _ h).
    + replace (2 * q + 2) with (2 * (q + 1)) in h by (clear; lia).
      replace (2 * q + 1 + 2) with (2 * (q + 1) + 1) by (clear; lia).
      destruct (core0Finish_even_odd 0 (q + 1) (u - 1 - 1)
                  (if cx =? 0 then tl else Ucons u (cx - 1) tl)) as [he ho].
      rewrite he in h; injection h as h; subst out.
      rewrite ho; reflexivity.
  - destruct (z1 mod 2 =? 1).
    + destruct (z1 / 2 =? 0); [discriminate |].
      replace (2 * q + 2) with (2 * (q + 1)) in h by (clear; lia).
      replace (2 * q + 1 + 2) with (2 * (q + 1) + 1) by (clear; lia).
      rewrite mod2_even, div2_even in h; cbn [N.eqb] in h.
      injection h as h; subst out.
      rewrite mod2_odd, div2_odd; cbn [N.eqb].
      rewrite upush_upush_same; do 3 f_equal; clear; lia.
    + destruct (core0Finish_even_odd (z1 / 2) q (u - 1)
                  (if cx =? 0 then tl else Ucons u (cx - 1) tl)) as [he ho].
      rewrite he in h; injection h as h; subst out.
      rewrite ho; reflexivity.
Qed.

Lemma core0Finish_uappend (m j x1 : N) (rest tail : UList) :
  core0Finish m j x1 (uappend rest tail) =
    match core0Finish m j x1 rest with
    | retB o => retB (uappend o tail)
    | retD o => retD (uappend o tail)
    end.
Proof.
  unfold core0Finish. destruct (j mod 2 =? 0); rewrite !uappend_upush; reflexivity.
Qed.

Lemma core0Loop_uappend (u : UList) :
  forall (tail : UList) (z1 j : N) (out : UList),
    core0Loop z1 j u = Some (retB out) ->
    core0Loop z1 j (uappend u tail) = Some (retB (uappend out tail)).
Proof.
  induction u as [| u0 cx tl IH]; intros tail z1 j out h; [discriminate |].
  cbn [core0Loop] in h.
  destruct (u0 =? 0) eqn:hu0.
  - apply N.eqb_eq in hu0; subst u0.
    cbn [uappend]. rewrite core0Loop_upush_zero.
    replace (z1 + (cx + 1)) with (z1 + cx + 1) by lia.
    exact (IH tail _ _ _ h).
  - pose proof (proj1 (N.eqb_neq u0 0) hu0) as hu0'.
    destruct ((z1 =? 1) && (u0 - 1 =? 0)) eqn:h11.
    + apply andb_prop in h11; destruct h11 as [hz1 hx1].
      rewrite hz1, hx1 in h.
      apply N.eqb_eq in hz1; apply N.eqb_eq in hx1.
      assert (u0 = 1) by lia; subst z1 u0.
      cbn [uappend]. rewrite core0Loop_upush_one.
      exact (IH tail 1 (j + 2 * (cx + 1)) out h).
    + set (rest := if cx =? 0 then tl else Ucons u0 (cx - 1) tl) in *.
      assert (hex : exists c' t',
                upush u0 (cx + 1) (uappend tl tail) = Ucons u0 c' t' /\
                (if c' =? 0 then t' else Ucons u0 (c' - 1) t') = uappend rest tail).
      { destruct (uappend tl tail) as [| u' c0 tl'] eqn:hw.
        - exists cx, Unil; split.
          + unfold upush; replace (cx + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
            replace (cx + 1 - 1) with cx by lia; reflexivity.
          + unfold rest; destruct (cx =? 0) eqn:hcx; [exact (eq_sym hw) |].
            cbn [uappend]; rewrite hw; unfold upush.
            apply N.eqb_neq in hcx.
            replace (cx - 1 + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
            replace (cx - 1 + 1 - 1) with (cx - 1) by lia; reflexivity.
        - unfold upush; replace (cx + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
          replace (cx + 1 - 1) with cx by lia.
          destruct (u0 =? u') eqn:hu'.
          + apply N.eqb_eq in hu'; subst u'.
            exists (cx + 1 + c0), tl'; split; [reflexivity |].
            replace (cx + 1 + c0 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
            unfold rest; destruct (cx =? 0) eqn:hcx.
            * apply N.eqb_eq in hcx; subst cx; rewrite hw; f_equal; lia.
            * apply N.eqb_neq in hcx; cbn [uappend]; rewrite hw; unfold upush.
              replace (cx - 1 + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
              rewrite N.eqb_refl; f_equal; lia.
          + exists cx, (Ucons u' c0 tl'); split; [reflexivity |].
            unfold rest; destruct (cx =? 0) eqn:hcx; [exact (eq_sym hw) |].
            apply N.eqb_neq in hcx; cbn [uappend]; rewrite hw; unfold upush.
            replace (cx - 1 + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
            rewrite hu'; f_equal; lia. }
      destruct hex as [c' [t' [hcons hrest]]].
      cbn [uappend]; rewrite hcons; cbn [core0Loop].
      rewrite hu0, hrest.
      destruct (z1 =? 1) eqn:hz1.
      * cbn [andb] in h11; rewrite h11 in h |- *.
        rewrite core0Finish_uappend. injection h as h; rewrite h; reflexivity.
      * destruct (z1 mod 2 =? 1).
        -- destruct (z1 / 2 =? 0); [discriminate |].
           destruct ((j + 2) mod 2 =? 0); [| discriminate].
           injection h as h; subst out; rewrite !uappend_upush; reflexivity.
        -- rewrite core0Finish_uappend. injection h as h; rewrite h; reflexivity.
Qed.

Fixpoint Only01 (u : UList) : Prop :=
  match u with
  | Unil => True
  | Ucons u0 _ tl => u0 <= 1 /\ Only01 tl
  end.

Lemma only01_upush (u n : N) (w : UList) (hu : u <= 1) (hw : Only01 w) :
  Only01 (upush u n w).
Proof.
  unfold upush. destruct (n =? 0); [exact hw |].
  destruct w as [| u' c' tl]; [exact (conj hu I) |].
  destruct (u =? u'); cbn [Only01]; [exact (conj hu (proj2 hw)) | exact (conj hu hw)].
Qed.

Lemma only01_uappend {u1 u2 : UList} (h1 : Only01 u1) (h2 : Only01 u2) :
  Only01 (uappend u1 u2).
Proof.
  induction u1 as [| u c tl IH]; [exact h2 |].
  destruct h1 as [hu htl]. cbn [uappend]. apply only01_upush; [exact hu | exact (IH htl)].
Qed.

Lemma core0Loop_only01 (w : UList) :
  forall (z1 j : N) (out : UList),
    Only01 w -> core0Loop z1 j w = Some (retB out) -> Only01 out.
Proof.
  induction w as [| u cx tl IH]; intros z1 j out hw h; [discriminate |].
  destruct hw as [hu htl]. cbn [core0Loop] in h.
  destruct (u =? 0) eqn:hu0; [exact (IH _ _ _ htl h) |].
  apply N.eqb_neq in hu0. assert (u = 1) by lia; subst u.
  assert (hrest : Only01 (if cx =? 0 then tl else Ucons 1 (cx - 1) tl)).
  { destruct (cx =? 0); [exact htl | exact (conj (N.le_refl 1) htl)]. }
  change (1 =? 0) with false in h; change (1 - 1) with 0 in h; change (0 =? 0) with true in h; cbv iota zeta in h.
  destruct (z1 =? 1).
  - exact (IH _ _ _ htl h).
  - destruct (z1 mod 2 =? 1).
    + destruct (z1 / 2 =? 0); [discriminate |].
      destruct ((j + 2) mod 2 =? 0); [| discriminate].
      injection h as h; subst out.
      repeat (apply only01_upush; [lia |]); exact hrest.
    + unfold core0Finish in h.
      destruct (j mod 2 =? 0); [| discriminate].
      injection h as h; subst out.
      repeat (apply only01_upush; [lia |]); exact hrest.
Qed.

Inductive ZChain : N -> UList -> UList -> Prop :=
| zc_zero : forall u, ZChain 0 u u
| zc_step : forall n u1 u2 u3,
    core0Loop 0 0 u1 = Some (retB u2) -> ZChain n u2 u3 -> ZChain (n + 1) u1 u3.

Lemma ZChain_zero_inv {u1 u2 : UList} (h : ZChain 0 u1 u2) : u1 = u2.
Proof. inversion h; [reflexivity | lia]. Qed.

Lemma ZChain_succ_inv {n : N} {u1 u3 : UList} (hc : ZChain (n + 1) u1 u3) :
  exists u2, core0Loop 0 0 u1 = Some (retB u2) /\ ZChain n u2 u3.
Proof.
  inversion hc as [? heq | n0 ? u2 ? hs hr heq]; [lia |].
  assert (n0 = n) by lia; subst n0.
  exists u2; split; assumption.
Qed.

Lemma ZChain_trans {m n : N} {u1 u2 u3 : UList}
  (h1 : ZChain m u1 u2) (h2 : ZChain n u2 u3) : ZChain (m + n) u1 u3.
Proof.
  induction h1 as [u | m u1 um u2 hs _ IH].
  - replace (0 + n) with n by lia; exact h2.
  - replace (m + 1 + n) with ((m + n) + 1) by lia.
    eapply zc_step; [exact hs | exact (IH h2)].
Qed.

Lemma ZChain_append {n : N} {u1 u2 : UList} (h : ZChain n u1 u2) (tail : UList) :
  ZChain n (uappend u1 tail) (uappend u2 tail).
Proof.
  induction h as [u | n u1 um u2 hs _ IH].
  - apply zc_zero.
  - eapply zc_step; [exact (core0Loop_uappend _ tail 0 0 _ hs) | exact IH].
Qed.

Lemma ZChain_det (a : N) :
  forall {b : N} {u1 u2 u3 : UList},
    ZChain (a + b) u1 u3 -> ZChain a u1 u2 -> ZChain b u2 u3.
Proof.
  nind a; intros b u1 u2 u3 h13 h12.
  - pose proof (ZChain_zero_inv h12); subst u2.
    replace b with (0 + b) by lia; exact h13.
  - replace (a + 1 + b) with ((a + b) + 1) in h13 by lia.
    destruct (ZChain_succ_inv h13) as [um1 [hs1 hr1]].
    destruct (ZChain_succ_inv h12) as [um2 [hs2 hr2]].
    rewrite hs1 in hs2; injection hs2 as heq; subst um2.
    exact (IH b um1 u2 u3 hr1 hr2).
Qed.

Lemma ZChain_split_last (n : N) :
  forall {u1 u3 : UList},
    ZChain (n + 1) u1 u3 -> exists u2, ZChain n u1 u2 /\ core0Loop 0 0 u2 = Some (retB u3).
Proof.
  nind n; intros u1 u3 h.
  - destruct (ZChain_succ_inv h) as [u2 [hs hr]].
    pose proof (ZChain_zero_inv hr); subst u2.
    exists u1; split; [apply zc_zero | exact hs].
  - destruct (ZChain_succ_inv h) as [um [hs hr]].
    destruct (IH um u3 hr) as [u2 [hc hlast]].
    exists u2; split; [eapply zc_step; [exact hs | exact hc] | exact hlast].
Qed.

Lemma ZChain_only01 {n : N} {u1 u2 : UList} (h01 : Only01 u1) (hc : ZChain n u1 u2) :
  Only01 u2.
Proof.
  induction hc as [u | n ua ub uc hs _ IH].
  - exact h01.
  - exact (IH (core0Loop_only01 ua 0 0 ub h01 hs)).
Qed.

Lemma ZChain_to_PsiReach_Z {n : N} {u1 u2 : UList} (hc : ZChain n u1 u2) :
  PsiReach n (upush 0 1 u1) (upush 0 1 u2).
Proof.
  induction hc as [u | n ua ub uc hs _ IH].
  - apply PsiReach_refl.
  - eapply pr_succ; [| exact IH].
    apply ustepPsi_sound. unfold ustepPsi.
    rewrite ustepCore0_upush_zero, hs; reflexivity.
Qed.

Lemma core0Loop_01 (w out : UList) (h : core0Loop 0 0 w = Some (retB out)) :
  core0Loop 0 1 w = Some (retD (upush 1 1 out)).
Proof. exact (core0Loop_even_odd w 0 0 out h). Qed.

Lemma ZChain_to_PsiReach_1_even (k : N) :
  forall {u1 u2 : UList},
    ZChain (2 * k) u1 u2 -> PsiReach k (upush 1 1 u1) (upush 1 1 u2).
Proof.
  nind k; intros u1 u2 hc.
  - pose proof (ZChain_zero_inv hc); subst u2; apply PsiReach_refl.
  - replace (2 * (k + 1)) with ((2 * k + 1) + 1) in hc by lia.
    destruct (ZChain_succ_inv hc) as [um1 [hs1 hr1]].
    destruct (ZChain_succ_inv hr1) as [um2 [hs2 hr2]].
    eapply pr_succ; [| exact (IH um2 u2 hr2)].
    apply ustepPsi_sound. unfold ustepPsi.
    rewrite ustepCore0_upush_one, (core0Loop_01 u1 um1 hs1),
            ustepCore0_upush_one, (core0Loop_01 um1 um2 hs2).
    reflexivity.
Qed.

(* Injectivity helpers *)
Lemma encUTok_inj (u : N) {x y : side} (h : encUTok u x = encUTok u y) : x = y.
Proof. exact (repBit_inj true (2 * u + 1) (cons_inj h)). Qed.

Lemma repUTok_inj (u n : N) {x y : side} :
  repUTok u n x = repUTok u n y -> x = y.
Proof.
  nind n; [exact (fun h => h) |].
  rewrite !repUTok_succ; intro h; apply IH; exact (encUTok_inj u h).
Qed.

Lemma encU_default_head (u : UList) : Streams.hd (encU u (const S0)) = S0.
Proof.
  destruct u as [| u0 c0 tl]; [reflexivity |].
  cbn [encU]. replace (c0 + 1) with ((c0) + 1) by lia.
  rewrite repUTok_succ; reflexivity.
Qed.

Lemma encUTok_zero_ne_one (u1 u2 : UList) :
  encUTok 0 (encU u1 (const S0)) <> encUTok 1 (encU u2 (const S0)).
Proof.
  intro h. unfold encUTok in h; cbn [N.mul N.add repBit N.iter Pos.iter bitSym] in h.
  apply cons_inj in h; apply cons_inj in h.
  apply (f_equal (@Streams.hd Sym)) in h; cbn [Streams.hd] in h.
  rewrite encU_default_head in h; discriminate.
Qed.

Lemma repUTok_one_enc0_inj (m : N) :
  forall (n : N) (u1 u2 : UList),
    repUTok 1 m (encUTok 0 (encU u1 (const S0))) =
      repUTok 1 n (encUTok 0 (encU u2 (const S0))) ->
    m = n.
Proof.
  nind m; intros n u1 u2 h.
  - destruct (n =? 0) eqn:hn0; [apply N.eqb_eq in hn0; symmetry; exact hn0 |].
    apply N.eqb_neq in hn0. exfalso.
    replace n with ((n - 1) + 1) in h by lia.
    rewrite repUTok_0, repUTok_succ in h.
    replace (repUTok 1 (n - 1) (encUTok 0 (encU u2 (const S0))))
      with (encU (upush 1 (n - 1) (upush 0 1 u2)) (const S0)) in h
      by (rewrite !encU_upush; reflexivity).
    exact (encUTok_zero_ne_one u1 _ h).
  - destruct (n =? 0) eqn:hn0.
    + apply N.eqb_eq in hn0; subst n; exfalso.
      rewrite repUTok_succ, repUTok_0 in h.
      replace (repUTok 1 m (encUTok 0 (encU u1 (const S0))))
        with (encU (upush 1 m (upush 0 1 u1)) (const S0)) in h
        by (rewrite !encU_upush; reflexivity).
      exact (encUTok_zero_ne_one u2 _ (eq_sym h)).
    + apply N.eqb_neq in hn0.
      replace n with ((n - 1) + 1) in h by lia.
      rewrite !repUTok_succ in h.
      apply encUTok_inj in h.
      pose proof (IH (n - 1) u1 u2 h); lia.
Qed.

Lemma core0Loop_only01_head0 (w : UList) :
  forall (z1 q : N) (out : UList),
    Only01 w ->
    core0Loop z1 (2 * q) w = Some (retB out) ->
    (exists u0, encU out (const S0) = encUTok 0 (encU u0 (const S0))) ->
    q = 0 /\ exists m rest,
      (forall sr, repUTok 0 z1 (encU w sr) = repUTok 0 (2 * m) (encUTok 1 (encU rest sr))) /\
      out = upush 0 1 (upush 1 m (upush 0 1 rest)).
Proof.
  induction w as [| u cx tl IH]; intros z1 q out hw h hhead; [discriminate |].
  destruct hw as [hu htl]. cbn [core0Loop] in h.
  destruct (u =? 0) eqn:hu0.
  - apply N.eqb_eq in hu0; subst u.
    destruct (IH (z1 + cx + 1) q out htl h hhead) as [hq [m [rest [hpre hout]]]].
    refine (conj hq _); exists m, rest; split; [| exact hout].
    intro sr; cbn [encU]; rewrite <- repUTok_add.
    replace (z1 + (cx + 1)) with (z1 + cx + 1) by lia. apply hpre.
  - apply N.eqb_neq in hu0. assert (u = 1) by lia; subst u.
    set (rest := if cx =? 0 then tl else Ucons 1 (cx - 1) tl) in *.
    change (1 =? 0) with false in h; change (1 - 1) with 0 in h; change (0 =? 0) with true in h; cbv iota zeta in h.
    destruct (z1 =? 1) eqn:hz1.
    + exfalso.
      replace (2 * q + 2 * (cx + 1)) with (2 * (q + cx + 1)) in h by lia.
      destruct (IH 1 (q + cx + 1) out htl h hhead) as [hq _]; lia.
    + destruct (z1 mod 2 =? 1) eqn:hpar.
      * exfalso. destruct (z1 / 2 =? 0); [discriminate |].
        replace (2 * q + 2) with (2 * (q + 1)) in h by (clear; lia).
        rewrite mod2_even, div2_even in h; cbn [N.eqb] in h.
        injection h as h; subst out.
        destruct hhead as [u0 hu0'].
        rewrite encU_upush in hu0'.
        rewrite repUTok_succ in hu0'.
        replace (repUTok 1 q (encU (upush 0 2 (upush 1 (z1 / 2 - 1) (upush 0 1 rest))) (const S0)))
          with (encU (upush 1 q (upush 0 2 (upush 1 (z1 / 2 - 1) (upush 0 1 rest)))) (const S0)) in hu0'
          by (rewrite encU_upush; reflexivity).
        exact (encUTok_zero_ne_one u0 _ (eq_sym hu0')).
      * apply N.eqb_neq in hpar.
        destruct (core0Finish_even_odd (z1 / 2) q 0 rest) as [he _].
        rewrite he in h; injection h as h; subst out.
        destruct (q =? 0) eqn:hq0.
        -- apply N.eqb_eq in hq0; subst q; unfold upush at 1; cbn [N.eqb].
           split; [reflexivity |].
           exists (z1 / 2), rest; split; [| reflexivity].
           intro sr; rewrite (encU_cons_split 1 cx tl sr); fold rest.
           replace (2 * (z1 / 2)) with z1 by lia; reflexivity.
        -- apply N.eqb_neq in hq0; exfalso.
           destruct hhead as [u0 hu0'].
           rewrite encU_upush in hu0'.
           replace q with ((q - 1) + 1) in hu0' by lia.
           rewrite repUTok_succ in hu0'.
           replace (repUTok 1 (q - 1) (encU (upush 0 1 (upush 1 (z1 / 2) (upush 0 1 rest))) (const S0)))
             with (encU (upush 1 (q - 1) (upush 0 1 (upush 1 (z1 / 2) (upush 0 1 rest)))) (const S0)) in hu0'
             by (rewrite encU_upush; reflexivity).
           exact (encUTok_zero_ne_one u0 _ (eq_sym hu0')).
Qed.

Definition W_stalled (x y : N) : UList :=
  if y =? 0 then upush 0 (x + 1) Unil
  else upush 0 1 (upush 1 y (upush 0 x Unil)).

Definition W_pre (x y : N) : UList :=
  upush 0 (2 * y) (upush 1 1 (upush 0 (x - 1) Unil)).

Lemma encU_W_stalled (x y : N) (sr : side) :
  encU (W_stalled x y) sr = encUTok 0 (repUTok 1 y (repUTok 0 x sr)).
Proof.
  unfold W_stalled. destruct (y =? 0) eqn:hy0.
  - apply N.eqb_eq in hy0; subst y.
    rewrite encU_upush, repUTok_succ; reflexivity.
  - rewrite !encU_upush; reflexivity.
Qed.

Lemma W_stalled_append_zero (x y d : N) :
  uappend (W_stalled x y) (upush 0 d Unil) = W_stalled (x + d) y.
Proof.
  unfold W_stalled. destruct (y =? 0).
  - rewrite uappend_upush; cbn [uappend]; rewrite upush_upush_same; f_equal; lia.
  - rewrite !uappend_upush; cbn [uappend]; rewrite upush_upush_same; reflexivity.
Qed.

Lemma only01_W_stalled (x y : N) : Only01 (W_stalled x y).
Proof.
  unfold W_stalled; destruct (y =? 0);
    repeat (apply only01_upush; [lia |]); exact I.
Qed.

Lemma core0Loop_only01_preimage_stalled (w : UList) (nx ny : N)
  (h01 : Only01 w) (hnx : 1 <= nx)
  (h : core0Loop 0 0 w = Some (retB (W_stalled nx ny))) :
  forall sr, encU w sr = encU (W_pre nx ny) sr.
Proof.
  assert (hhead : exists u0, encU (W_stalled nx ny) (const S0) = encUTok 0 (encU u0 (const S0))).
  { exists (upush 1 ny (upush 0 nx Unil)). rewrite encU_W_stalled, !encU_upush; reflexivity. }
  destruct (core0Loop_only01_head0 w 0 0 (W_stalled nx ny) h01 h hhead) as [_ [m [rest [hpre hout]]]].
  assert (hdef2 : repUTok 1 ny (encUTok 0 (encU (upush 0 (nx - 1) Unil) (const S0))) =
                    repUTok 1 m (encUTok 0 (encU rest (const S0)))).
  { apply (encUTok_inj 0).
    transitivity (encU (W_stalled nx ny) (const S0)).
    - rewrite encU_W_stalled, encU_upush; cbn [encU].
      replace nx with (1 + (nx - 1)) at 2 by lia.
      rewrite repUTok_add; reflexivity.
    - rewrite hout, !encU_upush; reflexivity. }
  pose proof (repUTok_one_enc0_inj ny m _ _ hdef2) as hmn; subst m.
  intro sr.
  assert (hrest : encU rest sr = repUTok 0 (nx - 1) sr).
  { symmetry; apply (encUTok_inj 0); apply (repUTok_inj 1 ny); apply (encUTok_inj 0).
    transitivity (encU (W_stalled nx ny) sr).
    - rewrite encU_W_stalled. replace nx with (1 + (nx - 1)) at 2 by lia.
      rewrite repUTok_add; reflexivity.
    - rewrite hout, !encU_upush; reflexivity. }
  pose proof (hpre sr) as hw; rewrite repUTok_0 in hw.
  rewrite hw, hrest. unfold W_pre; rewrite !encU_upush; reflexivity.
Qed.

Lemma ZChain_to_PsiReach_1_odd {k nx ny : N} {w1 : UList}
  (h01 : Only01 w1) (hnx : 1 <= nx)
  (hc : ZChain (2 * k + 1) w1 (W_stalled nx ny)) :
  PsiReach k (upush 1 1 w1) (upush 1 1 (W_pre nx ny)).
Proof.
  destruct (ZChain_split_last (2 * k) hc) as [w_mid [hc_ev hlast]].
  pose proof (ZChain_only01 h01 hc_ev) as h01_mid.
  pose proof (ZChain_to_PsiReach_1_even k hc_ev) as hp.
  pose proof (core0Loop_only01_preimage_stalled w_mid nx ny h01_mid hnx hlast) as heq.
  refine (PsiReach_congr _ _ hp); [reflexivity | intro sr; rewrite !encU_upush, heq; reflexivity].
Qed.

Lemma W_pre_step_retB (x y : N) (hx : 1 <= x) :
  core0Loop 0 0 (W_pre x y) = Some (retB (W_stalled x y)).
Proof.
  unfold W_pre. rewrite core0Loop_upush_zero; cbn [N.add].
  assert (h2y : 2 * y =? 1 = false) by (apply N.eqb_neq; clear; lia).
  assert (hpar : (2 * y) mod 2 =? 1 = false) by (rewrite mod2_even; reflexivity).
  pose proof (div2_even y) as hdiv.
  destruct (x - 1 =? 0) eqn:hx1.
  - apply N.eqb_eq in hx1. assert (x = 1) by lia; subst x.
    change (upush 1 1 (upush 0 (1 - 1) Unil)) with (Ucons 1 0 Unil).
    cbn [core0Loop]; change (1 =? 0) with false; change (0 =? 0) with true; change (1 - 1) with 0; cbv iota zeta.
    rewrite h2y, hpar, hdiv; unfold core0Finish; cbn [N.div N.modulo N.eqb].
    unfold W_stalled; destruct (y =? 0) eqn:hy0; [apply N.eqb_eq in hy0; subst y; reflexivity |].
    unfold upush; rewrite hy0; change (1 =? 0) with false; change (0 =? 1) with false; cbv iota zeta; reflexivity.
  - pose proof (proj1 (N.eqb_neq (x - 1) 0) hx1) as hx1'.
    assert (hu0 : upush 0 (x - 1) Unil = Ucons 0 (x - 1 - 1) Unil) by (unfold upush; rewrite hx1; reflexivity).
    rewrite hu0.
    change (upush 1 1 (Ucons 0 (x - 1 - 1) Unil)) with (Ucons 1 0 (Ucons 0 (x - 1 - 1) Unil)).
    cbn [core0Loop]; change (1 =? 0) with false; change (0 =? 0) with true; change (1 - 1) with 0; cbv iota zeta.
    rewrite h2y, hpar, hdiv, <- hu0; unfold core0Finish; cbn [N.div N.modulo N.eqb].
    rewrite upush_upush_same. replace (1 + (x - 1)) with x by (clear - hx1'; lia).
    unfold W_stalled; destruct (y =? 0) eqn:hy0.
    + apply N.eqb_eq in hy0; subst y.
      change (upush 1 0 ?t) with t.
      rewrite upush_upush_same. replace (1 + x) with (x + 1) by (clear; lia); reflexivity.
    + change (upush 1 0 ?t) with t; reflexivity.
Qed.

Inductive Stalled : Type :=
| Se
| Sone0
| Sz1
| Scanon1 (x y : N) (p : bool)
| ScanonZ (x y : N).

Definition stValid (s : Stalled) : Prop :=
  match s with
  | Scanon1 x _ false => 1 <= x
  | _ => True
  end.

Definition toU (s : Stalled) : UList :=
  match s with
  | Se => Unil
  | Sone0 => upush 1 1 Unil
  | Sz1 => upush 0 1 Unil
  | Scanon1 x y true => upush 1 1 (W_stalled x y)
  | Scanon1 x y false => upush 1 1 (W_pre x y)
  | ScanonZ x y => upush 0 1 (W_stalled x y)
  end.

Definition addZBot (d : N) (s : Stalled) : Stalled :=
  if d =? 0 then s
  else
    let d' := d - 1 in
    match s with
    | Se => if d' =? 0 then Sz1 else ScanonZ (d' - 1) 0
    | Sone0 => Scanon1 d' 0 true
    | Sz1 => ScanonZ d' 0
    | Scanon1 x y p => Scanon1 (x + d' + 1) y p
    | ScanonZ x y => ScanonZ (x + d' + 1) y
    end.

Lemma stValid_addZBot (d : N) (s : Stalled) (hv : stValid s) : stValid (addZBot d s).
Proof.
  unfold addZBot. destruct (d =? 0) eqn:hd0; [exact hv |].
  apply N.eqb_neq in hd0.
  destruct s as [| | | x y [|] | x y]; cbn [stValid] in *; try exact I.
  - destruct (d - 1 =? 0); exact I.
  - lia.
Qed.

Lemma uappend_nil_r (u : UList) :
  (forall x y, u = toU (ScanonZ x y) -> uappend u Unil = u) /\
  (forall s, stValid s -> uappend (toU s) Unil = toU s).
Proof.
  split.
  - intros x y ->; cbn [toU]; unfold W_stalled.
    destruct (y =? 0); rewrite !uappend_upush; reflexivity.
  - intros [| | | x y [|] | x y] hv; cbn [toU]; try reflexivity.
    + unfold W_stalled; destruct (y =? 0); rewrite !uappend_upush; reflexivity.
    + unfold W_pre; rewrite !uappend_upush; reflexivity.
    + unfold W_stalled; destruct (y =? 0); rewrite !uappend_upush; reflexivity.
Qed.

Lemma toU_addZBot (d : N) (s : Stalled) (hv : stValid s) :
  uappend (toU s) (upush 0 d Unil) = toU (addZBot d s).
Proof.
  unfold addZBot. destruct (d =? 0) eqn:hd0.
  - apply N.eqb_eq in hd0; subst d; cbn [upush].
    exact (proj2 (uappend_nil_r Unil) s hv).
  - apply N.eqb_neq in hd0.
    destruct s as [| | | x y [|] | x y].
    + destruct (d - 1 =? 0) eqn:hd1.
      * apply N.eqb_eq in hd1; assert (d = 1) by lia; subst d; reflexivity.
      * apply N.eqb_neq in hd1; cbn [toU uappend]; unfold W_stalled; cbn [N.eqb].
        rewrite upush_upush_same; f_equal; lia.
    + cbn [toU]; unfold W_stalled; cbn [N.eqb]; rewrite !uappend_upush; cbn [uappend].
      replace (d - 1 + 1) with d by lia; reflexivity.
    + cbn [toU]; unfold W_stalled; cbn [N.eqb]; rewrite !uappend_upush; cbn [uappend].
      rewrite !upush_upush_same; f_equal; lia.
    + cbn [toU]. rewrite uappend_upush, W_stalled_append_zero.
      replace (x + d) with (x + (d - 1) + 1) by lia; reflexivity.
    + cbn [stValid] in hv. cbn [toU]; unfold W_pre.
      rewrite !uappend_upush; cbn [uappend]; rewrite upush_upush_same.
      do 4 f_equal; lia.
    + cbn [toU]. rewrite uappend_upush, W_stalled_append_zero.
      replace (x + d) with (x + (d - 1) + 1) by lia; reflexivity.
Qed.

Lemma ZChain_to_PsiReach_1 {m nx ny : N} {w1 : UList}
  (h01 : Only01 w1) (hnx : m mod 2 = 1 -> 1 <= nx)
  (hc : ZChain m w1 (W_stalled nx ny)) :
  PsiReach (m / 2) (upush 1 1 w1) (toU (Scanon1 nx ny (m mod 2 =? 0))).
Proof.
  destruct (m mod 2 =? 0) eqn:hm.
  - apply N.eqb_eq in hm. replace m with (2 * (m / 2)) in hc by lia.
    exact (ZChain_to_PsiReach_1_even (m / 2) hc).
  - apply N.eqb_neq in hm. assert (hm1 : m mod 2 = 1) by lia.
    replace m with (2 * (m / 2) + 1) in hc by lia.
    exact (ZChain_to_PsiReach_1_odd h01 (hnx hm1) hc).
Qed.

Record StAcc := mkStAcc { sa_st : Stalled; sa_acc : N }.

Definition applyDeltaM (cur : Stalled) (nx ny dm acc : N) : StAcc :=
  let fl := N.odd dm in
  match cur with
  | Scanon1 _ _ true => mkStAcc (Scanon1 nx ny (negb fl)) (acc + N.div2 dm)
  | Scanon1 _ _ false => mkStAcc (Scanon1 nx ny fl) (acc + N.div2 (dm + 1))
  | ScanonZ _ _ => mkStAcc (ScanonZ nx ny) (acc + dm)
  | _ => mkStAcc cur acc
  end.

Lemma applyDeltaM_sound (x y nx ny dm acc : N) (cur : Stalled) (tail : UList)
  (hcur : cur = ScanonZ x y \/ exists p, cur = Scanon1 x y p)
  (hv : stValid cur)
  (h01_tail : Only01 tail)
  (hpos : cur = Scanon1 x y false -> 1 <= dm)
  (hnx : 1 <= dm -> 1 <= nx)
  (hz : ZChain dm (uappend (W_stalled x y) tail) (W_stalled nx ny)) :
  stValid (sa_st (applyDeltaM cur nx ny dm acc)) /\
  PsiReach (sa_acc (applyDeltaM cur nx ny dm acc) - acc)
    (uappend (toU cur) tail) (toU (sa_st (applyDeltaM cur nx ny dm acc))).
Proof.
  destruct hcur as [-> | [[|] ->]].
  - cbn [applyDeltaM sa_st sa_acc stValid toU].
    replace (acc + dm - acc) with dm by lia.
    rewrite uappend_upush.
    exact (conj I (ZChain_to_PsiReach_Z hz)).
  - unfold applyDeltaM; rewrite N_div2_eq, N_odd_eq; cbn [sa_st sa_acc].
    replace (acc + dm / 2 - acc) with (dm / 2) by lia.
    assert (hb : negb (dm mod 2 =? 1) = (dm mod 2 =? 0)).
    { destruct (dm mod 2 =? 1) eqn:h1; [apply N.eqb_eq in h1; rewrite h1; reflexivity |].
      apply N.eqb_neq in h1; assert (h0 : dm mod 2 = 0) by lia; rewrite h0; reflexivity. }
    rewrite hb.
    split.
    + destruct (dm mod 2 =? 0) eqn:hm0; cbn [stValid]; [exact I |].
      apply N.eqb_neq in hm0; apply hnx; lia.
    + cbn [toU]; rewrite uappend_upush.
      refine (ZChain_to_PsiReach_1 (only01_uappend (only01_W_stalled x y) h01_tail) _ hz).
      intro hm1; apply hnx; clear - hm1; lia.
  - cbn [stValid] in hv. specialize (hpos eq_refl).
    unfold applyDeltaM; rewrite N_div2_eq, N_odd_eq; cbn [sa_st sa_acc].
    replace (acc + (dm + 1) / 2 - acc) with ((dm + 1) / 2) by lia.
    split.
    + destruct (dm mod 2 =? 1); cbn [stValid]; [exact I | exact (hnx hpos)].
    + cbn [toU]; rewrite uappend_upush.
      replace dm with ((dm - 1) + 1) in hz by lia.
      destruct (ZChain_succ_inv hz) as [u_mid [hs hr]].
      pose proof (core0Loop_uappend (W_pre x y) tail 0 0 (W_stalled x y) (W_pre_step_retB x y hv)) as hpre.
      assert (h1 : ustepPsi (upush 1 1 (uappend (W_pre x y) tail)) = Some (upush 1 1 u_mid)).
      { unfold ustepPsi.
        rewrite ustepCore0_upush_one, (core0Loop_01 _ _ hpre),
                ustepCore0_upush_one, (core0Loop_01 _ _ hs).
        reflexivity. }
      pose proof (core0Loop_only01 _ 0 0 _ (only01_uappend (only01_W_stalled x y) h01_tail) hs) as h01'.
      pose proof (ZChain_to_PsiReach_1 h01' (fun _ => hnx hpos) hr) as hsub.
      assert (hb : (dm mod 2 =? 1) = ((dm - 1) mod 2 =? 0)).
      { destruct (dm mod 2 =? 1) eqn:hdm1.
        - apply N.eqb_eq in hdm1; symmetry; apply N.eqb_eq; lia.
        - apply N.eqb_neq in hdm1; symmetry; apply N.eqb_neq; lia. }
      rewrite hb.
      replace ((dm + 1) / 2) with ((dm - 1) / 2 + 1) by lia.
      exact (pr_succ _ _ _ _ (ustepPsi_sound _ _ h1) hsub).
Qed.

Definition after1Core (x y : N) : UList :=
  if x mod 2 =? 1 then
    upush 1 y (upush 0 1 (upush 1 ((x + 1) / 2) Unil))
  else
    upush 1 (y + 1) (upush 0 2 (upush 1 (x / 2 - 1) Unil)).

Lemma after1Core_step (x y : N) (hx : 1 <= x) :
  core0Loop 0 0 (uappend (W_stalled x y) (upush 1 1 Unil)) =
    Some (retB (uappend (after1Core x y) (upush 0 1 Unil))).
Proof.
  assert (hcore : core0Loop 0 0 (uappend (W_stalled x y) (upush 1 1 Unil)) =
                    core0Loop (x + 1) (2 * y) (upush 1 1 Unil)).
  { unfold W_stalled; destruct (y =? 0) eqn:hy0.
    - apply N.eqb_eq in hy0; subst y.
      rewrite uappend_upush; cbn [uappend]; rewrite core0Loop_upush_zero; f_equal; lia.
    - rewrite !uappend_upush; cbn [uappend].
      rewrite core0Loop_upush_zero; cbn [N.add]; rewrite core0Loop_upush_one, core0Loop_upush_zero; f_equal; clear; lia. }
  rewrite hcore; change (upush 1 1 Unil) with (Ucons 1 0 Unil); cbn [core0Loop];
    change (1 =? 0) with false; change (0 =? 0) with true; change (1 - 1) with 0; cbv iota zeta.
  replace (x + 1 =? 1) with false by (symmetry; apply N.eqb_neq; lia).
  destruct (x mod 2 =? 1) eqn:hodd.
  - pose proof (proj1 (N.eqb_eq (x mod 2) 1) hodd) as hodd'.
    replace ((x + 1) mod 2 =? 1) with false by (symmetry; apply N.eqb_neq; clear - hodd'; lia).
    unfold core0Finish, after1Core; rewrite hodd, mod2_even, div2_even; cbn [N.eqb].
    rewrite !uappend_upush; cbn [uappend]; reflexivity.
  - pose proof (proj1 (N.eqb_neq (x mod 2) 1) hodd) as hodd'.
    replace ((x + 1) mod 2 =? 1) with true by (symmetry; apply N.eqb_eq; clear - hodd'; lia).
    replace ((x + 1) / 2 =? 0) with false by (symmetry; apply N.eqb_neq; clear - hx hodd'; lia).
    replace (2 * y + 2) with (2 * (y + 1)) by (clear; lia).
    rewrite mod2_even, div2_even; cbn [N.eqb].
    replace ((x + 1) / 2 - 1) with (x / 2 - 1) by (clear - hx hodd'; lia).
    unfold after1Core; rewrite hodd, !uappend_upush; cbn [uappend]; reflexivity.
Qed.

Lemma after1Core_add2 (x y : N) (hx : 3 <= x) :
  uappend (after1Core (x - 2) y) (upush 1 1 Unil) = after1Core x y.
Proof.
  unfold after1Core.
  assert (hm : (x - 2) mod 2 = x mod 2) by (clear - hx; lia).
  rewrite hm.
  destruct (x mod 2 =? 1) eqn:hodd;
    rewrite !uappend_upush; cbn [uappend]; rewrite upush_upush_same.
  - apply N.eqb_eq in hodd; do 3 f_equal; clear - hx hodd; lia.
  - apply N.eqb_neq in hodd; do 3 f_equal; clear - hx hodd; lia.
Qed.

Definition LCellSpec (W y py m : N) : Prop :=
  2 * y <= W /\
  2 * py <= W + 2 /\
  (2 * y = W -> py = y + 1 /\ m = 0) /\
  (2 * y < W -> 2 * py <= W + 1 /\ 1 <= m /\
    ZChain (m - 1) (after1Core (W - 2 * y) y) (W_stalled (W + 1 - 2 * py) py)).

Lemma LCellSpec_to_ZChain {W y py m : N} (h : LCellSpec W y py m) :
  ZChain m (uappend (W_stalled (W - 2 * y) y) (upush 1 1 Unil)) (W_stalled (W + 2 - 2 * py) py).
Proof.
  destruct h as [hy [hpy [h0 h1]]].
  destruct (2 * y =? W) eqn:heq.
  - apply N.eqb_eq in heq. destruct (h0 heq) as [-> ->].
    replace (W - 2 * y) with 0 by lia.
    replace (W + 2 - 2 * (y + 1)) with 0 by lia.
    unfold W_stalled.
    destruct (y =? 0) eqn:hy0.
    + apply N.eqb_eq in hy0; subst y; apply zc_zero.
    + replace (y + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia); cbv iota.
      change (upush 0 0 ?t) with t.
      rewrite !uappend_upush; cbn [uappend]; rewrite upush_upush_same.
      apply zc_zero.
  - apply N.eqb_neq in heq. assert (hlt : 2 * y < W) by lia.
    destruct (h1 hlt) as [hpy1 [hm1 hzc]].
    pose proof (after1Core_step (W - 2 * y) y ltac:(lia)) as hstep.
    pose proof (ZChain_append hzc (upush 0 1 Unil)) as hzc'.
    rewrite W_stalled_append_zero in hzc'.
    replace (W + 1 - 2 * py + 1) with (W + 2 - 2 * py) in hzc' by lia.
    replace m with ((m - 1) + 1) by lia.
    exact (zc_step _ _ _ _ hstep hzc').
Qed.

Definition DValid (k dx dy mD : N) : Prop :=
  2 <= k /\ 1 <= dx /\ dx + 2 * dy = 2 * k - 3 /\ 1 <= mD /\
  ZChain mD (upush 1 (k - 1) Unil) (W_stalled dx dy).

Lemma DValid_base2 : DValid 2 1 0 1.
Proof.
  unfold DValid; repeat split; try lia.
  change 1 with (0 + 1) at 1.
  eapply zc_step; [reflexivity | apply zc_zero].
Qed.

Lemma DValid_step {k dx dy mD py m : N}
  (hd : DValid k dx dy mD)
  (hl : LCellSpec (2 * k - 3) dy py m) :
  DValid (k + 1) (2 * k - 1 - 2 * py) py (mD + m).
Proof.
  destruct hd as [hk [hdx [hsum [hmD hzd]]]].
  assert (hW : 2 * dy < 2 * k - 3) by (clear - hk hdx hsum; lia).
  destruct (proj2 (proj2 (proj2 hl)) hW) as [hpy1 [hm1 _]].
  pose proof (LCellSpec_to_ZChain hl) as hzl.
  replace (2 * k - 3 - 2 * dy) with dx in hzl by (clear - hk hdx hsum; lia).
  replace (2 * k - 3 + 2 - 2 * py) with (2 * k - 1 - 2 * py) in hzl by (clear - hk hpy1; lia).
  pose proof (ZChain_append hzd (upush 1 1 Unil)) as hzd'.
  rewrite uappend_upush in hzd'; cbn [uappend] in hzd'; rewrite upush_upush_same in hzd'.
  replace (k - 1 + 1) with (k + 1 - 1) in hzd' by (clear - hk; lia).
  unfold DValid; repeat split; try (clear - hk hpy1 hmD hm1; lia).
  exact (ZChain_trans hzd' hzl).
Qed.

Lemma LCellSpec_x0 (y : N) : LCellSpec (2 * y) y (y + 1) 0.
Proof.
  unfold LCellSpec; repeat split; try lia.
Qed.

Lemma LCellSpec_y0_odd (k : N) : LCellSpec (2 * k + 1) 0 (k + 1) 1.
Proof.
  unfold LCellSpec; repeat split; try lia.
  replace (1 - 1) with 0 by lia.
  replace (2 * k + 1 - 2 * 0) with (2 * k + 1) by lia.
  replace (2 * k + 1 + 1 - 2 * (k + 1)) with 0 by lia.
  unfold after1Core, W_stalled.
  rewrite mod2_odd; replace (2 * k + 1 + 1) with (2 * (k + 1)) by lia; rewrite div2_even; cbv iota.
  replace (k + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia); cbv iota.
  unfold upush; replace (k + 1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  change (1 =? 0) with false; change (0 =? 0) with true; change (1 - 1) with 0; cbv iota zeta.
  apply zc_zero.
Qed.

Lemma LCellSpec_y0_x2 : LCellSpec 2 0 0 2.
Proof.
  unfold LCellSpec; repeat split; try lia.
  change (2 - 1) with (0 + 1).
  eapply zc_step; [reflexivity | apply zc_zero].
Qed.

Lemma LCellSpec_x2 (y dx dy mD : N) (hy : 1 <= y) (hd : DValid (y + 2) dx dy mD) :
  LCellSpec (2 * y + 2) y dy (mD + 1).
Proof.
  destruct hd as [_ [hdx [hsum [hmD hzd]]]].
  unfold LCellSpec; repeat split; try (clear hzd; lia).
  replace (mD + 1 - 1) with mD by (clear; lia).
  pose proof (ZChain_append hzd (upush 0 2 Unil)) as hzd'.
  rewrite W_stalled_append_zero in hzd'.
  replace (2 * y + 2 - 2 * y) with 2 by (clear; lia).
  replace (after1Core 2 y) with (uappend (upush 1 (y + 2 - 1) Unil) (upush 0 2 Unil)).
  - replace (2 * y + 2 + 1 - 2 * dy) with (dx + 2) by (clear - hy hdx hsum; lia). exact hzd'.
  - unfold after1Core; change (2 mod 2 =? 1) with false; change (2 / 2 - 1) with 0; cbv iota.
    replace (y + 2 - 1) with (y + 1) by (clear; lia).
    unfold upush at 1; replace (y + 1 =? 0) with false by (symmetry; apply N.eqb_neq; clear; lia); cbv iota zeta.
    cbn [uappend]; replace (y + 1 - 1 + 1) with (y + 1) by (clear; lia).
    change (upush 0 0 Unil) with (@Unil); reflexivity.
Qed.

Lemma LCellSpec_x1 (y dx dy mD py2 m2 : N) (hy : 1 <= y)
  (hd : DValid (y + 1) dx dy mD)
  (hl : LCellSpec (2 * y) dy py2 m2) :
  LCellSpec (2 * y + 1) y py2 (mD + 1 + m2).
Proof.
  destruct hd as [_ [hdx [hsum [hmD hzd]]]].
  pose proof (proj1 (proj2 hl)) as hpy2.
  unfold LCellSpec; repeat split; try (clear hzd hl; lia).
  pose proof (ZChain_append hzd (upush 0 1 (upush 1 1 Unil))) as hzd'.
  pose proof (LCellSpec_to_ZChain hl) as hzl.
  replace (2 * y - 2 * dy) with (dx + 1) in hzl by (clear - hy hdx hsum; lia).
  replace (2 * y + 2 - 2 * py2) with (2 * y + 1 + 1 - 2 * py2) in hzl by (clear - hpy2; lia).
  replace (2 * y + 1 - 2 * y) with 1 by (clear; lia).
  assert (ha1 : after1Core 1 y = uappend (upush 1 (y + 1 - 1) Unil) (upush 0 1 (upush 1 1 Unil))).
  { unfold after1Core; change (1 mod 2 =? 1) with true; change ((1 + 1) / 2) with 1; cbv iota.
    replace (y + 1 - 1) with y by (clear; lia).
    rewrite uappend_upush; reflexivity. }
  rewrite ha1.
  replace (uappend (W_stalled dx dy) (upush 0 1 (upush 1 1 Unil)))
    with (uappend (W_stalled (dx + 1) dy) (upush 1 1 Unil)) in hzd'
    by (rewrite <- W_stalled_append_zero, uappend_assoc; reflexivity).
  replace (mD + 1 + m2 - 1) with (mD + m2) by (clear; lia).
  exact (ZChain_trans hzd' hzl).
Qed.

Lemma LCellSpec_bulk (W y py1 m1 py2 m2 : N) (hx3 : 2 * y + 3 <= W)
  (hl1 : LCellSpec (W - 2) y py1 m1)
  (hl2 : LCellSpec (W - 1) py1 py2 m2) :
  LCellSpec W y py2 (m1 + m2).
Proof.
  assert (hlt1 : 2 * y < W - 2) by (clear - hx3; lia).
  destruct (proj2 (proj2 (proj2 hl1)) hlt1) as [hpy1 [hm1 hzc1]].
  pose proof (proj1 (proj2 hl2)) as hpy2.
  unfold LCellSpec; repeat split; try (clear hl1 hl2 hzc1; lia).
  pose proof (ZChain_append hzc1 (upush 1 1 Unil)) as hzc1'.
  pose proof (LCellSpec_to_ZChain hl2) as hzl2.
  replace (W - 2 - 2 * y) with ((W - 2 * y) - 2) in hzc1' by (clear - hx3; lia).
  assert (hx3' : 3 <= W - 2 * y) by (clear - hx3; lia).
  rewrite (after1Core_add2 (W - 2 * y) y hx3') in hzc1'.
  replace (W - 2 + 1 - 2 * py1) with (W - 1 - 2 * py1) in hzc1' by (clear - hx3 hpy1; lia).
  replace (W - 1 + 2 - 2 * py2) with (W + 1 - 2 * py2) in hzl2 by (clear - hx3 hpy2; lia).
  replace (m1 + m2 - 1) with ((m1 - 1) + m2) by (clear - hm1; lia).
  exact (ZChain_trans hzc1' hzl2).
Qed.

Lemma directOff0_sound {k c dx dy mD dx2 dy2 mD2 : N}
  (hc : 1 <= c) (hle : mD <= mD2)
  (hd1 : DValid k dx dy mD)
  (hd2 : DValid (k + c) dx2 dy2 mD2) :
  ZChain (mD2 - mD) (uappend (W_stalled dx dy) (upush 1 c Unil)) (W_stalled dx2 dy2).
Proof.
  pose proof (proj1 hd1) as hk.
  pose proof (ZChain_append (proj2 (proj2 (proj2 (proj2 hd1)))) (upush 1 c Unil)) as h1.
  rewrite uappend_upush in h1; cbn [uappend] in h1; rewrite upush_upush_same in h1.
  replace (k - 1 + c) with (k + c - 1) in h1 by lia.
  pose proof (proj2 (proj2 (proj2 (proj2 hd2)))) as h2.
  replace mD2 with (mD + (mD2 - mD)) in h2 by lia.
  exact (ZChain_det mD h2 h1).
Qed.

Lemma directOff12_sound {k c off dx dy mD py m : N}
  (hoff : off = 1 \/ off = 2) (hc : 2 <= c) (hle : mD + 1 <= m)
  (hd : DValid k dx dy mD)
  (hl : LCellSpec (2 * k - 4 + off + 2 * c) (k - off) py m) :
  ZChain (m - (mD + 1)) (uappend (W_stalled (dx + off) dy) (upush 1 c Unil))
    (W_stalled (2 * k - 3 + off + 2 * c - 2 * py) py).
Proof.
  pose proof (proj1 hd) as hk.
  pose proof (ZChain_append (proj2 (proj2 (proj2 (proj2 hd)))) (upush 0 off (upush 1 c Unil))) as h1.
  assert (hlt_off : 2 * (k - off) < 2 * k - 4 + off + 2 * c) by (clear - hoff hc hk; destruct hoff; lia).
  destruct (proj2 (proj2 (proj2 hl)) hlt_off) as [_ [hm1 hzc]].
  assert (ha : after1Core (2 * k - 4 + off + 2 * c - 2 * (k - off)) (k - off) =
                 uappend (upush 1 (k - 1) Unil) (upush 0 off (upush 1 c Unil))).
  { destruct hoff as [-> | ->].
    - replace (2 * k - 4 + 1 + 2 * c - 2 * (k - 1)) with (2 * c - 1) by (clear - hc hk; lia).
      unfold after1Core.
      replace ((2 * c - 1) mod 2 =? 1) with true by (symmetry; apply N.eqb_eq; clear - hc; lia).
      replace ((2 * c - 1 + 1) / 2) with c by (clear - hc; lia).
      rewrite uappend_upush; reflexivity.
    - replace (2 * k - 4 + 2 + 2 * c - 2 * (k - 2)) with (2 * c + 2) by (clear - hc hk; lia).
      unfold after1Core.
      replace ((2 * c + 2) mod 2 =? 1) with false by (symmetry; apply N.eqb_neq; clear; lia).
      replace (k - 2 + 1) with (k - 1) by (clear - hk; lia).
      replace ((2 * c + 2) / 2 - 1) with c by (clear; lia).
      rewrite uappend_upush; reflexivity. }
  rewrite ha in hzc.
  replace (2 * k - 4 + off + 2 * c + 1 - 2 * py) with (2 * k - 3 + off + 2 * c - 2 * py) in hzc by (clear - hk; lia).
  replace (m - 1) with (mD + (m - (mD + 1))) in hzc by (clear - hle; lia).
  pose proof (ZChain_det mD hzc h1) as hdet.
  replace (upush 0 off (upush 1 c Unil))
    with (uappend (upush 0 off Unil) (upush 1 c Unil)) in hdet
    by (rewrite uappend_upush; reflexivity).
  rewrite <- uappend_assoc, W_stalled_append_zero in hdet.
  exact hdet.
Qed.


(* --- Section 4: Trees, Big96, DP --- *)
Inductive Nib : Type := N00|N01|N02|N03|N04|N05|N06|N07|N08|N09|N10|N11|N12|N13|N14|N15.
Record Nib3 := mkNib3 { nb2 : Nib; nb1 : Nib; nb0 : Nib }.
Definition bits_to_nib (b3 b2 b1 b0 : bool) : Nib :=
  if b3 then if b2 then (if b1 then (if b0 then N15 else N14) else (if b0 then N13 else N12)) else (if b1 then (if b0 then N11 else N10) else (if b0 then N09 else N08))
  else if b2 then (if b1 then (if b0 then N07 else N06) else (if b0 then N05 else N04)) else (if b1 then (if b0 then N03 else N02) else (if b0 then N01 else N00)).
Definition N_to_nib3 (x : N) : Nib3 :=
  let b0 := N.odd x in let x1 := N.div2 x in let b1 := N.odd x1 in let x2 := N.div2 x1 in
  let b2 := N.odd x2 in let x3 := N.div2 x2 in let b3 := N.odd x3 in let x4 := N.div2 x3 in
  let b4 := N.odd x4 in let x5 := N.div2 x4 in let b5 := N.odd x5 in let x6 := N.div2 x5 in
  let b6 := N.odd x6 in let x7 := N.div2 x6 in let b7 := N.odd x7 in let x8 := N.div2 x7 in
  let b8 := N.odd x8 in let x9 := N.div2 x8 in let b9 := N.odd x9 in let x10 := N.div2 x9 in
  let b10 := N.odd x10 in let x11 := N.div2 x10 in let b11 := N.odd x11 in
  mkNib3 (bits_to_nib b11 b10 b9 b8) (bits_to_nib b7 b6 b5 b4) (bits_to_nib b3 b2 b1 b0).

Record V16 (A : Type) := mkV16 { q00:A;q01:A;q02:A;q03:A;q04:A;q05:A;q06:A;q07:A;q08:A;q09:A;q10:A;q11:A;q12:A;q13:A;q14:A;q15:A }.
Arguments mkV16 {A}.
Arguments q00 {A}. Arguments q01 {A}. Arguments q02 {A}. Arguments q03 {A}. Arguments q04 {A}. Arguments q05 {A}. Arguments q06 {A}. Arguments q07 {A}.
Arguments q08 {A}. Arguments q09 {A}. Arguments q10 {A}. Arguments q11 {A}. Arguments q12 {A}. Arguments q13 {A}. Arguments q14 {A}. Arguments q15 {A}.
Definition v16_const {A : Type} (d : A) : V16 A := mkV16 d d d d d d d d d d d d d d d d.
Notation get16 v i := (match i with N00=>q00 v|N01=>q01 v|N02=>q02 v|N03=>q03 v|N04=>q04 v|N05=>q05 v|N06=>q06 v|N07=>q07 v|N08=>q08 v|N09=>q09 v|N10=>q10 v|N11=>q11 v|N12=>q12 v|N13=>q13 v|N14=>q14 v|N15=>q15 v end).
Definition v16_set {A : Type} (v : V16 A) (i : Nib) (x : A) : V16 A :=
  match i with
  | N00 => mkV16 x (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N01 => mkV16 (q00 v) x (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N02 => mkV16 (q00 v) (q01 v) x (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N03 => mkV16 (q00 v) (q01 v) (q02 v) x (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N04 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) x (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N05 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) x (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N06 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) x (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N07 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) x (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N08 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) x (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N09 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) x (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N10 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) x (q11 v) (q12 v) (q13 v) (q14 v) (q15 v)
  | N11 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) x (q12 v) (q13 v) (q14 v) (q15 v)
  | N12 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) x (q13 v) (q14 v) (q15 v)
  | N13 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) x (q14 v) (q15 v)
  | N14 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) x (q15 v)
  | N15 => mkV16 (q00 v) (q01 v) (q02 v) (q03 v) (q04 v) (q05 v) (q06 v) (q07 v) (q08 v) (q09 v) (q10 v) (q11 v) (q12 v) (q13 v) (q14 v) x
  end.
Definition T4096 (A : Type) : Type := V16 (V16 (V16 A)).
Definition t4_const {A : Type} (d : A) : T4096 A := let v0 := v16_const d in let v1 := v16_const v0 in v16_const v1.
Definition get_t4 {A : Type} (t : T4096 A) (k : Nib3) : A :=
  let r2 := get16 t (nb2 k) in let r1 := get16 r2 (nb1 k) in get16 r1 (nb0 k).
Arguments get_t4 {A} : simpl never.
Definition t4_set {A : Type} (t : T4096 A) (k : Nib3) (x : A) : T4096 A :=
  let i2 := nb2 k in let i1 := nb1 k in let i0 := nb0 k in
  let v2 := get16 t i2 in let v1 := get16 v2 i1 in
  v16_set t i2 (v16_set v2 i1 (v16_set v1 i0 x)).

Record T8192 (A : Type) := mkT8 { t8_lo : T4096 A; t8_hi : T4096 A }.
Arguments mkT8 {A}. Arguments t8_lo {A}. Arguments t8_hi {A}.
Definition t8_get {A : Type} (t : T8192 A) (x : N) : A :=
  let k := N_to_nib3 x in if 4096 <=? x then get_t4 (t8_hi t) k else get_t4 (t8_lo t) k.
Definition t8_set {A : Type} (t : T8192 A) (x : N) (v : A) : T8192 A :=
  let k := N_to_nib3 x in
  if 4096 <=? x then mkT8 (t8_lo t) (t4_set (t8_hi t) k v) else mkT8 (t4_set (t8_lo t) k v) (t8_hi t).

Definition pack_v16_one {A : Type} (d : A) (xs : list A) : V16 A :=
  let a00 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a01 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a02 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a03 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a04 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a05 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a06 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a07 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a08 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a09 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a10 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a11 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a12 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a13 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a14 := match xs with x::_ => x | [] => d end in let xs := tl xs in
  let a15 := match xs with x::_ => x | [] => d end in
  mkV16 a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15.
Fixpoint pack_v16_list {A : Type} (d : A) (cnt : nat) (xs : list A) : list (V16 A) :=
  match cnt with O => [] | S cnt' => match xs with [] => [] | a00::a01::a02::a03::a04::a05::a06::a07::a08::a09::a10::a11::a12::a13::a14::a15::rest => mkV16 a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 :: pack_v16_list d cnt' rest | _ => [pack_v16_one d xs] end end.
Definition pack_t4 {A : Type} (d : A) (dv0 : V16 A) (dv1 : V16 (V16 A)) (xs : list A) : T4096 A :=
  pack_v16_one dv1 (pack_v16_list dv0 16%nat (pack_v16_list d 256%nat xs)).

Inductive D64 : Type := D00 | D01 | D02 | D03 | D04 | D05 | D06 | D07 | D08 | D09 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17 | D18 | D19 | D20 | D21 | D22 | D23 | D24 | D25 | D26 | D27 | D28 | D29 | D30 | D31 | D32 | D33 | D34 | D35 | D36 | D37 | D38 | D39 | D40 | D41 | D42 | D43 | D44 | D45 | D46 | D47 | D48 | D49 | D50 | D51 | D52 | D53 | D54 | D55 | D56 | D57 | D58 | D59 | D60 | D61 | D62 | D63.
Record V64 (A : Type) := mkV64 { p00 : A; p01 : A; p02 : A; p03 : A; p04 : A; p05 : A; p06 : A; p07 : A; p08 : A; p09 : A; p10 : A; p11 : A; p12 : A; p13 : A; p14 : A; p15 : A; p16 : A; p17 : A; p18 : A; p19 : A; p20 : A; p21 : A; p22 : A; p23 : A; p24 : A; p25 : A; p26 : A; p27 : A; p28 : A; p29 : A; p30 : A; p31 : A; p32 : A; p33 : A; p34 : A; p35 : A; p36 : A; p37 : A; p38 : A; p39 : A; p40 : A; p41 : A; p42 : A; p43 : A; p44 : A; p45 : A; p46 : A; p47 : A; p48 : A; p49 : A; p50 : A; p51 : A; p52 : A; p53 : A; p54 : A; p55 : A; p56 : A; p57 : A; p58 : A; p59 : A; p60 : A; p61 : A; p62 : A; p63 : A }.
Arguments mkV64 {A}.
Arguments p00 {A}. Arguments p01 {A}. Arguments p02 {A}. Arguments p03 {A}. Arguments p04 {A}. Arguments p05 {A}. Arguments p06 {A}. Arguments p07 {A}. Arguments p08 {A}. Arguments p09 {A}. Arguments p10 {A}. Arguments p11 {A}. Arguments p12 {A}. Arguments p13 {A}. Arguments p14 {A}. Arguments p15 {A}. Arguments p16 {A}. Arguments p17 {A}. Arguments p18 {A}. Arguments p19 {A}. Arguments p20 {A}. Arguments p21 {A}. Arguments p22 {A}. Arguments p23 {A}. Arguments p24 {A}. Arguments p25 {A}. Arguments p26 {A}. Arguments p27 {A}. Arguments p28 {A}. Arguments p29 {A}. Arguments p30 {A}. Arguments p31 {A}. Arguments p32 {A}. Arguments p33 {A}. Arguments p34 {A}. Arguments p35 {A}. Arguments p36 {A}. Arguments p37 {A}. Arguments p38 {A}. Arguments p39 {A}. Arguments p40 {A}. Arguments p41 {A}. Arguments p42 {A}. Arguments p43 {A}. Arguments p44 {A}. Arguments p45 {A}. Arguments p46 {A}. Arguments p47 {A}. Arguments p48 {A}. Arguments p49 {A}. Arguments p50 {A}. Arguments p51 {A}. Arguments p52 {A}. Arguments p53 {A}. Arguments p54 {A}. Arguments p55 {A}. Arguments p56 {A}. Arguments p57 {A}. Arguments p58 {A}. Arguments p59 {A}. Arguments p60 {A}. Arguments p61 {A}. Arguments p62 {A}. Arguments p63 {A}.
Definition v64_init {A : Type} (f : D64 -> A) : V64 A := mkV64 (f D00) (f D01) (f D02) (f D03) (f D04) (f D05) (f D06) (f D07) (f D08) (f D09) (f D10) (f D11) (f D12) (f D13) (f D14) (f D15) (f D16) (f D17) (f D18) (f D19) (f D20) (f D21) (f D22) (f D23) (f D24) (f D25) (f D26) (f D27) (f D28) (f D29) (f D30) (f D31) (f D32) (f D33) (f D34) (f D35) (f D36) (f D37) (f D38) (f D39) (f D40) (f D41) (f D42) (f D43) (f D44) (f D45) (f D46) (f D47) (f D48) (f D49) (f D50) (f D51) (f D52) (f D53) (f D54) (f D55) (f D56) (f D57) (f D58) (f D59) (f D60) (f D61) (f D62) (f D63).
Notation get64 v d := (match d with | D00 => p00 v | D01 => p01 v | D02 => p02 v | D03 => p03 v | D04 => p04 v | D05 => p05 v | D06 => p06 v | D07 => p07 v | D08 => p08 v | D09 => p09 v | D10 => p10 v | D11 => p11 v | D12 => p12 v | D13 => p13 v | D14 => p14 v | D15 => p15 v | D16 => p16 v | D17 => p17 v | D18 => p18 v | D19 => p19 v | D20 => p20 v | D21 => p21 v | D22 => p22 v | D23 => p23 v | D24 => p24 v | D25 => p25 v | D26 => p26 v | D27 => p27 v | D28 => p28 v | D29 => p29 v | D30 => p30 v | D31 => p31 v | D32 => p32 v | D33 => p33 v | D34 => p34 v | D35 => p35 v | D36 => p36 v | D37 => p37 v | D38 => p38 v | D39 => p39 v | D40 => p40 v | D41 => p41 v | D42 => p42 v | D43 => p43 v | D44 => p44 v | D45 => p45 v | D46 => p46 v | D47 => p47 v | D48 => p48 v | D49 => p49 v | D50 => p50 v | D51 => p51 v | D52 => p52 v | D53 => p53 v | D54 => p54 v | D55 => p55 v | D56 => p56 v | D57 => p57 v | D58 => p58 v | D59 => p59 v | D60 => p60 v | D61 => p61 v | D62 => p62 v | D63 => p63 v end).
Record R6 := mkR6 { r6_lo : D64; r6_c : bool }.
Definition d64_val (d : D64) : N := match d with | D00 => 0 | D01 => 1 | D02 => 2 | D03 => 3 | D04 => 4 | D05 => 5 | D06 => 6 | D07 => 7 | D08 => 8 | D09 => 9 | D10 => 10 | D11 => 11 | D12 => 12 | D13 => 13 | D14 => 14 | D15 => 15 | D16 => 16 | D17 => 17 | D18 => 18 | D19 => 19 | D20 => 20 | D21 => 21 | D22 => 22 | D23 => 23 | D24 => 24 | D25 => 25 | D26 => 26 | D27 => 27 | D28 => 28 | D29 => 29 | D30 => 30 | D31 => 31 | D32 => 32 | D33 => 33 | D34 => 34 | D35 => 35 | D36 => 36 | D37 => 37 | D38 => 38 | D39 => 39 | D40 => 40 | D41 => 41 | D42 => 42 | D43 => 43 | D44 => 44 | D45 => 45 | D46 => 46 | D47 => 47 | D48 => 48 | D49 => 49 | D50 => 50 | D51 => 51 | D52 => 52 | D53 => 53 | D54 => 54 | D55 => 55 | D56 => 56 | D57 => 57 | D58 => 58 | D59 => 59 | D60 => 60 | D61 => 61 | D62 => 62 | D63 => 63 end.
Definition N_to_d64 (n : N) : D64 :=
  if n =? 0 then D00
  else if n =? 1 then D01
  else if n =? 2 then D02
  else if n =? 3 then D03
  else if n =? 4 then D04
  else if n =? 5 then D05
  else if n =? 6 then D06
  else if n =? 7 then D07
  else if n =? 8 then D08
  else if n =? 9 then D09
  else if n =? 10 then D10
  else if n =? 11 then D11
  else if n =? 12 then D12
  else if n =? 13 then D13
  else if n =? 14 then D14
  else if n =? 15 then D15
  else if n =? 16 then D16
  else if n =? 17 then D17
  else if n =? 18 then D18
  else if n =? 19 then D19
  else if n =? 20 then D20
  else if n =? 21 then D21
  else if n =? 22 then D22
  else if n =? 23 then D23
  else if n =? 24 then D24
  else if n =? 25 then D25
  else if n =? 26 then D26
  else if n =? 27 then D27
  else if n =? 28 then D28
  else if n =? 29 then D29
  else if n =? 30 then D30
  else if n =? 31 then D31
  else if n =? 32 then D32
  else if n =? 33 then D33
  else if n =? 34 then D34
  else if n =? 35 then D35
  else if n =? 36 then D36
  else if n =? 37 then D37
  else if n =? 38 then D38
  else if n =? 39 then D39
  else if n =? 40 then D40
  else if n =? 41 then D41
  else if n =? 42 then D42
  else if n =? 43 then D43
  else if n =? 44 then D44
  else if n =? 45 then D45
  else if n =? 46 then D46
  else if n =? 47 then D47
  else if n =? 48 then D48
  else if n =? 49 then D49
  else if n =? 50 then D50
  else if n =? 51 then D51
  else if n =? 52 then D52
  else if n =? 53 then D53
  else if n =? 54 then D54
  else if n =? 55 then D55
  else if n =? 56 then D56
  else if n =? 57 then D57
  else if n =? 58 then D58
  else if n =? 59 then D59
  else if n =? 60 then D60
  else if n =? 61 then D61
  else if n =? 62 then D62
  else if n =? 63 then D63
  else D00.
Definition build_tabs6 : V64 (V64 R6) * V64 (V64 R6) * V64 R6 :=
  let p0 : V64 R6 := mkV64 (mkR6 D00 false) (mkR6 D01 false) (mkR6 D02 false) (mkR6 D03 false) (mkR6 D04 false) (mkR6 D05 false) (mkR6 D06 false) (mkR6 D07 false) (mkR6 D08 false) (mkR6 D09 false) (mkR6 D10 false) (mkR6 D11 false) (mkR6 D12 false) (mkR6 D13 false) (mkR6 D14 false) (mkR6 D15 false) (mkR6 D16 false) (mkR6 D17 false) (mkR6 D18 false) (mkR6 D19 false) (mkR6 D20 false) (mkR6 D21 false) (mkR6 D22 false) (mkR6 D23 false) (mkR6 D24 false) (mkR6 D25 false) (mkR6 D26 false) (mkR6 D27 false) (mkR6 D28 false) (mkR6 D29 false) (mkR6 D30 false) (mkR6 D31 false) (mkR6 D32 false) (mkR6 D33 false) (mkR6 D34 false) (mkR6 D35 false) (mkR6 D36 false) (mkR6 D37 false) (mkR6 D38 false) (mkR6 D39 false) (mkR6 D40 false) (mkR6 D41 false) (mkR6 D42 false) (mkR6 D43 false) (mkR6 D44 false) (mkR6 D45 false) (mkR6 D46 false) (mkR6 D47 false) (mkR6 D48 false) (mkR6 D49 false) (mkR6 D50 false) (mkR6 D51 false) (mkR6 D52 false) (mkR6 D53 false) (mkR6 D54 false) (mkR6 D55 false) (mkR6 D56 false) (mkR6 D57 false) (mkR6 D58 false) (mkR6 D59 false) (mkR6 D60 false) (mkR6 D61 false) (mkR6 D62 false) (mkR6 D63 false) in
  let p1 : V64 R6 := mkV64 (mkR6 D00 true) (mkR6 D01 true) (mkR6 D02 true) (mkR6 D03 true) (mkR6 D04 true) (mkR6 D05 true) (mkR6 D06 true) (mkR6 D07 true) (mkR6 D08 true) (mkR6 D09 true) (mkR6 D10 true) (mkR6 D11 true) (mkR6 D12 true) (mkR6 D13 true) (mkR6 D14 true) (mkR6 D15 true) (mkR6 D16 true) (mkR6 D17 true) (mkR6 D18 true) (mkR6 D19 true) (mkR6 D20 true) (mkR6 D21 true) (mkR6 D22 true) (mkR6 D23 true) (mkR6 D24 true) (mkR6 D25 true) (mkR6 D26 true) (mkR6 D27 true) (mkR6 D28 true) (mkR6 D29 true) (mkR6 D30 true) (mkR6 D31 true) (mkR6 D32 true) (mkR6 D33 true) (mkR6 D34 true) (mkR6 D35 true) (mkR6 D36 true) (mkR6 D37 true) (mkR6 D38 true) (mkR6 D39 true) (mkR6 D40 true) (mkR6 D41 true) (mkR6 D42 true) (mkR6 D43 true) (mkR6 D44 true) (mkR6 D45 true) (mkR6 D46 true) (mkR6 D47 true) (mkR6 D48 true) (mkR6 D49 true) (mkR6 D50 true) (mkR6 D51 true) (mkR6 D52 true) (mkR6 D53 true) (mkR6 D54 true) (mkR6 D55 true) (mkR6 D56 true) (mkR6 D57 true) (mkR6 D58 true) (mkR6 D59 true) (mkR6 D60 true) (mkR6 D61 true) (mkR6 D62 true) (mkR6 D63 true) in
  let mk (c : bool) (a b : D64) : R6 :=
    let s := d64_val a + d64_val b + (if c then 1 else 0) in
    let d := N_to_d64 (s mod 64) in
    if 64 <=? s then get64 p1 d else get64 p0 d in
  (v64_init (fun a => v64_init (fun b => mk false a b)),
   v64_init (fun a => v64_init (fun b => mk true a b)),
   p0).
Definition add6_in (t0 t1 : V64 (V64 R6)) (c : bool) (x y : D64) : R6 :=
  let tbl := if c then t1 else t0 in let row := get64 tbl x in get64 row y.
Arguments add6_in : simpl never.
Definition inc6_in (row0 idr : V64 R6) (c : bool) (x : D64) : R6 :=
  if c then get64 row0 x else get64 idr x.
Arguments inc6_in : simpl never.

Inductive Big96 : Type := u_nil | u_cons (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 : D64) (tl : Big96).
Definition big_small (d : D64) : Big96 := u_cons d D00 D00 D00 D00 D00 D00 D00 D00 D00 D00 D00 D00 D00 D00 D00 u_nil.

Fixpoint big_inc (t1 : V64 (V64 R6)) (idr : V64 R6) (x : Big96) : Big96 :=
  match x with
  | u_nil => big_small D01
  | u_cons a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 tl =>
    let row0 := p00 t1 in
    let r00 := inc6_in row0 idr true a00 in
    if negb (r6_c r00) then u_cons (r6_lo r00) a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 tl
    else
      let r01 := inc6_in row0 idr (r6_c r00) a01 in
      let r02 := inc6_in row0 idr (r6_c r01) a02 in
      let r03 := inc6_in row0 idr (r6_c r02) a03 in
      let r04 := inc6_in row0 idr (r6_c r03) a04 in
      let r05 := inc6_in row0 idr (r6_c r04) a05 in
      let r06 := inc6_in row0 idr (r6_c r05) a06 in
      let r07 := inc6_in row0 idr (r6_c r06) a07 in
      let r08 := inc6_in row0 idr (r6_c r07) a08 in
      let r09 := inc6_in row0 idr (r6_c r08) a09 in
      let r10 := inc6_in row0 idr (r6_c r09) a10 in
      let r11 := inc6_in row0 idr (r6_c r10) a11 in
      let r12 := inc6_in row0 idr (r6_c r11) a12 in
      let r13 := inc6_in row0 idr (r6_c r12) a13 in
      let r14 := inc6_in row0 idr (r6_c r13) a14 in
      let r15 := inc6_in row0 idr (r6_c r14) a15 in
      u_cons (r6_lo r00) (r6_lo r01) (r6_lo r02) (r6_lo r03) (r6_lo r04) (r6_lo r05) (r6_lo r06) (r6_lo r07) (r6_lo r08) (r6_lo r09) (r6_lo r10) (r6_lo r11) (r6_lo r12) (r6_lo r13) (r6_lo r14) (r6_lo r15) (if r6_c r15 then big_inc t1 idr tl else tl)
  end.

Fixpoint big_add_c (t0 t1 : V64 (V64 R6)) (idr : V64 R6) (c : bool) (x y : Big96) : Big96 :=
  match x, y with
  | u_nil, _ => if c then big_inc t1 idr y else y
  | _, u_nil => if c then big_inc t1 idr x else x
  | u_cons a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 tx, u_cons b00 b01 b02 b03 b04 b05 b06 b07 b08 b09 b10 b11 b12 b13 b14 b15 ty =>
    let r00 := add6_in t0 t1 c a00 b00 in
    let r01 := add6_in t0 t1 (r6_c r00) a01 b01 in
    let r02 := add6_in t0 t1 (r6_c r01) a02 b02 in
    let r03 := add6_in t0 t1 (r6_c r02) a03 b03 in
    let r04 := add6_in t0 t1 (r6_c r03) a04 b04 in
    let r05 := add6_in t0 t1 (r6_c r04) a05 b05 in
    let r06 := add6_in t0 t1 (r6_c r05) a06 b06 in
    let r07 := add6_in t0 t1 (r6_c r06) a07 b07 in
    let r08 := add6_in t0 t1 (r6_c r07) a08 b08 in
    let r09 := add6_in t0 t1 (r6_c r08) a09 b09 in
    let r10 := add6_in t0 t1 (r6_c r09) a10 b10 in
    let r11 := add6_in t0 t1 (r6_c r10) a11 b11 in
    let r12 := add6_in t0 t1 (r6_c r11) a12 b12 in
    let r13 := add6_in t0 t1 (r6_c r12) a13 b13 in
    let r14 := add6_in t0 t1 (r6_c r13) a14 b14 in
    let r15 := add6_in t0 t1 (r6_c r14) a15 b15 in
    u_cons (r6_lo r00) (r6_lo r01) (r6_lo r02) (r6_lo r03) (r6_lo r04) (r6_lo r05) (r6_lo r06) (r6_lo r07) (r6_lo r08) (r6_lo r09) (r6_lo r10) (r6_lo r11) (r6_lo r12) (r6_lo r13) (r6_lo r14) (r6_lo r15) (big_add_c t0 t1 idr (r6_c r15) tx ty)
  end.

Definition push_d64 (d : D64) (hi : N) : N :=
  match d with | D00 => (N.double (N.double (N.double (N.double (N.double (N.double hi)))))) | D01 => (N.succ_double (N.double (N.double (N.double (N.double (N.double hi)))))) | D02 => (N.double (N.succ_double (N.double (N.double (N.double (N.double hi)))))) | D03 => (N.succ_double (N.succ_double (N.double (N.double (N.double (N.double hi)))))) | D04 => (N.double (N.double (N.succ_double (N.double (N.double (N.double hi)))))) | D05 => (N.succ_double (N.double (N.succ_double (N.double (N.double (N.double hi)))))) | D06 => (N.double (N.succ_double (N.succ_double (N.double (N.double (N.double hi)))))) | D07 => (N.succ_double (N.succ_double (N.succ_double (N.double (N.double (N.double hi)))))) | D08 => (N.double (N.double (N.double (N.succ_double (N.double (N.double hi)))))) | D09 => (N.succ_double (N.double (N.double (N.succ_double (N.double (N.double hi)))))) | D10 => (N.double (N.succ_double (N.double (N.succ_double (N.double (N.double hi)))))) | D11 => (N.succ_double (N.succ_double (N.double (N.succ_double (N.double (N.double hi)))))) | D12 => (N.double (N.double (N.succ_double (N.succ_double (N.double (N.double hi)))))) | D13 => (N.succ_double (N.double (N.succ_double (N.succ_double (N.double (N.double hi)))))) | D14 => (N.double (N.succ_double (N.succ_double (N.succ_double (N.double (N.double hi)))))) | D15 => (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.double (N.double hi)))))) | D16 => (N.double (N.double (N.double (N.double (N.succ_double (N.double hi)))))) | D17 => (N.succ_double (N.double (N.double (N.double (N.succ_double (N.double hi)))))) | D18 => (N.double (N.succ_double (N.double (N.double (N.succ_double (N.double hi)))))) | D19 => (N.succ_double (N.succ_double (N.double (N.double (N.succ_double (N.double hi)))))) | D20 => (N.double (N.double (N.succ_double (N.double (N.succ_double (N.double hi)))))) | D21 => (N.succ_double (N.double (N.succ_double (N.double (N.succ_double (N.double hi)))))) | D22 => (N.double (N.succ_double (N.succ_double (N.double (N.succ_double (N.double hi)))))) | D23 => (N.succ_double (N.succ_double (N.succ_double (N.double (N.succ_double (N.double hi)))))) | D24 => (N.double (N.double (N.double (N.succ_double (N.succ_double (N.double hi)))))) | D25 => (N.succ_double (N.double (N.double (N.succ_double (N.succ_double (N.double hi)))))) | D26 => (N.double (N.succ_double (N.double (N.succ_double (N.succ_double (N.double hi)))))) | D27 => (N.succ_double (N.succ_double (N.double (N.succ_double (N.succ_double (N.double hi)))))) | D28 => (N.double (N.double (N.succ_double (N.succ_double (N.succ_double (N.double hi)))))) | D29 => (N.succ_double (N.double (N.succ_double (N.succ_double (N.succ_double (N.double hi)))))) | D30 => (N.double (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.double hi)))))) | D31 => (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.double hi)))))) | D32 => (N.double (N.double (N.double (N.double (N.double (N.succ_double hi)))))) | D33 => (N.succ_double (N.double (N.double (N.double (N.double (N.succ_double hi)))))) | D34 => (N.double (N.succ_double (N.double (N.double (N.double (N.succ_double hi)))))) | D35 => (N.succ_double (N.succ_double (N.double (N.double (N.double (N.succ_double hi)))))) | D36 => (N.double (N.double (N.succ_double (N.double (N.double (N.succ_double hi)))))) | D37 => (N.succ_double (N.double (N.succ_double (N.double (N.double (N.succ_double hi)))))) | D38 => (N.double (N.succ_double (N.succ_double (N.double (N.double (N.succ_double hi)))))) | D39 => (N.succ_double (N.succ_double (N.succ_double (N.double (N.double (N.succ_double hi)))))) | D40 => (N.double (N.double (N.double (N.succ_double (N.double (N.succ_double hi)))))) | D41 => (N.succ_double (N.double (N.double (N.succ_double (N.double (N.succ_double hi)))))) | D42 => (N.double (N.succ_double (N.double (N.succ_double (N.double (N.succ_double hi)))))) | D43 => (N.succ_double (N.succ_double (N.double (N.succ_double (N.double (N.succ_double hi)))))) | D44 => (N.double (N.double (N.succ_double (N.succ_double (N.double (N.succ_double hi)))))) | D45 => (N.succ_double (N.double (N.succ_double (N.succ_double (N.double (N.succ_double hi)))))) | D46 => (N.double (N.succ_double (N.succ_double (N.succ_double (N.double (N.succ_double hi)))))) | D47 => (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.double (N.succ_double hi)))))) | D48 => (N.double (N.double (N.double (N.double (N.succ_double (N.succ_double hi)))))) | D49 => (N.succ_double (N.double (N.double (N.double (N.succ_double (N.succ_double hi)))))) | D50 => (N.double (N.succ_double (N.double (N.double (N.succ_double (N.succ_double hi)))))) | D51 => (N.succ_double (N.succ_double (N.double (N.double (N.succ_double (N.succ_double hi)))))) | D52 => (N.double (N.double (N.succ_double (N.double (N.succ_double (N.succ_double hi)))))) | D53 => (N.succ_double (N.double (N.succ_double (N.double (N.succ_double (N.succ_double hi)))))) | D54 => (N.double (N.succ_double (N.succ_double (N.double (N.succ_double (N.succ_double hi)))))) | D55 => (N.succ_double (N.succ_double (N.succ_double (N.double (N.succ_double (N.succ_double hi)))))) | D56 => (N.double (N.double (N.double (N.succ_double (N.succ_double (N.succ_double hi)))))) | D57 => (N.succ_double (N.double (N.double (N.succ_double (N.succ_double (N.succ_double hi)))))) | D58 => (N.double (N.succ_double (N.double (N.succ_double (N.succ_double (N.succ_double hi)))))) | D59 => (N.succ_double (N.succ_double (N.double (N.succ_double (N.succ_double (N.succ_double hi)))))) | D60 => (N.double (N.double (N.succ_double (N.succ_double (N.succ_double (N.succ_double hi)))))) | D61 => (N.succ_double (N.double (N.succ_double (N.succ_double (N.succ_double (N.succ_double hi)))))) | D62 => (N.double (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.succ_double hi)))))) | D63 => (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.succ_double (N.succ_double hi)))))) end.

Fixpoint big_to_N (x : Big96) : N :=
  match x with
  | u_nil => 0
  | u_cons a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 tl =>
    let hi := big_to_N tl in
    (push_d64 a00 (push_d64 a01 (push_d64 a02 (push_d64 a03 (push_d64 a04 (push_d64 a05 (push_d64 a06 (push_d64 a07 (push_d64 a08 (push_d64 a09 (push_d64 a10 (push_d64 a11 (push_d64 a12 (push_d64 a13 (push_d64 a14 (push_d64 a15 hi))))))))))))))))
  end.

Inductive MEnt : Type := mnone | mzero (my : N) (pk : Nib3) (py : N) | mpos (my : N) (pk : Nib3) (py : N) (m : Big96).
Record DEnt := mkDEnt { de_ok : bool; de_k : N; de_dx : N; de_dyk : Nib3; de_dy : N; de_m : Big96 }.
Record LEnt := mkLEnt { le_ok : bool; le_W : N; le_y : N; le_py : N; le_m : N }.
Record DEntry := mkDEntry { den_ok : bool; den_k : N; den_dx : N; den_dy : N; den_mD : N }.

Fixpoint build_ev (t0 t1 : V64 (V64 R6)) (idr : V64 R6) (cnt : nat) (y ny W : N) (fe : list MEnt) (fO : T4096 MEnt) (dP : DEnt) : list MEnt :=
  match cnt with
  | O => []
  | S cnt' =>
    let '(e1, fe') := match fe with x::r => (x, r) | [] => (mnone, []) end in
    let cell :=
      match e1 with
      | mpos my pk1 py1 m1 =>
        if (my =? y) && (2 * y + 3 <=? W) then
          match get_t4 fO pk1 with
          | mpos my2 pk2 py2 m2 => if my2 =? py1 then mpos y pk2 py2 (big_add_c t0 t1 idr false m1 m2) else mnone
          | mzero my2 pk2 py2 => if my2 =? py1 then mpos y pk2 py2 m1 else mnone
          | mnone => mnone
          end
        else mnone
      | _ =>
        if y =? ny then let py := ny + 1 in mzero y (N_to_nib3 py) py
        else if (y + 1 =? ny) && de_ok dP && (de_k dP =? y + 2) && (1 <=? y) then
          mpos y (de_dyk dP) (de_dy dP) (big_inc t1 idr (de_m dP))
        else mnone
      end in
    cell :: build_ev t0 t1 idr cnt' (y + 1) ny W fe' fO dP
  end.

Fixpoint build_od (t0 t1 : V64 (V64 R6)) (idr : V64 R6) (cnt : nat) (y ny W1 : N) (fo : list MEnt) (fEv : T4096 MEnt) (dP : DEnt) : list MEnt :=
  match cnt with
  | O => []
  | S cnt' =>
    let '(e1, fo') := match fo with x::r => (x, r) | [] => (mnone, []) end in
    let cell :=
      match e1 with
      | mpos my pk1 py1 m1 =>
        if (my =? y) && (2 * y + 3 <=? W1) then
          match get_t4 fEv pk1 with
          | mpos my2 pk2 py2 m2 => if my2 =? py1 then mpos y pk2 py2 (big_add_c t0 t1 idr false m1 m2) else mnone
          | mzero my2 pk2 py2 => if my2 =? py1 then mpos y pk2 py2 m1 else mnone
          | mnone => mnone
          end
        else mnone
      | mzero _ _ _ => mnone
      | mnone =>
        if (y =? ny) && de_ok dP && (de_k dP =? y + 1) && (1 <=? y) then
          let dk := de_dyk dP in
          match get_t4 fEv dk with
          | mpos my2 pk2 py2 m2 => if my2 =? de_dy dP then mpos y pk2 py2 (big_add_c t0 t1 idr true (de_m dP) m2) else mnone
          | mzero my2 pk2 py2 => if my2 =? de_dy dP then mpos y pk2 py2 (big_inc t1 idr (de_m dP)) else mnone
          | mnone => mnone
          end
        else mnone
      end in
    cell :: build_od t0 t1 idr cnt' (y + 1) ny W1 fo' fEv dP
  end.

Record ExtSt := mkExtSt { es_y : N; es_acc : N; es_sh : N; es_h : N; es_lay : T4096 LEnt }.

Definition extract_step (W : N) (ft : T4096 MEnt) (st : ExtSt) : StepRes ExtSt :=
  let h := es_h st in
  let b0 := N.odd h in let h1 := N.div2 h in
  let b1 := N.odd h1 in let h2 := N.div2 h1 in
  let b2 := N.odd h2 in let h3 := N.div2 h2 in
  let b3 := N.odd h3 in let h4 := N.div2 h3 in
  let nib := (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0) in
  if nib =? 0 then mkStepRes true (mkExtSt (es_y st) 0 0 h4 (es_lay st))
  else if nib <? 8 then
    let y := es_y st + (es_acc st + N.shiftl (nib - 1) (es_sh st)) in
    let yk := N_to_nib3 y in
    let lay' :=
      match get_t4 ft yk with
      | mpos my _ py m => if my =? y then t4_set (es_lay st) yk (mkLEnt true W y py (big_to_N m)) else es_lay st
      | mzero my _ py => if my =? y then t4_set (es_lay st) yk (mkLEnt true W y py 0) else es_lay st
      | mnone => es_lay st
      end in
    mkStepRes false (mkExtSt (y + 1) 0 0 h4 lay')
  else
    mkStepRes false (mkExtSt (es_y st) (es_acc st + N.shiftl (nib - 8) (es_sh st)) (es_sh st + 3) h4 (es_lay st)).

Record DPState := mkDPState {
  dps_ny_nat : nat;
  dps_ny : N;
  dps_fe_l : list MEnt;
  dps_fo_l : list MEnt;
  dps_fo_t : T4096 MEnt;
  dps_dP : DEnt;
  dps_dC : DEnt;
  dps_ltab : T8192 (T4096 LEnt);
  dps_dtab : T4096 DEntry
}.

Fixpoint run_dp_chunk (t0 t1 : V64 (V64 R6)) (idr : V64 R6)
  (dv0 : V16 MEnt) (dv1 : V16 (V16 MEnt)) (le_emp : T4096 LEnt)
  (rem : nat) (h : N) (st : DPState) : DPState :=
  match rem with
  | O => st
  | S rem' =>
    let ny_nat := dps_ny_nat st in
    let ny := dps_ny st in
    let W := 2 * ny in let W1 := W + 1 in
    let fev_l := build_ev t0 t1 idr (S ny_nat) 0 ny W (dps_fe_l st) (dps_fo_t st) (dps_dP st) in
    let fev_t := pack_t4 mnone dv0 dv1 fev_l in
    let ex1 := sr_val (runPos 8192%positive (extract_step W fev_t) (mkExtSt 0 0 0 h le_emp)) in
    let ltab1 := t8_set (dps_ltab st) W (es_lay ex1) in
    let py0 := ny + 1 in
    let fod_l := mpos 0 (N_to_nib3 py0) py0 (big_small D01) :: build_od t0 t1 idr ny_nat 1 ny W1 (tl (dps_fo_l st)) fev_t (dps_dP st) in
    let fod_t := pack_t4 mnone dv0 dv1 fod_l in
    let ex2 := sr_val (runPos 8192%positive (extract_step W1 fod_t) (mkExtSt 0 0 0 (es_h ex1) le_emp)) in
    let ltab2 := t8_set ltab1 W1 (es_lay ex2) in
    let dC := dps_dC st in
    let n0 := mkNib3 N00 N00 N00 in
    let '(dN, dtab') :=
      if de_ok dC && (de_k dC =? ny + 2) then
        let dk := de_dyk dC in
        match get_t4 fod_t dk with
        | mpos my pk py m =>
          if my =? de_dy dC then
            let nm := big_add_c t0 t1 idr false (de_m dC) m in
            let kN := ny + 3 in
            let dxN := 2 * (ny + 2) - 1 - 2 * py in
            (mkDEnt true kN dxN pk py nm,
             if kN <? 4096 then t4_set (dps_dtab st) (N_to_nib3 kN) (mkDEntry true kN dxN py (big_to_N nm)) else dps_dtab st)
          else (mkDEnt false 0 0 n0 0 u_nil, dps_dtab st)
        | _ => (mkDEnt false 0 0 n0 0 u_nil, dps_dtab st)
        end
      else (mkDEnt false 0 0 n0 0 u_nil, dps_dtab st) in
    run_dp_chunk t0 t1 idr dv0 dv1 le_emp rem' (es_h ex2)
      (mkDPState (S ny_nat) (ny + 1) fev_l fod_l fod_t dC dN ltab2 dtab')
  end.

Definition hint_chunks : list (nat * N) := [
  (10%nat, 0x101254014331031111102111141011311201321120111203112110121120121121012210121111011220121110210211101110111101110111%N);
  (10%nat, 0x1032d2101172a1101112a4301242291105111011142281102e111011f351101110454122012102851110631112012b120281505235061210562101721013162%N);
  (10%nat, 0x10122372121f30122421137512101433234721013331f431311012342461f01643315421031262a210231311728110221332852013331f4312073741201f21214252022112132930122153471024222b01361f520512823013151f6032e1301112e221%N);
  (10%nat, 0x10114111f43920325281371f211012221543923036211f111f1f2101728328711101212436342b1101528132e5012c332b21310283281f210216281128531052b631f2013315332572207252a411201f32b2133220213332f112051631612821063283511301351363333120321251f515041313215332122%N);
  (10%nat, 0x1011f122417275011f145323132a1f2015224113511f6054113611f2152d0511f112413281f302821f1162112d22101f351116212f3012b4112151352a201644126143a01312147431272a10341216322e2102261432711162910153266312d22013441213333a201422113422b281204514633381101231131116217293032221411f112f210223111f3940141313423172a2%N);
  (10%nat, 0x1032d51221f61303c222f1312c21021381222b23011f1f62d311312c20612d2242915051f42132f629502a311f281162b302c7281711643421028116351263a3011f42861241122c420129144412613e011f412142333f310253521512b1f210272116172433a101f241362332b1f2011f44534112111f2920142226122d7120282213121f762a205512242171f11302832271312211f2a1%N);
  (10%nat, 0x104231f22f51202d38232a62a312202f521f133746302d212c312f11f416102393829221f014e2c132a3142013b32b47247055342a382372b03f3873163302c2f42b2172152210282e22b5351293012b4f134131f201294a411f12d012d732d2313b102d41f53412b2102292932b172312c103a4133832d201282b2c5323212a20296713272d1203d2212a7122a22%N);
  (10%nat, 0x1021f4a51112922338201235939122928205c4112c75271205f143832d2023833761302a4b22629152b210422a423823015f38612b110122e45282220414f2c632f305832d361f21304592b612f111105a121f4239130136c152f121101124f22931172815014d352a32e6104f31f67293210212d2d33128342e4104b5121f4112e52014b242d122d322%N);
  (10%nat, 0x10112b1f2e2d2a1532d1221011113b2e292e13422c2210138249512665663220132e23482c32122d32201f634b4252332f512047354d14492422074134d2d532a1413031f32214c42971f41421052224f2e2285323015414314e32d2d1420511244c22e2c221150574b643f3532026164c382831433037263d732b312e221074c1f2e231f1161201251214b2812d3a1101514e292b292229015e32f28341f1058532b2363172102454b13a421f11f1%N);
  (10%nat, 0x10162114e12c725c012923693412749104214c2e5212d3b210242414c2e1615a10233212c2d3853592012343391f32f435820514493a4212b3c12053512b653c521f13e2033223943c414731238301f1322828413b42c43a103221f73223e2e113d0133481313d22b123a11025112b71143d2e3d204152937292e135b102122b2161163b383b304222b352642f42d138111043c2a382b3232e13013391313292f1f283821101132a5312c2f31f43a3201337334c3428123e11%N);
  (10%nat, 0x102f2862f2d21f2943d301392153363e13172a4820138163d2c1472a4b013a1132d6213a35f1053a312c652c13e21022e4123d12c613848102d3211f29391f5359201392122a28329375f2013172e122929659120382312a2f52b53e2a202312e7642b44829303811224a412a47392a10214e222d2b2c22b012d12134b1312c5b201422d2d1142c3f12d051f1511f292929612e2a2d0713222e2a1162a5c302b12214b26475b21072422e2c2a1f31f483011f1214a4132975b2%N);
  (10%nat, 0x104936f11632e2b304e2254c2c11632952a2104a4526811f4b3014a32165f1216373a201492285f12734c014b22141294a32c4a10216115e274d21024b1241174d22824c104b2c4f143233292f2014a3435c12634482014431f4c1622e381204952a4953512c39220552d3a434242a381304a32b4941242173f2102a592254733b23013f1f2863b1314412b3a202959114452a3815053955d16156738503835293f116274d303c365921527443c21%N);
  (10%nat, 0x1012235e291f11222d65054f45592a129292825405a325c291f11512b28305f236e1f2641f1223210597e352a72443015b325c22a6134653172015a17c2412c5429015c1121693412d3c105f2b2142e361521025841259286142e367104f326c5322a72d2015b35b2843132e32a20146c42112a72d1202d3c56c141392112a203b55a2922113942a302d3c136c22212a6122c1023b35a2d2272a38014f17b131528313292013b3b3a2d11452c22d0553c24369112a2e2c%N);
  (10%nat, 0x1042f732c42d222b23012b5e1f3c15382f21312c205d293943d38114281150566b4d276152d2a550269353f3a1381162b307a63b44225738262a2107b4c451732a328643016c32334b2872e13382016b7392c28722b112b47016d2216934149281055811f5212c3a221026d1258281612c2a2a106d16b532912b31f2016c21265c4329342825201316c421293e1206832215c1f5553d22022316b41643f30684126c47412f1f10247928222f37016921582f281312d712%N);
  (10%nat, 0x102c44d52b58413f424302d2c124f136c4381f4161022c5932c3b2f4a221f0149134c15a3824813142012f24c5c38491113705532f4c24293c2d14b2b01f2d4e34f38491163302c2d4e224e3849262210286c44d3a66528293012b69324d3383f131f2011f26a24f3382a2c12d017e2214e2a32c149106a214c3b2a12c2b2102296c1273b22d2a412c2c107e4b332a533b772017d349342b32932932a2014493a6433292d1202d5e51f2f23a52d52c2206b53f438446642d1307d33f1252c312f412c21%N);
  (10%nat, 0x105d4d131295a6292e36120793c2375d144f22023165d224b61306b4b121f5c225921053496f22b292d3015c473c21295e5b11063b5295b122c3a31120415a73c52c4f15c30594b3246a2c282c113045a1448322b585a111104f2243c7e32b3b130134f313f372b584f112110114f44813b582563b15014e58236931315a104d613f66d21292b283210214d63e4175d614c24104c4d326c532e2d52014c34e36c434b32204f142d4e4214b51202d2d224d56c523c562%N);
  (10%nat, 0x102b1f4b591335d692013b3494f21245e3c3a204c4d1316c3f2f1203a782b236294c5c2201fc2312e4c383c1303911fd1253284b3c72921024c597329923012d316f2b2152d7e2a2046e2a552d1fe15055b282e3835b64c750761f9323295e4f302b63e5c331414e75b21075925b244f1f2d2c363017134c4f35315b7259201514f7497444f72d2e29015f64a2369342b2e11f1028a56134f549317210245a34e12635815811f1025c234c16b5329292d201235a54a2126a4e2162%N);
  (10%nat, 0x102e4d4214d7f21025f2e23d62416c69105d3a493326c487292015d338483436c5f203a3b3c45146c5f1202d3e6c435483b5e201f2d6c4352a2d3b5e302d3d16b1713493a5f10252e23b487361ff39014f316b1331f3e1f82013c46c222972f6852d0554e69264492e6804865c1f4353a1fd304d655f42244b5b2f2102d2a484e434c7c3014932a683534b581f2a2013f2d692534b7e0178582345d33d39101f92123a2d7a21023d49591224e29691%N);
  (10%nat, 0x1011fb5382f165f6d0128a58236935a5103f12b355c56921021f91f2f2d412691384384107f294c3216b692017f31f4f2126a5a5202a4d1316c2f53a1207e6a231582a4b74206a231582a4c29307d16a1125a292e2d741022a382e2129922b017931681213596f2045f14244e5b11f6057c5b1515e52e572d06a64e1f1324e6d730493d645a122168692106a2a54c242ac3016b3294f1216d692013933c2c4872116d6c011f958236934f1f1%N);
  (10%nat, 0x105486e2283b4529f210685f3632f32829e11015d5f2833822829f20129b2e39236935e110283d211f5f5d2102428e12823d11f5c2c4b11029911f333b6c692014b6d216343936c5a51107f273e1136c5f120298282c2b56a2284b220284282b56a259413028f11f173a36b15d21069227733f29c230128b311f12b2b1f6859520794282a2a29685b15053d683872b55e65b5021fa6283d355c6b302892428442f65c6a2101fc72c42b285d3b3f3011fd32382e3535c5d52%N);
  (10%nat, 0x1051f12229e62b1321f949302911632a8641f122128b2e306131f387a2a2a7242ac3029262c28b32951212982e20152262a82c5211298390128432a296f5823693680212ad2e34211f84c21027114978292e32416c6a0322129b1f393326c69204321381fa732e3436c5f20412487873951136c5f120431329f394356c74f2021251f28b394356c73c2a304113529b13817136c1f58013525396d5272a732af0312429c3152b1331f94d2012512c1fd452c2221f958041144e7d2e263696801229e6312d437a5a30125d6a632e422529e3%N);
  (10%nat, 0x103a122a84421f3d2a5a721503a32f37d5b54d7265b502d1f28122a864353f5f38301f2a112e37f486663f4456a302e1329b3b28284c456b302c621f71fa3d373534b285c62012d2232b1fa3d2a1154e286d01392c31fb5823693680211f2ae2c55811f3d3b21022f11628c3a2a412582816a02f1628d382b3216b69202c321292892f32c2126a5f20412a2882f2d11216c5961202f64329f2f2316b2f3e202123e31ff2f2316b2f3e302e34162b28a12f1126c383f01f13821792d22f212af02a2261629c312d12131fc3c2029122d121ff42c11321fd3f0293732d29a281516b3d3a%N);
  (10%nat, 0x102384917b4f21582a6b04e23f1629c1214f2b1359320138333d1229f1134f2c25a602942d348329f64d12d15f03e49122a81324d12d4e1f302d2d113f32a812214d12d5d303f116528a4c244d27c302d2d2a2e5f681214f317b2012a2b2562e2a8224f317e014a282c37a58234e2a3581f023612be4214c65f2a210263a28112894b614c24296a0491f161fc491f4b332a69203d3228128a4834349342b5f203842812a7f485113493a5f120482864329f753f2c1f482d20211f32b9753f4281f481f51303f2b412ac11f33f172c492b302d3811fc3e22f3b736e2303d22e1629c3161f3c12b592b2%N);
  (10%nat, 0x105d214936e34c23155e294c301681f3d416c4e12615d55b0294816a124e726a358105f2581628c215316874b204f294a1268173d23546864f0414f348283684e52b58374e04f5a1229832365e4e512054f1158329a33645a144d3058133e4784c282a59244e3054f2582c1fb353294f315920124d22481f2991152c4f44b28015b64836958236936802132d852e4d614d22102591129a4d4122e4b264a1f04f2133c7b4c3216b168204e32129b4f21269125d20414c6e4d11216b15f1205813f4329d236931585203821212d8236931585302d3a33d12ab11269125a6%N);
  (10%nat, 0x1014a429115b4c4d1121384b5f1203b14e69436f2b232e4d5e2014c211294d5a3b2b2312d4d5d1303a14e2b4e128a1252914c5d304f2f4b1595973621f91f2303834c22c4c166f2b215283128a20134a6d127a2a2352841ff1502e4e34b2e34a3f3835b64487501f44c45f124c5a3232864e5a302c58116934c5c3314463d5a1f301f59124a1785d2434c75c302a4c64c2e4f4f3531534b6a201715824b12e4f5825454e1f5d011f5c4a2c358582369345c05b24a16d34f56125869210255d248116f59126358145e036849166a54c1285a435a2055a324911784f21263596592015b44b2a5d4d11211f5c58712035f4a64328c2365e294c2%N);
  (10%nat, 0x105e3d16c648493324b3869203a3d383212f1fb483434932f5f20139417f3b485113493a5f1205d13d6e4436b4353f3c5e203e13b212299484353f3c3e2f302d3e13d37817817133f13b68023c3e2c4f1f148487363921fd05a33b27a166b1331f39311f92013d13397e12782221f3941fc0293e3d37b32869264492e6804943b7c122a5f43513861f8304e3f112b5e32a5f422439647b30494812b4f5a4e43392a7c304c2a2e2a692d683532e3297b2014813f22a4f292d692532e2c7e01494b285f33f582345d33e3904a22817e2b4f212392e7a21023e4c2811289591222f2e296a03c4f1f14e259591332b4969203e493228128a4f21242a3483d392%N);
  (10%nat, 0x102826d1f13a32f12e55b669210248592a7d113c2f2d4125b616a01f82d7c162f4c3215b1f69204a4f1f327d13d4f21258375f2012847e2a2a4d11215a295f1207f12c1fb43692314f2b5e2012a21692d3b4f2314f2b4c29307e12c1f8416f1125812a4c2b04c2d1fd12f4f215825e22b07c32a21fb166812134c31782013286c3a126b11324d45c12d07a1f531fc36b1515d64a2d06b4651fd126c1324d66f3078295111fb36c12214d646a306b2f1329b4c244d2a6b306e2b522a782c4f1214f32949382016a12b3221fb6c2114f2c6d016b3a287832e58236936802c5215d5d4b4214c2e692102683b1129a4b2414c2e16a%N);
  (10%nat, 0x1015c5f25d294f2833827968012a85b5f32b39236936805f25b1793d216e5e2102593695b112a4b2923d16c268029a55a11f4871f333b6c168205b5f1225b15f7343936b125d20145c5d273e1136b15f1202991428c431f2c2b56935e2012215d5d74282b56935d130298145e4e12c173a369125d305d528e177733f5b25e23028e32228c161f12b2b1f5b315f205d13793e122c2a2a21f5b45c15028c4328d33872b55e65b501fd426f3e1222c3d355b65e3028a61128c322c442f65b155d301fd716c2b3d2c42b285b26b30288266e282e5382e35358316a2011fc1626f1f2e5382f1155b46d011fd297d2c36582369368%N);
  (10%nat, 0x102ae135d28a24682f2a38302ba22ae2c51211fa3292f2012ad227f4e392111fa2c3a012b92ac33c23693680217b7b4217f2e2e21022af112ce2416a22a2e3802af129d3f3326c294f202ac321681fb3436c1f34c20412aa3951136c1f4f1202af6b5943384356c658204d682127b6e4356c658302d298329b13d17136c6159024b6a7d3a712b2a737a25a02ac229d1652b1337c314e20128e2a912282c2227c4590294d6936a5b3282e266c284f0596a7d49122812d437964d305f691129d3282e4227864c305b6915e7a3b46f5c305f695d2e4a2832f3286835a2%N);
  (10%nat, 0x1029b3a2c9122935594c62b302a8442a114c28a32b65c4962a302a842a17f4b3f285d483a302ac2862aa2e293535c3e3382012a92c22aa2e2a1155f3e3e012ca7d4a2c32b236934a2d012b2497e14a5693c3c21022a92e2a8113f4125a713b3e02c93e1f816393216b3a3e202bd327d4a14a2125a1f3833b2042a92a2d11216c383e1202c87f293c432e2316b2e3f207c212aa482316b2e3f30687e2ab413c1126c2e148027c2b813c211fb2292f02bd22ae162d12137f313d2017c1fc1f3d123811325f3844805c7d32af3381516b3c3b02ad6a6d12391321f863c302ba112ae33912211f8642f3%N);
  (10%nat, 0x1012ab2c111fd6d111129f4702932a92d122d92156c6802af12d11f978121329c63302c29f2e1112d831225f5b62302829e3812b2c9429a29302c29c312e2a2bf136b5831f2012929c32d22a1fa5c2229c2d012ba38282bd3323681368029a3a22816c7d212992b21022929a23a28112cb16c4c2d02aa33391f11f94c2d6c4b2d202ab342b322816b7e35f54932a203b4297f5b51136c492d1202a92c2a2bf43656c3f2e2042828212a4e495f56c3f2d1302a8172f2b2ac12c36c3f12c30732b2c913c1fe241f2302a812b2827d2d4b1661f1fe312c202a1f2cb121f21f1fe4291502ac71f34a28d32855e65b5%N);
  (10%nat, 0x1032cc332da314f2b25e0382885e276e395c21212a911012cd462cc232126815e2042a2ce372cd5134c2b6802832cc22dc32122a83042812cf11142d93329f1201f62cb121328b592b9130472994f1212d8352a8211011612d811217a3a5b1154f785011f2dc2dc21216836801f32cb121212d82ad321021472cb31117e78415a295d503282c9512d8326c5c52052d9121211ff6b35d75a322012d92412d911216c5a512032d9421fa6d4325d7586202832bd42122d956c586302d2bd1531f81f5d13136c58170122aa2a42da13329d27102bf2b13228b5c13329c3142%N);
  (10%nat, 0x102a7b46c212bb42b5493a5d1303911fd17515c7b6839348162c5d3022a66d73215b28c7a29c2302e3177e12a164d22c82b1f3b1fb2042e6f2a124f1fa682a21f3b1f8150481f7b734f312bf385e65b50761fe281259328c5e353e67b302b62c79441359117e7f64c1f6a3072f37e45d12de65d6b30283387f54e62db21534d76a20163a17f55a222da1155f6d01491fa35d12da1236936802971fc15e27e7c154f2969210243821fa6812db111126916a023a2cc37d2b68121368692033382c93212da121258295f203a11fc5d47e7b11216c5f1203c1fd6871fc68234685e202cc2167d6f2316b25c303a12ce228a6912116a25e%N);
  (10%nat, 0x102a83b412885b51136c15e1205c29a433e2cd4356b15e203d22cc212289584356b15e302d3c1129a14b32ca17136a1168023b221fa2d14a2cf73597d0582111fa2e163c22cd1336d692013c41fa2e123e2da2225b296c0293f1fc2e33e329858264d22c68048241f812d12482a849436d5f304d2311f82e348112d84224f7b304877f6b12bc3844e17c304a321f932e2c2e7c3a3b2f35927b2013f1fe32e4922bb38258127e014d1fc2b34c7c3b383a234c2c3680537e6d22b9139215a7a21023d1f7e26d29838113a14d14296a03b297c3365e2b813b4c2f69203c357e345e322884813934b385f201fe394c42ba2f1134a1385f1203a1fe2b434f28c4b2b5491395e2%N);
  (10%nat, 0x106f1f28b163c2d83216b69206e37328913c321fa1f692126a5f201728d2a2a42da11216c5f1206f1629a432d2dc2316b5e20728f3d212db2316b4c29306d17128e413a28c681126c53f2b05229a1392de217b3d22b06b731299162b22db12132a92074299122d1fe285e1132783d12d06a2e28d32d32db1516b53d2d05e4628f122f2ac481327959306f6428b32f112db122178134d306822a2ae131ff6824785b3068432928b2c622d81217b5b201692c28b382228c29492117a15e012f833b2dc23693245a012e2ac211f82a5b4217b59210258612e2ae112ce2416c35f05d12994c17a2f5a3326c25f205d132c83212cc3436c15e2%N);
  (10%nat, 0x1033a2829825b15a5c211f29d21021f8212f2822985b1129811f5c6a01f83828331fb2b5a12996c69207f32f3634289325b15c5a36c5f2012f2828f245c28d1136c5f1201f812e282c494a4352dc56c5e202f284281fe215d5e4e56c5d1307e162911f171fa1295e387e36c5d3061f228737f1282ef29c2307c2f311f12b7c16322882b4f1f29f201f1f4282a7d1252de21f29c1507b1f4877d3532896a55e65b506f676281fe1272de352a8301f9134628447e37111fa7b65c6a307931f3b4693e12db285d6b30796733a6b2e4628e5c3535c6a2017b173d6b2e1f22dc1155f6d017c428c2c32a2dc23693680643f16813f22dc5696921026f21f3f69114829b4e41269145e%N);
  (10%nat, 0x1011fc1592c54295e2261f86b112ba011fd42d8432cd2369368034b2e3612d592128d5d2b821021fa164b2e367a112d8416c6a01f82849391f8211ff68326c69201fa64b32e33a583212db36c5f20159397f4122cf1136c5f1201f81583947c3132d856c5e206928483947d21228b5d56c5e302d68164b13811f81131fe6b136c68027a638272a1f812de32af07c28483152b137c1241fd45e2af201683838452c27c1122da22ba0297a1f492e7c12128a5f63696806f6486312d7d122dc32ad301fa3538632e7d1112dc22529e301fa3382828e15e595c4529f301fa62f3635d4e15d128c32829e2011fc12f28328b115d5b5a2282a9011f854c289325b4d6a2369368%N);
  (10%nat, 0x1029c35a287c132cf294c456b3029c65937e622e2ba3534b286a20129e1592b3858222e2bb254e286d011f83e6e7c2c37c5f236936803c5c4f4f212db55811f69210228c625a2a7e112dc12582816a029a5a2b37c161fb6b16b692029935932c6f3212db2126a5f20159594e412a2be11216c5f12029a1583d6e6432bf236c5e2058593d6c2122d92316b5e30684d215912f7b3412ce126c68024d34f22f32d591f11fa6c2b8028e59312d76c26162bf212ac2014e15942d66b29127f69232af05c4f1692871f5b3732ca56c6801fe34e62b2d5d1f122cb322ab3028a134e641f142b5a11632cd32aa301fd64c2a7241f5e132d82ba3028834e3295317a262c2ae32af2%N);
  (10%nat, 0x1029a67b66d49127914e34f17c3028a3a37866d113f35c2d4e224e7c301fd3f6e7c12b7c2b5844d7e302883c7835c2e2a2e5f6934f37c2011fc128d7c22a2e5f6a24f37f011fd3d28e59282c32ab234e2a368036d7e22817f6a214c1f821021fa13f6d1f828117e6c14c22d6a01f84a6b1fb1f162be4b332a69201fa3f6d37b322812be4349342b5f20128d3f4f4292a2ad113493a5f1201f8128c1fb2e436f5c253f3c5e204a6a1f9212a1f95e53f4385d1307e161ff14e4b2b412bd33f172c5d3065a21f93812cd3b736e2307c4a6a313d5a22e166f5e1f3c11f9205a5a47e3a127a5d21f3d7e15029e1f6b7932f37a6b4d2865b506f61fc647a38122b82353f1f8301fa33e5a67e112e32bc63f4456a3%N);
  (10%nat, 0x1013c15e35d5c1246863b235e7802bf13c2a835931f5b73c56c6802b931f96a5a1265e4b322ab302bd131f96a115835145a144832aa302b867f6b136b59243c6b6e302bb31f9329582582c4f313f32af2012af11fc6b22582c4f448112ba012b842d84e329a2369368037e6d216e4d613f686f21022ad167e6f115f64d63e416c6a02ab287c7913f7a4d325d769202ad67e36a32129934e36c5f2011fc6e414c6c4f1136c5f1202ab11fb7a3f431f5b44d56c5e2028c287b7821228f44d55a295e302d28b167e17933d178159136c68021f83c7922f58491795935827c029f287b316f23f166b134d5a7c2011f9291fc46d4b127824c25a27d0291fa3a2cd34835a2f4c64e2d68%N);
  (10%nat, 0x1061f915b6f21fe73299230492a81fb7164d26c316f2b21529f202b81fa124f7846e2a235596a1502d91f782934f32a92e3835b65b503c639a12596e614d4a3232a8304f329c7b7359116c61fb33144f6a302cf32c814d2e3585b244f6b302cf67d74e64c2e31fc35315b6a2012d911fc5a24c2e5e492545836d014d29c1fa35d4a7e4a2369368029a2cc24a11f671fb5615a6921022bf622cc4a112c5d4e1265b16a02cd2cf491665e34c15e569202cc31fb5d324a12a35f4a2126a5f2011fc5d44b2a28b11216c5f1202cd11fc5d35842783c236c5e203c29f214c28783c2315e55e302c9213c2a94d413116a4b126c68033a25d695a156a3495f7802c91fc45e2581516873c212ac2%N);
  (10%nat, 0x10691fe2cc2127d6c4356c5e302d6811fd29a14b37d16b1713592a68024d298229814a1f826c7362a907c1ff29a163c27d316b1331f29f2014e291fd29c123e1f946c2221f5c6d0294f28f1fd2e33e32d9264492e6806f1fb329812487f66c43515b6b305f2982299348114b4966c42244b7b305a29b22cb12b697f434c76d305d3ae2c2e2a6937b3534b7b20159138d384922a697f2534b7e015a29b29834c282cb2345d368032cc2281681f9212587a21024f129d2ce28115f1fb1224e296a04d2a82885e1f15e1fd1335d69204f29d1fa69322815d311f821245e5f2013ae4c4295d1fa11216c5f1204d139f434f6f7692b236c5e202a82cc212a5b782b2316b5d1304b1639b15c2b5b11fd1254f1f5d3%N);
  (10%nat, 0x10129c2a2a43b6d6811216c5f1203882a9432d2896a2316b5e2029e3d212886a2314f2b4c29302fe129e413a28916a1126c4c2b07e2695f13928926a2129922b02fc12ab162b21fe316812134e7a207e2ac122d28a45f113228e12d028c2cc5e32d328f5b1516b4a2d01fe1f82a9122f28865e132587a3028a1239832f113d68645a12212aa301fd47f2cb131fb2a59245c6f302881f92ab2c623d5d3294f1212af2011fc11fa2aa38221fb2c4f2112ba011fd1fb29f33b5929a235c536801f82cc211fa2e4d4212ad21021fa1fc2ce111f92e4d2415b286a01f811fd2994c14f486c3326c69201fa1fc2cb3217f3693435b285f20139d3b414e486c51136c5f1201f838f433e1f86c435592a5e2%N);
  (10%nat, 0x1039911f81582b29a28333926c692039926a2e15e3229a36343936c5f2011fa5d2429a283e146c5f1203996c6d43529a282c2a156c5e201fc5f212992843b156c5d13038f11fc4e12929a11f172f335d75d30262ac12829a2287333c29c23038d12bc163228f311f12b2b1f29f201f5a7a12529b4282a2a29586b15039c2ad3532b972a155e65b5038862ac127299628282c352a83039a122aa371128f6284412e65c6a3038a344e5e3e128f3b42b363c386b3038b52982e4628e33a2e3535c6a201389312982e1f228e292b2f165f6d0138a32982c32a2db123693680628d13f23d6e3f12e5696921023882299114828c3f2d4126916a0388129a163c2892a4b3216b6920388229b13c3228935f2126a5f2%N);
  (10%nat, 0x1032cc212ad2e331212ad210239b72ce11729d2e321316a26a039911f2cc212ab393326c692039b72cb3211f29a32e3436c5f2012db4122a8395146c5f1203992dc31329f42d42156c5e202fa287f6c2122a83942156c5e302d2f911f2cd1132a8138152136c6802389262bd13f1fb2342a4332af038d292cd12429c3152b1332af2012f91f282bd1122a8452c222bc02938a282bd1213d28b2e26369680388632cb122a8632e432ad3039b262be1113f1f8632e4223229e30399237f6812a8283384529f3039c57e168129f3632f32829e20139a317e6811487e363382282a90139b37e5f322ba3812369368031f9169229d2833a211f29d210239927f116a3f7d28213c11f5c6a%N);
  (10%nat, 0x1013bc312bf222e2a82a164e286d013bd32cb2c32bb123591f36803c2cc212be2b155811f6921023bb22cc112bd2a1312582816a03bb12cd162ae2b3216b69203bb22c93212bb3762126a5f2012ca412a229e2d1316c5f1203bb2ce64329f2e12316b5e202e92cc2122b92e12316b5e30682e812ce3412ac12a321126c68022de122ca21f12ab22f2132ac03af12ce261629c312d1213229f2012df12cd29122a842c1422ad05c2e82ce3732b8281516b68039f32cc1f122a28d62b1322ab303ab122cd11632a8641f12212aa3039e422cb132ae2a7213529f303a942ce2612b28b32951212af20139d152cb2262a82c52112ba0139e62ce432cc1235e3368%N);
  (10%nat, 0x101339a3d22cb12b2bf244d2156e302ae7b3d2ce2a2e2a81214f317b2012139a13e2cb22a32b2a8224f3147a0439a3f2ce282c32aa1234e2a35c403bf32cc22812a2ab4214c337822103138f482ce28112bd614c213376a0238f1492cf1f162ae624b332a5c52038f482cb322812bb34349342b5e12012fd4291f32a8514493a5d21203892e4329f6153f2841f5b122038e4a2cc212a2b96153f438594130238c1492cf2b412ac15333f173295a330262be3812ab22f3b73369223038d4b2ce22e1629c3161f3c12b6d201f4a2bd3a122a8441283d2a6b15039c4a2bd32f32b8154d7265b5038863c2cb138122a864353f286f3039b23f2bf112e32a865163f44146a303993b32bc4132bf28364c456b303be52bb622e2a8373534b286a2%N);
  (10%nat, 0x101f33bf32cc2e3b123c93043bc122cd115833c8302933bc422cb133ad6d3028c2af42ce2583cb2012a13bc152cb222a3d3ce0763bc62ce4e33cd063bf32cc2148c2102b13b972ce11293fb02283b911f2ce13f3dc2063b972cb32148b2053ba12db414c3ce12063b92df3f433ce2043ad282cc2122b3ee302a23ac11f2cf33d13dd0523993a22cc4913dd1033ae292ce23f163cd11012139a291f2ce4b1229f2bc0239b392ce34832eb17e023b9632cc49122a9326c5e120439a3a22cd113f32a812214e2d5d3%N);
  (10%nat, 0x101289122bb1f2bd3ba6a15028932cb2bd32a7f2ff503b61fa122be62be48f301fe32cb122bc112b7c28b1ff303d3ca342bc14d5b38c302882bf52bb64c5f3892013b28a2c8312bf24c5e38d0481fb32c832cb33f5f38c033bf62be24a12ef792103c13c822cc1f3a113da03b3ca12ce49163cb2063c822c9322a2f13d82041fb2cb12ca44b3d812031fb2cb2ce5843c8203ca2cc214c797b2893013bf12ce4d416c2ef033bf122cc5a16b22ef031fe2c812ce22b3c12ea6f2013bf12cd5c126812f903bf2ce35936829a6e%N);
  (10%nat, 0x1023b29c12ad262be29d2fb032991629f382ad248c2013e129a122a928292ab3a91f904829a32a9282bd348f04c299122aa3392aa41fd38d30428f32aa262bf1148c304b33c8232c812b3fa302992ae52aa2e2a3fb2014c129a2af312bf22a2fe1ff04e28f32af32cb287b39a03bf32cc22817a3982104d13c822cc28112fc1ff04c2892c812ce1f16f39b203c822c9322817a2ab7b202982ba12ca42979398120288432ba2ce1fc2b96e203ca2cc212a6d39a1301ff12be12ce2b6e3993012be262be1fb638a230288162af12ce21ff38c2%N);
  (10%nat, 0x1029f2aa2cc213fa2930129d4129c12ce3fb2b028f2a129c23f29c2ab2cf22b02aa1628d12ce22a92ea2012ab122994929b3fc12d02ab32cb29b32ac2cc2d05d28f2a1229c3f29c2ab1fd7d302a832cb1229a112aa2e9305f3ca3c429a132a82ea3028e2b2c2883e29f22ac1f97d2015d2ac29e3c129d222ab2eb02e81f329e3c2a929e62ea03ca3f29c2129d2ee2105e128f2b83b2aa1148d05d29a2af3912ab129a2f92063c83b29f3212489202a92cb12a84129c2887d120299432cb2ac52992ee203e3ca392aa21229828a7e304829812ad3912ac32992fa%N);
  (10%nat, 0x1041f95d1ff12ca448c120328b3c431ff2ce48d201fd2cc2cc2148b13011fb2a3b128b12ce39d7e3062ad128b262be48c23062ad161fc12ce248c2012bc122881f2bd48d150281fb3f32982bd339e7b506e62ad1228b62be48f3052ac3298122bc1148c3078628f2ac342bc148e302828b2e28c52bb648e2016e291f92a2e28d312bf249907b628b2c328d32cb48f0329912ac62be248d2106f129a112ab22cc48f06e2882b1629e12ce48c2029c12aa22c93229e2ed20429b2a29812ca43be5d120329f432982ce48d2%N);
  (10%nat, 0x102882cd1fc28f14d138828b2062ad29a2994932138c1fe202dc2fe14a4138a2881202af2c432fe4e38c21fe20793ca28f4c2122fe28b307b2ae2c11fa28f14e32ff28c026e2cf11fa262be38b28d032cc167c28e4f248c2017912b82c127e281ff4d39928907b2cd37e282bd348f07f62be127f328f4c48f3042ca37f262bf1148c307e31fb2cc232c8148e301fa695f3b52c938f1fe2017f11fb691fc312bf249901f937f5f31fc32cb48f037f12f2ab32cc248d2101f811f8112cd22cc48f07f1fa12d3a28d12ce39f7c2037f12cc22c93248c2%N);
  (10%nat, 0x1032cc11f91fb68248d21029a12a93b111f822cc48f02992cf167b12ce48c202cf17f22c93238c1ff2042984d2a6d12ca448c120132da436d2ce48d204f2da7f2cc2148c305812d8417912ce48f024f2995b179229d3e3991ff02dd166a12ce238f1fc2014f12995c126e29f3d49b0592de32fe3d339a1fc028828d5f127929d3e39911fc302db32fe123c113981fb3028a28b2be29a43c1338e1fc302dd2c5d29c49239a1f92012882df7b29a13f223991fd03b83d37b29a4b38c421fc03ca29d3e2138b28821028913c82994c1148d%N);
  (10%nat, 0x1012aa1388591f816922a3fe02ac2fd3591f86d282cd42ac03bf32cc22812d82aa2102ab123be7f6e28113fc02aa2ef6a7d1781f12cd2ad203c87f6b322812d82a9202fe2ba16c4292cf2aa1202ac59432ba782ea2aa203ca7d6e212a2cb2ac13032a8591687d1782b2cc2ab30168262be2e9629c2302ee165a7c7922ed29e2012ad59126d6d1f5f48d1502ef36d7d5f32f8299502992429e5912687d66848f302ec36d7e25e112ee29d3029b2d81f931f95e12ef29e301fb6b2e6952bb62fa29b2012992d92e6a312bf22f929f029e29d3e2c36a32cb2f829e%N);
  (10%nat, 0x102ba328b2b8422cb1348b303983b428d58248c2012bb128b28d3a152cb2248f02af638e33a62ce48f061fc2ca32cc2148c2102bc13839872ce1148d02aa281fa28d4811f2ce148c2063b972cb32148b2051fb29b3a12db412dd2ad12062ff433a2df48d2028b282ac28c282cc21248a3028c292fe13e11f2cf32dd2ae0228b638a14f21fb68499032ab6b162f292ce248c20129c1388123b1f1fe5f49b029e1f828f34b1fe5f348f02aa2ff123e632cc2ef29f3042a96b34c21fb691148c302a933c821f86a12b3fa302ff581fa4c2e2a2cc2ae2%N);
  (10%nat, 0x102cc67e2cd61f9125948f3053c8127f3591148c302ce67c2984e342bc148e303e282f94d51fc4e648e2012cc29792984e311fc5a249902d962f94f31fa35d48f031f928d14e62be248d2102a83c1388114d22cc48f02cc1fa28f164812ce48c20638a14c22c9322eb2a82047f2994d11fc5d448c120338d43d1fd682ec2a82038d4c2cc2129e2a85c30138b413e12ce3c85e033c2eb13d122cc29f2a825e0339813d11ff5e248c2013d2eb123a12cd2a82a8168039933a2ce33be6802b8328d28a123b32cc2ec2aa30438e33a122cd1148c3%N);
  (10%nat, 0x1012cf17f2cf28291f9123e49b02d93bf2828b33e348f02dd66d2db3397e124848f303c43bd2628b3481148c302dc3791ff6e232c8148e302e86f528d2c2e48e2012dd1791ff783128d49249902df32dd79328b34c2dc2ba031f97b16d32cc248d2102de12de116f22cc2dc2ba02dd1fa7d17811ff5e48c2032dd16e22c93248c203a47f7f6f128d4c448c12033bf1ff434f48d201f91f96e2cc2148b1304812e96d128815c48c306792d8261f915b48c2303f63b91289164d248c2017f2d81f1fa124f48d150283bf1fa34f348a5%N);
  (10%nat, 0x103f3e2e923f1f91393fb22b03f38f12ab162b248c2016e2e9491fa122d3fc12d04a3bf1fa32d33f92d02ee3f3a2ef3f1f9122f2ec2aa303e3c8127f32f1148c302f83f382f93c429a1348b304a38d3e1fc2c6248c2012ee4b2d2f93c11fc382248f039d638f3c1fa33b48f03c5f2cd3f29c2148c2102ef13c83b2aa1148d02ee39682cf3917e4c148c2063c83b29f32148b203d5d2f911fc3b412df2ab1203c3bf7e433e48d202cf395f2d8392aa21248a302d93839e3917f14b32de2ad022cc3c5d2d82628a14a499033c8381f9163c248c2%N);
  (10%nat, 0x101f92d82cc215d3bd1306c13bf12bb1295e3bd306792d8262ac12848c23063b912bc163248c2017f2d81f2ad12548d150283bf2ad35348a502ff64b38862ac12748f3053c8122aa371148c3038964938a3428d3e148e30283af52982e462df2ae2012ff293e38a312982e1f2499038c63b932982c32a48f06d31f92cd628d13f248d21038813c82299114848f02ff1fa2cf129a163c48c203c39b229b13c3248c2047f2cf129c2a2a448c12033bf2a9432d2d92bb20782e929e3d213fa293013bf129e413a3fb2b%N);
  (10%nat, 0x101fb2f29e12db4124891205d29a29e2dc3134892038a4e682a9282cc21248a3038c28e29f11f2cd11348c022ff4f6a2b8262bd1499033ae292cd12448820138a14c2fa1f282bd11248f02c85b3bf282bd12148e039863a388632cb1248d306a43bd262be11148c3038f33e399232c815e3bf303c852c815d13bf2012bd6a13e39b312bf115d3cb039a33bf32be325b3cb031f92ca32cc25b13c821039913c822cc5b113c902ba6d1fa2cf12ba2b5a13c82033bd22c9325b13bf2047f2cf12c8245c3bf12033bf2ba43548d2%N);
  (10%nat, 0x103ba1fa2cf12cd163fe2029a2ad22c932148b2047f2cf12ca412a3f81206b33bf2ce6433f8202e8782e92cc21248a3028d6b13bf12ce3413ff022e86e4e2a9122cc1f1488029d2a912ce26163ef2012e816e2e812cd29123fe02ea2a829e2ce3733fd02d95f2f1fd2a932cc1f123fc3029c29f122cd11633fb303ab2d1ff29e422cb1348b302a829b42ce262c3e92013a92e28a29b152cb22648904be629b62ce4348801fc2d2ac32cc2148c2102d96813b972ce1148d03a91fa2c2a911f2cc2148c205963b972cb32148b2%N);
  (10%nat, 0x105d1f842ca32cc22813fb2103cc138f482ce28113fc02fb5f7d529c1492cf1f163ed201f829e482cb322813fa201f9229c12fd4292a3df1205f1f829e3892e433df207d429d4a2cc212a3f81307c29f1492cf2b413eb30242cc262be38139f5a2301fb2984b2ce22e163de2017f29d1f4a2bd3a1239d591501fe29e4a2bd32f33df502e8696138863c2cc38123eb301fa2a823f2bf112e33ea303bc57e2aa3b32c81348b301fe2c952bb622e39f5d2013ba61f92cb312bf222e3f803bf1fb2cb32cb2c33ef031f92a83c2cc2148c2102dd6d13c822cc1148d%N);
  (10%nat, 0x1013c82b13bc152cb22583ce03d863bc62ce4e33cd061fc2ca32cc2148c2103dd13b972ce1148d038a58281fa2be11f2ce13f3dc2063b972cb32148b2051fb2be12db414c3ab3a12063b92df3f433ce202ee4d2843ad282cc21248a303ad293ae11f2cf33d13dd023ac6539b3a22cc4913de033ae292ce23f163cd2012ee5e1239b291f2ce4b123dc03bf39d392ce34833db03c921fb2bd632cc49123da30439a3a22cd113f33d9303c91339a3d22cb12b3fa3039a3d2af2e2a2e3dc2013c83139a13e2cb22a2e3df03cd1f82a93f2ce282c33de%N);
  (10%nat, 0x103c93d63bc32c814d5d38a30283af51fc4e64c3ac3c2013c83c293b9311fc5a24c3dc03fa63b931fa35d4a3dc031f92cd2cc24a15c38c2103ee13c822cc4a113da03ed1fa2cf12ce491639c3e2063c822c9324a13d82047f2cf11fc5d44b3d812033bf1fd685843c8201fa3d39c2cc214c3cf301fb13bf12ce4d413cc027f33b39b122cc5a139b49033bf11ff5e25813ca2011fa13b39b12cd5c123cb01fc3bf2ce35933ca03c91f33bf32cc5a123c9306943bc122cd115833c8303c92933bc422cb1348b303bc428d5825839b3f2%N);
  (10%nat, 0x103c94c63b93298124829e2f83043bd2299348111ff38c303c94b33c822cb12b7b38e307c3c829a2c2e2a7c38e2013c84d13ca2994922a7b1399048833bf28e34c287c399031f92ca32cc22813bd4d2103ff13c82ce28117939a03fe1fa2cf2885e1f17813992033bd2cb32281782db4d2047f3de4c4296f13991207e34bf434f1fa39a201f92d82cc212a6e39913013bf28915c2b6d1399306792d8261f915b48c23063ba289164d27f39c2017f2e81fa124f1fb1f389150283bf1fa34f3288389502fe5a3b63bc1ff12591fc638c3053c81fa3591128823893%N);
  (10%nat, 0x107e16e2e92ac122d2ad2ce12d04a4ba32d32aa2ce2d03c95d3f39a2a9122f2ac2ea303e4bb32f112a9122df303c95f3f39a2cb1329e42e8301fb4a38d2ab2c6229f2ec2013c85e4b38f2aa382229e12ef03a829d638f29f33b29f2ef03c5f2cd2cc212a92ea21049813c82ce1129c2f8048f39682cf2994c129b12ef2063c82cb32129b2ef203d5d3ef3b4129a12ef1203c4ae433e29c2f8203c93e393a82cc2122992f8303fa3839e29a14b329812fa023bf3d3c39e229814a28a38e033c829a163c22992fa2013c83f13bf29c123e28b292fd038a7f3bf29c33e328838e%N);
  (10%nat, 0x106792d8262ac12848c23063b912bc163248c2017f2d81f2ad12548d150283bf2ad35348a503c96e63bc62ac12748f3053c8122aa371148c30782e87863bc3428d3e148e30283af52982e4648e2013c86f293b9312982e1f24990793cb63b932982c32a48f031f92cd628d13f248d210783c813c82299114848f04a81fa2cf129a163c48c203ca3c39b229b13c3248c2047f2cf129c2a2a448c12033bf2a9432d48d20782e929e3d213fa293013bf129e413a3fb2b03f3e2e922a91392ac2ce22b03f38f12ab162b248c2%N);
  (10%nat, 0x103c968283ca2cc2122ff28a306d3bd293bf2cd1132fe128c023bf6a63cb262bd1499033c82cd1242fb28c2013c87a13bf282bd1122ff28f04ad3bf282bd12148e03c97f628b2ad32cb1238a28a3043bd262be11148c303c97e33c8237f68148e303ba3c857e168148e2013c81f813ca317e681149904bb328b2bb37e5f3248f031f92ca31f9169248d2107a3cf13c827f116a48f04b91fa2cf11f81582b48c203ba33bd21f915e3248c2047f2cf11fa5d2448c12033bf2ba43548d201f92d81fc5f2148b13013bf11fc4e12948c3%N);
  (10%nat, 0x1047f2cf12ca412a3f81203bd33bf2ce6433f8203c94f3ca2cc21248a305c3bd13bf12ce3413ff023bf4e33c822cc1f13891fe032992ad12ce26163ef2013c85813c82cd29122fe1ff048b58e3732fe1fe02a839e33ca2cc1f122ff1fc30458d11632fe121f9302a83a833ca2cb1338c41fa303c82ce262c2ea1fe20129f3aa13ca2cb2262fe128904be63ca2ce432fe289061fc2cd2cc2138f1fc2104cb13c82ce1138a28a04b9281fa2cf2cc213891289203c963c82cb3213892892051fb49b4122fe1289120658e3132fe28a2%N);
  (10%nat, 0x104b94a1fa2cf2cf1f162c812ab2038d3f3c82cb322812ce2ab203e1fb49b4292a2ba12ab1203f5992e432ba2ac203894a1f92d82cc212a2cc2ab1304b3bf2cf2b412be12ab30629c2d8262be3813ea2303c3c82ce22e162af2ae203bd17f2e82bd3a122bb1f29b150393d82bd32f32cb29b502a83ba63bc2cc38122be629e303d3cd2bf112e32cc229b302a838f3c3ca32c8132ee29c3039d393c852bb622e3ed20129f39a383cb312bf222e3f804bb3c3bf32cb2c33ef03c931f92cd2cc212ed29e2104dc13c822cc1148d04db1fa2cf12cd163fe203b963c822c932148b2%N);
  (10%nat, 0x1061fc2ca32cc2148c2104fe17e2ca72ce1148d04ec281fa2be11f2ce13f3dc2063b972cb32148b2051fb2be12db414c3ce12063b92df3f433ce202a83ac283b9282cc21248a302aa3ab293ae11f2cf33d13dd0229e3ae63cb22cc4912bd2a8033ae292ce23f163cd20129f3be13af1f2ce4b122ba2a904e83bf2ce34832ba2a802a839e3c7a2ce632cc49123da3043bd22cd113f32ba29e302a83ca33c822cb12b2d92a8303c82ce2a2e5f7b2a820129f3cc13ca2cb22a2e2ba12ab04be3f3ca2ce282c32ba2ab03f1fc2ca32cc22813fb2104ed1792de2ce28112cf2ac%N);
  (10%nat, 0x10129f4e3af3cb312bf24c2e3bd02df3bb7e2d832cb4a2c33bc031f92cd62be24a13d921058f13c822cc4a113da058e1fa2cf12ce49163cb2063c822c9324a13d8204395d2cf12ca44b2a3bd12033bf2ce58433bd203d2a81fb2cc214c3cf3012cc1fa12ce4d413cc033b2a821f8122cc5a13cd033bf12ce258163bc2013b2a811f912cd5c123cb02cc1fa2ce35933ca02a83d933bf32cc5a123c93043bc122cd115833c8302a823d933bc422cb1348b303bc42ce2582c3ae20129f3dd13bc152cb22583ce04f963939a62ce4e33cd%N);
  (10%nat, 0x102a83fd33c8232c812b3fa303c852aa2e2a693a920129f3ff13ca312bf22a693ac02ab4e3be3ca32cb285f33ab03be1fc2ca32cc22813fb2105a813c822cc28113fc02dd3c91f822cf12ce1f1583ba203be3c822c9322813fa203bd1fb2cf12ca4295d3ac1203be3ca2ce69433ac203c91f92d82cc212a3f81303ca3bf12ce2b4e13b83064ab2d8262be6b13af2303bb1f82ce12ce269163ab2017f2d81f2bd6d123ac1503b81f82df2bd36a33ac502a83ed63bc62be6b123b8303bc3cd122bc116933af302a84b3bb3ca342bc14d3d8303b83c852bb64c2e3ba2%N);
  (10%nat, 0x102a81fd3993ca3f29c1fd1238e307939a3ef1229a111fb338d302a81ff3993ca3c429a1348b3038e3c83e29f21fb2c2fb20129f2e7b38d3cb3c129d221fb39b039d65d93c2a91f9339a06e39c1fc2cd3f29c2148c2105b913c83b2aa1148d02ba6d39f1fa2cf3912ab17a3a92063c83b29f32148b2039b1fb2f912a8417f39b1207e39c3ec2ac7a4339b202a86839f3ca392aa21248a3029a6f3a83bf3912ac37813aa0229e6a39c3cb262be7c13ab03fb33c8382ad27a1639a20129f3f913bf28292ab7e123a9029d3fd3bf282bd37b33a802a85a3bb3bf3392aa7c1239f3043bd262bf117a339e3%N);
  (10%nat, 0x1017f2d81f2bd298122f9150283bf2bd328d32f9502a84a863bc62be28e122fd303fc53c8122bc1128c32fc302a84aa63bc342bc11f839d30283af52bb67f2e2ff20129f3f3f9293b9312bf27f2e38a05ce63b932cb7d2c3389031f92cd62be27d139e2105ca13c822cc7d1139f02cd3fb1fa2cf12ce7c163982039c3c822c9327d139d203fb47f2cf12ca47e2a38a12033bf2ce1fb4338a20782e92cc217f38a293013bf12ce1f8412fd2b03996e2e923f29c1fd12fc22b07b3993bf12ce21fb163892016e2e94929b1ff122f912d07c38e3fa29b31fc32f92d%N);
  (10%nat, 0x10229e2fb2ae7b2df262be29f12f8033c828e4f229d162df20129f4ac16f2df281ff4d2a9122ee05ce3bf282bd329e32ed02a84b963b9328f4c29f122ec303ff43bd262bf1129d32eb302a84b833c8232c815e3bf3039c3b52c95d692ee20129f4ba13ca312bf25d692f905dc34d38932cb5b5f32f8031f92ca32cc25b13c82105db13c822cc5b113c905da1fa2cf12ce5a1582ff203ff33bd22c9325b13bf2047f2cf12ca45c5d2f912033bf2ce28c432f920593f2d82cc215d3bd13013bf12ce5e4e12fd306792d8262be28e12fc2303fc63b912ce228c162f82%N);
  (10%nat, 0x102a84893ca2cc212aa2e9305ab1782de12ce2ab412de0229e2df2ab3c8229d3e2b812df02ab3bf12ce22ae162ce20129f1f3fa13c829f3d2ba122dd048b2a84e83d32af32dc04bf2ab2c828929d3e2b8122db302ac4dd123c112ae32da302ef2d92ab2be28b29a43c1348b302a83c829c4922ae2c2c82012ee2dc29f2bf28b29a13f222ae2e804be64eb29a4b2ac32df02ae1fc2cd29d3e2148c2105ec13c82994c1148d04b92b91fa2cf28f14d129d2ee203fb63c82994932148b202ad1fb3df14a412aa2e81202ae4da4e29d432e8202a83a2ce2b93ca28f4c21248a3049b2ba3bf28f14e329b12ef%N);
  (10%nat, 0x102cf1fb3bd16c4292bb2be1202d84b8782bf432be202db1f92d87d6e212a3f81302dc3bf7d1782b2ac12ca3063bd2d8262be2c912c92302cd3c87c7922bf162bd203ab17f2e86d1f5f2cb122be1502ca3d87d5f32c832be505fc62a929a7d6682c9122ca302ce6d2ef7e25e112bf32c9304b82cd2ad29c31f95e12ab2ea302bc2ca3c852bb62aa2e2cc2014ba2c92ae29c312bf22aa2e2cf04bb2cd3bf32cb2a82c32ce036d2b2cd1fb6822a812eb2105fd13c822cc2a8112ec05fc1fa2cf12ce29f162dd202ae3c822c9322a812ea203ef47f2cf12ca42a92a2cf12033bf2ce2ae432cf2%N);
  (10%nat, 0x1068d281fa49e12d82bb2062ba3d932148b2051fb2be2dc412dd2ad12063b92df2d8432ad205ee282ac28c282cc21248a305ef293ae11f2cf32ce12bc025ee62ad29d21fb682da12bd03a833ae292ce22d8162ac2015ff12aa28c1f1fe5f2dc122bb03df3a93bf1fe5f32d932ba04bf2cd29e29a632cc2da122b93039e43bd21fb69112d832b83068c329c2ab21f86a12b3fa304dc3c81fa6b2a2bf2bb20168d129c2ad1f816922a2bf2be04be2d82b82991f86d282bd32bd02d81fc2ca32cc22813fb21068e13c87f6e28113fc04b92db1fa2cf7d1781f12ae2cc206d2d83c87f6b322813fa2%N);
  (10%nat, 0x1031f94f3da22db12b82106b8158f2db112b906af1fa49f2da162aa20658c322db12af2058b47f583da42dc2af12058c358e2e9429f2039b58f212dd795c3012b93dd2de416c5e039a358f2eb16b25e0589358f22e912a92039c158e2ed1268168058e32ea36868069b328d4892eb122a830458d112e9329f3069d328b48a1348b304fe58f22e92aa20169e128b48a222e92ad069a65992df32ac061fc49a2148c21069f12b83de1148d%N);
  (10%nat, 0x1012d84ef1794ac22bb2dd02ce34f8358e2b92dd03de31f949a22b912da2106c9158f2b9112db02be5891fa49f2b812da203dc3589322b912d9204fa47f49b42ba2d9120434fb32c93cc48d201f949d212bb2cf13012ab3dd158f2bc2cf30158967949f48c230164fb6589248c20124fd17f49e48d15034fe284fd348a502ac122ad3d967e49a48f30358955881148c306b967c49b12de2af3058a284f862dd2b82012ae588297949b22dd2bb02ac358c65882db2bb%N);
  (10%nat, 0x106db3f384bd1348b302c4cb4a4dc248c2012fa4de4b2d4bd2248f02f83584cb64de48f03c5f49a2148c2103bd49c158f1148d02e84f8396849e148c20658c32148b204e93d5d49b4148b120435f49a3c4ec48d206ba395f49d21248a302c914f9384ee348c022c812983dc3c5d49f4990164df358f248c2012ca124ec17f49e49b02cb34ed58e348f02ce124ee66d4ab48f30328f3dc458d1148c306bf3794ac12bc2d9304f94f82e2bb2da2%N);
  (10%nat, 0x1039a124cc64b4cd48f3034ce55881148c302fe4ed6494ce148e302e4cf284f8648e2012fd2e4cd293e4ce249902fd2c36e3fa658848f014ed31f949a248d2102fb114ed158f48f02fb164d4a91fa49f48c2014ed3c4df3248c202a7b3ec47f49b448c120434d9358e48d207848a784ae213fa2930414df158f3fb2b014df3f3e4b83fb22b016793ef3f4df248c20124db16e4af3fc12d037e3ed4a4db33f92d02f8124dd3f3a4bc48f3034df3e4de1148c3%N);
  (10%nat, 0x1013b8124b914c4d949b03b934e3fb58e348f03bc124bb63a4de48f3034b9458d1148c303fe3fb33e4df15e3bf305f3ee58f5d3c82013be4bc13e4df25d3cb03bc3583fc358e5b3cb031f949a25b13c82106fc158f5b113c903ac4ce1fa49f5a13c8203589325b13bf204bf47f49b45c3bf120435c3fb358e48d201f949d215d3bd13014ce158f5e3bd3014ce67949f48c230164c86589248c2012394a817f49e48d15034cb284fd348a5%N);
  (10%nat, 0x10239d14ac6e4e3f949901649e29d3f9248c20139f122d48a16e4af49b03a834a92a83ed348f03de124aa2f1fd3f948f3032e48d29c3f81148c3078e2d1ff3f81348b302c4982a83ee248c2013e83848a2e28a3ed2248f03de35bf63f848f048c1fc2d3fc2148c21078d158f1148d03ce4bd1fa2c489148c20658c32148b204b3fa1fb2f3fb4148b120434af29a3fe48d206ed4e683ff21248a303af14be28e488348c023ae14ba4f6a3ff4990164ac358f248c2%N);
  (10%nat, 0x105784a9212a3f8130149c3793fc3d2b3f830149e7a649b48c2301648d31f849b248c201248f1358b48d150349851f948f348a50488123b3ed2458948f30349b1fa49a1148c303ec5a3ef1fb49a148e302e49c31fb48a648e2013eb2e3b3ee1ff48f249903eb2c349e1fb49a48f014ba31f949a248d2103e9114ba158f48f03e9164ac1fa49f48c2014ba29a3f93248c202a2b48947f49b448c1204349e358e48d2039a4b8784ae2148c3039a414ac158f48f%N);
  (10%nat, 0x103ee575884148b120433ee6558c48d2078f28558a21248a3049d13f929358c348c0249c13f961fb49e49901633ee31f849e248c20149e123fe11f849d49b049f33ff54e838348f04aa124887f449b48f3033fe47d49f1148c307ad37a4893912b3fa3048b34ed2e2a3fb2014ac48917a4ab22a3fe04aa31f3fa57b4a8283fe079749e22813fb2107af16f4af28113fc049a49b66f4ac1f13fb207a649b322813fa2048c77a49d4293fa1204348d57b3f83f48d2%N);
  (10%nat, 0x104cf163f9658c48c2013f9664cd483248c203fd434ba5d448c12043ee324bb6848d202df3fd558a2148c302df413f9134eb3848f022ea13eb3358f499013eb334c84a2b248c2012ec123e85158e49b02ed33ee54fc5348f04cc123e84358f48f3033e85458d1148c307be32e4ef1348b303fa34cb58248c2014ce3f812e4ef2248f04cc33eb654fd748f062d4f92148c2107c812b4ed61148d04bc3f928658b148c203ec62e4ed32148b2%N);
  (10%nat, 0x10149d4358c248d2104be1149c5158f48f04be14a964bd5e48c20149e335893248c2049f434cb4c448c120324bd43293d48d2049f558a2148b1304a8134be15c48c30334bc12f3b48c230334bc164d248c20134c8124f48d150544ba3392d348a507d8244bc125948f3054bb3591148c304da3ff6588148e30488364b94e648e2014d93fe734ba5a249904d948b244af33d2f48f013ff3258a248d2104cf113ff134ed2e48f%N);
  (10%nat, 0x1017fa2f2b4ba382248f01f892f64af33b48f02d74ea2148c2107fb12b4c84a1148d07fa62b4ba4c148c2062e4bf3d32148b2072e4bd3b4148b12052f4ae433e48d207db52c4ed21248a307dd32d4b914b348c027d862e4b914a4990334d8163c248c2017db134d91243a49b07dd54cf33e348f07e9244cd1243c48f3044d93481148c304c949e34ea3b148e304aa34d82c2e48e2014c849e214dc73a249904c84aa324cc34c48f%N);
  (10%nat, 0x101f8d64d93e148e30364cd2e46148d2011f8b734ce2e1f249901f98244cd2c32a48f0324d913f248d2101f8c134d9114848f01f8b64d8163c48c2062e4b913c3248c20434da2a2a463fe120324df432d48d2054dc3d213fa2930134dc413a3fb2b03c34bc1393fb22b03c34ae6162b248c2013c4c8122d3fc12d053d4ba32d33f92d07fa3b44bc122f48f303954ae532f1148c307fc2e284de1348b3033f4a91f2c6248c2%N);
  (10%nat, 0x101f9c245881248d3044fc1f11148c3048e58c358e148e30158f34fe5148e20148d58c2158e11499048d598324ff3248f0158b434fc1f248d21048b1158a5158f48f048b158f64f82b48c20158c335893248c2058d434fe2448c120324f8223548d2058d558a2148b13058e134f912948c30334ef12848c230334ef163248c20134fb12548d150544ed35348a501f8b244ef12748f3054ee371148c3%N);
  (10%nat, 0x1017df5158e29123fe07ee55893733fd01f9e4358f1f123fc304fc5458d11633fb301f9b28358e1348b3034ee2d262c3e92011f9a2a158e22648904a94ff6558c4348807658f2148c2101f982d158f1148d01f9c2864f8282148c206658c32148b2057588412489120654fa7313489207fd28558a21248a307fe29358a11348c027fd6658b149903358b1244882011f8e1358b11248f048e589558912148e%N);
  (10%nat, 0x1063f4ef2c3813ea2303c358c22e163de20134ef2b3a123df15039558932f33df504a959c2458938123eb303d58d112e33ea304a94f93c58e1348b303934fe622e3ed2014a84f933858f222e3f801f9e3c258c2c33ef03d358c21483db2101f983e158f1148d01fbe658b16383dd202e658c32148b2043588412a2a3dd1203258c6433f8207ec54ef2a21248a307ed1358c3413ff027de334fa2c1f148803358f26163ef2%N);
  (10%nat, 0x101fb82854ef2a21248a301fb929358c33d13dd021f992e64fd2c4913de03c358f23f163cd2011f9a3e14fa2b4b123dc01fcb558934833db02cd6d843c58f49123da303e458d113f33d9302cd6cd4a358e12b3fa3079e358c2a2e3dc2012cc6cd4c158e22a2e3df01fa93f558c282c33de06d873f58f22813fb2101f984f158f28113fc02bd6de4a658c1f163ed2063f58c322813fa206e93e75884292a3df1203f558c2e433df204a54ef2a212a3f81304b358c2b413eb3%N);
  (10%nat, 0x102a7ba4358844b3d81207ce3258c5843c82054ef2a214c792ed301358c4d416c2ef0334fa2c5a16b22ef07c83358f25813ca20514fa2b5c126812f9055893593682f902cd78b4358f5a123c9305458d115833c8302cd79932bf3ce1348b307c8358c2583cb2012cc79b12bf3ce22583ce01fdc6558c4e33cd062be3c81f2148c2101fe912bc3da1148d01fcf2864ef2b13f3dc2062bf3cc32148b20574ef28414c3ce1206558c3f433ce2%N);
  (10%nat, 0x102be7cb629a3dc2c1f13fb2029d63e8322813fa207bc729d3d9284293fa120437bd529e3ed48d20529b3db2a212a3f813017cc329c3ef2b3f83017ce29d63cb2c48c230167bd32ab3e8248c20127bf134ef2b48d15037c852ac3dc348a502ac122d7ab2458948f3037cb2ad3df1148c302cd7ad2ae3df14d3d8307cc32ae3cf64c3d92012ae2d7ac2af33dc24c3dc02ac37ce22ac3df4a3dc07b932aa3e924a13d92101ffa12ab3eb4a113da02bd7bb658c49163cb2062ae3dd324a13d82%N);
  (10%nat, 0x102d2af3b91f2148c210289c12b4fb1148d02e87ba62bc3ba2b148c2062e4ed32148b207ab72bf3af284148b120437ac52c83cb48d201ffc52bd3b92a21248a302c917bb32be3cd348c022c817af2ae2e3af2c4990167a932ab3eb248c2012ca127ae12ab3ce2b49b02cb37af5589348f02ce127b82aa43de248f3037ae42a83ec1148c302889329d3ed312b3fa307bb34ed2e2a3fb2012d87b9129d3ed322a3fe02ce37ba529e3ed283fe029c73db1f22813fb210288b129a3fc28113fc%N);
  (10%nat, 0x1012fd2e78f734d83c249902fd2c379b2458848f01486fe3258a248d2102fb117af1358c48f02fb1638788658c48c2017af62bf3be3248c202a2a6ff43588448c1204379b3258c48d207ad54ef2a213fa2930417a91358c3fb2b017a92cd33a92c3fb22b01679b2cd33be248c201279d12cd3ac2b3fc12d0379e52ce3ba33f92d02f81279f2cc43ab2a48f3037a92ca53bd1148c30289d2e2b93a92b1348b302c78d32d83bb248c2012fa7a82f2bc39e2b2248f02f837ae2c863bd48f%N);
  (10%nat, 0x102ed2bb69a358e148e30695f6b8358c48e2012ec697969a2158e249902ec5f36ff3258c48f012af69d4358c248d2102ea117cc5158f48f02ea1587c6ab658c48c2017ce335893248c205d6e6aa43588448c1204378a3258c48d207cf54ef2a2148b1304e17981358c48c301798334ec2c48c2301678a33589248c201278c134ef2b48d150378d544fd348a5039a1278e244dd3b48f30379855881148c302fe7af64db3c148e302e799364f8648e2%N);
  (10%nat, 0x103de124f4fc42ab58f48f3035bc52ac58d1148c304a94f9282ab58e1348b302c5b92a8358c248c2013e84f4f92b29f58f2248f03de35bf62ad58c48f072ae4ff1f2148c2101f982be158f1148d03ce5cd2b964ef2b148c202ae658c32148b205ca2ad74ef284148b120435ca2ae558c48d207fd2b954ef2a21248a303af15cd2ba358c348c023ae15cd2ae64ef2c4990166ee3358c248c2013b8126fb134ef2b49b03b936fc5589348f03bc127969b2458948f3036fb458d1148c3%N);
  (10%nat, 0x10126d9134ef2b48d150358f2ca5589348a50488122d6bd2458948f30358e2ce58d1148c303ec4c4f92cd58e148e302e59b2ca34fe648e2013eb2e2d4f932c958f249903eb2c359a2cd258c48f01484fc2ce358c248d2103e9115ac2cf158f48f03e916386cd658c48c2015ae2e2ae58c3248c202a2a6cc43588448c120436e83258c48d2039a6fa54ef2a2148c3039a416ee1358c48f0239d15bf32ab4fa2c4990165b932ab58f248c20139f125bc2ad14fa2b49b03a835ca2a85589348f%N);
  (10%nat, 0x10249c14fb2bf64fd2c4990164ed2cd358f248c20149e124f82cf14fa2b49b049f36c95589348f04aa124f842cd58d248f3034f82cf458d1148c301f9b2db358b312b3fa306cd34ed2e2a3fb2014ac4ed2dd158b322a3fe04aa34fb2d8558c283fe072d84ff1f22813fb2101f982e8158f28113fc049a5892db64ef2c1f13fb2062d858c322813fa204fe2cf74ef284293fa120434fe2d8558c48d202db54ef2a212a3f813015892dc358c2b3f830158962d84ef2c48c230165892cd358c248c2%N);
  (10%nat, 0x106bf54ef2a213bf5c30416bb1358c3c85e016ad334fa2c3c825e016ad334c85e248c20126aa514fa2b3c9168036b8558933be6804cc126aa434fc2a48f3036aa5458d1148c306bf4c834fa2b1348b306bc34cb58248c2014ce2ef4ca14fa2b2248f04cc36ad6558c48f04be64ff1f2148c2106bc4cd158f1148d04bc6bb2864ef2b148c204bd658c32148b206b8574ef284148b120436b86558c48d2028d92854ef2a21248a3049d16bb29358c348c%N);
  (10%nat, 0x1038a4de74cb3b28448c1204df54bd434f48d202fe4ea54ef2a2148b1302ff4eb34be15c48c3064df4bf13e2c48c2304dc34bf164d248c20134c8123b2b48d1504d954be34f348a50299a244bc122d3b48f304dd4c83591148c304da2ec4dc4e93c148e302f84d934bf4e648e2014d92ec34d84cc2d3c249904d92f84dc24bb35d48f012eb4dd34da49248d2104cf112ea4de158f48f04cf166bb64cd4e48c2012ec4ce658c3248c206bf434ba2a4a448c12046b8324bb6848d2%N);
  (10%nat, 0x106fb4c864ce382b148c2062e4ed32148b204bc74dc2a284148b1204bd54ce433e48d206dc4c854ef2a21248a306dd4c934cf14b348c026bd2e4bd4de12d2c49904dc34db163c248c2016be4de14dc122a2b49b0299f54cf33e348f06ca44dc4db123e248f304de44d93481148c304c92fd4ea358b3148e306ec34d82c2e48e2014c82fd4ec14dc3e3249904c838c4df54cc34c48f012fc74df4ff1f248d2104be112fb4ef158f48f04be13884ea64bd492c48c2012fd64df58c3248c2%N);
  (10%nat, 0x10324d913f1148d21029ce134d9114848f029cd64d81638448c204bd64d813c3248c20434da2a2a448c120324df432d48d2054dc2a2a213fa2930134dc413a3fb2b034ba4ec152c3fb22b034ba4ec162b248c204bc14ed1222b3fc12d04af54e832d33f92d06fd44ba4ec1252a48f3054bb4ea32f1148c3078b4ba2e4db2b1348b304af34e92c6248c20178d4ae2f4ce52b2248f078864bc4dd33b48f04bd2d4e91f2148c21029bd12b4fb1148d%N);
  (10%nat, 0x10129dc2158e115d2a3b8029e8324ff325b3cb04358c25b173b921029da5158f5b113c9029de64f82b5a153bb2033589325b13bf20434fe245c43bb120324f843548d2054ef2a215d3bd130134f91295e3bd30334ec312848c230334ef163248c20134ef412548d150544ed35348a5029cd244dd2912748f3054ee371148c3029cf64d923c148e30364cd2e4648e20129cd734ce22c1f2499029da244cd2c32a48f%N);
  (10%nat, 0x101f9b283cc58e135d3bd303c9358c262c3e92011f9a2b3c858f2264f3c901fa963ce58c43488073cf4ff1f2148c2101f983df158f1148d01f9c3da64ef292148c203cf658c32148b203ce74ef284124891203cf5589313489207fd3da54ef2a21248a307fe3db358a11348c027fd3cf64ef2b149903358b12448820129d8134ef2b11248f029da558912148e029de2458812793ab30458c11148c3029dd358e15e2a3ac30358b15d13bf2%N);
  (10%nat, 0x102a882458938122d3cd303ef58d112e33ea301f9b3ee58e134c3ce303eb34fe622e3ed2011f9a33ea58f222e2d3da01f9e3ee258c2c33ef03ef358c21483db2101f983f8158f1148d02a88658b16383dd202e3cf58c32148b2043588412a2a3dd1203258c6433f82029ae54ef2a21248a3029af1358c3413ff027de33cc4fa2c1f1488033cc58f26163ef2017df3ce14fa2b29123fe07ee3c955893733fd01f9e43cc58f1f124f3bc3053cd58d11633fb3%N);
  (10%nat, 0x1011f9a3f814fa2b4b123dc02a8d558934833db01f9e43ee58d249123da303f8458d113f33d9301f9b3fc358b312b3fa3034ed2e2a2e3dc2011f9a3fe158b322a2e3df01fa93f9558c282c33de073f94ff1f22813fb2101f98489158f28113fc01f9c3fc64ef2c1f163ed2063f958c322813fa203f874ef284292a3df1203f9558c2e433df203fc54ef2a212a3f81303fd358c2b413eb3063f94ef2c3813ea2303ee358c22e163de20134ef2b3a123df1503eb558932f33df5%N);
  (10%nat, 0x10228ba334fa2c5a13cd0334c85e25813ca20128bb514fa2b5c123cb028ca558935933ca02a9b434fc2a5a123c9305458d115833c8302aa932e4db2b1348b3034cb582583cb2012aaa12e4db2b22583ce02a9e6558c4e33cd062d4e91f2148c2102aab12b4fb1148d02a992864ef2b13f3dc2062e4ed32148b20574ef28414c3ce1206558c3f433ce2029fa2854ef2a21248a3029fb29358c33d13dd021f993e864fd2c4913de03ee358f23f163cd2%N);
  (10%nat, 0x1054ef2a212a3f8130134be15c2b3f830334bc13e2c48c230334bc164d248c20134c8123b2b48d150544ba34f348a502abb244bc122d3b48f3054bb3591148c302abd64db3c14d3d830364b94e64c3d92012abb734ba2d3c24c3dc02ac8244af35d4a3dc0324d84924a13d92102abc1358c4a113da02abb64cd4e49163cb20664fe324a13d820434ba2a4a44b3d8120324bb685843c82028c854ef2a214c3cf3028c91358c4d413cc%N);
  (10%nat, 0x1072e4bd2a284148b12052f4ae433e48d202abe52c4da2a21248a302ac832d4b914b348c022abb62e4b912d2c4990334d8163c248c2012abe134d9122a2b49b02ac854cf33e348f02acc244cd123e248f3044d93481148c302acb358b312b3fa3034d82c2e2a3fb2012aca214dc3e322a3fe02ace324cc34c283fe0434fc1f22813fb2102ac85158f28113fc02acc64bd492c1f13fb2033589322813fa20434cb3b284293fa120324bd434f48d2%N);
  (10%nat, 0x102aee64d81638448c2062e4b913c3248c20434da2a2a448c120324df432d48d2054dc2a2a213fa2930134dc413a3fb2b03c34bc152c3fb22b03c34bc162b248c2013c4c81222b3fc12d053d4ba32d33f92d02add3b44bc1252a48f303954bb32f1148c302adf2e284ca2b1348b3033f4b92c6248c2012add2f2b4ba52b2248f02aec2f64af33b48f02d74da1f2148c2102ade12b4fb1148d02add62b4ba382b148c2062e4ed32148b2%N);
  (10%nat, 0x10434b9175a248d2102afb514ba116a48f02aff64ae154b2b48c20334b915e3248c20434b84592448c120324f843548d2054ba4c2a2148b130134ba4e12948c30334ec312848c230334ef163248c20134ef412548d150544ed35348a502aee244dd2912748f3054ee371148c302af864d923c148e30364cd2e4648e2012aee734ce22c1f249902afb244cd2c32a48f0324d913f1148d2102aef134d9114848f%N);
  (10%nat, 0x1011f9a2b4e94c85e22648901fa964ef58c43488074f84ff1f2148c2101f98588158f1148d01f9c4fb64ef292148c204f8658c32148b204ef74ef284124891204f85589313489207fd4fb54ef2a21248a307fe4fc358a11348c027fd4f864ef2b149903358b1244882012af9134ef2b11248f02afb558912148e02aff244cc4b1248d30458c11148c302afe34bd2a4d148e3034b9168148e2012afd214bd2a4d1149902b89324af5f3248f%N);
  (10%nat, 0x101f9b58f4ae6f1348b3058c34fe622e3ed2011f9a358b4af6f222e3f801f9e58f258c2c33ef0598358c21483db2101f98599158f1148d02ba9658b16383dd202e4f858c32148b2043588412a2a3dd1203258c6433f8202acf54ef2a21248a302ad81358c3413ff027de34ed4fa2c1f1488034ed58f26163ef2017df4ef14fa2b29123fe07ee4ea55893733fd01f9e44ed4c95d1f123fc3054ee58d11633fb301f9b284ed4bf5e1348b304ea358c262c3e92%N);
  (10%nat, 0x101f9e458f2cb3cb49123da30599458d113f33d9301f9b59d32c93cc12b3fa3032ab3e82a2e3dc2011f9a59f12c93cc22a2e3df01fa959a558c282c33de0759a2bd3d922813fb2101f985aa158f28113fc01f9c59d62ad3de1f163ed20659a58c322813fa2059972ad3da4292a3df12059a558c2e433df2059d54ef2a212a3f813059e358c2b413eb30659a4ef2c3813ea23058f358c22e163de20134ef2b3a123df15058c558932f33df502ba9244aa6e38123eb3059858d112e33ea3%N);
  (10%nat, 0x1016f9514fa2b5c123cb0788558935933ca02bbc432ba3dc5a123c9305458d115833c8302bca32b83dd1328f2fb30328948a2583cb2012bcb12b83dd22585e2ff02bbf6558c4e33cd064ff1f2128e2fd2102bcc158f1128d2ff02bba2864ef2b13f3dc20658c32128f2fb20574ef28414c3ce1206558c3f433ce202b9b2854ef2a21248a302b9c29358c33d13dd021f9958964fd2c4913de058f358f23f163cd2011f9a59914fa2b4b123dc02bae558934833db%N);
  (10%nat, 0x101fd13f82c1fb638a23031fd163ff21ff38c20131fe123ed2b48d15051fc3489328a2ff502bdc241fa122d3ed48f301fe348b1128838b302bde29f3ee14d5b38c3031fd48864c5f3892012bdc28a2d3ee24c5b338d02be921f9348f4a5f38c032983fb24a15a38e2102bdd158f4a115939802bdc628b48849163cb20658c324a15b38c20431f82a3fc44b3d8120321f949a5843c8206fe54ef2a214c3cf306ff1358c4d413cc026f8334fa2c5a13cd0331fe49825813ca2%N);
  (10%nat, 0x102bdf54ef2a2122982f9302be9328d13fd32992fa022bdc29c13df2c1fe2e2fb03299163ee21fc38f2012bdf129a123dc2b1ff39b02be9528d33f8348f02bed299123f821fd438d30428f33fa111fb398302bec358b312b6c39d30328e3de2e2a3fb2012bed129a3f8322a6c3a902bef528a33fe287b39a04ff1f22816b73982102bee158f28116a3a902bed61fb3fb2c1f16f39b2058c322816c638f2072893ed284297939812051fb434891fc3982054ef2a212a6d39a13031fc148e2b6e3993%N);
  (10%nat, 0x10432982a2a3c9448c1203229d433df48d20529a3dc2a213fa29301329a413ec3fb2b02aa13ce2c2a832cf22b02aa163dd229e32ea2012ab123cb2b2a92da12d0529e33df32ac2cc2d02bfe2aa123ce2a29f42eb302a833e91129d52e9302c882e4db2b132a82ea30329f2c3cf22ac2df2012bfe2f28c3ce2b222ab2eb02c8d29b33ed29e62ea02d4e91f2129d2ee2102bff12b4fb1148d02bfe628c3ea2b129a2f92062e4ed32148b20729a3dc284129c2ee120528c433f829e2ee2%N);
  (10%nat, 0x102ca867c1587c2f848c20337f14983248c20437e5d6e2ec448c120322ae433ce48d2051f83fe2a2148b130131f84e13db48c30332ad13bd2c48c230332ad163cc248c20132b9123ba2b48d150542ab33ce348a502c8f242ad123ac3b48f3052ac33d81148c302c99628f3cb3c148e303628b2e3cd648e2012c8f7328c2e3ac3c249902c9c2428b2c33dc48f03228f1483c8248d2102c981328f113fa48f02c8f628e16383cd48c20628e13ee3229e2ed2%N);
  (10%nat, 0x1076994ff1f2148c2101f986a9158f1148d01f9c69c62bf3af2b148c20699658c32148b2069872cd3a9284148b12069952bf433bd48d207fd69c54ef2a21248a307fe69d32c813ca348c027fd69962c913ac2c4990332c9163bb248c2012c9a132ca123a92b49b02c9c52c833bd348f02ca8242be12792dd48f3042ca33bf1148c302c9f31fb2bb2de148e3037f695f2fa48e2012c9e211fb69792de249902caa327d5f33cb48f0437f12af2eb248d2102c9c511f81149c48f%N);
  (10%nat, 0x1011f9a36ac2d92e2d388249901f9e6b822ca2c33a948f06b932cc14838d248d2101f986ba12cd113bf48f02cca62c9163839a48c202e6992cf13bb3248c20432cb2a2a38e448c120322d8433ac48d202bf852cd3a92a2148c302bf9132cd413b948f027de368e2dd139b2c4990368e2dd163aa248c2017df69812de123982b49b07ee68b52d933ac348f01f9e468e2dd124f2ee48f30568f2db33ae1148c301f9b2868e39e2ef1348b3068b32da2c39c248c2011f9a2b68a2df4f2ef2248f01fa966982ce33ba48f%N);
  (10%nat, 0x101f9b6be358b312b3fa3032fc2f82e2a3fb2011f9a6c8138838a322a3fe01fa96bb52f83398283fe076bb4ff1f22813fb2101f986cb158f28113fc01f9c6be62e938d2c1f13fb2066bb58c322813fa206ba72ef2ff284293fa1206bb52e94339b48d206be54ef2a212a3f81306bf32ea13a82b3f83066bb2eb138a2c48c2306b832eb16399248c20132ec122ff2b48d1506ad52ea339b348a502cca242e8122d2ff48f306b92ec339d1148c301f9b6b82d84c388148e306ad32cc2e39a648e2%N);
  (10%nat, 0x102cdd43398122e82a48f305438e32fb1148c302dc2b8e34fa2b1348b30338d2bd58248c2012db2b9813992e82b2248f02ce86538932ff48f02b8c64ff1f2148c2102d92b9b158f1148d02cdb2862fa2fc2b148c202b8b658c32148b20573882ee284148b120652fa4338a48d202cbc2854ef2a21248a302cbd2932fb138f348c021f996aa638a12f92c49906b832ff16388248c2011f9a6ba1388122ee2b49b02ccf52fb338a348f01f9e46b82ff1238a248f306ba42fd338c1148c3%N);
  (10%nat, 0x10134c8123b2b48d1502b9f54be34f348a502cfd244bc122d3b48f302bab4c83591148c302dc2baa38b2dd3c148e302b9f32ff2bf4e648e2012db32b9e38c2bf2d3c249902df2baa22fd2bd35d48f02bab32ff12d949248d2102d92bac13881138c48f02cfd62fc162c94e48c202b9c638a13883248c20432fe2bb2a4a448c1203238b42ab6848d2053882ee2a213bf5c3013388412fe3c85e03339812e82c3c825e03339812ae5e248c2051399122dd2b3c91680538c32f933be68%N);
  (10%nat, 0x1022da2e2b8b4de12d2c49902baa34db163c248c2012db2bac14dc122a2b49b02d8a54cf33e348f02df42baa4db123e248f302bac44d93481148c302dc2bb832e93a93148e3032dd2fa2c2e48e2012db2bba12e92fa3e3249902ea2bad52db2f834c48f072bad2e8139d1f248d2102d92bbd12de113ae48f02dd2bb862da12e9492c48c2062bad2e813aa3248c202bac72dc2ee3b28448c1202bad54bd434f48d202bb852de3982a2148b1302bb932de2df15c48c3062bad4bf13e2c48c2302baa34bf164d248c2%N);
  (10%nat, 0x1054dc2a2a213fa2930134dc413a3fb2b032b884ec152c3fb22b032b884ec162b248c202b8a14ed1222b3fc12d02afd54e832d33f92d039a42b884ec1252a48f3052b894ea32f1148c303a82b882e4db2b1348b302afd34e92c6248c2013aa2afc2f4ce52b2248f039d62b8a4dd33b48f02b8b2d4e91f2148c2102da812b4fb1148d03982b8e64ce382b148c2062e4ed32148b202b8a74dc2a284148b1202b8b54ce433e48d202f92b8e54ef2a21248a302fa2b8f34cf14b348c%N);
  (10%nat, 0x10434fe245c43bb120324f843548d2054ef2a215d3bd130134f91295e3bd30334ec312848c230334ef163248c20134ef412548d150544ed35348a502db8244dd2912748f3054ee371148c302dba64d923c148e30364cd2e4648e2012db8734ce22c1f249902dbd244cd2c32a48f0324d913f1148d2102db9134d9114848f02db864d81638448c202b8b64d813c3248c20434da2a2a448c120324df432d48d2%N);
  (10%nat, 0x104b92aa864ef292148c202a9d658c32148b202a9c74ef284124891202a9d55893134892049a2aa854ef2a21248a3049b2aa9358a11348c0249a2a9d64ef2b149903358b1244882012dbb134ef2b11248f02dbd558912148e02dc92458812793ab30458c11148c302dc8358e15e2a3ac30358b15d13bf2012dbf2158e115d2a3b802dcb324ff325b3cb04358c25b173b92102dbd5158f5b113c902dc964f82b5a153bb2033589325b13bf2%N);
  (10%nat, 0x102abd358c21483db2104ad2abe158f1148d02deb658b16383dd202e2a9d58c32148b2043588412a2a3dd1203258c6433f8202d9954ef2a21248a302d9a1358c3413ff023fb32a9a4fa2c1f1488032a9a58f26163ef2013fc2a9c14fa2b29123fe048b2a8f55893733fd04bb42a9a58f1f124f3bc3052a9b58d11633fb304b8282a9a58e135d3bd302a8f358c262c3e92014af2b2a8e58f2264f3c904be62a9c58c43488072a9d4ff1f2148c2104ad2aad158f1148d%N);
  (10%nat, 0x1013a89322a2e3df03a98282c33de01f22813fb2103a8e28113fc039fa2c1f163ed20322813fa20284292a3df1202e433df202a212a3f81302b413eb302c3813ea23022e163de202b3a123df15032f33df5039fb38122d3cd3058d112e33ea304b82abc58e134c3ce302ab934fe622e3ed2014af32ab858f222e2d3da04bb2abc258c2c33ef%N);
  (10%nat, 0x103a8a2b1348b30582583cb2013a892b22583ce03aa94e33cd01f2148c2103a9f1148d03a8b2b13f3dc2032148b2028414c3ce1203f433ce2039eb2a21248a303a8833d13dd0239e92c4913de023f163cd20139ea2b4b123dc039ff34833db03a8a249123da30113f33d9303a8a312b3fa302e2a2e3dc2%N);
  (10%nat, 0x1039e9122d3b48f303591148c303a8a3c14d3d8304e64c3d920139eb2d3c24c3dc039e935d4a3dc04924a13d92103ab84a113da039fa4e49163cb20324a13d8202a4a44b3d8120685843c82038a82a214c3cf3038bd4d413cc02389e2c5a13cd05e25813ca201389f2b5c123cb038bc35933ca03a8a2a5a123c930115833c83%N);
  (10%nat, 0x10139ff122a2b49b03a8833e348f03a8b123e248f303481148c303abd312b3fa302c2e2a3fb2013a8d3e322a3fe03a8b34c283fe01f22813fb2103ac928113fc039fb492c1f13fb20322813fa203b284293fa120434f48d202a212a3f813015c2b3f83013e2c48c230164d248c20123b2b48d15034f348a5%N);
  (10%nat, 0x101393fb22b0162b248c201222b3fc12d032d33f92d03aad1252a48f3032f1148c303abd2b1348b302c6248c2013aaf52b2248f03aad33b48f01f2148c2103ada1148d03a9d382b148c2032148b202a284148b120433e48d203a9e2a21248a3039fe14b348c0239fd12d2c4990163c248c2%N);
  (10%nat, 0x105b42148b1304e14648c3013648c230163248c2012548d15035348a503acf12748f30371148c303abb2e1f148e302e4648e2013aba2e1f249903aba2c31f348f012d29248d2103ab8112c2b48f03ab81662e48c2013c3248c202a2a448c120432a348d20282c213fa29304142e3fb2b%N);
  (10%nat, 0x10412489120313489203aec21248a303aec11348c023aeb1348e01244882013aec11248f03aed12148e03af91248d3011148c303aaa68148e30168148e2013aa9681149903aa95f21248f01681248d2103a9f115f348f03a9f1586648c2015e3248c205d2448c120432348d2%N);
  (10%nat, 0x103b9e1663f82032148b20412a3f812036433f8203aca212283f9303acc34143fb023aca1f133fd026163ef2013aca29123fe03acb3733fd03b8b1f123fc3011633fb303b8c1363fd30262c3e92013b8b22648903b8c34348802153ff2103b8d11448903b8b2134892032148b2%N);
  (10%nat, 0x1022812d3dd2103baf28112c3df03bb81f1663df20322813fa204292a3df12032e433df20212a283df1302b4143df3038133df23022e163de203a123df15032f33df503b9c38123eb30112e33ea303b9d132e3ec30622e3ed2013b9c222e3f803b9d32c33ef0212d3ee2103b9e112c3f8%N);
  (10%nat, 0x1013bbe22583ce03bbf34e33cd0214f3cc2103bc8114e3ce03bc813f63ce2032148b20414c3ce12033f433ce203b9f2124a3cf303ba933d143d9023b9f49133db023f163cd2013b9f4b123dc03ba834833db03bad49123da30113f33d9303bae12b2e3db302a2e5f38c2013bad22a2e3df03bae3282c33de%N);
  (10%nat, 0x103bd814d2e3b93064c2e3ba2013bcf24c2e3bd03bd834a2c33bc024a12d3bb2103bd94a112c3bd03bda491663bd20324a13d82044b2a3bd120358433bd203c8214c283be303ca4d4143c8023c85a133ca0258163bc2013c85c123cb03c935933ca03bbe5a123c930115833c8303bbf13583ca302582c3ae2%N);
  (10%nat, 0x103be87c1239f30117a339e303be912b693a8302e2a693a92013be822a693ac03be93285f33ab02281683aa2103bea28115f3ac03beb1f15863ac20322813fa204295d3ac120369433ac20212a5b3ac1302b4e143ac306b133ac230269163ab206d123ac15036a33ac503bcf6b123b830116933af3%N);
  (10%nat, 0x101ff122f912d031fc32f92d03bf91fd1238e30111fb338d303bfa131fb38f3021fb2c2fb2013bf9221fb39b03bfa31f9339a0211fa3992103bfb111f939b03bfb17a639b2032148b20417f39b12037a4339b203bda2127d39c303bdc3781439e023bda7c133a8027a1639a2013bda7e123a903bdb37b33a8%N);
  (10%nat, 0x1028e132f9230228c162f820298122f9150328d32f9503c8a28e122fd301128c32fc303c8b11f82e2fe3067f2e2ff2013c8a27f2e38a03c8b37d2c3389027d12d3882103c8c7d112c38a03c8d7c16638a20327d139d2047e2a38a12031fb4338a20217f282f929301f84142f92b01fd132f922b021fb163892%N);
  (10%nat, 0x103c8d2122a82e9303c8f329b142eb023c8d29f132ed0229d162df2013c8d2a9122ee03c8e329e32ed03c9b29f122ec301129d32eb303c9c15e692ed302fa5d692ee2013c9b25d692f903c9c35b5f32f8025b1682ef2103c9d5b115f2f903c9e5a15862f920325b13bf2045c5d2f9120328c432f920215d5b2f91305e4e142f93%N);
  (10%nat, 0x1042a92a2cf12032ae432cf203beb212aa282d8303bed2ab4142da023beb2b8132dc022ae162ce2013beb2ba122dd03bec32af32dc03cac2b8122db30112ae32da303cad132ae2dc3022ae2c2c82013cac222ae2e803cad32ac32df0212ad2de2103cae112ac2e803cae129d62e82032148b20412aa2e8120329d432e82%N);
  (10%nat, 0x103cd91f12ae62be20322813fa204292bb2be12032bf432be20212a2b92be1302b2ac142be302c9132be23022bf162bd202cb122be15032c832be503cbd2c9122ca30112bf32c9303cbe12ab2e2cb3062aa2e2cc2013cbd22aa2e2cf03cbe32a82c32ce022a812d2cd2103cbf2a8112c2cf03cc829f1662cf20322a812ea2%N);
  (10%nat, 0x10212e82ab2103ce9112df2ad03ce912d862ad2032148b20412dd2ad12032d8432ad203cc82122db2ae303cca32ce142b8023cc82da132ba022d8162ac2013cc82dc122bb03cc932d932ba03cce2da122b930112d832b8303ccf12b2bf2ba303b9d2a2bf2bb2013cce22a2bf2be03ccf3282bd32bd022812be2bc2103cd828112bd2be%N);
  (10%nat, 0x1012ae3bc922dd2bb02ac33bc932db2bb03bcb22db12b82102ac3bcd2db112b902aa3bd82da162aa20322db12af203bcc42dc2af1203bcc32e9429f203bce212dd795c303bd82de416c5e02eb136825e03bcd22e912a9202ed1268168032ea3686803cdf2eb122a830112e9329f303ce8132e92a9303bbf22e92aa2013cdf222e92ad03ce832df32ac%N);
  (10%nat, 0x102d93bb812bc2d9303b9b2e2bb2da2012d83bb822bb2dd02ce33bb832b92dd03bba22b912da2102ce3bbc2b9112db02be63bbf2b812da20322b912d9203bbb42ba2d9120433bbb348d203bbd212bb2cf130143bbf2bc2cf30133bbf48c230163bbc248c20123bbe48d15033bbe348a502ac123bc848f3033bc81148c302af3bc912de2af303bbd62dd2b82%N);
  (10%nat, 0x102f8123b9e48f3033b9e1148c302fb3b9f1348b302c3b8c248c2012fa3b9f2248f02f833b9f348f03ba92148c2102f83bab1148d02e863bad148c2032148b203baa4148b120433baa348d202ce3bac21248a302c9143bae348c022c8133bae4990163bab248c2012ca123bad49b02cb33bad348f02ce123baf48f3033baf1148c3%N);
  (10%nat, 0x10123b8b48d15033b8b348a5039a123b8d48f3033b8d1148c302fe2e3b8e148e302e3b8a648e2012fd2e3b8e249902fd2c33b8e348f012d3b98248d2102fb112c3b9a48f02fb1663b9d48c2013bab3248c202a3b99448c120433b99348d20283b9b213fa29304143b9d3fb2b0133b9d3fb22b0163b9a248c20123b9c3fc12d033b9c33f92d%N);
  (10%nat, 0x1023ae133afb4990163af8248c2013b8123afa49b03b933afa348f03bc123afc48f3033afc1148c303bf3afd15e3bf305f3aaf5d3c82013be3afd25d3cb03bc33afd35b3cb03aff25b13c82103bc3b895b113c903ac63b8c5a13c820325b13bf203b8845c3bf120433b88348d203b8a215d3bd130143b8c5e3bd30133b8c48c230163b89248c2%N);
  (10%nat, 0x1039a283ae82148c3039a4143aea48f0239d133aea4990163adf248c20139f123ae949b03a833ae9348f03de123aeb48f3033aeb1148c303e93aec1348b302c3ad9248c2013e83aec2248f03de33aec348f03aee2148c2103de3af81148d03ce63afa148c2032148b203aef4148b120433aef348d203bc3af921248a303af143afb348c%N);
  (10%nat, 0x103acd4293fa120433acd348d203acf212a3f8130143ad92b3f830133ad948c230163ace248c20123ad848d15033ad8348a50488123ada48f3033ada1148c303ec2e3adb148e302e3acf648e2013eb2e3adb249903eb2c33adb348f012d3add248d2103e9112c3adf48f03e91663aea48c2013af83248c202a3ade448c120433ade348d2%N);
  (10%nat, 0x104bc63abf148c2032148b203abc4148b120433abc348d204aa3abe21248a3049d143ac8348c0249c133ac84990163abd248c20149e123abf49b049f33abf348f04aa123ac948f3033ac91148c304ad3aca12b3fa303aad2e2a3fb2014ac3aca22a3fe04aa33aca3283fe03acc22813fb2104aa3ace28113fc049a63ad91f13fb20322813fa2%N);
  (10%nat, 0x10139fb5c248d2104cf1139fa5e48f04cf1639eb6948c2013abd3248c2039f85d448c120439e85d348d202df39ee5f2148c302df4139e96948f022ea133aaf4990139eb5e248c2012ec123aae49b02ed33aae348f04cc123ab848f3033ab81148c304cf3ab91348b3039fa58248c2014ce3ab92248f04cc33ab9348f03abb2148c2104cc3abd1148d%N);
  (10%nat, 0x1014c83aaf49249904c83aad349348f013aae4b248d2104be113aad4d48f04be13a9e65848c2013adf3248c203aab4c448c120434c348d203aa94e2148b1303a9c145848c30135848c230164d248c20124f48d15034f348a503dcc125948f303591148c304da39fc5a148e3039fc4e648e2014d939fc5a249904d939fa35a348f%N);
  (10%nat, 0x103e9b381348b302c6248c2013e9a382248f03e98338348f03a2148c2103e983c1148d03e8863e148c2032148b203b4148b120433b348d203dee3d21248a303de9143f348c023de8133f4990163c248c2013dea123e49b03deb33e348f03dee124848f303481148c304c93aaf49148e303aaf2c2e48e2%N);
  (10%nat, 0x103eba12748f30371148c303e9e2e1f148e302e4648e2013e9d2e1f249903e9d2c31f348f012d29248d2103e9b112c2b48f03e9b1662e48c2013c3248c202a2a448c120432a348d20282c213fa29304142e3fb2b0132e3fb22b0162b248c20122d3fc12d032d33f92d03e98122f48f3032f1148c3%N);
  (10%nat, 0x1013ecf11248f03ed812148e03edc1248d3011148c3048e3bcf148e3013bcf148e20148d3bcf11499048d3bce21248f013bcf1248d21048b113bce348f048b13bbf6648c2013bcd3248c203bcc2448c120432348d203bca42148b1303bbd14648c3013648c230163248c2012548d15035348a5%N);
  (10%nat, 0x1023ead1f133fd026163ef2013ead29123fe03eae3733fd03eee1f123fc3011633fb303eef1363fd30262c3e92013eee22648903eef34348802153ff2103ef811448903eee2134892032148b20412489120313489203ecf21248a303ecf11348c023ece1348e01244882%N);
  (10%nat, 0x10212a283df1302b4143df3038133df23022e163de203a123df15032f33df503eff38123eb30112e33ea303f88132e3ec30622e3ed2013eff222e3f803f8832c33ef0212d3ee2103f89112c3f803f891663f82032148b20412a3f812036433f8203ead212283f9303eaf34143fb%N);
  (10%nat, 0x10414c3ce12033f433ce203f8a2124a3cf303f8c33d143d9023f8a49133db023f163cd2013f8a4b123dc03f8b34833db03f9849123da30113f33d9303f9912b2e3db303ddf2a2e3dc2013f9822a2e3df03f993282c33de022812d3dd2103f9a28112c3df03f9b1f1663df20322813fa204292a3df12032e433df2%N);
  (10%nat, 0x102aa3e9a49163cb20324a13d8203e8e44b3d81203e8e35843c8203e98214c792ed303e9a4d416c2ef05a136822ef03e8f25813ca205c126812f903593682f903fa95a123c930115833c8303faa13583ca303e892583cb2013fa922583ce03faa34e33cd0214f3cc2103fab114e3ce03fab13f63ce2032148b2%N);
  (10%nat, 0x103dfc22813fb2102ce3dfe28113fc02be63e891f13fb20322813fa203dfd4293fa120433dfd348d203dff212a3f8130143e892b3f830133e8948c230163dfe248c20123e8848d15033e88348a502ac123e8a48f3033e8a1148c302af3e8b14d3d8303dff64c3d92012ae3e8b24c3dc02ac33e8b34a3dc03e8d24a13d92102ac3e8f4a113da%N);
  (10%nat, 0x1012fa3de92248f02f833de9348f03deb2148c2102f83ded1148d02e863def148c2032148b203dec4148b120433dec348d202ce3dee21248a302c9143df8348c022c8133df84990163ded248c2012ca123def49b02cb33def348f02ce123df948f3033df91148c302d93dfa12b3fa303ddd2e2a3fb2012d83dfa22a3fe02ce33dfa3283fe%N);
  (10%nat, 0x102fe2e3dd8148e302e3dcc648e2012fd2e3dd8249902fd2c33dd8348f012d3dda248d2102fb112c3ddc48f02fb1663ddf48c2013ded3248c202a3ddb448c120433ddb348d20283ddd213fa29304143ddf3fb2b0133ddf3fb22b0163ddc248c20123dde3fc12d033dde33f92d02f8123de848f3033de81148c302fb3de91348b302c3dce248c2%N);
  (10%nat, 0x103bc123dbe48f3033dbe1148c302ed693dbf148e30695f3cf948e2012ec693dbf249902ec5f33dbf348f01683dc9248d2102ea115f3dcb48f02ea15863dce48c2013e8f3248c205d3dca448c120433dca348d205b3dcc2148b1304e143dce48c30133dce48c230163dcb248c20123dcd48d15033dcd348a5039a123dcf48f3033dcf1148c3%N);
  (10%nat, 0x10139f123dab49b03a833dab348f03de123dad48f3033dad1148c303e93dae1348b302c3d9b248c2013e83dae2248f03de33dae348f03db82148c2103de3dba1148d03ce63dbc148c2032148b203db94148b120433db9348d203bc3dbb21248a303af143dbd348c023ae133dbd4990163dba248c2013b8123dbc49b03b933dbc348f%N);
  (10%nat, 0x10133d9b48c230163d98248c20123d9a48d15033d9a348a50488123d9c48f3033d9c1148c303ec2e3d9d148e302e3d99648e2013eb2e3d9d249903eb2c33d9d348f012d3d9f248d2103e9112c3da948f03e91663dac48c2013dba3248c202a3da8448c120433da8348d2039a283daa2148c3039a4143dac48f0239d133dac4990163da9248c2%N);
  (10%nat, 0x104aa3d8821248a3049d143d8a348c0249c133d8a4990163cff248c20149e123d8949b049f33d89348f04aa123d8b48f3033d8b1148c304ad3d8c12b3fa303cef2e2a3fb2014ac3d8c22a3fe04aa33d8c3283fe03d8e22813fb2104aa3d9828113fc049a63d9b1f13fb20322813fa203d8f4293fa120433d8f348d203d99212a3f8130143d9b2b3f83%N);
  (10%nat, 0x103cba5d448c12043caa5d348d203cb85f213bf5c30413cab693c85e0133cf93c825e013cad5e248c20123cf83c9168033cf833be6804cc123cfa48f3033cfa1148c304cf3cfb1348b303cbc58248c2014ce3cfb2248f04cc33cfb348f03cfd2148c2104cc3cff1148d04bc63d89148c2032148b203cfe4148b120433cfe348d2%N);
  (10%nat, 0x104be13ce865848c2013da93248c203ced4c448c120434c348d203ceb4e2148b1303cde145848c30135848c230164d248c20124f48d15034f348a50488e125948f303591148c304da3cbe5a148e303cbe4e648e2014d93cbe5a249904d93cbc35a348f013cbd5c248d2104cf113cbc5e48f04cf163cad6948c2013cff3248c2%N);
  (10%nat, 0x103a2148c21048da3c1148d048ca63e148c2032148b203b4148b120433b348d2048b83d21248a3048ab143f348c0248aa133f4990163c248c20148ac123e49b048ad33e348f048b8124848f303481148c304c93cf949148e303cf92c2e48e2014c83cf949249904c83cef349348f013cf84b248d2104be113cef4d48f%N);
  (10%nat, 0x10148df2e1f2499048df2c31f348f012d29248d21048dd112c2b48f048dd1662e48c2013c3248c202a2a448c120432a348d20282c213fa29304142e3fb2b0132e3fb22b0162b248c20122d3fc12d032d33f92d048da122f48f3032f1148c3048dd381348b302c6248c20148dc382248f048da338348f%N);
  (10%nat, 0x1049a815e3bf3015d13bf201499f115d3cb0499e2125b3cb0125b13c8210499e35b113c90498e665a13c820325b13bf20245c3bf120432348d204215d3bd1301465e3bd3013648c230163248c2012548d15035348a5048fc12748f30371148c3048e82e1f148e302e4648e2%N);
  (10%nat, 0x1049b81f123fc3011633fb3049b91363fd30262c3e920149b8226489049b934348802153ff21049ba114489049b82134892032148b2041248912031348920499921248a30499911348c0249981348e0124488201499911248f0499a12148e0499e1248d3011148c3%N);
  (10%nat, 0x103a123df15032f33df5049c938123eb30112e33ea3049ca132e3ec30622e3ed20149c9222e3f8049ca32c33ef0212d3ee21049cb112c3f8049cb1663f82032148b20412a3f812036433f82048ef212283f93048f934143fb0248ef1f133fd026163ef20148ef29123fe048f83733fd%N);
  (10%nat, 0x10249cc49133db023f163cd20149cc4b123dc049cd34833db049da49123da30113f33d93049db12b2e3db302e2a2e3dc20149da22a2e3df049db3282c33de022812d3dd21049dc28112c3df049dd1f1663df20322813fa204292a3df12032e433df20212a283df1302b4143df3038133df23022e163de2%N);
  (10%nat, 0x103fb95f214c3cf303fb9694d413cc0248895a133ca05e25813ca20148895c123cb0488a35933ca049eb5a123c930115833c83049ec13583ca30582583cb20149eb22583ce049ec34e33cd0214f3cc21049ed114e3ce049ed13f63ce2032148b20414c3ce12033f433ce2049cc2124a3cf3049ce33d143d9%N);
  (10%nat, 0x104c4293fa120434c348d204e212a3f813014582b3f830135848c230164d248c20124f48d15034f348a5049af125948f303591148c3049ba5a14d3d8304e64c3d920149b95a24c3dc049af35a34a3dc05c24a13d921049af5e4a113da049ad6949163cb20324a13d8205d44b3d81205d35843c82%N);
  (10%nat, 0x1049eb63e148c2032148b203b4148b120433b348d2049d93d21248a3049cc143f348c0249cb133f4990163c248c20149cd123e49b049ce33e348f049d9124848f303481148c3049dc4912b3fa302c2e2a3fb20149db4922a3fe049d93493283fe04b22813fb21049d94d28113fc049c96581f13fb20322813fa2%N);
  (10%nat, 0x1012d29248d21049fe112c2b48f049fe1662e48c2013c3248c202a2a448c120432a348d20282c213fa29304142e3fb2b0132e3fb22b0162b248c20122d3fc12d032d33f92d049fb122f48f3032f1148c3049fe381348b302c6248c20149fd382248f049fb338348f03a2148c21049fb3c1148d%N);
  (10%nat, 0x10149ef6811499049ef5f21248f01681248d21049ed115f348f049ed1586648c2015e3248c205d2448c120432348d205b42148b1304e14648c3013648c230163248c2012548d15035348a504a9d12748f30371148c304a892e1f148e302e4648e2014a882e1f249904a882c31f348f%N);
  (10%nat, 0x104ada1363fd30262c3e92014ad922648904ada34348802153ff2104adb11448904ad92134892032148b20412489120313489204aba21248a304aba11348c024ab91348e01244882014aba11248f04abb12148e04abf1248d3011148c3049f868148e30168148e2%N);
  (10%nat, 0x104aea38123eb30112e33ea304aeb132e3ec30622e3ed2014aea222e3f804aeb32c33ef0212d3ee2104aec112c3f804aec1663f82032148b20412a3f812036433f8204a98212283f9304a9a34143fb024a981f133fd026163ef2014a9829123fe04a993733fd04ad91f123fc3011633fb3%N);
  (10%nat, 0x1014aed4b123dc04aee34833db04afb49123da30113f33d9304afc12b2e3db302e992a2e3dc2014afb22a2e3df04afc3282c33de022812d3dd2104afd28112c3df04afe1f1663df20322813fa204292a3df12032e433df20212a283df1302b4143df3038133df23022e163de203a123df15032f33df5%N);
  (10%nat, 0x1023dbf5a133ca02ec925813ca2013dbf5c123cb03dc835933ca04b8c5a123c930115833c8304b8d13583ca302ebb2583cb2014b8c22583ce04b8d34e33cd0214f3cc2104b8e114e3ce04b8e13f63ce2032148b20414c3ce12033f433ce204aed2124a3cf304aef33d143d9024aed49133db023f163cd2%N);
  (10%nat, 0x102eb9212a3f8130142ebb2b3f830132ebb48c230162eb8248c20122eba48d15032eba348a502cdd122ebc48f3032ebc1148c302ce82ebd14d3d8302eb964c3d92012cdf2ebd24c3dc02cdd32ebd34a3dc02ebf24a13d92102cdd2ec94a113da02cdb2ecc49163cb20324a13d8202ec844b3d81202ec835843c8207fc2eca214c3cf307fc2ecc4d413cc%N);
  (10%nat, 0x102e9e4148b120432e9e348d202cff2ea821248a302cfa142eaa348c022cf9132eaa4990162e9f248c2012cfb122ea949b02cfc32ea9348f02cff122eab48f3032eab1148c302d8a2eac12b3fa302e8f2e2a3fb2012d892eac22a3fe02cff32eac3283fe02eae22813fb2102cff2eb828113fc02cef62ebb1f13fb20322813fa202eaf4293fa120432eaf348d2%N);
  (10%nat, 0x102dac1662e9948c2012e9f3248c202a2e8d448c120432e8d348d20282e8f213fa29304142e993fb2b0132e993fb22b0162e8e248c20122e983fc12d032e9833f92d02da9122e9a48f3032e9a1148c302dac2e9b1348b302c2e88248c2012dab2e9b2248f02da932e9b348f02e9d2148c2102da92e9f1148d02d9962ea9148c2032148b2%N);
  (10%nat, 0x101682dfb248d2102d9b115f2dfd48f02d9b15862e8848c2012ec93248c205d2dfc448c120432dfc348d205b2dfe2148b1304e142e8848c30132e8848c230162dfd248c20122dff48d15032dff348a502dcb122e8948f3032e891148c302daf2e2e8a148e302e2dfe648e2012dae2e2e8a249902dae2c32e8a348f012d2e8c248d2102dac112c2e8e48f%N);
  (10%nat, 0x1012e992de82248f02e8f32de8348f02dea2148c2102e8f2dec1148d02dff62dee148c2032148b202deb4148b120432deb348d202ded2ded21248a302de8142def348c022ddf132def4990162dec248c2012de9122dee49b02dea32dee348f02ded122df848f3032df81148c302d9e692df9148e30692c882fa48e2012d9d692df9249902d9d5f32df9348f%N);
  (10%nat, 0x102e9d2e2dcf148e302e2dcb648e2012e9c2e2dcf249902e9c2c32dcf348f012d2dd9248d2102e9a112c2ddb48f02e9a1662dde48c2012dec3248c202a2dda448c120432dda348d202dcb282ddc2148c302dcb4142dde48f022dce132dde4990162ddb248c2012dd8122ddd49b02dd932ddd348f02e8f122ddf48f3032ddf1148c302e9a2de81348b302c2dcd248c2%N);
  (10%nat, 0x102edb122dbd48f3032dbd1148c302ede2dbe12b3fa302f82bcf2a3fb2012edd2dbe22a3fe02edb32dbe3283fe02dc822813fb2102edb2dca28113fc02ecb62dcd1f13fb20322813fa202dc94293fa120432dc9348d202dcb212a3f8130142dcd2b3f830132dcd48c230162dca248c20122dcc48d15032dcc348a502eb9122dce48f3032dce1148c3%N);
  (10%nat, 0x10122daa3c9168032daa33be6802efd122dac48f3032dac1148c302f882dad1348b302bd2bf9248c2012eff2dad2248f02efd32dad348f02daf2148c2102efd2db91148d02eed62dbb148c2032148b202db84148b120432db8348d202edb2dba21248a302ece142dbc348c022ecd132dbc4990162db9248c2012ecf122dbb49b02ed832dbb348f%N);
  (10%nat, 0x10132bf948c230162bee248c20122bf848d15032bf8348a5038c8122bfa48f3032bfa1148c302f8b2bf2bfb148e302bf2bef648e2012f8a2bf2bfb249902f8a2bd32bfb348f012be2bfd248d2102f88112bd2bff48f02f88162ae2c8a48c2012db93248c202bb2bfe448c12042ab2bfe348d202b92c88213bf5c30412ac2c8a3c85e0132dab3c825e012ae2bff248c2%N);
  (10%nat, 0x1038ea2bde21248a3038dd142be8348c0238dc132be84990162bdd248c20138de122bdf49b038df32bdf348f038ea122be948f3032be91148c302efa2fa2bea148e302fa2bcd2e48e2012ef92fa2bea249902ef92f832bea348f012f92bec248d2102eef112f82bee48f02eef12e962bf948c2012ddb3248c202ee2bed448c120432bed348d202ec2bef2148b1302df142bf948c3%N);
  (10%nat, 0x102a2bcb448c120432bcb348d20282bcd213fa29304142bcf3fb2b0132bcf3fb22b0162bcc248c20122bce3fc12d032bce33f92d0398c122bd848f3032bd81148c30398f2bd91348b302c2bbe248c201398e2bd92248f0398c32bd9348f02bdb2148c210398c2bdd1148d038fc62bdf148c2032148b202bdc4148b120432bdc348d2%N);
  (10%nat, 0x1039c862bbe5a13c820325b13bf202bba45c3bf120432bba348d202bbc215d3bd130142bbe5e3bd30132bbe48c230162bbb248c20122bbd48d15032bbd348a5039ae122bbf48f3032bbf1148c30399a2e2bc8148e302e2bbc648e20139992e2bc82499039992c32bc8348f012d2bca248d210398f112c2bcc48f0398f1662bcf48c2012bdd3248c2%N);
  (10%nat, 0x102ba82148c21039fa2baa1148d039ea62bac148c2032148b202ba94148b120432ba9348d2039d82bab21248a3039cb142bad348c0239ca132bad4990162baa248c20139cc122bac49b039cd32bac348f039d8122bae48f3032bae1148c3039db2baf15e3bf305f2ae95d3c820139da2baf25d3cb039d832baf35b3cb02bb925b13c821039d82bbb5b113c9%N);
  (10%nat, 0x10139ff2e2b8d2499039ff2c32b8d348f012d2b8f248d21039fd112c2b9948f039fd1662b9c48c2012baa3248c202a2b98448c120432b98348d2039ae282b9a2148c3039ae4142b9c48f0239b9132b9c4990162b99248c20139bb122b9b49b039bc32b9b348f039fa122b9d48f3032b9d1148c3039fd2b9e1348b302c2b8b248c20139fc2b9e2248f039fa32b9e348f%N);
  (10%nat, 0x103ac92afc12b3fa302adf2e2a3fb2013ac82afc22a3fe03abe32afc3283fe02afe22813fb2103abe2b8828113fc03aae62b8b1f13fb20322813fa202aff4293fa120432aff348d202b89212a3f8130142b8b2b3f830132b8b48c230162b88248c20122b8a48d15032b8a348a503a9c122b8c48f3032b8c1148c303a882e2b8d148e302e2b89648e2%N);
  (10%nat, 0x103ae8122aea48f3032aea1148c303aeb2aeb1348b302aac58248c2013aea2aeb2248f03ae832aeb348f02aed2148c2103ae82aef1148d03ad862af9148c2032148b202aee4148b120432aee348d203abe2af821248a303ab9142afa348c023ab8132afa4990162aef248c2013aba122af949b03abb32af9348f03abe122afb48f3032afb1148c3%N);
  (10%nat, 0x10124f48d15034f348a504d9a125948f303591148c303aee2aae5a148e302aae4e648e2013aed2aae5a249903aed2aac35a348f012aad5c248d2103aeb112aac5e48f03aeb162a9d6948c2012aef3248c202aaa5d448c12042a9a5d348d2038fb2aa85f2148c3038fb412a9b6948f0238fe132ae9499012a9d5e248c2013988122ae849b0398932ae8348f%N);
  (10%nat, 0x1024dae133f4990163c248c2014db8123e49b04db933e348f04dbc124848f303481148c303add2ae949148e302ae92c2e48e2013adc2ae949249903adc2adf349348f012ae84b248d2103ada112adf4d48f03ada12ad865848c2012b993248c202add4c448c120434c348d202adb4e2148b1302ace145848c30135848c230164d248c2%N);
  (10%nat, 0x10282c213fa29304142e3fb2b0132e3fb22b0162b248c20122d3fc12d032d33f92d04dde122f48f3032f1148c304de9381348b302c6248c2014de8382248f04dde338348f03a2148c2104dde3c1148d04dce63e148c2032148b203b4148b120433b348d204dbc3d21248a304daf143f348c%N);
  (10%nat, 0x102bfe2448c120432348d202bfc42148b1302bef14648c3013648c230163248c2012548d15035348a504e8812748f30371148c304dec2e1f148e302e4648e2014deb2e1f249904deb2c31f348f012d29248d2104de9112c2b48f04de91662e48c2013c3248c202a2a448c120432a348d2%N);
  (10%nat, 0x104ebc2134892032148b20412489120313489204e9d21248a304e9d11348c024e9c1348e01244882014e9d11248f04e9e12148e04eaa1248d3011148c303aaa2c89148e3012c89148e2013aa92c891149903aa92c8821248f012c891248d2103a9f112c88348f03a9f12bf96648c2012bff3248c2%N);
  (10%nat, 0x10212d3ee304ecf112c3ee204ecf1663f82032148b110412a3f812036433f8204dfb212283f9304dfd34143fb024dfb1f133fd026163ef2014dfb29123fe04dfc3733fd04ebc1f123fc3011633fb304ebd1363fd30262c3e92014ebc22648904ebd34348802153ff2104ebe114489%N);
  (10%nat, 0x104ecf22a2e3cc2a0284ece3282c33cb2a04ecf22812d3cc2b074ed928112c3cc12904ed91f1663ce2a04ecc322813ea17204ecd4292a3d829034ece32e433df204ecf212a283da28024ed92b4143da53014ed938133ec0124ecf22e163de2014ecf3a123ed04ece32f33df504ecf38123ee04ecf112e33ea30132e3ef0622e3ed110222e3ee204ece32c33ef%N);
  (10%nat, 0x1038d92dff13583cd02938cf2e892582c3b8038cf2dff22583ce038cd2e8834e33cd038cd2e89214f3cf038cd12e8a114e3ce038cc2e8b13f63d8038cd12dfd32148d038ce2dfe414c3d904ece33f433cb5038d82dfe2124a3da038d82e8833d143cd4049133ce1404ecf23f163cb1304b123cf14034ece34833db049123cf3304ed9113f33cf21204ed912b2e3cc2904ed92a2e5f2fc622%N);
  (10%nat, 0x1034ecf6b123bb0124ecf116933ba038c82e9814d2e3bc0138be2e8c64c2e3bc038be2e9824c2e3bd038bc2e9934a2c33bc038bc2e9a24a12d3be038bc12e9b4a112c3bd038bb2e9d491663bf038bc12e8e324a13da038bd2e8f44b2a3c802b4ece358433bf038bf2e8f214c283c902a38bf2e994d4143c8014eea5a133ca012a4ecf258163be014ee85c123cb034ece35933ca034ee85a123cc0374ed9115833cb%N);
  (10%nat, 0x1012e9a7e123a9034ece37b33a8032e9a7c123aa038bb32e9a117a33a9038af2ea912b693ab038ad62dfe2e2a693ab038ad2ea922a693ac038ab2eaa3285f33ab038ab2eab2281683ad038ab12eac28115f3ac038aa2eae1f15863ae038ab12e9f322813fc038ac2ea84295d3af034ece369433ae038ae2ea8212a5b3b80238ae2eaa2b4e143af014ed96b133b90124ecf269163ad014ecf6d123ba034ece36a33b9%N);
  (10%nat, 0x1012dfa1fd1338f038db12dfa21fb1638b012df81ff12398034ece31fc338f032df81fd12399038dd32df8111fb339802c4ebc131fb39a02a38ca2dfb21fb2c2fd02a4ebc221fb39b0284ebd31f9339a0284ebe211fa39c02814ebf111f939b01f4ec817a639d02814eba32148d0294ebb417f39e038b92e9c37a4339d02b4ebb2127d39f02b389e2e9e3781439e012e9c7c133a8038b912e9c27a1639c%N);
  (10%nat, 0x1064ecf215d5b2fd0424ed95e4e142fc014ed928e132fe0124ecf228c162fa014ecf298122ff034ece328d32fe034ecf28e123880124ecf1128c32ff044ecd11f82e3890124ec967f2e389024ecd27f2e38a04ece37d2c338904ecf27d12d38b014ed87d112c38a014ed97c16638c014ecb327d139f014ecc47e2a38d038db2dfa31fb4338c034ecc217f2838e0338d92dfc1f841438d%N);
  (10%nat, 0x104ecd412aa6a298034ece329d432ea04ecf2122a86c28f024ed9329b146c28e014ed929f132ed0124ecf229d162e9014ecf2a9122ee034ece329e32ed034ecf29f122ef0124ecf1129d32ee054ed915e692f806139ad2dab5d692f8074ecf25d692f90284ece35b5f32f80284ecf25b1682fa011f4ed95b115f2f90294ed95a15862fb011f4ecc325b13c901f4ecd45c5d2fc034ece328c432fb%N);
  (10%nat, 0x104ed929f1663e2aa04ecc322a815a12a804ecd42a92a482a904ece32ae435d28b04ecf212aa284a2a804ed92ab4144a2c28a02b81368128a04ecf22ae165d128902ba1269128a034ece32af32dc02b81269328904ed9112ae369328804ed9132ae5e29804ed922ae2c49628a04ecf222ae5e29904ece32ac35d29904ecf212ad5e29a04ed9112ac5e129804ed8129d66829904ecc3212fc128f%N);
  (10%nat, 0x104ecf22812be32bc04ed928112bd312ba04ed91f12ae652bb04ecc322812c912b904ecd4292bb72ba034ece32bf432c804ecf212a2b9282b9024ed92b2ac14282b8014ed92c9132cb0124ecf22bf162bf014ecf2cb122cc034ece32c832cb034ecf2c9122cd0124ecf112bf32cc04ed912ab2e3c2a9014ecb62aa2e3c2a904ecf22aa2e3c2aa04ece32a82c33b2aa04ecf22a812d3c2ab04ed92a8112c3c12a9%N);
  (10%nat, 0x104eca5222e92ad04ec8632df32ac04ec87212e82ae04ec811f112df2ad04ebf2812d862af04ec81332148d04ec94412dd2b804ece32d84322ad04ecb42122db2b904ecb632ce1442ac02da13512ac04ecf22d816212ab02dc12612ac034ece32d932ba02da12632ab04ed9112d83632aa04ed912b2bf32ba034ece2a2bf362ac04ecf22a2bf32bb04ece3282bd322bb%N);
  (10%nat, 0x10384ebb2d12de2ba03914eb92962dd2ba03a4eb92d22dd2bb033b4eaf2e32db2bb03c4eaf2f22db12bb03c4eaf1382db112b903f4eae3a2da162ac04eaf12b322db12b903f4eb82c42dc2ba02a2b4ece32e942a903f4eba2c212dd2b902c2a4eba2e2de412ab014eea2eb132a902a12a4ecf22e912ab014ee82ed122aa034ece32ea32a9034ee82eb122ab0374ed9112e932aa04ecc5132e92ac05294eca722e92ac%N);
  (10%nat, 0x10124ebd32f49a0374eae32f1148f01f4eaa3e12bc2dc0294ea8642e2bb2dc0294ea83e22bb2dd032a4e9e3f32b92dd02b4e9e4822b912dd02b4e9e1492b9112db062e4e9d4b2b812dc04e9e13c322b912db02e4e9f3d42ba2dc0432a34ece348f02e4ea93d212bb2db0142c24ea93f2bc2da0132d14ed94990162a124ecf248e0122e14ecf49b032d34ece348f0122e34ecf49a032e124ecf1148f%N);
  (10%nat, 0x1049b0159eb024ecf2498024ece11148f012b4ebc1348e012a14ebc1248e012a4ebc2248f032284ebd348f03284ebe2148f032814ebf1148d0661f4ec8148e02814eba32148d06294ebb4148e04354eac39348f062b4ebb21248d01462b4e993b348c0134ebc13949901654eac139248e0124ebd12f49b03534ece348f%N);
  (1%nat, 0x100%N)
].

Definition init_and_run_dp : T8192 (T4096 LEnt) * T4096 DEntry :=
  let '(t0, t1, idr) := build_tabs6 in
  let dv0 := v16_const mnone in let dv1 := v16_const dv0 in
  let lent0 := mkLEnt false 0 0 0 0 in
  let le_emp := t4_const lent0 in
  let ltab_half := t4_const le_emp in
  let ltab0 := mkT8 ltab_half ltab_half in
  let n0 := mkNib3 N00 N00 N00 in let n1 := mkNib3 N00 N00 N01 in let n2 := mkNib3 N00 N00 N02 in
  let l0 := t4_set le_emp n0 (mkLEnt true 0 0 1 0) in
  let l1 := t4_set le_emp n0 (mkLEnt true 1 0 1 1) in
  let l2 := t4_set (t4_set le_emp n0 (mkLEnt true 2 0 0 2)) n1 (mkLEnt true 2 1 2 0) in
  let l3 := t4_set (t4_set le_emp n0 (mkLEnt true 3 0 2 1)) n1 (mkLEnt true 3 1 0 4) in
  let ltab_init := t8_set (t8_set (t8_set (t8_set ltab0 0 l0) 1 l1) 2 l2) 3 l3 in
  let dtab0 := t4_const (mkDEntry false 0 0 0 0) in
  let dtab_init :=
    t4_set (t4_set (t4_set dtab0 (N_to_nib3 2) (mkDEntry true 2 1 0 1))
                                 (N_to_nib3 3) (mkDEntry true 3 1 1 2))
           (N_to_nib3 4) (mkDEntry true 4 5 0 6) in
  let f2_l := [mpos 0 n0 0 (big_small D02); mzero 1 n2 2] in
  let f3_l := [mpos 0 n2 2 (big_small D01); mpos 1 n0 0 (big_small D04)] in
  let f3_t := pack_t4 mnone dv0 dv1 f3_l in
  let d3 := mkDEnt true 3 1 n1 1 (big_small D02) in
  let d4 := mkDEnt true 4 5 n0 0 (big_small D06) in
  let st0 := mkDPState 2%nat 2 f2_l f3_l f3_t d3 d4 ltab_init dtab_init in
  let stF := List.fold_left (fun st '(steps, h) => run_dp_chunk t0 t1 idr dv0 dv1 le_emp steps h st) hint_chunks st0 in
  (dps_ltab stF, dps_dtab stF).


(* ========================================================================= *)
(* Section 4b: Soundness of Radix Trees, Big96, and DP Runner                *)
(* ========================================================================= *)

Definition v16_all {A : Type} (P : A -> Prop) (v : V16 A) : Prop :=
  P (q00 v) /\ P (q01 v) /\ P (q02 v) /\ P (q03 v) /\
  P (q04 v) /\ P (q05 v) /\ P (q06 v) /\ P (q07 v) /\
  P (q08 v) /\ P (q09 v) /\ P (q10 v) /\ P (q11 v) /\
  P (q12 v) /\ P (q13 v) /\ P (q14 v) /\ P (q15 v).

Lemma get16_all {A : Type} {P : A -> Prop} {v : V16 A} (hv : v16_all P v) (i : Nib) :
  P (get16 v i).
Proof.
  destruct hv as [h00 [h01 [h02 [h03 [h04 [h05 [h06 [h07 [h08 [h09 [h10 [h11 [h12 [h13 [h14 h15]]]]]]]]]]]]]]].
  destruct i; assumption.
Qed.

Lemma v16_const_all {A : Type} {P : A -> Prop} {d : A} (hd : P d) :
  v16_all P (v16_const d).
Proof.
  unfold v16_const, v16_all; cbn; repeat split; exact hd.
Qed.

Lemma v16_set_all {A : Type} {P : A -> Prop} {v : V16 A} (hv : v16_all P v)
  (i : Nib) {x : A} (hx : P x) :
  v16_all P (v16_set v i x).
Proof.
  destruct hv as [h00 [h01 [h02 [h03 [h04 [h05 [h06 [h07 [h08 [h09 [h10 [h11 [h12 [h13 [h14 h15]]]]]]]]]]]]]]].
  destruct i; unfold v16_set, v16_all; cbn; repeat split; assumption.
Qed.

Definition t4_all {A : Type} (P : A -> Prop) (t : T4096 A) : Prop :=
  v16_all (v16_all (v16_all P)) t.

Lemma get_t4_all {A : Type} {P : A -> Prop} {t : T4096 A} (ht : t4_all P t) (k : Nib3) :
  P (get_t4 t k).
Proof.
  unfold get_t4; cbv zeta; exact (get16_all (get16_all (get16_all ht (nb2 k)) (nb1 k)) (nb0 k)).
Qed.

Lemma t4_const_all {A : Type} {P : A -> Prop} {d : A} (hd : P d) :
  t4_all P (t4_const d).
Proof.
  exact (v16_const_all (v16_const_all (v16_const_all hd))).
Qed.

Lemma t4_set_all {A : Type} {P : A -> Prop} {t : T4096 A} (ht : t4_all P t)
  (k : Nib3) {x : A} (hx : P x) :
  t4_all P (t4_set t k x).
Proof.
  unfold t4_set, t4_all.
  apply v16_set_all; [exact ht |].
  apply v16_set_all; [exact (get16_all ht (nb2 k)) |].
  apply v16_set_all; [exact (get16_all (get16_all ht (nb2 k)) (nb1 k)) | exact hx].
Qed.

Definition t8_all {A : Type} (P : A -> Prop) (t : T8192 A) : Prop :=
  t4_all P (t8_lo t) /\ t4_all P (t8_hi t).

Lemma t8_get_all {A : Type} {P : A -> Prop} {t : T8192 A} (ht : t8_all P t) (x : N) :
  P (t8_get t x).
Proof.
  unfold t8_get; destruct (4096 <=? x);
    [exact (get_t4_all (proj2 ht) _) | exact (get_t4_all (proj1 ht) _)].
Qed.

Lemma t8_set_all {A : Type} {P : A -> Prop} {t : T8192 A} (ht : t8_all P t)
  (x : N) {v : A} (hv : P v) :
  t8_all P (t8_set t x v).
Proof.
  unfold t8_set, t8_all; destruct (4096 <=? x); cbn [t8_lo t8_hi];
    [exact (conj (proj1 ht) (t4_set_all (proj2 ht) _ hv))
    | exact (conj (t4_set_all (proj1 ht) _ hv) (proj2 ht))].
Qed.

Lemma forall_hd_tl {A : Type} {P : A -> Prop} {d : A} (hd : P d) {xs : list A} (hxs : Forall P xs) :
  P (match xs with x :: _ => x | [] => d end) /\ Forall P (tl xs).
Proof.
  destruct hxs as [| x l hx hl]; [exact (conj hd (Forall_nil P)) | exact (conj hx hl)].
Qed.

Lemma pack_v16_one_all {A : Type} {P : A -> Prop} {d : A} (hd : P d) {xs : list A} (hxs : Forall P xs) :
  v16_all P (pack_v16_one d xs).
Proof.
  unfold pack_v16_one, v16_all; cbn [q00 q01 q02 q03 q04 q05 q06 q07 q08 q09 q10 q11 q12 q13 q14 q15].
  do 16 (destruct (forall_hd_tl hd hxs) as [? hxs_next]; clear hxs; rename hxs_next into hxs).
  repeat split; assumption.
Qed.

Lemma pack_v16_list_all {A : Type} {P : A -> Prop} {d : A} (hd : P d) :
  forall (cnt : nat) {xs : list A}, Forall P xs -> Forall (v16_all P) (pack_v16_list d cnt xs).
Proof.
  induction cnt as [| cnt' IH]; intros xs hxs; cbn [pack_v16_list]; [constructor |].
  destruct hxs as [| a00 xs h00 hxs]; [constructor |].
  destruct hxs as [| a01 xs h01 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a02 xs h02 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a03 xs h03 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a04 xs h04 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a05 xs h05 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a06 xs h06 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a07 xs h07 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a08 xs h08 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a09 xs h09 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a10 xs h10 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a11 xs h11 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a12 xs h12 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a13 xs h13 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a14 xs h14 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  destruct hxs as [| a15 xs h15 hxs]; [constructor; [unfold pack_v16_one, v16_all; cbn; repeat split; assumption | constructor] |].
  constructor; [unfold v16_all; cbn; repeat split; assumption | exact (IH xs hxs)].
Qed.

Lemma pack_t4_all {A : Type} {P : A -> Prop} {d : A} (hd : P d) {xs : list A} (hxs : Forall P xs) :
  t4_all P (pack_t4 d (v16_const d) (v16_const (v16_const d)) xs).
Proof.
  unfold pack_t4, t4_all.
  pose proof (v16_const_all hd) as hdv0.
  pose proof (v16_const_all hdv0) as hdv1.
  exact (pack_v16_one_all hdv1 (pack_v16_list_all hdv0 16%nat (pack_v16_list_all hd 256%nat hxs))).
Qed.

Lemma push_d64_spec (d : D64) (hi : N) :
  push_d64 d hi = d64_val d + 64 * hi.
Proof.
  destruct d; cbn [push_d64 d64_val]; rewrite ?N.double_spec, ?N.succ_double_spec; lia.
Qed.

Definition forall_d64 (f : D64 -> bool) : bool :=
  (f D00 && (f D01 && (f D02 && (f D03 && (f D04 && (f D05 && (f D06 && (f D07 && (f D08 && (f D09 && (f D10 && (f D11 && (f D12 && (f D13 && (f D14 && (f D15 && (f D16 && (f D17 && (f D18 && (f D19 && (f D20 && (f D21 && (f D22 && (f D23 && (f D24 && (f D25 && (f D26 && (f D27 && (f D28 && (f D29 && (f D30 && (f D31 && (f D32 && (f D33 && (f D34 && (f D35 && (f D36 && (f D37 && (f D38 && (f D39 && (f D40 && (f D41 && (f D42 && (f D43 && (f D44 && (f D45 && (f D46 && (f D47 && (f D48 && (f D49 && (f D50 && (f D51 && (f D52 && (f D53 && (f D54 && (f D55 && (f D56 && (f D57 && (f D58 && (f D59 && (f D60 && (f D61 && (f D62 && f D63))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Lemma forall_d64_ok (f : D64 -> bool) (h : forall_d64 f = true) (d : D64) :
  f d = true.
Proof.
  unfold forall_d64 in h.
  do 63 (apply andb_prop in h; destruct h as [? h]).
  destruct d; assumption.
Qed.

Definition Tabs6Ok (t0 t1 : V64 (V64 R6)) (idr : V64 R6) : Prop :=
  (forall (a : D64), r6_c (get64 idr a) = false /\ d64_val (r6_lo (get64 idr a)) = d64_val a) /\
  (forall (c : bool) (a b : D64),
    let r := add6_in t0 t1 c a b in
    d64_val (r6_lo r) + 64 * (if r6_c r then 1 else 0) =
      d64_val a + d64_val b + (if c then 1 else 0)).

Definition check_idr_b (idr : V64 R6) : bool :=
  forall_d64 (fun a => negb (r6_c (get64 idr a)) && (d64_val (r6_lo (get64 idr a)) =? d64_val a)).

Definition check_add6_b (t0 t1 : V64 (V64 R6)) : bool :=
  let chk (c : bool) :=
    forall_d64 (fun a => forall_d64 (fun b =>
      let r := add6_in t0 t1 c a b in
      d64_val (r6_lo r) + 64 * (if r6_c r then 1 else 0) =?
        d64_val a + d64_val b + (if c then 1 else 0))) in
  chk false && chk true.

Definition check_tabs6_all : bool :=
  let '(t0, t1, idr) := build_tabs6 in
  check_idr_b idr && check_add6_b t0 t1.

Lemma check_tabs6_all_true : check_tabs6_all = true.
Proof. vm_compute; reflexivity. Qed.

Lemma check_tabs6_sound (t0 t1 : V64 (V64 R6)) (idr : V64 R6)
  (h : check_idr_b idr && check_add6_b t0 t1 = true) :
  Tabs6Ok t0 t1 idr.
Proof.
  apply andb_prop in h; destruct h as [hidr hadd].
  apply andb_prop in hadd; destruct hadd as [hadd0 hadd1].
  split.
  - intro a. pose proof (forall_d64_ok _ hidr a) as ha; cbn beta in ha.
    apply andb_prop in ha; destruct ha as [hc hlo].
    split; [destruct (r6_c (get64 idr a)); [discriminate | reflexivity]
           | apply N.eqb_eq; exact hlo].
  - intros [|] a b.
    + pose proof (forall_d64_ok _ (forall_d64_ok _ hadd1 a) b) as hab; cbn beta in hab.
      apply N.eqb_eq; exact hab.
    + pose proof (forall_d64_ok _ (forall_d64_ok _ hadd0 a) b) as hab; cbn beta in hab.
      apply N.eqb_eq; exact hab.
Qed.

Lemma build_tabs6_ok (P : V64 (V64 R6) -> V64 (V64 R6) -> V64 R6 -> Prop)
  (hP : forall t0 t1 idr, Tabs6Ok t0 t1 idr -> P t0 t1 idr) :
  let '(t0, t1, idr) := build_tabs6 in P t0 t1 idr.
Proof.
  generalize check_tabs6_all_true; unfold check_tabs6_all.
  destruct build_tabs6 as [[t0 t1] idr].
  intro h; exact (hP t0 t1 idr (check_tabs6_sound t0 t1 idr h)).
Qed.

Lemma inc6_spec {t0 t1 : V64 (V64 R6)} {idr : V64 R6} (htabs : Tabs6Ok t0 t1 idr)
  (cin : bool) (a : D64) :
  let r := inc6_in (p00 t1) idr cin a in
  d64_val (r6_lo r) + 64 * (if r6_c r then 1 else 0) = d64_val a + (if cin then 1 else 0).
Proof.
  unfold inc6_in; destruct cin; cbv zeta.
  - pose proof (proj2 htabs true D00 a) as h; unfold add6_in in h; cbv beta iota zeta in h.
    cbn [d64_val] in h; lia.
  - destruct (proj1 htabs a) as [hc hlo]; rewrite hc, hlo; lia.
Qed.

Lemma limb_inc_combine (lo a hi_new hi_old : N) (cin cout : bool)
  (hlo : lo + 64 * (if cout then 1 else 0) = a + (if cin then 1 else 0))
  (hhi : hi_new = hi_old + (if cout then 1 else 0)) :
  lo + 64 * hi_new = (a + 64 * hi_old) + (if cin then 1 else 0).
Proof. lia. Qed.

Lemma limb_add_combine (lo a b hi_new hi_x hi_y : N) (cin cout : bool)
  (hlo : lo + 64 * (if cout then 1 else 0) = a + b + (if cin then 1 else 0))
  (hhi : hi_new = hi_x + hi_y + (if cout then 1 else 0)) :
  lo + 64 * hi_new = (a + 64 * hi_x) + (b + 64 * hi_y) + (if cin then 1 else 0).
Proof. lia. Qed.

Lemma chunk16_val (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 : D64) (hi : N) :
  push_d64 a00 (push_d64 a01 (push_d64 a02 (push_d64 a03 (push_d64 a04
  (push_d64 a05 (push_d64 a06 (push_d64 a07 (push_d64 a08 (push_d64 a09
  (push_d64 a10 (push_d64 a11 (push_d64 a12 (push_d64 a13 (push_d64 a14
  (push_d64 a15 hi))))))))))))))) =
  d64_val a00 + 64 * (d64_val a01 + 64 * (d64_val a02 + 64 * (d64_val a03 +
  64 * (d64_val a04 + 64 * (d64_val a05 + 64 * (d64_val a06 + 64 * (d64_val a07 +
  64 * (d64_val a08 + 64 * (d64_val a09 + 64 * (d64_val a10 + 64 * (d64_val a11 +
  64 * (d64_val a12 + 64 * (d64_val a13 + 64 * (d64_val a14 + 64 * (d64_val a15 + 64 * hi))))))))))))))).
Proof. rewrite !push_d64_spec; reflexivity. Qed.

Lemma big_inc_spec {t0 t1 : V64 (V64 R6)} {idr : V64 R6} (htabs : Tabs6Ok t0 t1 idr)
  (x : Big96) :
  big_to_N (big_inc t1 idr x) = big_to_N x + 1.
Proof.
  induction x as [| a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 tl IH].
  - cbn [big_inc big_small big_to_N push_d64 N.double N.succ_double]; reflexivity.
  - cbn [big_inc]; cbv zeta.
    pose proof (inc6_spec htabs true a00) as hr00; cbv zeta in hr00.
    set (r00 := inc6_in (p00 t1) idr true a00) in *; clearbody r00.
    destruct (negb (r6_c r00)) eqn:hnc.
    + destruct (r6_c r00); [discriminate |].
      cbn [big_to_N]; cbv zeta; rewrite !chunk16_val.
      clear - hr00; lia.
    + do 15 (
        lazymatch goal with
        | |- context [inc6_in (p00 t1) idr (r6_c ?rprev) ?ai] =>
          let hri := fresh "hr" in
          let ri := fresh "r" in
          pose proof (inc6_spec htabs (r6_c rprev) ai) as hri; cbv zeta in hri;
          set (ri := inc6_in (p00 t1) idr (r6_c rprev) ai) in *; clearbody ri
        end
      ).
      cbn [big_to_N]; cbv zeta; rewrite !chunk16_val.
      eapply (limb_inc_combine _ _ _ _ true); [exact hr00 |].
      do 15 (eapply limb_inc_combine; [eassumption |]).
      lazymatch goal with |- big_to_N (if ?c then _ else _) = _ => destruct c end; [exact IH | clear; lia].
Qed.

Lemma big_add_c_spec {t0 t1 : V64 (V64 R6)} {idr : V64 R6} (htabs : Tabs6Ok t0 t1 idr)
  (x : Big96) :
  forall (c : bool) (y : Big96),
    big_to_N (big_add_c t0 t1 idr c x y) = big_to_N x + big_to_N y + (if c then 1 else 0).
Proof.
  induction x as [| a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 tx IH];
    intros c y.
  - cbn [big_add_c big_to_N].
    destruct c; [rewrite (big_inc_spec htabs y); lia | lia].
  - destruct y as [| b00 b01 b02 b03 b04 b05 b06 b07 b08 b09 b10 b11 b12 b13 b14 b15 ty].
    + cbn [big_add_c]; change (big_to_N u_nil) with 0.
      destruct c; [rewrite (big_inc_spec htabs _); lia | lia].
    + cbn [big_add_c]; cbv zeta.
      do 16 (
        lazymatch goal with
        | |- context [add6_in t0 t1 ?cin ?ai ?bi] =>
          let hri := fresh "hr" in
          let ri := fresh "r" in
          pose proof (proj2 htabs cin ai bi) as hri; cbv zeta in hri;
          set (ri := add6_in t0 t1 cin ai bi) in *; clearbody ri
        end
      ).
      cbn [big_to_N]; cbv zeta; rewrite !chunk16_val.
      do 16 (eapply limb_add_combine; [eassumption |]).
      exact (IH _ ty).
Qed.

Definition MEntValid (W : N) (e : MEnt) : Prop :=
  match e with
  | mnone => True
  | mzero my _ py => LCellSpec W my py 0
  | mpos my _ py m => 1 <= big_to_N m /\ LCellSpec W my py (big_to_N m)
  end.

Definition DEntValid (d : DEnt) : Prop :=
  de_ok d = true -> DValid (de_k d) (de_dx d) (de_dy d) (big_to_N (de_m d)).

Definition LEntValid (e : LEnt) : Prop :=
  le_ok e = true -> LCellSpec (le_W e) (le_y e) (le_py e) (le_m e).

Definition DEntryValid (e : DEntry) : Prop :=
  den_ok e = true -> DValid (den_k e) (den_dx e) (den_dy e) (den_mD e).

Lemma build_ev_valid {t0 t1 : V64 (V64 R6)} {idr : V64 R6} (htabs : Tabs6Ok t0 t1 idr)
  (ny : N) (fO : T4096 MEnt) (hfO : t4_all (MEntValid (2 * ny - 1)) fO)
  (dP : DEnt) (hdP : DEntValid dP) :
  forall (cnt : nat) (y : N) (fe : list MEnt),
    Forall (MEntValid (2 * ny - 2)) fe ->
    Forall (MEntValid (2 * ny)) (build_ev t0 t1 idr cnt y ny (2 * ny) fe fO dP).
Proof.
  induction cnt as [| cnt' IH]; intros y fe hfe; cbn [build_ev]; [constructor |].
  assert (hpair : exists (e1 : MEnt) (fe' : list MEnt),
            (match fe with x :: r => (x, r) | [] => (mnone, []) end) = (e1, fe') /\
            MEntValid (2 * ny - 2) e1 /\ Forall (MEntValid (2 * ny - 2)) fe').
  { destruct hfe as [| x r hx hr];
      [exists mnone, (@nil MEnt); repeat split; constructor
      | exists x, r; repeat split; assumption]. }
  destruct hpair as [e1 [fe' [-> [he1 hfe']]]]; cbv zeta.
  constructor; [| exact (IH (y + 1) fe' hfe')].
  destruct e1 as [| my0 pk0 py0 | my pk1 py1 m1].
  - destruct (y =? ny) eqn:hy_ny.
    + apply N.eqb_eq in hy_ny; subst y; cbn [MEntValid]; exact (LCellSpec_x0 ny).
    + destruct ((y + 1 =? ny) && de_ok dP && (de_k dP =? y + 2) && (1 <=? y)) eqn:hc; [| exact I].
      apply andb_prop in hc; destruct hc as [hc hy1].
      apply andb_prop in hc; destruct hc as [hc hdk].
      apply andb_prop in hc; destruct hc as [hy_ny1 hdok].
      apply N.eqb_eq in hy_ny1; apply N.eqb_eq in hdk; apply N.leb_le in hy1.
      pose proof (hdP hdok) as hd_val; rewrite hdk in hd_val.
      cbn [MEntValid]; rewrite (big_inc_spec htabs (de_m dP)).
      split; [clear; lia |].
      replace (2 * ny) with (2 * y + 2) by (clear - hy_ny1; lia).
      exact (LCellSpec_x2 y (de_dx dP) (de_dy dP) (big_to_N (de_m dP)) hy1 hd_val).
  - destruct (y =? ny) eqn:hy_ny.
    + apply N.eqb_eq in hy_ny; subst y; cbn [MEntValid]; exact (LCellSpec_x0 ny).
    + destruct ((y + 1 =? ny) && de_ok dP && (de_k dP =? y + 2) && (1 <=? y)) eqn:hc; [| exact I].
      apply andb_prop in hc; destruct hc as [hc hy1].
      apply andb_prop in hc; destruct hc as [hc hdk].
      apply andb_prop in hc; destruct hc as [hy_ny1 hdok].
      apply N.eqb_eq in hy_ny1; apply N.eqb_eq in hdk; apply N.leb_le in hy1.
      pose proof (hdP hdok) as hd_val; rewrite hdk in hd_val.
      cbn [MEntValid]; rewrite (big_inc_spec htabs (de_m dP)).
      split; [clear; lia |].
      replace (2 * ny) with (2 * y + 2) by (clear - hy_ny1; lia).
      exact (LCellSpec_x2 y (de_dx dP) (de_dy dP) (big_to_N (de_m dP)) hy1 hd_val).
  - destruct he1 as [hm1 hl1].
    destruct ((my =? y) && (2 * y + 3 <=? 2 * ny)) eqn:hc; [| exact I].
    apply andb_prop in hc; destruct hc as [hmy hx3].
    apply N.eqb_eq in hmy; apply N.leb_le in hx3; subst my.
    pose proof (get_t4_all hfO pk1) as he2.
    destruct (get_t4 fO pk1) as [| my2 pk2 py2 | my2 pk2 py2 m2]; [exact I | |].
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; cbn [MEntValid] in he2 |- *.
      split; [exact hm1 |].
      replace (big_to_N m1) with (big_to_N m1 + 0) by (clear; lia).
      exact (LCellSpec_bulk (2 * ny) y py1 (big_to_N m1) py2 0 hx3 hl1 he2).
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; destruct he2 as [hm2 hl2].
      cbn [MEntValid]; rewrite (big_add_c_spec htabs m1 false m2).
      replace (big_to_N m1 + big_to_N m2 + 0) with (big_to_N m1 + big_to_N m2) by (clear; lia).
      split; [clear - hm1; lia |].
      exact (LCellSpec_bulk (2 * ny) y py1 (big_to_N m1) py2 (big_to_N m2) hx3 hl1 hl2).
Qed.

Lemma build_od_valid {t0 t1 : V64 (V64 R6)} {idr : V64 R6} (htabs : Tabs6Ok t0 t1 idr)
  (ny : N) (hny : 1 <= ny) (fEv : T4096 MEnt) (hfEv : t4_all (MEntValid (2 * ny)) fEv)
  (dP : DEnt) (hdP : DEntValid dP) :
  forall (cnt : nat) (y : N) (fo : list MEnt),
    Forall (MEntValid (2 * ny - 1)) fo ->
    Forall (MEntValid (2 * ny + 1)) (build_od t0 t1 idr cnt y ny (2 * ny + 1) fo fEv dP).
Proof.
  induction cnt as [| cnt' IH]; intros y fo hfo; cbn [build_od]; [constructor |].
  assert (hpair : exists (e1 : MEnt) (fo' : list MEnt),
            (match fo with x :: r => (x, r) | [] => (mnone, []) end) = (e1, fo') /\
            MEntValid (2 * ny - 1) e1 /\ Forall (MEntValid (2 * ny - 1)) fo').
  { destruct hfo as [| x r hx hr];
      [exists mnone, (@nil MEnt); repeat split; constructor
      | exists x, r; repeat split; assumption]. }
  destruct hpair as [e1 [fo' [-> [he1 hfo']]]]; cbv zeta.
  constructor; [| exact (IH (y + 1) fo' hfo')].
  destruct e1 as [| my0 pk0 py0 | my pk1 py1 m1].
  - destruct ((y =? ny) && de_ok dP && (de_k dP =? y + 1) && (1 <=? y)) eqn:hc; [| exact I].
    apply andb_prop in hc; destruct hc as [hc hy1].
    apply andb_prop in hc; destruct hc as [hc hdk].
    apply andb_prop in hc; destruct hc as [hy_ny hdok].
    apply N.eqb_eq in hy_ny; apply N.eqb_eq in hdk; apply N.leb_le in hy1; subst ny.
    pose proof (hdP hdok) as hd_val; rewrite hdk in hd_val.
    pose proof (get_t4_all hfEv (de_dyk dP)) as he2.
    destruct (get_t4 fEv (de_dyk dP)) as [| my2 pk2 py2 | my2 pk2 py2 m2]; [exact I | |].
    + destruct (my2 =? de_dy dP) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; cbn [MEntValid] in he2 |- *.
      rewrite (big_inc_spec htabs (de_m dP)).
      split; [clear; lia |].
      replace (big_to_N (de_m dP) + 1) with (big_to_N (de_m dP) + 1 + 0) by (clear; lia).
      exact (LCellSpec_x1 y (de_dx dP) (de_dy dP) (big_to_N (de_m dP)) py2 0 hy1 hd_val he2).
    + destruct (my2 =? de_dy dP) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; destruct he2 as [hm2 hl2].
      cbn [MEntValid]; rewrite (big_add_c_spec htabs (de_m dP) true m2).
      split; [clear; lia |].
      replace (big_to_N (de_m dP) + big_to_N m2 + 1) with (big_to_N (de_m dP) + 1 + big_to_N m2) by (clear; lia).
      exact (LCellSpec_x1 y (de_dx dP) (de_dy dP) (big_to_N (de_m dP)) py2 (big_to_N m2) hy1 hd_val hl2).
  - exact I.
  - destruct he1 as [hm1 hl1].
    destruct ((my =? y) && (2 * y + 3 <=? 2 * ny + 1)) eqn:hc; [| exact I].
    apply andb_prop in hc; destruct hc as [hmy hx3].
    apply N.eqb_eq in hmy; apply N.leb_le in hx3; subst my.
    pose proof (get_t4_all hfEv pk1) as he2.
    replace (2 * ny - 1) with (2 * ny + 1 - 2) in hl1 by (clear - hny; lia).
    replace (2 * ny) with (2 * ny + 1 - 1) in he2 by (clear; lia).
    destruct (get_t4 fEv pk1) as [| my2 pk2 py2 | my2 pk2 py2 m2]; [exact I | |].
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; cbn [MEntValid] in he2 |- *.
      split; [exact hm1 |].
      replace (big_to_N m1) with (big_to_N m1 + 0) by (clear; lia).
      exact (LCellSpec_bulk (2 * ny + 1) y py1 (big_to_N m1) py2 0 hx3 hl1 he2).
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; destruct he2 as [hm2 hl2].
      cbn [MEntValid]; rewrite (big_add_c_spec htabs m1 false m2).
      replace (big_to_N m1 + big_to_N m2 + 0) with (big_to_N m1 + big_to_N m2) by (clear; lia).
      split; [clear - hm1; lia |].
      exact (LCellSpec_bulk (2 * ny + 1) y py1 (big_to_N m1) py2 (big_to_N m2) hx3 hl1 hl2).
Qed.

Lemma extract_step_valid (W : N) (ft : T4096 MEnt) (hft : t4_all (MEntValid W) ft)
  (p : positive) (st : ExtSt) (hlay : t4_all LEntValid (es_lay st)) :
  t4_all LEntValid (es_lay (sr_val (runPos p (extract_step W ft) st))).
Proof.
  refine (runPos_rel
            (fun s1 s2 => t4_all LEntValid (es_lay s1) -> t4_all LEntValid (es_lay s2))
            (fun _ _ _ h12 h23 h1 => h23 (h12 h1))
            (extract_step W ft) _ p st hlay).
  intros s hs; unfold extract_step; cbv zeta.
  set (nib := (if N.odd (es_h s) then 1 else 0) +
              (if N.odd (N.div2 (es_h s)) then 2 else 0) +
              (if N.odd (N.div2 (N.div2 (es_h s))) then 4 else 0) +
              (if N.odd (N.div2 (N.div2 (N.div2 (es_h s)))) then 8 else 0)).
  destruct (nib =? 0); [exact hs |].
  destruct (nib <? 8); [| exact hs].
  cbn [sr_val es_lay].
  set (y := es_y s + (es_acc s + N.shiftl (nib - 1) (es_sh s))).
  set (yk := N_to_nib3 y).
  pose proof (get_t4_all hft yk) as he.
  destruct (get_t4 ft yk) as [| my pk py | my pk py m]; [exact hs | |].
  - destruct (my =? y) eqn:hmy; [| exact hs].
    apply N.eqb_eq in hmy; subst my.
    apply t4_set_all; [exact hs | intro; exact he].
  - destruct (my =? y) eqn:hmy; [| exact hs].
    apply N.eqb_eq in hmy; subst my.
    apply t4_set_all; [exact hs | intro; exact (proj2 he)].
Qed.

Definition DPStateValid (st : DPState) : Prop :=
  2 <= dps_ny st /\
  Forall (MEntValid (2 * dps_ny st - 2)) (dps_fe_l st) /\
  Forall (MEntValid (2 * dps_ny st - 1)) (dps_fo_l st) /\
  t4_all (MEntValid (2 * dps_ny st - 1)) (dps_fo_t st) /\
  DEntValid (dps_dP st) /\
  DEntValid (dps_dC st) /\
  t8_all (t4_all LEntValid) (dps_ltab st) /\
  t4_all DEntryValid (dps_dtab st).

Lemma run_dp_chunk_valid {t0 t1 : V64 (V64 R6)} {idr : V64 R6} (htabs : Tabs6Ok t0 t1 idr)
  (le_emp : T4096 LEnt) (hle_emp : t4_all LEntValid le_emp) :
  forall (rem : nat) (h : N) (st : DPState),
    DPStateValid st ->
    DPStateValid (run_dp_chunk t0 t1 idr (v16_const mnone) (v16_const (v16_const mnone)) le_emp rem h st).
Proof.
  induction rem as [| rem' IH]; intros h st hst; [exact hst |].
  cbn [run_dp_chunk]; cbv zeta.
  destruct hst as [hny [hfe_l [hfo_l [hfo_t [hdP [hdC [hltab hdtab]]]]]]].
  set (ny := dps_ny st) in *.
  pose proof (build_ev_valid htabs ny (dps_fo_t st) hfo_t (dps_dP st) hdP (S (dps_ny_nat st)) 0 (dps_fe_l st) hfe_l) as hfev_l.
  pose proof (pack_t4_all (I : MEntValid (2 * ny) mnone) hfev_l) as hfev_t.
  set (fev_l := build_ev t0 t1 idr (S (dps_ny_nat st)) 0 ny (2 * ny) (dps_fe_l st) (dps_fo_t st) (dps_dP st)) in *.
  set (fev_t := pack_t4 mnone (v16_const mnone) (v16_const (v16_const mnone)) fev_l) in *.
  set (ex1 := sr_val (runPos 8192%positive (extract_step (2 * ny) fev_t) (mkExtSt 0 0 0 h le_emp))) in *.
  pose proof (extract_step_valid (2 * ny) fev_t hfev_t 8192%positive (mkExtSt 0 0 0 h le_emp) hle_emp) as hex1.
  fold ex1 in hex1.
  pose proof (t8_set_all hltab (2 * ny) hex1) as hltab1.
  pose proof (proj2 (forall_hd_tl (I : MEntValid (2 * ny - 1) mnone) hfo_l)) as hfo_tl.
  assert (hny1 : 1 <= ny) by (clear - hny; lia).
  pose proof (build_od_valid htabs ny hny1 fev_t hfev_t (dps_dP st) hdP (dps_ny_nat st) 1 (tl (dps_fo_l st)) hfo_tl) as hfod_tl.
  assert (hfod_hd : MEntValid (2 * ny + 1) (mpos 0 (N_to_nib3 (ny + 1)) (ny + 1) (big_small D01))).
  { cbn [MEntValid big_small big_to_N push_d64 N.double N.succ_double].
    split; [clear; lia | exact (LCellSpec_y0_odd ny)]. }
  pose proof (Forall_cons _ hfod_hd hfod_tl) as hfod_l.
  set (fod_l := mpos 0 (N_to_nib3 (ny + 1)) (ny + 1) (big_small D01) ::
                  build_od t0 t1 idr (dps_ny_nat st) 1 ny (2 * ny + 1) (tl (dps_fo_l st)) fev_t (dps_dP st)) in *.
  pose proof (pack_t4_all (I : MEntValid (2 * ny + 1) mnone) hfod_l) as hfod_t.
  set (fod_t := pack_t4 mnone (v16_const mnone) (v16_const (v16_const mnone)) fod_l) in *.
  set (ex2 := sr_val (runPos 8192%positive (extract_step (2 * ny + 1) fod_t) (mkExtSt 0 0 0 (es_h ex1) le_emp))) in *.
  pose proof (extract_step_valid (2 * ny + 1) fod_t hfod_t 8192%positive (mkExtSt 0 0 0 (es_h ex1) le_emp) hle_emp) as hex2.
  fold ex2 in hex2.
  pose proof (t8_set_all hltab1 (2 * ny + 1) hex2) as hltab2.
  set (dC := dps_dC st) in *.
  set (n0 := mkNib3 N00 N00 N00).
  lazymatch goal with
  | |- DPStateValid (match ?u with _ => _ end) => set (upd := u)
  end.
  assert (hupd : DEntValid (fst upd) /\ t4_all DEntryValid (snd upd)).
  { subst upd.
    destruct (de_ok dC && (de_k dC =? ny + 2)) eqn:hdc_ok;
      [| split; [intro; discriminate | exact hdtab]].
    apply andb_prop in hdc_ok; destruct hdc_ok as [hdok hdk].
    apply N.eqb_eq in hdk.
    pose proof (hdC hdok) as hd_val; rewrite hdk in hd_val.
    pose proof (get_t4_all hfod_t (de_dyk dC)) as he_od.
    destruct (get_t4 fod_t (de_dyk dC)) as [| ? ? ? | my pk py m];
      [split; [intro; discriminate | exact hdtab]
      | split; [intro; discriminate | exact hdtab]
      |].
    destruct (my =? de_dy dC) eqn:hmy;
      [| split; [intro; discriminate | exact hdtab]].
    apply N.eqb_eq in hmy; subst my; destruct he_od as [_ hl_od].
    replace (2 * ny + 1) with (2 * (ny + 2) - 3) in hl_od by (clear - hny; lia).
    pose proof (DValid_step hd_val hl_od) as hd_next.
    replace (ny + 2 + 1) with (ny + 3) in hd_next by (clear; lia).
    cbv zeta; cbn [fst snd].
    assert (hnm : big_to_N (big_add_c t0 t1 idr false (de_m dC) m) = big_to_N (de_m dC) + big_to_N m).
    { rewrite (big_add_c_spec htabs (de_m dC) false m); clear; lia. }
    split.
    - intro; cbn [de_k de_dx de_dy de_m]; rewrite hnm; exact hd_next.
    - destruct (ny + 3 <? 4096); [| exact hdtab].
      apply t4_set_all; [exact hdtab |].
      intro; cbn [den_k den_dx den_dy den_mD]; rewrite hnm; exact hd_next. }
  destruct upd as [dN dtab']; destruct hupd as [hdN hdtab'].
  apply IH.
  unfold DPStateValid; cbn [dps_ny dps_fe_l dps_fo_l dps_fo_t dps_dP dps_dC dps_ltab dps_dtab].
  replace (2 * (ny + 1) - 2) with (2 * ny) by (clear; lia).
  replace (2 * (ny + 1) - 1) with (2 * ny + 1) by (clear; lia).
  refine (conj _ (conj hfev_l (conj hfod_l (conj hfod_t (conj hdC (conj hdN (conj hltab2 hdtab'))))))).
  clear - hny; lia.
Qed.

Lemma fold_left_dp_valid {t0 t1 : V64 (V64 R6)} {idr : V64 R6} (htabs : Tabs6Ok t0 t1 idr)
  (le_emp : T4096 LEnt) (hle_emp : t4_all LEntValid le_emp)
  (chunks : list (nat * N)) :
  forall st : DPState,
    DPStateValid st ->
    DPStateValid (List.fold_left
      (fun s '(steps, h) => run_dp_chunk t0 t1 idr (v16_const mnone) (v16_const (v16_const mnone)) le_emp steps h s)
      chunks st).
Proof.
  induction chunks as [| [steps h] rest IH]; intros st hst; [exact hst |].
  cbn [List.fold_left].
  exact (IH _ (run_dp_chunk_valid htabs le_emp hle_emp steps h st hst)).
Qed.

Lemma init_and_run_dp_valid :
  let '(ltab, dtab) := init_and_run_dp in
  t8_all (t4_all LEntValid) ltab /\ t4_all DEntryValid dtab.
Proof.
  unfold init_and_run_dp.
  pose proof check_tabs6_all_true as htabs_b; unfold check_tabs6_all in htabs_b.
  destruct build_tabs6 as [[t0 t1] idr].
  pose proof (check_tabs6_sound t0 t1 idr htabs_b) as htabs; clear htabs_b.
  cbv beta iota zeta.
  assert (hl_0_0 : LCellSpec 0 0 1 0) by exact (LCellSpec_x0 0).
  assert (hl_1_0 : LCellSpec 1 0 1 1) by exact (LCellSpec_y0_odd 0).
  assert (hl_2_0 : LCellSpec 2 0 0 2) by exact LCellSpec_y0_x2.
  assert (hl_2_1 : LCellSpec 2 1 2 0) by exact (LCellSpec_x0 1).
  assert (hl_3_0 : LCellSpec 3 0 2 1) by exact (LCellSpec_y0_odd 1).
  assert (hd_2 : DValid 2 1 0 1) by exact DValid_base2.
  assert (hl_3_1 : LCellSpec 3 1 0 4)
    by exact (LCellSpec_x1 1 1 0 1 0 2 (N.le_refl 1) hd_2 hl_2_0).
  assert (hd_3 : DValid 3 1 1 2) by exact (DValid_step hd_2 hl_1_0).
  assert (hd_4 : DValid 4 5 0 6) by exact (DValid_step hd_3 hl_3_1).
  set (lent0 := mkLEnt false 0 0 0 0).
  assert (hlent0 : LEntValid lent0) by (intro; discriminate).
  set (le_emp := t4_const lent0).
  pose proof (t4_const_all hlent0 : t4_all LEntValid le_emp) as hle_emp.
  set (ltab_half := t4_const le_emp).
  pose proof (t4_const_all hle_emp : t4_all (t4_all LEntValid) ltab_half) as hltab_half.
  set (ltab0 := mkT8 ltab_half ltab_half).
  assert (hltab0 : t8_all (t4_all LEntValid) ltab0) by exact (conj hltab_half hltab_half).
  set (n0 := mkNib3 N00 N00 N00); set (n1 := mkNib3 N00 N00 N01); set (n2 := mkNib3 N00 N00 N02).
  assert (hl0 : t4_all LEntValid (t4_set le_emp n0 (mkLEnt true 0 0 1 0)))
    by (apply t4_set_all; [exact hle_emp | intro; exact hl_0_0]).
  assert (hl1 : t4_all LEntValid (t4_set le_emp n0 (mkLEnt true 1 0 1 1)))
    by (apply t4_set_all; [exact hle_emp | intro; exact hl_1_0]).
  assert (hl2 : t4_all LEntValid (t4_set (t4_set le_emp n0 (mkLEnt true 2 0 0 2)) n1 (mkLEnt true 2 1 2 0)))
    by (apply t4_set_all; [apply t4_set_all; [exact hle_emp | intro; exact hl_2_0] | intro; exact hl_2_1]).
  assert (hl3 : t4_all LEntValid (t4_set (t4_set le_emp n0 (mkLEnt true 3 0 2 1)) n1 (mkLEnt true 3 1 0 4)))
    by (apply t4_set_all; [apply t4_set_all; [exact hle_emp | intro; exact hl_3_0] | intro; exact hl_3_1]).
  pose proof (t8_set_all (t8_set_all (t8_set_all (t8_set_all hltab0 0 hl0) 1 hl1) 2 hl2) 3 hl3) as hltab_init.
  assert (hdent0 : DEntryValid (mkDEntry false 0 0 0 0)) by (intro; discriminate).
  pose proof (t4_const_all hdent0) as hdtab0.
  assert (hdtab_init : t4_all DEntryValid
    (t4_set (t4_set (t4_set (t4_const (mkDEntry false 0 0 0 0)) (N_to_nib3 2) (mkDEntry true 2 1 0 1))
                    (N_to_nib3 3) (mkDEntry true 3 1 1 2))
            (N_to_nib3 4) (mkDEntry true 4 5 0 6))).
  { apply t4_set_all; [apply t4_set_all; [apply t4_set_all; [exact hdtab0 | intro; exact hd_2] | intro; exact hd_3] | intro; exact hd_4]. }
  assert (hf2_l : Forall (MEntValid 2) [mpos 0 n0 0 (big_small D02); mzero 1 n2 2]).
  { constructor; [cbn [MEntValid big_small big_to_N push_d64 N.double N.succ_double]; split; [lia | exact hl_2_0] |].
    constructor; [exact hl_2_1 | constructor]. }
  assert (hf3_l : Forall (MEntValid 3) [mpos 0 n2 2 (big_small D01); mpos 1 n0 0 (big_small D04)]).
  { constructor; [cbn [MEntValid big_small big_to_N push_d64 N.double N.succ_double]; split; [lia | exact hl_3_0] |].
    constructor; [cbn [MEntValid big_small big_to_N push_d64 N.double N.succ_double]; split; [lia | exact hl_3_1] | constructor]. }
  pose proof (pack_t4_all (I : MEntValid 3 mnone) hf3_l) as hf3_t.
  assert (hd3_v : DEntValid (mkDEnt true 3 1 n1 1 (big_small D02)))
    by (intro; cbn [de_k de_dx de_dy de_m big_small big_to_N push_d64 N.double N.succ_double]; exact hd_3).
  assert (hd4_v : DEntValid (mkDEnt true 4 5 n0 0 (big_small D06)))
    by (intro; cbn [de_k de_dx de_dy de_m big_small big_to_N push_d64 N.double N.succ_double]; exact hd_4).
  assert (hst0 : DPStateValid (mkDPState 2%nat 2
    [mpos 0 n0 0 (big_small D02); mzero 1 n2 2]
    [mpos 0 n2 2 (big_small D01); mpos 1 n0 0 (big_small D04)]
    (pack_t4 mnone (v16_const mnone) (v16_const (v16_const mnone)) [mpos 0 n2 2 (big_small D01); mpos 1 n0 0 (big_small D04)])
    (mkDEnt true 3 1 n1 1 (big_small D02))
    (mkDEnt true 4 5 n0 0 (big_small D06))
    (t8_set (t8_set (t8_set (t8_set ltab0 0 (t4_set le_emp n0 (mkLEnt true 0 0 1 0)))
                            1 (t4_set le_emp n0 (mkLEnt true 1 0 1 1)))
                    2 (t4_set (t4_set le_emp n0 (mkLEnt true 2 0 0 2)) n1 (mkLEnt true 2 1 2 0)))
            3 (t4_set (t4_set le_emp n0 (mkLEnt true 3 0 2 1)) n1 (mkLEnt true 3 1 0 4)))
    (t4_set (t4_set (t4_set (t4_const (mkDEntry false 0 0 0 0)) (N_to_nib3 2) (mkDEntry true 2 1 0 1))
                    (N_to_nib3 3) (mkDEntry true 3 1 1 2))
            (N_to_nib3 4) (mkDEntry true 4 5 0 6)))).
  { unfold DPStateValid; cbn [dps_ny dps_fe_l dps_fo_l dps_fo_t dps_dP dps_dC dps_ltab dps_dtab].
    exact (conj (N.le_refl 2) (conj hf2_l (conj hf3_l (conj hf3_t (conj hd3_v (conj hd4_v (conj hltab_init hdtab_init))))))). }
  pose proof (fold_left_dp_valid htabs le_emp hle_emp hint_chunks _ hst0) as hstF.
  exact (conj (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hstF)))))))
              (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hstF)))))))).
Qed.

(* --- Section 5: Macro Stepper --- *)
Definition lookupL (ltab : T8192 (T4096 LEnt)) (W y : N) : option (N * N) :=
  if (W <? 8192) && (y <? 4096) then
    let e := get_t4 (t8_get ltab W) (N_to_nib3 y) in
    if le_ok e && (le_W e =? W) && (le_y e =? y) then Some (le_py e, le_m e) else None
  else None.

Definition lookupD (dtab : T4096 DEntry) (k : N) : N * N * N :=
  if k <? 4096 then
    let e := get_t4 dtab (N_to_nib3 k) in
    if den_ok e && (den_k e =? k) then (den_dx e, den_dy e, den_mD e) else (0, 0, 0)
  else (0, 0, 0).

Definition exhaust01StepL (ltab : T8192 (T4096 LEnt)) (cur : Stalled) (acc : N) : option StAcc :=
  match cur with
  | Scanon1 x y _ | ScanonZ x y =>
    let W := x + 2 * y in
    match lookupL ltab W y with
    | None => None
    | Some (py, m) => Some (applyDeltaM cur (W + 2 - 2 * py) py m acc)
    end
  | _ => None
  end.

Fixpoint exhaust01LoopPos (ltab : T8192 (T4096 LEnt)) (p : positive) (cur : Stalled) (acc : N) : option StAcc :=
  match p with
  | xH => exhaust01StepL ltab cur acc
  | xO q =>
    match exhaust01LoopPos ltab q cur acc with
    | Some r1 => exhaust01LoopPos ltab q (sa_st r1) (sa_acc r1)
    | None => None
    end
  | xI q =>
    match exhaust01LoopPos ltab q cur acc with
    | Some r1 =>
      match exhaust01LoopPos ltab q (sa_st r1) (sa_acc r1) with
      | Some r2 => exhaust01StepL ltab (sa_st r2) (sa_acc r2)
      | None => None
      end
    | None => None
    end
  end.

Definition exhaust01LoopL (ltab : T8192 (T4096 LEnt)) (c : N) (cur : Stalled) (acc : N) : option StAcc :=
  match c with
  | N0 => Some (mkStAcc cur acc)
  | Npos p => exhaust01LoopPos ltab p cur acc
  end.

Definition tryDirectCanon (ltab : T8192 (T4096 LEnt)) (dtab : T4096 DEntry) (cur : Stalled) (x y c acc : N) : option StAcc :=
  let W := x + 2 * y in
  if W mod 2 =? 1 then
    let k0 := (W + 3) / 2 in
    let '(dx1, dy1, m1) := lookupD dtab k0 in
    let '(dx2, dy2, m2) := lookupD dtab (k0 + c) in
    if (dx1 =? x) && (dy1 =? y) && negb (m1 =? 0) && negb (m2 =? 0) then if m1 + 1 <=? m2 then
      Some (applyDeltaM cur dx2 dy2 (m2 - m1) acc)
      else
        let k2 := (W + 1) / 2 in
        let '(dx, dy, vmD) := lookupD dtab k2 in
        if (2 <=? k2) && (dx + 2 =? x) && (dy =? y) && negb (vmD =? 0) then
          let Wq := 2 * k2 - 2 + 2 * c in
          match lookupL ltab Wq (k2 - 2) with
          | Some (py, m) => if 2 * py <? Wq + 1 then if vmD + 2 <=? m then Some (applyDeltaM cur (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc) else None else None
          | None => None
          end
        else None
    else
      let k2 := (W + 1) / 2 in
      let '(dx, dy, vmD) := lookupD dtab k2 in
      if (2 <=? k2) && (dx + 2 =? x) && (dy =? y) && negb (vmD =? 0) then
        let Wq := 2 * k2 - 2 + 2 * c in
        match lookupL ltab Wq (k2 - 2) with
        | Some (py, m) => if 2 * py <? Wq + 1 then if vmD + 2 <=? m then Some (applyDeltaM cur (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc) else None else None
        | None => None
        end
      else None
  else
    let k1 := (W + 2) / 2 in
    let '(dx, dy, vmD) := lookupD dtab k1 in
    if (2 <=? k1) && negb (vmD =? 0) && (dx + 1 =? x) && (dy =? y) then
      let Wq := 2 * k1 - 3 + 2 * c in
      match lookupL ltab Wq (k1 - 1) with
      | Some (py, m) => if (vmD + 2 <=? m) && (2 * py <? Wq + 1) then Some (applyDeltaM cur (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc) else None
      | None => None
      end
    else None.

Definition exhaust01AddOnes (ltab : T8192 (T4096 LEnt)) (dtab : T4096 DEntry) (cur : Stalled) (c acc : N) : option StAcc :=
  match cur with
  | Se =>
    if c =? 1 then Some (mkStAcc Sone0 acc)
    else let '(dx, dy, vmD) := lookupD dtab c in if vmD =? 0 then None else Some (mkStAcc (Scanon1 dx dy (negb (N.odd vmD))) (acc + N.div2 vmD))
  | Sone0 =>
    let '(dx, dy, vmD) := lookupD dtab (c + 1) in if vmD =? 0 then None else Some (mkStAcc (Scanon1 dx dy (negb (N.odd vmD))) (acc + N.div2 vmD))
  | Sz1 =>
    let '(dx, dy, vmD) := lookupD dtab (c + 1) in if vmD =? 0 then None else Some (mkStAcc (ScanonZ dx dy) (acc + vmD))
  | ScanonZ x y =>
    if (x =? 1) && (y =? 0) then
      let '(dx, dy, vmD) := lookupD dtab (c + 2) in if vmD =? 0 then None else Some (mkStAcc (ScanonZ dx dy) (acc + (vmD - 1)))
    else
      match (if 2 <=? c then tryDirectCanon ltab dtab cur x y c acc else None) with
      | Some r => Some r
      | None => exhaust01LoopL ltab c cur acc
      end
  | Scanon1 x y _ =>
    match (if 2 <=? c then tryDirectCanon ltab dtab cur x y c acc else None) with
    | Some r => Some r
    | None => exhaust01LoopL ltab c cur acc
    end
  end.

Fixpoint exhaust01Fold (ltab : T8192 (T4096 LEnt)) (dtab : T4096 DEntry) (cur : Stalled) (seg : UList) (acc : N) : option StAcc :=
  match seg with
  | Unil => Some (mkStAcc cur acc)
  | Ucons u c tl =>
    if u =? 0 then exhaust01Fold ltab dtab (addZBot (c + 1) cur) tl acc
    else if u =? 1 then
      match exhaust01AddOnes ltab dtab cur (c + 1) acc with
      | Some r => exhaust01Fold ltab dtab (sa_st r) tl (sa_acc r)
      | None => None
      end
    else None
  end.

Fixpoint splitOnly01 (u : UList) : UList * UList :=
  match u with
  | Unil => (Unil, Unil)
  | Ucons x c tl =>
    if x <=? 1 then let '(p, r) := splitOnly01 tl in (Ucons x c p, r)
    else (Unil, u)
  end.

Definition exhaustBandStep (ltab : T8192 (T4096 LEnt)) (dtab : T4096 DEntry) (st : option (UList * N)) : StepRes (option (UList * N)) :=
  match st with
  | None => mkStepRes true None
  | Some (u, acc) =>
    let '(pref, rest) := splitOnly01 u in
    let step1 :=
      match pref with
      | Unil => Some (u, acc)
      | _ =>
        match exhaust01Fold ltab dtab Se pref acc with
        | Some r => Some (uappend (toU (sa_st r)) rest, sa_acc r)
        | None => None
        end
      end in
    match step1 with
    | None => mkStepRes true None
    | Some (u1, acc1) =>
      match rest with
      | Unil => mkStepRes true (Some (u1, acc1))
      | _ =>
        match ustepPsi u1 with
        | None => mkStepRes true (Some (u1, acc1))
        | Some u2 => mkStepRes false (Some (u2, acc1 + 1))
        end
      end
    end
  end.

Definition exhaustAnyBand (ltab : T8192 (T4096 LEnt)) (dtab : T4096 DEntry) (p : positive) (u : UList) (acc : N) : option (UList * N) :=
  sr_val (runPos p (exhaustBandStep ltab dtab) (Some (u, acc))).

Definition fast_ones (n : N) : N := N.iter n N.succ_double 0.
Definition mask_fast (k v : N) : N := if N.size v <=? k then v else N.land v (fast_ones k).

Record ScanRes := mkScan { sc_len : N; sc_val : N; sc_inf : bool; sc_rem : list LTok }.
Fixpoint scanLPairs_fuel (fuel : nat) (l : list LTok) : ScanRes :=
  match fuel with
  | O => mkScan 0 0 false l
  | S f =>
    match l with
    | [] => mkScan 0 0 true []
    | Lo _ :: _ => mkScan 0 0 false l
    | Lpairs len val :: rest =>
      let sc := scanLPairs_fuel f rest in
      let v' := mask_fast len val in
      mkScan (len + sc_len sc) (v' + N.shiftl (sc_val sc) len) (sc_inf sc) (sc_rem sc)
    | Lz k :: rest =>
      let c := k + 1 in
      if 2 <=? c then
        let p := N.div2 c in
        let l' := if N.odd c then Lz 0 :: rest else rest in
        let sc := scanLPairs_fuel f l' in
        mkScan (p + sc_len sc) (N.iter p N.succ_double (sc_val sc)) (sc_inf sc) (sc_rem sc)
      else
        match rest with
        | [] => mkScan 1 1 true []
        | Lo k2 :: rest2 =>
          let sc := scanLPairs_fuel f (if k2 =? 0 then rest2 else Lo (k2 - 1) :: rest2) in
          mkScan (1 + sc_len sc) (N.double (sc_val sc)) (sc_inf sc) (sc_rem sc)
        | Lz k2 :: rest2 =>
          scanLPairs_fuel f (Lz (k2 + 1) :: rest2)
        | Lpairs len2 v2 :: rest2 =>
          if len2 =? 0 then scanLPairs_fuel f (Lz 0 :: rest2)
          else
            let l' := lpushBit (negb (N.odd v2)) 1 (lpushPairs (len2 - 1) (N.div2 v2) rest2) in
            let sc := scanLPairs_fuel f l' in
            mkScan (1 + sc_len sc) (N.succ_double (sc_val sc)) (sc_inf sc) (sc_rem sc)
        end
    end
  end.
Definition scanLPairsCompact (l : list LTok) : ScanRes := scanLPairs_fuel 200%nat l.

Fixpoint pos_find_split (p : positive) (q : N) : N * N * N :=
  if q =? 0 then
    match p with
    | xH => (0, 0, 0)
    | xI p' => (0, 0, Npos p')
    | xO p' => let '(i, lo, hi) := pos_find_split p' 0 in (i + 1, N.double lo, hi)
    end
  else
    match p with
    | xH => (0, 0, 0)
    | xO p' =>
      let '(i, lo, hi) := pos_find_split p' (N.div2 q) in
      (i + 1, N.double lo, hi)
    | xI p' =>
      let q' := if N.odd q then N.div2 q else N.div2 q - 1 in
      let '(i, lo, hi) := pos_find_split p' q' in
      (i + 1, N.succ_double lo, hi)
    end.

Definition mD_exhaust_apply (sc : ScanRes) (mm : N) (r_rem : list RTok) (u_end : UList) (N_max : N) : option CoreState :=
  if mm <? 2 then None else
  let m0 := mm - 1 in
  let q := N.shiftr N_max m0 in
  let slen := sc_len sc in let sval := sc_val sc in
  if q <? sval then
    match sval with
    | N0 => None
    | Npos p =>
      let '(i_star, S_q, hi) := pos_find_split p q in
      if i_star <? slen then
        let R_rem := N_max - N.shiftl S_q m0 in
        let n_bits := m0 + i_star in
        let pval := N.succ_double (fast_ones n_bits - R_rem) in
        let l1 := lpushPairs (slen - i_star - 1) hi (sc_rem sc) in
        Some (Crun mA (lpushPairs (n_bits + 2) pval l1) (restoreUR u_end r_rem))
      else None
    end
  else if sc_inf sc then
    let p_len := N.shiftl 1 slen in
    let target := q - sval + p_len in
    let i_star := N.size target - 1 in
    let p_i := N.shiftl 1 i_star in
    let S_q := sval + (p_i - p_len) in
    if (slen <=? i_star) && (S_q <=? q) && (q <? S_q + p_i) then
      let R_rem := N_max - N.shiftl S_q m0 in
      let n_bits := m0 + i_star in
      let pval := N.succ_double (fast_ones n_bits - R_rem) in
      Some (Crun mA (lpushPairs (n_bits + 2) pval []) (restoreUR u_end r_rem))
    else None
  else None.

Fixpoint runPsiPos (p : positive) (u : UList) : option UList :=
  match p with
  | xH => ustepPsi u
  | xO q => match runPsiPos q u with Some u1 => runPsiPos q u1 | None => None end
  | xI q => match runPsiPos q u with Some u1 => match runPsiPos q u1 with Some u2 => ustepPsi u2 | None => None end | None => None end
  end.
Definition runPsi (n : N) (u : UList) : option UList :=
  match n with N0 => Some u | Npos p => runPsiPos p u end.

Definition stepMacro (ltab : T8192 (T4096 LEnt)) (dtab : T4096 DEntry) (s : CoreState) : CoreState :=
  match s with
  | Chalt l r => Chalt l r
  | Crun md l r =>
    match md with
    | mD =>
      match r with
      | [] => Crun mA (lpush1_1 l) []
      | Rz k :: rs =>
        if k =? 0 then
          match rs with
          | Rw01 w :: rs2 => Crun mD l (rpush1_2 (rpush0_1 (if w =? 0 then rs2 else Rw01 (w - 1) :: rs2)))
          | _ => Crun mA (lpush1_1 l) rs
          end
        else if k =? 1 then
          match rs with
          | Rw01 w :: rs2 => Crun mD (lpush1_n (2 * (w + 1)) l) (rpush0_2 rs2)
          | Ro o :: rs2 => Crun mD l (rpush1_2 (rpush0_1 (if o =? 0 then rs2 else Ro (o - 1) :: rs2)))
          | _ => Crun mA (lpush1_1 l) (Rz 0 :: rs)
          end
        else if k =? 2 then
          match rs with
          | Ro o :: rs2 => Crun mD (lpush1_2 l) (rpush0_2 (if o =? 0 then rs2 else Ro (o - 1) :: rs2))
          | _ => Crun mA (lpush1_1 l) (Rz 1 :: rs)
          end
        else Crun mA (lpush1_1 l) (Rz (k - 1) :: rs)
      | Rw01 k :: rs =>
        if k =? 0 then
          match rs with
          | Rz z0 :: Rw01 w0 :: Rw0111 w :: rs3 =>
            if (z0 =? 0) && (w0 =? 0) then Crun mA (lpush1_n (4 * (w + 1) + 1) l) (rpush1_1 (rpush0_2 (rpush1_1 rs3)))
            else Crun mA (lpush0_1 (lpush1_1 l)) rs
          | Ro o :: rs1 => Crun mA (lpush0 (o + 2) (lpush1_1 l)) rs1
          | _ => Crun mA (lpush0_1 (lpush1_1 l)) rs
          end
        else Crun mA (lpush0_1 (lpush1_1 l)) (Rw01 (k - 1) :: rs)
      | Rw0111 k :: rs =>
        if k =? 0 then
          match rs with
          | Ro o :: rs1 => Crun mA (lpush0 (o + 4) (lpush1_1 l)) rs1
          | _ => Crun mA (lpush0 3 (lpush1_1 l)) rs
          end
        else Crun mA (lpush0 3 (lpush1_1 l)) (Rw0111 (k - 1) :: rs)
      | Ro k :: rs =>
        if k =? 1 then
          match l with
          | [] => stepRLE_until_AD 100%positive (stepRLE s)
          | Lo lk :: ls =>
            if 3 <=? lk then Crun mD (lpushBit true ((lk + 1) mod 4) ls) (rpush1_2 (rpushW0111 ((lk + 1) / 4) rs))
            else if lk =? 2 then let lp := lpop1 ls in Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (rpushW0111_1 rs)))
            else if lk =? 0 then
              match ls with
              | Lz zk :: ls2 => Crun mD (if zk =? 0 then ls2 else Lz (zk - 1) :: ls2) (rpush0_2 (rpush1_2 rs))
              | _ => stepRLE_until_AD 100%positive (stepRLE s)
              end
            else stepRLE_until_AD 100%positive (stepRLE s)
          | Lpairs len val :: ls =>
            if 1 <=? len then
              let rest := if len =? 1 then ls else Lpairs (len - 1) (N.div2 val) :: ls in
              Crun mD rest (if N.odd val then rpushW0111_1 rs else rpush1_n 4 rs)
            else stepRLE_until_AD 100%positive (stepRLE s)
          | Lz zk :: ls =>
            if zk =? 0 then let lp := lpop1 ls in Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 rs))
            else Crun mD (if zk =? 1 then ls else Lz (zk - 2) :: ls) (rpushW0111_1 rs)
          end
        else if (3 <=? k) && ((k + 1) mod 2 =? 0) then
          let sc := scanLPairsCompact l in
          if (1 <=? sc_len sc) || sc_inf sc then
            let mm := (k + 1) / 2 in
            let up := extractUPrefixR rs in
            let us := up_u up in let r_rem := up_r up in
            match us with
            | Unil => stepRLE_until_AD 100%positive (stepRLE s)
            | _ =>
              if negb (sc_inf sc) && (sc_val sc =? 0) then
                Crun mD (sc_rem sc) (rpushBit true (2 * (mm + sc_len sc)) (restoreUR us r_rem))
              else if (if negb (sc_inf sc) && (mm - 1 <=? 10) then if sc_val sc <=? 1024 then N.shiftl (sc_val sc) (mm - 1) <=? 1024 else false else false) then
                match runPsi (N.shiftl (sc_val sc) (mm - 1)) us with
                | Some u_mid => Crun mD (sc_rem sc) (rpushBit true (2 * (mm + sc_len sc)) (restoreUR u_mid r_rem))
                | None =>
                  match exhaustAnyBand ltab dtab 10000%positive us 0 with
                  | Some (u_end, nmax) => match mD_exhaust_apply sc mm r_rem u_end nmax with Some s' => s' | None => s end
                  | None => s
                  end
                end
              else
                match exhaustAnyBand ltab dtab 10000%positive us 0 with
                | Some (u_end, nmax) => match mD_exhaust_apply sc mm r_rem u_end nmax with Some s' => s' | None => s end
                | None => s
                end
            end
          else stepRLE_until_AD 100%positive (stepRLE s)
        else stepRLE_until_AD 100%positive (stepRLE s)
      end
    | mA =>
      match r with
      | [] => stepRLE_until_AD 100%positive (stepRLE s)
      | Ro k :: rs =>
        if k =? 0 then
          match rs with
          | Rz z0 :: Rw01 w0 :: Rw0111 w :: rs3 =>
            if (z0 =? 0) && (w0 =? 0) then Crun mA (lpush1_n (4 * (w + 1)) l) (rpush1_1 (rpush0_2 (rpush1_1 rs3)))
            else if z0 =? 0 then
              let l1 := lpush0 1 l in Crun mD (if w0 =? 0 then lpush1_1 l1 else lpush1_n (2 * w0 + 1) l1) (rpush0_2 (Rw0111 w :: rs3))
            else Crun mA (lpush0 1 l) rs
          | Rz z0 :: Rw01 w :: rs2 =>
            if z0 =? 0 then
              let l1 := lpush0 1 l in Crun mD (if w =? 0 then lpush1_1 l1 else lpush1_n (2 * w + 1) l1) (rpush0_2 rs2)
            else Crun mA (lpush0 1 l) rs
          | _ => Crun mA (lpush0 1 l) rs
          end
        else
          let l1 := lpush0 (k + 1) l in
          match rs with
          | Rz z0 :: Rw01 w :: rs2 =>
            if z0 =? 0 then Crun mD (if w =? 0 then lpush1_1 l1 else lpush1_n (2 * w + 1) l1) (rpush0_2 rs2)
            else Crun mA l1 rs
          | _ => Crun mA l1 rs
          end
      | Rz k :: rs =>
        if k =? 0 then
          match rs with
          | Rw01 w :: rs1 => Crun mD (if w =? 0 then lpush1_1 l else lpush1_n (2 * w + 1) l) (rpush0_2 rs1)
          | Ro o :: rs1 =>
            let lp := lpop1 l in
            Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (rpush0_1 (if o =? 0 then rs1 else Ro (o - 1) :: rs1))))
          | _ => stepRLE_until_AD 100%positive (stepRLE s)
          end
        else if k =? 1 then
          match rs with
          | Ro o :: rs1 => Crun mD (lpush1_1 l) (rpush0_2 (if o =? 0 then rs1 else Ro (o - 1) :: rs1))
          | _ => stepRLE_until_AD 100%positive (stepRLE s)
          end
        else stepRLE_until_AD 100%positive (stepRLE s)
      | _ =>
        let early :=
          match r, l with
          | Rw01 w :: rs, Lo ok :: ls =>
            let rem_r := if w =? 0 then rs else Rw01 (w - 1) :: rs in
            Some (Crun mD (if ok =? 0 then ls else Lo (ok - 1) :: ls) (rpush1_2 (rpush0_1 rem_r)))
          | Rw01 _ :: _, [] => Some (stepRLE_until_AD 100%positive (stepRLE s))
          | Rw0111 _ :: _, [] => Some (stepRLE_until_AD 100%positive (stepRLE s))
          | Rw0111 _ :: _, Lo _ :: _ => Some (stepRLE_until_AD 100%positive (stepRLE s))
          | _, _ => None
          end in
        match early with
        | Some s' => s'
        | None =>
          let zr := lpopZRun l in
          let Z := zr_n zr in let l_tmp := zr_l zr in
          if 1 <=? Z then
            let up := extractUPrefixR r in
            let us := up_u up in let r_rem := up_r up in
            match ustepCore0 us with
            | None => stepRLE_until_AD 100%positive (stepRLE s)
            | Some (retB u1) =>
              if 3 <=? Z then
                let lp := lpop1 (lpushBit false (Z - 3) l_tmp) in
                Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR (upush 0 1 u1) r_rem)))
              else
                let lp := lpop1 (lpushBit false (Z - 1) l_tmp) in
                Crun mB (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u1 r_rem)))
            | Some (retD u1) =>
              let try2 :=
                if 3 <=? Z then
                  match ustepCore0 u1 with
                  | Some (retD u2) =>
                    let lp := lpop1 (lpushBit false (Z - 3) l_tmp) in
                    Some (Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u2 r_rem))))
                  | _ => None
                  end
                else None in
              match try2 with
              | Some s' => s'
              | None =>
                let lp := lpop1 (lpushBit false (Z - 1) l_tmp) in
                Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (restoreUR u1 r_rem)))
              end
            end
          else stepRLE_until_AD 100%positive (stepRLE s)
        end
      end
    | _ => stepRLE_until_AD 100%positive (stepRLE s)
    end
  end.

Definition stepMacro_step (ltab : T8192 (T4096 LEnt)) (dtab : T4096 DEntry) (s : CoreState) : StepRes CoreState :=
  match s with
  | Chalt l r => mkStepRes true (Chalt l r)
  | _ => mkStepRes false (stepMacro ltab dtab s)
  end.

Definition cert_check_fuel (fuel : positive) (dp : T8192 (T4096 LEnt) * T4096 DEntry) : bool :=
  let '(ltab, dtab) := dp in
  match sr_val (runPos fuel (stepMacro_step ltab dtab) (Crun mB [Lo 0] [])) with
  | Chalt _ _ => true
  | _ => false
  end.

Notation cert_check := (cert_check_fuel 1000000%positive init_and_run_dp).


(* ========================================================================= *)
(* Section 5b: Soundness of Lookup, Exhaustion, Scanner, Macro, and Halting  *)
(* ========================================================================= *)

Lemma lookupL_sound {ltab : T8192 (T4096 LEnt)} (hltab : t8_all (t4_all LEntValid) ltab)
  (W y py m : N) (h : lookupL ltab W y = Some (py, m)) :
  LCellSpec W y py m.
Proof.
  unfold lookupL in h; cbv zeta in h.
  destruct ((W <? 8192) && (y <? 4096)); [| discriminate].
  pose proof (get_t4_all (t8_get_all hltab W) (N_to_nib3 y)) as he.
  set (e := get_t4 (t8_get ltab W) (N_to_nib3 y)) in *; clearbody e.
  destruct (le_ok e && (le_W e =? W) && (le_y e =? y)) eqn:hok; [| discriminate].
  apply andb_prop in hok; destruct hok as [hok hy].
  apply andb_prop in hok; destruct hok as [hok hW].
  apply N.eqb_eq in hW; apply N.eqb_eq in hy.
  injection h as hpy hm; subst py m W y.
  exact (he hok).
Qed.

Lemma lookupD_sound {dtab : T4096 DEntry} (hdtab : t4_all DEntryValid dtab) (k : N) :
  let '(dx, dy, vmD) := lookupD dtab k in
  vmD <> 0 -> DValid k dx dy vmD.
Proof.
  unfold lookupD; cbv zeta.
  destruct (k <? 4096); [| intro hne; exfalso; exact (hne eq_refl)].
  pose proof (get_t4_all hdtab (N_to_nib3 k)) as he.
  set (e := get_t4 dtab (N_to_nib3 k)) in *; clearbody e.
  destruct (den_ok e && (den_k e =? k)) eqn:hok; [| intro hne; exfalso; exact (hne eq_refl)].
  apply andb_prop in hok; destruct hok as [hdok hdk].
  apply N.eqb_eq in hdk; subst k.
  intro; exact (he hdok).
Qed.

Lemma applyDeltaM_le (cur : Stalled) (nx ny dm acc : N) :
  acc <= sa_acc (applyDeltaM cur nx ny dm acc).
Proof.
  destruct cur as [| | | ? ? [|] | ? ?]; cbn [applyDeltaM sa_acc]; clear; lia.
Qed.

Lemma negb_odd_eq_mod2_0 (n : N) : negb (N.odd n) = (n mod 2 =? 0).
Proof.
  rewrite N_odd_eq.
  destruct (n mod 2 =? 1) eqn:h1.
  - apply N.eqb_eq in h1; rewrite h1; reflexivity.
  - apply N.eqb_neq in h1; assert (h0 : n mod 2 = 0) by (clear - h1; lia); rewrite h0; reflexivity.
Qed.

Lemma exhaust01StepL_sound {ltab : T8192 (T4096 LEnt)} (hltab : t8_all (t4_all LEntValid) ltab)
  (cur : Stalled) (acc : N) (r : StAcc)
  (hv : stValid cur)
  (h : exhaust01StepL ltab cur acc = Some r) :
  acc <= sa_acc r /\ stValid (sa_st r) /\
  PsiReach (sa_acc r - acc) (uappend (toU cur) (upush 1 1 Unil)) (toU (sa_st r)).
Proof.
  assert (hcur : exists x y,
            (cur = ScanonZ x y \/ exists p, cur = Scanon1 x y p) /\
            match lookupL ltab (x + 2 * y) y with
            | None => None
            | Some (py, m) => Some (applyDeltaM cur (x + 2 * y + 2 - 2 * py) py m acc)
            end = Some r).
  { destruct cur as [| | | x y p | x y]; try discriminate;
      [exists x, y; split; [right; exists p; reflexivity | exact h]
      | exists x, y; split; [left; reflexivity | exact h]]. }
  clear h; destruct hcur as [x [y [hcur h]]].
  destruct (lookupL ltab (x + 2 * y) y) as [[py m] |] eqn:hlk; [| discriminate].
  injection h as hr; subst r.
  pose proof (lookupL_sound hltab (x + 2 * y) y py m hlk) as hl.
  pose proof (LCellSpec_to_ZChain hl) as hzc.
  replace (x + 2 * y - 2 * y) with x in hzc by (clear; lia).
  assert (hpos : cur = Scanon1 x y false -> 1 <= m).
  { intro heq; subst cur; cbn [stValid] in hv.
    assert (hlt : 2 * y < x + 2 * y) by (clear - hv; lia).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 hl)) hlt))). }
  assert (hnx : 1 <= m -> 1 <= x + 2 * y + 2 - 2 * py).
  { intro hm1.
    destruct (2 * y =? x + 2 * y) eqn:heq.
    - apply N.eqb_eq in heq.
      destruct (proj1 (proj2 (proj2 hl)) heq) as [_ hm0]; clear - hm1 hm0; lia.
    - apply N.eqb_neq in heq. pose proof (proj1 hl) as hy.
      assert (hlt : 2 * y < x + 2 * y) by (clear - hy heq; lia).
      pose proof (proj1 (proj2 (proj2 (proj2 hl)) hlt)) as hpy1.
      clear - hpy1; lia. }
  pose proof (applyDeltaM_sound x y (x + 2 * y + 2 - 2 * py) py m acc cur (upush 1 1 Unil)
                hcur hv (only01_upush 1 1 Unil (N.le_refl 1) I) hpos hnx hzc) as [hv' hp].
  exact (conj (applyDeltaM_le cur _ _ _ acc) (conj hv' hp)).
Qed.

Lemma exhaust01LoopPos_sound {ltab : T8192 (T4096 LEnt)} (hltab : t8_all (t4_all LEntValid) ltab)
  (p : positive) :
  forall (cur : Stalled) (acc : N) (r : StAcc),
    stValid cur ->
    exhaust01LoopPos ltab p cur acc = Some r ->
    acc <= sa_acc r /\ stValid (sa_st r) /\
    PsiReach (sa_acc r - acc) (uappend (toU cur) (upush 1 (Npos p) Unil)) (toU (sa_st r)).
Proof.
  induction p as [q IH | q IH |]; intros cur acc r hv h; cbn [exhaust01LoopPos] in h.
  - destruct (exhaust01LoopPos ltab q cur acc) as [r1 |] eqn:h1; [| discriminate].
    destruct (exhaust01LoopPos ltab q (sa_st r1) (sa_acc r1)) as [r2 |] eqn:h2; [| discriminate].
    destruct (IH cur acc r1 hv h1) as [hle1 [hv1 hp1]].
    destruct (IH (sa_st r1) (sa_acc r1) r2 hv1 h2) as [hle2 [hv2 hp2]].
    destruct (exhaust01StepL_sound hltab (sa_st r2) (sa_acc r2) r hv2 h) as [hle3 [hv3 hp3]].
    pose proof (PsiReach_append hp2 (upush 1 1 Unil)) as hp2'.
    rewrite uappend_assoc in hp2'.
    pose proof (PsiReach_trans
                  (PsiReach_append hp1 (uappend (upush 1 (Npos q) Unil) (upush 1 1 Unil)))
                  (PsiReach_trans hp2' hp3)) as htot.
    rewrite !uappend_assoc, !uappend_upush in htot.
    repeat change (uappend Unil ?x) with x in htot.
    rewrite !upush_upush_same in htot.
    replace (Npos q + Npos q + 1) with (Npos (xI q)) in htot by (clear; lia).
    replace (sa_acc r1 - acc + (sa_acc r2 - sa_acc r1 + (sa_acc r - sa_acc r2)))
      with (sa_acc r - acc) in htot by (clear - hle1 hle2 hle3; lia).
    split; [clear - hle1 hle2 hle3; lia | exact (conj hv3 htot)].
  - destruct (exhaust01LoopPos ltab q cur acc) as [r1 |] eqn:h1; [| discriminate].
    destruct (IH cur acc r1 hv h1) as [hle1 [hv1 hp1]].
    destruct (IH (sa_st r1) (sa_acc r1) r hv1 h) as [hle2 [hv2 hp2]].
    pose proof (PsiReach_trans (PsiReach_append hp1 (upush 1 (Npos q) Unil)) hp2) as htot.
    rewrite uappend_assoc, uappend_upush in htot.
    change (uappend Unil ?x) with x in htot.
    rewrite upush_upush_same in htot.
    replace (Npos q + Npos q) with (Npos (xO q)) in htot by (clear; lia).
    replace (sa_acc r1 - acc + (sa_acc r - sa_acc r1))
      with (sa_acc r - acc) in htot by (clear - hle1 hle2; lia).
    split; [clear - hle1 hle2; lia | exact (conj hv2 htot)].
  - exact (exhaust01StepL_sound hltab cur acc r hv h).
Qed.

Lemma exhaust01LoopL_sound {ltab : T8192 (T4096 LEnt)} (hltab : t8_all (t4_all LEntValid) ltab)
  (c : N) (cur : Stalled) (acc : N) (r : StAcc)
  (hv : stValid cur)
  (h : exhaust01LoopL ltab c cur acc = Some r) :
  acc <= sa_acc r /\ stValid (sa_st r) /\
  PsiReach (sa_acc r - acc) (uappend (toU cur) (upush 1 c Unil)) (toU (sa_st r)).
Proof.
  destruct c as [| p]; cbn [exhaust01LoopL] in h.
  - injection h as hr; subst r; cbn [sa_acc sa_st].
    change (upush 1 0 Unil) with (@Unil).
    rewrite (proj2 (uappend_nil_r Unil) cur hv).
    replace (acc - acc) with 0 by (clear; lia).
    exact (conj (N.le_refl acc) (conj hv (PsiReach_refl (toU cur)))).
  - exact (exhaust01LoopPos_sound hltab p cur acc r hv h).
Qed.

Lemma tryDirectCanon_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (cur : Stalled) (x y c acc : N) (r : StAcc)
  (hcur : cur = ScanonZ x y \/ exists p, cur = Scanon1 x y p)
  (hv : stValid cur) (hc : 2 <= c)
  (h : tryDirectCanon ltab dtab cur x y c acc = Some r) :
  acc <= sa_acc r /\ stValid (sa_st r) /\
  PsiReach (sa_acc r - acc) (uappend (toU cur) (upush 1 c Unil)) (toU (sa_st r)).
Proof.
  unfold tryDirectCanon in h; cbv zeta in h.
  assert (h01_c : Only01 (upush 1 c Unil)) by exact (only01_upush 1 c Unil (N.le_refl 1) I).
  destruct ((x + 2 * y) mod 2 =? 1) eqn:hodd.
  - assert (hk2_branch :
      (let k2 := (x + 2 * y + 1) / 2 in
       let '(dx, dy, vmD) := lookupD dtab k2 in
       if (2 <=? k2) && (dx + 2 =? x) && (dy =? y) && negb (vmD =? 0) then
         let Wq := 2 * k2 - 2 + 2 * c in
         match lookupL ltab Wq (k2 - 2) with
         | Some (py, m) =>
           if 2 * py <? Wq + 1 then
             if vmD + 2 <=? m then Some (applyDeltaM cur (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc)
             else None
           else None
         | None => None
         end
       else None) = Some r ->
      acc <= sa_acc r /\ stValid (sa_st r) /\
      PsiReach (sa_acc r - acc) (uappend (toU cur) (upush 1 c Unil)) (toU (sa_st r))).
    { intro hk2; cbv zeta in hk2.
      set (k2 := (x + 2 * y + 1) / 2) in hk2; clearbody k2.
      pose proof (lookupD_sound hdtab k2) as hd_raw.
      destruct (lookupD dtab k2) as [[dx dy] vmD].
      destruct ((2 <=? k2) && (dx + 2 =? x) && (dy =? y) && negb (vmD =? 0)) eqn:hg; [| discriminate].
      apply andb_prop in hg; destruct hg as [hg hvm].
      apply andb_prop in hg; destruct hg as [hg hdy].
      apply andb_prop in hg; destruct hg as [hk2_ge hdx].
      apply N.leb_le in hk2_ge; apply N.eqb_eq in hdx; apply N.eqb_eq in hdy.
      assert (hvm_ne : vmD <> 0) by (intro he; subst vmD; discriminate).
      pose proof (hd_raw hvm_ne) as hd.
      set (Wq := 2 * k2 - 2 + 2 * c) in hk2.
      destruct (lookupL ltab Wq (k2 - 2)) as [[py m] |] eqn:hlk; [| discriminate].
      destruct (2 * py <? Wq + 1) eqn:hpy; [| discriminate].
      destruct (vmD + 2 <=? m) eqn:hm; [| discriminate].
      apply N.ltb_lt in hpy; apply N.leb_le in hm.
      injection hk2 as hr; subst r.
      pose proof (lookupL_sound hltab Wq (k2 - 2) py m hlk) as hl.
      replace Wq with (2 * k2 - 4 + 2 + 2 * c) in hl by (subst Wq; clear - hk2_ge; lia).
      assert (hm_gt : vmD + 1 <= m) by (clear - hm; lia).
      assert (hm_sub : 1 <= m - (vmD + 1)) by (clear - hm; lia).
      assert (hnx_pos : 1 <= Wq + 1 - 2 * py) by (clear - hpy; lia).
      pose proof (directOff12_sound (or_intror eq_refl) hc hm_gt hd hl) as hzc.
      rewrite hdx, hdy in hzc.
      replace (2 * k2 - 3 + 2 + 2 * c - 2 * py) with (Wq + 1 - 2 * py) in hzc by (subst Wq; clear - hk2_ge; lia).
      pose proof (applyDeltaM_sound x y (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc cur (upush 1 c Unil)
                    hcur hv h01_c (fun _ => hm_sub) (fun _ => hnx_pos) hzc) as [hv' hp].
      exact (conj (applyDeltaM_le cur _ _ _ acc) (conj hv' hp)). }
    set (k0 := (x + 2 * y + 3) / 2) in h; clearbody k0.
    pose proof (lookupD_sound hdtab k0) as hd1_raw.
    pose proof (lookupD_sound hdtab (k0 + c)) as hd2_raw.
    destruct (lookupD dtab k0) as [[dx1 dy1] m1].
    destruct (lookupD dtab (k0 + c)) as [[dx2 dy2] m2].
    destruct ((dx1 =? x) && (dy1 =? y) && negb (m1 =? 0) && negb (m2 =? 0)) eqn:hg0; [| exact (hk2_branch h)].
    destruct (m1 + 1 <=? m2) eqn:hm12; [| exact (hk2_branch h)].
    injection h as hr; subst r.
    apply andb_prop in hg0; destruct hg0 as [hg0 hm2_nz].
    apply andb_prop in hg0; destruct hg0 as [hg0 hm1_nz].
    apply andb_prop in hg0; destruct hg0 as [hdx1 hdy1].
    apply N.eqb_eq in hdx1; apply N.eqb_eq in hdy1; apply N.leb_le in hm12.
    assert (hm1_ne : m1 <> 0) by (intro he; subst m1; discriminate).
    assert (hm2_ne : m2 <> 0) by (intro he; subst m2; discriminate).
    pose proof (hd1_raw hm1_ne) as hd1.
    pose proof (hd2_raw hm2_ne) as hd2.
    assert (hc1 : 1 <= c) by (clear - hc; lia).
    assert (hm1_lt : m1 <= m2) by (clear - hm12; lia).
    assert (hm_sub : 1 <= m2 - m1) by (clear - hm12; lia).
    pose proof (directOff0_sound hc1 hm1_lt hd1 hd2) as hzc.
    rewrite hdx1, hdy1 in hzc.
    pose proof (applyDeltaM_sound x y dx2 dy2 (m2 - m1) acc cur (upush 1 c Unil)
                  hcur hv h01_c (fun _ => hm_sub) (fun _ => proj1 (proj2 hd2)) hzc) as [hv' hp].
    exact (conj (applyDeltaM_le cur _ _ _ acc) (conj hv' hp)).
  - set (k1 := (x + 2 * y + 2) / 2) in h; clearbody k1.
    pose proof (lookupD_sound hdtab k1) as hd_raw.
    destruct (lookupD dtab k1) as [[dx dy] vmD].
    destruct ((2 <=? k1) && negb (vmD =? 0) && (dx + 1 =? x) && (dy =? y)) eqn:hg; [| discriminate].
    apply andb_prop in hg; destruct hg as [hg hdy].
    apply andb_prop in hg; destruct hg as [hg hdx].
    apply andb_prop in hg; destruct hg as [hk1_ge hvm].
    apply N.leb_le in hk1_ge; apply N.eqb_eq in hdx; apply N.eqb_eq in hdy.
    assert (hvm_ne : vmD <> 0) by (intro he; subst vmD; discriminate).
    pose proof (hd_raw hvm_ne) as hd.
    set (Wq := 2 * k1 - 3 + 2 * c) in h.
    destruct (lookupL ltab Wq (k1 - 1)) as [[py m] |] eqn:hlk; [| discriminate].
    destruct ((vmD + 2 <=? m) && (2 * py <? Wq + 1)) eqn:hok; [| discriminate].
    apply andb_prop in hok; destruct hok as [hm hpy].
    apply N.leb_le in hm; apply N.ltb_lt in hpy.
    injection h as hr; subst r.
    pose proof (lookupL_sound hltab Wq (k1 - 1) py m hlk) as hl.
    replace Wq with (2 * k1 - 4 + 1 + 2 * c) in hl by (subst Wq; clear - hk1_ge; lia).
    assert (hm_gt : vmD + 1 <= m) by (clear - hm; lia).
    assert (hm_sub : 1 <= m - (vmD + 1)) by (clear - hm; lia).
    assert (hnx_pos : 1 <= Wq + 1 - 2 * py) by (clear - hpy; lia).
    pose proof (directOff12_sound (or_introl eq_refl) hc hm_gt hd hl) as hzc.
    rewrite hdx, hdy in hzc.
    replace (2 * k1 - 3 + 1 + 2 * c - 2 * py) with (Wq + 1 - 2 * py) in hzc by (subst Wq; clear - hk1_ge; lia).
    pose proof (applyDeltaM_sound x y (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc cur (upush 1 c Unil)
                  hcur hv h01_c (fun _ => hm_sub) (fun _ => hnx_pos) hzc) as [hv' hp].
    exact (conj (applyDeltaM_le cur _ _ _ acc) (conj hv' hp)).
Qed.

Lemma exhaust01AddOnes_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (cur : Stalled) (c acc : N) (r : StAcc)
  (hc : 1 <= c) (hv : stValid cur)
  (h : exhaust01AddOnes ltab dtab cur c acc = Some r) :
  acc <= sa_acc r /\ stValid (sa_st r) /\
  PsiReach (sa_acc r - acc) (uappend (toU cur) (upush 1 c Unil)) (toU (sa_st r)).
Proof.
  destruct cur as [| | | x y p | x y]; cbn [exhaust01AddOnes] in h.
  - destruct (c =? 1) eqn:hc1.
    + apply N.eqb_eq in hc1; subst c; injection h as hr; subst r; cbn [sa_acc sa_st toU uappend].
      replace (acc - acc) with 0 by (clear; lia).
      exact (conj (N.le_refl acc) (conj I (PsiReach_refl (upush 1 1 Unil)))).
    + pose proof (lookupD_sound hdtab c) as hd_raw.
      destruct (lookupD dtab c) as [[dx dy] vmD].
      destruct (vmD =? 0) eqn:hvm; [discriminate |].
      apply N.eqb_neq in hvm; pose proof (hd_raw hvm) as hd.
      injection h as hr; subst r; cbn [sa_acc sa_st].
      rewrite negb_odd_eq_mod2_0, N_div2_eq.
      destruct hd as [hc2 [hdx [_ [_ hzd]]]].
      assert (hst_v : stValid (Scanon1 dx dy (vmD mod 2 =? 0)))
        by (destruct (vmD mod 2 =? 0); [exact I | exact hdx]).
      replace (acc + vmD / 2 - acc) with (vmD / 2) by (clear; lia).
      cbn [toU uappend].
      replace (upush 1 c Unil) with (upush 1 1 (upush 1 (c - 1) Unil))
        by (rewrite upush_upush_same; f_equal; clear - hc; lia).
      split; [clear; lia | refine (conj hst_v _)].
      exact (ZChain_to_PsiReach_1 (only01_upush 1 (c - 1) Unil (N.le_refl 1) I) (fun _ => hdx) hzd).
  - pose proof (lookupD_sound hdtab (c + 1)) as hd_raw.
    destruct (lookupD dtab (c + 1)) as [[dx dy] vmD].
    destruct (vmD =? 0) eqn:hvm; [discriminate |].
    apply N.eqb_neq in hvm; pose proof (hd_raw hvm) as hd.
    injection h as hr; subst r; cbn [sa_acc sa_st].
    rewrite negb_odd_eq_mod2_0, N_div2_eq.
    destruct hd as [_ [hdx [_ [_ hzd]]]].
    assert (hst_v : stValid (Scanon1 dx dy (vmD mod 2 =? 0)))
      by (destruct (vmD mod 2 =? 0); [exact I | exact hdx]).
    replace (acc + vmD / 2 - acc) with (vmD / 2) by (clear; lia).
    cbn [toU]; rewrite uappend_upush; cbn [uappend].
    replace (c + 1 - 1) with c in hzd by (clear; lia).
    split; [clear; lia | refine (conj hst_v _)].
    exact (ZChain_to_PsiReach_1 (only01_upush 1 c Unil (N.le_refl 1) I) (fun _ => hdx) hzd).
  - pose proof (lookupD_sound hdtab (c + 1)) as hd_raw.
    destruct (lookupD dtab (c + 1)) as [[dx dy] vmD].
    destruct (vmD =? 0) eqn:hvm; [discriminate |].
    apply N.eqb_neq in hvm; pose proof (hd_raw hvm) as hd.
    injection h as hr; subst r; cbn [sa_acc sa_st].
    destruct hd as [_ [_ [_ [_ hzd]]]].
    replace (acc + vmD - acc) with vmD by (clear; lia).
    cbn [toU]; rewrite uappend_upush; cbn [uappend].
    replace (c + 1 - 1) with c in hzd by (clear; lia).
    split; [clear; lia | exact (conj I (ZChain_to_PsiReach_Z hzd))].
  - destruct (2 <=? c) eqn:hc2.
    + apply N.leb_le in hc2.
      destruct (tryDirectCanon ltab dtab (Scanon1 x y p) x y c acc) as [r' |] eqn:htr.
      * injection h as hr; subst r'.
        exact (tryDirectCanon_sound hltab hdtab (Scanon1 x y p) x y c acc r (or_intror (ex_intro _ p eq_refl)) hv hc2 htr).
      * exact (exhaust01LoopL_sound hltab c (Scanon1 x y p) acc r hv h).
    + exact (exhaust01LoopL_sound hltab c (Scanon1 x y p) acc r hv h).
  - destruct ((x =? 1) && (y =? 0)) eqn:h10.
    + apply andb_prop in h10; destruct h10 as [hx1 hy0].
      apply N.eqb_eq in hx1; apply N.eqb_eq in hy0; subst x y.
      pose proof (lookupD_sound hdtab (c + 2)) as hd_raw.
      destruct (lookupD dtab (c + 2)) as [[dx dy] vmD].
      destruct (vmD =? 0) eqn:hvm; [discriminate |].
      apply N.eqb_neq in hvm; pose proof (hd_raw hvm) as hd.
      injection h as hr; subst r; cbn [sa_acc sa_st].
      replace (c + 2) with (2 + c) in hd by (clear; lia).
      pose proof (directOff0_sound hc (proj1 (proj2 (proj2 (proj2 hd)))) DValid_base2 hd) as hzc.
      replace (acc + (vmD - 1) - acc) with (vmD - 1) by (clear; lia).
      cbn [toU]; rewrite uappend_upush.
      split; [clear; lia | exact (conj I (ZChain_to_PsiReach_Z hzc))].
    + destruct (2 <=? c) eqn:hc2.
      * apply N.leb_le in hc2.
        destruct (tryDirectCanon ltab dtab (ScanonZ x y) x y c acc) as [r' |] eqn:htr.
        -- injection h as hr; subst r'.
           exact (tryDirectCanon_sound hltab hdtab (ScanonZ x y) x y c acc r (or_introl eq_refl) hv hc2 htr).
        -- exact (exhaust01LoopL_sound hltab c (ScanonZ x y) acc r hv h).
      * exact (exhaust01LoopL_sound hltab c (ScanonZ x y) acc r hv h).
Qed.

Lemma exhaust01Fold_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (seg : UList) :
  forall (cur : Stalled) (acc : N) (r : StAcc),
    stValid cur ->
    exhaust01Fold ltab dtab cur seg acc = Some r ->
    acc <= sa_acc r /\ stValid (sa_st r) /\
    PsiReach (sa_acc r - acc) (uappend (toU cur) seg) (toU (sa_st r)).
Proof.
  induction seg as [| u c tl IH]; intros cur acc r hv h; cbn [exhaust01Fold] in h.
  - injection h as hr; subst r; cbn [sa_acc sa_st].
    rewrite (proj2 (uappend_nil_r Unil) cur hv).
    replace (acc - acc) with 0 by (clear; lia).
    exact (conj (N.le_refl acc) (conj hv (PsiReach_refl (toU cur)))).
  - destruct (u =? 0) eqn:hu0.
    + apply N.eqb_eq in hu0; subst u.
      destruct (IH (addZBot (c + 1) cur) acc r (stValid_addZBot (c + 1) cur hv) h) as [hle [hv' hp]].
      assert (heq : forall sr, encU (uappend (toU (addZBot (c + 1) cur)) tl) sr =
                               encU (uappend (toU cur) (Ucons 0 c tl)) sr).
      { intro sr. rewrite <- (toU_addZBot (c + 1) cur hv), !encU_uappend, encU_upush; reflexivity. }
      exact (conj hle (conj hv' (PsiReach_congr heq (fun _ => eq_refl) hp))).
    + destruct (u =? 1) eqn:hu1; [| discriminate].
      apply N.eqb_eq in hu1; subst u.
      destruct (exhaust01AddOnes ltab dtab cur (c + 1) acc) as [r1 |] eqn:h1; [| discriminate].
      destruct (exhaust01AddOnes_sound hltab hdtab cur (c + 1) acc r1 ltac:(clear; lia) hv h1) as [hle1 [hv1 hp1]].
      destruct (IH (sa_st r1) (sa_acc r1) r hv1 h) as [hle2 [hv2 hp2]].
      pose proof (PsiReach_trans (PsiReach_append hp1 tl) hp2) as htot.
      replace (sa_acc r1 - acc + (sa_acc r - sa_acc r1)) with (sa_acc r - acc) in htot by (clear - hle1 hle2; lia).
      assert (heq : forall sr, encU (uappend (uappend (toU cur) (upush 1 (c + 1) Unil)) tl) sr =
                               encU (uappend (toU cur) (Ucons 1 c tl)) sr).
      { intro sr. rewrite !encU_uappend, encU_upush; reflexivity. }
      split; [clear - hle1 hle2; lia | exact (conj hv2 (PsiReach_congr heq (fun _ => eq_refl) htot))].
Qed.

Lemma encU_splitOnly01 (u : UList) (sr : side) :
  encU (uappend (fst (splitOnly01 u)) (snd (splitOnly01 u))) sr = encU u sr.
Proof.
  induction u as [| x c tl IH]; [reflexivity |].
  cbn [splitOnly01].
  destruct (x <=? 1).
  - destruct (splitOnly01 tl) as [p r]; cbn [fst snd uappend encU] in *.
    rewrite encU_upush, IH; reflexivity.
  - reflexivity.
Qed.

Definition BandRel (s1 s2 : option (UList * N)) : Prop :=
  (s1 = None -> s2 = None) /\
  (forall u1 a1 u2 a2, s1 = Some (u1, a1) -> s2 = Some (u2, a2) ->
     a1 <= a2 /\ PsiReach (a2 - a1) u1 u2).

Lemma BandRel_trans (x y z : option (UList * N)) (hxy : BandRel x y) (hyz : BandRel y z) :
  BandRel x z.
Proof.
  split.
  - intro hx; exact (proj1 hyz (proj1 hxy hx)).
  - intros u1 a1 u3 a3 hx hz.
    destruct y as [[u2 a2] |].
    + destruct (proj2 hxy u1 a1 u2 a2 hx eq_refl) as [hle1 hp1].
      destruct (proj2 hyz u2 a2 u3 a3 eq_refl hz) as [hle2 hp2].
      pose proof (PsiReach_trans hp1 hp2) as htot.
      replace (a2 - a1 + (a3 - a2)) with (a3 - a1) in htot by (clear - hle1 hle2; lia).
      split; [clear - hle1 hle2; lia | exact htot].
    + pose proof (proj1 hyz eq_refl) as hz_none; rewrite hz_none in hz; discriminate.
Qed.

Lemma exhaustBandStep_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (st : option (UList * N)) :
  BandRel st (sr_val (exhaustBandStep ltab dtab st)).
Proof.
  destruct st as [[u acc] |]; [| split; [exact (fun _ => eq_refl) | intros ? ? ? ? h; discriminate]].
  split; [intro h; discriminate |].
  intros u_in a_in u_out a_out hin hout.
  injection hin as <- <-.
  unfold exhaustBandStep in hout; cbv zeta in hout.
  pose proof (encU_splitOnly01 u) as hsplit.
  destruct (splitOnly01 u) as [pref rest]; cbn [fst snd] in hsplit.
  assert (hstep1 : forall step1 : option (UList * N),
            (forall u1 acc1, step1 = Some (u1, acc1) -> acc <= acc1 /\ PsiReach (acc1 - acc) u u1) ->
            sr_val match step1 with
                   | None => mkStepRes true None
                   | Some (u1, acc1) =>
                     match rest with
                     | Unil => mkStepRes true (Some (u1, acc1))
                     | _ =>
                       match ustepPsi u1 with
                       | None => mkStepRes true (Some (u1, acc1))
                       | Some u2 => mkStepRes false (Some (u2, acc1 + 1))
                       end
                     end
                   end = Some (u_out, a_out) ->
            acc <= a_out /\ PsiReach (a_out - acc) u u_out).
  { intros [ [u1 acc1] |] hs1 hm; [| discriminate].
    destruct (hs1 u1 acc1 eq_refl) as [hle1 hp1].
    destruct rest as [| rx rc rtl].
    - cbn [sr_val] in hm; injection hm as <- <-; exact (conj hle1 hp1).
    - destruct (ustepPsi u1) as [u2 |] eqn:hpsi; cbn [sr_val] in hm; injection hm as <- <-.
      + pose proof (PsiReach_trans hp1 (PsiReach_step (ustepPsi_sound u1 u2 hpsi))) as htot.
        replace (acc1 - acc + 1) with (acc1 + 1 - acc) in htot by (clear - hle1; lia).
        split; [clear - hle1; lia | exact htot].
      + exact (conj hle1 hp1). }
  refine (hstep1 _ _ hout).
  intros u1 acc1 hs1.
  destruct pref as [| px pc ptl].
  - injection hs1 as <- <-; replace (acc - acc) with 0 by (clear; lia).
    exact (conj (N.le_refl acc) (PsiReach_refl u)).
  - destruct (exhaust01Fold ltab dtab Se (Ucons px pc ptl) acc) as [r |] eqn:hf; [| discriminate].
    injection hs1 as <- <-.
    destruct (exhaust01Fold_sound hltab hdtab (Ucons px pc ptl) Se acc r I hf) as [hle1 [_ hp1]].
    cbn [toU uappend] in hp1.
    pose proof (PsiReach_append hp1 rest) as hp1'.
    exact (conj hle1 (PsiReach_congr hsplit (fun _ => eq_refl) hp1')).
Qed.

Lemma exhaustAnyBand_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (p : positive) (u u_out : UList) (acc acc_out : N)
  (h : exhaustAnyBand ltab dtab p u acc = Some (u_out, acc_out)) :
  acc <= acc_out /\ PsiReach (acc_out - acc) u u_out.
Proof.
  pose proof (runPos_rel BandRel BandRel_trans (exhaustBandStep ltab dtab)
                (exhaustBandStep_sound hltab hdtab) p (Some (u, acc))) as hrel.
  exact (proj2 hrel u acc u_out acc_out eq_refl h).
Qed.

(* Scanner and Split Soundness *)
Lemma iter_succ_double (p hi : N) :
  N.iter p N.succ_double hi = (2 ^ p - 1) + hi * 2 ^ p.
Proof.
  nind p; [cbn; lia |].
  rewrite N_iter_succ_r, IH, N.succ_double_spec, pow2_succ.
  pose proof (pow2_pos p) as hp.
  set (pw := 2 ^ p) in *; clearbody pw; nia.
Qed.

Lemma fast_ones_eq (n : N) : fast_ones n = 2 ^ n - 1.
Proof.
  unfold fast_ones; rewrite iter_succ_double; clear; lia.
Qed.

Lemma pos_lt_pow2_size (p : positive) : Npos p < 2 ^ N.pos (Pos.size p).
Proof.
  induction p as [q IH | q IH |]; cbn [Pos.size].
  - replace (N.pos (Pos.succ (Pos.size q))) with (N.pos (Pos.size q) + 1) by (clear; lia).
    rewrite pow2_succ; change (Npos (xI q)) with (2 * Npos q + 1); clear - IH; lia.
  - replace (N.pos (Pos.succ (Pos.size q))) with (N.pos (Pos.size q) + 1) by (clear; lia).
    rewrite pow2_succ; change (Npos (xO q)) with (2 * Npos q); clear - IH; lia.
  - change (2 ^ 1) with 2; clear; lia.
Qed.

Lemma N_lt_pow2_size (v : N) : v < 2 ^ N.size v.
Proof.
  destruct v as [| p]; [change (2 ^ 0) with 1; clear; lia | exact (pos_lt_pow2_size p)].
Qed.

Lemma mask_fast_spec (k v : N) :
  mask_fast k v < 2 ^ k /\
  (forall sl, encPairs k (mask_fast k v) sl = encPairs k v sl).
Proof.
  unfold mask_fast.
  destruct (N.size v <=? k) eqn:hsz.
  - apply N.leb_le in hsz.
    pose proof (N_lt_pow2_size v) as hv.
    pose proof (pow2_mono (N.size v) k hsz) as hpm.
    split; [clear - hv hpm; lia | intro; reflexivity].
  - assert (ho : fast_ones k = N.ones k).
    { rewrite fast_ones_eq; unfold N.ones; rewrite N.shiftl_1_l; clear; lia. }
    rewrite ho; fold (maskPow2 k v).
    exact (conj (maskPow2_lt k v) (encPairs_maskPow2 k v)).
Qed.

Lemma mul_pow2_add_lt (a b l1 l2 : N) (ha : a < 2 ^ l1) (hb : b < 2 ^ l2) :
  a + b * 2 ^ l1 < 2 ^ (l1 + l2).
Proof.
  rewrite N.pow_add_r.
  set (p1 := 2 ^ l1) in *; set (p2 := 2 ^ l2) in *; clearbody p1 p2; nia.
Qed.

Lemma scanLPairs_fuel_sound (fuel : nat) :
  forall l : list LTok,
    let sc := scanLPairs_fuel fuel l in
    sc_val sc < 2 ^ sc_len sc /\
    encL l = encPairs (sc_len sc) (sc_val sc) (encL (sc_rem sc)) /\
    (sc_inf sc = true -> sc_rem sc = []).
Proof.
  induction fuel as [| f IH]; intro l; cbn [scanLPairs_fuel].
  - cbn [sc_len sc_val sc_inf sc_rem encPairs N.to_nat]; change (2 ^ 0) with 1.
    split; [clear; lia | split; [reflexivity | intro; discriminate]].
  - destruct l as [| [k | k | len val] rest].
    + cbn [sc_len sc_val sc_inf sc_rem encPairs N.to_nat]; change (2 ^ 0) with 1.
      split; [clear; lia | split; [reflexivity | intro; reflexivity]].
    + destruct (2 <=? k + 1) eqn:hc2.
      * apply N.leb_le in hc2.
        set (p := N.div2 (k + 1)).
        set (l' := if N.odd (k + 1) then Lz 0 :: rest else rest).
        destruct (IH l') as [hval [henc hinf]]; cbv zeta.
        set (sc := scanLPairs_fuel f l') in *.
        cbn [sc_len sc_val sc_inf sc_rem].
        rewrite iter_succ_double.
        pose proof (pow2_pos p) as hp_pos.
        assert (hlt1 : 2 ^ p - 1 < 2 ^ p) by (clear - hp_pos; lia).
        split; [exact (mul_pow2_add_lt (2 ^ p - 1) (sc_val sc) p (sc_len sc) hlt1 hval) |].
        split; [| exact hinf].
        rewrite (encPairs_add p (sc_len sc) (2 ^ p - 1) (sc_val sc) _ hlt1), <- henc, encPairs_all_ones.
        cbn [encL]; unfold l', p; rewrite N_div2_eq, N_odd_eq.
        destruct ((k + 1) mod 2 =? 1) eqn:hodd.
        -- apply N.eqb_eq in hodd; cbn [encL repBit N.iter Pos.iter bitSym].
           replace (k + 1) with (2 * ((k + 1) / 2) + 1) at 1 by (clear - hodd; lia).
           rewrite (repBit_add false (2 * ((k + 1) / 2)) 1); reflexivity.
        -- apply N.eqb_neq in hodd.
           replace (k + 1) with (2 * ((k + 1) / 2)) at 1 by (clear - hodd; lia); reflexivity.
      * apply N.leb_gt in hc2; assert (k = 0) by (clear - hc2; lia); subst k.
        destruct rest as [| [k2 | k2 | len2 v2] rest2].
        -- cbn [sc_len sc_val sc_inf sc_rem encL]; change (2 ^ 1) with 2.
           split; [clear; lia | split; [| intro; reflexivity]].
           change (repBit false (0 + 1) ?s) with (S0 >> s).
           change (encPairs 1 1 ?s) with (S0 >> S0 >> s).
           f_equal; apply default_eq_cons_zero.
        -- assert (heq : encL (Lz 0 :: Lz k2 :: rest2) = encL (Lz (k2 + 1) :: rest2)).
           { cbn [encL]; rewrite <- repBit_add; f_equal; clear; lia. }
           destruct (IH (Lz (k2 + 1) :: rest2)) as [hv [he hi]].
           rewrite heq; exact (conj hv (conj he hi)).
        -- set (l' := if k2 =? 0 then rest2 else Lo (k2 - 1) :: rest2).
           destruct (IH l') as [hv [he hi]]; cbv zeta.
           set (sc := scanLPairs_fuel f l') in *.
           cbn [sc_len sc_val sc_inf sc_rem].
           rewrite N.double_spec.
           assert (h0lt : 0 < 2 ^ 1) by (change (2 ^ 1) with 2; clear; lia).
           replace (2 * sc_val sc) with (0 + sc_val sc * 2 ^ 1) by (change (2 ^ 1) with 2; clear; lia).
           split; [exact (mul_pow2_add_lt 0 (sc_val sc) 1 (sc_len sc) h0lt hv) |].
           split; [| exact hi].
           rewrite (encPairs_add 1 (sc_len sc) 0 (sc_val sc) _ h0lt), <- he.
           cbn [encL]; change (repBit false (0 + 1) ?s) with (S0 >> s);
             change (encPairs 1 0 ?s) with (S0 >> S1 >> s).
           rewrite repBit_succ; cbn [bitSym].
           f_equal; f_equal; unfold l'; destruct (k2 =? 0) eqn:hk2.
           ++ apply N.eqb_eq in hk2; subst k2; reflexivity.
           ++ apply N.eqb_neq in hk2; cbn [encL].
              replace (k2 - 1 + 1) with k2 by (clear - hk2; lia); reflexivity.
        -- destruct (len2 =? 0) eqn:hlen2.
           ++ apply N.eqb_eq in hlen2; subst len2.
              destruct (IH (Lz 0 :: rest2)) as [hv [he hi]].
              exact (conj hv (conj he hi)).
           ++ apply N.eqb_neq in hlen2.
              set (l' := lpushBit (negb (N.odd v2)) 1 (lpushPairs (len2 - 1) (N.div2 v2) rest2)).
              destruct (IH l') as [hv [he hi]]; cbv zeta.
              set (sc := scanLPairs_fuel f l') in *.
              cbn [sc_len sc_val sc_inf sc_rem].
              rewrite N.succ_double_spec.
              assert (h1lt : 1 < 2 ^ 1) by (change (2 ^ 1) with 2; clear; lia).
              replace (2 * sc_val sc + 1) with (1 + sc_val sc * 2 ^ 1) by (change (2 ^ 1) with 2; clear; lia).
              split; [exact (mul_pow2_add_lt 1 (sc_val sc) 1 (sc_len sc) h1lt hv) |].
              split; [| exact hi].
              rewrite (encPairs_add 1 (sc_len sc) 1 (sc_val sc) _ h1lt), <- he.
              cbn [encL]; change (repBit false (0 + 1) ?s) with (S0 >> s);
                change (encPairs 1 1 ?s) with (S0 >> S0 >> s).
              f_equal.
              replace len2 with ((len2 - 1) + 1) at 1 by (clear - hlen2; lia).
              rewrite encPairs_succ.
              unfold l'; rewrite encL_lpushBit, encL_lpushPairs, N_div2_eq, N_odd_eq.
              change (repBit ?b 1 ?x) with (bitSym b >> x).
              destruct (v2 mod 2 =? 1); reflexivity.
    + cbn [sc_len sc_val sc_inf sc_rem encPairs N.to_nat]; change (2 ^ 0) with 1.
      split; [clear; lia | split; [reflexivity | intro; discriminate]].
    + destruct (IH rest) as [hv [he hi]]; cbv zeta.
      set (sc := scanLPairs_fuel f rest) in *.
      destruct (mask_fast_spec len val) as [hmlt hmeq].
      set (v' := mask_fast len val) in *.
      cbn [sc_len sc_val sc_inf sc_rem].
      rewrite N.shiftl_mul_pow2.
      split; [exact (mul_pow2_add_lt v' (sc_val sc) len (sc_len sc) hmlt hv) |].
      split; [| exact hi].
      rewrite (encPairs_add len (sc_len sc) v' (sc_val sc) _ hmlt), <- he, hmeq.
      reflexivity.
Qed.

Lemma scanLPairsCompact_sound (l : list LTok) :
  sc_val (scanLPairsCompact l) < 2 ^ sc_len (scanLPairsCompact l) /\
  encL l = encPairs (sc_len (scanLPairsCompact l)) (sc_val (scanLPairsCompact l)) (encL (sc_rem (scanLPairsCompact l))) /\
  (sc_inf (scanLPairsCompact l) = true -> sc_rem (scanLPairsCompact l) = []).
Proof. exact (scanLPairs_fuel_sound 200%nat l). Qed.

Lemma pos_find_split_spec (p : positive) :
  forall (q : N),
    q < Npos p ->
    let '(i, lo, hi) := pos_find_split p q in
    lo < 2 ^ i /\ lo <= q /\ q < lo + 2 ^ i /\
    Npos p = lo + 2 ^ i + hi * 2 ^ (i + 1).
Proof.
  induction p as [p' IH | p' IH |]; intros q hlt; cbn [pos_find_split].
  - change (Npos (xI p')) with (2 * Npos p' + 1) in hlt |- *.
    destruct (q =? 0) eqn:hq0.
    + apply N.eqb_eq in hq0; subst q; change (2 ^ 0) with 1; change (2 ^ (0 + 1)) with 2.
      clear; lia.
    + apply N.eqb_neq in hq0.
      set (q' := if N.odd q then N.div2 q else N.div2 q - 1).
      assert (hq'_lt : q' < Npos p').
      { unfold q'; rewrite N_div2_eq, N_odd_eq.
        destruct (q mod 2 =? 1) eqn:ho; [apply N.eqb_eq in ho | apply N.eqb_neq in ho];
          clear - hlt hq0 ho; lia. }
      pose proof (IH q' hq'_lt) as ih.
      destruct (pos_find_split p' q') as [[i lo] hi].
      destruct ih as [hlo [hle [hub hdecomp]]].
      rewrite N.succ_double_spec, pow2_succ, (pow2_succ (i + 1)).
      assert (hq_bounds : 2 * lo + 1 <= q /\ q < 2 * lo + 1 + 2 * 2 ^ i).
      { unfold q' in hle, hub; rewrite N_div2_eq, N_odd_eq in hle, hub.
        destruct (q mod 2 =? 1) eqn:ho; [apply N.eqb_eq in ho | apply N.eqb_neq in ho];
          (assert (hqd : q = 2 * (q / 2) + q mod 2) by (clear; lia));
          (set (qh := q / 2) in *; clearbody qh; set (pi := 2 ^ i) in *; clearbody pi; clear - hq0 ho hqd hle hub; lia). }
      destruct hq_bounds as [hb1 hb2].
      split; [clear - hlo; lia | split; [exact hb1 | split; [exact hb2 |]]].
      set (pi := 2 ^ i) in *; clearbody pi; clear - hdecomp; nia.
  - change (Npos (xO p')) with (2 * Npos p') in hlt |- *.
    assert (heq_call :
              (if q =? 0 then let '(i, lo, hi) := pos_find_split p' 0 in (i + 1, N.double lo, hi)
               else let '(i, lo, hi) := pos_find_split p' (N.div2 q) in (i + 1, N.double lo, hi)) =
              (let '(i, lo, hi) := pos_find_split p' (N.div2 q) in (i + 1, N.double lo, hi))).
    { destruct (q =? 0) eqn:hq0; [apply N.eqb_eq in hq0; subst q; reflexivity | reflexivity]. }
    rewrite heq_call; clear heq_call.
    assert (hq'_lt : N.div2 q < Npos p') by (rewrite N_div2_eq; clear - hlt; lia).
    pose proof (IH (N.div2 q) hq'_lt) as ih.
    destruct (pos_find_split p' (N.div2 q)) as [[i lo] hi].
    destruct ih as [hlo [hle [hub hdecomp]]].
    rewrite N.double_spec, pow2_succ, (pow2_succ (i + 1)).
    rewrite N_div2_eq in hle, hub.
    assert (hq_bounds : 2 * lo <= q /\ q < 2 * lo + 2 * 2 ^ i).
    { assert (hqd : 2 * (q / 2) <= q /\ q <= 2 * (q / 2) + 1) by (clear; lia).
      set (qh := q / 2) in *; clearbody qh; set (pi := 2 ^ i) in *; clearbody pi; clear - hqd hle hub; lia. }
    destruct hq_bounds as [hb1 hb2].
    split; [clear - hlo; lia | split; [exact hb1 | split; [exact hb2 |]]].
    set (pi := 2 ^ i) in *; clearbody pi; clear - hdecomp; nia.
  - change (Npos 1) with 1 in hlt |- *.
    assert (q = 0) by (clear - hlt; lia); subst q; cbn [N.eqb]; change (2 ^ 0) with 1; change (2 ^ 1) with 2.
    clear; lia.
Qed.

Lemma div_pow2_bounds (N_max m0 S_q i_star : N)
  (hSq_le : S_q <= N_max / 2 ^ m0)
  (hq_ub : N_max / 2 ^ m0 < S_q + 2 ^ i_star) :
  S_q * 2 ^ m0 <= N_max /\
  N_max - S_q * 2 ^ m0 < 2 ^ (m0 + i_star).
Proof.
  pose proof (pow2_pos m0) as hpm_pos.
  rewrite N.pow_add_r.
  assert (hdiv_mod : N_max = 2 ^ m0 * (N_max / 2 ^ m0) + N_max mod 2 ^ m0)
    by (apply N.div_mod; clear - hpm_pos; lia).
  assert (hmod_lt : N_max mod 2 ^ m0 < 2 ^ m0)
    by (apply N.mod_lt; clear - hpm_pos; lia).
  set (q := N_max / 2 ^ m0) in *; set (rm := N_max mod 2 ^ m0) in *;
    set (pm := 2 ^ m0) in *; set (pi := 2 ^ i_star) in *.
  clearbody q rm pm pi.
  clear - hSq_le hq_ub hpm_pos hdiv_mod hmod_lt; nia.
Qed.

Lemma mD_exhaust_apply_sound (l : list LTok) (sc : ScanRes) (mm : N) (r_rem : list RTok)
  (us u_end : UList) (N_max : N) (s_out : CoreState)
  (hval_lt : sc_val sc < 2 ^ sc_len sc)
  (hencL : encL l = encPairs (sc_len sc) (sc_val sc) (encL (sc_rem sc)))
  (hinf_rem : sc_inf sc = true -> sc_rem sc = [])
  (hp : PsiReach N_max us u_end)
  (h : mD_exhaust_apply sc mm r_rem u_end N_max = Some s_out) :
  ((encL l) {{D}}> repBit true (2 * mm) (encU us (encR r_rem))) -[ tm ]->* encodeCore s_out.
Proof.
  unfold mD_exhaust_apply in h; cbv zeta in h.
  destruct (mm <? 2) eqn:hmm; [discriminate |].
  apply N.ltb_ge in hmm.
  set (m0 := mm - 1) in *.
  rewrite N.shiftr_div_pow2 in h.
  set (q := N_max / 2 ^ m0) in *.
  destruct (q <? sc_val sc) eqn:hq_lt.
  - apply N.ltb_lt in hq_lt.
    destruct (sc_val sc) as [| p] eqn:hsval; [discriminate |].
    pose proof (pos_find_split_spec p q hq_lt) as hsp.
    destruct (pos_find_split p q) as [[i_star S_q] hi].
    destruct hsp as [hSq_lt [hSq_le [hq_ub hdecomp]]].
    destruct (i_star <? sc_len sc) eqn:hi_lt; [| discriminate].
    apply N.ltb_lt in hi_lt.
    injection h as hs; subst s_out.
    rewrite N.shiftl_mul_pow2, N.succ_double_spec, fast_ones_eq.
    destruct (div_pow2_bounds N_max m0 S_q i_star hSq_le hq_ub) as [hprod_le hR_lt].
    set (R_rem := N_max - S_q * 2 ^ m0) in *.
    set (n_bits := m0 + i_star) in *.
    assert (hN_eq : N_max = S_q * 2 ^ m0 + R_rem) by (subst R_rem; clear - hprod_le; lia).
    rewrite hN_eq in hp.
    destruct (PsiReach_split (S_q * 2 ^ m0) R_rem hp) as [u_mid [hp1 hp2]].
    set (l1 := lpushPairs (sc_len sc - i_star - 1) hi (sc_rem sc)).
    assert (hL_split : encL l = encPairs i_star S_q (S0 >> S0 >> encL l1)).
    { rewrite hencL.
      replace (sc_len sc) with (i_star + ((sc_len sc - i_star - 1) + 1)) by (clear - hi_lt; lia).
      assert (hp_eq : Npos p = S_q + (2 * hi + 1) * 2 ^ i_star).
      { rewrite pow2_succ in hdecomp; set (pi := 2 ^ i_star) in *; clearbody pi; clear - hdecomp; nia. }
      rewrite hp_eq, (encPairs_add i_star ((sc_len sc - i_star - 1) + 1) S_q (2 * hi + 1) _ hSq_lt).
      apply (f_equal (encPairs i_star S_q)).
      rewrite encPairs_succ, mod2_odd, div2_odd; cbn [N.eqb].
      unfold l1; rewrite encL_lpushPairs; reflexivity. }
    rewrite hL_split.
    replace (2 * mm) with (2 * (m0 + 1)) by (subst m0; clear - hmm; lia).
    eapply rs_trans; [exact (mD_pairs_sweep_sound i_star S_q m0 hSq_lt hp1 (S0 >> S0 >> encL l1) (encR r_rem)) |].
    replace (2 * (m0 + 1 + i_star)) with (2 * n_bits + 2) by (subst n_bits; clear; lia).
    cbn [encodeCore]; rewrite encL_lpushPairs, encR_restoreUR.
    replace (2 * (2 ^ n_bits - 1 - R_rem) + 1) with (1 + 2 * (2 ^ n_bits - 1 - R_rem)) by (clear; lia).
    exact (mD_exhaust_cascade_sound n_bits R_rem hR_lt hp2 (encL l1) (encR r_rem)).
  - destruct (sc_inf sc) eqn:hinf; [| discriminate].
    set (i_star := N.size (q - sc_val sc + N.shiftl 1 (sc_len sc)) - 1) in h; clearbody i_star.
    rewrite !N.shiftl_1_l in h.
    set (S_q := sc_val sc + (2 ^ i_star - 2 ^ sc_len sc)) in h.
    destruct ((sc_len sc <=? i_star) && (S_q <=? q) && (q <? S_q + 2 ^ i_star)) eqn:hok2; [| discriminate].
    apply andb_prop in hok2; destruct hok2 as [hok2 hq_ub].
    apply andb_prop in hok2; destruct hok2 as [hlen_le hSq_le].
    apply N.leb_le in hlen_le; apply N.leb_le in hSq_le; apply N.ltb_lt in hq_ub.
    injection h as hs; subst s_out.
    rewrite N.shiftl_mul_pow2, N.succ_double_spec, fast_ones_eq.
    pose proof (pow2_mono (sc_len sc) i_star hlen_le) as hpow_le.
    assert (hSq_lt : S_q < 2 ^ i_star) by (subst S_q; clear - hval_lt hpow_le; lia).
    destruct (div_pow2_bounds N_max m0 S_q i_star hSq_le hq_ub) as [hprod_le hR_lt].
    set (R_rem := N_max - S_q * 2 ^ m0) in *.
    set (n_bits := m0 + i_star) in *.
    assert (hN_eq : N_max = S_q * 2 ^ m0 + R_rem) by (subst R_rem; clear - hprod_le; lia).
    rewrite hN_eq in hp.
    destruct (PsiReach_split (S_q * 2 ^ m0) R_rem hp) as [u_mid [hp1 hp2]].
    assert (hL_split : encL l = encPairs i_star S_q (S0 >> S0 >> const S0)).
    { rewrite hencL, (hinf_rem eq_refl); cbn [encL].
      assert (hSq_eq : S_q = sc_val sc + (2 ^ (i_star - sc_len sc) - 1) * 2 ^ sc_len sc).
      { subst S_q.
        assert (hpi : 2 ^ i_star = 2 ^ (i_star - sc_len sc) * 2 ^ sc_len sc)
          by (rewrite <- N.pow_add_r; f_equal; clear - hlen_le; lia).
        pose proof (pow2_pos (i_star - sc_len sc)) as hp1_pos.
        rewrite hpi; set (pa := 2 ^ (i_star - sc_len sc)) in *; set (pb := 2 ^ sc_len sc) in *;
          clearbody pa pb; clear - hp1_pos; nia. }
      rewrite hSq_eq.
      replace i_star with (sc_len sc + (i_star - sc_len sc)) at 1 by (clear - hlen_le; lia).
      rewrite (encPairs_add (sc_len sc) (i_star - sc_len sc) (sc_val sc) (2 ^ (i_star - sc_len sc) - 1) _ hval_lt), encPairs_all_ones.
      apply (f_equal (encPairs (sc_len sc) (sc_val sc))).
      rewrite <- default_eq_cons_zero, <- default_eq_cons_zero, repBit_false_default; reflexivity. }
    rewrite hL_split.
    replace (2 * mm) with (2 * (m0 + 1)) by (subst m0; clear - hmm; lia).
    eapply rs_trans; [exact (mD_pairs_sweep_sound i_star S_q m0 hSq_lt hp1 (S0 >> S0 >> const S0) (encR r_rem)) |].
    replace (2 * (m0 + 1 + i_star)) with (2 * n_bits + 2) by (subst n_bits; clear; lia).
    cbn [encodeCore]; rewrite encL_lpushPairs, encR_restoreUR; cbn [encL].
    replace (2 * (2 ^ n_bits - 1 - R_rem) + 1) with (1 + 2 * (2 ^ n_bits - 1 - R_rem)) by (clear; lia).
    exact (mD_exhaust_cascade_sound n_bits R_rem hR_lt hp2 (const S0) (encR r_rem)).
Qed.

Lemma runPsiPos_sound (p : positive) :
  forall (u u_out : UList),
    runPsiPos p u = Some u_out ->
    PsiReach (Npos p) u u_out.
Proof.
  induction p as [q IH | q IH |]; intros u u_out h; cbn [runPsiPos] in h.
  - destruct (runPsiPos q u) as [u1 |] eqn:h1; [| discriminate].
    destruct (runPsiPos q u1) as [u2 |] eqn:h2; [| discriminate].
    pose proof (PsiReach_trans (IH u u1 h1) (PsiReach_trans (IH u1 u2 h2) (PsiReach_step (ustepPsi_sound u2 u_out h)))) as htot.
    replace (Npos q + (Npos q + 1)) with (Npos (xI q)) in htot by (clear; lia); exact htot.
  - destruct (runPsiPos q u) as [u1 |] eqn:h1; [| discriminate].
    pose proof (PsiReach_trans (IH u u1 h1) (IH u1 u_out h)) as htot.
    replace (Npos q + Npos q) with (Npos (xO q)) in htot by (clear; lia); exact htot.
  - exact (PsiReach_step (ustepPsi_sound u u_out h)).
Qed.

Lemma runPsi_sound (n : N) (u u_out : UList) (h : runPsi n u = Some u_out) :
  PsiReach n u u_out.
Proof.
  destruct n as [| p]; cbn [runPsi] in h.
  - injection h as ->; apply PsiReach_refl.
  - exact (runPsiPos_sound p u u_out h).
Qed.

(* Fused Macro Rules and Stepper Soundness *)
Lemma rule_A1 (sl sr : side) :
  (sl {{A}}> (S0 >> S0 >> S1 >> sr)) -[ tm ]->*
    ((S1 >> sl) {{D}}> (S0 >> S0 >> sr)).
Proof. tsteps. Qed.

Lemma rule_A2 (lb : Sym) (sl sr : side) :
  ((lb >> sl) {{A}}> (S0 >> S1 >> sr)) -[ tm ]->*
    (sl {{D}}> (lb >> S1 >> S0 >> sr)).
Proof. tsteps. Qed.

Lemma rule_D_z2_1 (sl sr : side) :
  (sl {{D}}> (S0 >> S0 >> S1 >> sr)) -[ tm ]->*
    (sl {{D}}> (S1 >> S1 >> S0 >> sr)).
Proof. tsteps. Qed.

Lemma rule_D_z3_1 (sl sr : side) :
  (sl {{D}}> (S0 >> S0 >> S0 >> S1 >> sr)) -[ tm ]->*
    ((S1 >> S1 >> sl) {{D}}> (S0 >> S0 >> sr)).
Proof. tsteps. Qed.

Lemma rule_D_o1_0 (lb : Sym) (sl sr : side) :
  ((S0 >> lb >> sl) {{D}}> (S1 >> S1 >> sr)) -[ tm ]->*
    (sl {{D}}> (lb >> S1 >> S1 >> S1 >> sr)).
Proof. tsteps. Qed.

Lemma rule_D_o1_10 (sl sr : side) :
  ((S1 >> S0 >> sl) {{D}}> (S1 >> S1 >> sr)) -[ tm ]->*
    (sl {{D}}> (S0 >> S0 >> S1 >> S1 >> sr)).
Proof. tsteps. Qed.

Lemma rule_D_o1_111 (lb : Sym) (sl sr : side) :
  ((S1 >> S1 >> S1 >> lb >> sl) {{D}}> (S1 >> S1 >> sr)) -[ tm ]->*
    (sl {{D}}> (lb >> S1 >> S0 >> S1 >> S1 >> S1 >> sr)).
Proof. tsteps. Qed.

Lemma rule_A1_G1 (w : N) (sl sr : side) :
  (sl {{A}}> (S0 >> encW01 (w + 1) sr)) -[ tm ]->*
    ((repBit true (2 * w + 1) sl) {{D}}> (S0 >> S0 >> sr)).
Proof.
  rewrite encW01_succ.
  eapply rs_trans; [apply rule_A1 |].
  pose proof (g1_run w (S1 >> sl) sr) as hg.
  replace (2 * w + 1) with (2 * w + 1) by reflexivity.
  rewrite (repBit_add true (2 * w) 1); exact hg.
Qed.

Lemma step_D_zero (sl sr : side) :
  (sl {{D}}> (S0 >> sr)) -[ tm ]->* ((S1 >> sl) {{A}}> sr).
Proof. tsteps. Qed.

Lemma step_D_01 (sl sr : side) :
  (sl {{D}}> (S0 >> S1 >> sr)) -[ tm ]->* ((S0 >> S1 >> sl) {{A}}> sr).
Proof. tsteps. Qed.

Lemma encR_pop_w01 (w : N) (rs : list RTok) :
  encR (if w =? 0 then rs else Rw01 (w - 1) :: rs) = encW01 w (encR rs).
Proof.
  destruct (w =? 0) eqn:hw.
  - apply N.eqb_eq in hw; subst w; reflexivity.
  - apply N.eqb_neq in hw; cbn [encR]; f_equal; clear - hw; lia.
Qed.

Lemma encR_pop_o (o : N) (rs : list RTok) :
  encR (if o =? 0 then rs else Ro (o - 1) :: rs) = repBit true o (encR rs).
Proof.
  destruct (o =? 0) eqn:ho.
  - apply N.eqb_eq in ho; subst o; reflexivity.
  - apply N.eqb_neq in ho; cbn [encR]; f_equal; clear - ho; lia.
Qed.

Lemma encL_pop_z (z : N) (ls : list LTok) :
  encL (if z =? 0 then ls else Lz (z - 1) :: ls) = repBit false z (encL ls).
Proof.
  destruct (z =? 0) eqn:hz.
  - apply N.eqb_eq in hz; subst z; reflexivity.
  - apply N.eqb_neq in hz; cbn [encL]; f_equal; clear - hz; lia.
Qed.

Lemma encL_pop_o (o : N) (ls : list LTok) :
  encL (if o =? 0 then ls else Lo (o - 1) :: ls) = repBit true o (encL ls).
Proof.
  destruct (o =? 0) eqn:ho.
  - apply N.eqb_eq in ho; subst o; reflexivity.
  - apply N.eqb_neq in ho; cbn [encL]; f_equal; clear - ho; lia.
Qed.

Lemma stepMacro_mD_Rz_sound (l : list LTok) (k : N) (rs : list RTok) :
  encodeCore (Crun mD l (Rz k :: rs)) -[ tm ]->*
  encodeCore (
    if k =? 0 then
      match rs with
      | Rw01 w :: rs2 => Crun mD l (rpush1_2 (rpush0_1 (if w =? 0 then rs2 else Rw01 (w - 1) :: rs2)))
      | _ => Crun mA (lpush1_1 l) rs
      end
    else if k =? 1 then
      match rs with
      | Rw01 w :: rs2 => Crun mD (lpush1_n (2 * (w + 1)) l) (rpush0_2 rs2)
      | Ro o :: rs2 => Crun mD l (rpush1_2 (rpush0_1 (if o =? 0 then rs2 else Ro (o - 1) :: rs2)))
      | _ => Crun mA (lpush1_1 l) (Rz 0 :: rs)
      end
    else if k =? 2 then
      match rs with
      | Ro o :: rs2 => Crun mD (lpush1_2 l) (rpush0_2 (if o =? 0 then rs2 else Ro (o - 1) :: rs2))
      | _ => Crun mA (lpush1_1 l) (Rz 1 :: rs)
      end
    else Crun mA (lpush1_1 l) (Rz (k - 1) :: rs)).
Proof.
  destruct (k =? 0) eqn:hk0.
  - apply N.eqb_eq in hk0; subst k.
    destruct rs as [| [zk | ok | w | wk] rs2];
      try (cbn [encodeCore]; change (encR (Rz 0 :: ?t)) with (S0 >> encR t); rewrite encL_lpush1_1; apply step_D_zero).
    cbn [encodeCore encR]; change (repBit false (0 + 1) ?x) with (S0 >> x).
    rewrite encW01_succ, encR_rpush1_2, encR_rpush0_1, encR_pop_w01.
    apply rule_D_z2_1.
  - destruct (k =? 1) eqn:hk1.
    + apply N.eqb_eq in hk1; subst k.
      destruct rs as [| [zk | o | w | wk] rs2];
        try (cbn [encodeCore]; change (encR (Rz 1 :: ?t)) with (S0 >> S0 >> encR t);
             change (encR (Rz 0 :: ?t)) with (S0 >> encR t); rewrite encL_lpush1_1; apply step_D_zero).
      * cbn [encodeCore encR]; change (repBit false (1 + 1) ?x) with (S0 >> S0 >> x).
        rewrite repBit_succ, encR_rpush1_2, encR_rpush0_1, encR_pop_o; cbn [bitSym].
        apply rule_D_z2_1.
      * cbn [encodeCore encR]; change (repBit false (1 + 1) ?x) with (S0 >> S0 >> x).
        rewrite encL_lpush1_n by (clear; lia); rewrite encR_rpush0_2.
        apply g1_run.
    + destruct (k =? 2) eqn:hk2.
      * apply N.eqb_eq in hk2; subst k.
        destruct rs as [| [zk | o | w | wk] rs2];
          try (cbn [encodeCore]; change (encR (Rz 2 :: ?t)) with (S0 >> S0 >> S0 >> encR t);
               change (encR (Rz 1 :: ?t)) with (S0 >> S0 >> encR t); rewrite encL_lpush1_1; apply step_D_zero).
        cbn [encodeCore encR]; change (repBit false (2 + 1) ?x) with (S0 >> S0 >> S0 >> x).
        rewrite repBit_succ, encL_lpush1_2, encR_rpush0_2, encR_pop_o; cbn [bitSym].
        apply rule_D_z3_1.
      * apply N.eqb_neq in hk0; apply N.eqb_neq in hk1; apply N.eqb_neq in hk2.
        cbn [encodeCore encR]; rewrite encL_lpush1_1.
        replace (k + 1) with ((k - 1 + 1) + 1) by (clear - hk0; lia).
        rewrite repBit_succ; cbn [bitSym]; apply step_D_zero.
Qed.

Lemma stepMacro_mD_Rw01_sound (l : list LTok) (k : N) (rs : list RTok) :
  encodeCore (Crun mD l (Rw01 k :: rs)) -[ tm ]->*
  encodeCore (
    if k =? 0 then
      match rs with
      | Rz z0 :: Rw01 w0 :: Rw0111 w :: rs3 =>
        if (z0 =? 0) && (w0 =? 0) then Crun mA (lpush1_n (4 * (w + 1) + 1) l) (rpush1_1 (rpush0_2 (rpush1_1 rs3)))
        else Crun mA (lpush0_1 (lpush1_1 l)) rs
      | Ro o :: rs1 => Crun mA (lpush0 (o + 2) (lpush1_1 l)) rs1
      | _ => Crun mA (lpush0_1 (lpush1_1 l)) rs
      end
    else Crun mA (lpush0_1 (lpush1_1 l)) (Rw01 (k - 1) :: rs)).
Proof.
  assert (hbase : forall r' : list RTok,
            encodeCore (Crun mD l (Rw01 0 :: r')) -[ tm ]->*
              encodeCore (Crun mA (lpush0_1 (lpush1_1 l)) r')).
  { intro r'; cbn [encodeCore encR]; change (encW01 (0 + 1) ?x) with (S0 >> S1 >> x).
    rewrite encL_lpush0_1, encL_lpush1_1; apply step_D_01. }
  destruct (k =? 0) eqn:hk0.
  - apply N.eqb_eq in hk0; subst k.
    destruct rs as [| [z0 | o | ? | ?] rs1]; try apply hbase.
    + destruct rs1 as [| [? | ? | w0 | ?] rs2]; try apply hbase.
      destruct rs2 as [| [? | ? | ? | w] rs3]; try apply hbase.
      destruct ((z0 =? 0) && (w0 =? 0)) eqn:hz0w0; [| apply hbase].
      apply andb_prop in hz0w0; destruct hz0w0 as [hz0 hw0].
      apply N.eqb_eq in hz0; apply N.eqb_eq in hw0; subst z0 w0.
      cbn [encodeCore encR];
        change (encW01 (0 + 1) ?x) with (S0 >> S1 >> x);
        change (repBit false (0 + 1) ?x) with (S0 >> x).
      rewrite encL_lpush1_n by (clear; lia).
      rewrite encR_rpush1_1, encR_rpush0_2, encR_rpush1_1.
      eapply rs_trans; [apply step_D_zero |].
      rewrite (repBit_add true (4 * (w + 1)) 1);
        change (repBit true 1 ?x) with (S1 >> x).
      exact (g2_run (w + 1) (S1 >> encL l) (encR rs3)).
    + cbn [encodeCore encR]; change (encW01 (0 + 1) ?x) with (S0 >> S1 >> x).
      rewrite encL_lpush0 by (clear; lia); rewrite encL_lpush1_1.
      eapply rs_trans; [apply step_D_zero |].
      change (S1 >> repBit true (o + 1) (encR rs1)) with (repBit true 1 (repBit true (o + 1) (encR rs1))).
      rewrite <- repBit_add; replace (1 + (o + 1)) with (o + 2) by (clear; lia).
      apply sweep_A1.
  - apply N.eqb_neq in hk0.
    cbn [encodeCore encR]; rewrite encL_lpush0_1, encL_lpush1_1.
    replace (k + 1) with ((k - 1 + 1) + 1) by (clear - hk0; lia).
    rewrite encW01_succ; apply step_D_01.
Qed.

Lemma stepMacro_mD_Rw0111_sound (l : list LTok) (k : N) (rs : list RTok) :
  encodeCore (Crun mD l (Rw0111 k :: rs)) -[ tm ]->*
  encodeCore (
    if k =? 0 then
      match rs with
      | Ro o :: rs1 => Crun mA (lpush0 (o + 4) (lpush1_1 l)) rs1
      | _ => Crun mA (lpush0 3 (lpush1_1 l)) rs
      end
    else Crun mA (lpush0 3 (lpush1_1 l)) (Rw0111 (k - 1) :: rs)).
Proof.
  assert (hbase : forall sr : side,
            ((encL l) {{D}}> (S0 >> S1 >> S1 >> S1 >> sr)) -[ tm ]->*
              ((encL (lpush0 3 (lpush1_1 l))) {{A}}> sr)).
  { intro sr; rewrite encL_lpush0 by (clear; lia); rewrite encL_lpush1_1.
    eapply rs_trans; [apply step_D_zero |].
    exact (sweep_A1 3 (S1 >> encL l) sr). }
  destruct (k =? 0) eqn:hk0.
  - apply N.eqb_eq in hk0; subst k.
    destruct rs as [| [? | o | ? | ?] rs1];
      try (cbn [encodeCore]; change (encR (Rw0111 0 :: ?t)) with (S0 >> S1 >> S1 >> S1 >> encR t); apply hbase).
    cbn [encodeCore encR]; change (encW0111 (0 + 1) ?x) with (S0 >> S1 >> S1 >> S1 >> x).
    rewrite encL_lpush0 by (clear; lia); rewrite encL_lpush1_1.
    eapply rs_trans; [apply step_D_zero |].
    change (S1 >> S1 >> S1 >> repBit true (o + 1) (encR rs1))
      with (repBit true 3 (repBit true (o + 1) (encR rs1))).
    rewrite <- repBit_add; replace (3 + (o + 1)) with (o + 4) by (clear; lia).
    apply sweep_A1.
  - apply N.eqb_neq in hk0.
    cbn [encodeCore encR].
    replace (k + 1) with ((k - 1 + 1) + 1) by (clear - hk0; lia).
    rewrite encW0111_succ; apply hbase.
Qed.

Lemma stepMacro_mD_Ro1_sound (l : list LTok) (rs : list RTok) :
  let s := Crun mD l (Ro 1 :: rs) in
  encodeCore s -[ tm ]->*
  encodeCore (
    match l with
    | [] => stepRLE_until_AD 100%positive (stepRLE s)
    | Lo lk :: ls =>
      if 3 <=? lk then Crun mD (lpushBit true ((lk + 1) mod 4) ls) (rpush1_2 (rpushW0111 ((lk + 1) / 4) rs))
      else if lk =? 2 then let lp := lpop1 ls in Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (rpushW0111_1 rs)))
      else if lk =? 0 then
        match ls with
        | Lz zk :: ls2 => Crun mD (if zk =? 0 then ls2 else Lz (zk - 1) :: ls2) (rpush0_2 (rpush1_2 rs))
        | _ => stepRLE_until_AD 100%positive (stepRLE s)
        end
      else stepRLE_until_AD 100%positive (stepRLE s)
    | Lpairs len val :: ls =>
      if 1 <=? len then
        let rest := if len =? 1 then ls else Lpairs (len - 1) (N.div2 val) :: ls in
        Crun mD rest (if N.odd val then rpushW0111_1 rs else rpush1_n 4 rs)
      else stepRLE_until_AD 100%positive (stepRLE s)
    | Lz zk :: ls =>
      if zk =? 0 then let lp := lpop1 ls in Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 rs))
      else Crun mD (if zk =? 1 then ls else Lz (zk - 2) :: ls) (rpushW0111_1 rs)
    end).
Proof.
  cbv zeta.
  assert (hfb : forall s0, encodeCore s0 -[ tm ]->* encodeCore (stepRLE_until_AD 100%positive (stepRLE s0)))
    by (intro s0; exact (rs_trans (stepRLE_sound s0) (stepRLE_until_AD_sound 100%positive (stepRLE s0)))).
  destruct l as [| [zk | lk | len val] ls]; [apply hfb | | |].
  - destruct (zk =? 0) eqn:hzk0.
    + apply N.eqb_eq in hzk0; subst zk; cbv zeta.
      cbn [encodeCore encL encR];
        change (repBit false (0 + 1) ?x) with (S0 >> x);
        change (repBit true (1 + 1) ?x) with (S1 >> S1 >> x).
      rewrite (encL_lpop1 ls), encR_rpushBool1, encR_rpush1_3.
      apply rule_D_o1_0.
    + apply N.eqb_neq in hzk0.
      cbn [encodeCore encL encR];
        change (repBit true (1 + 1) ?x) with (S1 >> S1 >> x).
      assert (hrest : encL (if zk =? 1 then ls else Lz (zk - 2) :: ls) = repBit false (zk - 1) (encL ls)).
      { destruct (zk =? 1) eqn:hzk1.
        - apply N.eqb_eq in hzk1; subst zk; reflexivity.
        - apply N.eqb_neq in hzk1; cbn [encL]; f_equal; clear - hzk0 hzk1; lia. }
      rewrite hrest, encR_rpushW0111_1.
      replace (zk + 1) with (2 + (zk - 1)) by (clear - hzk0; lia).
      rewrite (repBit_add false 2 (zk - 1));
        change (repBit false 2 ?x) with (S0 >> S0 >> x).
      apply rule_D_o1_0.
  - destruct (3 <=? lk) eqn:hlk3.
    + apply N.leb_le in hlk3.
      cbn [encodeCore encL encR]; change (repBit true (1 + 1) ?x) with (S1 >> S1 >> x).
      rewrite encL_lpushBit, encR_rpush1_2, encR_rpushW0111.
      assert (hdiv4 : lk + 1 = 4 * ((lk + 1) / 4) + (lk + 1) mod 4) by (apply N.div_mod; clear; lia).
      set (q := (lk + 1) / 4) in *; set (rm := (lk + 1) mod 4) in *; clearbody q rm.
      rewrite hdiv4, (repBit_add true (4 * q) rm).
      apply g3_run.
    + destruct (lk =? 2) eqn:hlk2.
      * apply N.eqb_eq in hlk2; subst lk; cbv zeta.
        cbn [encodeCore encL encR];
          change (repBit true (2 + 1) ?x) with (S1 >> S1 >> S1 >> x);
          change (repBit true (1 + 1) ?x) with (S1 >> S1 >> x).
        rewrite (encL_lpop1 ls), encR_rpushBool1, encR_rpush1_1, encR_rpushW0111_1.
        apply rule_D_o1_111.
      * destruct (lk =? 0) eqn:hlk0; [| apply hfb].
        apply N.eqb_eq in hlk0; subst lk.
        destruct ls as [| [zk | ? | ? ?] ls2]; try apply hfb.
        cbn [encodeCore encL encR]; change (repBit true (0 + 1) ?x) with (S1 >> x);
          change (repBit true (1 + 1) ?x) with (S1 >> S1 >> x).
        rewrite repBit_succ, encL_pop_z, encR_rpush0_2, encR_rpush1_2; cbn [bitSym].
        apply rule_D_o1_10.
  - destruct (1 <=? len) eqn:hlen; [| apply hfb].
    apply N.leb_le in hlen; cbv zeta.
    cbn [encodeCore encL encR]; change (repBit true (1 + 1) ?x) with (S1 >> S1 >> x).
    replace len with ((len - 1) + 1) at 1 by (clear - hlen; lia).
    rewrite encPairs_succ.
    assert (hrest : encL (if len =? 1 then ls else Lpairs (len - 1) (N.div2 val) :: ls) =
                    encPairs (len - 1) (val / 2) (encL ls)).
    { rewrite N_div2_eq; destruct (len =? 1) eqn:hl1.
      - apply N.eqb_eq in hl1; subst len; reflexivity.
      - reflexivity. }
    rewrite hrest, N_odd_eq.
    destruct (val mod 2 =? 1).
    + rewrite encR_rpushW0111_1; apply rule_D_o1_0.
    + rewrite encR_rpush1_n by (clear; lia);
        change (repBit true 4 ?x) with (S1 >> S1 >> S1 >> S1 >> x); apply rule_D_o1_0.
Qed.

Lemma stepMacro_mA_Ro_sweep (l : list LTok) (k : N) (rs : list RTok) :
  encodeCore (Crun mA l (Ro k :: rs)) -[ tm ]->*
  encodeCore (
    let l1 := lpush0 (k + 1) l in
    match rs with
    | Rz z0 :: Rw01 w :: rs2 =>
      if z0 =? 0 then Crun mD (if w =? 0 then lpush1_1 l1 else lpush1_n (2 * w + 1) l1) (rpush0_2 rs2)
      else Crun mA l1 rs
    | _ => Crun mA l1 rs
    end).
Proof.
  cbv zeta.
  assert (hsw : encodeCore (Crun mA l (Ro k :: rs)) -[ tm ]->* encodeCore (Crun mA (lpush0 (k + 1) l) rs)).
  { cbn [encodeCore encR]; rewrite encL_lpush0 by (clear; lia); apply sweep_A1. }
  eapply rs_trans; [exact hsw |].
  set (l1 := lpush0 (k + 1) l).
  destruct rs as [| [z0 | ? | ? | ?] rs1]; try apply rs_refl.
  destruct rs1 as [| [? | ? | w | ?] rs2]; try apply rs_refl.
  destruct (z0 =? 0) eqn:hz0; [| apply rs_refl].
  apply N.eqb_eq in hz0; subst z0.
  destruct (w =? 0) eqn:hw0.
  - apply N.eqb_eq in hw0; subst w; cbn [encodeCore encR];
      change (repBit false (0 + 1) ?x) with (S0 >> x);
      change (encW01 (0 + 1) ?x) with (S0 >> S1 >> x).
    rewrite encL_lpush1_1, encR_rpush0_2; apply rule_A1.
  - apply N.eqb_neq in hw0; cbn [encodeCore encR]; change (repBit false (0 + 1) ?x) with (S0 >> x).
    rewrite encL_lpush1_n by (clear; lia); rewrite encR_rpush0_2.
    apply rule_A1_G1.
Qed.

Lemma stepMacro_mA_u_zr_sound (l : list LTok) (r : list RTok)
  (zr : ZRunRes) (fb : CoreState)
  (hL : encL l = repBit false (zr_n zr) (encL (zr_l zr)))
  (hfb : encodeCore (Crun mA l r) -[ tm ]->* encodeCore fb) :
  encodeCore (Crun mA l r) -[ tm ]->*
  encodeCore (
    let Z := zr_n zr in let l_tmp := zr_l zr in
    if 1 <=? Z then
      let up := extractUPrefixR r in
      let us := up_u up in let r_rem := up_r up in
      match ustepCore0 us with
      | None => fb
      | Some (retB u1) =>
        if 3 <=? Z then
          let lp := lpop1 (lpushBit false (Z - 3) l_tmp) in
          Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR (upush 0 1 u1) r_rem)))
        else
          let lp := lpop1 (lpushBit false (Z - 1) l_tmp) in
          Crun mB (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u1 r_rem)))
      | Some (retD u1) =>
        let try2 :=
          if 3 <=? Z then
            match ustepCore0 u1 with
            | Some (retD u2) =>
              let lp := lpop1 (lpushBit false (Z - 3) l_tmp) in
              Some (Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u2 r_rem))))
            | _ => None
            end
          else None in
        match try2 with
        | Some s' => s'
        | None =>
          let lp := lpop1 (lpushBit false (Z - 1) l_tmp) in
          Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (restoreUR u1 r_rem)))
        end
      end
    else fb).
Proof.
  cbv zeta.
  destruct zr as [Z l_tmp]; cbn [zr_n zr_l] in *.
  destruct (1 <=? Z) eqn:hZ1; [| exact hfb].
  apply N.leb_le in hZ1.
  pose proof (encR_extractUPrefixR r) as hR.
  destruct (extractUPrefixR r) as [us r_rem]; cbn [up_u up_r] in *.
  assert (hcore0 : forall res : Core0Res, ustepCore0 us = Some res ->
            encodeCore (Crun mA l r) -[ tm ]->*
              encodeCore (
                let lp := lpop1 (lpushBit false (Z - 1) l_tmp) in
                match res with
                | retB u0 => Crun mB (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u0 r_rem)))
                | retD u0 => Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (restoreUR u0 r_rem)))
                end)).
  { intros res hc0; cbv zeta.
    set (lp := lpop1 (lpushBit false (Z - 1) l_tmp)).
    assert (hL1 : encL l = S0 >> bitSym (bpl_b lp) >> encL (bpl_l lp)).
    { rewrite hL; replace Z with (1 + (Z - 1)) by (clear - hZ1; lia).
      rewrite (repBit_add false 1 (Z - 1)), <- encL_lpushBit, (encL_lpop1 (lpushBit false (Z - 1) l_tmp)).
      reflexivity. }
    pose proof (ustepCore0_sound us res hc0 (bitSym (bpl_b lp) >> encL (bpl_l lp)) (encR r_rem)) as hs.
    destruct res as [u0 | u0]; cbn [encodeCore core0ResCfg] in hs |- *; rewrite hL1, hR.
    - rewrite encR_rpushBool1, encR_rpush1_3, encR_restoreUR; exact hs.
    - rewrite encR_rpushBool1, encR_rpush1_1, encR_restoreUR; exact hs. }
  assert (hpsi_step : forall u_out : UList, 3 <= Z -> ustepPsi us = Some u_out ->
            encodeCore (Crun mA l r) -[ tm ]->*
              encodeCore (
                let lp := lpop1 (lpushBit false (Z - 3) l_tmp) in
                Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u_out r_rem))))).
  { intros u_out hZ3 hpsi; cbv zeta.
    set (lp := lpop1 (lpushBit false (Z - 3) l_tmp)).
    assert (hL3 : encL l = repBit false 3 (bitSym (bpl_b lp) >> encL (bpl_l lp))).
    { rewrite hL; replace Z with (3 + (Z - 3)) by (clear - hZ3; lia).
      rewrite (repBit_add false 3 (Z - 3)), <- encL_lpushBit, (encL_lpop1 (lpushBit false (Z - 3) l_tmp)).
      reflexivity. }
    pose proof (coreK_sound 0 (PsiReach_step (ustepPsi_sound us u_out hpsi))
                  (bitSym (bpl_b lp) >> encL (bpl_l lp)) (encR r_rem)) as hck.
    cbn [encodeCore]; rewrite hL3, hR, encR_rpushBool1, encR_rpush1_3, encR_restoreUR.
    exact hck. }
  destruct (ustepCore0 us) as [[u1 | u1] |] eqn:hc0; [| | exact hfb].
  - destruct (3 <=? Z) eqn:hZ3.
    + apply N.leb_le in hZ3.
      apply (hpsi_step (upush 0 1 u1) hZ3).
      unfold ustepPsi; rewrite hc0; reflexivity.
    + exact (hcore0 (retB u1) eq_refl).
  - destruct (3 <=? Z) eqn:hZ3.
    + apply N.leb_le in hZ3.
      destruct (ustepCore0 u1) as [[? | u2] |] eqn:hc1.
      * exact (hcore0 (retD u1) eq_refl).
      * apply (hpsi_step u2 hZ3).
        unfold ustepPsi; rewrite hc0, hc1; reflexivity.
      * exact (hcore0 (retD u1) eq_refl).
    + exact (hcore0 (retD u1) eq_refl).
Qed.

Lemma stepMacro_mA_u_sound (l : list LTok) (r : list RTok) :
  let s := Crun mA l r in
  encodeCore s -[ tm ]->*
  encodeCore (
    let zr := lpopZRun l in
    let Z := zr_n zr in let l_tmp := zr_l zr in
    if 1 <=? Z then
      let up := extractUPrefixR r in
      let us := up_u up in let r_rem := up_r up in
      match ustepCore0 us with
      | None => stepRLE_until_AD 100%positive (stepRLE s)
      | Some (retB u1) =>
        if 3 <=? Z then
          let lp := lpop1 (lpushBit false (Z - 3) l_tmp) in
          Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR (upush 0 1 u1) r_rem)))
        else
          let lp := lpop1 (lpushBit false (Z - 1) l_tmp) in
          Crun mB (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u1 r_rem)))
      | Some (retD u1) =>
        let try2 :=
          if 3 <=? Z then
            match ustepCore0 u1 with
            | Some (retD u2) =>
              let lp := lpop1 (lpushBit false (Z - 3) l_tmp) in
              Some (Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_3 (restoreUR u2 r_rem))))
            | _ => None
            end
          else None in
        match try2 with
        | Some s' => s'
        | None =>
          let lp := lpop1 (lpushBit false (Z - 1) l_tmp) in
          Crun mD (bpl_l lp) (rpushBool1 (bpl_b lp) (rpush1_1 (restoreUR u1 r_rem)))
        end
      end
    else stepRLE_until_AD 100%positive (stepRLE s)).
Proof.
  cbv zeta.
  exact (stepMacro_mA_u_zr_sound l r (lpopZRun l)
           (stepRLE_until_AD 100%positive (stepRLE (Crun mA l r)))
           (encL_lpopZRun l)
           (rs_trans (stepRLE_sound (Crun mA l r)) (stepRLE_until_AD_sound 100%positive (stepRLE (Crun mA l r))))).
Qed.

Lemma stepMacro_mD_Ro_sc_eb_sound
  (l : list LTok) (k : N) (rs : list RTok) (sc : ScanRes) (up : UPrefRes)
  (fb : CoreState) (eb : option (UList * N))
  (hk3 : 3 <= k) (hkev : (k + 1) mod 2 = 0)
  (hsc_val : sc_val sc < 2 ^ sc_len sc)
  (hsc_enc : encL l = encPairs (sc_len sc) (sc_val sc) (encL (sc_rem sc)))
  (hsc_inf : sc_inf sc = true -> sc_rem sc = [])
  (hexR : encR rs = encU (up_u up) (encR (up_r up)))
  (hfb : encodeCore (Crun mD l (Ro k :: rs)) -[ tm ]->* encodeCore fb)
  (heb_ok : forall u_end nmax, eb = Some (u_end, nmax) -> PsiReach nmax (up_u up) u_end) :
  let s := Crun mD l (Ro k :: rs) in
  encodeCore s -[ tm ]->*
  encodeCore (
    if (1 <=? sc_len sc) || sc_inf sc then
      let mm := (k + 1) / 2 in
      let us := up_u up in let r_rem := up_r up in
      match us with
      | Unil => fb
      | _ =>
        if negb (sc_inf sc) && (sc_val sc =? 0) then
          Crun mD (sc_rem sc) (rpushBit true (2 * (mm + sc_len sc)) (restoreUR us r_rem))
        else if (if negb (sc_inf sc) && (mm - 1 <=? 10) then if sc_val sc <=? 1024 then N.shiftl (sc_val sc) (mm - 1) <=? 1024 else false else false) then
          match runPsi (N.shiftl (sc_val sc) (mm - 1)) us with
          | Some u_mid => Crun mD (sc_rem sc) (rpushBit true (2 * (mm + sc_len sc)) (restoreUR u_mid r_rem))
          | None =>
            match eb with
            | Some (u_end, nmax) => match mD_exhaust_apply sc mm r_rem u_end nmax with Some s' => s' | None => s end
            | None => s
            end
          end
        else
          match eb with
          | Some (u_end, nmax) => match mD_exhaust_apply sc mm r_rem u_end nmax with Some s' => s' | None => s end
          | None => s
          end
      end
    else fb).
Proof.
  cbv zeta.
  destruct ((1 <=? sc_len sc) || sc_inf sc) eqn:hsc_ok; [| exact hfb].
  assert (h2m : k + 1 = 2 * ((k + 1) / 2)) by (clear - hkev; lia).
  assert (hmm2 : 2 <= (k + 1) / 2) by (clear - hk3 hkev; lia).
  set (mm := (k + 1) / 2) in *; clearbody mm.
  destruct up as [us r_rem]; cbn [up_u up_r] in *.
  assert (hencR : encR (Ro k :: rs) = repBit true (2 * mm) (encU us (encR r_rem))).
  { cbn [encR]; rewrite h2m, hexR; reflexivity. }
  assert (hexh :
            encodeCore (Crun mD l (Ro k :: rs)) -[ tm ]->*
            encodeCore (
              match eb with
              | Some (u_end, nmax) =>
                match mD_exhaust_apply sc mm r_rem u_end nmax with
                | Some s' => s'
                | None => Crun mD l (Ro k :: rs)
                end
              | None => Crun mD l (Ro k :: rs)
              end)).
  { destruct eb as [[u_end nmax] |] eqn:heb; [| apply rs_refl].
    pose proof (heb_ok u_end nmax eq_refl) as hp.
    destruct (mD_exhaust_apply sc mm r_rem u_end nmax) as [s' |] eqn:happ; [| apply rs_refl].
    cbn [encodeCore]; rewrite hencR.
    exact (mD_exhaust_apply_sound l sc mm r_rem us u_end nmax s' hsc_val hsc_enc hsc_inf hp happ). }
  destruct us as [| u0 c0 tl]; [exact hfb |].
  destruct (negb (sc_inf sc) && (sc_val sc =? 0)) eqn:hz.
  - apply andb_prop in hz; destruct hz as [_ hv0]; apply N.eqb_eq in hv0.
    assert (h0lt : 0 < 2 ^ sc_len sc) by (pose proof (pow2_pos (sc_len sc)) as hp2; clear - hp2; lia).
    cbn [encodeCore]; rewrite hsc_enc, hv0, hencR, encR_rpushBit, encR_restoreUR.
    replace (2 * mm) with (2 * ((mm - 1) + 1)) by (clear - hmm2; lia).
    replace (2 * (mm + sc_len sc)) with (2 * ((mm - 1) + 1 + sc_len sc)) by (clear - hmm2; lia).
    exact (mD_pairs_sweep_sound (sc_len sc) 0 (mm - 1) h0lt
             (PsiReach_refl (Ucons u0 c0 tl)) (encL (sc_rem sc)) (encR r_rem)).
  - destruct (if negb (sc_inf sc) && (mm - 1 <=? 10) then if sc_val sc <=? 1024 then N.shiftl (sc_val sc) (mm - 1) <=? 1024 else false else false);
      [| exact hexh].
    destruct (runPsi (N.shiftl (sc_val sc) (mm - 1)) (Ucons u0 c0 tl)) as [u_mid |] eqn:hrp; [| exact hexh].
    pose proof (runPsi_sound _ _ _ hrp) as hp.
    rewrite N.shiftl_mul_pow2 in hp.
    cbn [encodeCore]; rewrite hsc_enc, hencR, encR_rpushBit, encR_restoreUR.
    replace (2 * mm) with (2 * ((mm - 1) + 1)) by (clear - hmm2; lia).
    replace (2 * (mm + sc_len sc)) with (2 * ((mm - 1) + 1 + sc_len sc)) by (clear - hmm2; lia).
    exact (mD_pairs_sweep_sound (sc_len sc) (sc_val sc) (mm - 1) hsc_val hp (encL (sc_rem sc)) (encR r_rem)).
Qed.

Lemma exhaustAnyBand_0_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (p : positive) (us u_end : UList) (nmax : N)
  (h : exhaustAnyBand ltab dtab p us 0 = Some (u_end, nmax)) :
  PsiReach nmax us u_end.
Proof.
  destruct (exhaustAnyBand_sound hltab hdtab p us u_end 0 nmax h) as [_ hp].
  replace (nmax - 0) with nmax in hp by (clear; lia).
  exact hp.
Qed.

Lemma stepMacro_mD_Ro_sc_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (l : list LTok) (k : N) (rs : list RTok) (sc : ScanRes)
  (hk3 : 3 <= k) (hkev : (k + 1) mod 2 = 0)
  (hsc_val : sc_val sc < 2 ^ sc_len sc)
  (hsc_enc : encL l = encPairs (sc_len sc) (sc_val sc) (encL (sc_rem sc)))
  (hsc_inf : sc_inf sc = true -> sc_rem sc = []) :
  let s := Crun mD l (Ro k :: rs) in
  encodeCore s -[ tm ]->*
  encodeCore (
    if (1 <=? sc_len sc) || sc_inf sc then
      let mm := (k + 1) / 2 in
      let up := extractUPrefixR rs in
      let us := up_u up in let r_rem := up_r up in
      match us with
      | Unil => stepRLE_until_AD 100%positive (stepRLE s)
      | _ =>
        if negb (sc_inf sc) && (sc_val sc =? 0) then
          Crun mD (sc_rem sc) (rpushBit true (2 * (mm + sc_len sc)) (restoreUR us r_rem))
        else if (if negb (sc_inf sc) && (mm - 1 <=? 10) then if sc_val sc <=? 1024 then N.shiftl (sc_val sc) (mm - 1) <=? 1024 else false else false) then
          match runPsi (N.shiftl (sc_val sc) (mm - 1)) us with
          | Some u_mid => Crun mD (sc_rem sc) (rpushBit true (2 * (mm + sc_len sc)) (restoreUR u_mid r_rem))
          | None =>
            match exhaustAnyBand ltab dtab 10000%positive us 0 with
            | Some (u_end, nmax) => match mD_exhaust_apply sc mm r_rem u_end nmax with Some s' => s' | None => s end
            | None => s
            end
          end
        else
          match exhaustAnyBand ltab dtab 10000%positive us 0 with
          | Some (u_end, nmax) => match mD_exhaust_apply sc mm r_rem u_end nmax with Some s' => s' | None => s end
          | None => s
          end
      end
    else stepRLE_until_AD 100%positive (stepRLE s)).
Proof.
  cbv zeta.
  exact (stepMacro_mD_Ro_sc_eb_sound l k rs sc (extractUPrefixR rs)
           (stepRLE_until_AD 100%positive (stepRLE (Crun mD l (Ro k :: rs))))
           (exhaustAnyBand ltab dtab 10000%positive (up_u (extractUPrefixR rs)) 0)
           hk3 hkev hsc_val hsc_enc hsc_inf
           (encR_extractUPrefixR rs)
           (rs_trans (stepRLE_sound (Crun mD l (Ro k :: rs))) (stepRLE_until_AD_sound 100%positive (stepRLE (Crun mD l (Ro k :: rs)))))
           (exhaustAnyBand_0_sound hltab hdtab 10000%positive (up_u (extractUPrefixR rs)))).
Qed.

Lemma stepMacro_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (s : CoreState) :
  encodeCore s -[ tm ]->* encodeCore (stepMacro ltab dtab s).
Proof.
  assert (hfb : forall s0, encodeCore s0 -[ tm ]->* encodeCore (stepRLE_until_AD 100%positive (stepRLE s0)))
    by (intro s0; exact (rs_trans (stepRLE_sound s0) (stepRLE_until_AD_sound 100%positive (stepRLE s0)))).
  destruct s as [[| | | | |] l r | l r]; try apply rs_refl; try apply hfb.
  - (* mA *)
    cbn [stepMacro].
    destruct r as [| [k | k | w | w] rs]; [apply hfb | | | |].
    + (* Rz k :: rs *)
      destruct (k =? 0) eqn:hk0.
      * apply N.eqb_eq in hk0; subst k.
        destruct rs as [| [? | o | w | ?] rs1]; try apply hfb.
        -- cbv zeta; cbn [encodeCore encR]; change (repBit false (0 + 1) ?x) with (S0 >> x).
           rewrite repBit_succ, (encL_lpop1 l), encR_rpushBool1, encR_rpush1_1, encR_rpush0_1, encR_pop_o; cbn [bitSym].
           apply rule_A2.
        -- destruct (w =? 0) eqn:hw0.
           ++ apply N.eqb_eq in hw0; subst w; cbn [encodeCore encR];
                change (repBit false (0 + 1) ?x) with (S0 >> x);
                change (encW01 (0 + 1) ?x) with (S0 >> S1 >> x).
              rewrite encL_lpush1_1, encR_rpush0_2; apply rule_A1.
           ++ apply N.eqb_neq in hw0; cbn [encodeCore encR]; change (repBit false (0 + 1) ?x) with (S0 >> x).
              rewrite encL_lpush1_n by (clear; lia); rewrite encR_rpush0_2; apply rule_A1_G1.
      * destruct (k =? 1) eqn:hk1; [| apply hfb].
        apply N.eqb_eq in hk1; subst k.
        destruct rs as [| [? | o | ? | ?] rs1]; try apply hfb.
        cbn [encodeCore encR]; change (repBit false (1 + 1) ?x) with (S0 >> S0 >> x).
        rewrite repBit_succ, encL_lpush1_1, encR_rpush0_2, encR_pop_o; cbn [bitSym].
        apply rule_A1.
    + (* Ro k :: rs *)
      destruct (k =? 0) eqn:hk0; [| exact (stepMacro_mA_Ro_sweep l k rs)].
      apply N.eqb_eq in hk0; subst k.
      destruct rs as [| [z0 | ? | ? | ?] rs1]; try exact (stepMacro_mA_Ro_sweep l 0 _).
      destruct rs1 as [| [? | ? | w0 | ?] rs2]; try exact (stepMacro_mA_Ro_sweep l 0 _).
      destruct rs2 as [| [? | ? | ? | w] rs3]; try exact (stepMacro_mA_Ro_sweep l 0 _).
      destruct ((z0 =? 0) && (w0 =? 0)) eqn:hzw.
      * apply andb_prop in hzw; destruct hzw as [hz0 hw0].
        apply N.eqb_eq in hz0; apply N.eqb_eq in hw0; subst z0 w0.
        cbn [encodeCore encR];
          change (repBit true (0 + 1) ?x) with (S1 >> x);
          change (repBit false (0 + 1) ?x) with (S0 >> x);
          change (encW01 (0 + 1) ?x) with (S0 >> S1 >> x).
        rewrite encL_lpush1_n by (clear; lia).
        rewrite encR_rpush1_1, encR_rpush0_2, encR_rpush1_1.
        exact (g2_run (w + 1) (encL l) (encR rs3)).
      * exact (stepMacro_mA_Ro_sweep l 0 (Rz z0 :: Rw01 w0 :: Rw0111 w :: rs3)).
    + (* Rw01 w :: rs *)
      destruct l as [| [zk | ok | len val] ls];
        [apply hfb | exact (stepMacro_mA_u_sound _ _) | | exact (stepMacro_mA_u_sound _ _)].
      cbv zeta; cbn [encodeCore encL encR].
      rewrite repBit_succ, encW01_succ, encL_pop_o, encR_rpush1_2, encR_rpush0_1, encR_pop_w01; cbn [bitSym].
      apply rule_A2.
    + (* Rw0111 w :: rs *)
      destruct l as [| [zk | ok | len val] ls];
        [apply hfb | exact (stepMacro_mA_u_sound _ _) | apply hfb | exact (stepMacro_mA_u_sound _ _)].
  - (* mD *)
    cbn [stepMacro].
    destruct r as [| [k | k | k | k] rs].
    + cbn [encodeCore encR]; rewrite default_eq_cons_zero at 1; rewrite encL_lpush1_1; apply step_D_zero.
    + exact (stepMacro_mD_Rz_sound l k rs).
    + (* Ro k :: rs *)
      destruct (k =? 1) eqn:hk1.
      * apply N.eqb_eq in hk1; subst k; exact (stepMacro_mD_Ro1_sound l rs).
      * destruct ((3 <=? k) && ((k + 1) mod 2 =? 0)) eqn:hk3; [| apply hfb].
        apply andb_prop in hk3; destruct hk3 as [hk3 hkev].
        apply N.leb_le in hk3; apply N.eqb_eq in hkev.
        destruct (scanLPairsCompact_sound l) as [hsc_val [hsc_enc hsc_inf]].
        cbv zeta.
        exact (stepMacro_mD_Ro_sc_sound hltab hdtab l k rs (scanLPairsCompact l) hk3 hkev hsc_val hsc_enc hsc_inf).
    + exact (stepMacro_mD_Rw01_sound l k rs).
    + exact (stepMacro_mD_Rw0111_sound l k rs).
Qed.

Lemma stepMacro_step_sound {ltab : T8192 (T4096 LEnt)} {dtab : T4096 DEntry}
  (hltab : t8_all (t4_all LEntValid) ltab)
  (hdtab : t4_all DEntryValid dtab)
  (s : CoreState) :
  encodeCore s -[ tm ]->* encodeCore (sr_val (stepMacro_step ltab dtab s)).
Proof.
  destruct s as [m l r | l r]; cbn [stepMacro_step sr_val].
  - exact (stepMacro_sound hltab hdtab (Crun m l r)).
  - apply rs_refl.
Qed.

Lemma finish_halt (final : CoreState)
  (hrun : encodeCore (Crun mB [Lo 0] []) -[ tm ]->* encodeCore final)
  (hchk : (match final with Chalt _ _ => true | _ => false end) = true) :
  halts tm c0.
Proof.
  destruct final as [? ? ? | lh rh]; [discriminate |].
  exact (evstep_to_halts (rs_trans entry_steps hrun) (halted_Chalt lh rh)).
Qed.

Lemma finish_dp_fuel (fuel : positive) (dp : T8192 (T4096 LEnt) * T4096 DEntry)
  (hdp : let '(ltab, dtab) := dp in t8_all (t4_all LEntValid) ltab /\ t4_all DEntryValid dtab)
  (hcert : cert_check_fuel fuel dp = true) :
  halts tm c0.
Proof.
  destruct dp as [ltab dtab]; destruct hdp as [hltab hdtab]; unfold cert_check_fuel in hcert.
  exact (finish_halt
           (sr_val (runPos fuel (stepMacro_step ltab dtab) (Crun mB [Lo 0] [])))
           (runPos_rel
              (fun s1 s2 => encodeCore s1 -[ tm ]->* encodeCore s2)
              (fun _ _ _ => rs_trans)
              (stepMacro_step ltab dtab)
              (stepMacro_step_sound hltab hdtab)
              fuel
              (Crun mB [Lo 0] []))
           hcert).
Qed.

Lemma halt_internal_from_cert (hcert : cert_check = true) : halts tm c0.
Proof.
  exact (finish_dp_fuel 1000000%positive init_and_run_dp init_and_run_dp_valid hcert).
Qed.

Lemma cert_ok : cert_check = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma halt_internal : halts tm c0.
Proof. exact (halt_internal_from_cert cert_ok). Qed.

End Internal.

Theorem halt : halts tm c0.
Proof. exact Internal.halt_internal. Qed.
