(* BB(6) holdout 608:#235 / 797:#318: 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB halts. *)

From BusyCoq Require Import Individual62.
From BusyCoq Require BigUint.
From Coq Require Uint63.
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


(* --- Section 4: Radix trees and DP --- *)
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

(* The DP stores round counts as BusyCoq BigUint values.
   Index arithmetic and the semantic specification still use N. *)
Definition big_to_N (a : BigUint.BigUint) : N := Z.to_N (BigUint.toZ' a).
Definition big_small (a : Z) := BigUint.BigUintCons (Uint63.of_Z a) BigUint.BigUintNil.
Definition bit63 (c : bool) := if c then Uint63.of_Z 1 else Uint63.of_Z 0.
Definition big_add_c (c : bool) (a b : BigUint.BigUint) :=
  BigUint.addc a b (bit63 c).

Lemma big_inc_spec a : big_to_N (BigUint.succ a) = big_to_N a + 1.
Proof.
  unfold big_to_N. rewrite !BigUint.toZ'_spec, BigUint.succ_spec.
  now rewrite Z2N.inj_add by (try apply BigUint.toZ_ge0; lia).
Qed.

Lemma big_add_c_spec a c b :
  big_to_N (big_add_c c a b) = big_to_N a + big_to_N b + (if c then 1 else 0).
Proof.
  unfold big_to_N, big_add_c. rewrite !BigUint.toZ'_spec.
  rewrite BigUint.addc_spec by (destruct c; reflexivity).
  pose proof (BigUint.toZ_ge0 a). pose proof (BigUint.toZ_ge0 b).
  assert (hc : Uint63.to_Z (bit63 c) = (if c then 1 else 0)%Z)
    by (destruct c; reflexivity).
  rewrite hc. destruct c; rewrite !Z2N.inj_add by lia; reflexivity.
Qed.

Lemma count_1 : big_to_N (big_small 1%Z) = 1.
Proof. reflexivity. Qed.
Lemma count_2 : big_to_N (big_small 2%Z) = 2.
Proof. reflexivity. Qed.
Lemma count_4 : big_to_N (big_small 4%Z) = 4.
Proof. reflexivity. Qed.
Lemma count_6 : big_to_N (big_small 6%Z) = 6.
Proof. reflexivity. Qed.

Inductive MEnt : Type := mnone | mzero (my : N) (pk : Nib3) (py : N) | mpos (my : N) (pk : Nib3) (py : N) (m : BigUint.BigUint).
Record DEnt := mkDEnt { de_ok : bool; de_k : N; de_dx : N; de_dyk : Nib3; de_dy : N; de_m : BigUint.BigUint }.
Fixpoint build_ev (cnt : nat) (y ny W : N) (fe : list MEnt) (fO : N -> MEnt) (dP : DEnt) : list MEnt :=
  match cnt with
  | O => []
  | S cnt' =>
    let '(e1, fe') := match fe with x::r => (x, r) | [] => (mnone, []) end in
    let cell :=
      match e1 with
      | mpos my pk1 py1 m1 =>
        if (my =? y) && (2 * y + 3 <=? W) then
          match fO py1 with
          | mpos my2 pk2 py2 m2 => if my2 =? py1 then mpos y pk2 py2 (big_add_c false m1 m2) else mnone
          | mzero my2 pk2 py2 => if my2 =? py1 then mpos y pk2 py2 m1 else mnone
          | mnone => mnone
          end
        else mnone
      | _ =>
        if y =? ny then let py := ny + 1 in mzero y (N_to_nib3 py) py
        else if (y + 1 =? ny) && de_ok dP && (de_k dP =? y + 2) && (1 <=? y) then
          mpos y (de_dyk dP) (de_dy dP) (BigUint.succ (de_m dP))
        else mnone
      end in
    cell :: build_ev cnt' (y + 1) ny W fe' fO dP
  end.

Fixpoint build_od (cnt : nat) (y ny W1 : N) (fo : list MEnt) (fEv : N -> MEnt) (dP : DEnt) : list MEnt :=
  match cnt with
  | O => []
  | S cnt' =>
    let '(e1, fo') := match fo with x::r => (x, r) | [] => (mnone, []) end in
    let cell :=
      match e1 with
      | mpos my pk1 py1 m1 =>
        if (my =? y) && (2 * y + 3 <=? W1) then
          match fEv py1 with
          | mpos my2 pk2 py2 m2 => if my2 =? py1 then mpos y pk2 py2 (big_add_c false m1 m2) else mnone
          | mzero my2 pk2 py2 => if my2 =? py1 then mpos y pk2 py2 m1 else mnone
          | mnone => mnone
          end
        else mnone
      | mzero _ _ _ => mnone
      | mnone =>
        if (y =? ny) && de_ok dP && (de_k dP =? y + 1) && (1 <=? y) then
          let dk := de_dyk dP in
          match fEv (de_dy dP) with
          | mpos my2 pk2 py2 m2 => if my2 =? de_dy dP then mpos y pk2 py2 (big_add_c true (de_m dP) m2) else mnone
          | mzero my2 pk2 py2 => if my2 =? de_dy dP then mpos y pk2 py2 (BigUint.succ (de_m dP)) else mnone
          | mnone => mnone
          end
        else mnone
      end in
    cell :: build_od cnt' (y + 1) ny W1 fo' fEv dP
  end.

Definition Checkpoints := T8192 (option (N * T4096 MEnt)).
Definition saveRow (ck : Checkpoints) (W : N) (t : T4096 MEnt) : Checkpoints :=
  t8_set ck W (Some (W,t)).
Definition packRow := pack_t4 mnone (v16_const mnone) (v16_const (v16_const mnone)).
Definition readRow (row : T4096 MEnt) (y : N) := get_t4 row (N_to_nib3 y).
Definition noD := mkDEnt false 0 0 (N_to_nib3 0) 0 BigUint.BigUintNil.
Definition firstOdd (ny : N) := mpos 0 (N_to_nib3 (ny+1)) (ny+1) (big_small 1%Z).

Record DPState := mkDPState {
  dps_ny_nat : nat;
  dps_ny : N;
  dps_fe_l : list MEnt;
  dps_fo_l : list MEnt;
  dps_fo_t : T4096 MEnt;
  dps_dP : DEnt;
  dps_dC : DEnt;
  dps_ltab : Checkpoints;
  dps_dtab : T4096 DEnt
}.

Fixpoint run_dp (rem : nat) (st : DPState) : DPState :=
  match rem with
  | O => st
  | S rem' =>
    let ny := dps_ny st in
    let W := 2 * ny in let W1 := W + 1 in
    let fev_l := build_ev (S (dps_ny_nat st)) 0 ny W (dps_fe_l st)
                  (readRow (dps_fo_t st)) (dps_dP st) in
    let fev_t := packRow fev_l in
    let fod_l := firstOdd ny :: build_od (dps_ny_nat st) 1 ny W1
                  (tl (dps_fo_l st)) (readRow fev_t) (dps_dP st) in
    let fod_t := packRow fod_l in
    let ck := if ny mod 8 =? 1 then saveRow (saveRow (dps_ltab st) W fev_t) W1 fod_t
              else dps_ltab st in
    let dC := dps_dC st in
    let '(dN, dtab') :=
      if de_ok dC && (de_k dC =? ny + 2) then
        match get_t4 fod_t (de_dyk dC) with
        | mpos my pk py m =>
          if my =? de_dy dC then
            let kN := ny + 3 in
            let dN := mkDEnt true kN (2 * (ny+2)-1-2*py) pk py (big_add_c false (de_m dC) m) in
            (dN, if kN <? 4096 then t4_set (dps_dtab st) (N_to_nib3 kN) dN else dps_dtab st)
          else (noD, dps_dtab st)
        | _ => (noD, dps_dtab st)
        end
      else (noD, dps_dtab st) in
    run_dp rem' (mkDPState (S (dps_ny_nat st)) (ny+1) fev_l fod_l fod_t dC dN ck dtab')
  end.

Definition seed0 := [mzero 0 (N_to_nib3 1) 1].
Definition seed1 := [firstOdd 0].
Definition seed2 := [mpos 0 (N_to_nib3 0) 0 (big_small 2%Z); mzero 1 (N_to_nib3 2) 2].
Definition seed3 := [firstOdd 1; mpos 1 (N_to_nib3 0) 0 (big_small 4%Z)].
Definition ds2 := mkDEnt true 2 1 (N_to_nib3 0) 0 (big_small 1%Z).
Definition ds3 := mkDEnt true 3 1 (N_to_nib3 1) 1 (big_small 2%Z).
Definition ds4 := mkDEnt true 4 5 (N_to_nib3 0) 0 (big_small 6%Z).

Definition dp_start : DPState :=
  let empty := t4_const None in
  let ck := List.fold_left (fun ck '(W, xs) => saveRow ck W (packRow xs))
    [(0,seed0);(1,seed1);(2,seed2);(3,seed3)] (mkT8 empty empty) in
  let dt := List.fold_left (fun dt d => t4_set dt (N_to_nib3 (de_k d)) d)
    [ds2;ds3;ds4] (t4_const noD) in
  mkDPState 2%nat 2 seed2 seed3 (packRow seed3) ds3 ds4 ck dt.

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

Definition MEntValid (W : N) (e : MEnt) : Prop :=
  match e with
  | mnone => True
  | mzero my _ py => LCellSpec W my py 0
  | mpos my _ py m => 1 <= big_to_N m /\ LCellSpec W my py (big_to_N m)
  end.

Definition DEntValid (d : DEnt) : Prop :=
  de_ok d = true -> DValid (de_k d) (de_dx d) (de_dy d) (big_to_N (de_m d)).

Definition RowValid (r : option (N * T4096 MEnt)) :=
  match r with Some (W,t) => t4_all (MEntValid W) t | None => True end.

Lemma saveRow_valid {ck W t} (hc : t8_all RowValid ck) (hr : t4_all (MEntValid W) t) :
  t8_all RowValid (saveRow ck W t).
Proof. unfold saveRow. apply t8_set_all; [exact hc | exact hr]. Qed.

Lemma readRow_valid {W t} (ht : t4_all (MEntValid W) t) :
  forall y, MEntValid W (readRow t y).
Proof. intro y. exact (get_t4_all ht _). Qed.

Lemma build_ev_valid (ny : N) (fO : N -> MEnt) (hfO : forall z, MEntValid (2 * ny - 1) (fO z))
  (dP : DEnt) (hdP : DEntValid dP) :
  forall (cnt : nat) (y : N) (fe : list MEnt),
    Forall (MEntValid (2 * ny - 2)) fe ->
    Forall (MEntValid (2 * ny)) (build_ev cnt y ny (2 * ny) fe fO dP).
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
      cbn [MEntValid]; rewrite (big_inc_spec (de_m dP)).
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
      cbn [MEntValid]; rewrite (big_inc_spec (de_m dP)).
      split; [clear; lia |].
      replace (2 * ny) with (2 * y + 2) by (clear - hy_ny1; lia).
      exact (LCellSpec_x2 y (de_dx dP) (de_dy dP) (big_to_N (de_m dP)) hy1 hd_val).
  - destruct he1 as [hm1 hl1].
    destruct ((my =? y) && (2 * y + 3 <=? 2 * ny)) eqn:hc; [| exact I].
    apply andb_prop in hc; destruct hc as [hmy hx3].
    apply N.eqb_eq in hmy; apply N.leb_le in hx3; subst my.
    pose proof (hfO py1) as he2.
    destruct (fO py1) as [| my2 pk2 py2 | my2 pk2 py2 m2]; [exact I | |].
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; cbn [MEntValid] in he2 |- *.
      split; [exact hm1 |].
      replace (big_to_N m1) with (big_to_N m1 + 0) by (clear; lia).
      exact (LCellSpec_bulk (2 * ny) y py1 (big_to_N m1) py2 0 hx3 hl1 he2).
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; destruct he2 as [hm2 hl2].
      cbn [MEntValid]; rewrite (big_add_c_spec m1 false m2).
      replace (big_to_N m1 + big_to_N m2 + 0) with (big_to_N m1 + big_to_N m2) by (clear; lia).
      split; [clear - hm1; lia |].
      exact (LCellSpec_bulk (2 * ny) y py1 (big_to_N m1) py2 (big_to_N m2) hx3 hl1 hl2).
Qed.

Lemma build_od_valid (ny : N) (hny : 1 <= ny) (fEv : N -> MEnt) (hfEv : forall z, MEntValid (2 * ny) (fEv z))
  (dP : DEnt) (hdP : DEntValid dP) :
  forall (cnt : nat) (y : N) (fo : list MEnt),
    Forall (MEntValid (2 * ny - 1)) fo ->
    Forall (MEntValid (2 * ny + 1)) (build_od cnt y ny (2 * ny + 1) fo fEv dP).
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
    pose proof (hfEv (de_dy dP)) as he2.
    destruct (fEv (de_dy dP)) as [| my2 pk2 py2 | my2 pk2 py2 m2]; [exact I | |].
    + destruct (my2 =? de_dy dP) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; cbn [MEntValid] in he2 |- *.
      rewrite (big_inc_spec (de_m dP)).
      split; [clear; lia |].
      replace (big_to_N (de_m dP) + 1) with (big_to_N (de_m dP) + 1 + 0) by (clear; lia).
      exact (LCellSpec_x1 y (de_dx dP) (de_dy dP) (big_to_N (de_m dP)) py2 0 hy1 hd_val he2).
    + destruct (my2 =? de_dy dP) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; destruct he2 as [hm2 hl2].
      cbn [MEntValid]; rewrite (big_add_c_spec (de_m dP) true m2).
      split; [clear; lia |].
      replace (big_to_N (de_m dP) + big_to_N m2 + 1) with (big_to_N (de_m dP) + 1 + big_to_N m2) by (clear; lia).
      exact (LCellSpec_x1 y (de_dx dP) (de_dy dP) (big_to_N (de_m dP)) py2 (big_to_N m2) hy1 hd_val hl2).
  - exact I.
  - destruct he1 as [hm1 hl1].
    destruct ((my =? y) && (2 * y + 3 <=? 2 * ny + 1)) eqn:hc; [| exact I].
    apply andb_prop in hc; destruct hc as [hmy hx3].
    apply N.eqb_eq in hmy; apply N.leb_le in hx3; subst my.
    pose proof (hfEv py1) as he2.
    replace (2 * ny - 1) with (2 * ny + 1 - 2) in hl1 by (clear - hny; lia).
    replace (2 * ny) with (2 * ny + 1 - 1) in he2 by (clear; lia).
    destruct (fEv py1) as [| my2 pk2 py2 | my2 pk2 py2 m2]; [exact I | |].
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; cbn [MEntValid] in he2 |- *.
      split; [exact hm1 |].
      replace (big_to_N m1) with (big_to_N m1 + 0) by (clear; lia).
      exact (LCellSpec_bulk (2 * ny + 1) y py1 (big_to_N m1) py2 0 hx3 hl1 he2).
    + destruct (my2 =? py1) eqn:hmy2; [| exact I].
      apply N.eqb_eq in hmy2; subst my2; destruct he2 as [hm2 hl2].
      cbn [MEntValid]; rewrite (big_add_c_spec m1 false m2).
      replace (big_to_N m1 + big_to_N m2 + 0) with (big_to_N m1 + big_to_N m2) by (clear; lia).
      split; [clear - hm1; lia |].
      exact (LCellSpec_bulk (2 * ny + 1) y py1 (big_to_N m1) py2 (big_to_N m2) hx3 hl1 hl2).
Qed.

Definition DPStateValid (st : DPState) : Prop :=
  2 <= dps_ny st /\
  Forall (MEntValid (2 * dps_ny st - 2)) (dps_fe_l st) /\
  Forall (MEntValid (2 * dps_ny st - 1)) (dps_fo_l st) /\
  t4_all (MEntValid (2 * dps_ny st - 1)) (dps_fo_t st) /\
  DEntValid (dps_dP st) /\
  DEntValid (dps_dC st) /\
  t8_all RowValid (dps_ltab st) /\
  t4_all DEntValid (dps_dtab st).

Lemma run_dp_valid n st : DPStateValid st -> DPStateValid (run_dp n st).
Proof.
  revert st. induction n as [|n IH]; intros st hst; [exact hst |].
  cbn [run_dp]; cbv zeta.
  destruct hst as [hny [hfe_l [hfo_l [hfo_t [hdP [hdC [hltab hdtab]]]]]]].
  set (ny := dps_ny st) in *.
  pose proof (build_ev_valid ny _ (readRow_valid hfo_t) _ hdP
    (S (dps_ny_nat st)) 0 (dps_fe_l st) hfe_l) as hfev_l.
  pose proof (pack_t4_all (I : MEntValid (2*ny) mnone) hfev_l) as hfev_t.
  set (fev_l := build_ev (S (dps_ny_nat st)) 0 ny (2*ny) (dps_fe_l st)
    (readRow (dps_fo_t st)) (dps_dP st)) in *.
  set (fev_t := packRow fev_l) in *.
  pose proof (proj2 (forall_hd_tl (I : MEntValid (2*ny-1) mnone) hfo_l)) as hfo_tl.
  assert (hny1 : 1 <= ny) by lia.
  pose proof (build_od_valid ny hny1 _ (readRow_valid hfev_t) _ hdP
    (dps_ny_nat st) 1 (tl (dps_fo_l st)) hfo_tl) as hfod_tl.
  assert (hfod_hd : MEntValid (2*ny+1) (firstOdd ny)).
  { cbn [firstOdd MEntValid]. rewrite count_1. split; [lia | exact (LCellSpec_y0_odd ny)]. }
  pose proof (Forall_cons _ hfod_hd hfod_tl) as hfod_l.
  set (fod_l := firstOdd ny :: build_od (dps_ny_nat st) 1 ny (2*ny+1) (tl (dps_fo_l st))
    (readRow fev_t) (dps_dP st)) in *.
  pose proof (pack_t4_all (I : MEntValid (2*ny+1) mnone) hfod_l) as hfod_t.
  set (fod_t := packRow fod_l) in *.
  change (t4_all (MEntValid (2*ny+1)) fod_t) in hfod_t.
  assert (hltab2 : t8_all RowValid
    (if ny mod 8 =? 1 then saveRow (saveRow (dps_ltab st) (2*ny) fev_t) (2*ny+1) fod_t
                      else dps_ltab st)).
  { destruct (ny mod 8 =? 1); [apply saveRow_valid; [apply saveRow_valid; eassumption | exact hfod_t] | exact hltab]. }
  set (dC := dps_dC st) in *.
  set (n0 := mkNib3 N00 N00 N00).
  lazymatch goal with
  | |- DPStateValid (match ?u with _ => _ end) => set (upd := u)
  end.
  assert (hupd : DEntValid (fst upd) /\ t4_all DEntValid (snd upd)).
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
    assert (hnm : big_to_N (big_add_c false (de_m dC) m) = big_to_N (de_m dC) + big_to_N m).
    { rewrite (big_add_c_spec (de_m dC) false m); clear; lia. }
    split.
    - intro; cbn [de_k de_dx de_dy de_m]; rewrite hnm; exact hd_next.
    - destruct (ny + 3 <? 4096); [| exact hdtab].
      apply t4_set_all; [exact hdtab |].
      intro; cbn [de_k de_dx de_dy de_m]; rewrite hnm; exact hd_next. }
  destruct upd as [dN dtab']; destruct hupd as [hdN hdtab'].
  apply IH.
  unfold DPStateValid; cbn [dps_ny dps_fe_l dps_fo_l dps_fo_t dps_dP dps_dC dps_ltab dps_dtab].
  replace (2 * (ny + 1) - 2) with (2 * ny) by (clear; lia).
  replace (2 * (ny + 1) - 1) with (2 * ny + 1) by (clear; lia).
  refine (conj _ (conj hfev_l (conj hfod_l (conj hfod_t (conj hdC (conj hdN (conj hltab2 hdtab'))))))).
  clear - hny; lia.
Qed.

Lemma dp_start_valid : DPStateValid dp_start.
Proof.
  assert (f0 : Forall (MEntValid 0) seed0).
  { constructor; [exact (LCellSpec_x0 0) | constructor]. }
  assert (f1 : Forall (MEntValid 1) seed1).
  { constructor; [| constructor]. cbn [seed1 firstOdd MEntValid]. rewrite count_1.
    split; [lia | exact (LCellSpec_y0_odd 0)]. }
  assert (f2 : Forall (MEntValid 2) seed2).
  { constructor; [| constructor; [exact (LCellSpec_x0 1) | constructor]].
    cbn [MEntValid]. rewrite count_2. split; [lia | exact LCellSpec_y0_x2]. }
  pose proof DValid_base2 as d2.
  pose proof (LCellSpec_x1 1 1 0 1 0 2 (N.le_refl 1) d2 LCellSpec_y0_x2) as l31.
  pose proof (DValid_step d2 (LCellSpec_y0_odd 0)) as d3.
  pose proof (DValid_step d3 l31) as d4.
  assert (f3 : Forall (MEntValid 3) seed3).
  { constructor; [| constructor; [| constructor]]; cbn [firstOdd MEntValid].
    - rewrite count_1. split; [lia | exact (LCellSpec_y0_odd 1)].
    - rewrite count_4. split; [lia | exact l31]. }
  assert (g2 : DEntValid ds2) by (intro; exact d2).
  assert (g3 : DEntValid ds3) by (intro; exact d3).
  assert (g4 : DEntValid ds4) by (intro; exact d4).
  unfold dp_start, DPStateValid; cbn [fold_left dps_ny dps_fe_l dps_fo_l dps_fo_t dps_dP dps_dC dps_ltab dps_dtab].
  refine (conj (N.le_refl 2) (conj f2 (conj f3 (conj _ (conj g3 (conj g4 (conj _ _))))))).
  - exact (pack_t4_all (I : MEntValid 3 mnone) f3).
  - apply saveRow_valid; [apply saveRow_valid; [apply saveRow_valid; [apply saveRow_valid |] |] |].
    + split; apply t4_const_all; exact I.
    + exact (pack_t4_all (I : MEntValid 0 mnone) f0).
    + exact (pack_t4_all (I : MEntValid 1 mnone) f1).
    + exact (pack_t4_all (I : MEntValid 2 mnone) f2).
    + exact (pack_t4_all (I : MEntValid 3 mnone) f3).
  - apply t4_set_all; [apply t4_set_all; [apply t4_set_all | exact g3] | exact g4].
    + apply t4_const_all. unfold DEntValid. discriminate.
    + exact g2.
Qed.

(* Retain every eighth pair of layers, then solve a cell from at most
   sixteen preceding widths.  build_ev/build_od also serve as one-cell
   recurrences; unfold no unrelated entries. *)
Definition rowWidth (ny : N) (odd : bool) := 2 * ny + (if odd then 1 else 0).
Definition getD (dt : T4096 DEnt) (k : N) := get_t4 dt (N_to_nib3 k).

Fixpoint resolve (lim : nat) (ck : Checkpoints) (dt : T4096 DEnt)
  (ny : N) (odd : bool) (y : N) : MEnt :=
  let W := rowWidth ny odd in
  if ny <? y then mnone else
  match t8_get ck W with
  | Some (W', row) => if W =? W' then get_t4 row (N_to_nib3 y) else mnone
  | None =>
    match lim with
    | O => mnone
    | S lim' =>
      if ny <? 2 then mnone else
      let prev := resolve lim' ck dt (ny-1) odd y in
      let dp := getD dt (ny+1) in
      if odd then
        if y =? 0 then firstOdd ny else
        hd mnone (build_od 1%nat y ny (2*ny+1) [prev]
          (resolve lim' ck dt ny false) dp)
      else
        hd mnone (build_ev 1%nat y ny (2*ny) [prev]
          (resolve lim' ck dt (ny-1) true) dp)
    end
  end.

Lemma firstOdd_valid ny : MEntValid (2*ny+1) (firstOdd ny).
Proof.
  cbn [firstOdd MEntValid]. rewrite count_1. split; [lia | apply LCellSpec_y0_odd].
Qed.

Lemma resolve_valid ck dt (hc : t8_all RowValid ck) (hdp : t4_all DEntValid dt) :
  forall lim ny odd y, MEntValid (rowWidth ny odd) (resolve lim ck dt ny odd y).
Proof.
  induction lim as [|lim IH]; intros ny odd y; cbn [resolve];
    destruct (ny <? y); try exact I.
  all: pose proof (t8_get_all hc (rowWidth ny odd)) as hrow;
    destruct (t8_get ck (rowWidth ny odd)) as [[w row]|]; try exact I.
  1,2: destruct (rowWidth ny odd =? w) eqn:hw; [apply N.eqb_eq in hw; subst w; exact (get_t4_all hrow _) | exact I].
  destruct (ny <? 2) eqn:hny; [exact I |]. apply N.ltb_ge in hny.
  pose proof (get_t4_all hdp (N_to_nib3 (ny+1))) as hD.
  destruct odd; cbn [rowWidth] in *; rewrite ?N.add_0_r in *.
  - destruct (y =? 0); [apply firstOdd_valid |].
    assert (hp : MEntValid (2*ny-1) (resolve lim ck dt (ny-1) true y)).
    { replace (2*ny-1) with (rowWidth (ny-1) true) by (unfold rowWidth; lia). apply IH. }
    assert (hq : forall z, MEntValid (2*ny) (resolve lim ck dt ny false z)).
    { intros z. specialize (IH ny false z).
      change (MEntValid (2*ny+0) (resolve lim ck dt ny false z)) in IH.
      now rewrite N.add_0_r in IH. }
    exact (proj1 (forall_hd_tl (I : MEntValid (2*ny+1) mnone)
      (build_od_valid ny ltac:(lia) _ hq _ hD 1%nat y _ (Forall_cons _ hp (Forall_nil _))))).
  - assert (hp : MEntValid (2*ny-2) (resolve lim ck dt (ny-1) false y)).
    { replace (2*ny-2) with (rowWidth (ny-1) false) by (unfold rowWidth; lia). apply IH. }
    assert (hq : forall z, MEntValid (2*ny-1) (resolve lim ck dt (ny-1) true z)).
    { intros z. replace (2*ny-1) with (rowWidth (ny-1) true) by (unfold rowWidth; lia). apply IH. }
    replace (rowWidth ny false) with (2*ny) by (unfold rowWidth; lia).
    exact (proj1 (forall_hd_tl (I : MEntValid (2*ny) mnone)
      (build_ev_valid ny _ hq _ hD 1%nat y _ (Forall_cons _ hp (Forall_nil _))))).
Qed.

Definition LQuery := N -> N -> option (N * N).
Definition LQueryValid (f : LQuery) := forall W y py m, f W y = Some (py,m) -> LCellSpec W y py m.

Definition lookupFrom ck dt : LQuery :=
  fun W y =>
  if (W <? 8192) && (y <? 4096) then
    match resolve 16%nat ck dt (N.div2 W) (N.odd W) y with
    | mnone => None
    | mzero my _ py => if my =? y then Some (py,0) else None
    | mpos my _ py m => if my =? y then Some (py,big_to_N m) else None
    end
  else None.

Lemma lookupFrom_valid ck dt (hc : t8_all RowValid ck) (hdp : t4_all DEntValid dt) :
  LQueryValid (lookupFrom ck dt).
Proof.
  intros W y py m h. unfold lookupFrom in h.
  destruct ((W <? 8192) && (y <? 4096)); [| discriminate].
  pose proof (resolve_valid ck dt hc hdp 16%nat (N.div2 W) (N.odd W) y) as hf.
  assert (hw : rowWidth (N.div2 W) (N.odd W) = W).
  { unfold rowWidth. pose proof (N.div2_odd W) as hdiv.
    destruct (N.odd W); cbn [N.b2n] in hdiv |- *; lia. }
  rewrite hw in hf.
  destruct (resolve 16%nat ck dt (N.div2 W) (N.odd W) y) as [|my ? out|my ? out n]; try discriminate.
  all: destruct (my =? y) eqn:hy; [apply N.eqb_eq in hy; subst my | discriminate];
    injection h as <- <-; first [exact hf | exact (proj2 hf)].
Qed.

Definition init_and_run_dp : LQuery * T4096 DEnt :=
  let st := run_dp 2291%nat dp_start in
  let dt := dps_dtab st in (lookupFrom (dps_ltab st) dt, dt).

Local Opaque run_dp.
Lemma init_and_run_dp_valid :
  let '(ltab,dtab) := init_and_run_dp in LQueryValid ltab /\ t4_all DEntValid dtab.
Proof.
  unfold init_and_run_dp. pose proof (run_dp_valid 2291 dp_start dp_start_valid) as h.
  destruct h as [_ [_ [_ [_ [_ [_ [hc hd]]]]]]].
  exact (conj (lookupFrom_valid _ _ hc hd) hd).
Qed.
Local Transparent run_dp.

Definition lookupD (dtab : T4096 DEnt) (k : N) : N * N * N :=
  if k <? 4096 then
    let e := get_t4 dtab (N_to_nib3 k) in
    if de_ok e && (de_k e =? k) then (de_dx e, de_dy e, big_to_N (de_m e)) else (0, 0, 0)
  else (0, 0, 0).

Definition exhaust01StepL (ltab : LQuery) (cur : Stalled) (acc : N) : option StAcc :=
  match cur with
  | Scanon1 x y _ | ScanonZ x y =>
    let W := x + 2 * y in
    match ltab W y with
    | None => None
    | Some (py, m) => Some (applyDeltaM cur (W + 2 - 2 * py) py m acc)
    end
  | _ => None
  end.

Fixpoint exhaust01LoopPos (ltab : LQuery) (p : positive) (cur : Stalled) (acc : N) : option StAcc :=
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

Definition exhaust01LoopL (ltab : LQuery) (c : N) (cur : Stalled) (acc : N) : option StAcc :=
  match c with
  | N0 => Some (mkStAcc cur acc)
  | Npos p => exhaust01LoopPos ltab p cur acc
  end.

Definition tryDirectCanon (ltab : LQuery) (dtab : T4096 DEnt) (cur : Stalled) (x y c acc : N) : option StAcc :=
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
          match ltab Wq (k2 - 2) with
          | Some (py, m) => if 2 * py <? Wq + 1 then if vmD + 2 <=? m then Some (applyDeltaM cur (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc) else None else None
          | None => None
          end
        else None
    else
      let k2 := (W + 1) / 2 in
      let '(dx, dy, vmD) := lookupD dtab k2 in
      if (2 <=? k2) && (dx + 2 =? x) && (dy =? y) && negb (vmD =? 0) then
        let Wq := 2 * k2 - 2 + 2 * c in
        match ltab Wq (k2 - 2) with
        | Some (py, m) => if 2 * py <? Wq + 1 then if vmD + 2 <=? m then Some (applyDeltaM cur (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc) else None else None
        | None => None
        end
      else None
  else
    let k1 := (W + 2) / 2 in
    let '(dx, dy, vmD) := lookupD dtab k1 in
    if (2 <=? k1) && negb (vmD =? 0) && (dx + 1 =? x) && (dy =? y) then
      let Wq := 2 * k1 - 3 + 2 * c in
      match ltab Wq (k1 - 1) with
      | Some (py, m) => if (vmD + 2 <=? m) && (2 * py <? Wq + 1) then Some (applyDeltaM cur (Wq + 1 - 2 * py) py (m - (vmD + 1)) acc) else None
      | None => None
      end
    else None.

Definition exhaust01AddOnes (ltab : LQuery) (dtab : T4096 DEnt) (cur : Stalled) (c acc : N) : option StAcc :=
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

Fixpoint exhaust01Fold (ltab : LQuery) (dtab : T4096 DEnt) (cur : Stalled) (seg : UList) (acc : N) : option StAcc :=
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

Definition exhaustBandStep (ltab : LQuery) (dtab : T4096 DEnt) (st : option (UList * N)) : StepRes (option (UList * N)) :=
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

Definition exhaustAnyBand (ltab : LQuery) (dtab : T4096 DEnt) (p : positive) (u : UList) (acc : N) : option (UList * N) :=
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

Definition stepMacro (ltab : LQuery) (dtab : T4096 DEnt) (s : CoreState) : CoreState :=
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

Definition stepMacro_step (ltab : LQuery) (dtab : T4096 DEnt) (s : CoreState) : StepRes CoreState :=
  match s with
  | Chalt l r => mkStepRes true (Chalt l r)
  | _ => mkStepRes false (stepMacro ltab dtab s)
  end.

Definition cert_check_fuel (fuel : positive) (dp : LQuery * T4096 DEnt) : bool :=
  let '(ltab, dtab) := dp in
  match sr_val (runPos fuel (stepMacro_step ltab dtab) (Crun mB [Lo 0] [])) with
  | Chalt _ _ => true
  | _ => false
  end.

Notation cert_check := (cert_check_fuel 1000000%positive init_and_run_dp).


(* ========================================================================= *)
(* Section 5b: Soundness of Lookup, Exhaustion, Scanner, Macro, and Halting  *)
(* ========================================================================= *)

Lemma lookupD_sound {dtab : T4096 DEnt} (hdtab : t4_all DEntValid dtab) (k : N) :
  let '(dx, dy, vmD) := lookupD dtab k in
  vmD <> 0 -> DValid k dx dy vmD.
Proof.
  unfold lookupD; cbv zeta.
  destruct (k <? 4096); [| intro hne; exfalso; exact (hne eq_refl)].
  pose proof (get_t4_all hdtab (N_to_nib3 k)) as he.
  set (e := get_t4 dtab (N_to_nib3 k)) in *; clearbody e.
  destruct (de_ok e && (de_k e =? k)) eqn:hok; [| intro hne; exfalso; exact (hne eq_refl)].
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

Lemma exhaust01StepL_sound {ltab : LQuery} (hltab : LQueryValid ltab)
  (cur : Stalled) (acc : N) (r : StAcc)
  (hv : stValid cur)
  (h : exhaust01StepL ltab cur acc = Some r) :
  acc <= sa_acc r /\ stValid (sa_st r) /\
  PsiReach (sa_acc r - acc) (uappend (toU cur) (upush 1 1 Unil)) (toU (sa_st r)).
Proof.
  assert (hcur : exists x y,
            (cur = ScanonZ x y \/ exists p, cur = Scanon1 x y p) /\
            match ltab (x + 2 * y) y with
            | None => None
            | Some (py, m) => Some (applyDeltaM cur (x + 2 * y + 2 - 2 * py) py m acc)
            end = Some r).
  { destruct cur as [| | | x y p | x y]; try discriminate;
      [exists x, y; split; [right; exists p; reflexivity | exact h]
      | exists x, y; split; [left; reflexivity | exact h]]. }
  clear h; destruct hcur as [x [y [hcur h]]].
  destruct (ltab (x + 2 * y) y) as [[py m] |] eqn:hlk; [| discriminate].
  injection h as hr; subst r.
  pose proof (hltab (x + 2 * y) y py m hlk) as hl.
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

Lemma exhaust01LoopPos_sound {ltab : LQuery} (hltab : LQueryValid ltab)
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

Lemma exhaust01LoopL_sound {ltab : LQuery} (hltab : LQueryValid ltab)
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

Lemma tryDirectCanon_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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
         match ltab Wq (k2 - 2) with
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
      destruct (ltab Wq (k2 - 2)) as [[py m] |] eqn:hlk; [| discriminate].
      destruct (2 * py <? Wq + 1) eqn:hpy; [| discriminate].
      destruct (vmD + 2 <=? m) eqn:hm; [| discriminate].
      apply N.ltb_lt in hpy; apply N.leb_le in hm.
      injection hk2 as hr; subst r.
      pose proof (hltab Wq (k2 - 2) py m hlk) as hl.
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
    destruct (ltab Wq (k1 - 1)) as [[py m] |] eqn:hlk; [| discriminate].
    destruct ((vmD + 2 <=? m) && (2 * py <? Wq + 1)) eqn:hok; [| discriminate].
    apply andb_prop in hok; destruct hok as [hm hpy].
    apply N.leb_le in hm; apply N.ltb_lt in hpy.
    injection h as hr; subst r.
    pose proof (hltab Wq (k1 - 1) py m hlk) as hl.
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

Lemma exhaust01AddOnes_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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

Lemma exhaust01Fold_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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

Lemma exhaustBandStep_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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

Lemma exhaustAnyBand_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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

Lemma exhaustAnyBand_0_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
  (p : positive) (us u_end : UList) (nmax : N)
  (h : exhaustAnyBand ltab dtab p us 0 = Some (u_end, nmax)) :
  PsiReach nmax us u_end.
Proof.
  destruct (exhaustAnyBand_sound hltab hdtab p us u_end 0 nmax h) as [_ hp].
  replace (nmax - 0) with nmax in hp by (clear; lia).
  exact hp.
Qed.

Lemma stepMacro_mD_Ro_sc_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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

Lemma stepMacro_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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

Lemma stepMacro_step_sound {ltab : LQuery} {dtab : T4096 DEnt}
  (hltab : LQueryValid ltab)
  (hdtab : t4_all DEntValid dtab)
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

Lemma finish_dp_fuel (fuel : positive) (dp : LQuery * T4096 DEnt)
  (hdp : let '(ltab, dtab) := dp in LQueryValid ltab /\ t4_all DEntValid dtab)
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
Proof. native_check_eq. Qed.

Lemma halt_internal : halts tm c0.
Proof. exact (halt_internal_from_cert cert_ok). Qed.

End Internal.

Theorem halt : halts tm c0.
Proof. exact Internal.halt_internal. Qed.
