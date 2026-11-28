(** One sweep of the map at a time, with the affine stretches it stays on.
    Everything here is sound whatever the untrusted division [adiv] returns; see the [_spec] lemmas. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Num Big Map.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

(** ** The letters of the map, in Z *)
Lemma L_D a b : a + 3 < b -> aStep a b = Some (2*a+6, b-a-3, -30*a+18).
Proof.
  intros H. unfold aStep. destruct (Z.eqb_spec b (a+3)); [lia|]. destruct (Z.ltb_spec (a+3) b); [reflexivity|lia].
Qed.
Lemma L_tail a b : b < a + 3 -> aStep a b =
  if b =? 1 then
    if a mod 4 =? 2 then Some (6, a+7, 2*a*a+39*a+354)
    else Some (22, a-2, 2*a*a+39*a+250)
  else if b =? 3 then
    if a mod 4 =? 2 then Some (6, a+13, 2*a*a+63*a+774)
    else Some (a+8, 2, a+136)
  else if b mod 2 =? 1 then
    if b =? a+1 then Some (6, a+b+2, 8*a*a+30*a+174)
    else if (a-b+5) mod 4 =? 2 then Some (a-b+11, 2*b-4, 4*b*(a+b)-11*a+29*b+13)
    else Some (a-b+19, 2*b-8, 4*b*(a+b)-19*a+37*b-29)
  else if (a-b) mod 4 =? 2 then Some (6, a+b+7, 2*a*a+6*b*b+39*a-9*b+378)
  else Some (22, a+b-2, 2*a*a+6*b*b+39*a-9*b+274).
Proof.
  intros H. unfold aStep. destruct (Z.eqb_spec b (a+3)); [lia|]. destruct (Z.ltb_spec (a+3) b); [lia|reflexivity].
Qed.

Lemma Reach_snoc a0 B a b n r a' b' r1 : Reach a0 B a b n r -> aStep a b = Some (a', b', r1) -> Reach a0 B a' b' (n+1) (r+r1).
Proof.
  intros H S. eapply Reach_trans; [exact H|]. replace 1 with (1+0) by ring. replace r1 with (r1+0) by ring.
  econstructor; [exact S|constructor].
Qed.

(** ** Levels: the state after a prefix of letters, affine in the start [B'] along one residue class mod 4 *)
Record Lev := mkLev { la : W; lga : W; lc : W; lbase : W; lhi : W; lU0 : W; lU1 : W; lW0 : W; lW1 : W; llen : W }.

Definition Aat (L : Lev) (y : Z) := val (la L) + val (lga L) * y.
Definition Rat (L : Lev) (B' y : Z) := 4 * B' * (val (lU0 L) + val (lU1 L) * y) + (val (lW0 L) + val (lW1 L) * y).

Definition lev_fits (L : Lev) : bool :=
  fits (la L) && fits (lga L) && fits (lc L) && fits (lbase L) && fits (lhi L)
  && fits (lU0 L) && fits (lU1 L) && fits (lW0 L) && fits (lW1 L) && fits (llen L).

Definition lev_ok (a0 : Z) (L : Lev) : Prop :=
  lev_fits L = true /\
  forall B', val (lbase L) <= B' <= val (lhi L) -> (B' - val (lbase L)) mod 4 = 0 ->
    Reach a0 B' (Aat L (B' - val (lbase L))) (B' + val (lc L) - Aat L (B' - val (lbase L))) (val (llen L))
      (Rat L B' (B' - val (lbase L))).

(** ** A whole sweep from a reset state, over a range of starts *)
Record Sum := mkSum { sbase : W; shi : W; sdelta : W; sna0 : W; slen : W; sU0 : W; sU1 : W; sW0 : W; sW1 : W;
                      sae : W; sgae : W; sbe : W; sgbe : W; sca : int; scb : int }.

Definition sum_cost (S : Sum) (B' y : Z) :=
  4 * B' * (val (sU0 S) + val (sU1 S) * y) + (val (sW0 S) + val (sW1 S) * y)
  + phi (sca S) * ((val (sae S) + val (sgae S) * y) * (val (sae S) + val (sgae S) * y))
  + phi (scb S) * ((val (sbe S) + val (sgbe S) * y) * (val (sbe S) + val (sgbe S) * y)).

Definition sum_ok (a0 : Z) (S : Sum) : Prop :=
  forall B', val (sbase S) <= B' <= val (shi S) -> (B' - val (sbase S)) mod 4 = 0 ->
    Reach a0 B' (val (sna0 S)) (B' + val (sdelta S)) (val (slen S)) (sum_cost S B' (B' - val (sbase S))).

(** ** Untrusted division: only a suggestion, verified by multiplying back *)
Definition shr (x : W) (e : int) : W :=
  mkW (hi x >> e)%uint63 ((lo x >> e) lor (hi x << (63 - e)))%uint63.

Definition adiv_slow (g m : W) : W :=
  if (hi m =? 0)%uint63 then
    let d := lo m in
    if (hi g =? 0)%uint63 then mkW 0%uint63 (lo g / d)%uint63
    else if (hi g <? d)%uint63 then
      let (q, _) := diveucl_21 (hi g) (lo g) d in mkW 0%uint63 q
    else
      let (qh, r) := diveucl (hi g) d in
      let (ql, _) := diveucl_21 r (lo g) d in mkW qh ql
  else
    let e := (64 - head0 (hi m))%uint63 in
    let d := (lo (shr m e) + 1)%uint63 in
    let g' := shr g e in
    let q0 := if (hi g' =? 0)%uint63 then (lo g' / d)%uint63
              else if (hi g' <? d)%uint63 then fst (diveucl_21 (hi g') (lo g') d) else 0%uint63 in
    let q := mkW 0%uint63 q0 in
    match mul_nn m q with
    | Some p => if leb m (sub g p) then add q (wc 1%uint63) else q
    | None => q
    end.

Definition adiv : W -> W -> W := adiv_slow.

(** The new end of the range for a guard [g + sl * y >= 0]. *)
Definition bnd (h B g sl : W) : W :=
  if is_neg sl then
    let m := neg sl in
    if ltb g m then B else
    let q := adiv g m in
    match mul_nn m q with
    | Some p => if leb p g then wmin h (add B q) else B
    | None => B
    end
  else h.

Notation P122 := 5316911983139663491615228241121378304%Z.

Lemma bnd_spec h B g sl :
  -P122 <= val h < P122 -> -P122 <= val B < P122 -> -P122 <= val g < P122 -> -P122 <= val sl < P122 ->
  val B <= val h -> 0 <= val g ->
  val B <= val (bnd h B g sl) <= val h /\
  forall y, 0 <= y <= val (bnd h B g sl) - val B -> 0 <= val g + val sl * y.
Proof.
  intros Bh BB Bg Bs Le G. unfold bnd.
  destruct (is_neg sl) eqn:N.
  2:{ assert (N' : 0 <= val sl).
      { destruct (Z.le_gt_cases 0 (val sl)) as [X|X]; [exact X|]. apply is_neg_spec in X. congruence. }
      split; [lia|]. intros y Hy. nia. }
  apply is_neg_spec in N. cbv zeta.
  assert (Vm : val (neg sl) = - val sl) by (apply val_neg; lia).
  destruct (ltb g (neg sl)) eqn:Lt.
  { split; [lia|]. intros y Hy. assert (y = 0) by lia. subst y. lia. }
  destruct (mul_nn (neg sl) (adiv g (neg sl))) as [p|] eqn:M.
  2:{ split; [lia|]. intros y Hy. assert (y = 0) by lia. subst y. lia. }
  destruct (mul_nn_spec _ _ _ M) as [Ep Bp].
  set (q := adiv g (neg sl)) in *.
  destruct (leb p g) eqn:Lp.
  2:{ split; [lia|]. intros y Hy. assert (y = 0) by lia. subst y. lia. }
  apply leb_spec_W in Lp. rewrite Vm in Ep.
  assert (Q0 : 0 <= val q) by nia.
  assert (Q1 : val q <= val g) by nia.
  assert (Va : val (add B q) = val B + val q) by (apply val_add; lia).
  rewrite val_wmin, Va. split; [lia|].
  intros y Hy. assert (y <= val q) by lia. nia.
Qed.
