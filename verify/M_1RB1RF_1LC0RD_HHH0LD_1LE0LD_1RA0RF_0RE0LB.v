(** * 1RB1RF_1LC0RD_---0LD_1LE0LD_1RA0RF_0RE0LB Non-Halting Proof *)

From BusyCoq Require Import Individual62.
From Coq Require Import String List Bool Arith PeanoNat Lia.
From Coq Require Import Lists.Streams.
Import ListNotations.
Close Scope sym.
Open Scope nat_scope.
Set Default Goal Selector "!".

Definition tm : TM := TM_from_str "1RB1RF_1LC0RD_---0LD_1LE0LD_1RA0RF_0RE0LB"%string.

Local Arguments Nat.div : simpl never.
Local Arguments Nat.modulo : simpl never.

Ltac pose_dm x k :=
  lazymatch goal with
  | _ : x = k * (x / k) + x mod k |- _ => fail
  | _ =>
    pose proof (Nat.div_mod x k ltac:(lia));
    pose proof (Nat.mod_upper_bound x k ltac:(lia))
  end.

Ltac dlia :=
  repeat match goal with
  | |- context [?x / ?k] =>
    lazymatch k with S _ => pose_dm x k end
  | |- context [?x mod ?k] =>
    lazymatch k with S _ => pose_dm x k end
  | H : context [?x / ?k] |- _ =>
    lazymatch k with S _ => pose_dm x k end
  | H : context [?x mod ?k] |- _ =>
    lazymatch k with S _ => pose_dm x k end
  end;
  lia.

Notation s0inf := (@const sym S0).

Lemma zero_cons_default : @Cons sym S0 s0inf = s0inf.
Proof. symmetry. apply (@const_unfold sym S0). Qed.

Ltac norm_s0 :=
  change BB62.Sym with sym in *;
  repeat rewrite zero_cons_default in *.

Lemma mod2_cases (x : nat) :
  (x mod 2 = 0 /\ (x mod 2 =? 0) = true) \/
  (x mod 2 = 1 /\ (x mod 2 =? 0) = false).
Proof.
  pose proof (Nat.mod_upper_bound x 2 ltac:(lia)).
  destruct (x mod 2) as [| [| ?]]; [left; split; reflexivity | right; split; reflexivity | lia].
Qed.

(* ========================================================================== *)
(* Section 2: Macro Rules, Round, Sweeps, EraRound                            *)
(* ========================================================================== *)

Lemma rule_B_000 (l r : side) :
  (l {{E}}> ([S0; S0; S0] *> r)) -[ tm ]->+ (l <{{D}} ([S0; S0; S1] *> r)).
Proof. start_progress. Qed.

Lemma rule_B_0011 (l r : side) :
  (l {{E}}> ([S0; S0; S1; S1] *> r)) -[ tm ]->+ (l <{{D}} ([S0; S1; S0; S0] *> r)).
Proof. start_progress. Qed.

Lemma rule_B_00100 (l r : side) :
  (l {{E}}> ([S0; S0; S1; S0; S0] *> r)) -[ tm ]->+ ((l <* [S0; S1; S1; S1; S1]) {{E}}> r).
Proof. start_progress. Qed.

Lemma rule_B_001010 (l r : side) :
  (l {{E}}> ([S0; S0; S1; S0; S1; S0] *> r)) -[ tm ]->+ ((l <* [S0; S1; S1; S1; S1; S1]) {{E}}> r).
Proof. start_progress. Qed.

Lemma rule_B_0010110 (l r : side) :
  (l {{E}}> ([S0; S0; S1; S0; S1; S1; S0] *> r)) -[ tm ]->+ ((l <* [S0; S1; S1; S1; S1; S1; S1]) {{E}}> r).
Proof. start_progress. Qed.

Lemma rule_B_010 (l r : side) :
  (l {{E}}> ([S0; S1; S0] *> r)) -[ tm ]->+ ((l <* [S0; S1; S1]) {{E}}> r).
Proof. start_progress. Qed.

Lemma rule_B_0110 (l r : side) :
  (l {{E}}> ([S0; S1; S1; S0] *> r)) -[ tm ]->+ ((l <* [S0; S1; S1; S1]) {{E}}> r).
Proof. start_progress. Qed.

Lemma rule_B_10 (l r : side) :
  (l {{E}}> ([S1; S0] *> r)) -[ tm ]->+ ((l <* [S0; S0]) {{E}}> r).
Proof. start_progress. Qed.

Lemma rule_E_01111 (l r : side) :
  ((l <* [S0; S1; S1; S1; S1]) <{{D}} r) -[ tm ]->+ (l <{{D}} ([S0; S0; S0; S1; S0] *> r)).
Proof. start_progress. Qed.

Lemma rule_E_011111 (l r : side) :
  ((l <* [S0; S1; S1; S1; S1; S1]) <{{D}} r) -[ tm ]->+ (l <{{D}} ([S0; S0; S0; S0; S1; S0] *> r)).
Proof. start_progress. Qed.

Lemma rule_E_0111111 (l r : side) :
  ((l <* [S0; S1; S1; S1; S1; S1; S1]) <{{D}} r) -[ tm ]->+ (l <{{D}} ([S0; S0; S0; S0; S0; S1; S0] *> r)).
Proof. start_progress. Qed.

Lemma rule_E_011 (l r : side) :
  ((l <* [S0; S1; S1]) <{{D}} r) -[ tm ]->+ (l <{{D}} ([S0; S1; S0] *> r)).
Proof. start_progress. Qed.

Lemma rule_E_0111 (l r : side) :
  ((l <* [S0; S1; S1; S1]) <{{D}} r) -[ tm ]->+ (l <{{D}} ([S0; S0; S1; S0] *> r)).
Proof. start_progress. Qed.

Lemma rule_E_00 (l r : side) :
  ((l <* [S0; S0]) <{{D}} (S0 >> r)) -[ tm ]->+ ((l <* [S0; S1; S1]) {{E}}> r).
Proof. start_progress. Qed.

Lemma rule_E_nil (r : side) :
  (s0inf <{{D}} (S0 >> r)) -[ tm ]->+ ((s0inf <* [S0; S1; S1]) {{E}}> r).
Proof. start_progress. Qed.

Definition Round (r r' : side) : Prop :=
  forall l : side, (l {{E}}> r) -[ tm ]->+ (l <{{D}} r').

Inductive Sweeps : nat -> side -> side -> Prop :=
  | Sweeps_zero (r : side) : Sweeps 0 r r
  | Sweeps_succ {n : nat} {r r1 r2 : side} :
      Round r r1 -> Sweeps n r1 r2 -> Sweeps (S n) r r2.

Lemma Sweeps_trans {a b : nat} {r1 r2 r3 : side}
    (h1 : Sweeps a r1 r2) (h2 : Sweeps b r2 r3) : Sweeps (a + b) r1 r3.
Proof.
  induction h1 as [r | n r r1 r2 hr _ IH]; cbn [Nat.add].
  - exact h2.
  - exact (Sweeps_succ hr (IH h2)).
Qed.

Lemma round_000 (r : side) :
  Round ([S0; S0; S0] *> r) ([S0; S0; S1] *> r).
Proof. intro l. apply rule_B_000. Qed.

Lemma round_0011 (r : side) :
  Round ([S0; S0; S1; S1] *> r) ([S0; S1; S0; S0] *> r).
Proof. intro l. apply rule_B_0011. Qed.

Lemma round_00100 {r r' : side} (h : Round r r') :
  Round ([S0; S0; S1; S0; S0] *> r) ([S0; S0; S0; S1; S0] *> r').
Proof.
  intro l.
  eapply progress_trans; [apply rule_B_00100 |].
  eapply progress_trans; [apply h |].
  apply rule_E_01111.
Qed.

Lemma round_001010 {r r' : side} (h : Round r r') :
  Round ([S0; S0; S1; S0; S1; S0] *> r) ([S0; S0; S0; S0; S1; S0] *> r').
Proof.
  intro l.
  eapply progress_trans; [apply rule_B_001010 |].
  eapply progress_trans; [apply h |].
  apply rule_E_011111.
Qed.

Lemma round_0010110 {r r' : side} (h : Round r r') :
  Round ([S0; S0; S1; S0; S1; S1; S0] *> r) ([S0; S0; S0; S0; S0; S1; S0] *> r').
Proof.
  intro l.
  eapply progress_trans; [apply rule_B_0010110 |].
  eapply progress_trans; [apply h |].
  apply rule_E_0111111.
Qed.

Lemma round_010 {r r' : side} (h : Round r r') :
  Round ([S0; S1; S0] *> r) ([S0; S1; S0] *> r').
Proof.
  intro l.
  eapply progress_trans; [apply rule_B_010 |].
  eapply progress_trans; [apply h |].
  apply rule_E_011.
Qed.

Lemma round_0110 {r r' : side} (h : Round r r') :
  Round ([S0; S1; S1; S0] *> r) ([S0; S0; S1; S0] *> r').
Proof.
  intro l.
  eapply progress_trans; [apply rule_B_0110 |].
  eapply progress_trans; [apply h |].
  apply rule_E_0111.
Qed.

Lemma round_10 {r1 r r2 : side}
    (h1 : Round r1 (S0 >> r)) (h2 : Round r r2) :
  Round ([S1; S0] *> r1) ([S0; S1; S0] *> r2).
Proof.
  intro l.
  eapply progress_trans; [apply rule_B_10 |].
  eapply progress_trans; [apply h1 |].
  eapply progress_trans; [apply rule_E_00 |].
  eapply progress_trans; [apply h2 |].
  apply rule_E_011.
Qed.

(* ========================================================================== *)
(* Section 3: Fueled Bool-List Round Runner                                   *)
(* ========================================================================== *)

Lemma opt_map_some {A B : Type} {f : A -> B} {x : option A} {y : B}
    (h : option_map f x = Some y) : exists a, x = Some a /\ f a = y.
Proof.
  destruct x as [a |]; cbn in h; [inversion h; eauto | discriminate].
Qed.

Definition b2f (b : bool) : sym := if b then S1 else S0.

Fixpoint toTape (bs : list bool) : side :=
  match bs with
  | [] => s0inf
  | b :: bs' => b2f b >> toTape bs'
  end.

Definition pad7B (bs : list bool) : list bool :=
  bs ++ [false; false; false; false; false; false; false].

Lemma toTape_pad7B (bs : list bool) : toTape (pad7B bs) = toTape bs.
Proof.
  induction bs as [| b bs IH].
  - cbn [pad7B app toTape b2f]. norm_s0. reflexivity.
  - unfold pad7B in *. cbn [app toTape]. rewrite IH. reflexivity.
Qed.

Fixpoint dropTrailingFalse (bs : list bool) : list bool :=
  match bs with
  | [] => []
  | b :: bs' =>
    match dropTrailingFalse bs' with
    | [] => if b then [true] else []
    | rest => b :: rest
    end
  end.

Lemma toTape_dropTrailingFalse (bs : list bool) :
  toTape (dropTrailingFalse bs) = toTape bs.
Proof.
  induction bs as [| b bs IH]; [reflexivity |].
  cbn [dropTrailingFalse].
  destruct (dropTrailingFalse bs) as [| r rs] eqn:Hrest.
  - destruct b; cbn [toTape b2f]; rewrite <- IH; cbn [toTape];
    [reflexivity | symmetry; apply zero_cons_default].
  - cbn [toTape]. rewrite <- IH. reflexivity.
Qed.

Fixpoint roundBool (fuel : nat) (bs : list bool) : option (list bool) :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match pad7B bs with
    | false :: false :: false :: rest =>
      Some (false :: false :: true :: rest)
    | false :: false :: true :: true :: rest =>
      Some (false :: true :: false :: false :: rest)
    | false :: false :: true :: false :: false :: rest =>
      option_map (fun r' => false :: false :: false :: true :: false :: r') (roundBool fuel' rest)
    | false :: false :: true :: false :: true :: false :: rest =>
      option_map (fun r' => false :: false :: false :: false :: true :: false :: r') (roundBool fuel' rest)
    | false :: false :: true :: false :: true :: true :: false :: rest =>
      option_map (fun r' => false :: false :: false :: false :: false :: true :: false :: r') (roundBool fuel' rest)
    | false :: true :: false :: rest =>
      option_map (fun r' => false :: true :: false :: r') (roundBool fuel' rest)
    | false :: true :: true :: false :: rest =>
      option_map (fun r' => false :: false :: true :: false :: r') (roundBool fuel' rest)
    | true :: false :: rest =>
      match roundBool fuel' rest with
      | Some (false :: r1) => option_map (fun r2 => false :: true :: false :: r2) (roundBool fuel' r1)
      | _ => None
      end
    | _ => None
    end
  end.

Lemma roundBool_sound (fuel : nat) : forall (bs ys : list bool),
    roundBool fuel bs = Some ys -> Round (toTape bs) (toTape ys).
Proof.
  induction fuel as [| fuel IH]; intros bs ys h; [discriminate |].
  rewrite <- (toTape_pad7B bs).
  cbn [roundBool] in h.
  destruct (pad7B bs) as [| [|] l1]; [discriminate | |].
  - (* true :: l1 *)
    destruct l1 as [| [|] rest]; [discriminate | discriminate |].
    destruct (roundBool fuel rest) as [[| [|] r1] |] eqn:Hr1; try discriminate.
    apply opt_map_some in h as [r2 [Hr2 <-]].
    cbn [toTape b2f Str_app].
    exact (round_10 (IH rest (false :: r1) Hr1) (IH r1 r2 Hr2)).
  - (* false :: l1 *)
    destruct l1 as [| [|] l2]; [discriminate | |].
    + (* false :: true :: l2 *)
      destruct l2 as [| [|] l3]; [discriminate | |].
      * (* false :: true :: true :: l3 *)
        destruct l3 as [| [|] rest]; [discriminate | discriminate |].
        apply opt_map_some in h as [r' [Hr' <-]].
        cbn [toTape b2f Str_app].
        exact (round_0110 (IH rest r' Hr')).
      * (* false :: true :: false :: l3 *)
        apply opt_map_some in h as [r' [Hr' <-]].
        cbn [toTape b2f Str_app].
        exact (round_010 (IH l3 r' Hr')).
    + (* false :: false :: l2 *)
      destruct l2 as [| [|] l3]; [discriminate | |].
      * (* false :: false :: true :: l3 *)
        destruct l3 as [| [|] l4]; [discriminate | |].
        -- (* false :: false :: true :: true :: l4 *)
           inversion h; subst; clear h.
           cbn [toTape b2f Str_app].
           exact (round_0011 (toTape l4)).
        -- (* false :: false :: true :: false :: l4 *)
           destruct l4 as [| [|] l5]; [discriminate | |].
           ++ (* false :: false :: true :: false :: true :: l5 *)
              destruct l5 as [| [|] l6]; [discriminate | |].
              ** (* false :: false :: true :: false :: true :: true :: l6 *)
                 destruct l6 as [| [|] rest]; [discriminate | discriminate |].
                 apply opt_map_some in h as [r' [Hr' <-]].
                 cbn [toTape b2f Str_app].
                 exact (round_0010110 (IH rest r' Hr')).
              ** (* false :: false :: true :: false :: true :: false :: l6 *)
                 apply opt_map_some in h as [r' [Hr' <-]].
                 cbn [toTape b2f Str_app].
                 exact (round_001010 (IH l6 r' Hr')).
           ++ (* false :: false :: true :: false :: false :: l5 *)
              apply opt_map_some in h as [r' [Hr' <-]].
              cbn [toTape b2f Str_app].
              exact (round_00100 (IH l5 r' Hr')).
      * (* false :: false :: false :: l3 *)
        inversion h; subst; clear h.
        cbn [toTape b2f Str_app].
        exact (round_000 (toTape l3)).
Qed.

Fixpoint sweepsBool (fuel n : nat) (bs : list bool) : option (list bool) :=
  match n with
  | 0 => Some bs
  | S n' =>
    match roundBool fuel bs with
    | Some bs1 => sweepsBool fuel n' bs1
    | None => None
    end
  end.

Lemma sweepsBool_sound (fuel n : nat) : forall (bs ys : list bool),
    sweepsBool fuel n bs = Some ys -> Sweeps n (toTape bs) (toTape ys).
Proof.
  induction n as [| n IH]; intros bs ys h; cbn [sweepsBool] in h.
  - inversion h; subst. apply Sweeps_zero.
  - destruct (roundBool fuel bs) as [bs1 |] eqn:Hr; [| discriminate].
    exact (Sweeps_succ (roundBool_sound fuel bs bs1 Hr) (IH bs1 ys h)).
Qed.

Definition roundBoolTrim (fuel : nat) (bs : list bool) : option (list bool) :=
  option_map dropTrailingFalse (roundBool fuel bs).

Lemma roundBoolTrim_sound (fuel : nat) (bs ys : list bool)
    (h : roundBoolTrim fuel bs = Some ys) : Round (toTape bs) (toTape ys).
Proof.
  apply opt_map_some in h as [raw [Hraw <-]].
  rewrite toTape_dropTrailingFalse.
  exact (roundBool_sound fuel bs raw Hraw).
Qed.

Definition sweepsBoolTrim (fuel n : nat) (bs : list bool) : option (list bool) :=
  option_map dropTrailingFalse (sweepsBool fuel n bs).

Lemma sweepsBoolTrim_sound (fuel n : nat) (bs ys : list bool)
    (h : sweepsBoolTrim fuel n bs = Some ys) : Sweeps n (toTape bs) (toTape ys).
Proof.
  apply opt_map_some in h as [raw [Hraw <-]].
  rewrite toTape_dropTrailingFalse.
  exact (sweepsBool_sound fuel n bs raw Hraw).
Qed.

(* ========================================================================== *)
(* Section 4: rep010, EraRound, pDiv0, pDiv1, pB & Parameterized Lemmas       *)
(* ========================================================================== *)

Fixpoint rep010 (k : nat) (r : side) : side :=
  match k with
  | 0 => r
  | S k' => [S0; S1; S0] *> rep010 k' r
  end.

Lemma rep010_add (a b : nat) (r : side) :
    rep010 (a + b) r = rep010 a (rep010 b r).
Proof.
  induction a as [| a IH]; cbn [Nat.add rep010]; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Definition EraRound (u r' : side) : Prop :=
  exists v : side, u = S0 >> v /\ Round v r'.

Lemma eraRound_tm_step {u r' : side} (h : EraRound u r') :
    (s0inf <{{D}} u) -[ tm ]->+ (s0inf <{{D}} ([S0; S1; S0] *> r')).
Proof.
  destruct h as [v [-> hv]].
  eapply progress_trans; [apply rule_E_nil |].
  eapply progress_trans; [apply hv |].
  apply rule_E_011.
Qed.

Lemma round_rep010 (k : nat) {r r' : side} (h : Round r r') :
    Round (rep010 k r) (rep010 k r').
Proof.
  induction k as [| k IH]; cbn [rep010]; [exact h | exact (round_010 IH)].
Qed.

Lemma sweeps_rep010 (k : nat) {n : nat} {r r' : side} (h : Sweeps n r r') :
    Sweeps n (rep010 k r) (rep010 k r').
Proof.
  induction h as [r | n r r1 r2 hr _ IH].
  - apply Sweeps_zero.
  - exact (Sweeps_succ (round_rep010 k hr) IH).
Qed.

Lemma sweeps_010 {n : nat} {r r' : side} (h : Sweeps n r r') :
    Sweeps n ([S0; S1; S0] *> r) ([S0; S1; S0] *> r').
Proof.
  exact (sweeps_rep010 1 h).
Qed.

Lemma eraRound_010 {s s1 r' : side}
    (hR : Round s s1) (hE : EraRound s1 r') :
    EraRound ([S0; S1; S0] *> s) ([S0; S1; S0] *> r').
Proof.
  destruct hE as [v1 [-> hv1]].
  exists ([S1; S0] *> s).
  split; [reflexivity | exact (round_10 hR hv1)].
Qed.

Lemma eraRound_rep010 {N : nat} {rem u r' : side}
    (hS : Sweeps N rem u) (hE : EraRound u r') :
    EraRound (rep010 N rem) (rep010 N r').
Proof.
  induction hS as [r | n r r1 r2 hr _ IH]; cbn [rep010].
  - exact hE.
  - exact (eraRound_010 (round_rep010 n hr) (IH hE)).
Qed.

Definition pDiv0 (r : side) : side := [S0; S0; S0; S0; S1; S0] *> r.
Definition pDiv1 (r : side) : side := [S0; S0; S1; S0; S1; S0] *> r.
Definition pB (r : side) : side := [S0; S0; S1; S1; S0] *> r.

Lemma round_pDiv0 (r : side) : Round (pDiv0 r) (pDiv1 r).
Proof. exact (round_000 ([S0; S1; S0] *> r)). Qed.

Lemma round_pDiv1 {r r' : side} (h : Round r r') : Round (pDiv1 r) (pDiv0 r').
Proof. exact (round_001010 h). Qed.

Lemma sweeps_pDiv0_even {k : nat} {r r' : side} (h : Sweeps k r r') :
    Sweeps (2 * k) (pDiv0 r) (pDiv0 r').
Proof.
  induction h as [r | m r0 r1 r2 hr _ IH].
  - apply Sweeps_zero.
  - pose proof (Sweeps_succ (round_pDiv0 r0) (Sweeps_succ (round_pDiv1 hr) (Sweeps_zero _))) as h2.
    pose proof (Sweeps_trans h2 IH) as htr.
    replace (2 * S m) with (2 + 2 * m) by lia.
    exact htr.
Qed.

Lemma sweeps_pDiv0_odd {k : nat} {r r' : side} (h : Sweeps k r r') :
    Sweeps (2 * k + 1) (pDiv0 r) (pDiv1 r').
Proof.
  exact (Sweeps_trans (sweeps_pDiv0_even h) (Sweeps_succ (round_pDiv0 r') (Sweeps_zero _))).
Qed.

Lemma sweeps_pDiv1_even {k : nat} {r r' : side} (h : Sweeps k r r') :
    Sweeps (2 * k) (pDiv1 r) (pDiv1 r').
Proof.
  induction h as [r | m r0 r1 r2 hr _ IH].
  - apply Sweeps_zero.
  - pose proof (Sweeps_succ (round_pDiv1 hr) (Sweeps_succ (round_pDiv0 r1) (Sweeps_zero _))) as h2.
    pose proof (Sweeps_trans h2 IH) as htr.
    replace (2 * S m) with (2 + 2 * m) by lia.
    exact htr.
Qed.

Lemma sweeps_pDiv1_odd {k : nat} {r r' : side} (h : Sweeps (S k) r r') :
    Sweeps (2 * k + 1) (pDiv1 r) (pDiv0 r').
Proof.
  inversion h as [| m r0 r1 r2 hr hs]; subst.
  replace (2 * k + 1) with (S (2 * k)) by lia.
  exact (Sweeps_succ (round_pDiv1 hr) (sweeps_pDiv0_even hs)).
Qed.

Definition StartsZero (u : side) : Prop :=
  exists v : side, u = S0 >> v.

Lemma rep010_startsZero (k : nat) {u : side} (hu : StartsZero u) :
    StartsZero (rep010 k u).
Proof.
  destruct k as [| k']; [exact hu |].
  exists ([S1; S0] *> rep010 k' u). reflexivity.
Qed.

Lemma sweeps_pB_010_startsZero {u : side} (hu : StartsZero u) :
    Sweeps 2 (pB ([S0; S1; S0] *> u)) ([S0; S1; S0] *> pB u).
Proof.
  destruct hu as [v ->].
  eapply Sweeps_succ; [exact (round_0011 ([S0; S0; S1; S0; S0] *> v)) |].
  eapply Sweeps_succ; [exact (round_010 (round_000 ([S1; S0; S0] *> v))) |].
  apply Sweeps_zero.
Qed.

Lemma sweeps_pB_rep010 (k : nat) {u : side} (hu : StartsZero u) :
    Sweeps (2 * k) (pB (rep010 k u)) (rep010 k (pB u)).
Proof.
  induction k as [| k IH]; cbn [rep010].
  - apply Sweeps_zero.
  - pose proof (sweeps_pB_010_startsZero (rep010_startsZero k hu)) as h2.
    pose proof (Sweeps_trans h2 (sweeps_010 IH)) as htr.
    replace (2 * S k) with (2 + 2 * k) by lia.
    exact htr.
Qed.

Lemma sweeps_pB_pDiv0 {u u1 : side} (h1 : Round u u1) :
    Sweeps 6 (pB (pDiv0 u)) (rep010 2 (pB u1)).
Proof.
  eapply Sweeps_succ; [exact (round_0011 ([S0; S0; S0; S0; S0; S1; S0] *> u)) |].
  eapply Sweeps_succ; [exact (round_010 (round_000 ([S0; S0; S0; S1; S0] *> u))) |].
  eapply Sweeps_succ; [exact (round_010 (round_00100 (round_010 h1))) |].
  eapply Sweeps_succ; [exact (round_010 (round_000 ([S1; S0; S0; S1; S0] *> u1))) |].
  eapply Sweeps_succ; [exact (round_010 (round_0011 ([S0; S0; S1; S0] *> u1))) |].
  eapply Sweeps_succ; [exact (round_010 (round_010 (round_000 ([S1; S0] *> u1)))) |].
  apply Sweeps_zero.
Qed.

Lemma sweeps_pB_pDiv1 {u u1 r1' : side}
    (h1 : Round u u1) (hE : EraRound u1 r1') :
    Sweeps 3 (pB (pDiv1 u)) ([S0; S1; S0] *> pDiv0 ([S0; S1; S0] *> r1')).
Proof.
  destruct hE as [v1 [-> hv1]].
  eapply Sweeps_succ; [exact (round_0011 ([S0; S0; S0; S1; S0; S1; S0] *> u)) |].
  eapply Sweeps_succ; [exact (round_010 (round_000 ([S0; S1; S0; S1; S0] *> u))) |].
  eapply Sweeps_succ; [exact (round_010 (round_001010 (round_10 h1 hv1))) |].
  apply Sweeps_zero.
Qed.

Lemma eraRound_pDiv0 (u : side) :
    EraRound (pDiv0 u) (pB u).
Proof.
  exists ([S0; S0; S0; S1; S0] *> u).
  split; [reflexivity | exact (round_000 ([S1; S0] *> u))].
Qed.

Lemma eraRound_pDiv1 {u u1 r1' : side}
    (h1 : Round u u1) (hE : EraRound u1 r1') :
    EraRound (pDiv1 u) (rep010 2 r1').
Proof.
  destruct hE as [v1 [-> hv1]].
  exists ([S0; S1; S0; S1; S0] *> u).
  split; [reflexivity | exact (round_010 (round_10 h1 hv1))].
Qed.

(* ========================================================================== *)
(* Section 5: CoreTree, UTree, stepDefaultAux, stepCore, stepU & Soundness    *)
(* ========================================================================== *)

Inductive CoreTree : Type :=
  | sw0 : CoreTree
  | sw1 : CoreTree
  | sw2 : CoreTree
  | sw3 : CoreTree
  | div0 : nat -> CoreTree -> CoreTree
  | div1 : nat -> CoreTree -> CoreTree.

Definition UTree : Type := (nat * CoreTree)%type.

Fixpoint evalCore (w : CoreTree) : side :=
  match w with
  | sw0 => s0inf
  | sw1 => [S0; S0; S1] *> s0inf
  | sw2 => [S0; S0; S0; S1; S0; S0; S0; S1; S0] *> s0inf
  | sw3 => [S0; S0; S1; S1; S0; S0; S0; S1; S0] *> s0inf
  | div0 k ch => pDiv0 (rep010 k (evalCore ch))
  | div1 k ch => pDiv1 (rep010 k (evalCore ch))
  end.

Definition evalU (u : UTree) : side :=
  rep010 (fst u) (evalCore (snd u)).

Lemma evalCore_startsZero (w : CoreTree) : StartsZero (evalCore w).
Proof.
  destruct w as [| | | | k ch | k ch]; cbn [evalCore pDiv0 pDiv1 Str_app].
  - exists (s0inf). symmetry. apply zero_cons_default.
  - exists ([S0; S1] *> s0inf). reflexivity.
  - exists ([S0; S0; S1; S0; S0; S0; S1; S0] *> s0inf). reflexivity.
  - exists ([S0; S1; S1; S0; S0; S0; S1; S0] *> s0inf). reflexivity.
  - exists ([S0; S0; S0; S1; S0] *> rep010 k (evalCore ch)). reflexivity.
  - exists ([S0; S1; S0; S1; S0] *> rep010 k (evalCore ch)). reflexivity.
Qed.

Fixpoint levelCore (w : CoreTree) : nat :=
  match w with
  | sw0 => 1
  | sw1 => 2
  | sw2 => 3
  | sw3 => 4
  | div0 k ch => 2 * (3 * k + levelCore ch)
  | div1 k ch => 2 * (3 * k + levelCore ch) + 1
  end.

Definition levelU (u : UTree) : nat :=
  3 * fst u + levelCore (snd u).

Lemma levelCore_pos (w : CoreTree) : 1 <= levelCore w.
Proof.
  induction w; cbn [levelCore]; lia.
Qed.

Definition mkSw (s : nat) : CoreTree :=
  match s with
  | 0 => sw0
  | 1 => sw1
  | 2 => sw2
  | _ => sw3
  end.

Definition coreTagIdx (w : CoreTree) : option nat :=
  match w with
  | sw0 => Some 0
  | sw1 => Some 1
  | sw2 => Some 2
  | sw3 => Some 3
  | div0 _ _ => None
  | div1 _ _ => None
  end.

Fixpoint stepDefaultAux (fuel s : nat) : UTree :=
  match fuel with
  | 0 => (0, mkSw s)
  | S fuel' =>
    if s <=? 3 then (0, mkSw s)
    else
      let m := s - 4 in
      let sub := stepDefaultAux fuel' (m / 2) in
      if (m mod 2) =? 0 then (1, div0 (fst sub) (snd sub))
      else (1, div1 (fst sub) (snd sub))
  end.

Lemma stepDefaultAux_le3 (fuel s : nat) (hs : s <= 3) :
    stepDefaultAux fuel s = (0, mkSw s).
Proof.
  destruct fuel as [| fuel']; [reflexivity |].
  cbn [stepDefaultAux].
  destruct (Nat.leb_spec0 s 3); [reflexivity | lia].
Qed.

Lemma stepDefaultAux_add4 (fuel m : nat) :
    stepDefaultAux (S fuel) (m + 4) =
      (let sub := stepDefaultAux fuel (m / 2) in
       if (m mod 2) =? 0 then (1, div0 (fst sub) (snd sub))
       else (1, div1 (fst sub) (snd sub))).
Proof.
  cbn [stepDefaultAux].
  destruct (Nat.leb_spec0 (m + 4) 3); [lia |].
  replace (m + 4 - 4) with m by lia.
  reflexivity.
Qed.

Definition stepDefault (s : nat) : UTree :=
  stepDefaultAux s s.

Fixpoint stepCore (s : nat) (w : CoreTree) : UTree :=
  match w with
  | sw0 => stepDefault s
  | sw1 => stepDefault (s + 1)
  | sw2 => stepDefault (s + 2)
  | sw3 => stepDefault (s + 3)
  | div0 k ch =>
    let sub := stepCore (s / 2) ch in
    if (s mod 2) =? 0 then (0, div0 (k + fst sub) (snd sub))
    else (0, div1 (k + fst sub) (snd sub))
  | div1 k ch =>
    let sub := stepCore ((s + 1) / 2) ch in
    if (s mod 2) =? 0 then (0, div1 (k + fst sub) (snd sub))
    else (0, div0 (k + fst sub) (snd sub))
  end.

Definition stepU (s : nat) (u : UTree) : UTree :=
  let sub := stepCore s (snd u) in
  (fst u + fst sub, snd sub).

Definition stepDiv0Sw0 (s : nat) : CoreTree :=
  let sub := stepDefault (s / 2) in
  if (s mod 2) =? 0 then div0 (fst sub) (snd sub)
  else div1 (fst sub) (snd sub).

Definition stepDivCore (s : nat) (w : CoreTree) : CoreTree :=
  match w with
  | div0 k ch =>
    let sub := stepCore (s / 2) ch in
    if (s mod 2) =? 0 then div0 (k + fst sub) (snd sub)
    else div1 (k + fst sub) (snd sub)
  | div1 k ch =>
    let sub := stepCore ((s + 1) / 2) ch in
    if (s mod 2) =? 0 then div1 (k + fst sub) (snd sub)
    else div0 (k + fst sub) (snd sub)
  | _ => w
  end.

Lemma levelU_stepDefaultAux (fuel : nat) : forall (s : nat), s <= fuel ->
    levelU (stepDefaultAux fuel s) = s + 1.
Proof.
  induction fuel as [| fuel IH]; intros s hs.
  - assert (s = 0) by lia; subst s; reflexivity.
  - destruct ( le_lt_dec s 3 ) as [hle | hgt].
    + rewrite (stepDefaultAux_le3 (S fuel) s hle).
      destruct s as [| [| [| [| ?]]]]; try reflexivity; lia.
    + replace s with ((s - 4) + 4) by lia.
      set (m := s - 4).
      rewrite stepDefaultAux_add4.
      assert (hm_le : m / 2 <= fuel) by (unfold m; dlia).
      pose proof (IH (m / 2) hm_le) as Hsub.
      unfold levelU in Hsub.
      destruct (mod2_cases m) as [[Hev Hevb] | [Hod Hodb]];
        [rewrite Hevb | rewrite Hodb];
        unfold levelU; cbn [fst snd levelCore]; dlia.
Qed.

Lemma levelU_stepDefault (s : nat) : levelU (stepDefault s) = s + 1.
Proof. exact (levelU_stepDefaultAux s s (Nat.le_refl s)). Qed.

Lemma levelU_stepCore (w : CoreTree) : forall (s : nat),
    levelU (stepCore s w) = levelCore w + s.
Proof.
  induction w as [| | | | k ch IH | k ch IH]; intros s.
  - cbn [stepCore levelCore]. rewrite levelU_stepDefault. lia.
  - cbn [stepCore levelCore]. rewrite levelU_stepDefault. lia.
  - cbn [stepCore levelCore]. rewrite levelU_stepDefault. lia.
  - cbn [stepCore levelCore]. rewrite levelU_stepDefault. lia.
  - pose proof (IH (s / 2)) as Hsub; unfold levelU in Hsub.
    cbn [stepCore].
    destruct (mod2_cases s) as [[Hev Hevb] | [Hod Hodb]];
      [rewrite Hevb | rewrite Hodb];
      unfold levelU; cbn [fst snd levelCore]; dlia.
  - pose proof (IH ((s + 1) / 2)) as Hsub; unfold levelU in Hsub.
    cbn [stepCore].
    destruct (mod2_cases s) as [[Hev Hevb] | [Hod Hodb]];
      [rewrite Hevb | rewrite Hodb];
      unfold levelU; cbn [fst snd levelCore]; dlia.
Qed.

Lemma levelU_stepU (s : nat) (u : UTree) : levelU (stepU s u) = levelU u + s.
Proof.
  destruct u as [k w].
  pose proof (levelU_stepCore w s) as Hsub.
  unfold stepU, levelU in *; cbn [fst snd] in *. lia.
Qed.

Lemma levelCore_stepDiv0Sw0 (s : nat) : levelCore (stepDiv0Sw0 s) = s + 2.
Proof.
  pose proof (levelU_stepDefault (s / 2)) as Hsub; unfold levelU in Hsub.
  unfold stepDiv0Sw0.
  destruct (mod2_cases s) as [[Hev Hevb] | [Hod Hodb]];
    [rewrite Hevb | rewrite Hodb];
    cbn [levelCore]; dlia.
Qed.

Lemma levelCore_stepDivCore (s : nat) (w : CoreTree) (hw : coreTagIdx w = None) :
    levelCore (stepDivCore s w) = levelCore w + s.
Proof.
  destruct w as [| | | | k ch | k ch]; try discriminate.
  - pose proof (levelU_stepCore ch (s / 2)) as Hsub; unfold levelU in Hsub.
    cbn [stepDivCore].
    destruct (mod2_cases s) as [[Hev Hevb] | [Hod Hodb]];
      [rewrite Hevb | rewrite Hodb];
      cbn [levelCore]; dlia.
  - pose proof (levelU_stepCore ch ((s + 1) / 2)) as Hsub; unfold levelU in Hsub.
    cbn [stepDivCore].
    destruct (mod2_cases s) as [[Hev Hevb] | [Hod Hodb]];
      [rewrite Hevb | rewrite Hodb];
      cbn [levelCore]; dlia.
Qed.

Lemma round_sw0_sw1 : Round (evalCore sw0) (evalCore sw1).
Proof.
  exact (roundBoolTrim_sound 5 [] [false; false; true] eq_refl).
Qed.

Lemma round_sw1_sw2 : Round (evalCore sw1) (evalCore sw2).
Proof.
  pose proof (roundBoolTrim_sound 10 [false; false; true]
    [false; false; false; true; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f evalCore Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma round_sw2_sw3 : Round (evalCore sw2) (evalCore sw3).
Proof.
  pose proof (roundBoolTrim_sound 10 [false; false; false; true; false; false; false; true]
    [false; false; true; true; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f evalCore Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma round_sw3_div0 : Round (evalCore sw3) (evalU (1, div0 0 sw0)).
Proof.
  pose proof (roundBoolTrim_sound 10 [false; false; true; true; false; false; false; true]
    [false; true; false; false; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f evalCore evalU fst snd rep010 pDiv0 Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma stepDefaultAux_eq (fuel1 : nat) : forall (fuel2 s : nat),
    s <= fuel1 -> s <= fuel2 -> stepDefaultAux fuel1 s = stepDefaultAux fuel2 s.
Proof.
  induction fuel1 as [| fuel1 IH]; intros fuel2 s h1 h2.
  - assert (s = 0) by lia; subst s.
    symmetry. apply stepDefaultAux_le3; lia.
  - destruct (le_lt_dec s 3) as [hle | hgt].
    + rewrite !stepDefaultAux_le3; [reflexivity | exact hle | exact hle].
    + destruct fuel2 as [| fuel2]; [lia |].
      replace s with ((s - 4) + 4) by lia.
      set (m := s - 4).
      rewrite !stepDefaultAux_add4.
      rewrite (IH fuel2 (m / 2) ltac:(unfold m; dlia) ltac:(unfold m; dlia)).
      reflexivity.
Qed.

Lemma stepDefault_add4_eq (m : nat) :
    stepDefault (m + 4) = (1, stepDiv0Sw0 m).
Proof.
  unfold stepDefault.
  replace (m + 4) with (S (m + 3)) at 1 by lia.
  rewrite stepDefaultAux_add4.
  rewrite (stepDefaultAux_eq (m + 3) (m / 2) (m / 2) ltac:(dlia) (Nat.le_refl _)).
  unfold stepDiv0Sw0, stepDefault.
  destruct ((m mod 2) =? 0); reflexivity.
Qed.

Lemma stepDefault_one_more (q : nat) :
    Round (evalU (stepDefault q)) (evalU (stepDefault (q + 1))).
Proof.
  induction q as [q IH] using strong_induction.
  destruct (le_lt_dec q 3) as [hle | hgt].
  - destruct q as [| [| [| [| ?]]]]; try lia.
    + exact round_sw0_sw1.
    + exact round_sw1_sw2.
    + exact round_sw2_sw3.
    + exact round_sw3_div0.
  - replace q with ((q - 4) + 4) by lia.
    set (m := q - 4).
    replace (m + 4 + 1) with ((m + 1) + 4) by lia.
    rewrite (stepDefault_add4_eq m), (stepDefault_add4_eq (m + 1)).
    unfold evalU; cbn [fst snd rep010].
    apply round_010.
    unfold stepDiv0Sw0.
    destruct (mod2_cases m) as [[Hev Hevb] | [Hod Hodb]].
    + assert (H1 : ((m + 1) mod 2 =? 0) = false) by (apply Nat.eqb_neq; dlia).
      assert (Hdiv : (m + 1) / 2 = m / 2) by dlia.
      rewrite Hevb, H1, Hdiv.
      cbn [evalCore]. apply round_pDiv0.
    + assert (H1 : ((m + 1) mod 2 =? 0) = true) by (apply Nat.eqb_eq; dlia).
      assert (Hdiv : (m + 1) / 2 = m / 2 + 1) by dlia.
      rewrite Hodb, H1, Hdiv.
      cbn [evalCore].
      apply round_pDiv1.
      apply IH. unfold m; dlia.
Qed.

Lemma round_stepDiv0Sw0 (m : nat) :
    Round (evalCore (stepDiv0Sw0 m)) (evalCore (stepDiv0Sw0 (m + 1))).
Proof.
  unfold stepDiv0Sw0.
  destruct (mod2_cases m) as [[Hev Hevb] | [Hod Hodb]].
  - assert (H1 : ((m + 1) mod 2 =? 0) = false) by (apply Nat.eqb_neq; dlia).
    assert (Hdiv : (m + 1) / 2 = m / 2) by dlia.
    rewrite Hevb, H1, Hdiv.
    cbn [evalCore]. apply round_pDiv0.
  - assert (H1 : ((m + 1) mod 2 =? 0) = true) by (apply Nat.eqb_eq; dlia).
    assert (Hdiv : (m + 1) / 2 = m / 2 + 1) by dlia.
    rewrite Hodb, H1, Hdiv.
    cbn [evalCore].
    exact (round_pDiv1 (stepDefault_one_more (m / 2))).
Qed.

Lemma stepDefault_from (t s : nat) :
    Sweeps s (evalU (stepDefault t)) (evalU (stepDefault (s + t))).
Proof.
  induction s as [| s IH].
  - cbn [Nat.add]. apply Sweeps_zero.
  - pose proof (Sweeps_succ (stepDefault_one_more (s + t)) (Sweeps_zero _)) as h1.
    pose proof (Sweeps_trans IH h1) as htr.
    replace (S s + t) with (s + t + 1) by lia.
    replace (S s) with (s + 1) by lia.
    exact htr.
Qed.

Lemma stepDefault_sound (s : nat) : Sweeps s (evalCore sw0) (evalU (stepDefault s)).
Proof.
  pose proof (stepDefault_from 0 s) as h.
  rewrite Nat.add_0_r in h. exact h.
Qed.

Lemma stepCore_sound (w : CoreTree) : forall (s : nat),
    Sweeps s (evalCore w) (evalU (stepCore s w)).
Proof.
  induction w as [| | | | k ch IH | k ch IH]; intros s.
  - exact (stepDefault_sound s).
  - exact (stepDefault_from 1 s).
  - exact (stepDefault_from 2 s).
  - exact (stepDefault_from 3 s).
  - pose proof (sweeps_rep010 k (IH (s / 2))) as hsub.
    unfold evalU in hsub; rewrite <- rep010_add in hsub.
    cbn [stepCore].
    destruct (mod2_cases s) as [[Hev Hevb] | [Hod Hodb]];
      [rewrite Hevb | rewrite Hodb];
      unfold evalU; cbn [fst snd rep010 evalCore].
    + pose proof (sweeps_pDiv0_even hsub) as h.
      replace s with (2 * (s / 2)) at 1 by dlia. exact h.
    + pose proof (sweeps_pDiv0_odd hsub) as h.
      replace s with (2 * (s / 2) + 1) at 1 by dlia. exact h.
  - cbn [stepCore].
    destruct (mod2_cases s) as [[Hev Hevb] | [Hod Hodb]];
      [rewrite Hevb | rewrite Hodb];
      unfold evalU; cbn [fst snd rep010 evalCore].
    + assert (Heq : (s + 1) / 2 = s / 2) by dlia.
      pose proof (sweeps_rep010 k (IH ((s + 1) / 2))) as hsub.
      unfold evalU in hsub; rewrite <- rep010_add in hsub.
      rewrite Heq in hsub at 1.
      pose proof (sweeps_pDiv1_even hsub) as h.
      replace s with (2 * (s / 2)) at 1 by dlia. exact h.
    + assert (Heq : (s + 1) / 2 = S (s / 2)) by dlia.
      pose proof (sweeps_rep010 k (IH ((s + 1) / 2))) as hsub.
      unfold evalU in hsub; rewrite <- rep010_add in hsub.
      rewrite Heq in hsub at 1.
      pose proof (sweeps_pDiv1_odd hsub) as h.
      replace s with (2 * (s / 2) + 1) at 1 by dlia. exact h.
Qed.

Lemma stepU_sound (s : nat) (u : UTree) :
    Sweeps s (evalU u) (evalU (stepU s u)).
Proof.
  pose proof (sweeps_rep010 (fst u) (stepCore_sound (snd u) s)) as h.
  unfold stepU, evalU in *; cbn [fst snd] in *.
  rewrite <- rep010_add in h. exact h.
Qed.

Lemma stepDivCore_sound (s : nat) (w : CoreTree) (hw : coreTagIdx w = None) :
    Sweeps s (evalCore w) (evalCore (stepDivCore s w)).
Proof.
  destruct w as [| | | | k ch | k ch]; try discriminate.
  - pose proof (stepCore_sound (div0 k ch) s) as h.
    cbn [stepCore stepDivCore] in h |- *.
    destruct ((s mod 2) =? 0); unfold evalU in h; cbn [fst snd rep010] in h; exact h.
  - pose proof (stepCore_sound (div1 k ch) s) as h.
    cbn [stepCore stepDivCore] in h |- *.
    destruct ((s mod 2) =? 0); unfold evalU in h; cbn [fst snd rep010] in h; exact h.
Qed.

Lemma round_of_sweeps_one {r r' : side} (h : Sweeps 1 r r') : Round r r'.
Proof.
  inversion h as [| n r0 r1 r2 hr h0]; subst.
  inversion h0; subst. exact hr.
Qed.

(* ========================================================================== *)
(* Section 6: Fueled 2-Function opsAux & Soundness                            *)
(* ========================================================================== *)

Record ResB : Type := mkResB {
  resB_c : nat;
  resB_u : UTree
}.

Record ResP : Type := mkResP {
  resP_p : nat;
  resP_c : nat;
  resP_u : UTree
}.

Record Ops : Type := mkOps {
  bCore : CoreTree -> ResB;
  aCore : CoreTree -> ResP
}.

Definition bUFrom (bCoreFn : CoreTree -> ResB) (u : UTree) : ResB :=
  let sub := bCoreFn (snd u) in
  mkResB (2 * fst u + resB_c sub) (fst u + fst (resB_u sub), snd (resB_u sub)).

Definition aPullSucc (aCoreFn : CoreTree -> ResP) (k : nat) (w : CoreTree) : ResP :=
  match coreTagIdx w with
  | Some t =>
    if (k + t) <=? 3 then
      let sub := aCoreFn (mkSw (k + t)) in
      mkResP (k + resP_p sub) (resP_c sub) (resP_u sub)
    else
      let sub := aCoreFn (stepDiv0Sw0 (k + t - 3)) in
      mkResP (k + 1 + resP_p sub) (resP_c sub) (resP_u sub)
  | None =>
    let sub := aCoreFn (stepDivCore k w) in
    mkResP (k + resP_p sub) (resP_c sub) (resP_u sub)
  end.

Definition aPullFrom (aCoreFn : CoreTree -> ResP) (u : UTree) : ResP :=
  match fst u with
  | 0 => aCoreFn (snd u)
  | S k' => aPullSucc aCoreFn (S k') (snd u)
  end.

Definition is_sw0 (w : CoreTree) : bool :=
  match w with
  | sw0 => true
  | _ => false
  end.

Lemma zero_sw0_cases (k : nat) (ch : CoreTree) :
  (k = 0 /\ ch = sw0 /\ ((k =? 0) && is_sw0 ch)%bool = true) \/
  (~ (k = 0 /\ ch = sw0) /\ ((k =? 0) && is_sw0 ch)%bool = false).
Proof.
  destruct k as [| k']; [| right; split; [intros [? _]; discriminate | reflexivity]].
  destruct ch; try (right; split; [intros [_ ?]; discriminate | reflexivity]).
  left; repeat split; reflexivity.
Qed.

Fixpoint opsAux (fuel : nat) : Ops :=
  match fuel with
  | 0 =>
    mkOps
      (fun _ => mkResB 0 (0, sw0))
      (fun _ => mkResP 0 0 (0, sw0))
  | S fuel' =>
    mkOps
      (fun w =>
        match w with
        | sw0 => mkResB 1 (1, sw0)
        | sw1 => mkResB 0 (0, sw3)
        | sw2 => mkResB 15 (6, div0 0 sw2)
        | sw3 => mkResB 9 (3, div0 0 sw2)
        | div0 k ch =>
          if ((k =? 0) && is_sw0 ch)%bool then
            mkResB 6 (2, sw3)
          else
            let u1 := stepU 1 (k, ch) in
            let sub := bUFrom (bCore (opsAux fuel')) u1 in
            mkResB (6 + resB_c sub) (2 + fst (resB_u sub), snd (resB_u sub))
        | div1 k ch =>
          if ((k =? 0) && is_sw0 ch)%bool then
            mkResB 3 (1, div0 2 sw1)
          else
            let u1 := stepU 1 (k, ch) in
            let sub := aPullFrom (aCore (opsAux fuel')) u1 in
            mkResB (3 + 2 * resP_c sub) (1, div0 (1 + resP_p sub + fst (resP_u sub)) (snd (resP_u sub)))
        end)
      (fun w =>
        match w with
        | sw0 => mkResP 0 0 (0, sw1)
        | sw1 => mkResP 1 0 (0, sw1)
        | sw2 => mkResP 0 2 (1, sw2)
        | sw3 => mkResP 0 11 (4, div0 0 sw2)
        | div0 k ch =>
          if ((k =? 0) && is_sw0 ch)%bool then
            mkResP 0 1 (1, sw0)
          else
            let sub := bUFrom (bCore (opsAux fuel')) (k, ch) in
            mkResP 0 (resB_c sub) (resB_u sub)
        | div1 k ch =>
          if ((k =? 0) && is_sw0 ch)%bool then
            mkResP 3 0 (0, sw1)
          else
            let u1 := stepU 1 (k, ch) in
            let sub := aPullFrom (aCore (opsAux fuel')) u1 in
            mkResP (2 + resP_p sub) (resP_c sub) (resP_u sub)
        end)
  end.

Lemma bCore_sw0_sound : Sweeps 1 (pB (evalCore sw0)) (evalU (1, sw0)).
Proof.
  pose proof (sweepsBoolTrim_sound 10 1 [false; false; true; true; false]
    [false; true] eq_refl) as h.
  cbn [toTape b2f pB evalCore evalU fst snd rep010 Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma bCore_sw1_sound : Sweeps 0 (pB (evalCore sw1)) (evalU (0, sw3)).
Proof.
  cbn [pB evalCore evalU fst snd rep010 Str_app].
  norm_s0.
  apply Sweeps_zero.
Qed.

Lemma bCore_sw2_sound : Sweeps 15 (pB (evalCore sw2)) (evalU (6, div0 0 sw2)).
Proof.
  pose proof (sweepsBoolTrim_sound 20 15
    [false; false; true; true; false; false; false; false; true; false; false; false; true]
    [false; true; false; false; true; false; false; true; false; false; true; false; false; true; false; false; true; false;
     false; false; false; false; true; false; false; false; false; true; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f pB evalCore evalU fst snd rep010 pDiv0 Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma bCore_sw3_sound : Sweeps 9 (pB (evalCore sw3)) (evalU (3, div0 0 sw2)).
Proof.
  pose proof (sweepsBoolTrim_sound 20 9
    [false; false; true; true; false; false; false; true; true; false; false; false; true]
    [false; true; false; false; true; false; false; true; false;
     false; false; false; false; true; false; false; false; false; true; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f pB evalCore evalU fst snd rep010 pDiv0 Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma bCore_div0_sw0_sound : Sweeps 6 (pB (evalCore (div0 0 sw0))) (evalU (2, sw3)).
Proof.
  pose proof (sweepsBoolTrim_sound 20 6
    [false; false; true; true; false; false; false; false; false; true]
    [false; true; false; false; true; false; false; false; true; true; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f pB evalCore evalU fst snd rep010 pDiv0 Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma bCore_div1_sw0_sound : Sweeps 3 (pB (evalCore (div1 0 sw0))) (evalU (1, div0 2 sw1)).
Proof.
  pose proof (sweepsBoolTrim_sound 20 3
    [false; false; true; true; false; false; false; true; false; true]
    [false; true; false; false; false; false; false; true; false;
     false; true; false; false; true; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f pB evalCore evalU fst snd rep010 pDiv0 pDiv1 Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma aCore_sw0_sound : EraRound (evalCore sw0) (rep010 0 (evalCore sw1)).
Proof.
  exists (s0inf).
  split; [symmetry; apply zero_cons_default | exact round_sw0_sw1].
Qed.

Lemma aCore_sw1_sound : EraRound (evalCore sw1) (rep010 1 (evalCore sw1)).
Proof.
  exists ([S0; S1] *> s0inf).
  split; [reflexivity |].
  pose proof (roundBoolTrim_sound 10 [false; true] [false; true; false; false; false; true] eq_refl) as h.
  cbn [toTape b2f evalCore rep010 Str_app] in h |- *.
  norm_s0. exact h.
Qed.

Lemma aCore_sw2_sound :
    exists r', EraRound (evalCore sw2) (rep010 0 r') /\ Sweeps 2 r' (evalU (1, sw2)).
Proof.
  exists ([S0; S0; S0; S1; S0; S0; S1; S0; S0; S0; S1] *> s0inf).
  split.
  - exists ([S0; S0; S1; S0; S0; S0; S1; S0] *> s0inf).
    split; [reflexivity |].
    pose proof (roundBoolTrim_sound 10 [false; false; true; false; false; false; true]
      [false; false; false; true; false; false; true; false; false; false; true] eq_refl) as h.
    cbn [toTape b2f rep010 Str_app] in h |- *.
    norm_s0. exact h.
  - pose proof (sweepsBoolTrim_sound 15 2
      [false; false; false; true; false; false; true; false; false; false; true]
      [false; true; false; false; false; false; true; false; false; false; true] eq_refl) as h.
    cbn [toTape b2f evalU evalCore fst snd rep010 Str_app] in h |- *.
    norm_s0. exact h.
Qed.

Lemma aCore_sw3_sound :
    exists r', EraRound (evalCore sw3) (rep010 0 r') /\ Sweeps 11 r' (evalU (4, div0 0 sw2)).
Proof.
  exists ([S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S0; S1] *> s0inf).
  split.
  - exists ([S0; S1; S1; S0; S0; S0; S1; S0] *> s0inf).
    split; [reflexivity |].
    pose proof (roundBoolTrim_sound 10 [false; true; true; false; false; false; true]
      [false; false; true; false; false; false; false; true; false; false; false; true] eq_refl) as h.
    cbn [toTape b2f rep010 Str_app] in h |- *.
    norm_s0. exact h.
  - pose proof (sweepsBoolTrim_sound 20 11
      [false; false; true; false; false; false; false; true; false; false; false; true]
      [false; true; false; false; true; false; false; true; false; false; true; false;
       false; false; false; false; true; false; false; false; false; true; false; false; false; true] eq_refl) as h.
    cbn [toTape b2f evalU evalCore fst snd rep010 pDiv0 Str_app] in h |- *.
    norm_s0. exact h.
Qed.

Lemma aCore_div0_sw0_sound :
    exists r', EraRound (evalCore (div0 0 sw0)) (rep010 0 r') /\ Sweeps 1 r' (evalU (1, sw0)).
Proof.
  exists (pB (evalCore sw0)).
  split; [exact (eraRound_pDiv0 (evalCore sw0)) | exact bCore_sw0_sound].
Qed.

Lemma aCore_div1_sw0_sound :
    EraRound (evalCore (div1 0 sw0)) (rep010 3 (evalCore sw1)).
Proof.
  pose proof (eraRound_pDiv1 round_sw0_sw1 aCore_sw1_sound) as h.
  cbn [evalCore rep010] in h |- *. exact h.
Qed.

Lemma levelU_gt_one_of_ne_sw0 {k : nat} {ch : CoreTree} (h : ~ (k = 0 /\ ch = sw0)) :
    2 <= levelU (k, ch).
Proof.
  destruct k as [| k'].
  - destruct ch as [| | | | k0 ch0 | k0 ch0];
      try (unfold levelU; cbn; lia).
    + exfalso; apply h; auto.
    + pose proof (levelCore_pos ch0); unfold levelU; cbn [fst snd levelCore]; lia.
    + pose proof (levelCore_pos ch0); unfold levelU; cbn [fst snd levelCore]; lia.
  - pose proof (levelCore_pos ch); unfold levelU; cbn [fst snd]; lia.
Qed.

Lemma bUFrom_sound {bCoreFn : CoreTree -> ResB} {fuel : nat}
    (hb : forall w : CoreTree, levelCore w <= fuel ->
      Sweeps (resB_c (bCoreFn w)) (pB (evalCore w)) (evalU (resB_u (bCoreFn w))))
    (u : UTree) (hu : levelU u <= fuel) :
    let res := bUFrom bCoreFn u in
    Sweeps (resB_c res) (pB (evalU u)) (evalU (resB_u res)).
Proof.
  destruct u as [k w]; cbn [bUFrom fst snd resB_c resB_u].
  assert (hcw : levelCore w <= fuel) by (unfold levelU in hu; cbn [fst snd] in hu; lia).
  pose proof (hb w hcw) as hsub.
  pose proof (sweeps_pB_rep010 k (evalCore_startsZero w)) as h1.
  pose proof (sweeps_rep010 k hsub) as h2.
  pose proof (Sweeps_trans h1 h2) as htr.
  unfold evalU in *; cbn [fst snd] in *.
  rewrite <- rep010_add in htr. exact htr.
Qed.

Lemma stepCore_eq_stepDefault {w : CoreTree} {t k : nat} (ht : coreTagIdx w = Some t) :
    stepCore k w = stepDefault (k + t).
Proof.
  destruct w; cbn [coreTagIdx] in ht; try discriminate;
    inversion ht; subst; cbn [stepCore]; f_equal; lia.
Qed.

Lemma aPullSucc_sound {aCoreFn : CoreTree -> ResP} {fuel k : nat} {w : CoreTree}
    (hk : 1 <= k)
    (ha : forall w' : CoreTree, levelCore w' <= fuel ->
      let res := aCoreFn w' in
      exists r', EraRound (evalCore w') (rep010 (resP_p res) r') /\ Sweeps (resP_c res) r' (evalU (resP_u res)))
    (hu : 3 * k + levelCore w <= fuel) :
    let res := aPullSucc aCoreFn k w in
    exists r', EraRound (rep010 k (evalCore w)) (rep010 (resP_p res) r') /\ Sweeps (resP_c res) r' (evalU (resP_u res)).
Proof.
  unfold aPullSucc.
  destruct (coreTagIdx w) as [t |] eqn:htag.
  - assert (ht_le : t <= 3 /\ levelCore w = t + 1).
    { destruct w; cbn [coreTagIdx] in htag; try discriminate;
        inversion htag; subst; cbn [levelCore]; lia. }
    destruct (Nat.leb_spec0 (k + t) 3) as [hs_le | hs_gt].
    + assert (h_mk : levelCore (mkSw (k + t)) = k + t + 1).
      { assert (k + t = 1 \/ k + t = 2 \/ k + t = 3) as [H | [H | H]] by lia;
          rewrite H; reflexivity. }
      assert (h_lvl : levelCore (mkSw (k + t)) <= fuel) by lia.
      destruct (ha (mkSw (k + t)) h_lvl) as [r' [hE hS]].
      exists r'; cbn [resP_p resP_c resP_u]; split; [| exact hS].
      assert (h_sw : Sweeps k (evalCore w) (evalCore (mkSw (k + t)))).
      { pose proof (stepCore_sound w k) as h_step.
        rewrite (stepCore_eq_stepDefault htag) in h_step.
        assert (h_eq : stepDefault (k + t) = (0, mkSw (k + t))).
        { assert (k + t = 1 \/ k + t = 2 \/ k + t = 3) as [H | [H | H]] by lia;
            rewrite H; reflexivity. }
        rewrite h_eq in h_step. exact h_step. }
      pose proof (eraRound_rep010 h_sw hE) as hE_rep.
      rewrite <- rep010_add in hE_rep. exact hE_rep.
    + assert (h_lvl : levelCore (stepDiv0Sw0 (k + t - 3)) <= fuel).
      { rewrite levelCore_stepDiv0Sw0; lia. }
      destruct (ha (stepDiv0Sw0 (k + t - 3)) h_lvl) as [r' [hE hS]].
      exists r'; cbn [resP_p resP_c resP_u]; split; [| exact hS].
      pose proof (stepCore_sound w k) as h_step.
      rewrite (stepCore_eq_stepDefault htag) in h_step.
      replace (k + t) with ((k + t - 4) + 4) in h_step by lia.
      rewrite stepDefault_add4_eq in h_step.
      unfold evalU in h_step; cbn [fst snd rep010] in h_step.
      assert (h1 : Round (evalCore (stepDiv0Sw0 (k + t - 4))) (evalCore (stepDiv0Sw0 (k + t - 3)))).
      { pose proof (round_stepDiv0Sw0 (k + t - 4)) as hr.
        replace (k + t - 4 + 1) with (k + t - 3) in hr by lia. exact hr. }
      pose proof (eraRound_010 h1 hE) as hE1.
      pose proof (eraRound_rep010 h_step hE1) as hE_rep.
      change (rep010 k ([S0; S1; S0] *> rep010 (resP_p (aCoreFn (stepDiv0Sw0 (k + t - 3)))) r'))
        with (rep010 k (rep010 1 (rep010 (resP_p (aCoreFn (stepDiv0Sw0 (k + t - 3)))) r'))) in hE_rep.
      rewrite <- !rep010_add in hE_rep.
      replace (k + (1 + resP_p (aCoreFn (stepDiv0Sw0 (k + t - 3)))))
        with (k + 1 + resP_p (aCoreFn (stepDiv0Sw0 (k + t - 3)))) in hE_rep by lia.
      exact hE_rep.
  - assert (h_lvl : levelCore (stepDivCore k w) <= fuel).
    { rewrite (levelCore_stepDivCore k w htag); lia. }
    destruct (ha (stepDivCore k w) h_lvl) as [r' [hE hS]].
    exists r'; cbn [resP_p resP_c resP_u]; split; [| exact hS].
    pose proof (stepDivCore_sound k w htag) as h_sw.
    pose proof (eraRound_rep010 h_sw hE) as hE_rep.
    rewrite <- rep010_add in hE_rep. exact hE_rep.
Qed.

Lemma aPullFrom_sound {aCoreFn : CoreTree -> ResP} {fuel : nat}
    (ha : forall w : CoreTree, levelCore w <= fuel ->
      let res := aCoreFn w in
      exists r', EraRound (evalCore w) (rep010 (resP_p res) r') /\ Sweeps (resP_c res) r' (evalU (resP_u res)))
    (u : UTree) (hu : levelU u <= fuel) :
    let res := aPullFrom aCoreFn u in
    exists r', EraRound (evalU u) (rep010 (resP_p res) r') /\ Sweeps (resP_c res) r' (evalU (resP_u res)).
Proof.
  destruct u as [[| k'] w]; unfold aPullFrom; cbn [fst snd].
  - unfold levelU in hu; cbn [fst snd] in hu.
    exact (ha w ltac:(lia)).
  - unfold levelU in hu; cbn [fst snd] in hu.
    exact (aPullSucc_sound (k := S k') ltac:(lia) ha hu).
Qed.

Lemma opsAux_sound (fuel : nat) :
    (forall w : CoreTree, levelCore w <= fuel ->
      let res := bCore (opsAux fuel) w in
      Sweeps (resB_c res) (pB (evalCore w)) (evalU (resB_u res))) /\
    (forall w : CoreTree, levelCore w <= fuel ->
      let res := aCore (opsAux fuel) w in
      exists r', EraRound (evalCore w) (rep010 (resP_p res) r') /\ Sweeps (resP_c res) r' (evalU (resP_u res))).
Proof.
  induction fuel as [| fuel [ihB ihA]].
  - split; intros w hw; pose proof (levelCore_pos w); lia.
  - split; intros w hw.
    + destruct w as [| | | | k ch | k ch]; cbn [opsAux bCore].
      * exact bCore_sw0_sound.
      * exact bCore_sw1_sound.
      * exact bCore_sw2_sound.
      * exact bCore_sw3_sound.
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resB_c resB_u].
        -- exact bCore_div0_sw0_sound.
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u1_lvl : levelU (stepU 1 (k, ch)) <= fuel).
           { rewrite levelU_stepU; cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           pose proof (round_of_sweeps_one (stepU_sound 1 (k, ch))) as h1.
           pose proof (sweeps_pB_pDiv0 h1) as h6.
           pose proof (bUFrom_sound ihB (stepU 1 (k, ch)) h_u1_lvl) as hsub.
           pose proof (sweeps_rep010 2 hsub) as hsub'.
           pose proof (Sweeps_trans h6 hsub') as htr.
           unfold evalU in htr |- *; cbn [fst snd] in htr |- *.
           rewrite <- rep010_add in htr. exact htr.
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resB_c resB_u].
        -- exact bCore_div1_sw0_sound.
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u1_lvl : levelU (stepU 1 (k, ch)) <= fuel).
           { rewrite levelU_stepU; cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           pose proof (round_of_sweeps_one (stepU_sound 1 (k, ch))) as h1.
           destruct (aPullFrom_sound ihA (stepU 1 (k, ch)) h_u1_lvl) as [r' [hE hS]].
           pose proof (sweeps_pB_pDiv1 h1 hE) as h3.
           set (sub := aPullFrom (aCore (opsAux fuel)) (stepU 1 (k, ch))) in *.
           pose proof (sweeps_rep010 (resP_p sub) hS) as hS_rep.
           pose proof (sweeps_010 (sweeps_pDiv0_even (sweeps_010 hS_rep))) as h2c.
           pose proof (Sweeps_trans h3 h2c) as htr.
           unfold evalU in htr |- *; cbn [fst snd rep010 evalCore] in htr |- *.
           change ([S0; S1; S0] *> rep010 (resP_p sub) (rep010 (fst (resP_u sub)) (evalCore (snd (resP_u sub)))))
             with (rep010 1 (rep010 (resP_p sub) (rep010 (fst (resP_u sub)) (evalCore (snd (resP_u sub)))))) in htr.
           rewrite <- !rep010_add in htr.
           replace (1 + (resP_p sub + fst (resP_u sub)))
             with (1 + resP_p sub + fst (resP_u sub)) in htr by lia.
           exact htr.
    + destruct w as [| | | | k ch | k ch]; cbn [opsAux aCore].
      * exists (evalCore sw1); split; [exact aCore_sw0_sound | apply Sweeps_zero].
      * exists (evalCore sw1); split; [exact aCore_sw1_sound | apply Sweeps_zero].
      * exact aCore_sw2_sound.
      * exact aCore_sw3_sound.
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resP_p resP_c resP_u].
        -- exact aCore_div0_sw0_sound.
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u_lvl : levelU (k, ch) <= fuel).
           { cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           pose proof (bUFrom_sound ihB (k, ch) h_u_lvl) as hsub.
           exists (pB (evalU (k, ch))).
           split; [exact (eraRound_pDiv0 (evalU (k, ch))) | exact hsub].
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resP_p resP_c resP_u].
        -- exists (evalCore sw1); split; [exact aCore_div1_sw0_sound | apply Sweeps_zero].
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u1_lvl : levelU (stepU 1 (k, ch)) <= fuel).
           { rewrite levelU_stepU; cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           pose proof (round_of_sweeps_one (stepU_sound 1 (k, ch))) as h1.
           destruct (aPullFrom_sound ihA (stepU 1 (k, ch)) h_u1_lvl) as [r' [hE hS]].
           pose proof (eraRound_pDiv1 h1 hE) as hE'.
           rewrite <- rep010_add in hE'.
           exists r'; split; [exact hE' | exact hS].
Qed.

(* ========================================================================== *)
(* Section 7: 4-Piecewise Linear Arithmetic Bounds                            *)
(* ========================================================================== *)

Definition min4 (a b c d : nat) : nat := Nat.min (Nat.min a b) (Nat.min c d).

Definition CB4 (x : nat) : nat := min4 (6 * x - 3) (3 * x + 10) ((3 * x) / 2 + 25) ((11 * x) / 16 + 67).
Definition CA4 (x : nat) : nat := min4 (3 * x) ((3 * x) / 2 + 10) ((3 * x) / 4 + 25) ((3 * x) / 8 + 64).
Definition DB4 (x : nat) : nat := min4 (6 * x - 2) (3 * x + 31) ((3 * x) / 2 + 70) ((5 * x) / 4 + 150).
Definition DAC4 (x : nat) : nat := min4 (4 * x - 1) ((3 * x) / 2 + 31) ((3 * x) / 4 + 70) ((21 * x) / 32 + 130).
Definition DAU4 (x : nat) : nat := min4 (4 * x - 1) ((9 * x) / 4 + 21) ((3 * x) / 2 + 31) ((5 * x) / 4 + 71).

Definition CAP (x : nat) : nat := Nat.max 11 (CB4 (x / 2)).
Definition DAP (x : nat) : nat := Nat.max 7 (DB4 (x / 2)).

Lemma le_min4 {x a b c d : nat} (ha : x <= a) (hb : x <= b) (hc : x <= c) (hd : x <= d) :
    x <= min4 a b c d.
Proof. unfold min4; lia. Qed.

Lemma CB4_le (x : nat) :
    CB4 x <= 6 * x - 3 /\ CB4 x <= 3 * x + 10 /\ CB4 x <= (3 * x) / 2 + 25 /\ CB4 x <= (11 * x) / 16 + 67.
Proof. unfold CB4, min4; lia. Qed.

Lemma CA4_le (x : nat) :
    CA4 x <= 3 * x /\ CA4 x <= (3 * x) / 2 + 10 /\ CA4 x <= (3 * x) / 4 + 25 /\ CA4 x <= (3 * x) / 8 + 64.
Proof. unfold CA4, min4; lia. Qed.

Lemma DB4_le (x : nat) :
    DB4 x <= 6 * x - 2 /\ DB4 x <= 3 * x + 31 /\ DB4 x <= (3 * x) / 2 + 70 /\ DB4 x <= (5 * x) / 4 + 150.
Proof. unfold DB4, min4; lia. Qed.

Lemma DAC4_le (x : nat) :
    DAC4 x <= 4 * x - 1 /\ DAC4 x <= (3 * x) / 2 + 31 /\ DAC4 x <= (3 * x) / 4 + 70 /\ DAC4 x <= (21 * x) / 32 + 130.
Proof. unfold DAC4, min4; lia. Qed.

Lemma DAU4_le (x : nat) :
    DAU4 x <= 4 * x - 1 /\ DAU4 x <= (9 * x) / 4 + 21 /\ DAU4 x <= (3 * x) / 2 + 31 /\ DAU4 x <= (5 * x) / 4 + 71.
Proof. unfold DAU4, min4; lia. Qed.

Lemma CB4_mono {x y : nat} (h : x <= y) : CB4 x <= CB4 y.
Proof.
  destruct (CB4_le x) as [h1 [h2 [h3 h4]]].
  unfold CB4 at 2; apply le_min4; dlia.
Qed.

Lemma CA4_mono {x y : nat} (h : x <= y) : CA4 x <= CA4 y.
Proof.
  destruct (CA4_le x) as [h1 [h2 [h3 h4]]].
  unfold CA4 at 2; apply le_min4; dlia.
Qed.

Lemma DB4_mono {x y : nat} (h : x <= y) : DB4 x <= DB4 y.
Proof.
  destruct (DB4_le x) as [h1 [h2 [h3 h4]]].
  unfold DB4 at 2; apply le_min4; dlia.
Qed.

Lemma CAP_mono {x y : nat} (h : x <= y) : CAP x <= CAP y.
Proof.
  pose proof (CB4_mono (y := y / 2) (x := x / 2) ltac:(dlia)).
  unfold CAP; lia.
Qed.

Lemma DAP_mono {x y : nat} (h : x <= y) : DAP x <= DAP y.
Proof.
  pose proof (DB4_mono (y := y / 2) (x := x / 2) ltac:(dlia)).
  unfold DAP; lia.
Qed.

Lemma bound_bCore_div0 {m c1 lu1 : nat} (hm : 2 <= m)
    (hc : c1 <= CB4 (m + 1)) (hd : lu1 <= c1 + DB4 (m + 1)) :
    6 + c1 <= CB4 (2 * m) /\ 6 + lu1 <= (6 + c1) + DB4 (2 * m).
Proof.
  destruct (CB4_le (m + 1)) as [h1 [h2 [h3 h4]]].
  pose proof (DB4_mono (x := m + 1) (y := 2 * m) ltac:(lia)).
  split; [unfold CB4; apply le_min4; dlia | lia].
Qed.

Lemma bound_bCore_div1 {m c1 p1 lu1 : nat} (hm : 2 <= m)
    (hc : c1 <= CA4 (m + 1)) (hd : 3 * p1 + lu1 <= c1 + DAU4 (m + 1)) :
    3 + 2 * c1 <= CB4 (2 * m + 1) /\
    9 + 2 * (3 * p1 + lu1) <= (3 + 2 * c1) + DB4 (2 * m + 1).
Proof.
  destruct (CA4_le (m + 1)) as [hc1 [hc2 [hc3 hc4]]].
  destruct (DAU4_le (m + 1)) as [hd1 [hd2 [hd3 hd4]]].
  split.
  - unfold CB4; apply le_min4; dlia.
  - assert (h_db : 6 + 2 * DAU4 (m + 1) <= DB4 (2 * m + 1)) by (unfold DB4; apply le_min4; dlia).
    lia.
Qed.

Lemma bound_bUFrom (k : nat) {mc c0 lu0 : nat} (hmc : 1 <= mc)
    (hc : c0 <= CB4 mc) (hd : lu0 <= c0 + DB4 mc) :
    2 * k + c0 <= CB4 (3 * k + mc) /\ 3 * k + lu0 <= (2 * k + c0) + DB4 (3 * k + mc).
Proof.
  destruct (CB4_le mc) as [hc1 [hc2 [hc3 hc4]]].
  destruct (DB4_le mc) as [hd1 [hd2 [hd3 hd4]]].
  split.
  - unfold CB4; apply le_min4; dlia.
  - assert (h_db : k + DB4 mc <= DB4 (3 * k + mc)) by (unfold DB4 at 2; apply le_min4; dlia).
    lia.
Qed.

Lemma bound_aCore_div0 {m c0 lu0 : nat} (hm : 2 <= m)
    (hc : c0 <= CB4 m) (hd : lu0 <= c0 + DB4 m) :
    c0 <= CA4 (2 * m) /\ c0 <= CAP (2 * m) /\
    lu0 <= c0 + DAC4 (2 * m) /\ lu0 <= c0 + DAP (2 * m).
Proof.
  destruct (CB4_le m) as [hc1 [hc2 [hc3 hc4]]].
  destruct (DB4_le m) as [hd1 [hd2 [hd3 hd4]]].
  assert (hdiv : (2 * m) / 2 = m) by dlia.
  split; [| split; [| split]].
  - unfold CA4; apply le_min4; dlia.
  - unfold CAP; rewrite hdiv; lia.
  - assert (h_da : DB4 m <= DAC4 (2 * m)) by (unfold DAC4; apply le_min4; dlia).
    lia.
  - unfold DAP; rewrite hdiv; lia.
Qed.

Lemma bound_aCore_div1 {m c1 p1 lu1 : nat} (hm : 2 <= m)
    (hc : c1 <= CA4 (m + 1)) (hcap : c1 <= CAP (m + 1))
    (hd : 3 * p1 + lu1 <= c1 + DAU4 (m + 1)) (hdap : lu1 <= c1 + DAP (m + 1)) :
    c1 <= CA4 (2 * m + 1) /\ c1 <= CAP (2 * m + 1) /\
    3 * (2 + p1) + lu1 <= c1 + DAC4 (2 * m + 1) /\ lu1 <= c1 + DAP (2 * m + 1).
Proof.
  destruct (DAU4_le (m + 1)) as [hd1 [hd2 [hd3 hd4]]].
  pose proof (CA4_mono (x := m + 1) (y := 2 * m + 1) ltac:(lia)).
  pose proof (CAP_mono (x := m + 1) (y := 2 * m + 1) ltac:(lia)).
  pose proof (DAP_mono (x := m + 1) (y := 2 * m + 1) ltac:(lia)).
  assert (h_da : 6 + DAU4 (m + 1) <= DAC4 (2 * m + 1)) by (unfold DAC4; apply le_min4; dlia).
  split; [lia | split; [lia | split; lia]].
Qed.

Lemma bound_aPull_sw_le {k t c0 p0 lu0 : nat} (hk : 1 <= k) (hs : k + t <= 3)
    (hc : c0 <= CA4 (k + t + 1)) (hcap : c0 <= CAP (k + t + 1))
    (hd : 3 * p0 + lu0 <= c0 + DAC4 (k + t + 1)) (hdap : lu0 <= c0 + DAP (k + t + 1)) :
    c0 <= CA4 (3 * k + (t + 1)) /\ c0 <= CAP (3 * k + (t + 1)) /\
    3 * (k + p0) + lu0 <= c0 + DAU4 (3 * k + (t + 1)) /\
    lu0 <= c0 + DAP (3 * k + (t + 1)).
Proof.
  destruct (DAC4_le (k + t + 1)) as [hd1 [hd2 [hd3 hd4]]].
  pose proof (CA4_mono (x := k + t + 1) (y := 3 * k + (t + 1)) ltac:(lia)).
  pose proof (CAP_mono (x := k + t + 1) (y := 3 * k + (t + 1)) ltac:(lia)).
  pose proof (DAP_mono (x := k + t + 1) (y := 3 * k + (t + 1)) ltac:(lia)).
  assert (h_da : 3 * k + DAC4 (k + t + 1) <= DAU4 (3 * k + (t + 1))) by (unfold DAU4; apply le_min4; dlia).
  split; [lia | split; [lia | split; lia]].
Qed.

Lemma bound_aPull_sw_gt {k t c0 p0 lu0 : nat} (hk : 1 <= k) (ht : t <= 3) (hs : 4 <= k + t)
    (hc : c0 <= CA4 (k + t - 1)) (hcap : c0 <= CAP (k + t - 1))
    (hd : 3 * p0 + lu0 <= c0 + DAC4 (k + t - 1)) (hdap : lu0 <= c0 + DAP (k + t - 1)) :
    c0 <= CA4 (3 * k + (t + 1)) /\ c0 <= CAP (3 * k + (t + 1)) /\
    3 * (k + 1 + p0) + lu0 <= c0 + DAU4 (3 * k + (t + 1)) /\
    lu0 <= c0 + DAP (3 * k + (t + 1)).
Proof.
  destruct (DAC4_le (k + t - 1)) as [hd1 [hd2 [hd3 hd4]]].
  pose proof (CA4_mono (x := k + t - 1) (y := 3 * k + (t + 1)) ltac:(lia)).
  pose proof (CAP_mono (x := k + t - 1) (y := 3 * k + (t + 1)) ltac:(lia)).
  pose proof (DAP_mono (x := k + t - 1) (y := 3 * k + (t + 1)) ltac:(lia)).
  assert (h_da : 3 * (k + 1) + DAC4 (k + t - 1) <= DAU4 (3 * k + (t + 1))) by (unfold DAU4; apply le_min4; dlia).
  split; [lia | split; [lia | split; lia]].
Qed.

Lemma bound_aPull_div {k mc c0 p0 lu0 : nat} (hk : 1 <= k) (hmc : 2 <= mc)
    (hc : c0 <= CA4 (mc + k)) (hcap : c0 <= CAP (mc + k))
    (hd : 3 * p0 + lu0 <= c0 + DAC4 (mc + k)) (hdap : lu0 <= c0 + DAP (mc + k)) :
    c0 <= CA4 (3 * k + mc) /\ c0 <= CAP (3 * k + mc) /\
    3 * (k + p0) + lu0 <= c0 + DAU4 (3 * k + mc) /\
    lu0 <= c0 + DAP (3 * k + mc).
Proof.
  destruct (DAC4_le (mc + k)) as [hd1 [hd2 [hd3 hd4]]].
  pose proof (CA4_mono (x := mc + k) (y := 3 * k + mc) ltac:(lia)).
  pose proof (CAP_mono (x := mc + k) (y := 3 * k + mc) ltac:(lia)).
  pose proof (DAP_mono (x := mc + k) (y := 3 * k + mc) ltac:(lia)).
  assert (h_da : 3 * k + DAC4 (mc + k) <= DAU4 (3 * k + mc)) by (unfold DAU4; apply le_min4; dlia).
  split; [lia | split; [lia | split; lia]].
Qed.

Lemma bUFrom_bounds {bCoreFn : CoreTree -> ResB} {fuel : nat}
    (hb : forall w : CoreTree, levelCore w <= fuel ->
      let res := bCoreFn w in
      resB_c res <= CB4 (levelCore w) /\ levelU (resB_u res) <= resB_c res + DB4 (levelCore w))
    (u : UTree) (hu : levelU u <= fuel) :
    let res := bUFrom bCoreFn u in
    resB_c res <= CB4 (levelU u) /\ levelU (resB_u res) <= resB_c res + DB4 (levelU u).
Proof.
  destruct u as [k w]; unfold bUFrom; cbn [fst snd resB_c resB_u].
  assert (hcw : levelCore w <= fuel) by (unfold levelU in hu; cbn [fst snd] in hu; lia).
  destruct (hb w hcw) as [hc hd].
  destruct (bound_bUFrom k (levelCore_pos w) hc hd) as [h1 h2].
  unfold levelU in *; cbn [fst snd] in *.
  split; [exact h1 | lia].
Qed.

Lemma levelCore_ge_two_of_none {w : CoreTree} (hw : coreTagIdx w = None) :
    2 <= levelCore w.
Proof.
  destruct w as [| | | | k ch | k ch]; try discriminate;
    pose proof (levelCore_pos ch); cbn [levelCore]; lia.
Qed.

Lemma DAC4_le_DAU4 (x : nat) : DAC4 x <= DAU4 x.
Proof.
  destruct (DAC4_le x) as [h1 [h2 [h3 h4]]].
  assert (x <= 12 \/ x = 13 \/ x = 14 \/ 15 <= x) as [hx | [-> | [-> | hx]]] by lia.
  - unfold DAU4; apply le_min4; dlia.
  - vm_compute; lia.
  - vm_compute; lia.
  - unfold DAU4; apply le_min4; dlia.
Qed.

Lemma aPullSucc_bounds {aCoreFn : CoreTree -> ResP} {fuel k : nat} {w : CoreTree}
    (hk : 1 <= k)
    (ha : forall w' : CoreTree, levelCore w' <= fuel ->
      let res := aCoreFn w' in
      resP_c res <= CA4 (levelCore w') /\ resP_c res <= CAP (levelCore w') /\
      3 * resP_p res + levelU (resP_u res) <= resP_c res + DAC4 (levelCore w') /\
      levelU (resP_u res) <= resP_c res + DAP (levelCore w'))
    (hu : 3 * k + levelCore w <= fuel) :
    let res := aPullSucc aCoreFn k w in
    resP_c res <= CA4 (3 * k + levelCore w) /\ resP_c res <= CAP (3 * k + levelCore w) /\
    3 * resP_p res + levelU (resP_u res) <= resP_c res + DAU4 (3 * k + levelCore w) /\
    levelU (resP_u res) <= resP_c res + DAP (3 * k + levelCore w).
Proof.
  unfold aPullSucc.
  destruct (coreTagIdx w) as [t |] eqn:htag.
  - assert (ht_le : t <= 3 /\ levelCore w = t + 1).
    { destruct w; cbn [coreTagIdx] in htag; try discriminate;
        inversion htag; subst; cbn [levelCore]; lia. }
    destruct ht_le as [ht_le1 ht_le2].
    destruct (Nat.leb_spec0 (k + t) 3) as [hs_le | hs_gt].
    + assert (h_mk : levelCore (mkSw (k + t)) = k + t + 1).
      { assert (k + t = 1 \/ k + t = 2 \/ k + t = 3) as [H | [H | H]] by lia;
          rewrite H; reflexivity. }
      assert (h_lvl : levelCore (mkSw (k + t)) <= fuel) by lia.
      destruct (ha (mkSw (k + t)) h_lvl) as [hc [hcap [hd hdap]]].
      rewrite h_mk in hc, hcap, hd, hdap.
      rewrite ht_le2; cbn [resP_p resP_c resP_u].
      exact (bound_aPull_sw_le hk hs_le hc hcap hd hdap).
    + assert (h_mk : levelCore (stepDiv0Sw0 (k + t - 3)) = k + t - 1).
      { rewrite levelCore_stepDiv0Sw0; lia. }
      assert (h_lvl : levelCore (stepDiv0Sw0 (k + t - 3)) <= fuel) by lia.
      destruct (ha (stepDiv0Sw0 (k + t - 3)) h_lvl) as [hc [hcap [hd hdap]]].
      rewrite h_mk in hc, hcap, hd, hdap.
      rewrite ht_le2; cbn [resP_p resP_c resP_u].
      exact (bound_aPull_sw_gt hk ht_le1 ltac:(lia) hc hcap hd hdap).
  - pose proof (levelCore_ge_two_of_none htag) as hmc2.
    pose proof (levelCore_stepDivCore k w htag) as h_mk.
    assert (h_lvl : levelCore (stepDivCore k w) <= fuel) by lia.
    destruct (ha (stepDivCore k w) h_lvl) as [hc [hcap [hd hdap]]].
    rewrite h_mk in hc, hcap, hd, hdap.
    cbn [resP_p resP_c resP_u].
    exact (bound_aPull_div hk hmc2 hc hcap hd hdap).
Qed.

Lemma aPullFrom_bounds {aCoreFn : CoreTree -> ResP} {fuel : nat}
    (ha : forall w : CoreTree, levelCore w <= fuel ->
      let res := aCoreFn w in
      resP_c res <= CA4 (levelCore w) /\ resP_c res <= CAP (levelCore w) /\
      3 * resP_p res + levelU (resP_u res) <= resP_c res + DAC4 (levelCore w) /\
      levelU (resP_u res) <= resP_c res + DAP (levelCore w))
    (u : UTree) (hu : levelU u <= fuel) :
    let res := aPullFrom aCoreFn u in
    resP_c res <= CA4 (levelU u) /\ resP_c res <= CAP (levelU u) /\
    3 * resP_p res + levelU (resP_u res) <= resP_c res + DAU4 (levelU u) /\
    levelU (resP_u res) <= resP_c res + DAP (levelU u).
Proof.
  destruct u as [[| k'] w]; unfold aPullFrom; cbn [fst snd].
  - assert (hlu0 : levelU (0, w) = levelCore w) by reflexivity.
    rewrite hlu0 in hu |- *.
    destruct (ha w hu) as [hc [hcap [hd hdap]]].
    pose proof (DAC4_le_DAU4 (levelCore w)).
    split; [exact hc | split; [exact hcap | split; [lia | exact hdap]]].
  - assert (hlu : levelU (S k', w) = 3 * S k' + levelCore w) by reflexivity.
    rewrite hlu in hu |- *.
    exact (aPullSucc_bounds (k := S k') ltac:(lia) ha hu).
Qed.

Lemma opsAux_bounds (fuel : nat) :
    (forall w : CoreTree, levelCore w <= fuel ->
      let res := bCore (opsAux fuel) w in
      resB_c res <= CB4 (levelCore w) /\ levelU (resB_u res) <= resB_c res + DB4 (levelCore w)) /\
    (forall w : CoreTree, levelCore w <= fuel ->
      let res := aCore (opsAux fuel) w in
      resP_c res <= CA4 (levelCore w) /\ resP_c res <= CAP (levelCore w) /\
      3 * resP_p res + levelU (resP_u res) <= resP_c res + DAC4 (levelCore w) /\
      levelU (resP_u res) <= resP_c res + DAP (levelCore w)).
Proof.
  induction fuel as [| fuel [ihB ihA]].
  - split; intros w hw; pose proof (levelCore_pos w); lia.
  - split; intros w hw.
    + destruct w as [| | | | k ch | k ch]; cbn [opsAux bCore].
      * vm_compute; split; lia.
      * vm_compute; split; lia.
      * vm_compute; split; lia.
      * vm_compute; split; lia.
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resB_c resB_u].
        -- vm_compute; split; lia.
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u1_lvl : levelU (stepU 1 (k, ch)) <= fuel).
           { rewrite levelU_stepU; cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           destruct (bUFrom_bounds ihB (stepU 1 (k, ch)) h_u1_lvl) as [hc hd].
           rewrite levelU_stepU in hc, hd.
           destruct (bound_bCore_div0 hm2 hc hd) as [hb1 hb2].
           cbn [levelCore]; unfold levelU in *; cbn [fst snd] in *.
           split; [exact hb1 | lia].
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resB_c resB_u].
        -- vm_compute; split; lia.
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u1_lvl : levelU (stepU 1 (k, ch)) <= fuel).
           { rewrite levelU_stepU; cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           destruct (aPullFrom_bounds ihA (stepU 1 (k, ch)) h_u1_lvl) as [hc [_ [hd _]]].
           rewrite levelU_stepU in hc, hd.
           destruct (bound_bCore_div1 hm2 hc hd) as [hb1 hb2].
           cbn [levelCore]; unfold levelU in *; cbn [fst snd levelCore] in *.
           split; [exact hb1 | lia].
    + destruct w as [| | | | k ch | k ch]; cbn [opsAux aCore].
      * vm_compute; repeat split; lia.
      * vm_compute; repeat split; lia.
      * vm_compute; repeat split; lia.
      * vm_compute; repeat split; lia.
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resP_p resP_c resP_u].
        -- vm_compute; repeat split; lia.
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u_lvl : levelU (k, ch) <= fuel).
           { cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           destruct (bUFrom_bounds ihB (k, ch) h_u_lvl) as [hc hd].
           destruct (bound_aCore_div0 hm2 hc hd) as [ha1 [ha2 [ha3 ha4]]].
           cbn [levelCore]; unfold levelU in *; cbn [fst snd] in *.
           split; [exact ha1 | split; [exact ha2 | split; [lia | exact ha4]]].
      * destruct (zero_sw0_cases k ch) as [[-> [-> Hcond]] | [Hne Hcond]]; rewrite Hcond; cbn [resP_p resP_c resP_u].
        -- vm_compute; repeat split; lia.
        -- pose proof (levelU_gt_one_of_ne_sw0 Hne) as hm2.
           assert (h_u1_lvl : levelU (stepU 1 (k, ch)) <= fuel).
           { rewrite levelU_stepU; cbn [levelCore] in hw; unfold levelU in hm2 |- *; cbn [fst snd] in *; lia. }
           destruct (aPullFrom_bounds ihA (stepU 1 (k, ch)) h_u1_lvl) as [hc [hcap [hd hdap]]].
           rewrite levelU_stepU in hc, hcap, hd, hdap.
           destruct (bound_aCore_div1 hm2 hc hcap hd hdap) as [ha1 [ha2 [ha3 ha4]]].
           cbn [levelCore]; unfold levelU in *; cbn [fst snd] in *.
           split; [exact ha1 | split; [exact ha2 | split; [exact ha3 | exact ha4]]].
Qed.

(* ========================================================================== *)
(* Section 8: Finite Bridge (init -> Era 1 -> Era 133) & Infinite Invariant   *)
(* ========================================================================== *)

Definition eraStepBool (fuel : nat) (bs : list bool) : option (list bool) :=
  match pad7B bs with
  | false :: v => option_map (fun r' => false :: true :: false :: r') (roundBool fuel v)
  | _ => None
  end.

Lemma eraStepBool_sound (fuel : nat) (bs ys : list bool)
    (h : eraStepBool fuel bs = Some ys) :
    (s0inf <{{D}} (toTape bs)) -[ tm ]->+ (s0inf <{{D}} (toTape ys)).
Proof.
  rewrite <- (toTape_pad7B bs).
  unfold eraStepBool in h.
  destruct (pad7B bs) as [| [|] v]; try discriminate.
  apply opt_map_some in h as [r' [Hr' <-]].
  cbn [toTape b2f].
  apply eraRound_tm_step.
  exists (toTape v); split; [reflexivity | exact (roundBool_sound fuel v r' Hr')].
Qed.

Fixpoint eraStepsBool (fuel m : nat) (bs : list bool) : option (list bool) :=
  match m with
  | 0 => Some bs
  | S m' =>
    match eraStepBool fuel bs with
    | Some bs1 => eraStepsBool fuel m' bs1
    | None => None
    end
  end.

Lemma eraStepsBool_sound (fuel m : nat) : forall (bs ys : list bool),
    eraStepsBool fuel m bs = Some ys ->
    (s0inf <{{D}} (toTape bs)) -[ tm ]->* (s0inf <{{D}} (toTape ys)).
Proof.
  induction m as [| m IH]; intros bs ys h; cbn [eraStepsBool] in h.
  - inversion h; subst; apply evstep_refl.
  - destruct (eraStepBool fuel bs) as [bs1 |] eqn:Hs; [| discriminate].
    eapply evstep_trans; [apply progress_evstep; exact (eraStepBool_sound fuel bs bs1 Hs) |].
    exact (IH bs1 ys h).
Qed.

Fixpoint rep010Bool (k : nat) (bs : list bool) : list bool :=
  match k with
  | 0 => bs
  | S k' => false :: true :: false :: rep010Bool k' bs
  end.

Lemma toTape_rep010Bool (k : nat) (bs : list bool) :
    toTape (rep010Bool k bs) = rep010 k (toTape bs).
Proof.
  induction k as [| k IH]; [reflexivity |].
  cbn [rep010Bool rep010 toTape b2f Str_app]. rewrite IH. reflexivity.
Qed.

Lemma init_reaches_era0 :
    c0 -[ tm ]->+ (s0inf <{{D}} (toTape [false; true])).
Proof.
  cbn [toTape b2f]. start_progress.
Qed.

Lemma init_reaches_era1 :
    c0 -[ tm ]->* (s0inf <{{D}} (rep010 3 (evalCore sw1))).
Proof.
  assert (h1 : option_map dropTrailingFalse (eraStepsBool 20 1 [false; true]) =
      Some (rep010Bool 3 [false; false; true])) by (vm_compute; reflexivity).
  apply opt_map_some in h1 as [ys [hys hdrop]].
  pose proof (eraStepsBool_sound 20 1 [false; true] ys hys) as hstar.
  assert (h_ys : toTape ys = rep010 3 (evalCore sw1)).
  { rewrite <- (toTape_dropTrailingFalse ys), hdrop, toTape_rep010Bool.
    cbn [toTape b2f evalCore Str_app]. reflexivity. }
  rewrite h_ys in hstar.
  eapply evstep_trans; [apply progress_evstep; exact init_reaches_era0 | exact hstar].
Qed.

Definition stepEraU (N : nat) (u : UTree) : option (nat * UTree) :=
  let res := aPullFrom (aCore (opsAux (levelU u))) u in
  let N' := N + 1 + resP_p res in
  if resP_c res <=? N' then
    Some (N', stepU (N' - resP_c res) (resP_u res))
  else
    None.

Lemma stepEraU_sound {N N' : nat} {rem : side} {u u' : UTree}
    (hS : Sweeps N rem (evalU u)) (hstep : stepEraU N u = Some (N', u')) :
    exists rem', ((s0inf <{{D}} (rep010 N rem)) -[ tm ]->+ (s0inf <{{D}} (rep010 N' rem'))) /\
      Sweeps N' rem' (evalU u').
Proof.
  unfold stepEraU in hstep.
  set (res := aPullFrom (aCore (opsAux (levelU u))) u) in *.
  set (N1 := N + 1 + resP_p res) in *.
  destruct (Nat.leb_spec0 (resP_c res) N1) as [hle |]; [| discriminate].
  inversion hstep; subst N' u'; clear hstep.
  pose proof (proj2 (opsAux_sound (levelU u))) as ha.
  destruct (aPullFrom_sound ha u (Nat.le_refl _)) as [r' [hE hSr]].
  fold res in hE, hSr.
  pose proof (eraRound_rep010 hS hE) as hE_rep.
  pose proof (eraRound_tm_step hE_rep) as htm.
  rewrite <- rep010_add in htm.
  change ([S0; S1; S0] *> rep010 (N + resP_p res) r')
    with (rep010 1 (rep010 (N + resP_p res) r')) in htm.
  rewrite <- rep010_add in htm.
  replace (1 + (N + resP_p res)) with N1 in htm by (unfold N1; lia).
  pose proof (stepU_sound (N1 - resP_c res) (resP_u res)) as hSu.
  pose proof (Sweeps_trans hSr hSu) as htr.
  replace (resP_c res + (N1 - resP_c res)) with N1 in htr by lia.
  exists r'; split; [exact htm | exact htr].
Qed.

Fixpoint runEras (m N : nat) (u : UTree) : option (nat * UTree) :=
  match m with
  | 0 => Some (N, u)
  | S m' =>
    match stepEraU N u with
    | Some (N', u') => runEras m' N' u'
    | None => None
    end
  end.

Lemma runEras_sound (m : nat) : forall (N N_m : nat) (rem : side) (u u_m : UTree),
    Sweeps N rem (evalU u) -> runEras m N u = Some (N_m, u_m) ->
    exists rem_m, ((s0inf <{{D}} (rep010 N rem)) -[ tm ]->* (s0inf <{{D}} (rep010 N_m rem_m))) /\
      Sweeps N_m rem_m (evalU u_m).
Proof.
  induction m as [| m IH]; intros N N_m rem u u_m hS hrun; cbn [runEras] in hrun.
  - inversion hrun; subst. exists rem; split; [apply evstep_refl | exact hS].
  - destruct (stepEraU N u) as [[N' u'] |] eqn:hs; [| discriminate].
    destruct (stepEraU_sound hS hs) as [rem' [htm1 hS1]].
    destruct (IH N' N_m rem' u' u_m hS1 hrun) as [rem_m [htm_m hS_m]].
    exists rem_m; split; [| exact hS_m].
    eapply evstep_trans; [apply progress_evstep; exact htm1 | exact htm_m].
Qed.

Definition checkBridge : bool :=
  match runEras 132 3 (stepU 3 (0, sw1)) with
  | Some (N, u) => (2440 <=? N) && (3 * levelU u <=? 8 * N + 1200)
  | None => false
  end.

Lemma checkBridge_eq_true : checkBridge = true.
Proof. vm_compute. reflexivity. Qed.

Lemma era_inv_cap_le {N n : nat} (hN : 2440 <= N) (hn : 3 * n <= 8 * N + 1200) :
    CAP n <= N + 1.
Proof.
  destruct (CB4_le (n / 2)) as [_ [_ [_ h4]]].
  unfold CAP; dlia.
Qed.

Lemma era_inv_dap_le {N N' n c lu : nat} (hN : 2440 <= N) (hN' : N + 1 <= N')
    (hn : 3 * n <= 8 * N + 1200) (hc : c <= N') (hd : lu <= c + DAP n) :
    2440 <= N' /\ 3 * (lu + (N' - c)) <= 8 * N' + 1200.
Proof.
  destruct (DB4_le (n / 2)) as [_ [_ [_ h4]]].
  unfold DAP in hd; dlia.
Qed.

Definition EraInv (cfg : Q * tape) : Prop :=
  exists (N : nat) (rem : side) (u : UTree),
    2440 <= N /\ 3 * levelU u <= 8 * N + 1200 /\
    Sweeps N rem (evalU u) /\
    cfg = (s0inf <{{D}} (rep010 N rem)).

Lemma era_inv_init : exists cfg0, (c0 -[ tm ]->* cfg0) /\ EraInv cfg0.
Proof.
  pose proof checkBridge_eq_true as hb.
  unfold checkBridge in hb.
  destruct (runEras 132 3 (stepU 3 (0, sw1))) as [[N_133 u_133] |] eqn:hrun; [| discriminate].
  apply andb_prop in hb as [hb1 hb2].
  apply Nat.leb_le in hb1.
  apply Nat.leb_le in hb2.
  pose proof (stepU_sound 3 (0, sw1)) as hS1.
  destruct (runEras_sound 132 3 N_133 (evalCore sw1) (stepU 3 (0, sw1)) u_133 hS1 hrun)
    as [rem_133 [hstar_bridge hS_133]].
  exists (s0inf <{{D}} (rep010 N_133 rem_133)).
  split.
  - eapply evstep_trans; [exact init_reaches_era1 | exact hstar_bridge].
  - exists N_133, rem_133, u_133; repeat split; auto.
Qed.

Lemma era_inv_step (cfg : Q * tape) (hinv : EraInv cfg) :
    exists cfg', EraInv cfg' /\ (cfg -[ tm ]->+ cfg').
Proof.
  destruct hinv as [N [rem [u [hN [hn [hS ->]]]]]].
  pose proof (proj2 (opsAux_bounds (levelU u))) as ha_b.
  destruct (aPullFrom_bounds ha_b u (Nat.le_refl (levelU u))) as [_ [hcap [_ hdap]]].
  set (res := aPullFrom (aCore (opsAux (levelU u))) u) in *.
  set (N' := N + 1 + resP_p res).
  assert (hc_le : resP_c res <= N').
  { pose proof (era_inv_cap_le hN hn). unfold N'; lia. }
  assert (hstep : stepEraU N u = Some (N', stepU (N' - resP_c res) (resP_u res))).
  { unfold stepEraU; fold res; fold N'.
    destruct (Nat.leb_spec0 (resP_c res) N'); [reflexivity | lia]. }
  destruct (stepEraU_sound hS hstep) as [rem' [htm hS']].
  destruct (era_inv_dap_le hN (N' := N') ltac:(unfold N'; lia) hn hc_le hdap) as [hN' hlu'].
  exists (s0inf <{{D}} (rep010 N' rem')).
  split; [| exact htm].
  exists N', rem', (stepU (N' - resP_c res) (resP_u res)).
  repeat split; auto.
  rewrite levelU_stepU. exact hlu'.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  destruct era_inv_init as [cfg0 [hstar hinv0]].
  eapply multistep_nonhalt; [exact hstar |].
  eapply progress_nonhalt; [exact era_inv_step | exact hinv0].
Qed.

Print Assumptions nonhalt.
