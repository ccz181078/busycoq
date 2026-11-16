(* Classification: BEC.
   Consolidated from busycoq PR #22, #23, #25, #28, pinned in PR19_28_INVENTORY.json.
   Original proofs: Dahoas; Dennis Koshta.
   Common declarations are reused; each blank-state initialization is checked separately. *)

From BusyCoq Require Import Individual62.
From Coq Require Import String List Bool Arith PeanoNat Lia.
From Coq Require Import Lists.Streams.

Module TM1.
Import BusyCoq.Individual62.

Import String List Bool Arith PeanoNat Lia.

Import Streams.

Import ListNotations.

Close Scope sym.

Open Scope nat_scope.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1LE1LD_0LB0RE_1RF0LA_---0RA").

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

Lemma rule_B_000 (l r : side) :
  ([S0; S0; S0] *> r) <{{B}} l -[ tm ]->+ ([S0; S0; S1] *> r) {{A}}> l.
Proof. start_progress. Qed.

Lemma rule_B_0011 (l r : side) :
  ([S0; S0; S1; S1] *> r) <{{B}} l -[ tm ]->+ ([S0; S1; S0; S0] *> r) {{A}}> l.
Proof. start_progress. Qed.

Lemma rule_B_00100 (l r : side) :
  ([S0; S0; S1; S0; S0] *> r) <{{B}} l -[ tm ]->+ r <{{B}} (l <* [S0; S1; S1; S1; S1]).
Proof. start_progress. Qed.

Lemma rule_B_001010 (l r : side) :
  ([S0; S0; S1; S0; S1; S0] *> r) <{{B}} l -[ tm ]->+ r <{{B}} (l <* [S0; S1; S1; S1; S1; S1]).
Proof. start_progress. Qed.

Lemma rule_B_0010110 (l r : side) :
  ([S0; S0; S1; S0; S1; S1; S0] *> r) <{{B}} l -[ tm ]->+ r <{{B}} (l <* [S0; S1; S1; S1; S1; S1; S1]).
Proof. start_progress. Qed.

Lemma rule_B_010 (l r : side) :
  ([S0; S1; S0] *> r) <{{B}} l -[ tm ]->+ r <{{B}} (l <* [S0; S1; S1]).
Proof. start_progress. Qed.

Lemma rule_B_0110 (l r : side) :
  ([S0; S1; S1; S0] *> r) <{{B}} l -[ tm ]->+ r <{{B}} (l <* [S0; S1; S1; S1]).
Proof. start_progress. Qed.

Lemma rule_B_10 (l r : side) :
  ([S1; S0] *> r) <{{B}} l -[ tm ]->+ r <{{B}} (l <* [S0; S0]).
Proof. start_progress. Qed.

Lemma rule_E_01111 (l r : side) :
  r {{A}}> (l <* [S0; S1; S1; S1; S1]) -[ tm ]->+ ([S0; S0; S0; S1; S0] *> r) {{A}}> l.
Proof. start_progress. Qed.

Lemma rule_E_011111 (l r : side) :
  r {{A}}> (l <* [S0; S1; S1; S1; S1; S1]) -[ tm ]->+ ([S0; S0; S0; S0; S1; S0] *> r) {{A}}> l.
Proof. start_progress. Qed.

Lemma rule_E_0111111 (l r : side) :
  r {{A}}> (l <* [S0; S1; S1; S1; S1; S1; S1]) -[ tm ]->+ ([S0; S0; S0; S0; S0; S1; S0] *> r) {{A}}> l.
Proof. start_progress. Qed.

Lemma rule_E_011 (l r : side) :
  r {{A}}> (l <* [S0; S1; S1]) -[ tm ]->+ ([S0; S1; S0] *> r) {{A}}> l.
Proof. start_progress. Qed.

Lemma rule_E_0111 (l r : side) :
  r {{A}}> (l <* [S0; S1; S1; S1]) -[ tm ]->+ ([S0; S0; S1; S0] *> r) {{A}}> l.
Proof. start_progress. Qed.

Lemma rule_E_00 (l r : side) :
  (S0 >> r) {{A}}> (l <* [S0; S0]) -[ tm ]->+ r <{{B}} (l <* [S0; S1; S1]).
Proof. start_progress. Qed.

Lemma rule_E_nil (r : side) :
  (S0 >> r) {{A}}> s0inf -[ tm ]->+ r <{{B}} (s0inf <* [S0; S1; S1]).
Proof. start_progress. Qed.

Definition Round (r r' : side) : Prop :=
  forall l : side, (r <{{B}} l) -[ tm ]->+ (r' {{A}}> l).

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
  -  
    destruct l1 as [| [|] rest]; [discriminate | discriminate |].
    destruct (roundBool fuel rest) as [[| [|] r1] |] eqn:Hr1; try discriminate.
    apply opt_map_some in h as [r2 [Hr2 <-]].
    cbn [toTape b2f Str_app].
    exact (round_10 (IH rest (false :: r1) Hr1) (IH r1 r2 Hr2)).
  -  
    destruct l1 as [| [|] l2]; [discriminate | |].
    +  
      destruct l2 as [| [|] l3]; [discriminate | |].
      *  
        destruct l3 as [| [|] rest]; [discriminate | discriminate |].
        apply opt_map_some in h as [r' [Hr' <-]].
        cbn [toTape b2f Str_app].
        exact (round_0110 (IH rest r' Hr')).
      *  
        apply opt_map_some in h as [r' [Hr' <-]].
        cbn [toTape b2f Str_app].
        exact (round_010 (IH l3 r' Hr')).
    +  
      destruct l2 as [| [|] l3]; [discriminate | |].
      *  
        destruct l3 as [| [|] l4]; [discriminate | |].
        --  
           inversion h; subst; clear h.
           cbn [toTape b2f Str_app].
           exact (round_0011 (toTape l4)).
        --  
           destruct l4 as [| [|] l5]; [discriminate | |].
           ++  
              destruct l5 as [| [|] l6]; [discriminate | |].
              **  
                 destruct l6 as [| [|] rest]; [discriminate | discriminate |].
                 apply opt_map_some in h as [r' [Hr' <-]].
                 cbn [toTape b2f Str_app].
                 exact (round_0010110 (IH rest r' Hr')).
              **  
                 apply opt_map_some in h as [r' [Hr' <-]].
                 cbn [toTape b2f Str_app].
                 exact (round_001010 (IH l6 r' Hr')).
           ++  
              apply opt_map_some in h as [r' [Hr' <-]].
              cbn [toTape b2f Str_app].
              exact (round_00100 (IH l5 r' Hr')).
      *  
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
    (u {{A}}> s0inf) -[ tm ]->+ (([S0; S1; S0] *> r') {{A}}> s0inf).
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

Definition eraStepBool (fuel : nat) (bs : list bool) : option (list bool) :=
  match pad7B bs with
  | false :: v => option_map (fun r' => false :: true :: false :: r') (roundBool fuel v)
  | _ => None
  end.

Lemma eraStepBool_sound (fuel : nat) (bs ys : list bool)
    (h : eraStepBool fuel bs = Some ys) :
    ((toTape bs) {{A}}> s0inf) -[ tm ]->+ ((toTape ys) {{A}}> s0inf).
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
    ((toTape bs) {{A}}> s0inf) -[ tm ]->* ((toTape ys) {{A}}> s0inf).
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

Lemma init_reaches_era5 :
    c0 -[ tm ]->* ((rep010 17 (evalCore sw1)) {{A}}> s0inf).
Proof.
  assert (h5 : option_map dropTrailingFalse (eraStepsBool 20 5 []) =
      Some (rep010Bool 17 [false; false; true])) by (vm_compute; reflexivity).
  apply opt_map_some in h5 as [ys [hys hdrop]].
  pose proof (eraStepsBool_sound 20 5 [] ys hys) as hstar.
  assert (h_ys : toTape ys = rep010 17 (evalCore sw1)).
  { rewrite <- (toTape_dropTrailingFalse ys), hdrop, toTape_rep010Bool.
    cbn [toTape b2f evalCore Str_app]. reflexivity. }
  rewrite h_ys in hstar. exact hstar.
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
    exists rem', (((rep010 N rem) {{A}}> s0inf) -[ tm ]->+ ((rep010 N' rem') {{A}}> s0inf)) /\
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
    exists rem_m, (((rep010 N rem) {{A}}> s0inf) -[ tm ]->* ((rep010 N_m rem_m) {{A}}> s0inf)) /\
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
  match runEras 126 17 (stepU 17 (0, sw1)) with
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
    cfg = ((rep010 N rem) {{A}}> s0inf).

Lemma era_inv_init : exists cfg0, (c0 -[ tm ]->* cfg0) /\ EraInv cfg0.
Proof.
  pose proof checkBridge_eq_true as hb.
  unfold checkBridge in hb.
  destruct (runEras 126 17 (stepU 17 (0, sw1))) as [[N_131 u_131] |] eqn:hrun; [| discriminate].
  apply andb_prop in hb as [hb1 hb2].
  apply Nat.leb_le in hb1.
  apply Nat.leb_le in hb2.
  pose proof (stepU_sound 17 (0, sw1)) as hS5.
  destruct (runEras_sound 126 17 N_131 (evalCore sw1) (stepU 17 (0, sw1)) u_131 hS5 hrun)
    as [rem_131 [hstar_bridge hS_131]].
  exists ((rep010 N_131 rem_131) {{A}}> s0inf).
  split.
  - eapply evstep_trans; [exact init_reaches_era5 | exact hstar_bridge].
  - exists N_131, rem_131, u_131; repeat split; auto.
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
  exists ((rep010 N' rem') {{A}}> s0inf).
  split; [| exact htm].
  exists N', rem', (stepU (N' - resP_c res) (resP_u res)).
  repeat split; auto.
  rewrite levelU_stepU. exact hlu'.
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  destruct era_inv_init as [cfg0 [hstar hinv0]].
  eapply multistep_nonhalt; [exact hstar |].
  eapply progress_nonhalt; [exact era_inv_step | exact hinv0].
Qed.

End TM1.
Print Assumptions TM1.nonhalt.



Module TM2.
Import BusyCoq.Individual62.

Import String List Bool Arith PeanoNat Lia.

Import Streams.

Import ListNotations.

Close Scope sym.

Open Scope nat_scope.

Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RD_---0LD_1LE0LD_1RA0RF_0RE0LB").

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

Notation zero_cons_default := TM1.zero_cons_default.

Ltac norm_s0 :=
  change BB62.Sym with sym in *;
  repeat rewrite zero_cons_default in *.

Notation mod2_cases := TM1.mod2_cases.

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

Notation opt_map_some := TM1.opt_map_some.

Notation b2f := TM1.b2f.

Notation toTape := TM1.toTape.

Notation pad7B := TM1.pad7B.

Notation toTape_pad7B := TM1.toTape_pad7B.

Notation dropTrailingFalse := TM1.dropTrailingFalse.

Notation toTape_dropTrailingFalse := TM1.toTape_dropTrailingFalse.

Notation roundBool := TM1.roundBool.

Lemma roundBool_sound (fuel : nat) : forall (bs ys : list bool),
    roundBool fuel bs = Some ys -> Round (toTape bs) (toTape ys).
Proof.
  induction fuel as [| fuel IH]; intros bs ys h; [discriminate |].
  rewrite <- (toTape_pad7B bs).
  cbn [roundBool] in h.
  destruct (pad7B bs) as [| [|] l1]; [discriminate | |].
  -  
    destruct l1 as [| [|] rest]; [discriminate | discriminate |].
    destruct (roundBool fuel rest) as [[| [|] r1] |] eqn:Hr1; try discriminate.
    apply opt_map_some in h as [r2 [Hr2 <-]].
    cbn [toTape b2f Str_app].
    exact (round_10 (IH rest (false :: r1) Hr1) (IH r1 r2 Hr2)).
  -  
    destruct l1 as [| [|] l2]; [discriminate | |].
    +  
      destruct l2 as [| [|] l3]; [discriminate | |].
      *  
        destruct l3 as [| [|] rest]; [discriminate | discriminate |].
        apply opt_map_some in h as [r' [Hr' <-]].
        cbn [toTape b2f Str_app].
        exact (round_0110 (IH rest r' Hr')).
      *  
        apply opt_map_some in h as [r' [Hr' <-]].
        cbn [toTape b2f Str_app].
        exact (round_010 (IH l3 r' Hr')).
    +  
      destruct l2 as [| [|] l3]; [discriminate | |].
      *  
        destruct l3 as [| [|] l4]; [discriminate | |].
        --  
           inversion h; subst; clear h.
           cbn [toTape b2f Str_app].
           exact (round_0011 (toTape l4)).
        --  
           destruct l4 as [| [|] l5]; [discriminate | |].
           ++  
              destruct l5 as [| [|] l6]; [discriminate | |].
              **  
                 destruct l6 as [| [|] rest]; [discriminate | discriminate |].
                 apply opt_map_some in h as [r' [Hr' <-]].
                 cbn [toTape b2f Str_app].
                 exact (round_0010110 (IH rest r' Hr')).
              **  
                 apply opt_map_some in h as [r' [Hr' <-]].
                 cbn [toTape b2f Str_app].
                 exact (round_001010 (IH l6 r' Hr')).
           ++  
              apply opt_map_some in h as [r' [Hr' <-]].
              cbn [toTape b2f Str_app].
              exact (round_00100 (IH l5 r' Hr')).
      *  
        inversion h; subst; clear h.
        cbn [toTape b2f Str_app].
        exact (round_000 (toTape l3)).
Qed.

Notation sweepsBool := TM1.sweepsBool.

Lemma sweepsBool_sound (fuel n : nat) : forall (bs ys : list bool),
    sweepsBool fuel n bs = Some ys -> Sweeps n (toTape bs) (toTape ys).
Proof.
  induction n as [| n IH]; intros bs ys h; cbn [sweepsBool] in h.
  - inversion h; subst. apply Sweeps_zero.
  - destruct (roundBool fuel bs) as [bs1 |] eqn:Hr; [| discriminate].
    exact (Sweeps_succ (roundBool_sound fuel bs bs1 Hr) (IH bs1 ys h)).
Qed.

Notation roundBoolTrim := TM1.roundBoolTrim.

Lemma roundBoolTrim_sound (fuel : nat) (bs ys : list bool)
    (h : roundBoolTrim fuel bs = Some ys) : Round (toTape bs) (toTape ys).
Proof.
  apply opt_map_some in h as [raw [Hraw <-]].
  rewrite toTape_dropTrailingFalse.
  exact (roundBool_sound fuel bs raw Hraw).
Qed.

Notation sweepsBoolTrim := TM1.sweepsBoolTrim.

Lemma sweepsBoolTrim_sound (fuel n : nat) (bs ys : list bool)
    (h : sweepsBoolTrim fuel n bs = Some ys) : Sweeps n (toTape bs) (toTape ys).
Proof.
  apply opt_map_some in h as [raw [Hraw <-]].
  rewrite toTape_dropTrailingFalse.
  exact (sweepsBool_sound fuel n bs raw Hraw).
Qed.

Notation rep010 := TM1.rep010.

Notation rep010_add := TM1.rep010_add.

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

Notation pDiv0 := TM1.pDiv0.

Notation pDiv1 := TM1.pDiv1.

Notation pB := TM1.pB.

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

Notation StartsZero := TM1.StartsZero.

Notation rep010_startsZero := TM1.rep010_startsZero.

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

Notation CoreTree := TM1.CoreTree.

Notation sw0 := TM1.sw0.

Notation sw1 := TM1.sw1.

Notation sw2 := TM1.sw2.

Notation sw3 := TM1.sw3.

Notation div0 := TM1.div0.

Notation div1 := TM1.div1.

Notation UTree := TM1.UTree.

Notation evalCore := TM1.evalCore.

Notation evalU := TM1.evalU.

Notation evalCore_startsZero := TM1.evalCore_startsZero.

Notation levelCore := TM1.levelCore.

Notation levelU := TM1.levelU.

Notation levelCore_pos := TM1.levelCore_pos.

Notation mkSw := TM1.mkSw.

Notation coreTagIdx := TM1.coreTagIdx.

Notation stepDefaultAux := TM1.stepDefaultAux.

Notation stepDefaultAux_le3 := TM1.stepDefaultAux_le3.

Notation stepDefaultAux_add4 := TM1.stepDefaultAux_add4.

Notation stepDefault := TM1.stepDefault.

Notation stepCore := TM1.stepCore.

Notation stepU := TM1.stepU.

Notation stepDiv0Sw0 := TM1.stepDiv0Sw0.

Notation stepDivCore := TM1.stepDivCore.

Notation levelU_stepDefaultAux := TM1.levelU_stepDefaultAux.

Notation levelU_stepDefault := TM1.levelU_stepDefault.

Notation levelU_stepCore := TM1.levelU_stepCore.

Notation levelU_stepU := TM1.levelU_stepU.

Notation levelCore_stepDiv0Sw0 := TM1.levelCore_stepDiv0Sw0.

Notation levelCore_stepDivCore := TM1.levelCore_stepDivCore.

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

Notation stepDefaultAux_eq := TM1.stepDefaultAux_eq.

Notation stepDefault_add4_eq := TM1.stepDefault_add4_eq.

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

Notation ResB := TM1.ResB.

Notation mkResB := TM1.mkResB.

Notation resB_c := TM1.resB_c.

Notation resB_u := TM1.resB_u.

Notation ResP := TM1.ResP.

Notation mkResP := TM1.mkResP.

Notation resP_p := TM1.resP_p.

Notation resP_c := TM1.resP_c.

Notation resP_u := TM1.resP_u.

Notation Ops := TM1.Ops.

Notation mkOps := TM1.mkOps.

Notation bCore := TM1.bCore.

Notation aCore := TM1.aCore.

Notation bUFrom := TM1.bUFrom.

Notation aPullSucc := TM1.aPullSucc.

Notation aPullFrom := TM1.aPullFrom.

Notation is_sw0 := TM1.is_sw0.

Notation zero_sw0_cases := TM1.zero_sw0_cases.

Notation opsAux := TM1.opsAux.

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

Notation levelU_gt_one_of_ne_sw0 := TM1.levelU_gt_one_of_ne_sw0.

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

Notation stepCore_eq_stepDefault := TM1.stepCore_eq_stepDefault.

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

Notation min4 := TM1.min4.

Notation CB4 := TM1.CB4.

Notation CA4 := TM1.CA4.

Notation DB4 := TM1.DB4.

Notation DAC4 := TM1.DAC4.

Notation DAU4 := TM1.DAU4.

Notation CAP := TM1.CAP.

Notation DAP := TM1.DAP.

Notation le_min4 := TM1.le_min4.

Notation CB4_le := TM1.CB4_le.

Notation CA4_le := TM1.CA4_le.

Notation DB4_le := TM1.DB4_le.

Notation DAC4_le := TM1.DAC4_le.

Notation DAU4_le := TM1.DAU4_le.

Notation CB4_mono := TM1.CB4_mono.

Notation CA4_mono := TM1.CA4_mono.

Notation DB4_mono := TM1.DB4_mono.

Notation CAP_mono := TM1.CAP_mono.

Notation DAP_mono := TM1.DAP_mono.

Notation bound_bCore_div0 := TM1.bound_bCore_div0.

Notation bound_bCore_div1 := TM1.bound_bCore_div1.

Notation bound_bUFrom := TM1.bound_bUFrom.

Notation bound_aCore_div0 := TM1.bound_aCore_div0.

Notation bound_aCore_div1 := TM1.bound_aCore_div1.

Notation bound_aPull_sw_le := TM1.bound_aPull_sw_le.

Notation bound_aPull_sw_gt := TM1.bound_aPull_sw_gt.

Notation bound_aPull_div := TM1.bound_aPull_div.

Notation bUFrom_bounds := TM1.bUFrom_bounds.

Notation levelCore_ge_two_of_none := TM1.levelCore_ge_two_of_none.

Notation DAC4_le_DAU4 := TM1.DAC4_le_DAU4.

Notation aPullSucc_bounds := TM1.aPullSucc_bounds.

Notation aPullFrom_bounds := TM1.aPullFrom_bounds.

Notation opsAux_bounds := TM1.opsAux_bounds.

Notation eraStepBool := TM1.eraStepBool.

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

Notation eraStepsBool := TM1.eraStepsBool.

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

Notation rep010Bool := TM1.rep010Bool.

Notation toTape_rep010Bool := TM1.toTape_rep010Bool.

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

Notation stepEraU := TM1.stepEraU.

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

Notation runEras := TM1.runEras.

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

Notation era_inv_cap_le := TM1.era_inv_cap_le.

Notation era_inv_dap_le := TM1.era_inv_dap_le.

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

Theorem nonhalt: ~ halts tm c0.
Proof.
  destruct era_inv_init as [cfg0 [hstar hinv0]].
  eapply multistep_nonhalt; [exact hstar |].
  eapply progress_nonhalt; [exact era_inv_step | exact hinv0].
Qed.

End TM2.
Print Assumptions TM2.nonhalt.

From Coq Require Import Lia ZifyNat PeanoNat String List.

Module TM3.
Import BusyCoq.Individual62.

Import Lia ZifyNat PeanoNat String List.

Import ListNotations.

Open Scope list.

Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition ld : list Sym := [1; 1; 0]%sym.

Definition d0 : list Sym := [0; 0; 0]%sym.

Definition d1 : list Sym := [1; 0; 0]%sym.

Definition w1ld : list Sym := [1; 1; 1; 0]%sym.

Definition w1d0 : list Sym := [1; 0; 0; 0]%sym.

Definition w1d1 : list Sym := [1; 1; 0; 0]%sym.

Definition lh : side := [1]%sym *> 0inf%sym.

Open Scope nat_scope.

Lemma zDd : d0 *> 0inf%sym = 0inf%sym.
Proof. unfold d0. cbn [Str_app]. repeat rewrite <- const_unfold. reflexivity. Qed.

Lemma z1_eq : [1]%sym *> (d1 *> 0inf%sym) = ld *> 0inf%sym.
Proof. unfold d1, ld. cbn [Str_app]. repeat rewrite <- const_unfold. reflexivity. Qed.

Lemma z0_eq : [1]%sym *> (d0 *> 0inf%sym) = d1 *> 0inf%sym.
Proof. unfold d0, d1. cbn [Str_app]. repeat rewrite <- const_unfold. reflexivity. Qed.

Inductive Call : Type :=
  | ch
  | ch'.

Definition zCs (c : Call) : Q :=
  match c with
  | ch => B
  | ch' => D
  end.

Definition zCw (c : Call) : list Sym :=
  match c with
  | ch => []
  | ch' => [1]%sym
  end.

Definition zCR (l : side) (c : Call) (r : side) : Q * tape :=
  (zCw c *> l) {{zCs c}}> r.

Definition zCL (l : side) (r : side) : Q * tape :=
  l <{{C}} r.

Definition z04 (c : Call) (r1 r2 : side) : Prop :=
  forall l : side, zCR l c r1 -->+ zCL l r2.

Inductive Side : list Call -> side -> side -> Prop :=
  | Side_nil (r : side) : Side [] r r
  | Side_cons (c : Call) (ls : list Call) (r1 r2 r3 : side) :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3.

Definition Seg (ls_in ls_out : list Call) (w1 w2 : list Sym) : Prop :=
  forall r1 r2 : side, Side ls_out r1 r2 -> Side ls_in (w1 *> r1) (w2 *> r2).

Lemma z07 {A : Type} (l : list A) (m n : nat) : l ^^ (m + n) = l ^^ m ++ l ^^ n.
Proof. apply lpow_add. Qed.

Lemma z08 {ls1 ls2 : list Call} {r1 r2 r3 : side}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3.
Proof.
  induction h1 as [r | c ls ra rb rc hc _ ih].
  - exact h2.
  - exact (Side_cons c (ls ++ ls2) ra rb _ hc (ih h2)).
Qed.

Lemma z09 {ls1 ls2 : list Call} {r1 r3 : side}
    (h : Side (ls1 ++ ls2) r1 r3) : exists r2 : side, Side ls1 r1 r2 /\ Side ls2 r2 r3.
Proof.
  revert r1 h.
  induction ls1 as [| c ls1 ih]; intros r1 h.
  - exists r1. split; [exact (Side_nil r1) | exact h].
  - cbn [app] in h. inverts h as hc hrest.
    destruct (ih _ hrest) as [rmid [ha hb]].
    exists rmid. split; [exact (Side_cons c ls1 r1 _ rmid hc ha) | exact hb].
Qed.

Lemma z0a (w : list Sym) : Seg [] [] w w.
Proof.
  intros r1 r2 h. inverts h. exact (Side_nil (w *> r2)).
Qed.

Lemma zSc {ls1 ls2 : list Call} {w1 w2 : list Sym} {r1 r2 : side}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 *> r1) (w2 *> r2).
Proof. exact (h1 r1 r2 h2). Qed.

Lemma zSg {ls1 ls2 ls3 ls4 : list Call} {w1 w2 w3 : list Sym}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3.
Proof.
  intros r1 r3 h.
  destruct (z09 h) as [r2 [ha hb]].
  exact (z08 (h1 r1 r2 ha) (h2 r2 r3 hb)).
Qed.

Lemma zS4 {c : Call} {w1 w2 : list Sym}
    (h1 : forall l r : side, zCR l c (w1 *> r) -->+ zCL l (w2 *> r)) :
    Seg [c] [] w1 w2.
Proof.
  intros r1 r2 h. inverts h.
  exact (Side_cons c [] (w1 *> r2) (w2 *> r2) (w2 *> r2) (fun l => h1 l r2) (Side_nil _)).
Qed.

Lemma zS2 {c_in c_out : Call} (mid : list Sym) {w1 w2 : list Sym}
    (h1 : forall l r : side, zCR l c_in (w1 *> r) -->+ zCR (mid *> l) c_out r)
    (h2 : forall l r : side, zCL (mid *> l) r -->+ zCL l (w2 *> r)) :
    Seg [c_in] [c_out] w1 w2.
Proof.
  intros r1 r2 h. inverts h as hc hnil. inverts hnil.
  apply Side_cons with (r2 := w2 *> r2); [| apply Side_nil].
  intro l.
  eapply progress_trans; [exact (h1 l r1) |].
  eapply progress_trans; [exact (hc (mid *> l)) | exact (h2 l r2)].
Qed.

Lemma zS5 {c_in c1 c2 : Call} (mid1 mid2 : list Sym) {w1 w2 : list Sym}
    (h1 : forall l r : side, zCR l c_in (w1 *> r) -->+ zCR (mid1 *> l) c1 r)
    (h2 : forall l r : side, zCL (mid1 *> l) r -->+ zCR (mid2 *> l) c2 r)
    (h3 : forall l r : side, zCL (mid2 *> l) r -->+ zCL l (w2 *> r)) :
    Seg [c_in] [c1; c2] w1 w2.
Proof.
  intros r1 r3 h. inverts h as hc1 hrest. inverts hrest as hc2 hnil. inverts hnil.
  apply Side_cons with (r2 := w2 *> r3); [| apply Side_nil].
  intro l.
  eapply progress_trans; [exact (h1 l r1) |].
  eapply progress_trans; [exact (hc1 (mid1 *> l)) |].
  eapply progress_trans; [exact (h2 l _) |].
  eapply progress_trans; [exact (hc2 (mid2 *> l)) | exact (h3 l r3)].
Qed.

Lemma seg_ch_d0 : Seg [ch] [] d0 d1.
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d0, d1; es. Qed.

Lemma seg_ch_d1 : Seg [ch] [ch] d1 d0.
Proof.
  apply (zS2 [0; 0; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, d1, d0; es.
Qed.

Lemma seg_ch_ld : Seg [ch] [ch] ld ld.
Proof.
  apply (zS2 [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, ld; es.
Qed.

Lemma seg_ch'_ld_atom : Seg [ch'] [ch; ch'] ld ld.
Proof.
  apply (zS5 [1; 0; 1; 0]%sym [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, ld; es.
Qed.

Lemma seg_ch_w1ld_atom : Seg [ch] [ch; ch'] w1ld ld.
Proof.
  apply (zS5 [1; 0; 1; 0]%sym [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, w1ld, ld; es.
Qed.

Lemma seg_ch'_d1 : Seg [ch'] [] d1 (ld ++ [1]%sym).
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d1, ld; cbn [app]; es. Qed.

Lemma seg_ch'_d0_atom : Seg [ch'] [ch'; ch] d0 ld.
Proof.
  apply (zS5 [1; 1; 1]%sym [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, d0, ld; es.
Qed.

Lemma seg_ch_1d1 : Seg [ch] [] ([1]%sym ++ d1) (ld ++ [1]%sym).
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d1, ld; cbn [app]; es. Qed.

Lemma seg_ch_1d0 : Seg [ch] [] ([1]%sym ++ d0) (d0 ++ [1]%sym).
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d0; cbn [app]; es. Qed.

Lemma seg_wall_ld (k : nat) : Seg ([ch] ^^ k) ([ch] ^^ k) ld ld.
Proof.
  induction k as [| k ih].
  - exact (z0a ld).
  - cbn [lpow app]. exact (zSg seg_ch_ld ih).
Qed.

Lemma zSa {w2 : list Sym} (hw : Seg [ch; ch] [ch] w2 w2) (n : nat) :
    Seg ([ch] ^^ (n * 2)) ([ch] ^^ n) w2 w2.
Proof.
  induction n as [| n ih].
  - exact (z0a w2).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite z07. cbn [lpow app].
    exact (zSg hw ih).
Qed.

Lemma seg_ch2_d0 : Seg [ch; ch] [ch] d0 d0.
Proof. exact (zSg seg_ch_d0 seg_ch_d1). Qed.

Lemma seg_ch2_d1 : Seg [ch; ch] [ch] d1 d1.
Proof. exact (zSg seg_ch_d1 seg_ch_d0). Qed.

Lemma seg_d0_even (k : nat) : Seg ([ch] ^^ (k * 2)) ([ch] ^^ k) d0 d0.
Proof. exact (zSa seg_ch2_d0 k). Qed.

Lemma seg_d1_even (k : nat) : Seg ([ch] ^^ (k * 2)) ([ch] ^^ k) d1 d1.
Proof. exact (zSa seg_ch2_d1 k). Qed.

Lemma seg_d0_odd (k : nat) : Seg ([ch] ^^ (1 + k * 2)) ([ch] ^^ k) d0 d1.
Proof.
  change ([ch] ^^ (1 + k * 2)) with ([ch] ++ [ch] ^^ (k * 2)).
  change ([ch] ^^ k) with ([] ++ [ch] ^^ k).
  exact (zSg seg_ch_d0 (seg_d1_even k)).
Qed.

Lemma seg_hx_ld (k : nat) : Seg ([ch'] ++ [ch] ^^ k) ([ch] ++ ([ch'] ++ [ch] ^^ k)) ld ld.
Proof.
  change ([ch] ++ ([ch'] ++ [ch] ^^ k)) with ([ch; ch'] ++ [ch] ^^ k).
  exact (zSg seg_ch'_ld_atom (seg_wall_ld k)).
Qed.

Lemma seg_h1_ld (k : nat) : Seg ([ch] ^^ (1 + k)) ([ch] ++ ([ch'] ++ [ch] ^^ k)) w1ld ld.
Proof.
  change ([ch] ^^ (1 + k)) with ([ch] ++ [ch] ^^ k).
  change ([ch] ++ ([ch'] ++ [ch] ^^ k)) with ([ch; ch'] ++ [ch] ^^ k).
  exact (zSg seg_ch_w1ld_atom (seg_wall_ld k)).
Qed.

Lemma seg_hx_d0 (k : nat) : Seg ([ch'] ++ [ch] ^^ k) ([ch'] ++ [ch] ^^ (1 + k)) d0 ld.
Proof.
  change ([ch'] ++ [ch] ^^ (1 + k)) with ([ch'; ch] ++ [ch] ^^ k).
  exact (zSg seg_ch'_d0_atom (seg_wall_ld k)).
Qed.

Inductive RD : Type :=
  | LD
  | D0
  | D1
  | W1LD
  | W1D0
  | W1D1.

Inductive H : Type :=
  | hi
  | hx
  | h1.

Fixpoint toRC (ls : list RD) : side :=
  match ls with
  | [] => 0inf%sym
  | LD :: ls' => ld *> toRC ls'
  | D0 :: ls' => d0 *> toRC ls'
  | D1 :: ls' => d1 *> toRC ls'
  | W1LD :: ls' => w1ld *> toRC ls'
  | W1D0 :: ls' => w1d0 *> toRC ls'
  | W1D1 :: ls' => w1d1 *> toRC ls'
  end.

Definition toH' (tp : H) : list Sym :=
  match tp with
  | hi => []
  | hx => []
  | h1 => [1]%sym
  end.

Definition toH (tp : H) : list Call :=
  match tp with
  | hi => [ch]
  | hx => [ch']
  | h1 => []
  end.

Inductive RIncs : H -> nat -> list RD -> list RD -> Prop :=
  | hi_nil : RIncs hi 0 [] [D1]
  | hi_d0 (r : list RD) : RIncs hi 0 (D0 :: r) (D1 :: r)
  | hi_d1 {r r' : list RD} : RIncs hi 0 r r' -> RIncs hi 0 (D1 :: r) (D0 :: r')
  | hi_ld {r r' : list RD} : RIncs hi 0 r r' -> RIncs hi 0 (LD :: r) (LD :: r')
  | hi_w1d0 {r r' : list RD} : RIncs h1 0 r r' -> RIncs hi 0 (W1D0 :: r) (D0 :: r')
  | hi_w1d1 {r r' : list RD} : RIncs h1 0 r r' -> RIncs hi 0 (W1D1 :: r) (LD :: r')
  | hi_w1ld {r r1 r' : list RD} :
      RIncs hi 0 r r1 -> RIncs hx 0 r1 r' -> RIncs hi 0 (W1LD :: r) (LD :: r')
  | hx_ld {k : nat} {r r1 r' : list RD} :
      RIncs hi 0 r r1 -> RIncs hx k r1 r' -> RIncs hx k (LD :: r) (LD :: r')
  | hx_d1 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs hx k (D1 :: r) (LD :: r')
  | hx_d0 {k : nat} {r r' : list RD} :
      RIncs hx (1 + k) r r' -> RIncs hx k (D0 :: r) (LD :: r')
  | h1_ld {k : nat} {r r1 r' : list RD} :
      RIncs hi 0 r r1 -> RIncs hx k r1 r' -> RIncs h1 (1 + k) (LD :: r) (LD :: r')
  | h1_d1 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs h1 (1 + k) (D1 :: r) (LD :: r')
  | h1_d0_0 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs h1 (1 + k * 2) (D0 :: r) (D0 :: r')
  | h1_d0_1 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs h1 (2 + k * 2) (D0 :: r) (D1 :: r')
  | h1_rh_0 :
      RIncs h1 0 [] [D1]
  | h1_rh_1 {k : nat} {r' : list RD} :
      RIncs h1 k [] r' -> RIncs h1 (1 + k * 2) [] (D0 :: r')
  | h1_rh_2 {k : nat} {r' : list RD} :
      RIncs h1 k [] r' -> RIncs h1 (2 + k * 2) [] (D1 :: r')
  | h1_z1 :
      RIncs h1 0 [D1] [LD]
  | h1_z0 :
      RIncs h1 0 [D0] [D1]
  | h1_z_ld {r r1 r2 : list RD} :
      RIncs hi 0 r r1 -> RIncs hx 0 r1 r2 -> RIncs h1 0 (LD :: r) (W1LD :: r)
  | h1_z_d1 {r r1 : list RD} :
      r <> [] -> RIncs h1 0 r r1 -> RIncs h1 0 (D1 :: r) (W1D1 :: r)
  | h1_z_d0 {r r1 : list RD} :
      r <> [] -> RIncs h1 0 r r1 -> RIncs h1 0 (D0 :: r) (W1D0 :: r).

Lemma side_nil_eq {r1 r2 : side} (h : Side [] r1 r2) : r1 = r2.
Proof. inverts h; reflexivity. Qed.

Lemma RIncs_spec {tp : H} {k : nat} {r r' : list RD} (h : RIncs tp k r r') :
    Side (toH tp ++ [ch] ^^ k) (toH' tp *> toRC r) (toRC r').
Proof.
  induction h.
  - cbn [toH toH' toRC lpow app Str_app].
    rewrite <- zDd at 1.
    exact (zSc seg_ch_d0 (Side_nil 0inf%sym)).
  - cbn [toH toH' toRC lpow app Str_app].
    exact (zSc seg_ch_d0 (Side_nil (toRC r))).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc seg_ch_d1 IHh).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc seg_ch_ld IHh).
  - cbn [toH toH' toRC lpow app] in *.
    rewrite <- (side_nil_eq IHh).
    exact (zSc seg_ch_1d0 (Side_nil _)).
  - cbn [toH toH' toRC lpow app] in *.
    rewrite <- (side_nil_eq IHh).
    exact (zSc seg_ch_1d1 (Side_nil _)).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc seg_ch_w1ld_atom (z08 IHh1 IHh2)).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc (seg_hx_ld k) (z08 IHh1 IHh2)).
  - cbn [toH toH' toRC Str_app] in *.
    exact (z08 (zSc seg_ch'_d1 (Side_nil _)) (zSc (seg_wall_ld k) IHh)).
  - cbn [toH toH' toRC Str_app] in *.
    exact (zSc (seg_hx_d0 k) IHh).
  - cbn [toH toH' toRC lpow app] in *.
    exact (zSc (seg_h1_ld k) (z08 IHh1 IHh2)).
  - cbn [toH toH' toRC app] in *.
    exact (z08 (zSc seg_ch_1d1 (Side_nil _)) (zSc (seg_wall_ld k) IHh)).
  - cbn [toH toH' toRC app] in *.
    exact (z08 (zSc seg_ch_1d0 (Side_nil _)) (zSc (seg_d0_even k) IHh)).
  - cbn [toH toH' toRC app] in *.
    change (ch :: ch :: [ch] ^^ (k * 2)) with ([ch] ++ [ch] ^^ (1 + k * 2)).
    exact (z08 (zSc seg_ch_1d0 (Side_nil _)) (zSc (seg_d0_odd k) IHh)).
  - cbn [toH toH' toRC lpow app].
    rewrite <- z0_eq, zDd.
    exact (Side_nil ([1]%sym *> 0inf%sym)).
  - cbn [toH toH' toRC app] in *.
    rewrite <- zDd at 1.
    exact (z08 (zSc seg_ch_1d0 (Side_nil 0inf%sym)) (zSc (seg_d0_even k) IHh)).
  - cbn [toH toH' toRC app] in *.
    change (ch :: ch :: [ch] ^^ (k * 2)) with ([ch] ++ [ch] ^^ (1 + k * 2)).
    rewrite <- zDd at 1.
    exact (z08 (zSc seg_ch_1d0 (Side_nil 0inf%sym)) (zSc (seg_d0_odd k) IHh)).
  - assert (heq : toH' h1 *> toRC [D1] = toRC [LD]) by exact z1_eq.
    cbn [toH lpow app]. rewrite heq. exact (Side_nil _).
  - assert (heq : toH' h1 *> toRC [D0] = toRC [D1]) by exact z0_eq.
    cbn [toH lpow app]. rewrite heq. exact (Side_nil _).
  - cbn [toH lpow app]. exact (Side_nil _).
  - cbn [toH lpow app]. exact (Side_nil _).
  - cbn [toH lpow app]. exact (Side_nil _).
Qed.

Lemma RIncs_eqk {tp : H} {k k' : nat} {r r' : list RD}
    (h : RIncs tp k r r') (hk : k = k') : RIncs tp k' r r'.
Proof. subst k'; exact h. Qed.

Lemma RIncs_fun {tp : H} {k : nat} {r r1 r2 : list RD}
    (h1 : RIncs tp k r r1) (h_other : RIncs tp k r r2) : r1 = r2.
Proof.
  revert r2 h_other.
  induction h1; intros r_out h_other.
  - inverts h_other. reflexivity.
  - inverts h_other. reflexivity.
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2a h2b. rewrite <- (IHh1_1 _ h2a) in h2b. f_equal. exact (IHh1_2 _ h2b).
  - inverts h_other as h2a h2b. rewrite <- (IHh1_1 _ h2a) in h2b. f_equal. exact (IHh1_2 _ h2b).
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2a h2b; try lia. rewrite <- (IHh1_1 _ h2a) in h2b. f_equal. exact (IHh1_2 _ h2b).
  - inverts h_other as h2'; try lia. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other; try lia; reflexivity.
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other; try lia; try contradiction; reflexivity.
  - inverts h_other; try lia; try contradiction; reflexivity.
  - inverts h_other; try lia; reflexivity.
  - inverts h_other; try lia; try contradiction; reflexivity.
  - inverts h_other; try lia; try contradiction; reflexivity.
Qed.

Lemma RIncs_step {tp : H} {k : nat} {r r' : list RD}
    (h : RIncs tp k r r') (htp : tp <> hi) :
    exists r'', RIncs hi 0 r' r'' /\ RIncs tp (1 + k) r r''.
Proof.
  induction h; try (exfalso; apply htp; reflexivity).
  - destruct (IHh2 ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (hx_ld h2 h_ri')].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (hx_d1 h_ri')].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (hx_d0 h_ri')].
  - destruct (IHh2 ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (h1_ld h2 h_ri')].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (h1_d1 h_ri')].
  - exists (D1 :: r'). split; [exact (hi_d0 r') | eapply RIncs_eqk; [exact (h1_d0_1 h) | lia]].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (D0 :: r''). split; [exact (hi_d1 hJ) | eapply RIncs_eqk; [exact (h1_d0_0 h_ri') | lia]].
  - exists [D0; D1]. split; [exact (hi_d1 hi_nil) | exact (h1_rh_1 h1_rh_0)].
  - exists (D1 :: r'). split; [exact (hi_d0 r') | eapply RIncs_eqk; [exact (h1_rh_2 h) | lia]].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (D0 :: r''). split; [exact (hi_d1 hJ) | eapply RIncs_eqk; [exact (h1_rh_1 h_ri') | lia]].
  - exists [LD; D1]. split; [exact (hi_ld hi_nil) | exact (h1_d1 h1_rh_0)].
  - exists [D0; D1]. split; [exact (hi_d1 hi_nil) | exact (h1_d0_0 h1_rh_0)].
  - exists (LD :: r2). split; [exact (hi_w1ld h2 h3) | exact (h1_ld h2 h3)].
  - exists (LD :: r1). split; [exact (hi_w1d1 h) | exact (h1_d1 h)].
  - exists (D0 :: r1). split; [exact (hi_w1d0 h) | exact (h1_d0_0 h)].
Qed.

Lemma mod2 (n : nat) : (exists b, n = b * 2) \/ (exists b, n = 1 + b * 2).
Proof.
  induction n as [| n ih].
  - left. exists 0. lia.
  - destruct ih as [[b ->] | [b ->]].
     + right. exists b. lia.
     + left. exists (b + 1). lia.
Qed.

Inductive Good : H -> nat -> list RD -> Prop :=
  | Good_hx_ld {k : nat} {r r1 : list RD} :
      RIncs hi 0 r r1 -> Good hx (1 + k) r1 -> Good hx k (LD :: r)
  | Good_hx_d1 {k : nat} {r : list RD} :
      Good h1 (1 + k) r -> Good hx k (D1 :: r)
  | Good_hx_d0 {k : nat} {r : list RD} :
      Good hx (1 + k) r -> Good hx k (D0 :: r)
  | Good_h1_ld {k : nat} {r r1 : list RD} :
      RIncs hi 0 r r1 -> Good hx (1 + k) r1 -> Good h1 (1 + k) (LD :: r)
  | Good_h1_d1 {k : nat} {r : list RD} :
      Good h1 (1 + k) r -> Good h1 (1 + k) (D1 :: r)
  | Good_h1_d0_0 {a : nat} {r : list RD} :
      Good h1 a r -> Good h1 (1 + a * 2) (D0 :: r)
  | Good_h1_d0_1 {a : nat} {r : list RD} :
      Good h1 a r -> Good h1 (2 + a * 2) (D0 :: r)
  | Good_h1_z1 :
      Good h1 0 [D1]
  | Good_h1_nil (k : nat) :
      Good h1 k [].

Lemma RIncs_nxt_1_aux (m : nat) : forall k, k <= m -> exists r, RIncs h1 k [] r.
Proof.
  induction m as [| m ih]; intros k hk.
  - assert (k = 0) by lia; subst k. exists [D1]. exact h1_rh_0.
  - destruct k as [| k0].
    + exists [D1]. exact h1_rh_0.
    + destruct (mod2 k0) as [[b ->] | [b ->]].
      * destruct (ih b ltac:(lia)) as [r hI].
        exists (D0 :: r). eapply RIncs_eqk; [exact (h1_rh_1 hI) | lia].
      * destruct (ih b ltac:(lia)) as [r hI].
        exists (D1 :: r). eapply RIncs_eqk; [exact (h1_rh_2 hI) | lia].
Qed.

Lemma RIncs_nxt_1 (k : nat) : exists r, RIncs h1 k [] r.
Proof. exact (RIncs_nxt_1_aux k k (Nat.le_refl k)). Qed.

Lemma rK_nonnil {k : nat} {r rK : list RD} (h : RIncs h1 k r rK) : rK <> [].
Proof.
  inverts h; discriminate.
Qed.

Lemma inv_hx_ld {k : nat} {r rK : list RD} (h : RIncs hx k (LD :: r) rK) :
    exists r1 rK', RIncs hi 0 r r1 /\ RIncs hx k r1 rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_inc h_ri. exists r1, r'. repeat split; try reflexivity; assumption.
Qed.

Lemma inv_hx_d1 {k : nat} {r rK : list RD} (h : RIncs hx k (D1 :: r) rK) :
    exists rK', RIncs h1 k r rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_ri. exists r'. split; [exact h_ri | reflexivity].
Qed.

Lemma inv_hx_d0 {k : nat} {r rK : list RD} (h : RIncs hx k (D0 :: r) rK) :
    exists rK', RIncs hx (1 + k) r rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_ri. exists r'. split; [exact h_ri | reflexivity].
Qed.

Lemma inv_h1_ld {k : nat} {r rK : list RD} (h : RIncs h1 (1 + k) (LD :: r) rK) :
    exists r1 rK', RIncs hi 0 r r1 /\ RIncs hx k r1 rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_inc h_ri; try lia. exists r1, r'. repeat split; try reflexivity; assumption.
Qed.

Lemma inv_h1_d1 {k : nat} {r rK : list RD} (h : RIncs h1 (1 + k) (D1 :: r) rK) :
    exists rK', RIncs h1 k r rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_ri; try lia. exists r'. split; [exact h_ri | reflexivity].
Qed.

Lemma inv_h1_d0 {K : nat} {r rK : list RD} (h : RIncs h1 K (D0 :: r) rK) (hK : 1 <= K) :
    (exists A rK', K = 1 + A * 2 /\ RIncs h1 A r rK' /\ rK = D0 :: rK') \/
    (exists A rK', K = 2 + A * 2 /\ RIncs h1 A r rK' /\ rK = D1 :: rK').
Proof.
  inverts h as h_ri; try lia.
  - left. exists k, r'. repeat split; try reflexivity; exact h_ri.
  - right. exists k, r'. repeat split; try reflexivity; exact h_ri.
Qed.

Lemma inv_z1 {K : nat} {rK : list RD} (h : RIncs h1 K [D1] rK) :
    (K = 0 /\ rK = [LD]) \/
    (exists K0 rK', K = 1 + K0 /\ RIncs h1 K0 [] rK' /\ rK = LD :: rK').
Proof.
  inverts h as h_ri; try contradiction.
  - right. exists k, r'. repeat split; try reflexivity; exact h_ri.
  - left. split; reflexivity.
Qed.

Lemma End_step {tp : H} {m : nat} {e w : list RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    forall tq q, (tq = hx \/ tq = h1) -> exists w', RIncs tq q w w'.
Proof.
  induction h; try discriminate htp; try discriminate he; intros tq q htq.
  - destruct htq as [-> | ->].
    + destruct (RIncs_nxt_1 q) as [w' hI].
      exists (LD :: w'). exact (hx_d1 hI).
    + destruct q as [| q0].
      * exists [LD]. exact h1_z1.
      * destruct (RIncs_nxt_1 q0) as [w' hI].
        exists (LD :: w'). eapply RIncs_eqk; [exact (h1_d1 hI) | lia].
  - specialize (IHh eq_refl eq_refl).
    destruct htq as [-> | ->].
    + destruct (IHh hx (1 + q) (or_introl eq_refl)) as [w' hI2].
      exists (LD :: w'). exact (hx_d0 hI2).
    + destruct q as [| m0].
      * destruct (IHh h1 0 (or_intror eq_refl)) as [w' hI2].
        exists (W1D0 :: r'). exact (h1_z_d0 (rK_nonnil h) hI2).
      * destruct (mod2 m0) as [[b ->] | [b ->]].
        -- destruct (IHh h1 b (or_intror eq_refl)) as [w' hI2].
           exists (D0 :: w'). eapply RIncs_eqk; [exact (h1_d0_0 hI2) | lia].
        -- destruct (IHh h1 b (or_intror eq_refl)) as [w' hI2].
           exists (D1 :: w'). eapply RIncs_eqk; [exact (h1_d0_1 hI2) | lia].
  - specialize (IHh eq_refl eq_refl).
    destruct htq as [-> | ->].
    + destruct (IHh h1 q (or_intror eq_refl)) as [w' hI2].
      exists (LD :: w'). exact (hx_d1 hI2).
    + destruct q as [| q0].
      * destruct (IHh h1 0 (or_intror eq_refl)) as [w' hI2].
        exists (W1D1 :: r'). exact (h1_z_d1 (rK_nonnil h) hI2).
      * destruct (IHh h1 q0 (or_intror eq_refl)) as [w' hI2].
        exists (LD :: w'). eapply RIncs_eqk; [exact (h1_d1 hI2) | lia].
Qed.

Lemma Good_eqk {tp : H} {k k' : nat} {r : list RD}
    (h : Good tp k r) (hk : k = k') : Good tp k' r.
Proof. subst k'; exact h. Qed.

Lemma Good_step {tp : H} {k : nat} {r : list RD} (hG : Good tp k r) :
    forall j rK tq q, RIncs tp (k + j) r rK ->
    (tq = hx \/ (tq = h1 /\ tp = h1)) -> exists r2, RIncs tq q rK r2.
Proof.
  induction hG; intros j rK tq q E htq.
  - assert (htq_hx : tq = hx) by (destruct htq as [-> | [_ Hc]]; [reflexivity | discriminate]).
    subst tq.
    destruct (inv_hx_ld E) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
    exists (LD :: r2). exact (hx_ld J I2).
  - assert (htq_hx : tq = hx) by (destruct htq as [-> | [_ Hc]]; [reflexivity | discriminate]).
    subst tq.
    destruct (inv_hx_d1 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
    exists (LD :: r2). exact (hx_ld J I2).
  - assert (htq_hx : tq = hx) by (destruct htq as [-> | [_ Hc]]; [reflexivity | discriminate]).
    subst tq.
    destruct (inv_hx_d0 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + (1 + j)) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct (IHhG (1 + j) rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
    exists (LD :: r2). exact (hx_ld J I2).
  - assert (E0 : RIncs h1 (1 + (k + j)) (LD :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_ld E0) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct htq as [-> | [-> _]].
    + destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
      exists (LD :: r2). exact (hx_ld J I2).
    + destruct q as [| q0].
      * destruct (IHhG j rK'' hx 0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (W1LD :: rK'). exact (h1_z_ld J I2).
      * destruct (IHhG j rK'' hx q0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). eapply RIncs_eqk; [exact (h1_ld J I2) | lia].
  - assert (E0 : RIncs h1 (1 + (k + j)) (D1 :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_d1 E0) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct htq as [-> | [-> _]].
    + destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
      exists (LD :: r2). exact (hx_ld J I2).
    + destruct q as [| q0].
      * destruct (IHhG j rK'' hx 0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (W1LD :: rK'). exact (h1_z_ld J I2).
      * destruct (IHhG j rK'' hx q0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). eapply RIncs_eqk; [exact (h1_ld J I2) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' hx (1 + q) hE' (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). exact (hx_d0 I2).
      * destruct q as [| m0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D0 :: rK'). exact (h1_z_d0 (rK_nonnil E') I2).
        -- destruct (mod2 m0) as [[b ->] | [b ->]].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D0 :: r2). eapply RIncs_eqk; [exact (h1_d0_0 I2) | lia].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D1 :: r2). eapply RIncs_eqk; [exact (h1_d0_1 I2) | lia].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' h1 q hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
        exists (LD :: r2). exact (hx_d1 I2).
      * destruct q as [| q0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D1 :: rK'). exact (h1_z_d1 (rK_nonnil E') I2).
        -- destruct (IHhG (A - a) rK' h1 q0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (LD :: r2). eapply RIncs_eqk; [exact (h1_d1 I2) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' hx (1 + q) hE' (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). exact (hx_d0 I2).
      * destruct q as [| m0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D0 :: rK'). exact (h1_z_d0 (rK_nonnil E') I2).
        -- destruct (mod2 m0) as [[b ->] | [b ->]].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D0 :: r2). eapply RIncs_eqk; [exact (h1_d0_0 I2) | lia].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D1 :: r2). eapply RIncs_eqk; [exact (h1_d0_1 I2) | lia].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' h1 q hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
        exists (LD :: r2). exact (hx_d1 I2).
      * destruct q as [| q0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D1 :: rK'). exact (h1_z_d1 (rK_nonnil E') I2).
        -- destruct (IHhG (A - a) rK' h1 q0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (LD :: r2). eapply RIncs_eqk; [exact (h1_d1 I2) | lia].
  - destruct (inv_z1 E) as [[HK ->] | [K0 [rK' [HK [E' ->]]]]].
    + destruct htq as [-> | [-> _]].
      * destruct (RIncs_nxt_1 q) as [w hI].
        exists (LD :: LD :: w). exact (hx_ld hi_nil (hx_d1 hI)).
      * destruct q as [| q0].
        -- exists [W1LD]. exact (h1_z_ld hi_nil (hx_d1 h1_rh_0)).
        -- destruct (RIncs_nxt_1 q0) as [w hI].
           exists (LD :: LD :: w). eapply RIncs_eqk; [exact (h1_ld hi_nil (hx_d1 hI)) | lia].
    + destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
      destruct htq as [-> | [-> _]].
      * destruct (End_step E'' eq_refl eq_refl hx q (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). exact (hx_ld J I2).
      * destruct q as [| q0].
        -- destruct (End_step E'' eq_refl eq_refl hx 0 (or_introl eq_refl)) as [r2 I2].
           exists (W1LD :: rK'). exact (h1_z_ld J I2).
        -- destruct (End_step E'' eq_refl eq_refl hx q0 (or_introl eq_refl)) as [r2 I2].
           exists (LD :: r2). eapply RIncs_eqk; [exact (h1_ld J I2) | lia].
  - destruct htq as [-> | [-> _]].
    + exact (End_step E eq_refl eq_refl hx q (or_introl eq_refl)).
    + exact (End_step E eq_refl eq_refl h1 q (or_intror eq_refl)).
Qed.

Lemma End_good_1 {tp : H} {m : nat} {e w : list RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    forall q, m <= q -> Good h1 q w.
Proof.
  induction h; try discriminate htp; try discriminate he; intros q hq.
  - destruct q as [| q0].
    + exact Good_h1_z1.
    + eapply Good_eqk; [exact (Good_h1_d1 (Good_h1_nil (1 + q0))) | lia].
  - specialize (IHh eq_refl eq_refl).
    destruct (mod2 q) as [[c ->] | [c ->]].
    + destruct c as [| c]; [lia |].
      eapply Good_eqk; [exact (Good_h1_d0_1 (IHh c ltac:(lia))) | lia].
    + exact (Good_h1_d0_0 (IHh c ltac:(lia))).
  - specialize (IHh eq_refl eq_refl).
    destruct q as [| q0]; [lia |].
    eapply Good_eqk; [exact (Good_h1_d1 (IHh (1 + q0) ltac:(lia))) | lia].
Qed.

Lemma End_good_x {tp : H} {m : nat} {e w : list RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    forall q, m <= 2 * q + 2 -> Good hx q w.
Proof.
  induction h; try discriminate htp; try discriminate he; intros q hq.
  - exact (Good_hx_d1 (Good_h1_nil (1 + q))).
  - exact (Good_hx_d0 (IHh eq_refl eq_refl (1 + q) ltac:(lia))).
  - exact (Good_hx_d1 (End_good_1 h eq_refl eq_refl (1 + q) ltac:(lia))).
Qed.

Definition Inv (tp : H) (k j : nat) (tq : H) (q : nat) : Prop :=
  match tp, tq with
  | hx, hx => k <= q /\ j <= q
  | h1, hx => k <= q /\ j <= q
  | h1, h1 => (j = 0 /\ 2 * k + 1 <= q) \/ (1 <= j /\ k + j <= q /\ 1 <= q)
  | _, _ => False
  end.

Lemma Good_pres {tp : H} {k : nat} {r : list RD} (hG : Good tp k r) :
    forall j rK tq q, RIncs tp (k + j) r rK ->
    Inv tp k j tq q -> Good tq q rK.
Proof.
  induction hG; intros j rK tq q E HI.
  - destruct tq; try contradiction.
    destruct (inv_hx_ld E) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
  - destruct tq; try contradiction.
    destruct (inv_hx_d1 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
  - destruct tq; try contradiction.
    destruct (inv_hx_d0 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + (1 + j)) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    exact (Good_hx_ld J (IHhG (1 + j) rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
  - assert (E0 : RIncs h1 (1 + (k + j)) (LD :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_ld E0) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct tq; try contradiction.
    + exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
    + destruct q as [| q0]; [cbn [Inv] in HI; lia |].
      eapply Good_eqk; [exact (Good_h1_ld J (IHhG j rK'' hx (1 + q0) E3 ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - assert (E0 : RIncs h1 (1 + (k + j)) (D1 :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_d1 E0) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct tq; try contradiction.
    + exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
    + destruct q as [| q0]; [cbn [Inv] in HI; lia |].
      eapply Good_eqk; [exact (Good_h1_ld J (IHhG j rK'' hx (1 + q0) E3 ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d0 (IHhG (A - a) rK' hx (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct (mod2 q) as [[b ->] | [b ->]].
        -- destruct b as [| b0]; [cbn [Inv] in HI; lia |].
           eapply Good_eqk; [exact (Good_h1_d0_1 (IHhG (A - a) rK' h1 b0 hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
        -- exact (Good_h1_d0_0 (IHhG (A - a) rK' h1 b hE' ltac:(cbn [Inv] in HI |- *; lia))).
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d1 (IHhG (A - a) rK' h1 (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_d1 (IHhG (A - a) rK' h1 (1 + q0) hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d0 (IHhG (A - a) rK' hx (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct (mod2 q) as [[b ->] | [b ->]].
        -- destruct b as [| b0]; [cbn [Inv] in HI; lia |].
           eapply Good_eqk; [exact (Good_h1_d0_1 (IHhG (A - a) rK' h1 b0 hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
        -- exact (Good_h1_d0_0 (IHhG (A - a) rK' h1 b hE' ltac:(cbn [Inv] in HI |- *; lia))).
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d1 (IHhG (A - a) rK' h1 (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_d1 (IHhG (A - a) rK' h1 (1 + q0) hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - destruct (inv_z1 E) as [[HK ->] | [K0 [rK' [HK [E' ->]]]]].
    + destruct tq; try contradiction.
      * exact (Good_hx_ld hi_nil (Good_hx_d1 (Good_h1_nil _))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_ld hi_nil (Good_hx_d1 (Good_h1_nil (1 + (1 + q0))))) | lia].
    + destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
      destruct tq; try contradiction.
      * exact (Good_hx_ld J (End_good_x E'' eq_refl eq_refl (1 + q) ltac:(cbn [Inv] in HI; lia))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_ld J (End_good_x E'' eq_refl eq_refl (1 + q0) ltac:(cbn [Inv] in HI; lia))) | lia].
  - destruct tq; try contradiction.
    + exact (End_good_x E eq_refl eq_refl q ltac:(cbn [Inv] in HI; lia)).
    + exact (End_good_1 E eq_refl eq_refl q ltac:(cbn [Inv] in HI; lia)).
Qed.

Lemma domain {r r1 : list RD} (hG : Good hx 0 r) (hE : RIncs hx 0 r r1) :
    exists r2, RIncs hx 0 r1 r2 /\ Good hx 0 r1.
Proof.
  destruct (Good_step hG 0 r1 hx 0 hE (or_introl eq_refl)) as [r2 hR2].
  exists r2. split; [exact hR2 | exact (Good_pres hG 0 r1 hx 0 hE ltac:(cbn [Inv]; lia))].
Qed.

Definition S' (r : list RD) : Q * tape :=
  zCR lh ch' (toRC r).

Lemma turn_lh (r : list RD) : zCL lh (toRC r) -->+ S' r.
Proof.
  unfold zCL, S', zCR, lh, zCw, zCs. es.
Qed.

Lemma BigStep {r r' : list RD} (h : RIncs hx 0 r r') : S' r -->+ S' r'.
Proof.
  pose proof (RIncs_spec h) as hS.
  cbn [toH toH' lpow app Str_app] in hS.
  inverts hS as hc hnil. inverts hnil.
  eapply progress_trans; [exact (hc lh) | exact (turn_lh r')].
Qed.

Lemma start_to_S' : c0 -->* S' [D1].
Proof.
  unfold S', zCR, lh, zCw, zCs, toRC, d1.
  solve_init.
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := S' [D1]).
  - exact start_to_S'.
  - eapply progress_nonhalt_cond with
      (C := S')
      (P := fun r => (exists r1, RIncs hx 0 r r1) /\ Good hx 0 r)
      (i0 := [D1]).
    + intros r [[r1 hE] hG].
      destruct (domain hG hE) as [r2 [hE2 hG2]].
      exists r1. split; [exact (BigStep hE) | split; [exists r2; exact hE2 | exact hG2]].
    + split.
      * exists [LD; D1]. exact (hx_d1 h1_rh_0).
      * exact (Good_hx_d1 (Good_h1_nil 1)).
Qed.

End TM3.
Print Assumptions TM3.nonhalt.

Require Import Lia.
Require Import String.
Require Import List.
Require Import Arith.

Module TM4.
Import BusyCoq.Individual62.

Import Lia.

Import String.

Import List.

Import Arith.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

Lemma LP0 l r : l <* <[0;1;1] {{C}}> [0] *> r -->+ l <{{A}} [1;0;0;1] *> r.
Proof. es. Qed.

Lemma LP0z l : l <* <[0;1;1] {{C}}> 0inf -->+ l <{{A}} [1;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LP11 l r : l <* <[0;1;1] {{C}}> [1;1;0] *> r -->+ l <{{A}} [1;0;1;0;0;0] *> r.
Proof. es. Qed.

Lemma LPCr l e r : l <* <[0;1;1] {{C}}> [1;0;1] *> [0;0;1]^^e *> [0;0;0] *> r -->+
  l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <* <[0;1;1] {{C}}> r.
Proof. es. Qed.

Lemma LPCl0 l e r : l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;0] *> r -->+
  l <{{A}} [1;0;0;0;0;1] *> [0;0;1]^^e *> [0;0;0] *> r.
Proof. es. Qed.

Lemma LPCl1 l e r : l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;1;0;0;0] *> r -->+
  l <{{A}} [1;0;0;0;0;1] *> [0;0;1]^^(S e) *> [0;0;0] *> r.
Proof. es. Qed.

Lemma LP5r l e r : l <* <[0;1;1] {{C}}> [1;0;0;0;1] *> [0;0;1]^^e *> [0;0;0] *> r -->+
  l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e) <* <[0;1;1] {{C}}> r.
Proof. es. Qed.

Lemma LP5l0 l e r : l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e) <{{A}} [1;0;0] *> r -->+
  l <{{A}} [1;0;0;0;1] *> [0;0;1]^^(S e) *> [0;0;0] *> r.
Proof. es. Qed.

Lemma LP5l1 l e r : l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e) <{{A}} [1;0;1;0;0;0] *> r -->+
  l <{{A}} [1;0;0;0;1] *> [0;0;1]^^(S (S e)) *> [0;0;0] *> r.
Proof. es. Qed.

Lemma LP6r l e r : l <* <[0;1;1] {{C}}> [1;0;1;0;1] *> [0;0;1]^^e *> [0;0;0] *> r -->+
  l <* <[0;1;1;1] <* <[1;1;0] <* [0] <* <[0;1;1]^^(S e) {{C}}> r.
Proof. es. Qed.

Lemma W10 l r : l <* <[0;1;1;1] <{{E}} r -->+ l <{{A}} [1;0;0;0] *> r.
Proof. es. Qed.

Lemma RP0 l n r : l <* [0] <* <[0;1;1]^^(S n) <{{A}} [1;0;0] *> r -->+
  l <* <[1;1;0] <* [0] <* <[0;1;1]^^(S n) {{C}}> r.
Proof. es. Qed.

Lemma RP1 l n r : l <* [0] <* <[0;1;1]^^(S n) <{{A}} [1;0;1;0;0;0] *> r -->+
  l <* <[1;1;0] <* [0] <* <[0;1;1]^^(S (S n)) {{C}}> r.
Proof. es. Qed.

Lemma E1r l a e r : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [0;0;1]^^(S e) *> [0;0;0] *> r -->+
  l <* <[1;1;0]^^(S (S a)) <* [0] <* <[0;1;1]^^(S e) {{C}}> r.
Proof. es. Qed.

Lemma E2l0 l a e r : l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;0] *> r -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;1;1] *> [0;0;1]^^e *> [0;0;0] *> r.
Proof. es. Qed.

Lemma E2l1 l a e r : l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;1;0;0;0] *> r -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;1;1] *> [0;0;1]^^(S e) *> [0;0;0] *> r.
Proof. es. Qed.

Lemma Et0 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> 0inf -->+
  l <{{E}} [0;1] *> [0;0;1]^^(S a) *> [0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma Et1 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [1] *> 0inf -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;0;1;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma Et2 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [0;1;0;0;0;1] *> 0inf -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma Et3 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [1;1;0;0;0;1] *> 0inf -->+
  l <* <[1;1;0]^^(S a) <* [0] <* <[0;1;1] {{C}}> [0;0;1] *> 0inf.
Proof. es. Qed.

Lemma Rst k r : const 0 <{{E}} [0;1] *> [0;0;1]^^k *> [0;0;0] *> r -->+
  const 0 <* <[1;1;0] <* [0] <* <[0;1;1]^^(S k) {{C}}> r.
Proof. rewrite (const_unfold _ S0) at 1. es. Qed.

Lemma LPT1 l : l <* <[0;1;1] {{C}}> [1] *> 0inf -->+ l <{{A}} [1;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT2 l : l <* <[0;1;1] {{C}}> [1;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;1;0;0;0;0;1;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT3 l : l <* <[0;1;1] {{C}}> [1;0;1;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT4 l : l <* <[0;1;1] {{C}}> [1;0;0;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;0;0;1;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT5 l : l <* <[0;1;1] {{C}}> [1;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;1;0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT6 l : l <* <[0;1;1] {{C}}> [1;0;0;1;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;1;0;0;1;0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma z3 : [0;0;0] *> const 0 = const 0.
Proof. cbn. rewrite <- !const_unfold. reflexivity. Qed.

Inductive word : Type :=
| t0 | t1 | t2 | t3
| blk (d : bool) (e : nat) (w : word)
| p11 (x : nat) (w : word)
| p01 (x : nat) (w : word)
| p00 (w : word)
| p10 (w : word).

Definition dsym (d : bool) : Sym := if d then S1 else S0.

Fixpoint enc (w : word) : side :=
  match w with
  | t0 => const 0
  | t1 => [1] *> const 0
  | t2 => [0;1;0;0;0;1] *> const 0
  | t3 => [1;1;0;0;0;1] *> const 0
  | blk d e w => [dsym d; 0; 1] *> [0;0;1]^^e *> [0;0;0] *> enc w
  | p11 x w => [1;1] *> [0;0;1]^^x *> [0;0;0] *> enc w
  | p01 x w => [0;1] *> [0;0;1]^^x *> [0;0;0] *> enc w
  | p00 w => [0;0] *> enc w
  | p10 w => [1;0] *> enc w
  end.

Definition addb (e : nat) (d : bool) : nat := if d then S e else e.

Inductive LP : word -> word -> bool -> Prop :=
| LP_a e w : LP (blk false e w) (blk true e w) false
| LP_b e w w' d : LP w w' d -> LP (blk true e w) (blk false (addb e d) w') false
| LP_t0 : LP t0 t1 false
| LP_t1 : LP t1 t2 false
| LP_t2 : LP t2 t3 false
| LP_t3 : LP t3 (blk false 0 t0) true
| LP_11S x w : LP (p11 (S x) w) (p01 x w) true
| LP_110 w : LP (p11 0 w) (p00 w) true
| LP_01 x w : LP (p01 x w) (p11 x w) false
| LP_00 w : LP (p00 w) (p10 w) false
| LP_5 e w w' d : LP w w' d -> LP (p10 (blk false e w)) (p01 (S (addb e d)) w') false
| LP_6 e w k y : Phi 1 (S e) w k y -> LP (p10 (blk true e w)) (blk false k y) false
| LP_T2 : LP (p10 t2) (p01 1 (p01 1 t1)) false
| LP_T3 : LP (p10 t3) (p00 (p01 0 t2)) false
| LP_T4 : LP (p10 (p00 t2)) (p01 0 (p01 1 t1)) false
| LP_T5 : LP (p10 (p01 0 t2)) (p01 1 (p10 (p00 t2))) false
| LP_T6 : LP (p10 (p01 1 t1)) (p01 2 (p10 (p00 t2))) false
| LP_eq w1 w2 w' d : enc w1 = enc w2 -> LP w2 w' d -> LP w1 w' d
with Phi : nat -> nat -> word -> nat -> word -> Prop :=
| Phi_B a b w w' d k y : LP w w' d -> Phi (S a) (addb (S b) d) w' k y -> Phi a (S (S b)) w k y
| Phi_E1 a e w k y : Phi (S (S a)) (S e) w k y -> Phi a 1 (blk false e w) k y
| Phi_E2 a e w w' d : LP w w' d -> Phi a 1 (blk true e w) a (p11 (addb e d) w')
| Phi_E0 a : Phi a 1 t0 (S a) t1
| Phi_Et1 a : Phi a 1 t1 a (p01 1 t1)
| Phi_Et2 a : Phi a 1 t2 a (p10 (p00 t2))
| Phi_Et3 a k y : Phi (S a) 1 (blk false 0 t0) k y -> Phi a 1 t3 k y
| Phi_eq a b w1 w2 k y : enc w1 = enc w2 -> Phi a b w2 k y -> Phi a b w1 k y.

Scheme LP_mind := Induction for LP Sort Prop
with Phi_mind := Induction for Phi Sort Prop.

Combined Scheme LP_Phi_mind from LP_mind, Phi_mind.

Definition outp (d : bool) (r : side) : side :=
  if d then [1;0;1;0;0;0] *> r else [1;0;0] *> r.

Definition LPspec (w w' : word) (d : bool) : Prop :=
  forall l, l <* <[0;1;1] {{C}}> enc w -->+ l <{{A}} outp d (enc w').

Definition Phispec (a b : nat) (w : word) (k : nat) (y : word) : Prop :=
  forall l, l <* <[1;1;0]^^a <* [0] <* <[0;1;1]^^b {{C}}> enc w -->+
            l <{{E}} [0;1] *> [0;0;1]^^k *> [0;0;0] *> enc y.

Lemma enc_a0 : enc (blk false 0 t0) = [0;0;1] *> const 0.
Proof. cbn [enc]. rewrite z3. reflexivity. Qed.

Theorem sound :
  (forall w w' d, LP w w' d -> LPspec w w' d) /\
  (forall a b w k y, Phi a b w k y -> Phispec a b w k y).
Proof.
  apply LP_Phi_mind; unfold LPspec, Phispec.
  -   intros e w l. exact (LP0 l ([0;1] *> [0;0;1]^^e *> [0;0;0] *> enc w)).
  -   intros e w w' d H IH l. destruct d.
    + eapply progress_trans. { exact (LPCr l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (LPCl1 l e (enc w')).
    + eapply progress_trans. { exact (LPCr l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (LPCl0 l e (enc w')).
  -   intros l. exact (LP0z l).
  -   intros l. exact (LPT1 l).
  -   intros l. exact (LP0 l ([1;0;0;0;1] *> const 0)).
  -   intros l. unfold outp. rewrite enc_a0. exact (LP11 l ([0;0;1] *> const 0)).
  -   intros x w l. exact (LP11 l ([0;1] *> [0;0;1]^^x *> [0;0;0] *> enc w)).
  -   intros w l. exact (LP11 l ([0;0] *> enc w)).
  -   intros x w l. exact (LP0 l ([1] *> [0;0;1]^^x *> [0;0;0] *> enc w)).
  -   intros w l. exact (LP0 l ([0] *> enc w)).
  -   intros e w w' d H IH l. destruct d.
    + eapply progress_trans. { exact (LP5r l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e))). }
      exact (LP5l1 l e (enc w')).
    + eapply progress_trans. { exact (LP5r l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e))). }
      exact (LP5l0 l e (enc w')).
  -   intros e w k y H IH l.
    eapply progress_trans. { exact (LP6r l e (enc w)). }
    eapply progress_trans. { exact (IH (l <* <[0;1;1;1])). }
    exact (W10 l ([0;1] *> [0;0;1]^^k *> [0;0;0] *> enc y)).
  -   intros l. exact (LPT2 l).
  -   intros l. exact (LPT3 l).
  -   intros l. exact (LPT4 l).
  -   intros l. exact (LPT5 l).
  -   intros l. exact (LPT6 l).
  -   intros w1 w2 w' d E H IH l. rewrite E. apply IH.
  -   intros a b w w' d k y H IH H2 IH2 l. destruct d.
    + eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1]^^(S b))). }
      eapply progress_trans. { exact (RP1 (l <* <[1;1;0]^^a) b (enc w')). }
      exact (IH2 l).
    + eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1]^^(S b))). }
      eapply progress_trans. { exact (RP0 (l <* <[1;1;0]^^a) b (enc w')). }
      exact (IH2 l).
  -   intros a e w k y H IH l.
    eapply progress_trans. { exact (E1r l a e (enc w)). }
    exact (IH l).
  -   intros a e w w' d H IH l. destruct d.
    + eapply progress_trans. { exact (LPCr (l <* <[1;1;0]^^a <* [0]) e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (E2l1 l a e (enc w')).
    + eapply progress_trans. { exact (LPCr (l <* <[1;1;0]^^a <* [0]) e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (E2l0 l a e (enc w')).
  -   intros a l. exact (Et0 l a).
  -   intros a l. exact (Et1 l a).
  -   intros a l. exact (Et2 l a).
  -   intros a k y H IH l.
    eapply progress_trans. { exact (Et3 l a). }
    specialize (IH l). rewrite enc_a0 in IH. exact IH.
  -   intros a b w1 w2 k y E H IH l. rewrite E. apply IH.
Qed.

Definition K (N : nat) (y : word) : Q * tape :=
  const 0 <* <[1;1;0] <* [0] <* <[0;1;1]^^N {{C}}> enc y.

Lemma epoch_tm N y k y' : Phi 1 N y k y' -> K N y -->+ K (S k) y'.
Proof.
  intros H. eapply progress_trans.
  - exact (proj2 sound _ _ _ _ _ H (const 0)).
  - apply Rst.
Qed.

Lemma init : c0 -->* K 8 t2.
Proof. unfold K. cbn. solve_init. Qed.

Fixpoint lpf (n : nat) (w : word) {struct n} : option (word * bool) :=
  match n with
  | O => None
  | S n' =>
    match w with
    | t0 => Some (t1, false)
    | t1 => Some (t2, false)
    | t2 => Some (t3, false)
    | t3 => Some (blk false 0 t0, true)
    | blk false e w => Some (blk true e w, false)
    | blk true e w =>
        match lpf n' w with Some (w', d) => Some (blk false (addb e d) w', false) | None => None end
    | p11 (S x) w => Some (p01 x w, true)
    | p11 O w => Some (p00 w, true)
    | p01 x w => Some (p11 x w, false)
    | p00 w => Some (p10 w, false)
    | p10 w =>
        match w with
        | t0 => Some (t2, false)
        | t1 => Some (blk false 0 t1, false)
        | t2 => Some (p01 1 (p01 1 t1), false)
        | t3 => Some (p00 (p01 0 t2), false)
        | blk false e w =>
            match lpf n' w with Some (w', d) => Some (p01 (S (addb e d)) w', false) | None => None end
        | blk true e w =>
            match phif n' 1 (S e) w with Some (k, y) => Some (blk false k y, false) | None => None end
        | p00 t0 => Some (t2, false)
        | p00 t1 => Some (p01 1 t1, false)
        | p00 t2 => Some (p01 0 (p01 1 t1), false)
        | p01 0 t2 => Some (p01 1 (p10 (p00 t2)), false)
        | p01 1 t1 => Some (p01 2 (p10 (p00 t2)), false)
        | p10 (p00 t2) => Some (blk false 0 t3, false)
        | _ => None
        end
    end
  end
with phif (n : nat) (a b : nat) (w : word) {struct n} : option (nat * word) :=
  match n with
  | O => None
  | S n' =>
    match b with
    | O => None
    | S O =>
      match w with
      | blk false e w => phif n' (S (S a)) (S e) w
      | blk true e w =>
          match lpf n' w with Some (w', d) => Some (a, p11 (addb e d) w') | None => None end
      | t0 => Some (S a, t1)
      | t1 => Some (a, p01 1 t1)
      | t2 => Some (a, p10 (p00 t2))
      | t3 => phif n' (S a) 1 (blk false 0 t0)
      | p10 t0 => Some (a, p01 1 t1)
      | p10 t1 => Some (a, p11 0 t1)
      | p00 t0 => Some (S a, t1)
      | p00 t1 => phif n' (S (S a)) 1 t0
      | _ => None
      end
    | S (S b') =>
      match lpf n' w with
      | Some (w', d) => phif n' (S a) (addb (S b') d) w'
      | None => None
      end
    end
  end.

Lemma enc_p10t0 : enc (p10 t0) = enc t1.
Proof. cbn. rewrite <- const_unfold. reflexivity. Qed.

Lemma enc_p10t1 : enc (p10 t1) = enc (blk true 0 t0).
Proof. cbn [enc lpow dsym]. rewrite z3. reflexivity. Qed.

Lemma enc_p00t0 : enc (p00 t0) = enc t0.
Proof. cbn. rewrite <- !const_unfold. reflexivity. Qed.

Lemma enc_p00t1 : enc (p00 t1) = enc (blk false 0 t0).
Proof. cbn [enc lpow dsym]. rewrite z3. reflexivity. Qed.

Lemma enc_p10p00t0 : enc (p10 (p00 t0)) = enc t1.
Proof. cbn. rewrite <- !const_unfold. reflexivity. Qed.

Lemma enc_p10p00t1 : enc (p10 (p00 t1)) = enc (p10 (blk false 0 t0)).
Proof. cbn [enc lpow dsym]. rewrite z3. reflexivity. Qed.

Lemma model_sound n :
  (forall w w' d, lpf n w = Some (w', d) -> LP w w' d) /\
  (forall a b w k y, phif n a b w = Some (k, y) -> Phi a b w k y).
Proof.
  induction n as [|n [IHl IHp]]; [split; intros; discriminate|].
  split.
  - intros w w' d H. cbn [lpf] in H.
    destruct w as [| | | |[|] e w|[|x] w|x w|w|w]; try (inversion H; subst; constructor; fail).
    + destruct (lpf n w) as [[w1 d1]|] eqn:E; inversion H; subst. constructor. apply IHl, E.
    + destruct w as [| | | |[|] e w|[|x] w|x w|w|w]; try discriminate.
      * inversion H; subst. eapply LP_eq; [apply enc_p10t0 | constructor].
      * inversion H; subst. eapply LP_eq; [apply enc_p10t1 | ]. apply (LP_b 0 t0 t1 false). constructor.
      * inversion H; subst. constructor.
      * inversion H; subst. constructor.
      * destruct (phif n 1 (S e) w) as [[k y]|] eqn:E; inversion H; subst. constructor. apply IHp, E.
      * destruct (lpf n w) as [[w1 d1]|] eqn:E; inversion H; subst. constructor. apply IHl, E.
      * destruct x as [|[|x]]; try discriminate; destruct w; try discriminate;
          inversion H; subst; constructor.
      * destruct w; try discriminate; inversion H; subst.
        -- eapply LP_eq; [apply enc_p10p00t0 | constructor].
        -- eapply LP_eq; [apply enc_p10p00t1 | ]. apply (LP_5 0 t0 t1 false). constructor.
        -- constructor.
      * destruct w; try discriminate. destruct w; try discriminate. inversion H; subst.
        apply (LP_eq _ (blk true 0 t2)); [reflexivity | ]. apply (LP_b 0 t2 t3 false). constructor.
  - intros a b w k y H. cbn [phif] in H.
    destruct b as [|[|b]]; try discriminate.
    + destruct w as [| | | |[|] e w|[|x] w|x w|w|w]; try discriminate.
      * inversion H; subst. constructor.
      * inversion H; subst. constructor.
      * inversion H; subst. constructor.
      * constructor. apply IHp, H.
      * destruct (lpf n w) as [[w1 d1]|] eqn:E; inversion H; subst. constructor. apply IHl, E.
      * constructor. apply IHp, H.
      * destruct w; try discriminate; inversion H; subst.
        -- eapply Phi_eq; [apply enc_p00t0 | constructor].
        -- eapply Phi_eq; [apply enc_p00t1 | ]. constructor. apply IHp, H.
      * destruct w; try discriminate; inversion H; subst.
        -- eapply Phi_eq; [apply enc_p10t0 | constructor].
        -- eapply Phi_eq; [apply enc_p10t1 | ]. apply (Phi_E2 _ 0 t0 t1 false). constructor.
    + destruct (lpf n w) as [[w1 d1]|] eqn:E; try discriminate.
      eapply Phi_B; [apply IHl, E | apply IHp, H].
Qed.

Open Scope nat_scope.

Definition tl_of (s : nat) : word :=
  match s with O => t0 | 1 => t1 | 2 => t2 | _ => t3 end.

Fixpoint gw (bs : list (bool * nat)) (s : nat) : word :=
  match bs with [] => tl_of s | (d, e) :: bs => blk d e (gw bs s) end.

Fixpoint ginc (bs : list (bool * nat)) (s : nat) : list (bool * nat) * nat * bool :=
  match bs with
  | [] => match s with O => ([], 1, false) | 1 => ([], 2, false) | 2 => ([], 3, false)
          | _ => ([(false, 0)], O, true) end
  | (false, e) :: bs => ((true, e) :: bs, s, false)
  | (true, e) :: bs => let '(bs', s', d) := ginc bs s in ((false, addb e d) :: bs', s', false)
  end.

Fixpoint gval (bs : list (bool * nat)) (s : nat) : nat :=
  match bs with [] => 4 + s | (d, _) :: bs => (if d then 1 else 0) + 2 * gval bs s end.

Fixpoint gsum (bs : list (bool * nat)) : nat :=
  match bs with [] => O | (_, e) :: bs => e + gsum bs end.

Lemma ginc_LP bs s : s <= 3 -> forall bs' s' d, ginc bs s = (bs', s', d) -> LP (gw bs s) (gw bs' s') d.
Proof.
  intros Hs. induction bs as [|[[|] e] bs IH]; intros bs' s' d E; cbn in E.
  - destruct s as [|[|[|[|s]]]]; inversion E; subst; cbn; try constructor; lia.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. inversion E; subst. cbn. constructor. apply IH; reflexivity.
  - inversion E; subst. constructor.
Qed.

Lemma ginc_val bs s : s <= 3 -> forall bs' s' d, ginc bs s = (bs', s', d) ->
  gval bs' s' = S (gval bs s) /\ s' <= 3 /\
  gsum bs' + length bs + (if d then 1 else 0) = gsum bs + length bs' /\
  (d = true -> bs = []) /\ length bs <= length bs'.
Proof.
  intros Hs. induction bs as [|[[|] e] bs IH]; intros bs' s' d E; cbn in E.
  - destruct s as [|[|[|[|s]]]]; inversion E; subst; cbn; repeat split; try lia; auto.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. inversion E; subst.
    destruct (IH _ _ _ eq_refl) as (H1 & H2 & H3 & H4 & H5). cbn.
    destruct d1; cbn [addb]; [specialize (H4 eq_refl); subst bs; cbn in *|]; repeat split; try lia; discriminate.
  - inversion E; subst. cbn. repeat split; try lia; discriminate.
Qed.

Lemma gval_ge bs s : 4 <= gval bs s.
Proof. induction bs as [|[d e] bs IH]; cbn; lia. Qed.

Lemma gval_len bs s : length bs <= gval bs s.
Proof. induction bs as [|[d e] bs IH]; cbn; [lia|]. pose proof (gval_ge bs s). lia. Qed.

Definition Psi (bs : list (bool * nat)) (s b : nat) : nat := gval bs s + b + gsum bs - length bs.

Import ListNotations.

Definition blks := list (bool * nat).

Definition b2n (d : bool) : nat := if d then 1 else 0.

Lemma addb_b2n e d : addb e d = e + b2n d.
Proof. destruct d; cbn; lia. Qed.

Inductive GRes : Type := RE2 (k x : nat) (bs : blks) (s : nat) | RSp (k : nat) (y : word).

Definition rk (r : GRes) : nat := match r with RE2 k _ _ _ => k | RSp k _ => k end.

Definition ry (r : GRes) : word := match r with RE2 _ x bs s => p11 x (gw bs s) | RSp _ y => y end.

Inductive GPhi : nat -> nat -> blks -> nat -> GRes -> Prop :=
| GB a b bs s bs' s' d r : ginc bs s = (bs', s', d) -> GPhi (S a) (addb (S b) d) bs' s' r ->
    GPhi a (S (S b)) bs s r
| GE1 a e bs s r : GPhi (S (S a)) (S e) bs s r -> GPhi a 1 ((false, e) :: bs) s r
| GE2 a e bs s bs' s' d : ginc bs s = (bs', s', d) ->
    GPhi a 1 ((true, e) :: bs) s (RE2 a (addb e d) bs' s')
| GE0 a : GPhi a 1 [] 0 (RSp (S a) t1)
| GEt1 a : GPhi a 1 [] 1 (RSp a (p01 1 t1))
| GEt2 a : GPhi a 1 [] 2 (RSp a (p10 (p00 t2)))
| GEt3 a r : GPhi (S a) 1 [(false, 0)] 0 r -> GPhi a 1 [] 3 r.

Lemma ginc_s3 bs s bs' s' d : s <= 3 -> ginc bs s = (bs', s', d) -> s' <= 3.
Proof. intros Hs E. destruct (ginc_val bs s Hs _ _ _ E) as (_ & H & _). exact H. Qed.

Lemma GPhi_sound a b bs s r : GPhi a b bs s r -> s <= 3 -> Phi a b (gw bs s) (rk r) (ry r).
Proof.
  induction 1; intros Hs; cbn [gw rk ry tl_of] in *.
  - eapply Phi_B. { apply (ginc_LP bs s Hs _ _ _ H). } apply IHGPhi. eapply ginc_s3; eauto.
  - apply Phi_E1. apply IHGPhi. exact Hs.
  - apply Phi_E2. apply (ginc_LP bs s Hs _ _ _ H).
  - apply Phi_E0.
  - apply Phi_Et1.
  - apply Phi_Et2.
  - apply Phi_Et3. apply IHGPhi. lia.
Qed.

Lemma GPhi_s3 a b bs s r : GPhi a b bs s r -> s <= 3 ->
  match r with RE2 _ _ _ s2 => s2 <= 3 | RSp _ y => y = t1 \/ y = p01 1 t1 \/ y = p10 (p00 t2) end.
Proof.
  induction 1; intros Hs; auto; try (apply IHGPhi; first [lia | eapply ginc_s3; eauto]).
  eapply ginc_s3; eauto.
Qed.

Lemma GPhi_rk a b bs s r : GPhi a b bs s r -> a + b <= S (rk r).
Proof. induction 1; try destruct d; cbn [rk addb] in *; lia. Qed.

Lemma gcount : forall P bs s a b, s <= 3 -> 1 <= b -> Psi bs s b <= P -> exists r, GPhi a b bs s r.
Proof.
  induction P as [P IHP] using lt_wf_ind.
  intros bs s a b. revert bs s a. induction b as [b IHb] using lt_wf_ind. intros bs s a Hs Hb HP.
  destruct b as [|[|b]]; [lia| |].
  - destruct bs as [|[[|] e] bs].
    + destruct s as [|[|[|[|s]]]]; try lia.
      * eexists. apply GE0.
      * eexists. apply GEt1.
      * eexists. apply GEt2.
      * eexists. apply GEt3. apply (GE1 _ 0 []). apply GE0.
    + destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. eexists. eapply GE2. exact E1.
    + assert (Hlt : Psi bs s (S e) < P).
      { unfold Psi in *. cbn [gval gsum length] in HP. pose proof (gval_ge bs s). pose proof (gval_len bs s). lia. }
      destruct (IHP _ Hlt bs s (S (S a)) (S e) Hs ltac:(lia) (le_n _)) as (r & H).
      exists r. apply GE1, H.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1.
    destruct (ginc_val bs s Hs _ _ _ E1) as (V1 & S1 & M1 & D1 & L1).
    destruct d1.
    + specialize (D1 eq_refl). subst bs. cbn in E1.
      destruct s as [|[|[|[|s]]]]; inversion E1; subst; try lia.
      assert (Hlt : S b < S (S b)) by lia.
      destruct (IHb _ Hlt [(true, 0)] 0 (S (S a)) ltac:(lia) ltac:(lia)) as (r & H).
      { unfold Psi in *. cbn in HP |- *. lia. }
      exists r. eapply GB. { exact E1. }
      cbn [addb]. eapply GB. { reflexivity. } exact H.
    + assert (Hlt : S b < S (S b)) by lia.
      destruct (IHb _ Hlt b1 s1 (S a) S1 ltac:(lia)) as (r & H).
      { unfold Psi in *. lia. }
      exists r. eapply GB. { exact E1. } exact H.
Qed.

Inductive LPs : word -> word -> nat -> nat -> Prop :=
| LPs_eq w w' : enc w = enc w' -> LPs w w' 0 0
| LPs_step w w1 w2 d n c : LP w w1 d -> LPs w1 w2 n c -> LPs w w2 (S n) (c + b2n d).

Lemma LPs_step' w w1 w2 d n c c' : LP w w1 d -> LPs w1 w2 n c -> c' = c + b2n d -> LPs w w2 (S n) c'.
Proof. intros H1 H2 ->. econstructor; eauto. Qed.

Lemma LPs_eql w0 w1 w2 n c : enc w0 = enc w1 -> LPs w1 w2 n c -> LPs w0 w2 n c.
Proof.
  intros E H. inversion H; subst.
  - apply LPs_eq. congruence.
  - eapply LPs_step; [apply (LP_eq _ _ _ _ E); eassumption | eassumption].
Qed.

Lemma LPs_trans w1 w2 w3 n c n' c' : LPs w1 w2 n c -> LPs w2 w3 n' c' -> LPs w1 w3 (n + n') (c + c').
Proof.
  intros H. revert n' c' w3. induction H; intros n' c' w3 H'.
  - cbn. eapply LPs_eql; eassumption.
  - eapply LPs_step'; [eassumption | apply IHLPs, H' | ]. destruct d; cbn; lia.
Qed.

Lemma LPs_cn w w' n c : LPs w w' n c -> c <= n.
Proof. induction 1; [lia | destruct d; cbn; lia]. Qed.

Lemma LPs_hub w w' n c : LPs w w' n c -> forall a B k y, n + 2 <= B + c ->
  Phi (a + n) (B + c - n) w' k y -> Phi a B w k y.
Proof.
  induction 1 as [w w' E | w w1 w2 d n c H1 H2 IH]; intros a B k y Hb HP.
  - rewrite Nat.add_0_r in HP. replace (B + 0 - 0) with B in HP by lia. eapply Phi_eq; eassumption.
  - pose proof (LPs_cn _ _ _ _ H2) as Hc.
    destruct B as [|[|B]]; [destruct d; cbn in Hb; lia | destruct d; cbn in Hb; lia |].
    eapply Phi_B; [exact H1|]. apply IH.
    + rewrite addb_b2n. destruct d; unfold b2n in *; lia.
    + rewrite addb_b2n. replace (S a + n) with (a + S n) by lia.
      replace (S B + b2n d + c - n) with (S (S B) + (c + b2n d) - S n) by (destruct d; unfold b2n; lia).
      exact HP.
Qed.

Lemma LPs_nest y y' n c : LPs y y' n c -> forall k, LPs (blk false k y) (blk false (k + c) y') (2 * n) 0.
Proof.
  induction 1 as [y y' E | y y1 y2 d n c H1 H2 IH]; intros k.
  - rewrite Nat.add_0_r. apply LPs_eq. cbn [enc]. rewrite E. reflexivity.
  - replace (2 * S n) with (S (S (2 * n))) by lia.
    replace (k + (c + b2n d)) with (addb k d + c) by (rewrite addb_b2n; lia).
    eapply LPs_step'; [apply LP_a | eapply LPs_step'; [apply (LP_b k y y1 d H1) | apply IH | reflexivity] | reflexivity].
Qed.

Inductive DigE : word -> nat -> nat -> blks -> nat -> Prop :=
| DE0 : DigE (p10 t0) 0 0 [] 1
| DE1 : DigE (p10 t1) 0 0 [(true, 0)] 0
| DE2 : DigE (p10 t2) 13 5 [(false, 0)] 2
| DE3 : DigE (p10 t3) 7 2 [(false, 0)] 2
| DEs0 : DigE t1 0 0 [] 1
| DEs1 : DigE (p01 1 t1) 2 1 [] 2
| DEs2 : DigE (p10 (p00 t2)) 11 4 [(false, 0)] 2.

Ltac lps := first [ apply LPs_eq; first [reflexivity | apply enc_p10t0 | apply enc_p10t1]
                  | eapply LPs_step'; [ constructor | lps | reflexivity ] ].

Lemma DigE_sound y n c bs s : DigE y n c bs s -> LPs y (gw bs s) n c.
Proof. destruct 1; cbn [gw tl_of]; lps. Qed.

Lemma DigE_props y n c bs s : DigE y n c bs s ->
  n <= 13 /\ c <= 5 /\ length bs <= 1 /\ s <= 3 /\ Forall (fun e => e = 0) (map snd bs).
Proof. destruct 1; cbn; repeat split; auto; lia. Qed.

Inductive DigP : nat -> blks -> nat -> nat -> nat -> blks -> nat -> Prop :=
| DP x bs s n c bsp sp : DigT bs s n c bsp sp -> DigP x bs s (2 * x + 2 + n) (S x + c) bsp sp
with DigT : blks -> nat -> nat -> nat -> blks -> nat -> Prop :=
| DTa e bs s bs' s' d n c bsp sp : ginc bs s = (bs', s', d) ->
    DigP (S (addb e d)) bs' s' n c bsp sp -> DigT ((false, e) :: bs) s (S (S n)) c bsp sp
| DTb e bs s k x bs2 s2 n c bsp sp : GPhi 1 (S e) bs s (RE2 k x bs2 s2) ->
    DigP x bs2 s2 n c bsp sp -> DigT ((true, e) :: bs) s (S (2 * n)) 0 ((false, k + c) :: bsp) sp
| DTs e bs s k y n c bsp sp : GPhi 1 (S e) bs s (RSp k y) ->
    DigE y n c bsp sp -> DigT ((true, e) :: bs) s (S (2 * n)) 0 ((false, k + c) :: bsp) sp
| DTt s n c bsp sp : DigE (p10 (tl_of s)) n c bsp sp -> DigT [] s n c bsp sp.

Scheme DigP_mind := Induction for DigP Sort Prop
with DigT_mind := Induction for DigT Sort Prop.

Combined Scheme Dig_mind from DigP_mind, DigT_mind.

Lemma prefix_LPs x w : LPs (p11 x w) (p10 w) (2 * x + 2) (S x).
Proof.
  induction x as [|x IH].
  - eapply LPs_step'; [apply LP_110 | eapply LPs_step'; [apply LP_00 | apply LPs_eq; reflexivity | reflexivity] | reflexivity].
  - replace (2 * S x + 2) with (S (S (2 * x + 2))) by lia.
    eapply LPs_step'; [apply LP_11S | eapply LPs_step'; [apply LP_01 | exact IH | reflexivity] | cbn; lia].
Qed.

Lemma Dig_sound :
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> LPs (p11 x (gw bs s)) (gw bsp sp) n c) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> LPs (p10 (gw bs s)) (gw bsp sp) n c).
Proof.
  apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs.
    exact (LPs_trans _ _ _ _ _ _ _ (prefix_LPs x (gw bs s)) (IH Hs)).
  - intros e bs s bs' s' d n c bsp sp E H IH Hs. cbn [gw].
    eapply LPs_step'; [apply LP_5, (ginc_LP bs s Hs _ _ _ E) |
      eapply LPs_step'; [apply LP_01 | apply IH; eapply ginc_s3; eauto | reflexivity] | cbn; lia].
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs. cbn [gw].
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    eapply LPs_step'; [apply LP_6; exact (GPhi_sound _ _ _ _ _ HG Hs) |
      exact (LPs_nest _ _ _ _ (IH Hs2) k) | reflexivity].
  - intros e bs s k y n c bsp sp HG H Hs. cbn [gw].
    eapply LPs_step'; [apply LP_6; exact (GPhi_sound _ _ _ _ _ HG Hs) |
      exact (LPs_nest _ _ _ _ (DigE_sound _ _ _ _ _ H) k) | reflexivity].
  - intros s n c bsp sp H Hs. cbn [gw]. exact (DigE_sound _ _ _ _ _ H).
Qed.

Lemma Dig_sp :
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> sp <= 3) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> sp <= 3).
Proof.
  apply Dig_mind; intros; auto; eapply DigE_props; eassumption.
Qed.

Lemma epoch_ord N x bs s n c bsp sp r : s <= 3 -> DigP x bs s n c bsp sp -> n + 2 <= N ->
  GPhi (1 + n) (N + c - n) bsp sp r -> Phi 1 N (p11 x (gw bs s)) (rk r) (ry r).
Proof.
  intros Hs HD Hn HG.
  apply (LPs_hub _ _ _ _ (proj1 Dig_sound _ _ _ _ _ _ _ HD Hs) 1 N); [lia|].
  apply GPhi_sound; [exact HG | exact (proj1 Dig_sp _ _ _ _ _ _ _ HD)].
Qed.

Lemma epoch_spec N y n c bsp sp r : DigE y n c bsp sp -> n + 2 <= N ->
  GPhi (1 + n) (N + c - n) bsp sp r -> Phi 1 N y (rk r) (ry r).
Proof.
  intros HD Hn HG.
  apply (LPs_hub _ _ _ _ (DigE_sound _ _ _ _ _ HD) 1 N); [lia|].
  apply GPhi_sound; [exact HG | apply (DigE_props _ _ _ _ _ HD)].
Qed.

Definition exs (bs : blks) : list nat := map snd bs.

Fixpoint bumpl (l : list nat) : list nat :=
  match l with [] => [] | e :: l' => match l' with [] => [S e] | _ => e :: bumpl l' end end.

Lemma length_bumpl l : length (bumpl l) = length l.
Proof. induction l as [|e l IH]; [reflexivity|]. destruct l; cbn in *; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma length_exs bs : length (exs bs) = length bs.
Proof. apply length_map. Qed.

Lemma ginc_exps bs s : s <= 3 -> forall bs' s' d, ginc bs s = (bs', s', d) ->
  (exs bs' = exs bs /\ d = false) \/
  (exs bs' = bumpl (exs bs) ++ [0] /\ d = match bs with [] => true | _ => false end).
Proof.
  intros Hs. induction bs as [|[[|] e] bs IH]; intros bs' s' d E; cbn in E.
  - destruct s as [|[|[|[|s]]]]; inversion E; subst; cbn; auto; lia.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. inversion E; subst.
    destruct (IH _ _ _ eq_refl) as [[H1 H2] | [H1 H2]]; subst; unfold exs in *; cbn [map snd].
    + left. rewrite H1. auto.
    + right. rewrite H1. destruct bs as [|b bs]; cbn in *; subst; cbn; auto.
  - inversion E; subst. left. auto.
Qed.

Fixpoint qsum (l : list nat) : nat := match l with [] => 0 | e :: l => S e + 2 * qsum l end.

Definition Qp (f : nat) (bs : blks) (s p : nat) : nat := 2 ^ f * (gval bs s + 2 * qsum (exs bs) + p).

Definition QI (Q0 f : nat) (bs : blks) (s p : nat) : Prop := Qp f bs s p <= Q0 + 3 * 2 ^ (f + length bs).

Lemma qsum_app0 l : qsum (l ++ [0]) = qsum l + 2 ^ length l.
Proof. induction l as [|e l IH]; cbn [qsum app length]; [reflexivity|]. rewrite IH. cbn. lia. Qed.

Lemma qsum_bumpl l : l <> [] -> 2 * qsum (bumpl l) = 2 * qsum l + 2 ^ length l.
Proof.
  induction l as [|e l IH]; intros Hne; [congruence|].
  destruct l as [|e' l]; [cbn; lia|].
  change (bumpl (e :: e' :: l)) with (e :: bumpl (e' :: l)).
  cbn [qsum length]. rewrite Nat.pow_succ_r'. specialize (IH ltac:(discriminate)). cbn [qsum length] in IH. lia.
Qed.

Lemma gval_lb bs s : 4 * 2 ^ length bs <= gval bs s.
Proof. induction bs as [|[d e] bs IH]; cbn [gval length]; [cbn; lia|]. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma gval_ub bs s : s <= 3 -> gval bs s < 8 * 2 ^ length bs.
Proof. intros Hs. induction bs as [|[d e] bs IH]; cbn [gval length]; [cbn; lia|]. rewrite Nat.pow_succ_r'. destruct d; lia. Qed.

Lemma QI_low Q0 f bs s p : QI Q0 f bs s p -> 2 ^ (f + length bs) <= Q0.
Proof.
  unfold QI, Qp. intros H. pose proof (gval_lb bs s) as G. rewrite Nat.pow_add_r in *.
  assert (2 ^ f * (4 * 2 ^ length bs) <= 2 ^ f * (gval bs s + 2 * qsum (exs bs) + p)) by (apply Nat.mul_le_mono_l; lia).
  lia.
Qed.

Lemma QI_Ps Q0 Ps f bs s p : QI Q0 f bs s p -> Q0 < 2 ^ (Ps + 1) -> f + length bs <= Ps.
Proof.
  intros H HP. apply QI_low in H. destruct (Nat.le_gt_cases (f + length bs) Ps) as [|Hc]; [assumption|].
  assert (2 ^ (Ps + 1) <= 2 ^ (f + length bs)) by (apply Nat.pow_le_mono_r; lia). lia.
Qed.

Lemma QI_drop Q0 f bs s p : QI Q0 f bs s p -> QI Q0 f bs s 0.
Proof. unfold QI, Qp. intros H. assert (2 ^ f * (gval bs s + 2 * qsum (exs bs) + 0) <= 2 ^ f * (gval bs s + 2 * qsum (exs bs) + p)) by (apply Nat.mul_le_mono_l; lia). lia. Qed.

Lemma QI_cons Q0 f dd e bs s p : QI Q0 f ((dd, e) :: bs) s 0 -> p <= S e -> QI Q0 (S f) bs s p.
Proof.
  unfold QI, Qp, exs. cbn [map snd qsum gval length]. intros H Hp.
  replace (S f + length bs) with (f + S (length bs)) by lia.
  rewrite Nat.pow_succ_r'.
  set (F := 2 ^ f) in *. set (G := gval bs s) in *. set (Q := qsum (map snd bs)) in *.
  assert (F * p <= F * S e) by (apply Nat.mul_le_mono_l; lia).
  assert (E1 : 2 * F * (G + 2 * Q + p) = 2 * (F * G) + 4 * (F * Q) + 2 * (F * p)) by ring.
  assert (E2 : F * ((if dd then 1 else 0) + 2 * G + 2 * (S e + 2 * Q) + 0) =
    F * (if dd then 1 else 0) + 2 * (F * G) + 2 * (F * S e) + 4 * (F * Q)) by ring.
  rewrite E1. rewrite E2 in H. lia.
Qed.

Lemma QI_inc Q0 f bs s p bs' s' d : s <= 3 -> ginc bs s = (bs', s', d) ->
  QI Q0 f bs s (S p) -> QI Q0 f bs' s' (p + b2n d).
Proof.
  intros Hs E H. unfold QI, Qp in *.
  destruct (ginc_val bs s Hs _ _ _ E) as (V & _).
  destruct (ginc_exps bs s Hs _ _ _ E) as [[E1 E2] | [E1 E2]]; subst d.
  - assert (L : length bs' = length bs) by (rewrite <- !length_exs, E1; reflexivity).
    rewrite E1, V, L. cbn [b2n]. replace (S (gval bs s) + 2 * qsum (exs bs) + (p + 0)) with
      (gval bs s + 2 * qsum (exs bs) + S p) by lia. exact H.
  - assert (L : length bs' = S (length bs))
      by (rewrite <- !length_exs, E1, length_app, length_bumpl; cbn; lia).
    rewrite E1, V, L, qsum_app0, length_bumpl, length_exs.
    replace (f + S (length bs)) with (S (f + length bs)) by lia.
    rewrite Nat.pow_succ_r'. rewrite Nat.pow_add_r in *.
    destruct bs as [|b bs0].
    + cbn [bumpl exs map qsum length b2n] in *. rewrite Nat.pow_0_r in *.
      rewrite !Nat.mul_add_distr_l in *. lia.
    + cbn [b2n]. pose proof (qsum_bumpl (exs (b :: bs0)) ltac:(cbn; discriminate)) as QB.
      rewrite length_exs in QB.
      set (F := 2 ^ f) in *. set (X := 2 ^ length (b :: bs0)) in *.
      set (G := gval (b :: bs0) s) in *. set (Q := qsum (exs (b :: bs0))) in *.
      set (Q' := qsum (bumpl (exs (b :: bs0)))) in *.
      rewrite !Nat.mul_add_distr_l in *.
      assert (F * (2 * (Q' + X)) = 2 * (F * Q) + 3 * (F * X)) by nia.
      lia.
Qed.

Lemma QI_et3 Q0 f : QI Q0 f [] 3 0 -> QI Q0 f [(false, 0)] 0 0.
Proof. unfold QI, Qp. cbn. rewrite !Nat.add_0_r. rewrite Nat.add_1_r, Nat.pow_succ_r'. lia. Qed.

Fixpoint wpot (v : nat -> nat) (al be f : nat) (l : list nat) : nat :=
  match l with [] => 0 | e :: l => v f * (al * e + be) + wpot v al be (S f) l end.

Fixpoint vsum (v : nat -> nat) (f m : nat) : nat :=
  match m with 0 => 0 | S m => v f + vsum v (S f) m end.

Definition Pot (v : nat -> nat) (al be ga Ps f : nat) (l : list nat) : nat :=
  wpot v al be f l + ga * vsum v (f + length l) (Ps - (f + length l)).

Definition mono (v : nat -> nat) : Prop := forall i j, i <= j -> v i <= v j.

Lemma Pot_cons v al be ga Ps f e l :
  Pot v al be ga Ps f (e :: l) = v f * (al * e + be) + Pot v al be ga Ps (S f) l.
Proof. unfold Pot. cbn [wpot length]. replace (f + S (length l)) with (S f + length l) by lia. lia. Qed.

Lemma wpot_app1 v al be f l x : wpot v al be f (l ++ [x]) = wpot v al be f l + v (f + length l) * (al * x + be).
Proof.
  revert f. induction l as [|e l IH]; intros f; cbn [wpot app length].
  - rewrite !Nat.add_0_r. reflexivity.
  - rewrite IH. replace (S f + length l) with (f + S (length l)) by lia. lia.
Qed.

Lemma wpot_bumpl v al be f l : mono v -> wpot v al be f (bumpl l) <= wpot v al be f l + al * v (f + length l).
Proof.
  intros Hv. revert f. induction l as [|e l IH]; intros f; [cbn; lia|].
  destruct l as [|e' l].
  - cbn [bumpl wpot length]. pose proof (Hv f (f + 1) ltac:(lia)). nia.
  - change (bumpl (e :: e' :: l)) with (e :: bumpl (e' :: l)). cbn [wpot length].
    specialize (IH (S f)). cbn [wpot length] in IH. replace (S f + S (length l)) with (f + S (S (length l))) in IH by lia.
    lia.
Qed.

Lemma Pot_ov v al be ga Ps f l : mono v -> al + be + 1 <= ga -> f + length l + 1 <= Ps ->
  Pot v al be ga Ps f (bumpl l ++ [0]) + v (f + length l) <= Pot v al be ga Ps f l.
Proof.
  intros Hv Hg HP. unfold Pot. rewrite wpot_app1, length_app, length_bumpl. cbn [length].
  pose proof (wpot_bumpl v al be f l Hv) as B.
  replace (Ps - (f + length l)) with (S (Ps - (f + (length l + 1)))) by lia.
  cbn [vsum]. replace (S (f + length l)) with (f + (length l + 1)) by lia.
  set (V := v (f + length l)) in *. set (R := vsum v (f + (length l + 1)) (Ps - (f + (length l + 1)))).
  assert ((al + be + 1) * V <= ga * V) by (apply Nat.mul_le_mono_r; lia).
  rewrite Nat.mul_0_r, Nat.add_0_l, Nat.mul_add_distr_l. rewrite !Nat.mul_add_distr_r in *. lia.
Qed.

Lemma Pot_inc v al be ga Ps Q0 f bs s p bs' s' d : mono v -> al + be + 1 <= ga -> Q0 < 2 ^ (Ps + 1) -> s <= 3 ->
  ginc bs s = (bs', s', d) -> QI Q0 f bs s (S p) ->
  Pot v al be ga Ps f (exs bs') + b2n d * v f <= Pot v al be ga Ps f (exs bs).
Proof.
  intros Hv Hg HP Hs E HQ.
  pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ) as HQ'. apply (QI_Ps _ Ps) in HQ'; [|exact HP].
  destruct (ginc_exps bs s Hs _ _ _ E) as [[E1 E2] | [E1 E2]]; subst.
  - rewrite E1. cbn. lia.
  - rewrite E1. assert (length bs' = S (length bs)) as L
      by (rewrite <- !length_exs, E1, length_app, length_bumpl; cbn; lia).
    pose proof (Pot_ov v al be ga Ps f (exs bs) Hv Hg) as O. rewrite length_exs in O.
    specialize (O ltac:(lia)). destruct bs; cbn [b2n] in *; [rewrite Nat.add_0_r in O; lia | lia].
Qed.

Lemma GPhi_pot v al be ga Ps Q0 : mono v -> al + be + 1 <= ga -> 1 <= al -> 2 <= be -> Q0 < 2 ^ (Ps + 1) ->
  forall a b bs s r, GPhi a b bs s r -> s <= 3 -> forall f U, QI Q0 f bs s (b - 1) ->
  (forall q, f <= q -> U <= v q) ->
  match r with
  | RE2 k x bs2 s2 => exists h, QI Q0 (f + S h) bs2 s2 0 /\
      U * k + Pot v al be ga Ps (f + S h) (exs bs2) + v (f + h) * (al * x + be) <=
      Pot v al be ga Ps f (exs bs) + U * (a + b - 1) + al * v (f + h)
  | RSp k y => U * k <= Pot v al be ga Ps f (exs bs) + U * (a + b)
  end.
Proof.
  intros Hv Hg Ha Hb HP.
  induction 1 as [a b bs s bs' s' d r E H IH | a e bs s r H IH | a e bs s bs' s' d E | a | a | a | a r H IH];
    intros Hs f U HQ HU.
  -  
    replace (S (S b) - 1) with (S b) in HQ by lia.
    pose proof (Pot_inc v al be ga Ps Q0 f bs s b bs' s' d Hv Hg HP Hs E HQ) as PI.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ) as HQ'.
    specialize (IH (ginc_s3 _ _ _ _ _ Hs E) f U).
    rewrite addb_b2n in IH. replace (S b + b2n d - 1) with (b + b2n d) in IH by lia.
    specialize (IH HQ' HU). pose proof (HU f (le_n _)) as Uf.
    destruct r as [k x bs2 s2 | k y].
    + destruct IH as (h & H1 & H2). exists h. split; [exact H1|].
      assert (U * b2n d <= b2n d * v f) by (destruct d; cbn; lia). nia.
    + assert (U * b2n d <= b2n d * v f) by (destruct d; cbn; lia). nia.
  -  
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ'.
    specialize (IH Hs (S f) U). replace (S e - 1) with e in IH by lia. specialize (IH HQ').
    specialize (IH (fun q Hq => HU q ltac:(lia))). pose proof (HU f (le_n _)) as Uf.
    change (exs ((false, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    assert (U * (e + 2) <= v f * (al * e + be)).
    { apply (Nat.le_trans _ (v f * (e + 2))); [apply Nat.mul_le_mono_r; exact Uf|].
      apply Nat.mul_le_mono_l. assert (e <= al * e) by nia. lia. }
    destruct r as [k x bs2 s2 | k y].
    + destruct IH as (h & H1 & H2). exists (S h).
      replace (f + S (S h)) with (S f + S h) by lia. replace (f + S h) with (S f + h) by lia.
      split; [exact H1|].
      replace (S (S a) + S e - 1) with (a + (e + 2)) in H2 by lia. rewrite (Nat.mul_add_distr_l U a (e + 2)) in H2.
      replace (a + 1 - 1) with a by lia. lia.
    + replace (S (S a) + S e) with ((a + 1) + (e + 2)) in IH by lia. rewrite (Nat.mul_add_distr_l U (a + 1) (e + 2)) in IH. lia.
  -  
    exists 0. pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2.
    pose proof (Pot_inc v al be ga Ps Q0 (S f) bs s 0 bs' s' d Hv Hg HP Hs E HQ1) as PI.
    replace (f + 1) with (S f) by lia. rewrite Nat.add_0_r.
    split; [eapply QI_drop; exact HQ2|].
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons, addb_b2n.
    assert (v f * (al * (e + b2n d) + be) <= v f * (al * e + be) + al * v f) by (destruct d; cbn; nia).
    replace (a + 1 - 1) with a by lia. lia.
  - nia.
  - nia.
  - nia.
  -  
    pose proof (QI_et3 _ _ HQ) as HQ'.
    pose proof (QI_Ps _ Ps _ _ _ _ HQ' HP) as HPs. cbn [length] in HPs.
    pose proof (Pot_ov v al be ga Ps f [] Hv Hg ltac:(cbn; lia)) as O. cbn [bumpl app length] in O.
    rewrite Nat.add_0_r in O.
    specialize (IH ltac:(lia) f U HQ' HU). pose proof (HU f (le_n _)) as Uf.
    destruct r as [k x bs2 s2 | k y].
    + destruct IH as (h & H1 & H2). exists h. split; [exact H1|]. cbn [exs map snd] in *.
      replace (S a + 1 - 1) with (a + 1) in H2 by lia. rewrite (Nat.mul_add_distr_l U a 1) in H2.
      replace (a + 1 - 1) with a by lia. lia.
    + cbn [exs map snd] in *. replace (S a + 1) with (a + 1 + 1) in IH by lia.
      rewrite (Nat.mul_add_distr_l U (a + 1) 1) in IH. lia.
Qed.

Definition w (q : nat) : nat := 2 ^ ((q + 1) / 2).

Lemma w_mono : mono w.
Proof. intros i j H. unfold w. apply Nat.pow_le_mono_r; [lia|]. apply Nat.Div0.div_le_mono; lia. Qed.

Lemma w_lev l q : 2 * l <= q -> 2 ^ l <= w q.
Proof.
  intros H. unfold w. apply Nat.pow_le_mono_r; [lia|].
  replace l with ((2 * l) / 2) at 1 by (rewrite Nat.mul_comm, Nat.div_mul; lia).
  apply Nat.Div0.div_le_mono; lia.
Qed.

Lemma w_lev1 l q : 2 * l + 1 <= q -> 2 ^ S l <= w q.
Proof.
  intros H. unfold w. apply Nat.pow_le_mono_r; [lia|].
  replace (S l) with ((2 * S l) / 2) at 1 by (rewrite Nat.mul_comm, Nat.div_mul; lia).
  apply Nat.Div0.div_le_mono; lia.
Qed.

Lemma GPhi_QI Q0 Ps a b bs s k x bs2 s2 f : Q0 < 2 ^ (Ps + 1) -> GPhi a b bs s (RE2 k x bs2 s2) -> s <= 3 ->
  QI Q0 f bs s (b - 1) -> exists h, QI Q0 (f + S h) bs2 s2 0.
Proof.
  intros HP HG Hs HQ.
  pose proof (GPhi_pot (fun _ => 0) 1 2 4 Ps Q0 ltac:(intros ? ? ?; lia) ltac:(lia) ltac:(lia) ltac:(lia) HP
    _ _ _ _ _ HG Hs f 0 HQ ltac:(intros; lia)) as G.
  destruct G as (h & G & _). eauto.
Qed.

Lemma Dig_cost Q0 Ps : Q0 < 2 ^ (Ps + 1) ->
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 ^ l * n <= Pot w 2 8 11 Ps f (exs bs) + 2 ^ l * (2 * x + 2) + 13 * w Ps) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 ^ l * n <= Pot w 2 8 11 Ps f (exs bs) + 13 * w Ps).
Proof.
  intros HP. apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs l f Hl HQ. specialize (IH Hs l f Hl HQ).
    rewrite Nat.mul_add_distr_l. lia.
  - intros e bs s bs' s' d n c bsp sp E H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    specialize (IH (ginc_s3 _ _ _ _ _ Hs E) l (S f) ltac:(lia) HQ2).
    pose proof (Pot_inc w 2 8 11 Ps Q0 (S f) bs s 0 bs' s' d w_mono ltac:(lia) HP Hs E HQ1) as PI.
    change (exs ((false, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (w_lev l f Hl) as Wf. set (L := 2 ^ l) in *.
    assert (E1 : L * S (S n) = L * n + 2 * L) by ring.
    assert (E2 : L * (2 * S (addb e d) + 2) + 2 * L <= w f * (2 * e + 8)).
    { rewrite addb_b2n. assert (L * (2 * S (e + b2n d) + 2) + 2 * L <= L * (2 * e + 8)) by (destruct d; cbn [b2n]; nia).
      assert (L * (2 * e + 8) <= w f * (2 * e + 8)) by (apply Nat.mul_le_mono_r; exact Wf). lia. }
    lia.
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_pot w 2 8 11 Ps Q0 w_mono ltac:(lia) ltac:(lia) ltac:(lia) HP _ _ _ _ _ HG Hs (S f) 0) as G.
    replace (S e - 1) with e in G by lia. specialize (G HQ1 (fun _ _ => Nat.le_0_l _)).
    destruct G as (h & G1 & G2).
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    specialize (IH Hs2 (S l) (S f + S h) ltac:(lia) G1).
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (w_lev l f Hl) as Wf. pose proof (w_lev1 l (S f + h) ltac:(lia)) as Wh.
    rewrite Nat.pow_succ_r' in IH, Wh. set (L := 2 ^ l) in *. set (W' := w (S f + h)) in *.
    assert (E1 : L * S (2 * n) = L + 2 * L * n) by ring.
    assert (E2 : 2 * L * (2 * x + 2) <= W' * (2 * x + 2)) by (apply Nat.mul_le_mono_r; exact Wh).
    assert (E3 : W' * (2 * x + 8) = W' * (2 * x + 2) + 6 * W') by ring.
    assert (E4 : L <= w f * (2 * e + 8)) by nia.
    rewrite Nat.mul_0_l in G2. lia.
  - intros e bs s k y n c bsp sp HG H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (Hn & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (w_lev l f Hl) as Wf. pose proof (w_lev1 l Ps ltac:(lia)) as Wh.
    rewrite Nat.pow_succ_r' in Wh. set (L := 2 ^ l) in *.
    assert (E1 : L * S (2 * n) = L + 2 * L * n) by ring.
    assert (E2 : 2 * L * n <= 13 * w Ps) by nia.
    assert (E4 : L <= w f * (2 * e + 8)) by nia.
    lia.
  - intros s n c bsp sp H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (Hn & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    pose proof (w_lev l Ps ltac:(lia)) as Wf. nia.
Qed.

Fixpoint MO (u : nat -> nat) (l : nat) (es : list nat) : nat :=
  match es with [] => 0 | e :: es => u l * e + MO u (S l) es end.

Definition pu (u : nat -> nat) (l : nat) : nat := match l with 0 => 0 | S l' => u l' end.

Lemma pu_le u l : mono u -> pu u l <= u l.
Proof. intros Hu. destruct l; cbn; [lia | apply Hu; lia]. Qed.

Lemma MO_zero u l es : Forall (fun e => e = 0) es -> MO u l es = 0.
Proof. intros H. revert l. induction H as [|e es He H IH]; intros l; cbn; [reflexivity|]. rewrite IH, He. lia. Qed.

Lemma Dig_mass u v Q0 Ps : mono v -> mono u -> (forall l q, 2 * l <= q -> u l <= v q) -> Q0 < 2 ^ (Ps + 1) ->
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    pu u l * c + MO u l (exs bsp) <= Pot v 1 3 5 Ps f (exs bs) + pu u l * S x + 6 * v Ps) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    pu u l * c + MO u l (exs bsp) <= Pot v 1 3 5 Ps f (exs bs) + 6 * v Ps).
Proof.
  intros Hv Hu Huv HP. apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs l f Hl HQ. specialize (IH Hs l f Hl HQ).
    rewrite Nat.mul_add_distr_l. lia.
  - intros e bs s bs' s' d n c bsp sp E H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    specialize (IH (ginc_s3 _ _ _ _ _ Hs E) l (S f) ltac:(lia) HQ2).
    pose proof (Pot_inc v 1 3 5 Ps Q0 (S f) bs s 0 bs' s' d Hv ltac:(lia) HP Hs E HQ1) as PI.
    change (exs ((false, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (Nat.le_trans _ _ _ (pu_le u l Hu) (Huv l f Hl)) as Pf.
    assert (pu u l * S (S (addb e d)) <= v f * (1 * e + 3)).
    { rewrite addb_b2n. apply Nat.mul_le_mono; [exact Pf | destruct d; cbn; lia]. }
    lia.
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_pot v 1 3 5 Ps Q0 Hv ltac:(lia) ltac:(lia) ltac:(lia) HP _ _ _ _ _ HG Hs (S f) (u l)) as G.
    replace (S e - 1) with e in G by lia. specialize (G HQ1 (fun q Hq => Huv l q ltac:(lia))).
    destruct G as (h & G1 & G2).
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    specialize (IH Hs2 (S l) (S f + S h) ltac:(lia) G1). cbn [pu] in IH.
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    change (exs ((false, k + c) :: bsp)) with ((k + c) :: exs bsp). cbn [MO].
    pose proof (Huv l f Hl) as Uf. pose proof (Huv l (S f + h) ltac:(lia)) as Uh.
    set (U := u l) in *. set (V' := v (S f + h)) in *.
    assert (E1 : U * S x <= V' * (x + 2)) by (apply Nat.mul_le_mono; lia).
    assert (E2 : V' * (1 * x + 3) = V' * (x + 2) + V') by ring.
    assert (E3 : U * (1 + S e - 1) <= v f * (1 * e + 3)) by (apply Nat.mul_le_mono; lia).
    assert (E4 : U * (k + c) = U * k + U * c) by ring.
    rewrite Nat.mul_0_r. lia.
  - intros e bs s k y n c bsp sp HG H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & Hc & _ & _ & Hz).
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_pot v 1 3 5 Ps Q0 Hv ltac:(lia) ltac:(lia) ltac:(lia) HP _ _ _ _ _ HG Hs (S f) (u l)) as G.
    replace (S e - 1) with e in G by lia. specialize (G HQ1 (fun q Hq => Huv l q ltac:(lia))). cbn beta iota in G.
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    change (exs ((false, k + c) :: bsp)) with ((k + c) :: exs bsp). cbn [MO]. rewrite (MO_zero _ _ _ Hz).
    pose proof (Huv l f Hl) as Uf. pose proof (Huv l Ps ltac:(lia)) as Up.
    set (U := u l) in *.
    assert (E3 : U * (1 + S e) <= v f * (1 * e + 3)) by (apply Nat.mul_le_mono; lia).
    assert (E4 : U * (k + c) = U * k + U * c) by ring.
    assert (E5 : U * c <= 6 * v Ps) by nia.
    rewrite Nat.mul_0_r. lia.
  - intros s n c bsp sp H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & Hc & _ & _ & Hz). rewrite (MO_zero _ _ _ Hz).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    pose proof (Nat.le_trans _ _ _ (pu_le u l Hu) (Huv l Ps ltac:(lia))) as Pf. nia.
Qed.

Lemma Dig_len Q0 Ps : Q0 < 2 ^ (Ps + 1) ->
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 * (l + length bsp) <= Ps + 3) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 * (l + length bsp) <= Ps + 3).
Proof.
  intros HP. apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs l f Hl HQ. exact (IH Hs l f Hl HQ).
  - intros e bs s bs' s' d n c bsp sp E H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    exact (IH (ginc_s3 _ _ _ _ _ Hs E) l (S f) ltac:(lia) HQ2).
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    destruct (GPhi_QI Q0 Ps _ _ _ _ _ _ _ _ (S f) HP HG Hs ltac:(replace (S e - 1) with e by lia; exact HQ1)) as (h & G1).
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    specialize (IH Hs2 (S l) (S f + S h) ltac:(lia) G1). cbn [length]. lia.
  - intros e bs s k y n c bsp sp HG H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & _ & Hb & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in *. lia.
  - intros s n c bsp sp H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & _ & Hb & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in *. lia.
Qed.

Lemma pow_gt_self n : n < 2 ^ (n + 1).
Proof. induction n as [|n IH]; cbn; [lia|]. rewrite Nat.add_0_r. lia. Qed.

Lemma DigE_ex y : y = t1 \/ y = p01 1 t1 \/ y = p10 (p00 t2) -> exists n c bsp sp, DigE y n c bsp sp.
Proof. intros [-> | [-> | ->]]; do 4 eexists; constructor. Qed.

Lemma DigT_exists Q0 : forall D f bs s, s <= 3 -> QI Q0 f bs s 0 -> Q0 + 1 - 2 ^ f <= D ->
  exists n c bsp sp, DigT bs s n c bsp sp.
Proof.
  induction D as [D IHD] using lt_wf_ind. intros f bs s Hs HQ HD.
  pose proof (pow_gt_self Q0) as HP.
  destruct bs as [|[[|] e] bs].
  - destruct s as [|[|[|[|s]]]]; try lia; do 4 eexists; apply DTt; constructor.
  - destruct (gcount (Psi bs s (S e)) bs s 1 (S e) Hs ltac:(lia) (le_n _)) as (r & HG).
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hr.
    destruct r as [k x bs2 s2 | k y].
    + destruct (GPhi_QI Q0 Q0 _ _ _ _ _ _ _ _ (S f) HP HG Hs ltac:(replace (S e - 1) with e by lia; exact HQ1)) as (h & G1).
      pose proof (QI_low _ _ _ _ _ G1) as L1. rewrite Nat.pow_add_r in L1.
      assert (2 ^ f < 2 ^ (S f + S h)) by (apply Nat.pow_lt_mono_r; lia).
      assert (1 <= 2 ^ length bs2) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
      assert (2 ^ (S f + S h) <= Q0) by nia.
      destruct (IHD (Q0 + 1 - 2 ^ (S f + S h)) ltac:(lia) (S f + S h) bs2 s2 Hr G1 (le_n _)) as (n & c & bsp & sp & HT).
      do 4 eexists. eapply DTb; [exact HG | apply DP; exact HT].
    + destruct (DigE_ex y Hr) as (n & c & bsp & sp & HE).
      do 4 eexists. eapply DTs; [exact HG | exact HE].
  - destruct (ginc bs s) as [[bs' s'] d] eqn:E.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    pose proof (QI_low _ _ _ _ _ HQ2) as L1. rewrite Nat.pow_add_r in L1.
    assert (2 ^ f < 2 ^ S f) by (apply Nat.pow_lt_mono_r; lia).
    assert (1 <= 2 ^ length bs') by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    assert (2 ^ S f <= Q0) by nia.
    destruct (IHD (Q0 + 1 - 2 ^ S f) ltac:(lia) (S f) bs' s' (ginc_s3 _ _ _ _ _ Hs E) HQ2 (le_n _))
      as (n & c & bsp & sp & HT).
    do 4 eexists. eapply DTa; [exact E | apply DP; exact HT].
Qed.

Definition Rel (orig cur : list nat) : Prop :=
  (forall i, S i < length cur -> nth i cur 0 <= nth i orig 0 + 1) /\
  (forall i, length cur <= S i -> nth i cur 0 <= nth i orig 0).

Lemma nth_bumpl l i : nth i (bumpl l) 0 = nth i l 0 + (if Nat.eqb (S i) (length l) then 1 else 0).
Proof.
  revert i. induction l as [|e l IH]; intros i; [destruct i; reflexivity|].
  destruct l as [|e' l].
  - destruct i as [|[|i]]; cbn; lia.
  - change (bumpl (e :: e' :: l)) with (e :: bumpl (e' :: l)).
    destruct i as [|i]; cbn [nth length]; [cbn; lia|]. rewrite IH. reflexivity.
Qed.

Lemma nth_app0 l i : nth i (l ++ [0]) 0 = nth i l 0.
Proof. revert i. induction l as [|e l IH]; intros [|i]; cbn; auto. destruct i; reflexivity. Qed.

Lemma Rel_ov orig l : Rel orig l -> Rel orig (bumpl l ++ [0]).
Proof.
  intros [R1 R2]. unfold Rel. rewrite length_app, length_bumpl. cbn [length]. split; intros i Hi; rewrite nth_app0, nth_bumpl.
  - destruct (Nat.eqb_spec (S i) (length l)).
    + specialize (R2 i ltac:(lia)). lia.
    + destruct (Nat.lt_ge_cases (S i) (length l)) as [H|H]; [specialize (R1 i H); lia|].
      rewrite nth_overflow by lia. lia.
  - destruct (Nat.eqb_spec (S i) (length l)); [lia|]. rewrite nth_overflow by lia. lia.
Qed.

Lemma Rel_inc orig bs s bs' s' d : s <= 3 -> ginc bs s = (bs', s', d) -> Rel orig (exs bs) -> Rel orig (exs bs').
Proof.
  intros Hs E R. destruct (ginc_exps bs s Hs _ _ _ E) as [[E1 _] | [E1 _]]; rewrite E1; [exact R|].
  apply Rel_ov, R.
Qed.

Lemma Rel_tl orig cur : Rel orig cur -> Rel (tl orig) (tl cur).
Proof.
  intros [R1 R2]. split; intros i Hi.
  - destruct cur as [|c cur]; cbn in Hi; [lia|]. specialize (R1 (S i) ltac:(cbn; lia)).
    destruct orig as [|o orig]; destruct i; cbn in *; lia.
  - destruct cur as [|c cur]; [destruct i; cbn; lia|]. cbn [length tl] in Hi |- *.
    specialize (R2 (S i) ltac:(cbn; lia)).
    destruct orig as [|o orig]; destruct i; cbn in *; lia.
Qed.

Lemma Rel_refl l : Rel l l.
Proof. split; intros; lia. Qed.

Lemma GPhi_rel a b bs s r : GPhi a b bs s r -> s <= 3 -> forall orig, Rel orig (exs bs) ->
  match r with
  | RE2 k x bs2 s2 => exists h, Rel (skipn (S h) orig) (exs bs2) /\ x <= nth h orig 0 + 1
  | RSp _ _ => True
  end.
Proof.
  induction 1 as [a b bs s bs' s' d r E H IH | a e bs s r H IH | a e bs s bs' s' d E | a | a | a | a r H IH];
    intros Hs orig R; auto.
  - apply IH; [eapply ginc_s3; eauto | eapply Rel_inc; eauto].
  - specialize (IH Hs (tl orig) (Rel_tl _ _ R)). destruct r as [k x bs2 s2|]; [|exact I].
    destruct IH as (h & R1 & R2). exists (S h). split.
    + destruct orig; [destruct h|]; exact R1.
    + destruct orig; cbn in *; [destruct h|]; auto.
  - exists 0. split.
    + apply (Rel_inc _ bs s bs' s' d Hs E). exact (Rel_tl _ _ R).
    + destruct R as [R1 R2]. destruct (ginc_exps bs s Hs _ _ _ E) as [[_ ->] | [_ Ed]].
      * cbn [addb]. destruct bs as [|b bs].
        -- specialize (R2 0 ltac:(cbn; lia)). cbn in R2. lia.
        -- specialize (R1 0 ltac:(cbn; lia)). cbn in R1. lia.
      * destruct bs as [|b bs]; subst d; cbn [addb].
        -- specialize (R2 0 ltac:(cbn; lia)). cbn in R2. lia.
        -- specialize (R1 0 ltac:(cbn; lia)). cbn in R1. lia.
  - apply IH; [lia|]. destruct R as [R1 R2]. split; intros i Hi; cbn in Hi; [lia|].
    destruct i as [|[|i]]; cbn; apply Nat.le_0_l.
Qed.

Lemma GPhi_val a b bs s r : GPhi a b bs s r -> s <= 3 ->
  match r with RE2 k x bs2 s2 => 2 * gval bs2 s2 + a <= gval bs s + k + 2 | RSp _ _ => True end.
Proof.
  induction 1 as [a b bs s bs' s' d r E H IH | a e bs s r H IH | a e bs s bs' s' d E | a | a | a | a r H IH];
    intros Hs; auto.
  - destruct (ginc_val bs s Hs _ _ _ E) as (V & S1 & _). specialize (IH S1). destruct r; [rewrite V in IH; lia | exact I].
  - specialize (IH Hs). destruct r; [cbn [gval]; lia | exact I].
  - destruct (ginc_val bs s Hs _ _ _ E) as (V & _). cbn [gval]. rewrite V. lia.
  - specialize (IH ltac:(lia)). destruct r; [cbn [gval] in *; lia | exact I].
Qed.

Definition v2 (q : nat) : nat := 2 ^ (q / 2).

Definition p2 (q : nat) : nat := 2 ^ S q.

Definition cst1 (q : nat) : nat := 1.

Definition u1 (l : nat) : nat := match l with 0 => 0 | S l' => 2 * w l' end.

Definition u2 (l : nat) : nat := match l with 0 => 0 | S l' => 2 ^ S l' end.

Lemma v2_mono : mono v2.
Proof. intros i j H. unfold v2. apply Nat.pow_le_mono_r; [lia|]. apply Nat.Div0.div_le_mono; lia. Qed.

Lemma p2_mono : mono p2.
Proof. intros i j H. unfold p2. apply Nat.pow_le_mono_r; lia. Qed.

Lemma cst1_mono : mono cst1.
Proof. intros i j H. unfold cst1. lia. Qed.

Lemma v2_le_w q : v2 q <= w q.
Proof. unfold v2, w. apply Nat.pow_le_mono_r; [lia|]. apply Nat.Div0.div_le_mono; lia. Qed.

Lemma cst1_le_w q : cst1 q <= w q.
Proof. unfold cst1, w. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma u1_mono : mono u1.
Proof. intros [|i] [|j] H; cbn [u1]; try lia. pose proof (w_mono i j ltac:(lia)). lia. Qed.

Lemma u1_w l q : 2 * l <= q -> u1 l <= w q.
Proof.
  destruct l as [|l]; intros H; cbn [u1]; [lia|].
  pose proof (w_lev1 l q ltac:(lia)) as W. unfold w at 1.
  rewrite <- Nat.pow_succ_r'.
  apply (Nat.le_trans _ (2 ^ S l)); [|exact W].
  apply Nat.pow_le_mono_r; [lia|].
  destruct l as [|l]; [cbn; lia|].
  assert ((S l + 1) / 2 <= (2 * S l) / 2) by (apply Nat.Div0.div_le_mono; lia).
  rewrite (Nat.mul_comm 2 (S l)), Nat.div_mul in H0 by lia. lia.
Qed.

Lemma u2_mono : mono u2.
Proof. intros [|i] [|j] H; cbn [u2]; try lia. apply Nat.pow_le_mono_r; lia. Qed.

Lemma u2_v2 l q : 2 * l <= q -> u2 l <= v2 q.
Proof.
  destruct l as [|l]; intros H; cbn [u2]; [lia|]. unfold v2. apply Nat.pow_le_mono_r; [lia|].
  replace (S l) with ((2 * S l) / 2) at 1 by (rewrite Nat.mul_comm, Nat.div_mul; lia).
  apply Nat.Div0.div_le_mono; lia.
Qed.

Lemma MO_u1 l es : MO u1 (S l) es = 2 * wpot w 1 0 l es.
Proof. revert l. induction es as [|e es IH]; intros l; cbn [MO wpot]; [reflexivity|]. rewrite IH. cbn [u1]. lia. Qed.

Lemma MO_u1_0 es : MO u1 0 es = 2 * wpot w 1 0 0 (tl es).
Proof. destruct es as [|e es]; cbn [MO tl]; [reflexivity|]. rewrite MO_u1. cbn [u1]. lia. Qed.

Lemma MO_u2 l es : MO u2 (S l) es = wpot p2 1 0 l es.
Proof. revert l. induction es as [|e es IH]; intros l; cbn [MO wpot]; [reflexivity|]. rewrite IH. cbn [u2]. unfold p2. lia. Qed.

Lemma MO_u2_0 es : MO u2 0 es = wpot p2 1 0 0 (tl es).
Proof. destruct es as [|e es]; cbn [MO tl]; [reflexivity|]. rewrite MO_u2. cbn [u2]. lia. Qed.

Lemma nth_le_MO h es : forall l, nth h es 0 <= MO cst1 l es.
Proof.
  revert h. induction es as [|e es IH]; intros h l; [destruct h; cbn; lia|].
  destruct h as [|h]; cbn [nth MO]; unfold cst1 at 1; [lia|]. specialize (IH h (S l)). lia.
Qed.

Lemma wpot_shift v al be f f' l : mono v -> f <= f' -> wpot v al be f l <= wpot v al be f' l.
Proof.
  intros Hv. revert f f'. induction l as [|e l IH]; intros f f' H; cbn [wpot]; [lia|].
  pose proof (Hv f f' H). specialize (IH (S f) (S f') ltac:(lia)).
  assert (v f * (al * e + be) <= v f' * (al * e + be)) by (apply Nat.mul_le_mono_r; lia). lia.
Qed.

Lemma wpot_drop v al be f h l : wpot v al be (f + h) (skipn h l) <= wpot v al be f l.
Proof.
  revert f l. induction h as [|h IH]; intros f l; [rewrite Nat.add_0_r; reflexivity|].
  destruct l as [|e l]; cbn [skipn wpot]; [lia|]. specialize (IH (S f) l).
  replace (f + S h) with (S f + h) by lia. lia.
Qed.

Lemma wpot_skipn_tl v h l : mono v -> wpot v 1 0 0 (skipn (S h) l) <= wpot v 1 0 0 (tl l).
Proof.
  intros Hv. replace (skipn (S h) l) with (skipn h (tl l)) by (destruct l; [destruct h|]; reflexivity).
  apply (Nat.le_trans _ (wpot v 1 0 (0 + h) (skipn h (tl l)))); [apply wpot_shift; [exact Hv | lia]|].
  apply wpot_drop.
Qed.

Lemma wpot_le_nth v l1 : mono v -> forall l2 f, (forall i, nth i l1 0 <= nth i l2 0 + 1) ->
  wpot v 1 0 f l1 <= wpot v 1 0 f l2 + vsum v f (length l1).
Proof.
  intros Hv. induction l1 as [|e1 l1 IH]; intros l2 f H; cbn [wpot length vsum]; [lia|].
  destruct l2 as [|e2 l2].
  - assert (H' : forall i, nth i l1 0 <= nth i [] 0 + 1) by (intros i; specialize (H (S i)); destruct i; cbn in *; lia).
    specialize (IH [] (S f) H'). cbn [wpot] in IH |- *.
    pose proof (H 0) as H0. cbn in H0. assert (v f * (1 * e1 + 0) <= v f) by nia. lia.
  - specialize (IH l2 (S f) (fun i => H (S i))). cbn [wpot].
    pose proof (H 0) as H0. cbn in H0. assert (v f * (1 * e1 + 0) <= v f * (1 * e2 + 0) + v f) by nia. lia.
Qed.

Lemma Rel_nth orig cur : Rel orig cur -> forall i, nth i cur 0 <= nth i orig 0 + 1.
Proof. intros [R1 R2] i. destruct (Nat.lt_ge_cases (S i) (length cur)); [apply R1 | specialize (R2 i)]; lia. Qed.

Lemma wpot_split v al be f l : wpot v al be f l = wpot v al 0 f l + be * vsum v f (length l).
Proof. revert f. induction l as [|e l IH]; intros f; cbn [wpot vsum length]; [lia|]. rewrite IH. ring. Qed.

Lemma wpot_scale2 v f l : wpot v 2 0 f l = 2 * wpot v 1 0 f l.
Proof. revert f. induction l as [|e l IH]; intros f; cbn [wpot]; [lia|]. rewrite IH. ring. Qed.

Lemma wpot_le_v v v' al be f l : (forall q, v q <= v' q) -> wpot v al be f l <= wpot v' al be f l.
Proof.
  intros H. revert f. induction l as [|e l IH]; intros f; cbn [wpot]; [lia|].
  specialize (IH (S f)). assert (v f * (al * e + be) <= v' f * (al * e + be)) by (apply Nat.mul_le_mono_r, H). lia.
Qed.

Lemma vsum_add v f m m' : vsum v f (m + m') = vsum v f m + vsum v (f + m) m'.
Proof. revert f. induction m as [|m IH]; intros f; cbn [vsum Nat.add]; [rewrite Nat.add_0_r; lia|]. rewrite IH. replace (S f + m) with (f + S m) by lia. lia. Qed.

Lemma vsum_mono_m v f m m' : m <= m' -> vsum v f m <= vsum v f m'.
Proof. intros H. replace m' with (m + (m' - m)) by lia. rewrite vsum_add. lia. Qed.

Lemma vsum_cst1 f m : vsum cst1 f m = m.
Proof. revert f. induction m as [|m IH]; intros f; cbn; [reflexivity|]. rewrite IH. unfold cst1. lia. Qed.

Lemma vsum_p2 f m : vsum p2 f m + 2 ^ S f = 2 ^ S (f + m).
Proof.
  revert f. induction m as [|m IH]; intros f; cbn [vsum]; [rewrite Nat.add_0_r; lia|].
  specialize (IH (S f)). replace (f + S m) with (S f + m) by lia. unfold p2 in *. rewrite (Nat.pow_succ_r' 2 (S f)) in IH. lia.
Qed.

Lemma wpot_p2_S f l : wpot p2 1 0 (S f) l = 2 * wpot p2 1 0 f l.
Proof. revert f. induction l as [|e l IH]; intros f; cbn [wpot]; [lia|]. rewrite IH. unfold p2. rewrite (Nat.pow_succ_r' 2 (S f)). ring. Qed.

Lemma qsum_p2 l : 2 * qsum l + 2 = 2 ^ S (length l) + wpot p2 1 0 0 l.
Proof.
  induction l as [|e l IH]; cbn [qsum length wpot]; [cbn; lia|]. rewrite wpot_p2_S.
  change (p2 0) with 2. rewrite (Nat.pow_succ_r' 2 (S (length l))). lia.
Qed.

Lemma wpot_zero v f l : Forall (fun e => e = 0) l -> wpot v 1 0 f l = 0.
Proof. intros H. revert f. induction H as [|e l He H IH]; intros f; cbn; [reflexivity|]. rewrite IH, He. lia. Qed.

Lemma Pot_top v al be ga Ps l : be <= ga -> length l <= Ps ->
  Pot v al be ga Ps 0 l <= wpot v al 0 0 l + ga * vsum v 0 Ps.
Proof.
  intros Hb Hl. unfold Pot. rewrite wpot_split. cbn [Nat.add].
  pose proof (vsum_add v 0 (length l) (Ps - length l)) as E. replace (length l + (Ps - length l)) with Ps in E by lia.
  cbn [Nat.add] in E. rewrite E.
  assert (be * vsum v 0 (length l) <= ga * vsum v 0 (length l)) by (apply Nat.mul_le_mono_r; lia).
  rewrite Nat.mul_add_distr_l. lia.
Qed.

Definition Ws (P : nat) : nat := vsum w 0 P.

Definition V2s (P : nat) : nat := vsum v2 0 P.

Definition Pf (k : nat) : nat := Nat.max 12 (k + 3).

Definition Af (k : nat) : nat := 5 * Ws (Pf k) + 6 * w (Pf k) + 2 * Ws k.

Definition Bf (k : nat) : nat := Af k + 5 * V2s (Pf k) + 6 * v2 (Pf k) + 2 ^ (k + 1).

Definition Xf (k : nat) : nat := Af k + 5 * Pf k + 7.

Definition Costf (k : nat) : nat := 2 * Xf k + 2 + 2 * Af k + 11 * Ws (Pf k) + 13 * w (Pf k).

Definition Nlo (k : nat) : nat := 2 ^ (k + 3) - 8 * 2 ^ ((Pf k + 3) / 2).

Definition Nstar : nat := 17705.

Lemma Pf_mono k k' : k <= k' -> Pf k <= Pf k'.
Proof. unfold Pf. lia. Qed.

Lemma Ws_mono P P' : P <= P' -> Ws P <= Ws P'.
Proof. apply vsum_mono_m. Qed.

Lemma V2s_mono P P' : P <= P' -> V2s P <= V2s P'.
Proof. apply vsum_mono_m. Qed.

Lemma Af_mono k k' : k <= k' -> Af k <= Af k'.
Proof.
  intros H. unfold Af. pose proof (Pf_mono _ _ H).
  pose proof (Ws_mono _ _ H0). pose proof (w_mono _ _ H0). pose proof (Ws_mono _ _ H). lia.
Qed.

Lemma w_SS q : w (S (S q)) = 2 * w q.
Proof.
  unfold w. replace (S (S q) + 1) with ((q + 1) + 1 * 2) by lia. rewrite Nat.div_add by lia.
  rewrite Nat.pow_add_r. cbn. lia.
Qed.

Lemma v2_SS q : v2 (S (S q)) = 2 * v2 q.
Proof.
  unfold v2. replace (S (S q)) with (q + 1 * 2) by lia. rewrite Nat.div_add by lia.
  rewrite Nat.pow_add_r. cbn. lia.
Qed.

Lemma vsum_SS_w f m : vsum w (S (S f)) m = 2 * vsum w f m.
Proof. revert f. induction m as [|m IH]; intros f; cbn [vsum]; [lia|]. rewrite w_SS, IH. lia. Qed.

Lemma vsum_SS_v2 f m : vsum v2 (S (S f)) m = 2 * vsum v2 f m.
Proof. revert f. induction m as [|m IH]; intros f; cbn [vsum]; [lia|]. rewrite v2_SS, IH. lia. Qed.

Lemma Ws_SS P : Ws (S (S P)) = 2 * Ws P + 3.
Proof. unfold Ws. cbn [vsum]. rewrite vsum_SS_w. cbn. lia. Qed.

Lemma V2s_SS P : V2s (S (S P)) = 2 * V2s P + 2.
Proof. unfold V2s. cbn [vsum]. rewrite vsum_SS_v2. cbn. lia. Qed.

Lemma Pf_big k : 9 <= k -> Pf k = k + 3.
Proof. unfold Pf. lia. Qed.

Lemma Af_SS k : 9 <= k -> Af (S (S k)) = 2 * Af k + 21.
Proof.
  intros H. unfold Af. rewrite !Pf_big by lia.
  replace (S (S k) + 3) with (S (S (k + 3))) by lia. rewrite !Ws_SS, w_SS. lia.
Qed.

Definition gB (k : nat) : nat := Af k + 5 * V2s (k + 3) + 6 * v2 (k + 3).

Lemma gB_SS k : 9 <= k -> gB (S (S k)) = 2 * gB k + 31.
Proof.
  intros H. unfold gB. rewrite Af_SS by lia.
  replace (S (S k) + 3) with (S (S (k + 3))) by lia. rewrite V2s_SS, v2_SS. lia.
Qed.

Lemma gB_all m : gB (10 + 2 * m) + 31 < 7 * 2 ^ (10 + 2 * m) /\ gB (11 + 2 * m) + 31 < 7 * 2 ^ (11 + 2 * m).
Proof.
  induction m as [|m [IH1 IH2]].
  - split; apply Nat.ltb_lt; vm_compute; reflexivity.
  - replace (10 + 2 * S m) with (S (S (10 + 2 * m))) by lia.
    replace (11 + 2 * S m) with (S (S (11 + 2 * m))) by lia.
    rewrite !gB_SS by lia. rewrite !(Nat.pow_succ_r' 2 (S _)), !Nat.pow_succ_r'. lia.
Qed.

Lemma gB_ge k : 10 <= k -> gB k + 31 < 7 * 2 ^ k.
Proof.
  intros H. destruct (Nat.Even_or_Odd (k - 10)) as [[m Hm] | [m Hm]].
  - replace k with (10 + 2 * m) by lia. exact (proj1 (gB_all m)).
  - replace k with (11 + 2 * m) by lia. exact (proj2 (gB_all m)).
Qed.

Lemma N1 k : 7 * 2 ^ k + Bf k < 2 ^ (Pf k + 1).
Proof.
  destruct (le_lt_dec k 11) as [Hk|Hk].
  - assert (H : forallb (fun k => 7 * 2 ^ k + Bf k <? 2 ^ (Pf k + 1)) (seq 0 12) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in H. specialize (H k (proj2 (in_seq 12 0 k) ltac:(lia))). apply Nat.ltb_lt, H.
  - pose proof (gB_ge k ltac:(lia)) as G. unfold Bf. fold (gB k) in *.
    unfold gB in G. rewrite Pf_big in * by lia. unfold gB in *.
    replace (k + 3 + 1) with (k + 4) by lia. rewrite (Nat.pow_add_r 2 k 4), (Nat.pow_add_r 2 k 1).
    cbn [Nat.pow]. lia.
Qed.

Lemma Costf_SS k : 9 <= k -> Costf (S (S k)) + 10 * (k + 3) = 2 * Costf k + 121.
Proof.
  intros H. unfold Costf, Xf. rewrite Af_SS by lia. rewrite !Pf_big by lia.
  replace (S (S k) + 3) with (S (S (k + 3))) by lia. rewrite Ws_SS, w_SS. generalize (Af k) (Ws (k + 3)) (w (k + 3)). intros. lia.
Qed.

Lemma Nlo_SS k : 9 <= k -> Nlo (S (S k)) = 4 * 2 ^ (k + 3) - 16 * 2 ^ ((k + 6) / 2) /\
  Nlo k = 2 ^ (k + 3) - 8 * 2 ^ ((k + 6) / 2).
Proof.
  intros H. unfold Nlo. rewrite !Pf_big by lia. split.
  - replace ((S (S k) + 3 + 3) / 2) with ((k + 6) / 2 + 1)
      by (replace (S (S k) + 3 + 3) with ((k + 6) + 1 * 2) by lia; rewrite Nat.div_add by lia; lia).
    replace (S (S k) + 3) with (k + 3 + 2) by lia.
    rewrite (Nat.pow_add_r 2 (k + 3) 2), (Nat.pow_add_r 2 ((k + 6) / 2) 1).
    generalize (2 ^ (k + 3)) (2 ^ ((k + 6) / 2)). intros. cbn. lia.
  - replace (k + 3 + 3) with (k + 6) by lia. reflexivity.
Qed.

Lemma D_all m : Costf (12 + 2 * m) + 123 <= Nlo (12 + 2 * m) /\ Costf (13 + 2 * m) + 123 <= Nlo (13 + 2 * m).
Proof.
  induction m as [|m [IH1 IH2]].
  - split; apply Nat.leb_le; vm_compute; reflexivity.
  - replace (12 + 2 * S m) with (S (S (12 + 2 * m))) by lia.
    replace (13 + 2 * S m) with (S (S (13 + 2 * m))) by lia.
    pose proof (Costf_SS (12 + 2 * m) ltac:(lia)). pose proof (Costf_SS (13 + 2 * m) ltac:(lia)).
    destruct (Nlo_SS (12 + 2 * m) ltac:(lia)) as [E1 E2]. destruct (Nlo_SS (13 + 2 * m) ltac:(lia)) as [E3 E4].
    rewrite E1, E3. rewrite E2 in IH1. rewrite E4 in IH2. lia.
Qed.

Lemma N2 k : Costf k + 2 <= Nstar \/ Costf k + 2 <= Nlo k.
Proof.
  destruct (le_lt_dec k 11) as [Hk|Hk].
  - left. assert (H : forallb (fun k => Costf k + 2 <=? Nstar) (seq 0 12) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in H. specialize (H k (proj2 (in_seq 12 0 k) ltac:(lia))). apply Nat.leb_le, H.
  - right. destruct (Nat.Even_or_Odd (k - 12)) as [[m Hm] | [m Hm]].
    + replace k with (12 + 2 * m) by lia. pose proof (proj1 (D_all m)). lia.
    + replace k with (13 + 2 * m) by lia. pose proof (proj2 (D_all m)). lia.
Qed.

Lemma Nstar_ge : 15 <= Nstar.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Ltac opq t := let x := fresh "o" in set (x := t) in *; clearbody x.

Definition Mw (bs : blks) : nat := wpot w 1 0 0 (exs bs).

Definition M2 (bs : blks) : nat := wpot p2 1 0 0 (exs bs).

Definition Inv (k N : nat) (y : word) : Prop :=
  Nstar <= N /\ Nlo k <= N /\
  ((exists x bs s, y = p11 x (gw bs s) /\ s <= 3 /\ length bs <= k /\
      Mw bs <= Af k /\ M2 bs <= Bf k /\ x <= Xf k)
   \/ y = t1 \/ y = p01 1 t1 \/ y = p10 (p00 t2)).

Lemma next_inv k N n c bsp sp r :
  GPhi (1 + n) (N + c - n) bsp sp r -> sp <= 3 -> n + 2 <= N -> Nstar <= N -> Nlo k <= N ->
  MO u1 0 (exs bsp) <= Af k + 5 * Ws (Pf k) + 6 * w (Pf k) ->
  MO u2 0 (exs bsp) <= Af k + 5 * V2s (Pf k) + 6 * v2 (Pf k) ->
  MO cst1 0 (exs bsp) + 1 <= Xf k ->
  2 * length bsp <= Pf k + 3 ->
  exists k', Inv k' (S (rk r)) (ry r).
Proof.
  intros HG Hs Hn HN HL H1 H2 H3 H4.
  pose proof (GPhi_rk _ _ _ _ _ HG) as Hrk.
  pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hr.
  pose proof (GPhi_rel _ _ _ _ _ HG Hs (exs bsp) (Rel_refl _)) as HR.
  pose proof (GPhi_val _ _ _ _ _ HG Hs) as HV.
  destruct r as [kk x bs2 s2 | kk y]; cbn [rk ry] in *.
  - destruct HR as (h & R1 & R2).
    exists (Nat.max k (length bs2)).
    assert (Hk : k <= Nat.max k (length bs2)) by lia.
    assert (Hk2 : length bs2 <= Nat.max k (length bs2)) by lia.
    set (k' := Nat.max k (length bs2)) in *.
    split; [lia|]. split.
    + destruct (le_lt_dec (length bs2) k) as [Hle|Hgt].
      * replace k' with k by lia. lia.
      * replace k' with (length bs2) by lia.
        pose proof (gval_lb bs2 s2). pose proof (gval_ub bsp sp Hs).
        assert (2 ^ length bsp <= 2 ^ ((Pf (length bs2) + 3) / 2)).
        { apply Nat.pow_le_mono_r; [lia|]. pose proof (Pf_mono k (length bs2) ltac:(lia)).
          apply Nat.div_le_lower_bound; lia. }
        unfold Nlo. rewrite Nat.pow_add_r.
        generalize dependent (2 ^ length bs2). generalize dependent (2 ^ length bsp).
        generalize dependent (2 ^ ((Pf (length bs2) + 3) / 2)). intros. cbn [Nat.pow] in *. lia.
    + left. exists x, bs2, s2. split; [reflexivity|]. split; [exact Hr|]. split; [lia|].
      pose proof (Pf_mono _ _ Hk) as HPf.
      split; [|split].
      * unfold Mw.
        pose proof (wpot_le_nth w (exs bs2) w_mono _ 0 (Rel_nth _ _ R1)) as A1. rewrite length_exs in A1.
        pose proof (wpot_skipn_tl w h (exs bsp) w_mono) as A2.
        rewrite MO_u1_0 in H1.
        pose proof (Ws_mono _ _ Hk2). pose proof (Ws_mono _ _ Hk). pose proof (Ws_mono _ _ HPf).
        pose proof (w_mono _ _ HPf).
        unfold Af in *. fold (Ws (length bs2)) in A1.
        generalize dependent (wpot w 1 0 0 (exs bs2)). generalize dependent (wpot w 1 0 0 (skipn (S h) (exs bsp))).
        generalize dependent (wpot w 1 0 0 (tl (exs bsp))). intros. lia.
      * unfold M2.
        pose proof (wpot_le_nth p2 (exs bs2) p2_mono _ 0 (Rel_nth _ _ R1)) as A1. rewrite length_exs in A1.
        pose proof (wpot_skipn_tl p2 h (exs bsp) p2_mono) as A2.
        rewrite MO_u2_0 in H2.
        pose proof (vsum_p2 0 (length bs2)) as A3. cbn [Nat.add] in A3.
        assert (2 ^ S (length bs2) <= 2 ^ (k' + 1)) by (apply Nat.pow_le_mono_r; lia).
        pose proof (Af_mono _ _ Hk). pose proof (V2s_mono _ _ HPf). pose proof (v2_mono _ _ HPf).
        unfold Bf.
        generalize dependent (wpot p2 1 0 0 (exs bs2)). generalize dependent (wpot p2 1 0 0 (skipn (S h) (exs bsp))).
        generalize dependent (wpot p2 1 0 0 (tl (exs bsp))). intros. lia.
      * pose proof (nth_le_MO h (exs bsp) 0).
        assert (Xf k <= Xf k') by (unfold Xf; pose proof (Af_mono _ _ Hk); lia). lia.
  - exists k. split; [lia|]. split; [lia|]. right. exact Hr.
Qed.

Lemma inv_step k N y : Inv k N y -> exists kk y', Phi 1 N y kk y' /\ exists k', Inv k' (S kk) y'.
Proof.
  intros (HN & HL & Hy).
  pose proof (N2 k) as HC.
  destruct Hy as [(x & bs & s & -> & Hs & Hk & HM & HM2 & Hx) | Hsp].
  - set (Ps := Pf k).
    set (Q0 := Qp 0 bs s 0 - 3 * 2 ^ length bs).
    assert (HQ0 : 4 * 2 ^ length bs <= Qp 0 bs s 0).
    { unfold Qp. rewrite Nat.pow_0_r. pose proof (gval_lb bs s). lia. }
    assert (HQ : QI Q0 0 bs s 0).
    { unfold QI, Q0. cbn [Nat.add]. clear - HQ0. lia. }
    assert (HP : Q0 < 2 ^ (Ps + 1)).
    { pose proof (N1 k) as N1k. unfold Q0, Qp. rewrite Nat.pow_0_r, Nat.mul_1_l.
      pose proof (qsum_p2 (exs bs)) as QP. rewrite length_exs in QP. pose proof (gval_ub bs s Hs).
      assert (2 ^ length bs <= 2 ^ k) by (apply Nat.pow_le_mono_r; lia). unfold M2 in HM2.
      rewrite Nat.pow_succ_r' in QP. fold Ps in N1k. lia. }
    destruct (DigT_exists Q0 (Q0 + 1) 0 bs s Hs HQ ltac:(lia)) as (n0 & c0 & bsp & sp & HT).
    pose proof (DP x _ _ _ _ _ _ HT) as HD.
    set (n := 2 * x + 2 + n0) in *. set (c := S x + c0) in *.
    pose proof (proj1 (Dig_cost Q0 Ps HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hcost.
    rewrite Nat.pow_0_r, !Nat.mul_1_l in Hcost.
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [Nat.add] in HPs.
    assert (HPs' : length (exs bs) <= Ps) by (rewrite length_exs; exact HPs).
    pose proof (Pot_top w 2 8 11 Ps (exs bs) ltac:(lia) HPs') as PT. rewrite wpot_scale2 in PT.
    assert (Hn : n + 2 <= N).
    { unfold Costf in HC. fold Ps in HC. unfold Mw in HM. fold (Ws Ps) in PT.
      opq (w Ps). opq (Ws Ps). opq (Pot w 2 8 11 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)). lia. }
    pose proof (proj1 Dig_sp _ _ _ _ _ _ _ HD) as Hsp.
    destruct (gcount (Psi bsp sp (N + c - n)) bsp sp (1 + n) (N + c - n) Hsp ltac:(lia) (le_n _)) as (r & HG).
    exists (rk r), (ry r). split; [exact (epoch_ord N x bs s n c bsp sp r Hs HD Hn HG)|].
    apply (next_inv k N n c bsp sp r HG Hsp Hn HN HL).
    + pose proof (proj1 (Dig_mass u1 w Q0 Ps w_mono u1_mono u1_w HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hm.
      cbn [pu] in Hm. pose proof (Pot_top w 1 3 5 Ps (exs bs) ltac:(lia) HPs') as PT1.
      unfold Mw in HM. fold Ps. fold (Ws Ps) in PT1.
      opq (w Ps). opq (Ws Ps). opq (Pot w 1 3 5 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)). opq (MO u1 0 (exs bsp)). lia.
    + pose proof (proj1 (Dig_mass u2 v2 Q0 Ps v2_mono u2_mono u2_v2 HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hm.
      cbn [pu] in Hm. pose proof (Pot_top v2 1 3 5 Ps (exs bs) ltac:(lia) HPs') as PT1.
      pose proof (wpot_le_v v2 w 1 0 0 (exs bs) v2_le_w).
      unfold Mw in HM. fold Ps. fold (V2s Ps) in PT1.
      opq (v2 Ps). opq (V2s Ps). opq (Pot v2 1 3 5 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)).
      opq (wpot v2 1 0 0 (exs bs)). opq (MO u2 0 (exs bsp)). lia.
    + pose proof (proj1 (Dig_mass cst1 cst1 Q0 Ps cst1_mono cst1_mono ltac:(intros; unfold cst1; lia) HP)
        _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hm.
      cbn [pu] in Hm. pose proof (Pot_top cst1 1 3 5 Ps (exs bs) ltac:(lia) HPs') as PT1.
      rewrite vsum_cst1 in PT1. pose proof (wpot_le_v cst1 w 1 0 0 (exs bs) cst1_le_w).
      unfold Mw in HM. unfold Xf. fold Ps. unfold cst1 at 3 in Hm.
      opq (Pot cst1 1 3 5 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)). opq (wpot cst1 1 0 0 (exs bs)).
      opq (MO cst1 0 (exs bsp)). lia.
    + pose proof (proj1 (Dig_len Q0 Ps HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ). fold Ps. lia.
  - destruct (DigE_ex y Hsp) as (n & c & bsp & sp & HE).
    destruct (DigE_props _ _ _ _ _ HE) as (Hn13 & Hc5 & Hb1 & Hs3 & Hz).
    assert (Hn : n + 2 <= N) by (pose proof Nstar_ge; lia).
    destruct (gcount (Psi bsp sp (N + c - n)) bsp sp (1 + n) (N + c - n) Hs3 ltac:(lia) (le_n _)) as (r & HG).
    exists (rk r), (ry r). split; [exact (epoch_spec N y n c bsp sp r HE Hn HG)|].
    apply (next_inv k N n c bsp sp r HG Hs3 Hn HN HL); rewrite ?(MO_zero _ _ _ Hz); unfold Xf, Pf; lia.
Qed.

Fixpoint orbit (f n N : nat) (y : word) : option (nat * word) :=
  match n with
  | O => Some (N, y)
  | S n => match phif f 1 N y with Some (k, y') => orbit f n (S k) y' | None => None end
  end.

Lemma orbit_sound f n : forall N y N' y', orbit f n N y = Some (N', y') -> K N y -->* K N' y'.
Proof.
  induction n as [|n IH]; intros N y N' y' H; cbn [orbit] in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (phif f 1 N y) as [[k y1]|] eqn:E; [|discriminate].
    eapply evstep_trans; [apply progress_evstep, epoch_tm, (proj2 (model_sound f) _ _ _ _ _ E) | exact (IH _ _ _ _ H)].
Qed.

Definition B694 : blks := [(false, 17); (true, 1); (true, 1); (true, 1); (true, 1);
  (false, 1); (false, 1); (false, 1); (true, 1); (false, 0)].

Definition Y694 : word := p11 7 (gw B694 0).

Lemma fin694 : orbit 100000 691 8 t2 = Some (17713, Y694).
Proof. vm_compute. reflexivity. Qed.

Lemma inv694 : Inv 10 17713 Y694.
Proof.
  unfold Inv. split; [apply Nat.leb_le; vm_compute; reflexivity|]. split; [apply Nat.leb_le; vm_compute; reflexivity|].
  left. exists 7, B694, 0. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|].
  split; [|split]; [apply Nat.leb_le; vm_compute; reflexivity | apply Nat.leb_le; vm_compute; reflexivity |].
  apply Nat.leb_le; vm_compute; reflexivity.
Qed.

Lemma nonhalt_from N0 y0 (P : nat -> word -> Prop) :
  c0 -->* K N0 y0 -> P N0 y0 ->
  (forall N y, P N y -> exists k y', Phi 1 N y k y' /\ P (S k) y') ->
  ~ halts tm c0.
Proof.
  intros H0 HP0 Hstep.
  eapply multistep_nonhalt. { exact H0. }
  apply (progress_nonhalt_cond tm (nat * word) (N0, y0) (fun i => K (fst i) (snd i))
           (fun i => P (fst i) (snd i))); [| exact HP0].
  intros [N y] HP. cbn in HP.
  destruct (Hstep N y HP) as (k & y' & HPhi & HP').
  exists (S k, y'). split; [apply epoch_tm, HPhi | exact HP'].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply (nonhalt_from 17713 Y694 (fun N y => exists k, Inv k N y)).
  - eapply evstep_trans; [exact init | exact (orbit_sound _ _ _ _ _ _ fin694)].
  - exists 10. exact inv694.
  - intros N y [k Hk]. destruct (inv_step k N y Hk) as (kk & y' & H1 & H2). exists kk, y'. split; [exact H1 | exact H2].
Qed.

End TM4.
Print Assumptions TM4.nonhalt.

Require Import ZifyNat Lia.
Require Import ZArith.

Module TM5.
Import BusyCoq.Individual62.

Import ZifyNat Lia.

Import ZArith.

Import String.

Open Scope list.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma BR k: forall l r, l {{B}}> [1]^^k *> r -->* [1]^^k *> l {{B}}> r.
Proof. es. Qed.

Lemma SW k: forall l r, [1;0]^^k *> l <{{C}} r -->* l <{{C}} [0;1]^^k *> r.
Proof. es. Qed.

Lemma TT j: forall l r, [1;1;1]^^j *> l <{{C}} r -->* l <{{C}} [0;1;1]^^j *> r.
Proof. es. Qed.

Lemma PS b: forall l r, [1;1;0] *> l {{B}}> [1;0]^^b *> r -->* [1;1] *> [0;1]^^b *> [0] *> l {{B}}> r.
Proof. es. Qed.

Lemma RND2 q j: forall l r,
  l {{C}}> [0;0] *> [1;0]^^(q+3) *> [1;1;1]^^j *> [1;1;0] *> r -->+
  [1;0;1;0] *> l {{C}}> [0;0] *> [1;0]^^(q+1) *> [1;1;0]^^j *> [1;1;1] *> r.
Proof. es. Qed.

Lemma RND1 q j: forall l r,
  l {{C}}> [0;0] *> [1;0]^^(q+3) *> [1;1;1]^^j *> [1;1;1;1;0] *> r -->+
  [1;0;1;0] *> l {{C}}> [0;0] *> [1;0]^^(q+1) *> [1;1;1;1] *> [0;1;1]^^j *> [1] *> r.
Proof. es. Qed.

Lemma RND0 q j: forall l r,
  l {{C}}> [0;0] *> [1;0]^^(q+3) *> [1;1;1]^^j *> [1;1;1;0] *> r -->+
  [1;0;1;0] *> l {{C}}> [0;0] *> [1;0]^^q *> [1;1;1;1;1] *> [0;1;1]^^j *> [1] *> r.
Proof. es. Qed.

Lemma PUSH k: forall l r,
  l {{C}}> [0;0] *> [1;0]^^2 *> [1;1;0]^^k *> [1;1;1] *> r -->+
  [1;0;0]^^k *> [1;0;1;0] *> l {{C}}> [0;0] *> [1;0] *> [1] *> r.
Proof. es. Qed.

Lemma BITE1 p: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;0] *> [1;1] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+3) *> [1] *> r.
Proof. es. Qed.

Lemma BITE0 p j: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;1;1]^^j *> [1;1;0] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+2) *> [1] *> [0;1;1]^^j *> [1] *> r.
Proof. es. Qed.

Lemma BITE0c p j: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;1;1]^^j *> [1;1;1;1;1;1;0] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+2) *> [1;1;1] *> [1;1;0]^^j *> [1;1;1] *> r.
Proof. es. Qed.

Lemma BITE0c3 p: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;1;1;0;0] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+1) *> [1;1;1;1;1;1] *> r.
Proof. es. Qed.

Definition bitc (v : nat) : sym := if Nat.odd v then 0 else 1.

Fixpoint dg (L v : nat) : list sym :=
  match L with
  | O => []
  | S L' => [1;1;bitc v] ++ dg L' (Nat.div2 v)
  end.

Definition zone (r L v : nat) : list sym := [1]^^r ++ dg L v ++ [1;1;1].

Lemma bitc_even v: bitc (2*v) = 1.
Proof. unfold bitc. rewrite Nat.odd_mul. reflexivity. Qed.

Lemma bitc_odd v: bitc (2*v+1) = 0.
Proof. unfold bitc. rewrite Nat.add_1_r, Nat.odd_succ, Nat.even_mul. reflexivity. Qed.

Lemma div2_even v: Nat.div2 (2*v) = v.
Proof. apply Nat.div2_double. Qed.

Lemma div2_odd v: Nat.div2 (2*v+1) = v.
Proof. rewrite Nat.add_1_r. apply Nat.div2_succ_double. Qed.

Lemma dg_even L v: dg (S L) (2*v) = [1;1;1] ++ dg L v.
Proof. cbn [dg]. rewrite bitc_even, div2_even. reflexivity. Qed.

Lemma dg_odd L v: dg (S L) (2*v+1) = [1;1;0] ++ dg L v.
Proof. cbn [dg]. rewrite bitc_odd, div2_odd. reflexivity. Qed.

Lemma pow_pos P: 1 <= 2^P.
Proof. pose proof (Nat.pow_nonzero 2 P). lia. Qed.

Lemma dg_zero L: dg L 0 = [1;1;1]^^L.
Proof.
  induction L as [|L IH]; [reflexivity|].
  change (dg (S L) 0) with ([1;1;1] ++ dg L 0). rewrite IH. reflexivity.
Qed.

Lemma dg_full L: dg L (2^L - 1) = [1;1;0]^^L.
Proof.
  induction L as [|L IH]; [reflexivity|].
  replace (2^(S L) - 1) with (2*(2^L-1)+1) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos L); lia).
  rewrite dg_odd, IH. reflexivity.
Qed.

Lemma dg_low b L o: dg (b + S L) (2^b*(2*o+1)) = [1;1;1]^^b ++ [1;1;0] ++ dg L o.
Proof.
  induction b as [|b IH].
  - replace (2^0*(2*o+1)) with (2*o+1) by (cbn; lia). apply dg_odd.
  - replace (2^(S b)*(2*o+1)) with (2*(2^b*(2*o+1))) by (rewrite Nat.pow_succ_r'; lia).
    cbn [Nat.add]. rewrite dg_even, IH. reflexivity.
Qed.

Lemma dg_lowones k L o: dg (k + S L) (2^k - 1 + 2^(S k)*o) = [1;1;0]^^k ++ [1;1;1] ++ dg L o.
Proof.
  induction k as [|k IH].
  - replace (2^0 - 1 + 2^1*o) with (2*o) by (cbn; lia). apply dg_even.
  - replace (2^(S k) - 1 + 2^(S (S k))*o) with (2*(2^k - 1 + 2^(S k)*o)+1)
      by (rewrite !Nat.pow_succ_r'; pose proof (pow_pos k); lia).
    cbn [Nat.add]. rewrite dg_odd, IH. reflexivity.
Qed.

Lemma lowbit (x:nat): x <> 0%nat -> exists P o, x = 2^P*(2*o+1).
Proof.
  induction x as [x IH] using lt_wf_ind. intros Hx.
  destruct (Nat.Even_or_Odd x) as [[x' Hx']|[x' Hx']]; subst x.
  - destruct (IH x') as [P [o Ho]]; [lia|lia|].
    exists (S P), o. rewrite Nat.pow_succ_r'. lia.
  - exists 0%nat, x'. cbn. lia.
Qed.

Lemma lowbit_lt b o L: 2^b*(2*o+1) < 2^L -> b < L /\ o < 2^(L-b-1).
Proof.
  intros H.
  assert (Hb: b < L).
  { apply (Nat.pow_lt_mono_r_iff 2); [lia|]. pose proof (pow_pos b). nia. }
  split; [exact Hb|].
  replace L with (b + S (L-b-1)) in H by lia.
  rewrite Nat.pow_add_r, Nat.pow_succ_r' in H.
  pose proof (pow_pos b). nia.
Qed.

Lemma ones_comm b: [1;1] ++ [1;1;1]^^b = [1;1;1]^^b ++ [1;1].
Proof. induction b as [|b IH]; [reflexivity|]. cbn [lpow]. rewrite <-List.app_assoc, <-IH. reflexivity. Qed.

Lemma one_comm b: [1] ++ [1;1;1]^^b = [1;1;1]^^b ++ [1].
Proof. induction b as [|b IH]; [reflexivity|]. cbn [lpow]. rewrite <-List.app_assoc, <-IH. reflexivity. Qed.

Lemma sh110 b: [1;1] ++ [0;1;1]^^b = [1;1;0]^^b ++ [1;1].
Proof. induction b as [|b IH]; [reflexivity|]. cbn [lpow]. rewrite <-List.app_assoc, <-IH. reflexivity. Qed.

Lemma S_ones2 b s: [1;1] *> [1;1;1]^^b *> s = [1;1;1]^^b *> [1;1] *> s.
Proof. rewrite <-!Str_app_assoc, ones_comm. reflexivity. Qed.

Lemma S_ones1 b s: [1] *> [1;1;1]^^b *> s = [1;1;1]^^b *> [1] *> s.
Proof. rewrite <-!Str_app_assoc, one_comm. reflexivity. Qed.

Lemma S_sh110 b s: [1;1] *> [0;1;1]^^b *> s = [1;1;0]^^b *> [1;1] *> s.
Proof. rewrite <-!Str_app_assoc, sh110. reflexivity. Qed.

Definition RT (l : side) (q : nat) (Z : list sym) : Q * tape := l {{C}}> [0;0] *> [1;0]^^q *> Z *> const 0.

Lemma R1z l q L v: 1 <= v -> v < 2^L ->
  RT l (q+3) (zone 0 L v) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 0 L (v-1)).
Proof.
  intros H1 H2. destruct (lowbit v) as [b [o ->]]; [lia|].
  destruct (lowbit_lt _ _ _ H2) as [Hb Ho].
  remember (L-b-1) as L'. replace L with (b + S L') by lia.
  replace (2^b*(2*o+1) - 1) with (2^b - 1 + 2^(S b)*o) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos b); nia).
  unfold RT, zone. rewrite dg_low, dg_lowones. cbn [lpow app].
  rewrite !Str_app_assoc. apply RND2.
Qed.

Lemma R1t l q L v: 1 <= v -> v < 2^L ->
  RT l (q+3) (zone 2 L v) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 2 L (v-1)).
Proof.
  intros H1 H2. destruct (lowbit v) as [b [o ->]]; [lia|].
  destruct (lowbit_lt _ _ _ H2) as [Hb Ho].
  remember (L-b-1) as L'. replace L with (b + S L') by lia.
  replace (2^b*(2*o+1) - 1) with (2^b - 1 + 2^(S b)*o) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos b); nia).
  unfold RT, zone. rewrite dg_low, dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^2) with [1;1]. rewrite S_ones2.
  change ([1;1] *> [1;1;0] *> ?Y) with ([1;1;1;1;0] *> Y).
  eapply progress_evstep_trans. 1: apply RND1. apply evstep_refl'.
  change ([1;1;1;1] *> ?X) with ([1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

Lemma R2r l q L v: 1 <= v -> v < 2^L ->
  RT l (q+3) (zone 1 L v) -->+ RT ([1;0;1;0] *> l) q (zone 0 (S L) (2*v-2)).
Proof.
  intros H1 H2. destruct (lowbit v) as [b [o ->]]; [lia|].
  destruct (lowbit_lt _ _ _ H2) as [Hb Ho].
  remember (L-b-1) as L'. replace L with (b + S L') by lia.
  replace (2*(2^b*(2*o+1))-2) with (2*(2^b - 1 + 2^(S b)*o)) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos b); nia).
  unfold RT, zone. rewrite dg_low, dg_even, dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^1) with [1]. rewrite S_ones1.
  change ([1] *> [1;1;0] *> ?Y) with ([1;1;1;0] *> Y).
  eapply progress_evstep_trans. 1: apply RND0. apply evstep_refl'.
  change ([1;1;1;1;1] *> ?X) with ([1;1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

Lemma O2r l q L:
  RT l (q+3) (zone 2 L 0) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 0 (S L) (2^(S L)-1)).
Proof.
  unfold RT, zone. rewrite dg_zero, dg_full. rewrite !Str_app_assoc.
  change ([1]^^2) with [1;1]. change ([1]^^0 *> ?X) with X.
  assert (E: [1;1] *> [1;1;1]^^L *> [1;1;1] *> const 0 = [1;1;1]^^(S L) *> [1;1;0] *> const 0).
  { rewrite S_ones2, lpow_S, Str_app_assoc, <-lpow_shift'. f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. apply RND2.
Qed.

Lemma O1r l q L:
  RT l (q+3) (zone 1 L 0) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 2 L (2^L-1)).
Proof.
  unfold RT, zone. rewrite dg_zero, dg_full. rewrite !Str_app_assoc.
  change ([1]^^2) with [1;1]. change ([1]^^1) with [1].
  assert (E: [1] *> [1;1;1]^^L *> [1;1;1] *> const 0 = [1;1;1]^^L *> [1;1;1;1;0] *> const 0).
  { rewrite S_ones1. f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. eapply progress_evstep_trans. 1: apply RND1. apply evstep_refl'.
  change ([1;1;1;1] *> ?X) with ([1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

Lemma O0r l q L:
  RT l (q+3) (zone 0 L 0) -->+ RT ([1;0;1;0] *> l) q (zone 0 (S L) (2^(S L)-2)).
Proof.
  replace (2^(S L)-2) with (2*(2^L-1)) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos L); lia).
  unfold RT, zone. rewrite dg_zero, dg_even, dg_full. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X.
  assert (E: [1;1;1]^^L *> [1;1;1] *> const 0 = [1;1;1]^^L *> [1;1;1;0] *> const 0).
  { f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. eapply progress_evstep_trans. 1: apply RND0. apply evstep_refl'.
  change ([1;1;1;1;1] *> ?X) with ([1;1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

Definition FR (p : nat) (l : side) : side := [1] *> [0;1]^^p *> [0;0] *> l.

Lemma PUSHr l k L o:
  RT l 2 (zone 0 (k + S L) (2^k - 1 + 2^(S k)*o)) -->+ RT ([1;0;0]^^k *> [1;0;1;0] *> l) 1 (zone 1 L o).
Proof.
  unfold RT, zone. rewrite dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X.
  eapply progress_evstep_trans. 1: apply PUSH. apply evstep_refl'. reflexivity.
Qed.

Lemma B1z0 p l L v: RT (FR p l) 1 (zone 0 (S L) (2*v)) -->+ RT l (p+3) (zone 2 L v).
Proof.
  unfold RT, FR, zone. rewrite dg_even. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^1 *> [1;1;1] *> ?X) with ([1;0] *> [1;1] *> [1] *> X).
  eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
Qed.

Lemma B1z1 p l L v: RT (FR p l) 1 (zone 0 (S L) (2*v+1)) -->+ RT l (p+4) (zone 0 L v).
Proof.
  unfold RT, FR, zone. rewrite dg_odd. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^1 *> [1;1;0] *> ?X) with ([1;0] *> [1;1] *> [0] *> X).
  eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'.
  replace (p+4) with (S (p+3)) by lia. rewrite lpow_S, Str_app_assoc, <-lpow_shift'. reflexivity.
Qed.

Lemma B1o p l L v: RT (FR p l) 1 (zone 1 L v) -->+ RT l (p+3) (zone 0 L v).
Proof.
  unfold RT, FR, zone. destruct L as [|L].
  - cbn [dg]. change ([1;0]^^1 *> ([1]^^1 ++ [] ++ [1;1;1]) *> ?X) with ([1;0] *> [1;1] *> [1;1] *> X).
    eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
  - cbn [dg]. rewrite !Str_app_assoc.
    change ([1;0]^^1 *> [1]^^1 *> [1;1;bitc v] *> ?X) with ([1;0] *> [1;1] *> [1;bitc v] *> X).
    eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
Qed.

Lemma B1t p l L v: RT (FR p l) 1 (zone 2 L v) -->+ RT l (p+3) (zone 1 L v).
Proof.
  unfold RT, FR, zone. rewrite !Str_app_assoc.
  change ([1;0]^^1 *> [1]^^2 *> ?X) with ([1;0] *> [1;1] *> X).
  eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
Qed.

Lemma B0r p l b L o:
  RT (FR p l) 0 (zone 0 (S b + S L) (2^(S b)*(2*o+1))) -->+ RT l (p+3) (zone 0 (b + S L) (2^b - 1 + 2^(S b)*o)).
Proof.
  unfold RT, FR, zone. rewrite dg_low, dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^0 *> ?X) with X.
  eapply progress_evstep_trans. 1: apply BITE0. apply evstep_refl'.
  rewrite lpow_S, Str_app_assoc.
  change ([1] *> [0;1;1] *> ?X) with ([1;0] *> [1;1] *> X). rewrite S_sh110.
  replace (p+3) with (S (p+2)) by lia. rewrite (lpow_S (p+2)), Str_app_assoc, <-lpow_shift'. reflexivity.
Qed.

Lemma B0cr p l L: RT (FR p l) 0 (zone 0 (S L) 0) -->+ RT l (p+2) (zone 0 (S L) (2^(S L)-2)).
Proof.
  replace (2^(S L)-2) with (2*(2^L-1)) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos L); lia).
  unfold RT, FR, zone. rewrite dg_zero, dg_even, dg_full. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^0 *> ?X) with X.
  assert (E: [1;1;1]^^(S L) *> [1;1;1] *> const 0 = [1;1;1]^^L *> [1;1;1;1;1;1;0] *> const 0).
  { rewrite lpow_S, Str_app_assoc, <-lpow_shift'. f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. apply BITE0c.
Qed.

Lemma B0c3r p l: RT (FR p l) 0 (zone 0 0 0) -->+ RT l (p+1) (zone 0 1 0).
Proof.
  unfold RT, FR, zone. cbn [dg lpow app].
  assert (E: [1;1;1] *> const 0 = [1;1;1;0;0] *> const 0).
  { cbn. rewrite <-!const_unfold. reflexivity. }
  change ([1;0]^^0 *> ?X) with X. rewrite E.
  eapply progress_evstep_trans. 1: apply BITE0c3. apply evstep_refl'. reflexivity.
Qed.

Lemma FR_round p l: [1;0;1;0] *> FR p l = FR (p+2) l.
Proof.
  unfold FR. replace (p+2) with (S (S p)) by lia.
  cbn [lpow]. rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma init: c0 -->* RT (const 0) 6 (zone 2 0 0).
Proof. unfold RT, zone. cbn. solve_init. Qed.

Definition lev (P : nat) (l : side) : side :=
  match P with
  | O => l
  | S p => FR p l
  end.

Definition okL (P : nat) (l : side) : Prop := P = 0%nat -> l = const 0.

Lemma lev_round P l: okL P l -> [1;0;1;0] *> lev P l = lev (P+2) l.
Proof.
  unfold okL. destruct P as [|P]; intros H.
  - rewrite H by reflexivity. cbn. repeat f_equal. apply const_unfold.
  - cbn [lev]. replace (S P + 2) with (S (P+2)) by lia. apply FR_round.
Qed.

Lemma okL_S P l: okL (S P) l.
Proof. unfold okL. intros H. discriminate H. Qed.

Inductive Rnd : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| RR1z q L v: 1 <= v -> Rnd (q+3) 0 L v (q+1) 0 L (v-1)
| RR1t q L v: 1 <= v -> Rnd (q+3) 2 L v (q+1) 2 L (v-1)
| RR2 q L v: 1 <= v -> Rnd (q+3) 1 L v q 0 (S L) (2*v-2)
| RO2 q L: Rnd (q+3) 2 L 0 (q+1) 0 (S L) (2^(S L)-1)
| RO1 q L: Rnd (q+3) 1 L 0 (q+1) 2 L (2^L-1)
| RO0 q L: Rnd (q+3) 0 L 0 q 0 (S L) (2^(S L)-2).

Lemma Rnd_tape q r L v q' r' L' v' P l:
  Rnd q r L v q' r' L' v' -> v < 2^L -> okL P l ->
  RT (lev P l) q (zone r L v) -->+ RT (lev (P+2) l) q' (zone r' L' v').
Proof.
  intros H Hv Hl. rewrite <-(lev_round P l Hl).
  destruct H.
  - apply R1z; lia.
  - apply R1t; lia.
  - apply R2r; lia.
  - apply O2r.
  - apply O1r.
  - apply O0r.
Qed.

Lemma Rnd_valid q r L v q' r' L' v':
  Rnd q r L v q' r' L' v' -> v < 2^L -> r < 3 -> v' < 2^L' /\ r' < 3.
Proof.
  intros H Hv Hr. destruct H; rewrite ?Nat.pow_succ_r' in *; pose proof (pow_pos L); lia.
Qed.

Lemma Rnd_exists q r L v: 3 <= q -> r < 3 -> exists q' r' L' v', Rnd q r L v q' r' L' v'.
Proof.
  intros Hq Hr. replace q with ((q-3)+3) by lia.
  destruct (Nat.eq_dec v 0) as [->|Hv].
  - destruct r as [|[|[|]]]; [| | |lia]; eexists _, _, _, _.
    + apply RO0.
    + apply RO1.
    + apply RO2.
  - destruct r as [|[|[|]]]; [| | |lia]; eexists _, _, _, _.
    + apply RR1z; lia.
    + apply RR2; lia.
    + apply RR1t; lia.
Qed.

Lemma okL_ge P l: 1 <= P -> okL P l.
Proof. intros H. destruct P; [lia|apply okL_S]. Qed.

Definition cap (r L : nat) : nat := L + (if Nat.eqb r 1 then 1 else 0).

Definition Kst (n r L : nat) : Prop := 2^(S (cap r L)) + 2 <= n.

Definition Jst (n r : nat) : Prop := 3 <= n /\ (r <> 0%nat -> n mod 2 = 1%nat).

Definition Mv (n r L v : nat) : nat :=
  (n + (if Nat.eqb r 1 then v else 2*v) + 2 * 2^(cap r L + 2)) mod 3.

Definition Qv (P q r L v : nat) : nat := (Mv q r L v + 2*P) mod 3.

Definition Ist (n r L v : nat) : Prop :=
  r < 3 /\ v < 2^L /\ Kst n r L /\ Mv n r L v <> 0%nat /\ ~ (n = 6 /\ r = 1 /\ L = 0 /\ v = 0)%nat.

Lemma init_I: Ist 6 2 0 0.
Proof. unfold Ist, Kst, Mv, cap. cbn. repeat split; lia. Qed.

Lemma Rnd_sign P q r L v q' r' L' v':
  Rnd q r L v q' r' L' v' -> Qv P q r L v = Qv (P+2) q' r' L' v'.
Proof.
  intros H. unfold Qv, Mv, cap.
  destruct H as [q L v Hv|q L v Hv|q L v Hv|q L|q L|q L]; pose proof (pow_pos L);
    cbn [Nat.eqb]; rewrite ?Nat.pow_add_r; cbn [Nat.pow]; lia.
Qed.

Inductive EB : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| EB1z0 L v: EB 1 0 (S L) (2*v) 2 2 L v
| EB1z1 L v: EB 1 0 (S L) (2*v+1) 3 0 L v
| EB1o L v: EB 1 1 L v 2 0 L v
| EB1t L v: EB 1 2 L v 2 1 L v
| EB0 b L o: EB 0 0 (S b + S L) (2^(S b)*(2*o+1)) 2 0 (b + S L) (2^b - 1 + 2^(S b)*o)
| EB0c L: EB 0 0 (S L) 0 1 0 (S L) (2^(S L)-2)
| EB0c3: EB 0 0 0 0 0 0 1 0.

Lemma EB_tape q r L v e r' L' v' p l:
  EB q r L v e r' L' v' -> RT (FR p l) q (zone r L v) -->+ RT l (S p + e) (zone r' L' v').
Proof.
  intros H. destruct H.
  - replace (S p + 2) with (p+3) by lia. apply B1z0.
  - replace (S p + 3) with (p+4) by lia. apply B1z1.
  - replace (S p + 2) with (p+3) by lia. apply B1o.
  - replace (S p + 2) with (p+3) by lia. apply B1t.
  - replace (S p + 2) with (p+3) by lia. apply B0r.
  - replace (S p + 1) with (p+2) by lia. apply B0cr.
  - replace (S p + 0) with (p+1) by lia. apply B0c3r.
Qed.

Lemma EB_sign q r L v e r' L' v' P:
  EB q r L v e r' L' v' -> (Mv (P + e) r' L' v' + Qv P q r L v) mod 3 = 0%nat.
Proof.
  intros H. unfold Qv, Mv, cap.
  destruct H as [L v|L v|L v|L v|b L o|L|]; cbn [Nat.eqb]; rewrite ?Nat.pow_add_r; cbn [Nat.pow].
  1-4,6: pose proof (pow_pos L); lia.
  - pose proof (pow_pos L). pose proof (pow_pos b). nia.
  - lia.
Qed.

Lemma iter_FR0 k X: [1;0;0]^^k *> X = Nat.iter k (FR 0) X.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite lpow_S, Str_app_assoc, IH. reflexivity.
Qed.

Lemma PUSH_lev k L o P l: okL P l ->
  RT (lev P l) 2 (zone 0 (k + S L) (2^k - 1 + 2^(S k)*o)) -->+
  RT (Nat.iter k (FR 0) (lev (P+2) l)) 1 (zone 1 L o).
Proof.
  intros Hl. rewrite <-(lev_round P l Hl), <-iter_FR0. apply PUSHr.
Qed.

Lemma inner1 k L o X:
  RT (Nat.iter (S k) (FR 0) X) 1 (zone 1 L o) -->+ RT (Nat.iter k (FR 0) X) 3 (zone 0 L o).
Proof. cbn [Nat.iter]. apply (EB_tape 1 1 L o 2 0 L o 0). constructor. Qed.

Definition safe (c : Q * tape) (N : nat) : Prop := forall M, M <= N -> ~ halts_in tm c M.

Lemma safe_mono c N N': safe c N -> N' <= N -> safe c N'.
Proof. intros H Hle M HM. apply H. lia. Qed.

Lemma safe_ev c c' N: c -->* c' -> safe c' N -> safe c N.
Proof.
  intros H HN M HM Hh. apply with_counter in H as [n Hn].
  destruct (Nat.leb_spec n M).
  - apply (HN (M - n)); [lia|]. eapply preceeds_halt; eauto.
  - eapply exceeds_halt; eauto.
Qed.

Lemma safe_prog c c' N: c -->+ c' -> safe c' (N - 1) -> safe c N.
Proof.
  intros H HN M HM Hh. apply progress_multistep in H as [n Hn].
  destruct (Nat.leb_spec (S n) M).
  - apply (HN (M - S n)); [lia|]. eapply preceeds_halt; eauto.
  - eapply exceeds_halt; eauto.
Qed.

Lemma safe_prog0 c c': c -->+ c' -> safe c 0.
Proof.
  intros H M HM Hh. apply progress_multistep in H as [n Hn].
  eapply exceeds_halt; [exact Hh | | exact Hn]. lia.
Qed.

Lemma safe_RT0 l q Z: safe (RT l q Z) 0.
Proof.
  intros M HM [ch [Hrun Hh]]. assert (M = 0%nat) by lia. subst M.
  inversion Hrun; subst. unfold RT in Hh. cbn in Hh. discriminate.
Qed.

Lemma phase (Inv : nat -> nat -> nat -> nat -> nat -> Prop):
  (forall j q r L v q' r' L' v', Rnd q r L v q' r' L' v' -> v < 2^L ->
     Inv j q r L v -> Inv (j+2) q' r' L' v') ->
  forall q j P l r L v, okL (P + j) l -> r < 3 -> v < 2^L -> Inv j q r L v ->
  exists j' q' r' L' v', q' <= 2 /\ r' < 3 /\ v' < 2^L' /\ Inv j' q' r' L' v' /\
    j <= j' /\ (3 <= q -> j + 2 <= j') /\
    RT (lev (P + j) l) q (zone r L v) -->* RT (lev (P + j') l) q' (zone r' L' v').
Proof.
  intros Hstep q. induction q as [q IH] using lt_wf_ind. intros j P l r L v Hl Hr Hv HI.
  destruct (Nat.le_gt_cases q 2) as [Hq|Hq].
  - exists j, q, r, L, v. repeat split; try assumption; try lia. apply evstep_refl.
  - destruct (Rnd_exists q r L v ltac:(lia) Hr) as [q' [r' [L' [v' HR]]]].
    assert (Hq': q' < q) by (destruct HR; lia).
    destruct (Rnd_valid _ _ _ _ _ _ _ _ HR Hv Hr) as [Hv' Hr'].
    assert (Hl': okL (P + (j+2)) l) by (apply okL_ge; lia).
    destruct (IH q' Hq' (j+2) P l r' L' v' Hl' Hr' Hv' (Hstep _ _ _ _ _ _ _ _ _ HR Hv HI))
      as [j2 [q2 [r2 [L2 [v2 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]].
    exists j2, q2, r2, L2, v2. repeat split; try assumption; try lia.
    eapply evstep_trans. 2: exact H7.
    apply progress_evstep. replace (P + (j+2)) with ((P+j)+2) by lia. apply Rnd_tape; assumption.
Qed.

Lemma cap0 L: cap 0 L = L. Proof. unfold cap. cbn. lia. Qed.

Lemma cap1 L: cap 1 L = S L. Proof. unfold cap. cbn. lia. Qed.

Lemma cap2 L: cap 2 L = L. Proof. unfold cap. cbn. lia. Qed.

Ltac pw := rewrite ?Nat.pow_succ_r' in *.

Lemma pow0 L: L = 0%nat -> 2^L = 1%nat.
Proof. intros ->. reflexivity. Qed.

Definition Kx (n r L v : nat) : Prop :=
  Kst n r L /\ ~ (r = 2%nat /\ v = 2^L - 1 /\ n = 2^(S L) + 2) /\
  ~ (n = 6%nat /\ r = 1%nat /\ L = 0%nat /\ v = 0%nat).

Definition Pre (n r L v : nat) : Prop := Jst n r \/ Kx n r L v.

Definition Saf (q r L v : nat) : Prop :=
  match r with
  | O => (L = 0%nat -> 3 <= q) /\ ~ (q = 2%nat /\ v = 2^L - 1) /\ (q = 0%nat -> v mod 2 = 0%nat)
  | 1%nat => 3 <= q /\ (v = 0%nat -> (q <= 2^(S L) + 2 -> q mod 2 = 1%nat) /\ q <> 2^(S L) + 4)
  | _ => (q <= 2*v + 2 -> q mod 2 = 1%nat) /\ q <> 2*v + 4
  end.

Definition KI (j q r L v : nat) : Prop :=
  match r with
  | O => 2^L <= j + q /\ (2^(S L) <= j + 2*v + 2 \/ 2^(S L) + 1 <= j + q) /\
         (q = 0%nat -> v <> 0%nat) /\ (L = 0%nat -> 4 <= q)
  | 1%nat => 2^(S (S L)) + 2 <= q /\ (v = 0%nat -> 2^(S L) + 5 <= q)
  | _ => 2^(S L) + 2 <= j + q /\ 2*v + 5 <= q
  end.

Definition ZI (C q r L v : nat) : Prop :=
  1 <= C /\
  match r with
  | O => L <= S C /\ q + 2^(S (S L)) + C <= 2*v + L + 2^(S (S (S C))) + 1 /\
         (q = 0%nat -> v = 0%nat -> L <= C)
  | 1%nat => S (S L) <= C /\ q <= 2^(S (S L)) + 1 /\ 3 <= q
  | _ => S L <= C /\ q <= 2*v + 2^(S L) + 1
  end.

Lemma Saf_step q r L v q' r' L' v': Rnd q r L v q' r' L' v' -> v < 2^L -> Saf q r L v -> Saf q' r' L' v'.
Proof.
  intros H Hv HS. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  destruct H; cbn [Saf] in *; pw; lia.
Qed.

Lemma KI_step j q r L v q' r' L' v': Rnd q r L v q' r' L' v' -> v < 2^L -> KI j q r L v -> KI (j+2) q' r' L' v'.
Proof.
  intros H Hv HK. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  destruct H; cbn [KI] in *.
  1-5: pw; lia.
  destruct L as [|L]; cbn [Nat.pow] in *; [lia|]. pose proof (pow_pos L). pw. lia.
Qed.

Lemma pow_mono a b: a <= b -> 2^a <= 2^b.
Proof. intros H. apply Nat.pow_le_mono_r; lia. Qed.

Lemma pow_lin a: S a <= 2^a.
Proof. pose proof (Nat.pow_gt_lin_r 2 a ltac:(lia)). lia. Qed.

Lemma ZI_step C q r L v q' r' L' v': Rnd q r L v q' r' L' v' -> v < 2^L -> ZI C q r L v -> ZI C q' r' L' v'.
Proof.
  intros H Hv [HC HZ]. split; [exact HC|]. pose proof (pow_pos L) as HL. pose proof (pow_lin C) as HlC.
  pose proof (pow0 L) as H0.
  destruct H; cbn [ZI] in *.
  - pw; lia.
  - pw; lia.
  -   pose proof (pow_mono (S (S L)) C ltac:(lia)). pw; lia.
  -   pose proof (pow_mono (S L) C ltac:(lia)). pw; lia.
  -   pw; lia.
  -   destruct (Nat.eq_dec L (S C)) as [E|E].
    + subst L. pw. lia.
    + destruct L as [|L]; cbn [Nat.pow] in *; [lia|]. pose proof (pow_pos L). pw. lia.
Qed.

Definition PI (n r L v j q r' L' v' : nat) : Prop :=
  j mod 2 = 0%nat /\ Qv j q r' L' v' = Mv n r L v /\
  (r' = 1%nat -> j = 0%nat) /\ (r' = 2%nat -> L' = 0%nat -> j <= 2) /\
  Saf q r' L' v' /\ (Kx n r L v -> KI j q r' L' v') /\
  (Jst n r -> ~ Kst n r L -> ZI (S (cap r L)) q r' L' v').

Lemma PI_step n r L v j q r1 L1 v1 q' r' L' v':
  Rnd q r1 L1 v1 q' r' L' v' -> v1 < 2^L1 -> PI n r L v j q r1 L1 v1 -> PI n r L v (j+2) q' r' L' v'.
Proof.
  intros H Hv [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  split; [lia|]. split; [rewrite <-H2; symmetry; apply Rnd_sign; exact H|].
  split; [intros E; subst r'; inversion H|].
  split.
  { intros E1 E2. inversion H; subst; try discriminate.
    - cbn in Hv. lia.
    - specialize (H3 eq_refl). lia. }
  split; [eapply Saf_step; eauto|].
  split; [intros HK; eapply KI_step; eauto|].
  intros HJ HK. eapply ZI_step; eauto.
Qed.

Lemma Mv_lt3 n r L v: Mv n r L v < 3.
Proof. unfold Mv. apply Nat.mod_upper_bound. lia. Qed.

Lemma Qv0 q r L v: Qv 0 q r L v = Mv q r L v.
Proof. unfold Qv. rewrite Nat.mul_0_r, Nat.add_0_r. apply Nat.mod_small, Mv_lt3. Qed.

Lemma Pre_n3 n r L v: Pre n r L v -> 3 <= n.
Proof.
  intros [[H _]|[H _]]; [exact H|]. unfold Kst in H. pose proof (pow_pos (S (cap r L))). lia.
Qed.

Lemma Saf_start n r L v: r < 3 -> v < 2^L -> Pre n r L v -> Saf n r L v.
Proof.
  intros Hr Hv HP. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  destruct HP as [[Hn Hp]|[HK [HT H6]]].
  - destruct r as [|[|[|r]]]; cbn [Saf]; pw; lia.
  - unfold Kst in HK. destruct r as [|[|[|r]]]; cbn [Saf]; rewrite ?cap0, ?cap1, ?cap2 in HK; pw; try lia.
    destruct (Nat.eq_dec L 0) as [->|EL]; [cbn in *; lia|].
    assert (2 <= 2^L) by (destruct L; [lia|]; cbn [Nat.pow]; pose proof (pow_pos L); lia). lia.
Qed.

Lemma KI_start n r L v: r < 3 -> v < 2^L -> Kx n r L v -> KI 0 n r L v.
Proof.
  intros Hr Hv [HK [HT H6]]. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  unfold Kst in HK. destruct r as [|[|[|r]]]; cbn [KI]; rewrite ?cap0, ?cap1, ?cap2 in HK; pw; try lia.
  destruct (Nat.eq_dec L 0) as [->|EL]; [cbn in *; lia|].
  assert (2 <= 2^L) by (destruct L; [lia|]; cbn [Nat.pow]; pose proof (pow_pos L); lia). lia.
Qed.

Lemma ZI_start n r L v: r < 3 -> v < 2^L -> Jst n r -> ~ Kst n r L -> ZI (S (cap r L)) n r L v.
Proof.
  intros Hr Hv [Hn Hp] HK. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  unfold Kst in HK. split; [lia|].
  destruct r as [|[|[|r]]]; cbn [ZI]; rewrite ?cap0, ?cap1, ?cap2 in *; pw; lia.
Qed.

Lemma PI_start n r L v: r < 3 -> v < 2^L -> Pre n r L v -> PI n r L v 0 n r L v.
Proof.
  intros Hr Hv HP. split; [reflexivity|]. split; [apply Qv0|].
  split; [reflexivity|]. split; [lia|]. split; [apply Saf_start; assumption|].
  split; [intros HK; apply KI_start; assumption|].
  intros HJ HK. apply ZI_start; assumption.
Qed.

Definition Post (n r L v n' r' L' v' : nat) : Prop :=
  r' < 3 /\ v' < 2^L' /\
  (Jst n r -> Jst (S n') r') /\
  (Kx n r L v -> Kst n' r' L') /\
  (Jst n r -> ~ Kst n r L -> Kst (S n') r' L' \/ cap r' L' <= S (cap r L)) /\
  (Mv n' r' L' v' + Mv n r L v) mod 3 = 0%nat /\
  (r' = 1%nat -> L' = 0%nat -> v' = 0%nat -> n' = 4%nat \/ 8 <= n').

Definition U (N : nat) : Prop :=
  forall P l n r L v, okL P l -> r < 3 -> v < 2^L -> Pre n r L v ->
  (forall n' r' L' v', Post n r L v n' r' L' v' -> safe (RT l (P + n') (zone r' L' v')) (N - 1)) ->
  safe (RT (lev P l) n (zone r L v)) N.

Lemma lowones L: forall v, v < 2^L -> v <> 2^L - 1 ->
  exists k L' o, L = k + S L' /\ v = 2^k - 1 + 2^(S k) * o /\ o < 2^L'.
Proof.
  induction L as [|L IH]; intros v Hv Hne.
  - cbn in *. lia.
  - rewrite Nat.pow_succ_r' in Hv, Hne.
    destruct (Nat.Even_or_Odd v) as [[o Ho]|[v' Hv']].
    + exists 0%nat, L, o. cbn. lia.
    + destruct (IH v') as [k [L' [o [E1 [E2 E3]]]]]; [lia|lia|].
      exists (S k), L', o. split; [lia|]. split; [|exact E3].
      subst v v'. pose proof (pow_pos k). pw. lia.
Qed.

Lemma bite_shape j qb rb Lb vb: qb <= 2 -> rb < 3 -> vb < 2^Lb -> Saf qb rb Lb vb -> 2 <= j ->
  (rb = 1%nat -> j = 0%nat) ->
  (exists e r' L' v', EB qb rb Lb vb e r' L' v') \/
  (qb = 2%nat /\ rb = 0%nat /\ exists k L' o, Lb = k + S L' /\ vb = 2^k - 1 + 2^(S k) * o /\ o < 2^L').
Proof.
  intros Hq Hr Hv HS Hj H1.
  destruct rb as [|[|[|rb]]]; [| lia | | lia]; cbn [Saf] in HS.
  - destruct HS as [HS1 [HS2 HS3]].
    destruct qb as [|[|[|qb]]]; [| | |lia].
    + destruct Lb as [|Lb]; [lia|]. left.
      destruct (Nat.eq_dec vb 0) as [->|Hne].
      * eexists _, _, _, _. apply EB0c.
      * destruct (lowbit vb Hne) as [b [o ->]].
        destruct b as [|b]; [rewrite Nat.pow_0_r, Nat.mul_1_l in HS3; lia|].
        destruct (lowbit_lt _ _ _ Hv) as [Hb Ho].
        replace (S Lb) with (S b + S (Lb - b - 1)) by lia.
        eexists _, _, _, _. apply EB0.
    + destruct Lb as [|Lb]; [lia|]. left.
      destruct (Nat.Even_or_Odd vb) as [[w ->]|[w ->]]; eexists _, _, _, _; [apply EB1z0|apply EB1z1].
    + right. split; [reflexivity|]. split; [reflexivity|]. apply lowones; [exact Hv|]. tauto.
  - destruct HS as [HS1 HS2]. assert (qb = 1%nat) as -> by lia.
    left. eexists _, _, _, _. apply EB1t.
Qed.

Lemma EB_valid q r L v e r' L' v': EB q r L v e r' L' v' -> v < 2^L -> r' < 3 /\ v' < 2^L'.
Proof.
  intros H Hv. destruct H; (split; [lia|]).
  - pw. lia.
  - pw. lia.
  - exact Hv.
  - exact Hv.
  - rewrite Nat.pow_add_r in *. pw. pose proof (pow_pos b). pose proof (pow_pos L).
    assert (o < 2^L) by nia. nia.
  - pose proof (pow_pos L). pw. lia.
  - cbn. lia.
Qed.

Lemma EB_lev q r L v e r' L' v' P l: 1 <= P -> EB q r L v e r' L' v' ->
  RT (lev P l) q (zone r L v) -->+ RT l (P + e) (zone r' L' v').
Proof. intros HP H. destruct P as [|p]; [lia|]. cbn [lev]. apply EB_tape. exact H. Qed.

Lemma Kst_mono n n' r L: Kst n r L -> n <= n' -> Kst n' r L.
Proof. unfold Kst. lia. Qed.

Lemma ending n r L v j qb rb Lb vb e r' L' v':
  EB qb rb Lb vb e r' L' v' -> PI n r L v j qb rb Lb vb -> 2 <= j -> vb < 2^Lb ->
  Post n r L v (j + e) r' L' v'.
Proof.
  intros H [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hj Hvb.
  destruct (EB_valid _ _ _ _ _ _ _ _ H Hvb) as [Hr' Hv'].
  pose proof (EB_sign _ _ _ _ _ _ _ _ j H) as HS. rewrite H2 in HS.
  split; [exact Hr'|]. split; [exact Hv'|].
  split.
  { intros _. unfold Jst. destruct H; split; lia. }
  split.
  { intros HK. specialize (H6 HK). unfold Kst.
    destruct H; cbn [KI] in H6; rewrite ?cap0, ?cap1, ?cap2; cbn [Nat.add] in *; pw; lia. }
  split.
  { intros HJ HK. destruct (H7 HJ HK) as [HC7 HZ7]. right.
    destruct H; cbn [ZI] in HZ7; rewrite ?cap0, ?cap1, ?cap2; cbn [Nat.add] in *; lia. }
  split; [exact HS|].
  intros E1 E2 E3. destruct H; try discriminate E1. subst. left. specialize (H4 eq_refl eq_refl). lia.
Qed.

Lemma ending_B2 n r L v j L' o:
  PI n r L v j 2 0 (0 + S L') (2^0 - 1 + 2^1 * o) -> 2 <= j -> o < 2^L' ->
  Post n r L v (j + 4) 0 L' o.
Proof.
  intros [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hj Ho. cbn [Nat.add Nat.pow Nat.sub] in *.
  split; [lia|]. split; [exact Ho|].
  split; [intros _; unfold Jst; lia|].
  split.
  { intros HK. specialize (H6 HK). unfold Kst. cbn [KI] in H6. rewrite cap0. pw. lia. }
  split.
  { intros HJ HK. destruct (H7 HJ HK) as [HC7 HZ7]. right. cbn [ZI] in HZ7. rewrite cap0. lia. }
  split.
  { rewrite <-H2. unfold Qv, Mv, cap. cbn [Nat.eqb]. rewrite !Nat.pow_add_r. cbn [Nat.pow].
    pose proof (pow_pos L'). lia. }
  intros E. discriminate E.
Qed.

Definition Budget (n r L C : nat) : Prop := Kst n r L \/ cap r L <= C.

Definition SR (j a b : nat) : Prop :=
  (j mod 2 = 0%nat -> b = a) /\ (j mod 2 = 1%nat -> (a + b + 2) mod 3 = 0%nat).

Lemma JK n r L v: Jst n r -> Kst n r L -> Kx n r L v.
Proof.
  intros [Hn Hp] HK. split; [exact HK|]. split.
  - intros [-> [_ ->]]. pw. specialize (Hp ltac:(lia)). lia.
  - intros [-> [-> _]]. specialize (Hp ltac:(lia)). lia.
Qed.

Lemma Budget_step n r L v C n' r' L' v': Jst n r -> Budget n r L C -> Post n r L v n' r' L' v' ->
  Budget (S n') r' L' (S C).
Proof.
  intros HJ HB [_ [_ [_ [HU2 [HU3 _]]]]].
  destruct (Nat.le_gt_cases (2^(S (cap r L)) + 2) n) as [HK|HK].
  - left. apply (Kst_mono n'); [apply HU2, JK; assumption | lia].
  - destruct HB as [HB|HB]; [unfold Kst in HB; lia|].
    destruct (HU3 HJ ltac:(unfold Kst; lia)) as [H|H]; [left; exact H | right; lia].
Qed.

Lemma Mv_shift a n r L v: Mv (a + n) r L v = (Mv n r L v + a) mod 3.
Proof. unfold Mv. generalize (if Nat.eqb r 1 then v else 2*v) (2 * 2^(cap r L + 2)). intros x y. lia. Qed.

Lemma SR_step j n r L v n' r' L' v' b: b < 3 -> Post n r L v n' r' L' v' -> SR j (Mv (S n') r' L' v') b ->
  SR (S j) (Mv n r L v) b.
Proof.
  intros Hb [_ [_ [_ [_ [_ [HU4 _]]]]]] [HE HO].
  change (S n') with (1 + n') in HE, HO. rewrite Mv_shift in HE, HO.
  pose proof (Mv_lt3 n r L v). pose proof (Mv_lt3 n' r' L' v').
  split; intros Hj; lia.
Qed.

Lemma pow2_mod3 k: exists x, 2^k = 3*x + 1 + k mod 2.
Proof.
  induction k as [|k [x Hx]]; [exists 0%nat; reflexivity|].
  exists (2*x + k mod 2). rewrite Nat.pow_succ_r', Hx. pose proof (Nat.mod_upper_bound k 2). lia.
Qed.

Lemma QvN j k L o:
  (k mod 2 = 0%nat -> Qv j 2 0 (S k + S L) (2^(S k) - 1 + 2^(S (S k)) * o) = (Mv 3 0 L o + 1 + 2*j) mod 3) /\
  (k mod 2 = 1%nat -> Qv j 2 0 (S k + S L) (2^(S k) - 1 + 2^(S (S k)) * o) = (2 * (Mv 3 0 L o + 1) + 2*j) mod 3).
Proof.
  destruct (pow2_mod3 k) as [x Hx]. pose proof (pow_pos L).
  unfold Qv, Mv, cap. cbn [Nat.eqb]. rewrite !Nat.pow_add_r. cbn [Nat.pow]. rewrite Hx.
  split; intros Hk; rewrite Hk; lia.
Qed.

Lemma compose n r L v j k L' o n1 r1 L1 v1 n3 r3 L3 v3:
  PI n r L v j 2 0 (S k + S L') (2^(S k) - 1 + 2^(S (S k)) * o) -> 2 <= j ->
  Jst n1 r1 -> Budget n1 r1 L1 (L' + k) -> SR k (Mv 3 0 L' o) (Mv n1 r1 L1 v1) ->
  Post n1 r1 L1 v1 n3 r3 L3 v3 -> Post n r L v (j + 2 + n3) r3 L3 v3.
Proof.
  intros [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hj HJ1 HB1 HSR HP.
  pose proof (Budget_step _ _ _ _ _ _ _ _ _ HJ1 HB1 HP) as HB3.
  destruct HP as [Hr3 [Hv3 [HU1 [HU2 [HU3 [HU4 HU5]]]]]].
  destruct (HU1 HJ1) as [Hn3 Hp3].
  split; [exact Hr3|]. split; [exact Hv3|].
  split.
  { intros _. split; [lia|]. intros E. specialize (Hp3 E). lia. }
  split.
  { intros HK. specialize (H6 HK). cbn [KI] in H6. unfold Kst.
    destruct HB3 as [HB3|HB3]; [unfold Kst in HB3; lia|].
    pose proof (pow_mono (S (cap r3 L3)) (S k + S L') ltac:(lia)). lia. }
  split.
  { intros HJ HK. destruct (H7 HJ HK) as [HC7 HZ7]. cbn [ZI] in HZ7.
    destruct HB3 as [HB3|HB3]; [left; apply (Kst_mono (S n3)); [exact HB3|lia] | right; lia]. }
  split.
  { rewrite (Mv_shift (j + 2) n3). destruct HSR as [HE HO]. destruct (QvN j k L' o) as [QE QO].
    pose proof (Mv_lt3 n3 r3 L3 v3). pose proof (Mv_lt3 n1 r1 L1 v1). pose proof (Mv_lt3 3 0 L' o).
    pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
    rewrite <-H2.
    destruct (Nat.eq_dec (k mod 2) 0) as [Ek|Ek].
    - rewrite (QE Ek). specialize (HE Ek). lia.
    - assert (Ek1: k mod 2 = 1%nat) by lia. rewrite (QO Ek1). specialize (HO Ek1). lia. }
  intros E1 E2 E3. right. destruct (HU5 E1 E2 E3); lia.
Qed.

Lemma STK: forall j B, (forall B', B' <= B -> U B') -> forall n r L v C X,
  Jst n r -> Budget n r L C -> r < 3 -> v < 2^L ->
  (forall n1 r1 L1 v1, Jst n1 r1 -> Budget n1 r1 L1 (C + j) -> r1 < 3 -> v1 < 2^L1 ->
     SR j (Mv n r L v) (Mv n1 r1 L1 v1) -> safe (RT X n1 (zone r1 L1 v1)) (B - j)) ->
  safe (RT (Nat.iter j (FR 0) X) n (zone r L v)) B.
Proof.
  induction j as [|j IH]; intros B HU n r L v C X HJ HB Hr Hv Hk.
  - cbn [Nat.iter].
    pose proof (Hk n r L v HJ ltac:(rewrite Nat.add_0_r; exact HB) Hr Hv
                  ltac:(split; intros; [reflexivity|lia])) as H.
    rewrite Nat.sub_0_r in H. exact H.
  - change (Nat.iter (S j) (FR 0) X) with (lev 1 (Nat.iter j (FR 0) X)).
    apply (HU B (le_n B) 1%nat (Nat.iter j (FR 0) X) n r L v (okL_S 0 _) Hr Hv (or_introl HJ)).
    intros n' r' L' v' HP.
    change (1 + n') with (S n').
    pose proof HP as [Hr' [Hv' [HU1 _]]].
    apply (IH (B - 1) (fun B' HB' => HU B' ltac:(lia)) (S n') r' L' v' (S C) X (HU1 HJ)
             (Budget_step _ _ _ _ _ _ _ _ _ HJ HB HP) Hr' Hv').
    intros n1 r1 L1 v1 HJ1 HB1 Hr1 Hv1 HS1.
    replace (B - 1 - j) with (B - S j) by lia.
    apply Hk; try assumption.
    + replace (C + S j) with (S C + j) by lia. exact HB1.
    + eapply SR_step; [apply Mv_lt3 | eassumption | eassumption].
Qed.

Lemma U_all: forall N, U N.
Proof.
  intros N. induction N as [N IH] using strong_induction.
  intros P l n r L v Hl Hr Hv Hpre Hk.
  pose proof (Pre_n3 _ _ _ _ Hpre) as Hn.
  destruct N as [|N'].
  { destruct (Rnd_exists n r L v Hn Hr) as [q' [r' [L' [v' HR]]]].
    eapply safe_prog0. eapply Rnd_tape; eassumption. }
  destruct (phase (PI n r L v) (PI_step n r L v) n 0 P l r L v)
    as [j [qb [rb [Lb [vb [Hqb [Hrb [Hvb [HI [_ [Hj Hrun]]]]]]]]]]].
  { rewrite Nat.add_0_r. exact Hl. }
  { exact Hr. } { exact Hv. } { apply PI_start; assumption. }
  specialize (Hj Hn). rewrite Nat.add_0_r in Hrun. cbn [Nat.add] in Hj.
  eapply safe_ev; [exact Hrun|].
  assert (HlP: okL (P + j) l) by (apply okL_ge; lia).
  pose proof HI as [_ [_ [HI3 [_ [HI5 _]]]]].
  destruct (bite_shape j qb rb Lb vb Hqb Hrb Hvb HI5 Hj HI3)
    as [[e [r' [L' [v' HE]]]] | [Eq [Er [k [L' [o [EL [Ev Ho]]]]]]]].
  -  
    eapply safe_prog. { apply EB_lev; [lia | exact HE]. }
    replace (P + j + e) with (P + (j + e)) by lia.
    apply Hk. eapply ending; eassumption.
  - subst qb rb Lb vb. destruct k as [|k].
    +  
      eapply safe_prog.
      { eapply progress_trans. { apply (PUSH_lev 0 L' o (P + j) l HlP). }
        cbn [Nat.iter]. apply (EB_lev 1 1 L' o 2 0 L' o (P + j + 2) l); [lia | constructor]. }
      replace (P + j + 2 + 2) with (P + (j + 4)) by lia.
      apply Hk. apply ending_B2; assumption.
    +  
      assert (Hpush: RT (lev (P + j) l) 2 (zone 0 (S k + S L') (2^(S k) - 1 + 2^(S (S k)) * o)) -->+
                     RT (Nat.iter k (FR 0) (lev (P + j + 2) l)) 3 (zone 0 L' o)).
      { eapply progress_trans. { apply (PUSH_lev (S k) L' o (P + j) l HlP). } apply inner1. }
      eapply safe_prog; [exact Hpush|].
      replace (S N' - 1) with N' by lia.
      apply (STK k N' (fun B HB => IH B ltac:(lia)) 3 0 L' o L' (lev (P + j + 2) l)).
      * split; [lia|]. intros E; lia.
      * right. rewrite cap0. lia.
      * lia.
      * exact Ho.
      * intros n1 r1 L1 v1 HJ1 HB1 Hr1 Hv1 HS1.
        apply (IH (N' - k) ltac:(lia) (P + j + 2) l n1 r1 L1 v1 (okL_ge (P + j + 2) l ltac:(lia)) Hr1 Hv1 (or_introl HJ1)).
        intros n3 r3 L3 v3 HP3.
        replace (P + j + 2 + n3) with (P + (j + 2 + n3)) by lia.
        apply (safe_mono _ (S N' - 1)); [| lia].
        apply Hk. eapply compose; eassumption.
Qed.

Lemma Ist_Kx n r L v: Ist n r L v -> Kx n r L v.
Proof.
  unfold Ist, Kx. intros [Hr [Hv [HK [HM H6]]]]. split; [exact HK|]. split; [|exact H6].
  intros [-> [-> ->]]. apply HM. unfold Mv, cap. cbn [Nat.eqb]. rewrite !Nat.pow_add_r. cbn [Nat.pow].
  pose proof (pow_pos L). lia.
Qed.

Lemma cycles N: forall n r L v, Ist n r L v -> safe (RT (const 0) n (zone r L v)) N.
Proof.
  induction N as [N IH] using strong_induction. intros n r L v HI.
  pose proof (Ist_Kx _ _ _ _ HI) as HK. destruct HI as [Hr [Hv [HKs [HM H6]]]].
  apply (U_all N 0%nat (const 0) n r L v); [intros _; reflexivity | exact Hr | exact Hv | right; exact HK |].
  intros n' r' L' v' [Hr' [Hv' [_ [HU2 [_ [HU4 HU5]]]]]].
  destruct N as [|N']; [apply safe_RT0|].
  replace (S N' - 1) with N' by lia.
  change (0 + n')%nat with n'. apply IH; [lia|]. unfold Ist. split; [exact Hr'|]. split; [exact Hv'|]. split; [apply HU2, HK|].
  pose proof (Mv_lt3 n r L v). pose proof (Mv_lt3 n' r' L' v'). split; [lia|].
  intros [E1 [E2 [E3 E4]]]. destruct (HU5 E2 E3 E4); lia.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  intros [N HN].
  exact (safe_ev c0 _ N init (cycles N 6 2 0 0 init_I) N (le_n N) HN).
Qed.

End TM5.
Print Assumptions TM5.nonhalt.
