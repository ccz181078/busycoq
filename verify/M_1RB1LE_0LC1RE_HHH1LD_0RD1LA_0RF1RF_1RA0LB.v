(** * 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB halts

    BB(6) holdout (bbchallenge #23376).  It halts after about 1.27 * 10^758 steps.

    At the visits of the right end (the head in [A] on the blank cell right of the tape) the tape is,
    read from the head leftwards, a short front ([fH] or [fV]), a ladder of levels and a tail of cells.
    A level is a rung of [j + 1] blocks [blk] (ten cells) and one of eight separators ([W p j Y]); together
    with the kind of the next hit it has 16 positions.  A hit from the front is a fixed list of calls on
    the tape left of the front (five for an H-hit, one for a V-hit).  A hit on a level moves it to the next
    position; at ten positions it is absorbed, at six it is passed on to the rest of the tape left of the
    level, as a hit of the other kind ([hit0] ... [hit15], proved for every [j] and every rest by symbolic
    execution, using the calls on the rest as hypotheses).  So the levels are transparent: the tape left of
    a ladder lives as it would right behind the front, only slower ([stack_run], by induction on the
    ladder; whole turns of 16 hits are done by arithmetic).  The ladder is an odometer, level k getting
    (3/8)^(k-1) of the hits.  After a reset (step 27,167,343) the tail eats the old blocks, two per 12 hits,
    leaving three new levels; with 887 levels the old blocks are used up and the next hit runs into the
    blank left end, where state [C] reads a 0.

    The proof:
    - the level, front and halting rules, for every block count ([hit*], [halt*], [front*]);
    - [stack_run]: any number of hits on any ladder, with the block counts in binary;
    - [loop_ok]: an accelerated run, sound by construction.  It keeps the levels as numbers and simulates
      only the cells of the tail, cell by cell; up to [batchCap] hits on the tail are made in one pass over
      the levels.  When the tail's calls do not come back as the levels expect, the deepest level is
      written out as cells again;
    - [halt]: the run from the blank tape reaches a hit that halts.  This is the only computation
      (about 30 s in the VM).

    No tape data is in this file.  An earlier proof of the same result, with exact step counts, is in Lean
    (fractal-geometry-explorer/busy-beaver-explorer, holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB). *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia String ZArith.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB").

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

(** * Calls, hits and levels *)

(** A call on the left tape [T] in state [q]: the head stands on a cell [1] right of [T] and comes back
    on the cell right of that [1] in state [q'], with [T] changed into [T'], whatever lies to the right. *)
Definition Call (q q' : Q) (T T' : side) : Prop :=
  forall R, T {{q}}> (1 >> R) -->* (1 >> T') {{q'}}> R.
(** A call that does not come back: the machine halts. *)
Definition HaltCall (q : Q) (T : side) : Prop :=
  forall R, halts tm (T {{q}}> (1 >> R)).

(** An H-hit is five calls, a V-hit one; afterwards the tape has 2 (H) or 6 (V) more cells [1] in front. *)
Definition HitH (Y Y' : side) : Prop :=
  exists T0 T1 T2 T3 T4 T5, Y = 1 >> T0 /\
    Call C E T0 T1 /\ Call E F T1 T2 /\ Call B E T2 T3 /\ Call C A T3 T4 /\ Call D E T4 T5 /\
    Y' = 1 >> 1 >> 1 >> T5.
Definition HitV (Y Y' : side) : Prop :=
  exists T0 T1, Y = 1 >> T0 /\ Call C E T0 T1 /\ Y' = [1;1;1;1;1;1;1] *> T1.
(** Hits that halt: in the first call (any kind), or in the fourth call of an H-hit. *)
Definition HC (Y : side) : Prop := exists T0, Y = 1 >> T0 /\ HaltCall C T0.
Definition H4 (Y : side) : Prop :=
  exists T0 T1 T2 T3, Y = 1 >> T0 /\
    Call C E T0 T1 /\ Call E F T1 T2 /\ Call B E T2 T3 /\ HaltCall C T3.

(** The block [4] (ten cells, nearest first) and the separators of the 16 positions. *)
Definition blk : list Sym := [1;1;1;1;1;1;1;1;1;0].
Definition sepL (p : nat) : list Sym :=
  match p with
  | 0%nat | 5%nat => [1;0;1;1;1;0;1;0;1;1;1;0]
  | 1%nat | 12%nat => [1;0;1;1;1;1;1;1;1;0;1;1;1;0]
  | 2%nat | 7%nat => [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;0]
  | 3%nat | 14%nat => [1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0]
  | 4%nat | 9%nat => [1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0]
  | 6%nat | 11%nat => [1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1;1;0]
  | 8%nat | 13%nat => [1;0;1;1;1;0;1;1;1;1;1;1;1;0]
  | _ => [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]
  end.
(** A level at position [p] with [j + 1] blocks, in front of the rest [Y]. *)
Definition W (p j : nat) (Y : side) : side := blk ^^ (S j) *> sepL p *> Y.

(** The two fronts, [2 1] and [5]. *)
Definition fH : list Sym := [1;1;1;1;1;0;1;1;1;0].
Definition fV : list Sym := [1;1;1;1;1;1;1;1;1;1;1;0].

(** * Tactics: symbolic execution that uses the calls in the context *)

Ltac notdone R := lazymatch goal with |- (_, (_, hd R, tl R)) -[ _ ]->* _ => fail | _ => idtac end.
Ltac use_call := match goal with H : Call _ _ _ _ |- _ => eapply evstep_trans; [apply H|] end.
Ltac run_to R :=
  repeat (notdone R; first [ use_call | step1 | use_shift_rule | progress simpl_rotate ]);
  try simpl_rotate; apply evstep_refl.
Ltac do_call := let R := fresh "R" in intro R; unfold blk; simpl_tape; run_to R.
Ltac run_halt :=
  repeat (first [ apply evstep_refl | use_call | step1 | use_shift_rule | progress simpl_rotate ]).
Ltac do_halt :=
  let R := fresh "R" in intro R; unfold blk; simpl_tape;
  eapply halts_evstep; [ match goal with H : HaltCall _ _ |- _ => apply H end | run_halt ].
Ltac solve_eq := unfold blk; simpl_tape; simpl_rotate; reflexivity.
Ltac solve_parts :=
  first [ apply conj; [ first [ reflexivity | do_call | do_halt ] | solve_parts ]
        | first [ do_halt | solve_eq ] ].
Ltac solve_hit := unfold HitH, HitV, HC, H4, W; repeat lazymatch goal with |- exists _, _ => eexists end; solve_parts.
Ltac solve_die := solve_hit.
Ltac destruct_hit H :=
  first [ destruct H as (U0&U1&U2&U3&U4&U5&->&c1&c2&c3&c4&c5&->)
        | destruct H as (U0&U1&->&c1&->) ].
Ltac destruct_die H :=
  first [ destruct H as (U0&U1&U2&U3&->&c1&c2&c3&h4)
        | destruct H as (U0&->&h1) ].

(** * One hit on one level, for every block count and every rest *)

Lemma hit0 j Y : HitH (W 0 j Y) (W 1 j Y).
Proof. solve_hit. Qed.

Lemma hit1 j Y : HitV (W 1 j Y) (W 2 j Y).
Proof. solve_hit. Qed.

Lemma hit2 j Y Y' : HitH Y Y' -> HitH (W 2 j Y) (W 3 j Y').
Proof. intros H; destruct_hit H; solve_hit. Qed.

Lemma hit3 j Y : HitV (W 3 j Y) (W 4 (S j) Y).
Proof. solve_hit. Qed.

Lemma hit4 j Y Y' : HitV Y Y' -> HitH (W 4 j Y) (W 5 j Y').
Proof. intros H; destruct_hit H; solve_hit. Qed.

Lemma hit5 j Y : HitV (W 5 j Y) (W 6 j Y).
Proof. solve_hit. Qed.

Lemma hit6 j Y : HitH (W 6 j Y) (W 7 j Y).
Proof. solve_hit. Qed.

Lemma hit7 j Y Y' : HitH Y Y' -> HitV (W 7 j Y) (W 8 (S j) Y').
Proof. intros H; destruct_hit H; solve_hit. Qed.

Lemma hit8 j Y : HitH (W 8 j Y) (W 9 j Y).
Proof. solve_hit. Qed.

Lemma hit9 j Y : HitV (W 9 j Y) (W 10 j Y).
Proof. solve_hit. Qed.

Lemma hit10 j Y Y' : HitV Y Y' -> HitH (W 10 j Y) (W 11 j Y').
Proof. intros H; destruct_hit H; solve_hit. Qed.

Lemma hit11 j Y : HitV (W 11 j Y) (W 12 (S j) Y).
Proof. solve_hit. Qed.

Lemma hit12 j Y Y' : HitH Y Y' -> HitH (W 12 j Y) (W 13 j Y').
Proof. intros H; destruct_hit H; solve_hit. Qed.

Lemma hit13 j Y : HitV (W 13 j Y) (W 14 j Y).
Proof. solve_hit. Qed.

Lemma hit14 j Y : HitH (W 14 j Y) (W 15 j Y).
Proof. solve_hit. Qed.

Lemma hit15 j Y Y' : HitV Y Y' -> HitV (W 15 j Y) (W 0 (S j) Y').
Proof. intros H; destruct_hit H; solve_hit. Qed.

Lemma halt2_H4 j Y : H4 Y -> HC (W 2 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt2_HC j Y : HC Y -> HC (W 2 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt4_HC j Y : HC Y -> H4 (W 4 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt7_H4 j Y : H4 Y -> HC (W 7 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt7_HC j Y : HC Y -> HC (W 7 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt10_HC j Y : HC Y -> HC (W 10 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt12_H4 j Y : H4 Y -> H4 (W 12 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt12_HC j Y : HC Y -> H4 (W 12 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.

Lemma halt15_HC j Y : HC Y -> HC (W 15 j Y).
Proof. intros H; destruct_die H; solve_die. Qed.


Ltac run_fin :=
  repeat (first [ solve [finish] | use_call | step1 | use_shift_rule | progress simpl_rotate ]).
Ltac front_halt := unfold fH, fV; simpl_tape;
  eapply halts_evstep; [ match goal with H : HaltCall _ _ |- _ => apply H end | run_halt ].

Lemma frontH Y Y' : HitH Y Y' -> (fH *> Y) {{A}}> const 0 -->* (fV *> Y') {{A}}> const 0.
Proof. intros H; destruct_hit H. unfold fH, fV. simpl_tape. run_fin. Qed.
Lemma frontV Y Y' : HitV Y Y' -> (fV *> Y) {{A}}> const 0 -->* (fH *> Y') {{A}}> const 0.
Proof. intros H; destruct_hit H. unfold fH, fV. simpl_tape. run_fin. Qed.
Lemma frontH_HC Y : HC Y -> halts tm ((fH *> Y) {{A}}> const 0).
Proof. intros H; destruct_die H. front_halt. Qed.
Lemma frontH_H4 Y : H4 Y -> halts tm ((fH *> Y) {{A}}> const 0).
Proof. intros H; destruct_die H. front_halt. Qed.
Lemma frontV_HC Y : HC Y -> halts tm ((fV *> Y) {{A}}> const 0).
Proof. intros H; destruct_die H. front_halt. Qed.

Section P3_part.

Local Open Scope nat_scope.

(** * The table of the 16 positions *)

Inductive Kind := KH | KV.
Definition other (k : Kind) : Kind := match k with KH => KV | KV => KH end.
Definition Hit (k : Kind) : side -> side -> Prop := match k with KH => HitH | KV => HitV end.
Fixpoint Run (k : Kind) (n : nat) (Y Y' : side) : Prop :=
  match n with
  | O => Y = Y'
  | S n => exists Y1, Hit k Y Y1 /\ Run (other k) n Y1 Y'
  end.

Definition kindOf (p : nat) : Kind := if Nat.even p then KH else KV.
Definition passOf (p : nat) : option Kind :=
  match p with
  | 2 | 7 | 12 => Some KH
  | 4 | 10 | 15 => Some KV
  | _ => None
  end.
Definition nxt (p : nat) : nat := if p =? 15 then 0 else S p.
Definition inc (p : nat) : nat := match p with 3 | 7 | 11 | 15 => 1 | _ => 0 end.
(** The kind of the next hit that a level at position [p] passes on. *)
Definition firstPass (p : nat) : Kind :=
  match p with 0 | 1 | 2 | 5 | 6 | 7 | 11 | 12 => KH | _ => KV end.

Lemma level_hit p j : p < 16 ->
  (passOf p = None -> forall Y, Hit (kindOf p) (W p j Y) (W (nxt p) (j + inc p) Y)) /\
  (forall k, passOf p = Some k -> forall Y Y', Hit k Y Y' ->
     Hit (kindOf p) (W p j Y) (W (nxt p) (j + inc p) Y')).
Proof.
  intros Hp.
  do 16 (destruct p as [|p]; [cbn [passOf kindOf nxt inc Nat.even Nat.eqb firstPass Hit];
    rewrite ?Nat.add_0_r, ?Nat.add_1_r; split; intros;
    try discriminate;
    try match goal with H : Some _ = Some _ |- _ => injection H as <- end;
    first [ apply hit0 | apply hit1 | apply hit2 | apply hit3 | apply hit4 | apply hit5 | apply hit6
          | apply hit7 | apply hit8 | apply hit9 | apply hit10 | apply hit11 | apply hit12 | apply hit13
          | apply hit14 | apply hit15 ]; assumption |]).
  lia.
Qed.

End P3_part.

Section P4_part.

Local Open Scope nat_scope.

(** * Many hits on one level *)

Fixpoint advN (p j y : nat) : nat * nat :=
  match y with O => (p, j) | S y => advN (nxt p) (j + inc p) y end.
Fixpoint passN (p y : nat) : nat :=
  match y with O => O | S y => (if passOf p then 1 else 0) + passN (nxt p) y end.

Lemma tab_facts p : p < 16 ->
  nxt p < 16 /\ kindOf (nxt p) = other (kindOf p) /\
  (passOf p = None -> firstPass (nxt p) = firstPass p) /\
  (forall k, passOf p = Some k -> firstPass p = k /\ firstPass (nxt p) = other k).
Proof.
  intros H.
  do 16 (destruct p as [|p]; [cbn; repeat split; try lia; intros; try discriminate;
    try match goal with E : Some _ = Some _ |- _ => injection E as <- end; reflexivity |]).
  lia.
Qed.

Lemma level_run y : forall p j Y Y', p < 16 -> Run (firstPass p) (passN p y) Y Y' ->
  Run (kindOf p) y (W p j Y) (W (fst (advN p j y)) (snd (advN p j y)) Y').
Proof.
  induction y as [|y IH]; intros p j Y Y' Hp H.
  - cbn in *. subst. reflexivity.
  - destruct (tab_facts p Hp) as (Hn & Hk & Hnone & Hsome).
    destruct (level_hit p j Hp) as [L1 L2].
    cbn [passN] in H. cbn [Run advN].
    destruct (passOf p) as [k|] eqn:E.
    + destruct (Hsome k eq_refl) as [F1 F2]. rewrite F1 in H.
      destruct H as (Y1 & Hh & Hr). rewrite <- F2 in Hr.
      exists (W (nxt p) (j + inc p) Y1). split; [now apply (L2 k)|].
      rewrite <- Hk. now apply IH.
    + exists (W (nxt p) (j + inc p) Y). split; [now apply L1|].
      rewrite <- Hk. apply IH; auto. rewrite Hnone; auto.
Qed.

(** * Closed forms: 16 hits make a whole turn *)

Lemma advN_add a : forall b p j, advN p j (a + b) = advN (fst (advN p j a)) (snd (advN p j a)) b.
Proof. induction a; intros; cbn; auto. Qed.
Lemma passN_add a : forall b p j, passN p (a + b) = passN p a + passN (fst (advN p j a)) b.
Proof. induction a; intros; cbn; auto. rewrite (IHa b (nxt p) (j + inc p)). lia. Qed.
Lemma advN_shift y : forall p j k, advN p (j + k) y = (fst (advN p j y), snd (advN p j y) + k).
Proof. induction y; intros; cbn; auto. rewrite <- IHy. f_equal. lia. Qed.
Lemma adv16 p j : p < 16 -> advN p j 16 = (p, j + 4).
Proof.
  intros H. replace j with (0 + j) by lia. rewrite advN_shift.
  assert (E : advN p 0 16 = (p, 4)) by (do 16 (destruct p as [|p]; [reflexivity|]); lia).
  rewrite E. cbn [fst snd]. f_equal. lia.
Qed.
Lemma pass16 p : p < 16 -> passN p 16 = 6.
Proof. intros H. do 16 (destruct p as [|p]; [reflexivity|]). lia. Qed.
Lemma adv16q p j q : p < 16 -> advN p j (16 * q) = (p, j + 4 * q).
Proof.
  intros H. induction q. { cbn. f_equal; lia. }
  replace (16 * S q) with (16 * q + 16) by lia. rewrite advN_add, IHq. cbn [fst snd].
  rewrite adv16 by auto. f_equal; lia.
Qed.
Lemma pass16q p q : p < 16 -> passN p (16 * q) = 6 * q.
Proof.
  intros H. induction q. { reflexivity. }
  replace (16 * S q) with (16 * q + 16) by lia. rewrite (passN_add _ _ _ 0), IHq, (adv16q p 0 q H).
  cbn [fst]. rewrite pass16 by auto. lia.
Qed.

(** The same with the block counts and hit numbers in binary. *)
Local Open Scope N_scope.
Fixpoint posN (p : nat) (r : nat) : nat := match r with O => p | S r => posN (nxt p) r end.
Fixpoint incN (p : nat) (r : nat) : nat := match r with O => O | S r => (inc p + incN (nxt p) r)%nat end.
Definition advF (p : nat) (j y : N) : nat * N :=
  let r := N.to_nat (N.land y 15) in (posN p r, j + 4 * N.shiftr y 4 + N.of_nat (incN p r)).
Definition passF (p : nat) (y : N) : N := 6 * N.shiftr y 4 + N.of_nat (passN p (N.to_nat (N.land y 15))).
Local Close Scope N_scope.

Lemma advN_pos r : forall p j, advN p j r = (posN p r, j + incN p r).
Proof. induction r; intros; cbn; [f_equal; lia|]. rewrite IHr. f_equal. lia. Qed.

Lemma shr4 (y : N) : N.shiftr y 4 = (y / 16)%N.
Proof. rewrite N.shiftr_div_pow2. reflexivity. Qed.
Lemma land15 (y : N) : N.land y 15 = (y mod 16)%N.
Proof. change 15%N with (N.ones 4). rewrite N.land_ones. reflexivity. Qed.
Lemma split16 (y : N) : N.to_nat y = 16 * N.to_nat (N.shiftr y 4) + N.to_nat (N.land y 15).
Proof. rewrite shr4, land15. pose proof (N.div_mod y 16). lia. Qed.

Lemma advF_ok p j y : p < 16 ->
  advN p (N.to_nat j) (N.to_nat y) = (fst (advF p j y), N.to_nat (snd (advF p j y))).
Proof.
  intros H. unfold advF. rewrite (split16 y), advN_add, adv16q by auto.
  cbn [fst snd]. rewrite advN_pos. f_equal. lia.
Qed.
Lemma passF_ok p y : p < 16 -> N.to_nat (passF p y) = passN p (N.to_nat y).
Proof.
  intros H. unfold passF. rewrite (split16 y), (passN_add _ _ _ 0), pass16q, (adv16q p 0) by auto.
  cbn [fst]. lia.
Qed.

(** * A list of levels: the levels are transparent *)

Fixpoint Stack (ls : list (nat * N)) (Y : side) : side :=
  match ls with [] => Y | (p, j) :: ls => W p (N.to_nat j) (Stack ls Y) end.
Fixpoint advS (ls : list (nat * N)) (y : N) : list (nat * N) * N :=
  match ls with
  | [] => ([], y)
  | (p, j) :: ls => let r := advS ls (passF p y) in (advF p j y :: fst r, snd r)
  end.
Fixpoint tailKind (t : Kind) (ls : list (nat * N)) : Kind :=
  match ls with [] => t | (p, _) :: ls => tailKind (firstPass p) ls end.
Definition keqb (a b : Kind) : bool := match a, b with KH, KH | KV, KV => true | _, _ => false end.
Fixpoint chainOK (t : Kind) (ls : list (nat * N)) : bool :=
  match ls with
  | [] => true
  | (p, _) :: ls => (p <? 16) && keqb (kindOf p) t && chainOK (firstPass p) ls
  end.

Lemma keqb_ok a b : keqb a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.

Lemma stack_run ls : forall t y Y Y', chainOK t ls = true ->
  Run (tailKind t ls) (N.to_nat (snd (advS ls y))) Y Y' ->
  Run t (N.to_nat y) (Stack ls Y) (Stack (fst (advS ls y)) Y').
Proof.
  induction ls as [|[p j] ls IH]; intros t y Y Y' Hc H.
  - exact H.
  - cbn [chainOK] in Hc. apply andb_prop in Hc as [Hc Hc']. apply andb_prop in Hc as [Hp Hk].
    apply Nat.ltb_lt in Hp. apply keqb_ok in Hk. subst t.
    cbn [advS fst snd Stack tailKind] in *.
    pose proof (IH _ _ _ _ Hc' H) as IH'. rewrite passF_ok in IH' by auto.
    pose proof (level_run (N.to_nat y) p (N.to_nat j) _ _ Hp IH') as L.
    rewrite advF_ok in L by auto. cbn [fst snd] in L. destruct (advF p j y). exact L.
Qed.

Local Close Scope nat_scope.

(** * The front *)

Definition fOf (k : Kind) : list Sym := match k with KH => fH | KV => fV end.
Definition flipF (t : Kind) (y : N) : Kind := if N.even y then t else other t.

Lemma front_hit t Y Y' : Hit t Y Y' -> (fOf t *> Y) {{A}}> const 0 -->* (fOf (other t) *> Y') {{A}}> const 0.
Proof. destruct t; [apply frontH | apply frontV]. Qed.

Lemma other_other t : other (other t) = t.
Proof. destruct t; reflexivity. Qed.

Lemma front_run y : forall t Y Y', Run t y Y Y' ->
  (fOf t *> Y) {{A}}> const 0 -->* (fOf (if Nat.even y then t else other t) *> Y') {{A}}> const 0.
Proof.
  induction y as [|y IH]; intros t Y Y' H.
  - cbn in *. subst. apply evstep_refl.
  - destruct H as (Y1 & Hh & Hr). eapply evstep_trans; [apply front_hit, Hh|].
    specialize (IH _ _ _ Hr). rewrite Nat.even_succ, <- Nat.negb_even.
    destruct (Nat.even y); cbn in *; rewrite ?other_other in IH; exact IH.
Qed.

Lemma front_runN y t Y Y' : Run t (N.to_nat y) Y Y' ->
  (fOf t *> Y) {{A}}> const 0 -->* (fOf (flipF t y) *> Y') {{A}}> const 0.
Proof.
  intros H. pose proof (front_run _ _ _ _ H) as F. unfold flipF.
  replace (N.even y) with (Nat.even (N.to_nat y)); auto.
  destruct (N.Even_or_Odd y) as [[k ->]|[k ->]].
  - rewrite N.even_mul. replace (N.to_nat (2 * k)%N) with (2 * N.to_nat k)%nat by lia.
    rewrite Nat.even_mul. reflexivity.
  - replace (N.even (2 * k + 1)) with false by (rewrite N.add_comm, N.even_add_mul_2; reflexivity). replace (N.to_nat (2 * k + 1)%N) with (S (2 * N.to_nat k)) by lia.
    rewrite Nat.even_succ, <- Nat.negb_even, Nat.even_mul. reflexivity.
Qed.

End P4_part.

Notation zs := (@const Sym S0).

Section P5_part.

(** * Runs on finitely many cells, by evaluation *)

Definition hdl (l : list Sym) : Sym := match l with [] => S0 | x :: _ => x end.
Definition tll (l : list Sym) : list Sym := match l with [] => [] | _ :: l => l end.

Lemma hd_app l : hd (l *> zs) = hdl l.
Proof. destruct l; reflexivity. Qed.
Lemma tl_app l : tl (l *> zs) = tll l *> zs.
Proof. destruct l; reflexivity. Qed.

Lemma step_R q x w q' l (r : side) : tm (q, x) = Some (w, R, q') ->
  (l *> zs) {{q}}> (x >> r) -[ tm ]-> ((w :: l) *> zs) {{q'}}> r.
Proof. intros H. apply step_right. exact H. Qed.

Lemma step_L q x w q' l (r : side) : tm (q, x) = Some (w, L, q') ->
  (l *> zs) {{q}}> (x >> r) -[ tm ]-> (tll l *> zs) {{q'}}> (hdl l >> w >> r).
Proof.
  intros H. pose proof (@step_left tm q q' x w (l *> zs) r H) as S.
  cbn [move_left] in S. rewrite hd_app, tl_app in S. exact S.
Qed.

(** Run on the cells [l] (left, blank beyond) and [rs] (from the head on) until the head leaves [rs] to the
    right. *)
Fixpoint crun (f : nat) (l rs : list Sym) (q : Q) : option (list Sym * Q) :=
  match f with
  | O => None
  | S f =>
    match rs with
    | [] => Some (l, q)
    | x :: rs =>
      match tm (q, x) with
      | None => None
      | Some (w, R, q') => crun f (w :: l) rs q'
      | Some (w, L, q') => crun f (tll l) (hdl l :: w :: rs) q'
      end
    end
  end.

Lemma crun_ok f : forall l rs q l' q', crun f l rs q = Some (l', q') ->
  forall R, (l *> zs) {{q}}> (rs *> R) -->* (l' *> zs) {{q'}}> R.
Proof.
  induction f as [|f IH]; intros l rs q l' q' H R; [discriminate|].
  destruct rs as [|x rs]; cbn [crun] in H.
  - injection H as <- <-. apply evstep_refl.
  - destruct (tm (q, x)) as [[[w []] q2]|] eqn:E; [| |discriminate].
    + eapply evstep_step; [apply step_L, E|]. apply (IH _ _ _ _ _ H R).
    + eapply evstep_step; [apply step_R, E|]. apply (IH _ _ _ _ _ H R).
Qed.

(** The same run when it ends in a halt before the head leaves [rs]. *)
Fixpoint hrun (f : nat) (l rs : list Sym) (q : Q) : bool :=
  match f with
  | O => false
  | S f =>
    match rs with
    | [] => false
    | x :: rs =>
      match tm (q, x) with
      | None => true
      | Some (w, R, q') => hrun f (w :: l) rs q'
      | Some (w, L, q') => hrun f (tll l) (hdl l :: w :: rs) q'
      end
    end
  end.

Lemma hrun_ok f : forall l rs q, hrun f l rs q = true ->
  forall R, halts tm ((l *> zs) {{q}}> (rs *> R)).
Proof.
  induction f as [|f IH]; intros l rs q H R; [discriminate|].
  destruct rs as [|x rs]; cbn [hrun] in H; [discriminate|].
  destruct (tm (q, x)) as [[[w []] q2]|] eqn:E.
  - eapply halts_evstep; [apply (IH _ _ _ H R)|]. eapply evstep_step; [apply step_L, E|]. apply evstep_refl.
  - eapply halts_evstep; [apply (IH _ _ _ H R)|]. eapply evstep_step; [apply step_R, E|]. apply evstep_refl.
  - apply halted_halts. cbn. exact E.
Qed.

(** A visit: from the head in [A] on the blank cell right of the cells [l], to the next time the head is in
    [A] on a cell that it has not visited yet.  [r] holds the visited cells from the head on. *)
Fixpoint vrun (f : nat) (l r : list Sym) (q : Q) (moved : bool) : option (list Sym) :=
  match f with
  | O => None
  | S f =>
    match r, q, moved with
    | [], A, true => Some l
    | _, _, _ =>
      match tm (q, hdl r) with
      | None => None
      | Some (w, R, q') => vrun f (w :: l) (tll r) q' true
      | Some (w, L, q') => vrun f (tll l) (hdl l :: w :: tll r) q' true
      end
    end
  end.

Lemma hdtl_app r : r *> zs = hdl r >> (tll r *> zs).
Proof. destruct r; cbn; auto. apply const_unfold. Qed.

Lemma vrun_ok f : forall l r q b l', vrun f l r q b = Some l' ->
  (l *> zs) {{q}}> (r *> zs) -->* (l' *> zs) {{A}}> zs.
Proof.
  induction f as [|f IH]; intros l r q b l' H; [discriminate|].
  cbn [vrun] in H.
  assert (K : (l *> zs) {{q}}> (r *> zs) -->* (l' *> zs) {{A}}> zs \/
              (match tm (q, hdl r) with
               | None => None
               | Some (w, R, q') => vrun f (w :: l) (tll r) q' true
               | Some (w, L, q') => vrun f (tll l) (hdl l :: w :: tll r) q' true
               end = Some l')).
  { destruct r, q, b; auto. left. injection H as <-. apply evstep_refl. }
  destruct K as [K|K]; [exact K|].
  rewrite (hdtl_app r).
  destruct (tm (q, hdl r)) as [[[w []] q2]|] eqn:E; [| |discriminate].
  - eapply evstep_step; [apply step_L, E|]. apply (IH _ (hdl l :: w :: tll r) _ _ _ K).
  - eapply evstep_step; [apply step_R, E|]. apply (IH _ _ _ _ _ K).
Qed.

(** * Calls and hits on cells *)

Definition callFuel : nat := Nat.pow 10 7.
Global Opaque callFuel.

Definition call1 (q q' : Q) (l : list Sym) : option (list Sym) :=
  match crun callFuel l [S1] q with
  | Some (S1 :: l', q2) => if q_eqb q2 q' then Some l' else None
  | _ => None
  end.

Lemma call1_ok q q' l l' : call1 q q' l = Some l' -> Call q q' (l *> zs) (l' *> zs).
Proof.
  unfold call1. destruct (crun callFuel l [S1] q) as [[[|[] l2] q2]|] eqn:E; try discriminate.
  destruct (q_eqb_spec q2 q'); [|discriminate]. intros H. injection H as <-. subst.
  intros R. apply (crun_ok _ _ _ _ _ _ E R).
Qed.

Definition halt1 (q : Q) (l : list Sym) : bool := hrun callFuel l [S1] q.
Lemma halt1_ok q l : halt1 q l = true -> HaltCall q (l *> zs).
Proof. intros H R. apply (hrun_ok _ _ _ _ H R). Qed.

Definition tailHit (k : Kind) (c : list Sym) : option (list Sym) :=
  match k, c with
  | KH, S1 :: l0 =>
    match call1 C E l0 with None => None | Some l1 =>
    match call1 E F l1 with None => None | Some l2 =>
    match call1 B E l2 with None => None | Some l3 =>
    match call1 C A l3 with None => None | Some l4 =>
    match call1 D E l4 with None => None | Some l5 => Some (S1 :: S1 :: S1 :: l5)
    end end end end end
  | KV, S1 :: l0 =>
    match call1 C E l0 with None => None | Some l1 => Some (List.app [S1;S1;S1;S1;S1;S1;S1] l1) end
  | _, _ => None
  end.

Lemma tailHit_ok k c c' : tailHit k c = Some c' -> Hit k (c *> zs) (c' *> zs).
Proof.
  unfold tailHit. destruct k, c as [|[] l0]; try discriminate.
  - destruct (call1 C E l0) as [l1|] eqn:E1; [|discriminate].
    destruct (call1 E F l1) as [l2|] eqn:E2; [|discriminate].
    destruct (call1 B E l2) as [l3|] eqn:E3; [|discriminate].
    destruct (call1 C A l3) as [l4|] eqn:E4; [|discriminate].
    destruct (call1 D E l4) as [l5|] eqn:E5; [|discriminate].
    intros H. injection H as <-.
    exists (l0 *> zs), (l1 *> zs), (l2 *> zs), (l3 *> zs), (l4 *> zs),
      (l5 *> zs).
    repeat split; try reflexivity; apply call1_ok; assumption.
  - destruct (call1 C E l0) as [l1|] eqn:E1; [|discriminate].
    intros H. injection H as <-.
    exists (l0 *> zs), (l1 *> zs). repeat split; try reflexivity.
    apply call1_ok; assumption.
Qed.

(** * Hits that halt *)

Inductive HK := HKC | HK4.
Definition Dies (h : HK) : side -> Prop := match h with HKC => HC | HK4 => H4 end.

Definition tailHalt (k : Kind) (c : list Sym) : option HK :=
  match k, c with
  | KH, S1 :: l0 =>
    match call1 C E l0 with None => None | Some l1 =>
    match call1 E F l1 with None => None | Some l2 =>
    match call1 B E l2 with None => None | Some l3 =>
    if halt1 C l3 then Some HK4 else None
    end end end
  | KV, S1 :: l0 => if halt1 C l0 then Some HKC else None
  | _, _ => None
  end.

Lemma tailHalt_ok k c h : tailHalt k c = Some h -> Dies h (c *> zs).
Proof.
  unfold tailHalt. destruct k, c as [|[] l0]; try discriminate.
  - destruct (call1 C E l0) as [l1|] eqn:E1; [|discriminate].
    destruct (call1 E F l1) as [l2|] eqn:E2; [|discriminate].
    destruct (call1 B E l2) as [l3|] eqn:E3; [|discriminate].
    destruct (halt1 C l3) eqn:E4; [|discriminate]. intros H. injection H as <-.
    exists (l0 *> zs), (l1 *> zs), (l2 *> zs), (l3 *> zs).
    repeat split; try reflexivity; try (apply call1_ok; assumption). apply halt1_ok; assumption.
  - destruct (halt1 C l0) eqn:E4; [|discriminate]. intros H. injection H as <-.
    exists (l0 *> zs). split; [reflexivity|]. apply halt1_ok; assumption.
Qed.

Definition haltTab (p : nat) (h : HK) : option HK :=
  match p, h with
  | 2%nat, HK4 => Some HKC | 2%nat, HKC => Some HKC | 4%nat, HKC => Some HK4
  | 7%nat, HK4 => Some HKC | 7%nat, HKC => Some HKC | 10%nat, HKC => Some HKC
  | 12%nat, HK4 => Some HK4 | 12%nat, HKC => Some HK4 | 15%nat, HKC => Some HKC
  | _, _ => None
  end.

Lemma level_halt p j h h' Y : haltTab p h = Some h' -> Dies h Y -> Dies h' (W p j Y).
Proof.
  intros E D.
  do 16 (destruct p as [|p]; [destruct h; cbn in E; try discriminate; injection E as <-; cbn in D |- *;
    first [ exact (halt2_H4 _ _ D) | exact (halt2_HC _ _ D) | exact (halt4_HC _ _ D) | exact (halt7_H4 _ _ D)
          | exact (halt7_HC _ _ D) | exact (halt10_HC _ _ D) | exact (halt12_H4 _ _ D) | exact (halt12_HC _ _ D)
          | exact (halt15_HC _ _ D) ]|]).
  destruct h; discriminate.
Qed.

Fixpoint haltUp (ls : list (nat * N)) (h : HK) : option HK :=
  match ls with
  | [] => Some h
  | (p, j) :: ls => match haltUp ls h with None => None | Some h1 => haltTab p h1 end
  end.

Lemma haltUp_ok ls : forall h h' Y, haltUp ls h = Some h' -> Dies h Y -> Dies h' (Stack ls Y).
Proof.
  induction ls as [|[p j] ls IH]; intros h h' Y E D; cbn in E.
  - injection E as <-. exact D.
  - destruct (haltUp ls h) as [h1|] eqn:E1; [|discriminate].
    cbn [Stack]. eapply level_halt; [exact E|]. eapply IH; eauto.
Qed.

Definition frontHalt (t : Kind) (h : HK) : bool :=
  match t, h with KH, _ => true | KV, HKC => true | KV, HK4 => false end.

Lemma frontHalt_ok t h Y : frontHalt t h = true -> Dies h Y -> halts tm ((fOf t *> Y) {{A}}> zs).
Proof.
  destruct t, h; cbn; intros E D; try discriminate.
  - apply frontH_HC, D.
  - apply frontH_H4, D.
  - apply frontV_HC, D.
Qed.

End P5_part.

Section P6_part.

(** * The accelerated run *)

(** A state of the run at a visit: the front (if the cells start with one), the levels (position, blocks - 1)
    outermost first, and the cells left of them down to the blank left end. *)
Record St := mkS { fr : option Kind; lvs : list (nat * N); cells : list Sym }.
Definition frontC (o : option Kind) : list Sym := match o with Some k => fOf k | None => [] end.
Definition cfg (s : St) : Q * tape := (frontC (fr s) *> Stack (lvs s) (cells s *> zs)) {{A}}> zs.
Definition Reach (s : St) : Prop := c0 -->* cfg s.

(** [m] hits on the cells, alternately of the two kinds. *)
Fixpoint tailRun (k : Kind) (m : nat) (c : list Sym) : option (list Sym) :=
  match m with
  | O => Some c
  | S m => match tailHit k c with Some c' => tailRun (other k) m c' | None => None end
  end.
Lemma tailRun_ok m : forall k c c', tailRun k m c = Some c' -> Run k m (c *> zs) (c' *> zs).
Proof.
  induction m as [|m IH]; intros k c c' H; cbn in H |- *.
  - injection H as <-. reflexivity.
  - destruct (tailHit k c) as [c1|] eqn:E; [|discriminate].
    exists (c1 *> zs). split; [apply tailHit_ok, E | apply IH, H].
Qed.

Definition maxBatch : N := 1000%N.

(** [y] hits from the front; the hits that reach the cells are simulated on them. *)
Definition opAdv (s : St) (y : N) : option St :=
  match fr s with
  | None => None
  | Some t =>
    if chainOK t (lvs s) then
      let (ls', m) := advS (lvs s) y in
      if (m <=? maxBatch)%N then
        match tailRun (tailKind t (lvs s)) (N.to_nat m) (cells s) with
        | Some c' => Some (mkS (Some (flipF t y)) ls' c')
        | None => None
        end
      else None
    else None
  end.

Lemma opAdv_ok s y s' : Reach s -> opAdv s y = Some s' -> Reach s'.
Proof.
  unfold opAdv, Reach, cfg. intros Hr H. destruct (fr s) as [t|]; [|discriminate].
  destruct (chainOK t (lvs s)) eqn:Hc; [|discriminate].
  destruct (advS (lvs s) y) as [ls' m] eqn:Ea.
  destruct (m <=? maxBatch)%N; [|discriminate].
  destruct (tailRun (tailKind t (lvs s)) (N.to_nat m) (cells s)) as [c'|] eqn:Et; [|discriminate].
  injection H as <-. unfold cfg. cbn [fr lvs cells frontC].
  pose proof (stack_run (lvs s) t y (cells s *> zs) (c' *> zs) Hc) as SR. rewrite Ea in SR. cbn [fst snd] in SR.
  eapply evstep_trans; [exact Hr|]. apply front_runN. apply SR, tailRun_ok, Et.
Qed.

(** [strip w l = Some r] when [l = w ++ r]. *)
Fixpoint strip (w l : list Sym) : option (list Sym) :=
  match w, l with
  | [], l => Some l
  | _ :: _, [] => None
  | a :: w, b :: l => if sym_eqb a b then strip w l else None
  end.
Lemma strip_ok w : forall l r, strip w l = Some r -> l = List.app w r.
Proof.
  induction w as [|a w IH]; intros l r H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct l as [|b l]; [discriminate|]. destruct (sym_eqb_spec a b); [|discriminate].
    subst. cbn. f_equal. apply IH, H.
Qed.

Definition wList (p : nat) (j : N) : list Sym := List.app (blk ^^ S (N.to_nat j)) (sepL p).
Lemma W_list p j l : W p (N.to_nat j) (l *> zs) = List.app (wList p j) l *> zs.
Proof. unfold W, wList. rewrite !Str_app_assoc. reflexivity. Qed.
Lemma Stack_snoc ls : forall p j Y, Stack (List.app ls [(p, j)]) Y = Stack ls (W p (N.to_nat j) Y).
Proof. induction ls as [|[p' j'] ls IH]; intros; cbn; auto. rewrite IH. reflexivity. Qed.

(** Read the first cells as a level. *)
Definition opPeel (s : St) (p : nat) (j : N) : option St :=
  match strip (wList p j) (cells s) with
  | Some r => Some (mkS (fr s) (List.app (lvs s) [(p, j)]) r)
  | None => None
  end.
Lemma opPeel_ok s p j s' : Reach s -> opPeel s p j = Some s' -> Reach s'.
Proof.
  unfold opPeel, Reach, cfg. intros Hr H.
  destruct (strip (wList p j) (cells s)) as [r|] eqn:E; [|discriminate]. injection H as <-.
  cbn [fr lvs cells]. rewrite Stack_snoc, W_list, <- (strip_ok _ _ _ E). exact Hr.
Qed.

(** Write the deepest level out as cells. *)
Definition opUnpeel (s : St) : option St :=
  match List.rev (lvs s) with
  | [] => None
  | (p, j) :: r => Some (mkS (fr s) (List.rev r) (List.app (wList p j) (cells s)))
  end.
Lemma opUnpeel_ok s s' : Reach s -> opUnpeel s = Some s' -> Reach s'.
Proof.
  unfold opUnpeel, Reach, cfg. intros Hr H.
  destruct (List.rev (lvs s)) as [|[p j] r] eqn:E; [discriminate|]. injection H as <-.
  cbn [fr lvs cells].
  assert (E' : lvs s = List.app (List.rev r) [(p, j)]).
  { rewrite <- (List.rev_involutive (lvs s)), E. reflexivity. }
  rewrite E', Stack_snoc, W_list in Hr. exact Hr.
Qed.

(** The front starts the cells (no levels yet). *)
Definition opSplit (s : St) (k : Kind) : option St :=
  match fr s, lvs s with
  | None, [] => match strip (fOf k) (cells s) with Some r => Some (mkS (Some k) [] r) | None => None end
  | _, _ => None
  end.
Lemma opSplit_ok s k s' : Reach s -> opSplit s k = Some s' -> Reach s'.
Proof.
  unfold opSplit, Reach, cfg. intros Hr H.
  destruct (fr s); [discriminate|]. destruct (lvs s); [|discriminate].
  destruct (strip (fOf k) (cells s)) as [r|] eqn:E; [|discriminate]. injection H as <-.
  cbn [fr lvs cells frontC Stack] in *. rewrite (strip_ok _ _ _ E) in Hr. cbn [List.app Str_app] in Hr. rewrite Str_app_assoc in Hr. exact Hr.
Qed.

(** A plain visit on the cells (no levels). *)
Definition visitFuel : nat := Nat.pow 10 7.
Global Opaque visitFuel.
Definition opRaw (s : St) : option St :=
  match lvs s with
  | [] => match vrun visitFuel (List.app (frontC (fr s)) (cells s)) [] A false with
          | Some l => Some (mkS None [] l)
          | None => None
          end
  | _ => None
  end.
Lemma opRaw_ok s s' : Reach s -> opRaw s = Some s' -> Reach s'.
Proof.
  unfold opRaw, Reach, cfg. intros Hr H. destruct (lvs s); [|discriminate].
  destruct (vrun visitFuel (List.app (frontC (fr s)) (cells s)) [] A false) as [l|] eqn:E; [|discriminate].
  injection H as <-. cbn [fr lvs cells frontC Stack] in *.
  eapply evstep_trans; [exact Hr|]. rewrite <- Str_app_assoc. exact (vrun_ok _ _ _ _ _ _ E).
Qed.

(** The next hit halts. *)
Definition opFinal (s : St) : bool :=
  match fr s with
  | None => false
  | Some t =>
    match tailHalt (tailKind t (lvs s)) (cells s) with
    | None => false
    | Some h => match haltUp (lvs s) h with None => false | Some h' => frontHalt t h' end
    end
  end.
Lemma opFinal_ok s : Reach s -> opFinal s = true -> halts tm c0.
Proof.
  unfold opFinal, Reach, cfg. intros Hr H. destruct (fr s) as [t|]; [|discriminate].
  destruct (tailHalt (tailKind t (lvs s)) (cells s)) as [h|] eqn:E1; [|discriminate].
  destruct (haltUp (lvs s) h) as [h'|] eqn:E2; [|discriminate].
  eapply halts_evstep; [|exact Hr]. cbn [frontC].
  apply (frontHalt_ok t h' (Stack (lvs s) (cells s *> zs))); [exact H|]. eapply haltUp_ok; [exact E2|]. exact (tailHalt_ok _ _ _ E1).
Qed.

(** * The parts of the run that need no proof: which levels to read, how many hits to jump *)

Fixpoint cntBlocks (f : nat) (l : list Sym) (n : N) : N * list Sym :=
  match f with
  | O => (n, l)
  | S f => match strip blk l with Some r => cntBlocks f r (N.succ n) | None => (n, l) end
  end.
Definition keq (a b : Kind) : bool := keqb a b.
Fixpoint findSep (k : Kind) (l : list Sym) (ps : list nat) : option nat :=
  match ps with
  | [] => None
  | p :: ps => if andb (keq (kindOf p) k) (match strip (sepL p) l with Some _ => true | None => false end)
               then Some p else findSep k l ps
  end.
Definition allPos : list nat := List.seq 0 16.
Definition parsePeel (k : Kind) (c : list Sym) : option (nat * N) :=
  match cntBlocks (List.length c) c 0%N with
  | (0%N, _) => None
  | (n, r) => match findSep k r allPos with Some p => Some (p, N.pred n) | None => None end
  end.
Fixpoint peelAll (f : nat) (s : St) : St :=
  match f with
  | O => s
  | S f =>
    match fr s with
    | None => s
    | Some t =>
      match parsePeel (tailKind t (lvs s)) (cells s) with
      | None => s
      | Some (p, j) => match opPeel s p j with None => s | Some s' => peelAll f s' end
      end
    end
  end.
Lemma peelAll_ok f : forall s, Reach s -> Reach (peelAll f s).
Proof.
  induction f as [|f IH]; intros s Hr; cbn; auto.
  destruct (fr s); auto. destruct (parsePeel _ _) as [[p j]|]; auto.
  destruct (opPeel s p j) eqn:E; auto. apply IH. eapply opPeel_ok; eauto.
Qed.

Definition isPass (p : nat) : bool := match passOf p with Some _ => true | None => false end.
Fixpoint distPass (f p : nat) : nat :=
  match f with O => O | S f => if isPass p then O else S (distPass f (nxt p)) end.
Fixpoint walk (f p r : nat) : nat :=
  match f with
  | O => O
  | S f => match r with O => O | _ => S (walk f (nxt p) (if isPass p then pred r else r)) end
  end.
(** Division by 6 in one pass over the bits (no proof needed: [need] only steers the run). *)
Fixpoint pdiv6 (p : positive) : N * nat :=
  match p with
  | xH => (0%N, 1%nat)
  | xO p => let (q, r) := pdiv6 p in
            if (r + r <? 6)%nat then (N.double q, (r + r)%nat) else (N.succ_double q, (r + r - 6)%nat)
  | xI p => let (q, r) := pdiv6 p in
            if (S (r + r) <? 6)%nat then (N.double q, S (r + r)) else (N.succ_double q, (S (r + r) - 6)%nat)
  end.
Definition div6 (x : N) : N * nat := match x with N0 => (0%N, 0%nat) | Npos p => pdiv6 p end.
Definition need (p : nat) (x : N) : N :=
  match x with
  | N0 => 0%N
  | _ => let (q, r) := div6 (N.pred x) in (N.shiftl q 4 + N.of_nat (walk 40 p (S r)))%N
  end.
(** The hits from the front after which the cells have had [m] more hits. *)
Definition hitsFor (ls : list (nat * N)) (m : N) : N :=
  List.fold_left (fun e pj => need (fst pj) e) (List.rev ls) m.
(** How many hits in a row the cells take as the levels expect (at most [cap]). *)
Fixpoint regular (cap : nat) (k : Kind) (c : list Sym) : nat :=
  match cap with
  | O => O
  | S cap => match tailHit k c with Some c' => S (regular cap (other k) c') | None => O end
  end.
Definition batchCap : nat := 100.
Definition readyCount (ls : list (nat * N)) : N :=
  List.fold_left (fun e pj => let y := need (fst pj) e in
                   (y + N.of_nat (distPass 16 (posN (fst pj) (N.to_nat (N.land y 15)))))%N) (List.rev ls) 0%N.

(** The run.  With [true]: read the levels off the cells, find how many hits the cells take as the levels
    expect, and make that many in one jump; if none, move every level to where it passes the next hit on
    and continue with [false].  With [false]: the next hit halts, or the deepest level is written out as
    cells and the cells are tried again; with no levels left, a plain visit. *)
Fixpoint loop (f : nat) (b : bool) (s : St) : bool :=
  match f with
  | O => false
  | S f =>
    if b then
      match fr s with
      | None =>
        match opSplit s KH with Some s' => loop f true s' | None =>
        match opSplit s KV with Some s' => loop f true s' | None =>
        match opRaw s with Some s' => loop f true s' | None => false end end end
      | Some t =>
        let s1 := peelAll 100 s in
        match regular batchCap (tailKind t (lvs s1)) (cells s1) with
        | O => match opAdv s1 (readyCount (lvs s1)) with Some s2 => loop f false s2 | None => false end
        | m => match opAdv s1 (hitsFor (lvs s1) (N.of_nat m)) with Some s2 => loop f true s2 | None => false end
        end
      end
    else
      if opFinal s then true else
      match fr s with
      | None => false
      | Some t =>
        match opUnpeel s with
        | Some s4 =>
          match regular batchCap (tailKind t (lvs s4)) (cells s4) with
          | O => loop f false s4
          | m => match opAdv s4 (hitsFor (lvs s4) (N.of_nat m)) with Some s5 => loop f true s5 | None => false end
          end
        | None => match opRaw s with Some s5 => loop f true s5 | None => false end
        end
      end
  end.

Lemma loop_ok f : forall b s, Reach s -> loop f b s = true -> halts tm c0.
Proof.
  induction f as [|f IH]; intros b s Hr H; cbn [loop] in H; [discriminate|].
  destruct b.
  - destruct (fr s) as [t|] eqn:Ef.
    + destruct (regular _ _ _) as [|m].
      * destruct (opAdv (peelAll 100 s) _) as [s2|] eqn:E; [|discriminate].
        eapply IH; [|exact H]. eapply opAdv_ok; [apply peelAll_ok, Hr|exact E].
      * destruct (opAdv (peelAll 100 s) _) as [s2|] eqn:E; [|discriminate].
        eapply IH; [|exact H]. eapply opAdv_ok; [apply peelAll_ok, Hr|exact E].
    + destruct (opSplit s KH) as [s'|] eqn:E1; [eapply IH; [eapply opSplit_ok; eauto|exact H]|].
      destruct (opSplit s KV) as [s'|] eqn:E2; [eapply IH; [eapply opSplit_ok; eauto|exact H]|].
      destruct (opRaw s) as [s'|] eqn:E3; [eapply IH; [eapply opRaw_ok; eauto|exact H]|discriminate].
  - destruct (opFinal s) eqn:Ef; [eapply opFinal_ok; eauto|].
    destruct (fr s) as [t|]; [|discriminate].
    destruct (opUnpeel s) as [s4|] eqn:E4.
    + assert (R4 : Reach s4) by (eapply opUnpeel_ok; eauto).
      destruct (regular _ _ _) as [|m]; [eapply IH; eauto|].
      destruct (opAdv s4 _) as [s5|] eqn:E5; [|discriminate].
      eapply IH; [eapply opAdv_ok; eauto|exact H].
    + destruct (opRaw s) as [s5|] eqn:E5; [eapply IH; [eapply opRaw_ok; eauto|exact H]|discriminate].
Qed.
Definition s0 : St := mkS None [] [].
Lemma reach0 : Reach s0.
Proof. unfold Reach, cfg, s0. cbn. apply evstep_refl'. reflexivity. Qed.

End P6_part.

Theorem halt : halts tm c0.
Proof.
  apply (loop_ok 10000 true s0 reach0).
  native_cast_no_check (eq_refl true).
Time Qed.

Print Assumptions halt.
