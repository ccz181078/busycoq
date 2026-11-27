(** * 1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC--- does not halt

    BB(6) holdout (bbchallenge #32641).  After 16,730,681,219 steps from the blank tape the machine is a
    bouncer with a fixed far end: with [P = 1010001000100] (13 cells),

      [Cyc X k  =  0^inf A> 0 P^k X 0^inf]

    where [X] is a fixed stretch of 222,182 cells.  The run reaches [Cyc X 7], and from [Cyc X (n+1)] it
    reaches [Cyc X (n+2)]: the head sweeps right over the [P] blocks, makes an excursion of 1,517,479 steps
    into [X], sweeps back to the left end, sweeps right again, makes a second excursion of 1,511,551 steps
    into [X], and sweeps back.  The two excursions leave [X] as it was, with one more [P] in front of it.

    The proof has two parts.
    - [period]: for every [X] that passes [excs] (two finite runs on [X], checked by computation),
      [Cyc X (S n) -->+ Cyc X (S (S n))] for all [n].  The sweeps over the [P] blocks are three shift rules,
      proved by induction.
    - the run from the blank tape: a block macro simulator ([mrun], blocks of 32 cells, a table of block
      transitions filled in as it goes, sound by [mrun_ok]) makes [N] = 522,833,539 block crossings.
      [check] reads [X] off the configuration it reaches and tests [excs X].

    [final_ok : check final = true] is the only computation.  No tape data is written in this file: only the
    machine and the numbers [N], [n1], [n2].  The same argument was found independently in an informal
    proof (gap-word rewriting, period block 2443) posted on the bbchallenge Discord in November 2026. *)

From Coq Require Import Lists.List PArith FMapPositive String.
From BusyCoq Require Import Individual62.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm := Eval compute in (TM_from_str "1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC---").

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma iter_inv {X : Type} (P : X -> Prop) (f : X -> X) :
  (forall x, P x -> P (f x)) -> forall n x, P x -> P (Pos.iter f x n).
Proof.
  intros Hf. induction n as [n IH | n IH |]; intros x Hx; cbn [Pos.iter].
  - apply Hf, IH, IH, Hx.
  - apply IH, IH, Hx.
  - apply Hf, Hx.
Qed.

(** ** A window of cells

    [mkW l r q true]: the head is in state [q] on the first cell of [r], [l] is on its left (nearest cell
    first).  [mkW l r q false]: the head is on the first cell of [l], [r] is on its right.  A run inside the
    window is a run of the machine, whatever lies outside it. *)

Record W := mkW { wl : list sym; wr : list sym; wq : Q; wf : bool }.

Definition wsem (Lt Rt : side) (c : W) : Q * tape :=
  if wf c then (wl c *> Lt) {{wq c}}> (wr c *> Rt) else (wl c *> Lt) <{{wq c}} (wr c *> Rt).

Definition wstep (c : W) : option W :=
  match c with
  | mkW l r q true =>
    match r with
    | [] => None
    | s :: r =>
      match tm (q, s) with
      | Some (s', R, q') => Some (mkW (s' :: l) r q' true)
      | Some (s', L, q') => Some (mkW l (s' :: r) q' false)
      | None => None
      end
    end
  | mkW l r q false =>
    match l with
    | [] => None
    | s :: l =>
      match tm (q, s) with
      | Some (s', R, q') => Some (mkW (s' :: l) r q' true)
      | Some (s', L, q') => Some (mkW l (s' :: r) q' false)
      | None => None
      end
    end
  end.

Lemma wstep_ok c c' Lt Rt : wstep c = Some c' -> wsem Lt Rt c --> wsem Lt Rt c'.
Proof.
  intros H. destruct c as [l r q [|]]; [destruct r as [| s r] | destruct l as [| s l]];
    cbn [wstep] in H; try discriminate H;
    destruct (tm (q, s)) as [[[s' []] q'] |] eqn:E; inversion H; subst c';
    first [exact (step_left E) | exact (step_right E)].
Qed.

Definition wrun (n : positive) (c : W) : W :=
  Pos.iter (fun c => match wstep c with Some c' => c' | None => c end) c n.

Lemma wrun_ok n c Lt Rt : wsem Lt Rt c -->* wsem Lt Rt (wrun n c).
Proof.
  apply (iter_inv (fun d => wsem Lt Rt c -->* wsem Lt Rt d)); [| apply evstep_refl].
  intros x Hx. destruct (wstep x) as [x' |] eqn:E; [| exact Hx].
  eapply evstep_trans; [exact Hx |]. apply evstep_one, wstep_ok, E.
Qed.

(** Run until the head leaves the window. *)
Fixpoint brun (fuel : nat) (c : W) : option W :=
  match fuel with
  | O => None
  | S fuel =>
    match c with
    | mkW _ [] _ true | mkW [] _ _ false => Some c
    | _ => match wstep c with Some c' => brun fuel c' | None => None end
    end
  end.

Lemma brun_ok fuel c c' Lt Rt : brun fuel c = Some c' -> wsem Lt Rt c -->* wsem Lt Rt c'.
Proof.
  revert c. induction fuel as [| fuel IH]; intros c H; [discriminate |].
  cbn [brun] in H.
  assert (G : c' = c \/ exists d, wstep c = Some d /\ brun fuel d = Some c').
  { destruct c as [[| sl l] [| sr r] q [|]];
      first [ left; congruence | right; destruct (wstep _) as [d |]; [| discriminate]; eauto ]. }
  destruct G as [-> | [d [H1 H2]]]; [apply evstep_refl |].
  eapply evstep_step; [apply wstep_ok, H1 |]. apply IH, H2.
Qed.

(** ** Blocks

    A block is a [positive]: its bits are its cells, lowest bit first, and the top bit is a sentinel. *)

Fixpoint dec (p : positive) : list sym :=
  match p with xH => [] | xO p => 0 :: dec p | xI p => 1 :: dec p end.
Fixpoint enc (l : list sym) : positive :=
  match l with [] => xH | 0 :: l => xO (enc l) | 1 :: l => xI (enc l) end.
Lemma dec_enc l : dec (enc l) = l.
Proof. induction l as [| [|] l IH]; cbn [enc dec]; congruence. Qed.

(** What the machine does with one block: the head leaves it on the right ([ER], the new block read from
    its right end) or on the left ([EL], read from its left end), in a new state. *)
Inductive Ent := ER (b : positive) (q : Q) | EL (b : positive) (q : Q).

Definition FUEL := 4000.

(** [f = true]: the head enters [b] on its first cell, from the left; [f = false]: on its last cell, from
    the right, and [b] is then read right to left. *)
Definition entry (q : Q) (f : bool) (b : positive) : option Ent :=
  match brun FUEL (if f then mkW [] (dec b) q true else mkW (dec b) [] q false) with
  | Some (mkW l r q' true) => match r with [] => Some (ER (enc l) q') | _ => None end
  | Some (mkW l r q' false) => match l with [] => Some (EL (enc r) q') | _ => None end
  | None => None
  end.

Definition ent_sem (e : Ent) (Lt Rt : side) : Q * tape :=
  match e with ER b q => (dec b *> Lt) {{q}}> Rt | EL b q => Lt <{{q}} (dec b *> Rt) end.

Lemma entry_ok q f b e Lt Rt : entry q f b = Some e ->
  (if f then Lt {{q}}> (dec b *> Rt) else (dec b *> Lt) <{{q}} Rt) -->* ent_sem e Lt Rt.
Proof.
  unfold entry. intros H.
  destruct (brun _ _) as [[l r q' []] |] eqn:G; [destruct r | destruct l |]; cbn in H; try discriminate H;
    injection H as <-; cbn [ent_sem]; rewrite dec_enc; destruct f; exact (brun_ok _ _ _ Lt Rt G).
Qed.

(** ** The macro simulator

    It keeps a table of the entries it has computed, indexed by state, side and block. *)

Definition key (q : Q) (f : bool) (b : positive) : positive :=
  let b := if f then xI b else xO b in
  match q with
  | A => b~0~0~0 | B => b~0~0~1 | C => b~0~1~0 | D => b~0~1~1 | E => b~1~0~0 | F => b~1~0~1
  end.

Lemma key_inj q f b q' f' b' : key q f b = key q' f' b' -> q = q' /\ f = f' /\ b = b'.
Proof. destruct q, q', f, f'; cbn; intros H; inversion H; auto. Qed.

Definition Tab := PositiveMap.t Ent.

Definition tab_ok (t : Tab) : Prop :=
  forall q f b e, PositiveMap.find (key q f b) t = Some e -> entry q f b = Some e.

Definition look (t : Tab) (q : Q) (f : bool) (b : positive) : option Ent * Tab :=
  match PositiveMap.find (key q f b) t with
  | Some e => (Some e, t)
  | None =>
    match entry q f b with
    | Some e => (Some e, PositiveMap.add (key q f b) e t)
    | None => (None, t)
    end
  end.

Lemma look_ok t q f b o t' : tab_ok t -> look t q f b = (o, t') ->
  tab_ok t' /\ forall e, o = Some e -> entry q f b = Some e.
Proof.
  intros Ht. unfold look.
  destruct (PositiveMap.find (key q f b) t) as [e |] eqn:Hf.
  - intros H. injection H as <- <-. split; [exact Ht |]. intros e' He'. injection He' as <-. exact (Ht _ _ _ _ Hf).
  - destruct (entry q f b) as [e |] eqn:E; intros H; injection H as <- <-; [| split; [exact Ht | discriminate]].
    split; [| congruence].
    intros q1 f1 b1 e1. destruct (Pos.eq_dec (key q1 f1 b1) (key q f b)) as [Hk | Hk].
    + rewrite Hk, PositiveMap.gss. destruct (key_inj _ _ _ _ _ _ Hk) as [-> [-> ->]]. congruence.
    + rewrite PositiveMap.gso by exact Hk. apply Ht.
Qed.

(** A macro configuration: blocks on the left of the head (nearest first), blocks on its right, the state,
    and whether the head is about to enter the first right block ([true]) or the first left block. *)
Record MC := mkM { mL : list positive; mR : list positive; mq : Q; mf : bool }.

Fixpoint decs (bs : list positive) : side :=
  match bs with [] => const 0 | b :: bs => dec b *> decs bs end.

Definition msem (c : MC) : Q * tape :=
  if mf c then decs (mL c) {{mq c}}> decs (mR c) else decs (mL c) <{{mq c}} decs (mR c).

(** A blank block of 32 cells, used where the tape ends. *)
Definition bl : positive := 4294967296.

Lemma bl_blank : dec bl *> const 0 = const 0.
Proof. cbn. repeat rewrite <- const_unfold. reflexivity. Qed.

Definition after (e : Ent) (Ls Rs : list positive) : MC :=
  match e with ER b q => mkM (b :: Ls) Rs q true | EL b q => mkM Ls (b :: Rs) q false end.

(** The head enters block [b] in state [q] from side [f]; [Ls], [Rs] are the other blocks. *)
Definition cross (t : Tab) (q : Q) (f : bool) (b : positive) (Ls Rs : list positive) (c : MC) : Tab * MC :=
  match look t q f b with
  | (Some e, t') => (t', after e Ls Rs)
  | (None, t') => (t', c)
  end.

Definition mstep (x : Tab * MC) : Tab * MC :=
  let (t, c) := x in
  match c with
  | mkM Ls Rs q true =>
    match Rs with [] => cross t q true bl Ls [] c | b :: Rs => cross t q true b Ls Rs c end
  | mkM Ls Rs q false =>
    match Ls with [] => cross t q false bl [] Rs c | b :: Ls => cross t q false b Ls Rs c end
  end.

Lemma after_ok e Ls Rs : msem (after e Ls Rs) = ent_sem e (decs Ls) (decs Rs).
Proof. destruct e; reflexivity. Qed.

Lemma cross_ok (t : Tab) (q : Q) (f : bool) (b : positive) (Ls Rs : list positive) (c : MC) : tab_ok t ->
  msem c = (if f then decs Ls {{q}}> (dec b *> decs Rs) else (dec b *> decs Ls) <{{q}} decs Rs) ->
  tab_ok (fst (cross t q f b Ls Rs c)) /\ msem c -->* msem (snd (cross t q f b Ls Rs c)).
Proof.
  intros Ht Hs. unfold cross. destruct (look t q f b) as [o t'] eqn:E.
  destruct (look_ok _ _ _ _ _ _ Ht E) as [Ht' He]. split; [destruct o; exact Ht' |].
  destruct o as [e |]; [| apply evstep_refl].
  cbn [snd]. rewrite after_ok, Hs. apply entry_ok, He. reflexivity.
Qed.

Lemma mstep_ok t c : tab_ok t ->
  tab_ok (fst (mstep (t, c))) /\ msem c -->* msem (snd (mstep (t, c))).
Proof.
  intros Ht. destruct c as [[| b Ls] [| b' Rs] q []]; cbn [mstep]; apply cross_ok; try exact Ht;
    unfold msem; cbn [mf mL mR mq decs]; rewrite ?bl_blank; reflexivity.
Qed.

Definition mrun (n : positive) (x : Tab * MC) : Tab * MC := Pos.iter mstep x n.

Lemma mrun_ok n t c : tab_ok t -> msem c -->* msem (snd (mrun n (t, c))).
Proof.
  intros Ht.
  apply (iter_inv (fun x => tab_ok (fst x) /\ msem c -->* msem (snd x)) mstep);
    [| split; [exact Ht | apply evstep_refl]].
  intros [t' c'] [Ht' Hc]. destruct (mstep_ok t' c' Ht') as [H1 H2].
  split; [exact H1 |]. eapply evstep_trans; [exact Hc | exact H2].
Qed.

(** ** The period *)

(** The block, left to right; what the first sweep right leaves of it (read right to left); what the sweep
    back leaves of it. *)
Definition P : list sym := [1;0;1;0;0;0;1;0;0;0;1;0;0].
Definition P1 : list sym := [1;0;0;0;1;0;0;1;0;1;0;1;0].
Definition P2 : list sym := [1;0;0;0;1;0;0;0;1;0;0;1;0].

Definition Cyc (X : list sym) (k : nat) : Q * tape := const 0 {{A}}> (0 >> P ^^ k *> X *> const 0).

Lemma sweep1_once Lt Rt : Lt << 1 {{B}}> P *> Rt -->* (P1 *> Lt) << 1 {{B}}> Rt.
Proof. unfold P, P1. execute. Qed.

Lemma sweep1 n Lt Rt : Lt << 1 {{B}}> P ^^ n *> Rt -->* (P1 ^^ n *> Lt) << 1 {{B}}> Rt.
Proof.
  revert Lt. induction n as [| n IH]; intros Lt; [apply evstep_refl |].
  change (P ^^ S n) with (P ++ P ^^ n). rewrite Str_app_assoc.
  eapply evstep_trans; [apply sweep1_once |]. eapply evstep_trans; [apply IH |].
  rewrite lpow_shift'. apply evstep_refl.
Qed.

Lemma sweep2_once Lt Rt : (P1 *> Lt) {{E}}> (0 >> Rt) -->* Lt {{E}}> (0 >> P2 *> Rt).
Proof. unfold P1, P2. execute. Qed.

Lemma sweep2 n Lt Rt : (P1 ^^ n *> Lt) {{E}}> (0 >> Rt) -->* Lt {{E}}> (0 >> P2 ^^ n *> Rt).
Proof.
  revert Rt. induction n as [| n IH]; intros Rt; [apply evstep_refl |].
  change (P1 ^^ S n) with (P1 ++ P1 ^^ n). rewrite Str_app_assoc.
  eapply evstep_trans; [apply sweep2_once |]. eapply evstep_trans; [apply IH |].
  rewrite lpow_shift'. apply evstep_refl.
Qed.

Lemma rotate n (Rt : side) : 1 >> 0 >> P2 ^^ n *> Rt = P ^^ n *> 1 >> 0 >> Rt.
Proof.
  induction n as [| n IH]; [reflexivity |].
  change (P2 ^^ S n) with (P2 ++ P2 ^^ n). change (P ^^ S n) with (P ++ P ^^ n).
  rewrite !Str_app_assoc, <- IH. reflexivity.
Qed.

Lemma app_zeros (l : list sym) j : (l ++ repeat 0 j) *> const 0 = l *> const 0.
Proof.
  rewrite Str_app_assoc. f_equal.
  induction j as [| j IH]; cbn [repeat Str_app]; [reflexivity |].
  rewrite IH, <- const_unfold. reflexivity.
Qed.

(** The two excursions into [X] (with 32 blank cells after it): [n1] steps from [1 B> X], then [n2] steps
    from [0 1 1 B> r1], where [r1] is what the first one left.  Each must end in state [E], facing left, on
    the [0] next to the blocks; and then the stretch must be [X] again, one block further on. *)
Definition n1 : positive := 1517479.
Definition n2 : positive := 1511551.

Fixpoint leqb (a b : list sym) : bool :=
  match a, b with
  | [], [] => true
  | 0 :: a, 0 :: b => leqb a b
  | 1 :: a, 1 :: b => leqb a b
  | _, _ => false
  end.
Lemma leqb_ok a b : leqb a b = true -> a = b.
Proof.
  revert b. induction a as [| x a IH]; intros [| y b] H; cbn [leqb] in H; try discriminate; [reflexivity | |].
  - destruct x; discriminate.
  - destruct x, y; try discriminate; f_equal; apply IH, H.
Qed.

(** [w] ends in state [E], facing left, with one [0] left of the head, and [k] holds of what is right of it. *)
Definition ends (w : W) (k : list sym -> bool) : bool :=
  match w with
  | mkW [0] r E false => k r
  | _ => false
  end.

Lemma ends_ok w k : ends w k = true -> exists r, w = mkW [0] r E false /\ k r = true.
Proof.
  destruct w as [[| [|] [|]] r [] []]; cbn [ends]; try discriminate. eauto.
Qed.

Definition excs (X : list sym) : bool :=
  ends (wrun n1 (mkW [1] (X ++ repeat 0 32) B true)) (fun r1 =>
  ends (wrun n2 (mkW [1;1;0] r1 B true)) (fun r2 =>
  leqb ([1;0] ++ r2) (P ++ X ++ repeat 0 23))).

Theorem period X : excs X = true -> forall n, Cyc X (S n) -->+ Cyc X (S (S n)).
Proof.
  unfold excs. intros H.
  apply ends_ok in H as [r1 [E1 H]]. apply ends_ok in H as [r2 [E2 FC]]. apply leqb_ok in FC.
  intros n. unfold Cyc.
  assert (H1 : forall Lt, Lt << 1 {{B}}> X *> const 0 -->* Lt {{E}}> (0 >> r1 *> const 0)).
  { intros Lt. pose proof (wrun_ok n1 (mkW [1] (X ++ repeat 0 32) B true) Lt (const 0)) as G.
    rewrite E1 in G. rewrite <- (app_zeros X 32). exact G. }
  assert (H2 : forall Lt, Lt << 0 << 1 << 1 {{B}}> r1 *> const 0 -->* Lt {{E}}> (0 >> r2 *> const 0)).
  { intros Lt. pose proof (wrun_ok n2 (mkW [1;1;0] r1 B true) Lt (const 0)) as G.
    rewrite E2 in G. exact G. }
  apply progress_intro with (c' := const 0 << 1 {{B}}> P ^^ S n *> X *> const 0);
    [apply step_right; reflexivity |].
  eapply evstep_trans; [apply sweep1 |]. eapply evstep_trans; [apply H1 |].
  eapply evstep_trans; [apply sweep2 |].
  eapply evstep_trans with (c' := const 0 << 1 {{B}}> (1 >> 0 >> P2 ^^ S n *> r1 *> const 0)); [execute |].
  rewrite rotate. eapply evstep_trans; [apply sweep1 |].
  eapply evstep_trans with (c' := (P1 ^^ S n *> const 0) << 0 << 1 << 1 {{B}}> r1 *> const 0); [execute |].
  eapply evstep_trans; [apply H2 |]. eapply evstep_trans; [apply sweep2 |].
  eapply evstep_trans with (c' := const 0 {{A}}> (0 >> 1 >> 0 >> P2 ^^ S n *> r2 *> const 0)); [execute |].
  rewrite rotate.
  change (1 >> 0 >> r2 *> const 0) with (([1;0] ++ r2) *> const 0).
  rewrite FC, Str_app_assoc, app_zeros, lpow_shift'. apply evstep_refl.
Qed.

(** ** The run from the blank tape *)

(** The blank tape: the head on the first cell of a block, with a blank block of 22 cells on its left
    (this aligns the blocks so that [Cyc X 7] is met between two block crossings). *)
Definition cfg0 : MC := mkM [4194304%positive] [] A true.

Lemma cfg0_ok : msem cfg0 = c0.
Proof. unfold msem. cbn. repeat rewrite <- const_unfold. reflexivity. Qed.

Fixpoint cells (bs : list positive) : list sym :=
  match bs with [] => [] | b :: bs => dec b ++ cells bs end.
Lemma decs_cells bs : decs bs = cells bs *> const 0.
Proof. induction bs as [| b bs IH]; cbn [decs cells]; [reflexivity |]. rewrite Str_app_assoc, IH. reflexivity. Qed.

Definition is0 (s : sym) : bool := match s with 0 => true | 1 => false end.
Lemma zeros_const l : forallb is0 l = true -> l *> const 0 = const 0.
Proof.
  induction l as [| [|] l IH]; intros H; cbn [forallb] in H; [reflexivity | | discriminate].
  cbn [Str_app]. rewrite IH by exact H. rewrite <- const_unfold. reflexivity.
Qed.

(** The configuration faces left in state [A], the left side is blank, the right side starts with [P^7]
    and what follows ([X]) passes [excs]. *)
Definition check (c : MC) : bool :=
  match c with
  | mkM Ls Rs A false =>
    forallb is0 (cells Ls) && leqb (firstn 91 (cells Rs)) (P ^^ 7) && excs (skipn 91 (cells Rs))
  | _ => false
  end.

Lemma check_ok c : check c = true -> exists X, msem c = Cyc X 7 /\ excs X = true.
Proof.
  destruct c as [Ls Rs [] []]; cbn [check]; try discriminate.
  intros H. apply Bool.andb_true_iff in H as [H HX]. apply Bool.andb_true_iff in H as [HL HR].
  exists (skipn 91 (cells Rs)). split; [| exact HX].
  unfold msem, Cyc. cbn [mf mq mL mR]. rewrite !decs_cells, (zeros_const _ HL).
  rewrite <- (firstn_skipn 91 (cells Rs)) at 1. rewrite (leqb_ok _ _ HR), Str_app_assoc. reflexivity.
Qed.

Definition N : positive := 522833539.
Definition final : MC := snd (mrun N (PositiveMap.empty _, cfg0)).

Lemma final_ok : check final = true.
Proof. native_cast_no_check (eq_refl true). Time Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  destruct (check_ok final final_ok) as [X [HX Hp]].
  apply (multistep_nonhalt tm c0 (Cyc X 7)).
  - rewrite <- cfg0_ok, <- HX. apply mrun_ok. intros q f b e H. rewrite PositiveMap.gempty in H. discriminate.
  - apply (progress_nonhalt_simple tm nat (fun i => Cyc X (S i)) 6).
    intros i. exists (S i). apply period, Hp.
Qed.

Print Assumptions nonhalt.
