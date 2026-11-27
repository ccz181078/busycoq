(* PR74 fixed-far-end bouncer with packed, collision-checked block memoization. *)
From BusyCoq Require Import Individual62.
From Coq Require Import Lists.List PArith String ZArith.
From Coq Require Import PrimInt63.
From Coq Require Uint63 PArray.
Import ListNotations.
Module PR74Prefix.
Set Default Goal Selector "!".
Local Notation int := Uint63.int.

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

    A block is a packed [Uint63.int]: its bits are its cells, lowest bit first,
    and the top bit is a sentinel. *)

Fixpoint dec (p : positive) : list sym :=
  match p with xH => [] | xO p => 0 :: dec p | xI p => 1 :: dec p end.
Fixpoint enc (l : list sym) : positive :=
  match l with [] => xH | 0 :: l => xO (enc l) | 1 :: l => xI (enc l) end.
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


Definition block := Uint63.int.
Definition unpack (b : block) : list sym :=
  match Uint63.to_Z b with Zpos p => dec p | _ => [] end.
Definition pack (l : list sym) : block := Uint63.of_Z (Zpos (enc l)).
Definition pack_checked (l : list sym) : option block :=
  let b := pack l in if leqb (unpack b) l then Some b else None.
Lemma pack_ok l b : pack_checked l = Some b -> unpack b = l.
Proof.
  unfold pack_checked. destruct (leqb _ _) eqn:E; [| discriminate].
  intros H; injection H as <-. apply leqb_ok, E.
Qed.

(** What the machine does with one block: the head leaves it on the right ([ER], the new block read from
    its right end) or on the left ([EL], read from its left end), in a new state. *)
Inductive Ent := ER (b : block) (q : Q) | EL (b : block) (q : Q).

Definition FUEL := 4000.

(** [f = true]: the head enters [b] on its first cell, from the left; [f = false]: on its last cell, from
    the right, and [b] is then read right to left. *)
Definition entry (q : Q) (f : bool) (b : block) : option Ent :=
  match brun FUEL (if f then mkW [] (unpack b) q true else mkW (unpack b) [] q false) with
  | Some (mkW l r q' true) => match r with [] => option_map (fun b => ER b q') (pack_checked l) | _ => None end
  | Some (mkW l r q' false) => match l with [] => option_map (fun b => EL b q') (pack_checked r) | _ => None end
  | None => None
  end.

Definition ent_sem (e : Ent) (Lt Rt : side) : Q * tape :=
  match e with ER b q => (unpack b *> Lt) {{q}}> Rt | EL b q => Lt <{{q}} (unpack b *> Rt) end.

Lemma entry_ok q f b e Lt Rt : entry q f b = Some e ->
  (if f then Lt {{q}}> (unpack b *> Rt) else (unpack b *> Lt) <{{q}} Rt) -->* ent_sem e Lt Rt.
Proof.
  unfold entry. intros H.
  destruct (brun _ _) as [[l r q' []] |] eqn:G; [destruct r | destruct l |]; cbn [option_map] in H; try discriminate H.
  - destruct (pack_checked l) eqn:P; [| discriminate].
    injection H as <-. cbn [ent_sem]. rewrite (pack_ok _ _ P). destruct f; exact (brun_ok _ _ _ Lt Rt G).
  - destruct (pack_checked r) eqn:P; [| discriminate].
    injection H as <-. cbn [ent_sem]. rewrite (pack_ok _ _ P). destruct f; exact (brun_ok _ _ _ Lt Rt G).
Qed.

(** ** The macro simulator

    It keeps a table of the entries it has computed, indexed by state, side and block. *)

Definition qtag (q : Q) : int :=
  match q with
  | A => 0%uint63 | B => 1%uint63 | C => 2%uint63
  | D => 3%uint63 | E => 4%uint63 | F => 5%uint63
  end.
Definition tag (q : Q) (f : bool) : int := Uint63.add (qtag q) (if f then 0%uint63 else 8%uint63).
Lemma tag_inj q f q' f' : tag q f = tag q' f' -> q = q' /\ f = f'.
Proof.
  destruct q, q', f, f'; intro H; try (split; reflexivity);
    apply (proj2 (Uint63.eqb_spec _ _)) in H; vm_compute in H; discriminate.
Qed.

(* The index is just a hint: a collision can evict an entry but cannot
   certify a transition. The exact tags and packed blocks are compared. *)
Definition idx (t b : int) : int :=
  Uint63.land (Uint63.add
    (Uint63.lxor (Uint63.lxor b (Uint63.lsr b 13%uint63)) (Uint63.lsr b 23%uint63))
    (Uint63.mul 65537%uint63 t)) 1048575%uint63.
Definition Slot := (int * block * Ent)%type.
Definition Tab := PArray.array (option Slot).
Definition empty : Tab := PArray.make 1048576 None.

Definition slot_ok (s : option Slot) : Prop :=
  match s with
  | Some (t,b,e) => forall q f, tag q f = t -> entry q f b = Some e
  | None => True
  end.
Definition tab_ok (t : Tab) : Prop := forall i, slot_ok (PArray.get t i).

Definition remember (t : Tab) q f b : option Ent * Tab :=
  match entry q f b with
  | Some e => (Some e, PArray.set t (idx (tag q f) b) (Some (tag q f,b,e)))
  | None => (None,t)
  end.

Lemma remember_ok t q f b o t' : tab_ok t -> remember t q f b = (o,t') ->
  tab_ok t' /\ forall e, o = Some e -> entry q f b = Some e.
Proof.
  intros Ht. unfold remember.
  destruct (entry q f b) as [e |] eqn:E; intros H; injection H as <- <-.
  - split; [| congruence]. intros i.
    destruct (Uint63.eqb i (idx (tag q f) b)) eqn:Hi.
    + apply Uint63.eqb_spec in Hi as ->.
      destruct (Uint63.ltb (idx (tag q f) b) (PArray.length t)) eqn:Ho.
      * rewrite PArray.get_set_same by exact Ho.
        intros q' f' H. apply tag_inj in H as [-> ->]. exact E.
      * rewrite PArray.get_out_of_bounds, PArray.default_set; [| rewrite PArray.length_set; exact Ho].
        rewrite <- (@PArray.get_out_of_bounds _ _ _ Ho). apply Ht.
    + rewrite PArray.get_set_other; [apply Ht |].
      intros <-. rewrite (proj2 (Uint63.eqb_spec _ _) eq_refl) in Hi. discriminate.
  - split; [exact Ht | discriminate].
Qed.

Definition look (t : Tab) (q : Q) (f : bool) (b : block) : option Ent * Tab :=
  let k := tag q f in
  match PArray.get t (idx k b) with
  | Some (k',b',e) =>
      if Datatypes.andb (Uint63.eqb k k') (Uint63.eqb b b') then (Some e,t)
      else remember t q f b
  | None => remember t q f b
  end.

Lemma look_ok t q f b o t' : tab_ok t -> look t q f b = (o, t') ->
  tab_ok t' /\ forall e, o = Some e -> entry q f b = Some e.
Proof.
  intros Ht. unfold look.
  destruct (PArray.get t (idx (tag q f) b)) as [[[k b'] e] |] eqn:S; [| now apply remember_ok].
  destruct (Datatypes.andb (Uint63.eqb (tag q f) k) (Uint63.eqb b b')) eqn:E; [| now apply remember_ok].
  apply Bool.andb_true_iff in E as [Hk Hb].
  apply Uint63.eqb_spec in Hk.
  apply Uint63.eqb_spec in Hb as ->.
  intros H; injection H as <- <-. split; [exact Ht |].
  intros e' H; injection H as <-.
  specialize (Ht (idx (tag q f) b')); rewrite S in Ht. exact (Ht q f Hk).
Qed.

(** A macro configuration: blocks on the left of the head (nearest first), blocks on its right, the state,
    and whether the head is about to enter the first right block ([true]) or the first left block. *)
Record MC := mkM { mL : list block; mR : list block; mq : Q; mf : bool }.

Fixpoint decs (bs : list block) : side :=
  match bs with [] => const 0 | b :: bs => unpack b *> decs bs end.

Definition msem (c : MC) : Q * tape :=
  if mf c then decs (mL c) {{mq c}}> decs (mR c) else decs (mL c) <{{mq c}} decs (mR c).

(** A blank block of 32 cells, used where the tape ends. *)
Definition bl : block := 4294967296%uint63.

Lemma bl_blank : unpack bl *> const 0 = const 0.
Proof. cbn. repeat rewrite <- const_unfold. reflexivity. Qed.

Definition after (e : Ent) (Ls Rs : list block) : MC :=
  match e with ER b q => mkM (b :: Ls) Rs q true | EL b q => mkM Ls (b :: Rs) q false end.

(** The head enters block [b] in state [q] from side [f]; [Ls], [Rs] are the other blocks. *)
Definition cross (t : Tab) (q : Q) (f : bool) (b : block) (Ls Rs : list block) (c : MC) : Tab * MC :=
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

Lemma cross_ok (t : Tab) (q : Q) (f : bool) (b : block) (Ls Rs : list block) (c : MC) : tab_ok t ->
  msem c = (if f then decs Ls {{q}}> (unpack b *> decs Rs) else (unpack b *> decs Ls) <{{q}} decs Rs) ->
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
Proof. exact (shift_rule_R [1] tm P P1 B sweep1_once Lt Rt n). Qed.

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
  symmetry.
  apply (lpow_rotate' [1;0;0;0;1;0;0;0;1;0;0] [1;0] Rt n).
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
Definition cfg0 : MC := mkM [4194304%uint63] [] A true.

Lemma cfg0_ok : msem cfg0 = c0.
Proof. unfold msem. cbn. repeat rewrite <- const_unfold. reflexivity. Qed.

Fixpoint cells (bs : list block) : list sym :=
  match bs with [] => [] | b :: bs => unpack b ++ cells bs end.
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
    Datatypes.andb (Datatypes.andb (forallb is0 (cells Ls)) (leqb (firstn 91 (cells Rs)) (P ^^ 7)))
      (excs (skipn 91 (cells Rs)))
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
Definition final : MC := snd (mrun N (empty, cfg0)).

Theorem nonhalt_of_check : check final = true -> ~ halts tm c0.
Proof.
  intro H.
  destruct (check_ok final H) as [X [HX Hp]].
  apply (multistep_nonhalt tm c0 (Cyc X 7)).
  - rewrite <- cfg0_ok, <- HX. apply mrun_ok.
    intros i; unfold empty; rewrite PArray.get_make; exact I.
  - apply (progress_nonhalt_simple tm nat (fun i => Cyc X (S i)) 6).
    intros i. exists (S i). apply period, Hp.
Qed.

Print Assumptions nonhalt_of_check.

Lemma final_ok : check final = true.
Proof. native_cast_no_check (eq_refl true). Time Qed.

Theorem nonhalt : ~ halts tm c0.
Proof. exact (nonhalt_of_check final_ok). Qed.

Print Assumptions nonhalt.
End PR74Prefix.
