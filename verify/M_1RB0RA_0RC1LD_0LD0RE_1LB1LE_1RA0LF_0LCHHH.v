(** * BB(6) Holdout 608:#390 / 797:#517: 1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC--- *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Arith Lia PArith BinNat String.
Import ListNotations.

Definition tm : TM := TM_from_str "1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---"%string.

Module M390.

Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Notation f0 := S0.
Notation f1 := S1.
Notation blank := (const S0).

Lemma z00 : f0 >> blank = blank.
Proof. symmetry. exact (const_unfold Sym f0). Qed.

Definition finOfBool (b : bool) : Sym := if b then f1 else f0.

Fixpoint decBits (bs : list bool) (lb : side) : side :=
  match bs with
  | [] => lb
  | false :: bs' => f0 >> decBits bs' lb
  | true  :: bs' => f1 >> decBits bs' lb
  end.

Lemma decBits_cons (b : bool) (bs : list bool) (lb : side) :
  decBits (b :: bs) lb = finOfBool b >> decBits bs lb.
Proof. destruct b; reflexivity. Qed.

Lemma decBits_append (a b : list bool) (lb : side) :
  decBits (a ++ b) lb = decBits a (decBits b lb).
Proof.
  induction a as [|x xs IH]; [reflexivity |].
  destruct x; cbn [app decBits]; rewrite IH; reflexivity.
Qed.

(** Finite local execution: frame both unknown tape tails, and run only
    transitions that read an explicit symbol in the current window. *)
Module Window := BoundedConfig.

Definition sameWindow (x y : Window.T) : bool :=
  andb (Eqb.list_eqb Eqb.eqb (Window.l x) (Window.l y))
  (andb (Eqb.list_eqb Eqb.eqb (Window.r x) (Window.r y))
  (andb (Eqb.eqb (Window.s x) (Window.s y))
             (Eqb.eqb (Window.sgn x) (Window.sgn y)))).

Lemma sameWindow_eq x y : sameWindow x y = true -> x = y.
Proof.
  destruct x as [xl xr xq xd], y as [yl yr yq yd].
  cbv beta iota delta [sameWindow Window.l Window.r Window.s Window.sgn].
  destruct (Eqb.list_eqb_spec Eqb.eqb xl yl Eqb.eqb_spec),
    (Eqb.list_eqb_spec Eqb.eqb xr yr Eqb.eqb_spec),
    (Eqb.eqb_spec xq yq), (Eqb.eqb_spec xd yd);
    intro H; try discriminate H; subst; reflexivity.
Qed.

Fixpoint windowReach (fuel : nat) (x y : Window.T) : bool :=
  if sameWindow x y then true else
  match fuel with
  | 0 => false
  | S fuel' =>
      match Window.step tm x with
      | Some x' => windowReach fuel' x' y
      | None => false
      end
  end.

Lemma windowReach_sound fuel x y :
  windowReach fuel x y = true -> forall l r,
  Window.to_config x l r -[ tm ]->* Window.to_config y l r.
Proof.
  revert x; induction fuel as [|fuel IH]; intros x;
    cbn [windowReach]; destruct (sameWindow x y) eqn:E;
    try (intros _ l r; apply sameWindow_eq in E; subst; apply evstep_refl);
    try discriminate.
  pose proof (Window.step_spec tm x) as Hstep.
  destruct (Window.step tm x) eqn:Hnext; [|discriminate].
  intros H l r. eapply evstep_step; [apply Hstep | now apply IH].
Qed.

Definition windowProgress fuel x y : bool :=
  match Window.step tm x with
  | Some x' => windowReach fuel x' y
  | None => false
  end.

Lemma windowProgress_sound fuel x y :
  windowProgress fuel x y = true -> forall l r,
  Window.to_config x l r -[ tm ]->+ Window.to_config y l r.
Proof.
  unfold windowProgress. pose proof (Window.step_spec tm x) as Hstep.
  destruct (Window.step tm x); [|discriminate].
  intros H l r. eapply progress_intro; [apply Hstep | now apply windowReach_sound with (fuel := fuel)].
Qed.

Local Ltac windowSide xs :=
  lazymatch xs with
  | ?a >> ?rest =>
    let p := windowSide rest in
    lazymatch p with (?word, ?tail) => constr:((a :: word, tail)) end
  | decBits ?bs ?tail => constr:((map finOfBool bs, tail))
  | _ => constr:((@nil Sym, xs))
  end.

Local Ltac windowConfig cfg :=
  lazymatch cfg with
  | ?l {{A}}> ?r =>
    let wl := windowSide l in let wr := windowSide r in
    lazymatch wl with (?u, ?l0) => lazymatch wr with (?v, ?r0) =>
      constr:((Window.Build_T u v A R, l0, r0)) end end
  | ?l <{{D}} ?r =>
    let wl := windowSide l in let wr := windowSide r in
    lazymatch wl with (?u, ?l0) => lazymatch wr with (?v, ?r0) =>
      constr:((Window.Build_T v u D L, l0, r0)) end end
  end.

Local Ltac replayWindow fuel :=
  lazymatch goal with
  | |- ?x -[ tm ]->* ?y =>
    let wx := windowConfig x in let wy := windowConfig y in
    lazymatch wx with (?a, ?l, ?r) => lazymatch wy with (?b, _, _) =>
      exact (windowReach_sound fuel a b ltac:(vm_compute; reflexivity) l r)
    end end
  | |- ?x -[ tm ]->+ ?y =>
    let wx := windowConfig x in let wy := windowConfig y in
    lazymatch wx with (?a, ?l, ?r) => lazymatch wy with (?b, _, _) =>
      exact (windowProgress_sound fuel a b ltac:(vm_compute; reflexivity) l r)
    end end
  end.

(** ** 1. Local machine fragments *)

Lemma stepB_1 (l r : side) :
  (l {{A}}> (f1 >> r)) -[ tm ]->+ ((f0 >> l) {{A}}> r).
Proof. replayWindow 32. Qed.

Lemma stepB_01 (l r : side) :
  (l {{A}}> (f0 >> f1 >> r)) -[ tm ]->+ ((f1 >> l) <{{D}} (f1 >> r)).
Proof. replayWindow 32. Qed.

Lemma stepB_000 (l r : side) :
  (l {{A}}> (f0 >> f0 >> f0 >> r)) -[ tm ]->+ ((f0 >> f1 >> l) <{{D}} (f0 >> r)).
Proof. replayWindow 32. Qed.

Lemma stepB_0010 (l r : side) :
  (l {{A}}> (f0 >> f0 >> f1 >> f0 >> r)) -[ tm ]->+ ((f1 >> f0 >> f0 >> f1 >> l) {{A}}> r).
Proof. replayWindow 32. Qed.

Lemma stepB_0011 (l r : side) :
  (l {{A}}> (f0 >> f0 >> f1 >> f1 >> r)) -[ tm ]->+ ((f1 >> l) <{{D}} (f0 >> f0 >> f0 >> r)).
Proof. replayWindow 32. Qed.

Lemma stepE_01 (l r : side) :
  ((f0 >> f1 >> l) <{{D}} r) -[ tm ]->+ (l <{{D}} (f1 >> f1 >> r)).
Proof. replayWindow 32. Qed.

Lemma stepE_00_0 (l r : side) :
  ((f0 >> f0 >> l) <{{D}} (f0 >> r)) -[ tm ]->+ ((f1 >> f0 >> f0 >> l) {{A}}> r).
Proof. replayWindow 32. Qed.

Lemma stepE_00_1 (l r : side) :
  ((f0 >> f0 >> l) <{{D}} (f1 >> r)) -[ tm ]->+ (l <{{D}} (f0 >> f0 >> f0 >> r)).
Proof. replayWindow 32. Qed.

Lemma stepE_10 (l r : side) :
  ((f1 >> f0 >> l) <{{D}} r) -[ tm ]->+ ((f0 >> f1 >> l) {{A}}> r).
Proof. replayWindow 32. Qed.

Lemma stepE_1100 (l r : side) :
  ((f1 >> f1 >> f0 >> f0 >> l) <{{D}} r) -[ tm ]->+ (l <{{D}} (f0 >> f0 >> f0 >> f1 >> r)).
Proof. replayWindow 32. Qed.

Lemma stepE_1101 (l r : side) :
  ((f1 >> f1 >> f0 >> f1 >> l) <{{D}} r) -[ tm ]->+ ((f1 >> f0 >> l) {{A}}> (f0 >> f1 >> r)).
Proof. replayWindow 32. Qed.


Lemma br1_step (l r : side) :
  ((f1 >> f1 >> f0 >> f0 >> l) <{{D}} r) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> r)).
Proof. apply progress_evstep, stepE_1100. Qed.

Lemma br3_step (l r : side) :
  (l {{A}}> (f0 >> f0 >> f1 >> f0 >> r)) -[ tm ]->* ((f1 >> f0 >> f0 >> f1 >> l) {{A}}> r).
Proof. apply progress_evstep, stepB_0010. Qed.

Lemma br2_step (l r : side) :
  ((f0 >> f1 >> f0 >> f0 >> l) <{{D}} r) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma br4_step (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f1 >> f1 >> f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) <{{D}} (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma br5_step (l r : side) :
  (l {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> l) {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma br6_step (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> r)) -[ tm ]->* ((f1 >> f0 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> l) <{{D}} (f1 >> f0 >> f1 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma br7_step (l r : side) :
  ((f0 >> f1 >> f0 >> f1 >> f1 >> f0 >> f0 >> f1 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f1 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma lpa_0 (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma lpa_1 (l r : side) :
  ((f0 >> f1 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma lb_p0_q1_t (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f1 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma lb_p0_q1_f (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma lb_p1_base (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f1 >> f1 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma lb_p1_true (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->* ((f1 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma lb_p1_false (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->* ((f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma rp_entry (l r : side) :
  (l {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}> (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma rp_mid_zero (l r : side) :
  ((f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}> (f1 >> f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> l) {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma rp_mid_1011 (l r : side) :
  ((f0 >> f1 >> f0 >> l) {{A}}> (f1 >> f1 >> f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> l) {{A}}> (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma rp_mid_1000_t (l r : side) :
  ((f0 >> f1 >> f0 >> l) {{A}}> (f1 >> f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f1 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma rp_back_end (l r : side) :
  ((f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> l) {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma fwd_101111 (l r : side) :
  (l {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}> (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma rp_fwd_step (l r : side) :
  ((f0 >> l) {{A}}> (f1 >> f1 >> f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}> (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma rp_fwd_fin (l r : side) :
  ((f0 >> l) {{A}}> (f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> l) {{A}}> (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma sb_fwd_step (l r : side) :
  (l {{A}}> (f1 >> f1 >> f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> l) {{A}}> (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma sb_fwd_fin (l r : side) :
  (l {{A}}> (f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> r)) -[ tm ]->* ((f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f1 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma p4_turn (l r : side) :
  ((f0 >> l) {{A}}> (f1 >> f0 >> f0 >> f0 >> r)) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f0 >> r)).
Proof. replayWindow 128. Qed.

Lemma p4_back_0001 (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma p4_bounce_0101 (l r : side) :
  ((f1 >> f0 >> f1 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> l) {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma p4_finish_01 (l r : side) :
  (l {{A}}> (f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f1 >> f0 >> l) <{{D}} (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma p4b_true (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f1 >> f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->* ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) <{{D}} (f1 >> r)).
Proof. replayWindow 128. Qed.

Lemma p4b_false_enter (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}} (f1 >> f1 >> f1 >> f0 >> f1 >> r)) -[ tm ]->* ((f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}> (f1 >> r)).
Proof. replayWindow 128. Qed.


(** ** 4. Bit-Block Repetition, Word Encodings, and Shift Identities *)

Fixpoint repBits (u : list bool) (k : nat) (lb : side) : side :=
  match k with
  | 0 => lb
  | S k' => decBits u (repBits u k' lb)
  end.

Lemma repBits_add (u : list bool) (a b : nat) (lb : side) :
  repBits u (a + b) lb = repBits u a (repBits u b lb).
Proof.
  induction a as [|a IH]; [reflexivity |].
  cbn [Nat.add repBits]. rewrite IH. reflexivity.
Qed.

Lemma repBits_succ_right (u : list bool) (k : nat) (lb : side) :
  repBits u (S k) lb = repBits u k (decBits u lb).
Proof.
  induction k as [|k IH]; [reflexivity |].
  change (decBits u (repBits u (S k) lb) = decBits u (repBits u k (decBits u lb))).
  rewrite IH. reflexivity.
Qed.

Fixpoint flipW (w : list bool) : list bool :=
  match w with
  | [] => []
  | b :: bs => negb b :: flipW bs
  end.

Lemma flipW_append (a b : list bool) : flipW (a ++ b) = flipW a ++ flipW b.
Proof.
  induction a as [|x xs IH]; [reflexivity |].
  cbn [app flipW]. rewrite IH. reflexivity.
Qed.

Lemma flipW_repeat (k : nat) (b : bool) :
  flipW (List.repeat b k) = List.repeat (negb b) k.
Proof.
  induction k as [|k IH]; [reflexivity |].
  cbn [List.repeat flipW]. rewrite IH. reflexivity.
Qed.

Lemma flipW_involutive (w : list bool) : flipW (flipW w) = w.
Proof.
  induction w as [|x xs IH]; [reflexivity |].
  cbn [flipW]. rewrite Bool.negb_involutive, IH. reflexivity.
Qed.

Lemma flip_cond (f : bool) (w : list bool) :
  (if negb f then flipW w else w) = flipW (if f then flipW w else w).
Proof. destruct f; cbn; [symmetry; apply flipW_involutive | reflexivity]. Qed.

Lemma repeat_snoc {X : Type} (b : X) (k : nat) :
  List.repeat b k ++ [b] = b :: List.repeat b k.
Proof.
  induction k as [|k IH]; [reflexivity |].
  cbn [List.repeat app]. rewrite IH. reflexivity.
Qed.

Lemma rev_repeat {X : Type} (b : X) (k : nat) :
  List.rev (List.repeat b k) = List.repeat b k.
Proof.
  induction k as [|k IH]; [reflexivity |].
  cbn [List.repeat List.rev]. rewrite IH, repeat_snoc. reflexivity.
Qed.

Lemma repeat_len {X : Type} (b : X) (k : nat) :
  List.length (List.repeat b k) = k.
Proof.
  induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Lemma cons_repeat_append {X : Type} (b : X) (m : nat) (tl : list X) :
  b :: (List.repeat b m ++ tl) = List.repeat b m ++ b :: tl.
Proof.
  induction m as [|m IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Fixpoint encWL (w : list bool) (lb : side) : side :=
  match w with
  | [] => lb
  | false :: ws => f1 >> f0 >> f0 >> f0 >> encWL ws lb
  | true  :: ws => f0 >> f1 >> f0 >> f0 >> encWL ws lb
  end.

Fixpoint encWR (w : list bool) (lb : side) : side :=
  match w with
  | [] => lb
  | false :: ws => f1 >> f1 >> f1 >> f0 >> encWR ws lb
  | true  :: ws => f1 >> f0 >> f0 >> f0 >> encWR ws lb
  end.

Fixpoint encWL_b0 (w : list bool) (lb : side) : side :=
  match w with
  | [] => lb
  | false :: ws => f0 >> f1 >> f0 >> f0 >> encWL_b0 ws lb
  | true  :: ws => f0 >> f0 >> f1 >> f0 >> encWL_b0 ws lb
  end.

Fixpoint encWR0 (w : list bool) (lb : side) : side :=
  match w with
  | [] => lb
  | false :: ws => f0 >> f1 >> f1 >> f1 >> encWR0 ws lb
  | true  :: ws => f0 >> f1 >> f0 >> f0 >> encWR0 ws lb
  end.

Fixpoint encWR_q1 (w : list bool) (lb : side) : side :=
  match w with
  | [] => lb
  | false :: ws => f1 >> f1 >> f0 >> f1 >> encWR_q1 ws lb
  | true  :: ws => f0 >> f0 >> f0 >> f1 >> encWR_q1 ws lb
  end.

Lemma encWL_append (a b : list bool) (lb : side) :
  encWL (a ++ b) lb = encWL a (encWL b lb).
Proof. induction a as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma encWR_append (a b : list bool) (lb : side) :
  encWR (a ++ b) lb = encWR a (encWR b lb).
Proof. induction a as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma encWL_b0_append (a b : list bool) (lb : side) :
  encWL_b0 (a ++ b) lb = encWL_b0 a (encWL_b0 b lb).
Proof. induction a as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma encWR0_append (a b : list bool) (lb : side) :
  encWR0 (a ++ b) lb = encWR0 a (encWR0 b lb).
Proof. induction a as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma encWR_q1_append (a b : list bool) (lb : side) :
  encWR_q1 (a ++ b) lb = encWR_q1 a (encWR_q1 b lb).
Proof. induction a as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma encWL_rep_false (k : nat) (lb : side) :
  encWL (List.repeat false k) lb = repBits [true; false; false; false] k lb.
Proof. induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma encWL_b0_rep_false (k : nat) (lb : side) :
  encWL_b0 (List.repeat false k) lb = repBits [false; true; false; false] k lb.
Proof. induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma encWL_b0_rep_true (k : nat) (lb : side) :
  encWL_b0 (List.repeat true k) lb = repBits [false; false; true; false] k lb.
Proof. induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma encWR0_rep_false (k : nat) (lb : side) :
  encWR0 (List.repeat false k) lb = repBits [false; true; true; true] k lb.
Proof. induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma encWR0_rep_true (k : nat) (lb : side) :
  encWR0 (List.repeat true k) lb = repBits [false; true; false; false] k lb.
Proof. induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma encWR_q1_rep_false (k : nat) (lb : side) :
  encWR_q1 (List.repeat false k) lb = repBits [true; true; false; true] k lb.
Proof. induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma encWR_rep_false (k : nat) (lb : side) :
  encWR (List.repeat false k) lb = repBits [true; true; true; false] k lb.
Proof. induction k as [|k IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma shift_0_encWL (w : list bool) (lb : side) :
  f0 >> encWL w lb = encWL_b0 w (f0 >> lb).
Proof. induction w as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma shift_0_encWR (u : list bool) (lb : side) :
  f0 >> encWR u lb = encWR0 u (f0 >> lb).
Proof. induction u as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma shift_encWR_1 (u : list bool) (lb : side) :
  encWR u (f1 >> lb) = f1 >> encWR_q1 u lb.
Proof. induction u as [|[|] xs IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma shift_lb_p0_1 (k : nat) (lb : side) :
  repBits [false; false; false; true] k (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> lb) =
    f0 >> repBits [false; false; true; false] k (f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> lb).
Proof. induction k as [|k IH]; [reflexivity | cbn [repBits decBits]; rewrite IH; reflexivity]. Qed.

Lemma shift_lb_p0_2 (k : nat) (lb : side) :
  f1 >> repBits [true; false; false; true] k (f1 >> f0 >> f0 >> lb) =
    repBits [true; true; false; false] (S k) lb.
Proof. induction k as [|k IH]; [reflexivity | cbn [repBits decBits] in *; rewrite IH; reflexivity]. Qed.

Lemma shift_lb_p0_3 (k : nat) (lb : side) :
  repBits [false; false; false; true] (S k) (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> lb) =
    f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f1 >> f1 >> lb).
Proof. induction k as [|k IH]; [reflexivity | cbn [repBits decBits] in *; rewrite IH; reflexivity]. Qed.

Lemma shift_lb_p0_4 (m : nat) (lb : side) :
  f0 >> f1 >> repBits [true; true; false; true] m (f0 >> f0 >> lb) =
    repBits [false; true; true; true] m (f0 >> f1 >> f0 >> f0 >> lb).
Proof. induction m as [|m IH]; [reflexivity | cbn [repBits decBits]; rewrite IH; reflexivity]. Qed.

Lemma shift_rp_1_core (k : nat) (lb : side) :
  f1 >> repBits [true; true; false; true] k (f0 >> f1 >> lb) =
    repBits [true; true; true; false] k (f1 >> f0 >> f1 >> lb).
Proof. induction k as [|k IH]; [reflexivity | cbn [repBits decBits]; rewrite IH; reflexivity]. Qed.

Lemma shift_rp_1 (k : nat) (lb : side) :
  f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> repBits [true; true; false; true] k (f0 >> f1 >> lb) =
    f1 >> f1 >> f1 >> f1 >> f0 >> repBits [true; true; true; false] k (f1 >> f0 >> f1 >> lb).
Proof. repeat f_equal. apply shift_rp_1_core. Qed.

Lemma shift_p4_1 (m : nat) (lb : side) :
  repBits [false; true; false; false] m (f0 >> f1 >> f0 >> f1 >> f0 >> lb) =
    f0 >> repBits [true; false; false; false] m (f1 >> f0 >> f1 >> f0 >> lb).
Proof. induction m as [|m IH]; [reflexivity | cbn [repBits decBits]; rewrite IH; reflexivity]. Qed.

Lemma shift_sb_1_core (k : nat) (lb : side) :
  f1 >> repBits [true; true; false; true] k (f0 >> lb) =
    repBits [true; true; true; false] k (f1 >> f0 >> lb).
Proof. induction k as [|k IH]; [reflexivity | cbn [repBits decBits]; rewrite IH; reflexivity]. Qed.

Lemma shift_sb_1 (k : nat) (lb : side) :
  f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> repBits [true; true; false; true] k (f0 >> lb) =
    f1 >> f1 >> f1 >> f1 >> f0 >> repBits [true; true; true; false] k (f1 >> f0 >> lb).
Proof. repeat f_equal. apply shift_sb_1_core. Qed.

Lemma splitLeading (b : bool) (w : list bool) :
  exists (k : nat) (rest : list bool), w = List.repeat b k ++ rest /\
    (rest = [] \/ exists t, rest = negb b :: t).
Proof.
  induction w as [|x xs IH].
  - exists 0, (@nil bool). split; [reflexivity | left; reflexivity].
  - destruct (Bool.bool_dec x b) as [-> | Hne].
    + destruct IH as [k [rest [H1 H2]]].
      exists (S k), rest. split; [cbn; f_equal; exact H1 | exact H2].
    + assert (Hx : x = negb b) by (destruct x, b; congruence || reflexivity).
      subst x. exists 0, (negb b :: xs). split; [reflexivity | right; exists xs; reflexivity].
Qed.

(** ** 5. Loop & SafeWord Transducer Soundness Proofs *)

(** A local transfer repeated across a homogeneous run. [at] puts the
    source first regardless of the physical direction of the sweep. *)
Lemma repeatSweep
  (view : side -> side -> Q * tape)
  (take put : side -> side) (src dst : nat -> side -> side)
  (src0 : forall l, src 0 l = l) (dst0 : forall r, dst 0 r = r)
  (srcS : forall n l, src (S n) l = take (src n l))
  (dstS : forall n r, dst (S n) r = dst n (put r))
  (move : forall l r, view (take l) r -[ tm ]->* view l (put r))
  n l r : view (src n l) r -[ tm ]->* view l (dst n r).
Proof.
  revert r; induction n as [|n IH]; intros r.
  - rewrite src0, dst0. apply evstep_refl.
  - rewrite srcS, dstS. eapply evstep_trans; [apply move | apply IH].
Qed.

Lemma repeatBitsSweep (view : side -> side -> Q * tape) u v
  (move : forall l r,
    view (decBits u l) r -[ tm ]->* view l (decBits v r)) k l r :
  view (repBits u k l) r -[ tm ]->* view l (repBits v k r).
Proof.
  apply (repeatSweep view (decBits u) (decBits v) (repBits u) (repBits v));
    try reflexivity; [apply repBits_succ_right | exact move].
Qed.

Lemma loop_br1 (k : nat) (l r : side) :
  (repBits [true; true; false; false] k l <{{D}} r) -[ tm ]->*
    (l <{{D}} repBits [false; false; false; true] k r).
Proof. eapply repeatBitsSweep with (view := fun l r => l <{{D}} r); exact br1_step. Qed.

Lemma loop_br2 (k : nat) (l r : side) :
  (repBits [false; true; false; false] k l <{{D}} r) -[ tm ]->*
    (l <{{D}} repBits [false; false; false; true] k r).
Proof. eapply repeatBitsSweep with (view := fun l r => l <{{D}} r); exact br2_step. Qed.

Lemma loop_br3 (k : nat) (l r : side) :
  (l {{A}}> repBits [false; false; true; false] k r) -[ tm ]->*
    (repBits [true; false; false; true] k l {{A}}> r).
Proof. eapply repeatBitsSweep with (view := fun r l => l {{A}}> r); exact (fun r l => br3_step l r). Qed.

Lemma loop_q1_t (m : nat) (l r : side) :
  ((f1 >> f0 >> repBits [false; false; true; false] m l) <{{D}} (f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->*
    ((f1 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> repBits [true; true; false; true] m r)).
Proof. eapply repeatBitsSweep with (view := fun l r => (f1 >> f0 >> l) <{{D}} (f0 >> f0 >> f0 >> f1 >> r)); exact lb_p0_q1_t. Qed.

Lemma loop_p4_back (m : nat) (l r : side) :
  (repBits [true; false; false; false] m l <{{D}} (f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> f1 >> repBits [true; true; false; true] m r)).
Proof. eapply repeatBitsSweep with (view := fun l r => l <{{D}} (f0 >> f0 >> f0 >> f1 >> r)); exact p4_back_0001. Qed.

Lemma loop_sb_fwd (k : nat) (l r : side) :
  (l {{A}}> repBits [true; true; true; false] k (f1 >> r)) -[ tm ]->*
    (repBits [false; true; false; false] k l {{A}}> (f1 >> r)).
Proof.
  revert l. induction k as [|k IH]; intros l; [apply evstep_refl |].
  destruct k as [|k']; [apply sb_fwd_step |].
  rewrite (repBits_succ_right [false; true; false; false] (S k')).
  eapply evstep_trans.
  - exact (sb_fwd_step l (f1 >> f1 >> f0 >> repBits [true; true; true; false] k' (f1 >> r))).
  - exact (IH (f0 >> f1 >> f0 >> f0 >> l)).
Qed.

Lemma loop_rp_fwd (k : nat) (l r : side) :
  ((f0 >> l) {{A}}> repBits [true; true; true; false] k (f1 >> r)) -[ tm ]->*
    ((f0 >> repBits [true; false; false; false] k l) {{A}}> (f1 >> r)).
Proof.
  revert l. induction k as [|k IH]; intros l; [apply evstep_refl |].
  destruct k as [|k']; [apply rp_fwd_step |].
  rewrite (repBits_succ_right [true; false; false; false] (S k')).
  eapply evstep_trans.
  - exact (rp_fwd_step l (f1 >> f1 >> f0 >> repBits [true; true; true; false] k' (f1 >> r))).
  - exact (IH (f1 >> f0 >> f0 >> f0 >> l)).
Qed.

Lemma loop_rp_mid_1011 (k : nat) (l r : side) :
  ((f0 >> f1 >> f0 >> l) {{A}}> (f1 >> repBits [true; true; false; true] k r)) -[ tm ]->*
    ((f0 >> f1 >> f0 >> repBits [false; false; true; false] k l) {{A}}> (f1 >> r)).
Proof. eapply repeatBitsSweep with (view := fun r l => (f0 >> f1 >> f0 >> l) {{A}}> (f1 >> r)); exact (fun r l => rp_mid_1011 l r). Qed.

Lemma leftPassA_reaches (w : list bool) (l r : side) :
  (encWL w l <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> encWR (List.rev w) r)).
Proof.
  revert r. induction w as [|[|] ws IH]; intros r; [apply evstep_refl | | ].
  - cbn [encWL List.rev]. rewrite encWR_append. cbn [encWR].
    eapply evstep_trans; [apply lpa_1 | apply IH].
  - cbn [encWL List.rev]. rewrite encWR_append. cbn [encWR].
    eapply evstep_trans; [apply lpa_0 | apply IH].
Qed.

Lemma rep0010_shift (m : nat) (l : side) :
  repBits [false; false; true; false] m (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) =
    f0 >> f0 >> f1 >> f0 >> repBits [false; false; true; false] m (f0 >> f1 >> f0 >> f0 >> l).
Proof. induction m as [|m IH]; [reflexivity | cbn [repBits decBits] in *; rewrite IH; reflexivity]. Qed.

Lemma leftB_p0_run (k m : nat) (l r : side) :
  (repBits [false; true; false; false] k (repBits [false; false; true; false] m (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l))
    <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> r)) -[ tm ]->*
  (l <{{D}}
    (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> repBits [false; true; true; true] m (repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r)))).
Proof.
  rewrite rep0010_shift.
  pose proof (loop_br2 k (f0 >> f0 >> f1 >> f0 >> repBits [false; false; true; false] m (f0 >> f1 >> f0 >> f0 >> l))
                         (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> r)) as H1.
  rewrite shift_lb_p0_1 in H1.
  pose proof (progress_evstep _ _ _ (stepE_00_0 (f1 >> f0 >> repBits [false; false; true; false] m (f0 >> f1 >> f0 >> f0 >> l))
                         (repBits [false; false; true; false] k (f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> r)))) as H2.
  pose proof (loop_br3 k (f1 >> f0 >> f0 >> f1 >> f0 >> repBits [false; false; true; false] m (f0 >> f1 >> f0 >> f0 >> l))
                         (f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> r)) as H3.
  pose proof (progress_evstep _ _ _ (stepB_0011 (repBits [true; false; false; true] k (f1 >> f0 >> f0 >> f1 >> f0 >> repBits [false; false; true; false] m (f0 >> f1 >> f0 >> f0 >> l)))
                         (f1 >> f1 >> f1 >> r))) as H4.
  rewrite shift_lb_p0_2 in H4.
  pose proof (loop_br1 (S k) (f1 >> f0 >> repBits [false; false; true; false] m (f0 >> f1 >> f0 >> f0 >> l))
                             (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r)) as H5.
  rewrite shift_lb_p0_3 in H5.
  pose proof (loop_q1_t m (f0 >> f1 >> f0 >> f0 >> l)
                          (f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f1 >> f1 >> r))) as H6.
  pose proof (lb_p0_q1_f l (repBits [true; true; false; true] m (f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f1 >> f1 >> r)))) as H7.
  assert (HR7 : f0 >> f1 >> repBits [true; true; false; true] m (f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f1 >> f1 >> r)) =
                repBits [false; true; true; true] m (repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r))).
  { rewrite shift_lb_p0_4. f_equal.
    change (f0 >> f1 >> f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f1 >> f1 >> r))
      with (repBits [false; true; false; false] (S k) (f0 >> f1 >> f1 >> f1 >> r)).
    rewrite repBits_succ_right. reflexivity. }
  rewrite <- HR7.
  eapply evstep_trans; [exact H1 |].
  eapply evstep_trans; [exact H2 |].
  eapply evstep_trans; [exact H3 |].
  eapply evstep_trans; [exact H4 |].
  eapply evstep_trans; [exact H5 |].
  eapply evstep_trans; [exact H6 | exact H7].
Qed.

Lemma leftPassB_p0_reaches (w : list bool) (l r : side) :
  (encWL_b0 w (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l)
    <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> r)) -[ tm ]->*
  (l <{{D}}
    (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> encWR0 (List.rev (flipW w)) (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r))).
Proof.
  remember (List.length w) as n eqn:Hn.
  revert w Hn l r.
  induction n as [n IH] using strong_induction.
  intros w Hn l r. subst n.
  destruct (splitLeading false w) as [k [rest1 [Hw1 Hrest1]]].
  destruct Hrest1 as [-> | [t1 ->]].
  - rewrite app_nil_r in Hw1. subst w.
    rewrite encWL_b0_rep_false, flipW_repeat; cbn [negb].
    rewrite rev_repeat, encWR0_rep_true.
    exact (leftB_p0_run k 0 l r).
  - cbn [negb] in Hw1.
    destruct (splitLeading true t1) as [m [rest2 [Ht1 Hrest2]]].
    subst t1.
    destruct Hrest2 as [-> | [w' ->]].
    + rewrite app_nil_r in Hw1. subst w.
      change (true :: List.repeat true m) with (List.repeat true (S m)).
      rewrite encWL_b0_append, encWL_b0_rep_false, encWL_b0_rep_true.
      rewrite flipW_append, !flipW_repeat; cbn [negb].
      rewrite List.rev_app_distr, !rev_repeat, encWR0_append, encWR0_rep_false, encWR0_rep_true.
      exact (leftB_p0_run k (S m) l r).
    + cbn [negb] in Hw1. subst w.
      assert (Hlen : List.length w' < List.length (List.repeat false k ++ true :: List.repeat true m ++ false :: w')).
      { rewrite !length_app; cbn [List.length]; rewrite !length_app; cbn [List.length]; rewrite !repeat_len; lia. }
      assert (HL : encWL_b0 (List.repeat false k ++ true :: List.repeat true m ++ false :: w')
                     (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) =
                   repBits [false; true; false; false] k
                     (repBits [false; false; true; false] m
                       (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >>
                         encWL_b0 w' (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l)))).
      { rewrite encWL_b0_append, encWL_b0_rep_false. f_equal.
        rewrite cons_repeat_append, encWL_b0_append, encWL_b0_rep_true. reflexivity. }
      pose proof (leftB_p0_run k m (encWL_b0 w' (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l)) r) as Hstep1.
      pose proof (IH (List.length w') Hlen w' eq_refl l
        (repBits [false; true; true; true] m (repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r)))) as Hstep2.
      assert (HR : encWR0 (List.rev (flipW w'))
                     (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >>
                       repBits [false; true; true; true] m (repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r))) =
                   encWR0 (List.rev (flipW (List.repeat false k ++ true :: List.repeat true m ++ false :: w')))
                     (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r)).
      { rewrite cons_repeat_append.
        replace (List.repeat false k ++ List.repeat true m ++ true :: false :: w')
          with (List.repeat false k ++ List.repeat true m ++ [true; false] ++ w')
          by reflexivity.
        rewrite !flipW_append, !flipW_repeat; cbn [negb].
        rewrite !List.rev_app_distr, !rev_repeat; cbn [List.rev app].
        rewrite !encWR0_append, encWR0_rep_false, encWR0_rep_true; cbn [encWR0].
        reflexivity. }
      rewrite HL. rewrite HR in Hstep2.
      eapply evstep_trans; [exact Hstep1 | exact Hstep2].
Qed.

Lemma leftPassB_p1_reaches (w : list bool) (l r : side) :
  ((f1 >> f0 >> f0 >> encWL w (f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l))
    <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->*
  (l <{{D}}
    (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f1 >> f1 >> f0 >> encWR (List.rev (flipW w)) (f1 >> f1 >> f1 >> f0 >> r))).
Proof.
  revert r. induction w as [|[|] ws IH]; intros r; [apply lb_p1_base | | ].
  - cbn [encWL flipW negb List.rev]. rewrite encWR_append; cbn [encWR].
    eapply evstep_trans; [apply lb_p1_true | apply IH].
  - pose proof (lb_p1_false (encWL ws (f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> l)) r) as H1.
    pose proof (leftPassB_p0_reaches ws l (f0 >> r)) as H2.
    rewrite <- shift_0_encWL in H2.
    assert (HR : encWR0 (List.rev (flipW ws)) (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> f0 >> r) =
                 f0 >> encWR (List.rev (flipW (false :: ws))) (f1 >> f1 >> f1 >> f0 >> r)).
    { cbn [flipW negb List.rev]. rewrite encWR_append; cbn [encWR].
      rewrite shift_0_encWR. reflexivity. }
    rewrite HR in H2.
    eapply evstep_trans; [exact H1 | exact H2].
Qed.

Lemma rp_mid_run (k : nat) (l r : side) :
  ((f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}>
    (f1 >> repBits [true; true; false; true] k (f0 >> f0 >> f0 >> f1 >> r))) -[ tm ]->*
  ((f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] k (f0 >> f1 >> f0 >> f0 >> l))
    {{A}}> (f1 >> r)).
Proof.
  destruct k as [|k'].
  - eapply evstep_trans; [apply rp_mid_zero | apply rp_entry].
  - pose proof (loop_rp_mid_1011 (S k') (f1 >> f0 >> f0 >> f0 >> l) (f0 >> f0 >> f0 >> f1 >> r)) as H1.
    pose proof (rp_mid_1000_t (repBits [false; false; true; false] (S k') (f1 >> f0 >> f0 >> f0 >> l)) r) as H2.
    pose proof (loop_q1_t (S k') (f1 >> f0 >> f0 >> f0 >> l) (f0 >> f1 >> r)) as H3.
    pose proof (rp_back_end l (repBits [true; true; false; true] (S k') (f0 >> f1 >> r))) as H4.
    rewrite shift_rp_1 in H4.
    pose proof (fwd_101111 (f0 >> f1 >> f0 >> f0 >> l)
                  (f1 >> f1 >> f0 >> repBits [true; true; true; false] k' (f1 >> f0 >> f1 >> r))) as H5.
    pose proof (loop_rp_fwd (S k') (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) (f0 >> f1 >> r)) as H6.
    pose proof (rp_fwd_fin (repBits [true; false; false; false] (S k') (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l)) r) as H7.
    assert (HL : f0 >> f1 >> f0 >> repBits [true; false; false; false] (S k') (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) =
                 f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] (S k') (f0 >> f1 >> f0 >> f0 >> l)).
    { repeat f_equal.
      change (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l)
        with (decBits [true; false; false; false] (f0 >> f1 >> f0 >> f0 >> l)).
      rewrite <- repBits_succ_right. reflexivity. }
    rewrite HL in H7.
    eapply evstep_trans; [exact H1 |].
    eapply evstep_trans; [exact H2 |].
    eapply evstep_trans; [exact H3 |].
    eapply evstep_trans; [exact H4 |].
    eapply evstep_trans; [exact H5 |].
    eapply evstep_trans; [exact H6 | exact H7].
Qed.

Lemma rp_mid_all (v : list bool) (l r : side) :
  ((f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}>
    (f1 >> encWR_q1 v (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> r))) -[ tm ]->*
  ((f0 >> f1 >> f0 >> f0 >> encWL (List.rev v) (f0 >> f1 >> f0 >> f0 >> l))
    {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> f1 >> r)).
Proof.
  remember (List.length v) as n eqn:Hn.
  revert v Hn l r.
  induction n as [n IH] using strong_induction.
  intros v Hn l r. subst n.
  destruct (splitLeading false v) as [k [rest [Hv1 Hrest]]].
  destruct Hrest as [-> | [v' ->]].
  - rewrite app_nil_r in Hv1. subst v.
    rewrite encWR_q1_rep_false, rev_repeat, encWL_rep_false.
    destruct k as [|k'].
    + eapply evstep_trans; [apply rp_mid_zero | apply br5_step].
    + eapply evstep_trans; [apply rp_mid_run | apply rp_mid_zero].
  - cbn [negb] in Hv1. subst v.
    assert (Hlen : List.length v' < List.length (List.repeat false k ++ true :: v')).
    { rewrite length_app; cbn [List.length]; rewrite repeat_len; lia. }
    rewrite encWR_q1_append, encWR_q1_rep_false; cbn [encWR_q1].
    pose proof (rp_mid_run k l (encWR_q1 v' (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> r))) as H1.
    pose proof (IH (List.length v') Hlen v' eq_refl (repBits [true; false; false; false] k (f0 >> f1 >> f0 >> f0 >> l)) r) as H2.
    assert (HL : encWL (List.rev v') (f0 >> f1 >> f0 >> f0 >> repBits [true; false; false; false] k (f0 >> f1 >> f0 >> f0 >> l)) =
                 encWL (List.rev (List.repeat false k ++ true :: v')) (f0 >> f1 >> f0 >> f0 >> l)).
    { rewrite List.rev_app_distr; cbn [List.rev app]; rewrite rev_repeat, !encWL_append, encWL_rep_false; cbn [encWL].
      reflexivity. }
    rewrite HL in H2.
    eapply evstep_trans; [exact H1 | exact H2].
Qed.

Lemma rightPassQ1_reaches (v : list bool) (l r : side) :
  ((f0 >> f1 >> f0 >> f0 >> l) {{A}}>
    (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> f1 >> encWR_q1 v (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> r))) -[ tm ]->*
  ((f0 >> f1 >> f0 >> f0 >> encWL (List.rev v) (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l))
    {{A}}> (f1 >> f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> f1 >> r)).
Proof.
  eapply evstep_trans; [apply rp_entry | apply rp_mid_all].
Qed.

Lemma superBounce_reaches (k : nat) (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f1 >> f0 >> l))
    <{{D}} (f1 >> f0 >> f0 >> f0 >> r)) -[ tm ]->*
  ((f1 >> f0 >> f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l))
    <{{D}} (f1 >> f0 >> r)).
Proof.
  pose proof (progress_evstep _ _ _ (stepE_10 (f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f1 >> f0 >> l))
                       (f1 >> f0 >> f0 >> f0 >> r))) as H1.
  change (f0 >> f1 >> f0 >> f0 >> repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f1 >> f0 >> l))
    with (repBits [false; true; false; false] (S k) (f0 >> f1 >> f0 >> f1 >> f0 >> l)) in H1.
  rewrite (shift_p4_1 (S k)) in H1.
  pose proof (p4_turn (repBits [true; false; false; false] (S k) (f1 >> f0 >> f1 >> f0 >> l)) r) as H2.
  pose proof (loop_p4_back (S k) (f1 >> f0 >> f1 >> f0 >> l) (f0 >> r)) as H3.
  pose proof (p4_bounce_0101 l (repBits [true; true; false; true] (S k) (f0 >> r))) as H4.
  rewrite shift_sb_1 in H4.
  pose proof (fwd_101111 (f0 >> f1 >> l)
                (f1 >> f1 >> f0 >> repBits [true; true; true; false] k (f1 >> f0 >> r))) as H5.
  pose proof (loop_sb_fwd k (f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)
                            (f1 >> f1 >> f0 >> f1 >> f0 >> r)) as H6.
  change (f1 >> f1 >> f1 >> f0 >> f1 >> f0 >> r)
    with (decBits [true; true; true; false] (f1 >> f0 >> r)) in H6.
  rewrite <- repBits_succ_right in H6.
  pose proof (sb_fwd_fin (repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)) r) as H7.
  eapply evstep_trans; [exact H1 |].
  eapply evstep_trans; [exact H2 |].
  eapply evstep_trans; [exact H3 |].
  eapply evstep_trans; [exact H4 |].
  eapply evstep_trans; [exact H5 |].
  eapply evstep_trans; [exact H6 | exact H7].
Qed.

Lemma pass4_bounce (m : nat) (l r : side) :
  (repBits [false; true; false; false] (S m) (f0 >> f1 >> f0 >> f1 >> f0 >> l)
    {{A}}> (f1 >> f0 >> f0 >> f0 >> f1 >> r)) -[ tm ]->*
  ((f1 >> f0 >> f0 >> repBits [true; false; false; false] (S m) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l))
    <{{D}} (f1 >> r)).
Proof.
  rewrite shift_p4_1.
  pose proof (p4_turn (repBits [true; false; false; false] (S m) (f1 >> f0 >> f1 >> f0 >> l)) (f1 >> r)) as H1.
  pose proof (loop_p4_back (S m) (f1 >> f0 >> f1 >> f0 >> l) (f0 >> f1 >> r)) as H2.
  pose proof (p4_bounce_0101 l (repBits [true; true; false; true] (S m) (f0 >> f1 >> r))) as H3.
  rewrite shift_rp_1 in H3.
  pose proof (fwd_101111 (f0 >> f1 >> l)
                (f1 >> f1 >> f0 >> repBits [true; true; true; false] m (f1 >> f0 >> f1 >> r))) as H4.
  pose proof (loop_rp_fwd (S m) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l) (f0 >> f1 >> r)) as H5.
  pose proof (p4_finish_01 (f0 >> repBits [true; false; false; false] (S m) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)) r) as H6.
  eapply evstep_trans; [exact H1 |].
  eapply evstep_trans; [exact H2 |].
  eapply evstep_trans; [exact H3 |].
  eapply evstep_trans; [exact H4 |].
  eapply evstep_trans; [exact H5 | exact H6].
Qed.

Lemma p4b_false_run (k : nat) (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}}
    (repBits [true; true; true; false] (S k) (f1 >> f0 >> f0 >> f0 >> f1 >> r))) -[ tm ]->*
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] (S k) (f0 >> f1 >> f0 >> f0 >> l))
    <{{D}} (f1 >> r)).
Proof.
  assert (H1 : ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}}
                 (repBits [true; true; true; false] (S k) (f1 >> f0 >> f0 >> f0 >> f1 >> r))) -[ tm ]->*
               ((f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) {{A}}>
                 repBits [true; true; true; false] k (f1 >> f0 >> f0 >> f0 >> f1 >> r))).
  { destruct k as [|k']; [apply p4b_false_enter | apply p4b_false_enter]. }
  pose proof (loop_sb_fwd k (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) (f0 >> f0 >> f0 >> f1 >> r)) as H2.
  change (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l)
    with (decBits [false; true; false; false] (f0 >> f1 >> f0 >> f1 >> f0 >> f0 >> f0 >> l)) in H2.
  rewrite <- repBits_succ_right in H2.
  pose proof (pass4_bounce k (f0 >> f0 >> l) r) as H3.
  assert (HL3 : f1 >> f0 >> f0 >> repBits [true; false; false; false] (S k) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l) =
                f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] (S k) (f0 >> f1 >> f0 >> f0 >> l)).
  { repeat f_equal.
    change (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> l)
      with (decBits [true; false; false; false] (f0 >> f1 >> f0 >> f0 >> l)).
    rewrite <- repBits_succ_right. reflexivity. }
  rewrite HL3 in H3.
  eapply evstep_trans; [exact H1 |].
  eapply evstep_trans; [exact H2 | exact H3].
Qed.

Lemma p4b_all (v : list bool) (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}}
    (encWR v (f1 >> f0 >> f0 >> f0 >> f1 >> r))) -[ tm ]->*
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> encWL (List.rev v) (f0 >> f1 >> f0 >> f0 >> l))
    <{{D}} (f1 >> r)).
Proof.
  remember (List.length v) as n eqn:Hn.
  revert v Hn l r.
  induction n as [n IH] using strong_induction.
  intros v Hn l r. subst n.
  destruct (splitLeading false v) as [k [rest [Hv1 Hrest]]].
  destruct Hrest as [-> | [v' ->]].
  - rewrite app_nil_r in Hv1. subst v.
    destruct k as [|k']; [apply p4b_true |].
    rewrite encWR_rep_false, rev_repeat, encWL_rep_false.
    exact (p4b_false_run k' l r).
  - cbn [negb] in Hv1. subst v.
    assert (Hlen : List.length v' < List.length (List.repeat false k ++ true :: v')).
    { rewrite length_app; cbn [List.length]; rewrite repeat_len; lia. }
    rewrite encWR_append, encWR_rep_false; cbn [encWR].
    assert (Hhead1 : exists rt : side, encWR v' (f1 >> f0 >> f0 >> f0 >> f1 >> r) = f1 >> rt).
    { destruct v' as [|[|] ?]; eexists; reflexivity. }
    destruct Hhead1 as [rt Hrt].
    assert (H1 : ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> l) <{{D}}
                   (repBits [true; true; true; false] k (f1 >> f0 >> f0 >> f0 >> encWR v' (f1 >> f0 >> f0 >> f0 >> f1 >> r)))) -[ tm ]->*
                 ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] k (f0 >> f1 >> f0 >> f0 >> l))
                   <{{D}} (encWR v' (f1 >> f0 >> f0 >> f0 >> f1 >> r)))).
    { rewrite Hrt. destruct k as [|k']; [apply p4b_true | apply p4b_false_run]. }
    pose proof (IH (List.length v') Hlen v' eq_refl (repBits [true; false; false; false] k (f0 >> f1 >> f0 >> f0 >> l)) r) as H2.
    assert (HL : encWL (List.rev v') (f0 >> f1 >> f0 >> f0 >> repBits [true; false; false; false] k (f0 >> f1 >> f0 >> f0 >> l)) =
                 encWL (List.rev (List.repeat false k ++ true :: v')) (f0 >> f1 >> f0 >> f0 >> l)).
    { rewrite List.rev_app_distr; cbn [List.rev app]; rewrite rev_repeat, !encWL_append, encWL_rep_false; cbn [encWL].
      reflexivity. }
    rewrite HL in H2.
    eapply evstep_trans; [exact H1 | exact H2].
Qed.

Lemma pass4_111_reaches (v : list bool) (l r : side) :
  ((f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l) <{{D}}
    (f1 >> f1 >> f1 >> f0 >> encWR v (f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r))) -[ tm ]->*
  ((f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> encWL (List.rev v) (f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l))
    <{{D}} (f1 >> f1 >> f1 >> r)).
Proof.
  destruct (splitLeading false v) as [k [rest [Hv1 Hrest]]].
  destruct Hrest as [-> | [v' ->]].
  - rewrite app_nil_r in Hv1. subst v.
    rewrite encWR_rep_false, rev_repeat, encWL_rep_false.
    pose proof (progress_evstep _ _ _ (stepE_10 (f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l)
                         (f1 >> f1 >> f1 >> f0 >> repBits [true; true; true; false] k (f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r)))) as H1.
    pose proof (loop_sb_fwd (S k) (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l)
                                  (f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r)) as H2.
    change (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l)
      with (decBits [false; true; false; false] (f0 >> f1 >> f0 >> f1 >> f0 >> l)) in H2.
    rewrite <- repBits_succ_right in H2.
    pose proof (pass4_bounce (S k) l (f1 >> f1 >> r)) as H3.
    assert (HL3 : f1 >> f0 >> f0 >> repBits [true; false; false; false] (S (S k)) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l) =
                  f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] k (f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)).
    { change (repBits [true; false; false; false] (S (S k)) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l))
        with (f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] (S k) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)).
      rewrite (repBits_succ_right [true; false; false; false] k). reflexivity. }
    rewrite HL3 in H3.
    eapply evstep_trans; [exact H1 |].
    eapply evstep_trans; [exact H2 | exact H3].
  - cbn [negb] in Hv1. subst v.
    rewrite encWR_append, encWR_rep_false; cbn [encWR].
    assert (Hhead1 : exists rt : side, encWR v' (f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r) = f1 >> rt).
    { destruct v' as [|[|] ?]; eexists; reflexivity. }
    destruct Hhead1 as [rt Hrt].
    pose proof (progress_evstep _ _ _ (stepE_10 (f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l)
                         (f1 >> f1 >> f1 >> f0 >> repBits [true; true; true; false] k (f1 >> f0 >> f0 >> f0 >> encWR v' (f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r))))) as H1.
    assert (H2 : ((f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l) {{A}}>
                   (f1 >> f1 >> f1 >> f0 >> repBits [true; true; true; false] k (f1 >> f0 >> f0 >> f0 >> encWR v' (f1 >> f0 >> f0 >> f0 >> f1 >> f1 >> f1 >> r)))) -[ tm ]->*
                 (repBits [false; true; false; false] (S (S k)) (f0 >> f1 >> f0 >> f1 >> f0 >> l)
                   {{A}}> (f1 >> f0 >> f0 >> f0 >> f1 >> rt))).
    { rewrite Hrt.
      pose proof (loop_sb_fwd (S k) (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l) (f0 >> f0 >> f0 >> f1 >> rt)) as Hs.
      change (f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l)
        with (decBits [false; true; false; false] (f0 >> f1 >> f0 >> f1 >> f0 >> l)) in Hs.
      rewrite <- repBits_succ_right in Hs. exact Hs. }
    pose proof (pass4_bounce (S k) l rt) as H3.
    assert (HL3 : f1 >> f0 >> f0 >> repBits [true; false; false; false] (S (S k)) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l) =
                  f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] k (f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)).
    { change (repBits [true; false; false; false] (S (S k)) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l))
        with (f1 >> f0 >> f0 >> f0 >> repBits [true; false; false; false] (S k) (f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)).
      rewrite (repBits_succ_right [true; false; false; false] k). reflexivity. }
    rewrite HL3 in H3.
    pose proof (p4b_all v' (repBits [true; false; false; false] k (f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)) (f1 >> f1 >> r)) as H4.
    rewrite Hrt in H4.
    assert (HL4 : encWL (List.rev v') (f0 >> f1 >> f0 >> f0 >> repBits [true; false; false; false] k (f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)) =
                  encWL (List.rev (List.repeat false k ++ true :: v')) (f1 >> f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> l)).
    { rewrite List.rev_app_distr; cbn [List.rev app]; rewrite rev_repeat, !encWL_append, encWL_rep_false; cbn [encWL].
      reflexivity. }
    rewrite HL4 in H4.
    eapply evstep_trans; [exact H1 |].
    eapply evstep_trans; [exact H2 |].
    eapply evstep_trans; [exact H3 | exact H4].
Qed.

(** ** 6. Periodic-66 ([P66]) Encodings, Peel/Scan Commutation, and 5 Macro Rules *)

Definition plTopIs1 (n : nat) : bool :=
  match n with
  | 0 | 1 | 5 | 9 | 14 | 15 | 20 | 23 | 28 | 29 | 33 | 38 | 39 | 44 | 47 | 51 | 56 | 57 | 61 => true
  | _ => false
  end.

Definition prTopIs1 (n : nat) : bool :=
  match n with
  | 0 | 4 | 8 | 12 | 14 | 18 | 22 | 24 | 28 | 32 | 36 | 38 | 39 | 40 | 42 | 46 | 50 | 52 | 56 | 60 | 62 | 63 | 64 => true
  | _ => false
  end.

Definition prev66 (n : nat) : nat :=
  match n with
  | 0 => 65
  | S k => k
  end.

Definition pL0List : list bool :=
  [true; false; false; false; false; true; false; false; false; true; true;
   false; false; false; false; true; false; false; false; true; false; false;
   true; false; false; false; false; true; true; false; false; false; false;
   true; false; false; false; true; true; false; false; false; false; true;
   false; false; true; false; false; false; false; true; true; false; false;
   false; false; true; false; false; false; true; false; false; false; true].

Definition pR0List : list bool :=
  [true; false; true; true; true; false; true; false; false; false; true;
   false; false; false; true; false; true; false; false; false; true; false;
   false; false; true; false; true; true; true; false; true; false; false;
   false; true; false; false; false; true; false; false; false; true; false;
   true; false; false; false; true; false; false; false; true; false; true;
   false; false; false; true; false; false; false; true; false; false; false].

Definition rotList (u : list bool) (k : nat) : list bool :=
  skipn k u ++ firstn k u.

Definition pLList (r : nat) : list bool := rotList pL0List ((66 - r mod 66) mod 66).
Definition pRList (r : nat) : list bool := rotList pR0List ((66 - r mod 66) mod 66).

Lemma prev66_lt (r : nat) : r < 66 -> prev66 r < 66.
Proof. destruct r; cbn [prev66]; lia. Qed.

Definition pLBits (r : nat) (lb : side) : side := decBits (pLList r) lb.
Definition pRBits (r : nat) (lb : side) : side := decBits (pRList r) lb.

Fixpoint repPL (r c : nat) (lb : side) : side :=
  match c with
  | 0 => lb
  | S c' => pLBits r (repPL r c' lb)
  end.

Fixpoint repPR (r c : nat) (lb : side) : side :=
  match c with
  | 0 => lb
  | S c' => pRBits r (repPR r c' lb)
  end.

Lemma repPL_add (r a b : nat) (lb : side) :
  repPL r (a + b) lb = repPL r a (repPL r b lb).
Proof.
  induction a as [|a IH]; [reflexivity |].
  cbn [Nat.add repPL]. rewrite IH. reflexivity.
Qed.

Lemma repPL_succ_right (r c : nat) (lb : side) :
  repPL r c (pLBits r lb) = repPL r (S c) lb.
Proof.
  induction c as [|c IH]; [reflexivity | cbn [repPL]; rewrite IH; reflexivity].
Qed.

Lemma repPR_succ_right (r c : nat) (lb : side) :
  repPR r c (pRBits r lb) = repPR r (S c) lb.
Proof.
  induction c as [|c IH]; [reflexivity | cbn [repPR]; rewrite IH; reflexivity].
Qed.

Fixpoint beqBoolList (a b : list bool) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Bool.eqb x y && beqBoolList xs ys
  | _, _ => false
  end.

Lemma beqBoolList_eq (a b : list bool) : beqBoolList a b = true -> a = b.
Proof.
  revert b. induction a as [|x xs IH]; intros [|y ys] H; try discriminate H; [reflexivity |].
  cbn [beqBoolList] in H. apply Bool.andb_true_iff in H as [Hxy Hrest].
  apply Bool.eqb_prop in Hxy. subst y. f_equal. exact (IH ys Hrest).
Qed.

Fixpoint checkAllNat (f : nat -> bool) (n : nat) : bool :=
  match n with
  | 0 => true
  | S k => f k && checkAllNat f k
  end.

Lemma checkAllNat_spec (f : nat -> bool) (n : nat) :
  checkAllNat f n = true -> forall r, r < n -> f r = true.
Proof.
  induction n as [|n IH]; intros H r Hr; [lia |].
  cbn [checkAllNat] in H. apply Bool.andb_true_iff in H as [Hn Hrest].
  destruct (Nat.eq_dec r n) as [-> | Hne]; [exact Hn | apply IH; [exact Hrest | lia]].
Qed.

Lemma pLList_comm (r : nat) (Hr : r < 66) :
  plTopIs1 r :: pLList (prev66 r) = pLList r ++ [plTopIs1 r].
Proof.
  apply beqBoolList_eq.
  apply (checkAllNat_spec (fun k => beqBoolList (plTopIs1 k :: pLList (prev66 k)) (pLList k ++ [plTopIs1 k])) 66);
    [vm_compute; reflexivity | exact Hr].
Qed.

Lemma pRList_comm (r : nat) (Hr : r < 66) :
  prTopIs1 r :: pRList (prev66 r) = pRList r ++ [prTopIs1 r].
Proof.
  apply beqBoolList_eq.
  apply (checkAllNat_spec (fun k => beqBoolList (prTopIs1 k :: pRList (prev66 k)) (pRList k ++ [prTopIs1 k])) 66);
    [vm_compute; reflexivity | exact Hr].
Qed.

Lemma pLBits_comm (r : nat) (Hr : r < 66) (lb : side) :
  finOfBool (plTopIs1 r) >> pLBits (prev66 r) lb = pLBits r (finOfBool (plTopIs1 r) >> lb).
Proof.
  unfold pLBits. rewrite <- decBits_cons, (pLList_comm r Hr), decBits_append, decBits_cons.
  reflexivity.
Qed.

Lemma pRBits_comm (r : nat) (Hr : r < 66) (lb : side) :
  finOfBool (prTopIs1 r) >> pRBits (prev66 r) lb = pRBits r (finOfBool (prTopIs1 r) >> lb).
Proof.
  unfold pRBits. rewrite <- decBits_cons, (pRList_comm r Hr), decBits_append, decBits_cons.
  reflexivity.
Qed.

Lemma repPL_comm (r : nat) (Hr : r < 66) (c : nat) (lb : side) :
  finOfBool (plTopIs1 r) >> repPL (prev66 r) c lb = repPL r c (finOfBool (plTopIs1 r) >> lb).
Proof.
  induction c as [|c IH]; [reflexivity |].
  cbn [repPL]. rewrite (pLBits_comm r Hr), IH. reflexivity.
Qed.

Lemma repPR_comm (r : nat) (Hr : r < 66) (c : nat) (lb : side) :
  finOfBool (prTopIs1 r) >> repPR (prev66 r) c lb = repPR r c (finOfBool (prTopIs1 r) >> lb).
Proof.
  induction c as [|c IH]; [reflexivity |].
  cbn [repPR]. rewrite (pRBits_comm r Hr), IH. reflexivity.
Qed.

Lemma p66_L16 (l r : side) :
  (pLBits 16 l <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> pRBits 64 r)).
Proof. unfold pLBits, pRBits; replayWindow 1024. Qed.

Lemma p66_L9 (l r : side) :
  (pLBits 9 l <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> pRBits 36 r)).
Proof. unfold pLBits, pRBits; replayWindow 1024. Qed.

Lemma p66_L29 (l r : side) :
  (pLBits 29 l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> pRBits 14 r)).
Proof. unfold pLBits, pRBits; replayWindow 1024. Qed.

Lemma p66_R63 (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> l) <{{D}} (f1 >> pRBits 63 r)) -[ tm ]->*
    ((f1 >> f0 >> f0 >> f1 >> f0 >> pLBits 14 l) <{{D}} (f1 >> r)).
Proof. unfold pLBits, pRBits; replayWindow 1024. Qed.

Lemma p66_R4 (l r : side) :
  ((f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l) <{{D}} (f0 >> pRBits 4 r)) -[ tm ]->*
    ((f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> pLBits 4 l) <{{D}} (f0 >> r)).
Proof. unfold pLBits, pRBits; replayWindow 1024. Qed.

Lemma p66_L16_rep (c : nat) (l r : side) :
  (repPL 16 c l <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> repPR 64 c r)).
Proof.
  exact (repeatSweep (fun l r => l <{{D}} (f0 >> f0 >> f0 >> r)) (pLBits 16) (pRBits 64)
    (repPL 16) (repPR 64) (fun _ => eq_refl) (fun _ => eq_refl)
    (fun _ _ => eq_refl) (fun n r => eq_sym (repPR_succ_right 64 n r)) p66_L16 c l r).
Qed.

Lemma p66_L9_rep (c : nat) (l r : side) :
  (repPL 9 c l <{{D}} (f0 >> f0 >> f0 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> repPR 36 c r)).
Proof.
  exact (repeatSweep (fun l r => l <{{D}} (f0 >> f0 >> f0 >> r)) (pLBits 9) (pRBits 36)
    (repPL 9) (repPR 36) (fun _ => eq_refl) (fun _ => eq_refl)
    (fun _ _ => eq_refl) (fun n r => eq_sym (repPR_succ_right 36 n r)) p66_L9 c l r).
Qed.

Lemma p66_L29_rep (c : nat) (l r : side) :
  (repPL 29 c l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> r)) -[ tm ]->*
    (l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> repPR 14 c r)).
Proof.
  exact (repeatSweep (fun l r => l <{{D}} (f0 >> f0 >> f0 >> f1 >> f1 >> r)) (pLBits 29) (pRBits 14)
    (repPL 29) (repPR 14) (fun _ => eq_refl) (fun _ => eq_refl)
    (fun _ _ => eq_refl) (fun n r => eq_sym (repPR_succ_right 14 n r)) p66_L29 c l r).
Qed.

Lemma p66_R63_rep (c : nat) (l r : side) :
  ((f1 >> f0 >> f0 >> f1 >> f0 >> l) <{{D}} (f1 >> repPR 63 c r)) -[ tm ]->*
    ((f1 >> f0 >> f0 >> f1 >> f0 >> repPL 14 c l) <{{D}} (f1 >> r)).
Proof.
  exact (repeatSweep (fun r l => (f1 >> f0 >> f0 >> f1 >> f0 >> l) <{{D}} (f1 >> r)) (pRBits 63) (pLBits 14)
    (repPR 63) (repPL 14) (fun _ => eq_refl) (fun _ => eq_refl)
    (fun _ _ => eq_refl) (fun n r => eq_sym (repPL_succ_right 14 n r)) (fun r l => p66_R63 l r) c r l).
Qed.

Lemma p66_R4_rep (c : nat) (l r : side) :
  ((f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l) <{{D}} (f0 >> repPR 4 c r)) -[ tm ]->*
    ((f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> repPL 4 c l) <{{D}} (f0 >> r)).
Proof.
  exact (repeatSweep (fun r l => (f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f1 >> f0 >> l) <{{D}} (f0 >> r)) (pRBits 4) (pLBits 4)
    (repPR 4) (repPL 4) (fun _ => eq_refl) (fun _ => eq_refl)
    (fun _ _ => eq_refl) (fun n r => eq_sym (repPL_succ_right 4 n r)) (fun r l => p66_R4 l r) c r l).
Qed.

(** ** 7. Symbolic [Chunk] / [RState] Representation & [stepFast] Engine *)

Inductive Chunk : Type :=
  | b0 : Chunk
  | b1 : Chunk
  | wL : bool -> Chunk
  | wR : bool -> Chunk
  | pL : nat -> Chunk
  | pR : nat -> Chunk.

Inductive RState : Type :=
  | RState_mk : bool -> list Chunk -> list Chunk -> RState.

Inductive OptList : Type :=
  | OptList_none : OptList
  | OptList_some : list Chunk -> OptList.

Inductive OptPair : Type :=
  | OptPair_none : OptPair
  | OptPair_some : list Chunk -> list Chunk -> OptPair.

Definition matchBit (b : bool) (ch : Chunk) : bool :=
  match b, ch with
  | false, b0 => true
  | true,  b1 => true
  | _,     _  => false
  end.

Fixpoint scanPL (fuel rCur : nat) (xs : list Chunk) : OptList :=
  match xs with
  | pL r :: rest => if Nat.eqb r rCur then OptList_some rest else OptList_none
  | ch :: rest =>
    match fuel with
    | 0 => OptList_none
    | S fuel' =>
      if matchBit (plTopIs1 rCur) ch then
        match scanPL fuel' (prev66 rCur) rest with
        | OptList_none => OptList_none
        | OptList_some out => OptList_some (ch :: out)
        end
      else OptList_none
    end
  | [] => OptList_none
  end.

Fixpoint scanPR (fuel rCur : nat) (xs : list Chunk) : OptList :=
  match xs with
  | pR r :: rest => if Nat.eqb r rCur then OptList_some rest else OptList_none
  | ch :: rest =>
    match fuel with
    | 0 => OptList_none
    | S fuel' =>
      if matchBit (prTopIs1 rCur) ch then
        match scanPR fuel' (prev66 rCur) rest with
        | OptList_none => OptList_none
        | OptList_some out => OptList_some (ch :: out)
        end
      else OptList_none
    end
  | [] => OptList_none
  end.

Fixpoint stripBits (pat : list bool) (xs : list Chunk) : OptList :=
  match pat with
  | [] => OptList_some xs
  | b :: pat' =>
    match xs with
    | ch :: xs' => if matchBit b ch then stripBits pat' xs' else OptList_none
    | [] => OptList_none
    end
  end.

Fixpoint preBits (pat : list bool) (tl : list Chunk) : list Chunk :=
  match pat with
  | [] => tl
  | false :: pat' => b0 :: preBits pat' tl
  | true  :: pat' => b1 :: preBits pat' tl
  end.

Definition pL0_66  : list bool := Eval vm_compute in pLList 0.
Definition pL14_66 : list bool := Eval vm_compute in pLList 14.
Definition pL16_66 : list bool := Eval vm_compute in pLList 16.
Definition pL9_66  : list bool := Eval vm_compute in pLList 9.
Definition pL29_66 : list bool := Eval vm_compute in pLList 29.
Definition pR64_66 : list bool := Eval vm_compute in pRList 64.
Definition pR36_66 : list bool := Eval vm_compute in pRList 36.
Definition pR14_66 : list bool := Eval vm_compute in pRList 14.
Definition pR63_66 : list bool := Eval vm_compute in pRList 63.

Definition stripP16 (xs : list Chunk) : OptList := stripBits pL16_66 xs.
Definition stripP9  (xs : list Chunk) : OptList := stripBits pL9_66 xs.
Definition stripP29 (xs : list Chunk) : OptList := stripBits pL29_66 xs.
Definition stripR63 (xs : list Chunk) : OptList := stripBits pR63_66 xs.

Definition preR64 (tl : list Chunk) : list Chunk := preBits pR64_66 tl.
Definition preR36 (tl : list Chunk) : list Chunk := preBits pR36_66 tl.
Definition preR14 (tl : list Chunk) : list Chunk := preBits pR14_66 tl.
Definition preP14 (tl : list Chunk) : list Chunk := preBits pL14_66 tl.
Definition prePL0 (tl : list Chunk) : list Chunk := preBits pL0_66 tl.

(** Consume explicit copies of a finite period. A failed prefix match
    stops normally and leaves both the remaining tape and accumulator. *)
Fixpoint loopSweep (strip : list Chunk -> OptList)
    (push : list Chunk -> list Chunk) (k : nat) (xs acc : list Chunk) : OptPair :=
  match k with
  | 0 => OptPair_some xs acc
  | S k' =>
    match strip xs with
    | OptList_some xs' => loopSweep strip push k' xs' (push acc)
    | OptList_none => OptPair_some xs acc
    end
  end.

Definition loopP16 := loopSweep stripP16 preR64.
Definition loopP9 := loopSweep stripP9 preR36.
Definition loopP29 := loopSweep stripP29 preR14.
Definition loopR63 := loopSweep stripR63 preP14.

Fixpoint scanLeftB_p0 (k : nat) (xs accR : list Chunk) : OptPair :=
  match xs with
  | b0 :: b1 :: b0 :: b0 :: b1 :: b0 :: b0 :: restL => OptPair_some restL accR
  | b0 :: b1 :: b0 :: b0 :: restL =>
    match k with
    | 0 => OptPair_none
    | S k' => scanLeftB_p0 k' restL (b0 :: b1 :: b1 :: b1 :: accR)
    end
  | b1 :: b0 :: b0 :: b0 :: restL =>
    match k with
    | 0 => OptPair_none
    | S k' => scanLeftB_p0 k' restL (b0 :: b1 :: b0 :: b0 :: accR)
    end
  | _ => OptPair_none
  end.

Fixpoint scanLeftB_p1 (k : nat) (xs accR : list Chunk) : OptPair :=
  match xs with
  | b0 :: b1 :: b0 :: b0 :: b1 :: b0 :: b0 :: restL => OptPair_some restL accR
  | b0 :: b1 :: b0 :: b0 :: restL =>
    match k with
    | 0 => OptPair_none
    | S k' => scanLeftB_p1 k' restL (b1 :: b1 :: b1 :: b0 :: accR)
    end
  | b1 :: b0 :: b0 :: b0 :: restL =>
    match k with
    | 0 => OptPair_none
    | S k' => scanLeftB_p1 k' restL (b1 :: b0 :: b0 :: b0 :: accR)
    end
  | _ => OptPair_none
  end.

Fixpoint scanRightQ1 (k : nat) (xs accL : list Chunk) : OptPair :=
  match xs with
  | b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: restR => OptPair_some accL restR
  | b0 :: b0 :: b0 :: b1 :: restR =>
    match k with
    | 0 => OptPair_none
    | S k' => scanRightQ1 k' restR (b0 :: b1 :: b0 :: b0 :: accL)
    end
  | b1 :: b1 :: b0 :: b1 :: restR =>
    match k with
    | 0 => OptPair_none
    | S k' => scanRightQ1 k' restR (b1 :: b0 :: b0 :: b0 :: accL)
    end
  | _ => OptPair_none
  end.

Fixpoint concSafeLeftA (l accR : list Chunk) : OptPair :=
  match l with
  | b1 :: b0 :: b0 :: b0 :: restL => concSafeLeftA restL (b1 :: b1 :: b1 :: b0 :: accR)
  | b0 :: b1 :: b0 :: b0 :: restL => concSafeLeftA restL (b1 :: b0 :: b0 :: b0 :: accR)
  | _ => OptPair_some l accR
  end.

Fixpoint concSafeRightGo (had1 : bool) (xs accL : list Chunk) (best : OptPair) : OptPair :=
  match xs with
  | b0 :: b0 :: b0 :: b1 :: ((b0 :: b0 :: b0 :: b1 :: restR) as tail4) =>
    if had1 then
      let ck := OptPair_some accL restR in
      concSafeRightGo true tail4 (b0 :: b1 :: b0 :: b0 :: accL) ck
    else
      concSafeRightGo true tail4 (b0 :: b1 :: b0 :: b0 :: accL) best
  | b0 :: b0 :: b0 :: b1 :: restR =>
    concSafeRightGo true restR (b0 :: b1 :: b0 :: b0 :: accL) best
  | b1 :: b1 :: b0 :: b1 :: restR =>
    concSafeRightGo true restR (b1 :: b0 :: b0 :: b0 :: accL) best
  | _ => best
  end.

Fixpoint concSafeLeftBGo (had1 : bool) (xs accR : list Chunk) (best : OptPair) : OptPair :=
  match xs with
  | b0 :: b0 :: b1 :: b0 :: ((b0 :: b1 :: b0 :: b0 :: restL) as tail4) =>
    if had1 then
      let ck := OptPair_some restL accR in
      concSafeLeftBGo true tail4 (b0 :: b1 :: b1 :: b1 :: accR) ck
    else
      concSafeLeftBGo true tail4 (b0 :: b1 :: b1 :: b1 :: accR) best
  | b0 :: b0 :: b1 :: b0 :: restL =>
    concSafeLeftBGo true restL (b0 :: b1 :: b1 :: b1 :: accR) best
  | b0 :: b1 :: b0 :: b0 :: restL =>
    concSafeLeftBGo true restL (b0 :: b1 :: b0 :: b0 :: accR) best
  | _ => best
  end.

Fixpoint scanSuperBounce (xs : list Chunk) : OptList :=
  match xs with
  | b0 :: b1 :: b0 :: b0 :: restL =>
    match scanSuperBounce restL with
    | OptList_none => OptList_none
    | OptList_some out => OptList_some (b0 :: b1 :: b0 :: b0 :: out)
    end
  | b0 :: b1 :: b0 :: b1 :: b0 :: restL =>
    OptList_some (b0 :: b1 :: b0 :: b0 :: b0 :: b0 :: b1 :: restL)
  | _ => OptList_none
  end.

(* A bridge consumes one literal quartet and pushes one output block.
   The view chooses the scanned side and restores the fixed hub collars. *)
Definition literalChunk (b : bool) : Chunk := if b then b1 else b0.

Fixpoint bridgeSweep (view : list Chunk -> list Chunk -> RState)
    (a b d e : bool) (out : list Chunk) (xs acc : list Chunk) : RState :=
  match xs with
  | x :: y :: z :: t :: rest =>
      if matchBit a x && matchBit b y && matchBit d z && matchBit e t
      then bridgeSweep view a b d e out rest (out ++ acc)
      else view xs acc
  | _ => view xs acc
  end.

Definition br1Loop (l r : list Chunk) : RState :=
  bridgeSweep (fun l r => RState_mk true l r)
    true true false false [b0;b0;b0;b1] l r.

Definition br2Loop (l r : list Chunk) : RState :=
  bridgeSweep (fun l r => RState_mk true l r)
    false true false false [b0;b0;b0;b1] l r.

Definition br3Loop (l r : list Chunk) : RState :=
  bridgeSweep (fun r l => RState_mk false l r)
    false false true false [b1;b0;b0;b1] r l.

Definition br4Loop (l r : list Chunk) : RState :=
  bridgeSweep (fun r l => RState_mk true (b1 :: b0 :: b0 :: b0 :: l) (b1 :: r))
    true true false true [b0;b1;b0;b0] r l.

Definition br5Loop (l r : list Chunk) : RState :=
  bridgeSweep (fun r l => RState_mk false l (b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: b1 :: r))
    false false false true [b0;b1;b0;b0] r l.

Definition br6Loop (l r : list Chunk) : RState :=
  bridgeSweep (fun r l => RState_mk true (b1 :: b0 :: b0 :: b0 :: l) (b1 :: b0 :: b1 :: b0 :: r))
    false false true false [b0;b0;b1;b0] r l.

Definition br7Loop (l r : list Chunk) : RState :=
  bridgeSweep (fun l r => RState_mk true (b0 :: b1 :: b0 :: b1 :: l) (b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: r))
    true false false true [b1;b1;b0;b1] l r.

Definition peelPLStep (r : nat) (b : Chunk) (rest : list Chunk) : OptList :=
  if Nat.leb r 65 then
    if matchBit (plTopIs1 r) b then OptList_some (b :: pL (prev66 r) :: rest)
    else OptList_none
  else OptList_none.

Definition peelPRStep (r : nat) (b : Chunk) (rest : list Chunk) : OptList :=
  if Nat.leb r 65 then
    if matchBit (prTopIs1 r) b then OptList_some (b :: pR (prev66 r) :: rest)
    else OptList_none
  else OptList_none.

Fixpoint peelPL (k : nat) (xs : list Chunk) : OptList :=
  match xs with
  | [] => OptList_none
  | pL r :: rest =>
    match rest with
    | b :: rest' => peelPLStep r b rest'
    | [] => OptList_none
    end
  | ch :: rest =>
    match k with
    | 0 => OptList_none
    | S k' =>
      match peelPL k' rest with
      | OptList_none => OptList_none
      | OptList_some out => OptList_some (ch :: out)
      end
    end
  end.

Fixpoint peelPR (k : nat) (xs : list Chunk) : OptList :=
  match xs with
  | [] => OptList_none
  | pR r :: rest =>
    match rest with
    | b :: rest' => peelPRStep r b rest'
    | [] => OptList_none
    end
  | ch :: rest =>
    match k with
    | 0 => OptList_none
    | S k' =>
      match peelPR k' rest with
      | OptList_none => OptList_none
      | OptList_some out => OptList_some (ch :: out)
      end
    end
  end.

Definition pop1B_fallback (l r : list Chunk) : RState :=
  match peelPR 4 r with
  | OptList_some r' => RState_mk false l r'
  | OptList_none => RState_mk false l r
  end.

Fixpoint pop1B (l r : list Chunk) : RState :=
  match r with
  | b1 :: r' => pop1B (b0 :: l) r'
  | b0 :: b1 :: r' => RState_mk true (b1 :: l) (b1 :: r')
  | b0 :: b0 :: b0 :: r' => RState_mk true (b0 :: b1 :: l) (b0 :: r')
  | b0 :: b0 :: b1 :: b0 :: r' => RState_mk false (b1 :: b0 :: b0 :: b1 :: l) r'
  | b0 :: b0 :: b1 :: b1 :: r' => RState_mk true (b1 :: l) (b0 :: b0 :: b0 :: r')
  | [] => RState_mk true (b0 :: b1 :: l) [b0]
  | [b0] => RState_mk true (b0 :: b1 :: l) [b0]
  | [b0; b0] => RState_mk true (b0 :: b1 :: l) [b0]
  | [b0; b0; b1] => RState_mk false (b1 :: b0 :: b0 :: b1 :: l) []
  | _ => pop1B_fallback l r
  end.

Definition pop10E_fallback (l r : list Chunk) : RState :=
  match peelPL 4 l with
  | OptList_some l' => RState_mk true l' r
  | OptList_none =>
    match peelPR 4 r with
    | OptList_some r' => RState_mk true l r'
    | OptList_none => RState_mk true l r
    end
  end.

Fixpoint pop10E (l r : list Chunk) : RState :=
  match l, r with
  | b0 :: b1 :: l', _ => pop10E l' (b1 :: b1 :: r)
  | b0 :: b0 :: l', b0 :: r' => RState_mk false (b1 :: b0 :: b0 :: l') r'
  | b0 :: b0 :: l', [] => RState_mk false (b1 :: b0 :: b0 :: l') []
  | b0 :: b0 :: l', b1 :: r' => RState_mk true l' (b0 :: b0 :: b0 :: r')
  | [b0], b0 :: r' => RState_mk false [b1; b0; b0] r'
  | [b0], [] => RState_mk false [b1; b0; b0] []
  | [b0], b1 :: r' => RState_mk true [] (b0 :: b0 :: b0 :: r')
  | [], b0 :: r' => RState_mk false [b1; b0; b0] r'
  | [], [] => RState_mk false [b1; b0; b0] []
  | [], b1 :: r' => RState_mk true [] (b0 :: b0 :: b0 :: r')
  | b1 :: b0 :: l', _ => RState_mk false (b0 :: b1 :: l') r
  | [b1], _ => RState_mk false [b0; b1] r
  | b1 :: b1 :: b0 :: b0 :: l', _ => RState_mk true l' (b0 :: b0 :: b0 :: b1 :: r)
  | [b1; b1; b0], _ => RState_mk true [] (b0 :: b0 :: b0 :: b1 :: r)
  | [b1; b1], _ => RState_mk true [] (b0 :: b0 :: b0 :: b1 :: r)
  | b1 :: b1 :: b0 :: b1 :: l', _ => RState_mk false (b1 :: b0 :: l') (b0 :: b1 :: r)
  | _, _ => pop10E_fallback l r
  end.

Definition stepB_1111010 (l r restR : list Chunk) : RState :=
  match restR with
  | wR f :: b1 :: restR2 =>
    match l with
    | b0 :: b1 :: b0 :: b0 :: restL =>
      match scanRightQ1 64 restR2 (wL f :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: restL) with
      | OptPair_some outL restR' =>
        RState_mk false (b0 :: b1 :: b0 :: b0 :: outL) (b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: b1 :: restR')
      | OptPair_none => pop1B l r
      end
    | _ => pop1B l r
    end
  | b1 :: restR1 =>
    match l with
    | b0 :: b1 :: b0 :: b0 :: restL =>
      match concSafeRightGo false restR1 (b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: restL) OptPair_none with
      | OptPair_some outL restR' =>
        RState_mk false (b0 :: b1 :: b0 :: b0 :: outL) (b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: b1 :: restR')
      | OptPair_none =>
        match restR1 with
        | b0 :: b0 :: b0 :: b1 :: restR5 => br5Loop (b0 :: b1 :: b0 :: b0 :: l) restR5
        | _ => pop1B l r
        end
      end
    | _ =>
      match restR1 with
      | b0 :: b0 :: b0 :: b1 :: restR5 => br5Loop (b0 :: b1 :: b0 :: b0 :: l) restR5
      | _ => pop1B l r
      end
    end
  | _ => pop1B l r
  end.

Definition stepFalse (l r : list Chunk) : RState :=
  match r with
  | b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: restR => stepB_1111010 l r restR
  | b0 :: b0 :: b1 :: b0 :: restR => br3Loop (b1 :: b0 :: b0 :: b1 :: l) restR
  | _ => pop1B l r
  end.

Definition stepE_000_rest (l r restR : list Chunk) : RState :=
  match l with
  | b0 :: b1 :: b0 :: b0 :: _ =>
    match concSafeLeftA l restR with
    | OptPair_some l' r' => RState_mk true l' (b0 :: b0 :: b0 :: r')
    | OptPair_none => pop10E l r
    end
  | b1 :: b0 :: b0 :: b0 :: _ =>
    match concSafeLeftA l restR with
    | OptPair_some l' r' => RState_mk true l' (b0 :: b0 :: b0 :: r')
    | OptPair_none => pop10E l r
    end
  | b0 :: b0 :: b1 :: b0 :: _ =>
    match restR with
    | b1 :: b1 :: b1 :: b1 :: b1 :: restR8 =>
      match concSafeLeftBGo false l (b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: restR8) OptPair_none with
      | OptPair_some l' outR => RState_mk true l' (b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: b1 :: b1 :: outR)
      | OptPair_none => pop10E l r
      end
    | _ => pop10E l r
    end
  | b0 :: b1 :: b0 :: b1 :: b1 :: b0 :: b0 :: b1 :: restL =>
    match restR with
    | b1 :: b0 :: b0 :: b0 :: b1 :: restR8 => br7Loop restL (b1 :: b1 :: b0 :: b1 :: restR8)
    | _ => pop10E l r
    end
  | b1 :: b1 :: b0 :: b0 :: restL => br1Loop restL (b0 :: b0 :: b0 :: b1 :: r)
  | _ => pop10E l r
  end.

Definition stepE_000_p66 (l r restR : list Chunk) : RState :=
  match l with
  | pL 16 :: l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 64 :: restR)
  | pL 9 :: l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 36 :: restR)
  | pL 29 :: l' =>
    match restR with
    | b1 :: b1 :: restR5 => RState_mk true l' (b0 :: b0 :: b0 :: b1 :: b1 :: pR 14 :: restR5)
    | _ => pop10E l r
    end
  | b0 :: b1 :: b1 :: b0 :: _ =>
    match scanPL 66 16 l with
    | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 64 :: restR)
    | OptList_none =>
      match stripP16 l with
      | OptList_some l1 =>
        match loopP16 64 l1 (preR64 restR) with
        | OptPair_some l' r' => RState_mk true l' (b0 :: b0 :: b0 :: r')
        | OptPair_none => pop10E l r
        end
      | OptList_none => pop10E l r
      end
    end
  | b1 :: b0 :: b0 :: b0 :: _ =>
    match scanPL 66 9 l with
    | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 36 :: restR)
    | OptList_none =>
      match stripP9 l with
      | OptList_some l1 =>
        match loopP9 64 l1 (preR36 restR) with
        | OptPair_some l' r' => RState_mk true l' (b0 :: b0 :: b0 :: r')
        | OptPair_none => stepE_000_rest l r restR
        end
      | OptList_none => stepE_000_rest l r restR
      end
    end
  | b1 :: b1 :: b0 :: b0 :: _ =>
    match restR with
    | b1 :: b1 :: restR5 =>
      match scanPL 66 29 l with
      | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: b1 :: b1 :: pR 14 :: restR5)
      | OptList_none =>
        match stripP29 l with
        | OptList_some l1 =>
          match loopP29 64 l1 (preR14 restR5) with
          | OptPair_some l' r' => RState_mk true l' (b0 :: b0 :: b0 :: b1 :: b1 :: r')
          | OptPair_none => stepE_000_rest l r restR
          end
        | OptList_none => stepE_000_rest l r restR
        end
      end
    | _ => stepE_000_rest l r restR
    end
  | b0 :: _ =>
    match scanPL 66 16 l with
    | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 64 :: restR)
    | OptList_none => stepE_000_rest l r restR
    end
  | b1 :: _ =>
    match scanPL 66 9 l with
    | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 36 :: restR)
    | OptList_none =>
      match restR with
      | b1 :: b1 :: restR5 =>
        match scanPL 66 29 l with
        | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: b1 :: b1 :: pR 14 :: restR5)
        | OptList_none => stepE_000_rest l r restR
        end
      | _ => stepE_000_rest l r restR
      end
    end
  | _ => stepE_000_rest l r restR
  end.

Definition stepE_000 (l r restR : list Chunk) : RState :=
  match l with
  | wL f :: restL => RState_mk true restL (b0 :: b0 :: b0 :: wR f :: restR)
  | b1 :: b0 :: b0 :: wL f :: restL =>
    match scanLeftB_p1 64 restL (wR (negb f) :: b1 :: b1 :: b1 :: b0 :: restR) with
    | OptPair_some restL' outR =>
      RState_mk true restL' (b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: b1 :: b1 :: b0 :: outR)
    | OptPair_none => pop10E l r
    end
  | b0 :: wL f :: restL =>
    match restR with
    | b1 :: b1 :: b1 :: b1 :: b1 :: restR8 =>
      match scanLeftB_p0 64 restL (b0 :: wR (negb f) :: b1 :: b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: restR8) with
      | OptPair_some restL' outR =>
        RState_mk true restL' (b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: b1 :: b1 :: outR)
      | OptPair_none => pop10E l r
      end
    | _ => pop10E l r
    end
  | _ => stepE_000_p66 l r restR
  end.

Definition stepE_1 (l r restR : list Chunk) : RState :=
  match l with
  | b1 :: b0 :: b0 :: b1 :: b0 :: restL =>
    match scanPR 66 63 restR with
    | OptList_some r' => RState_mk true (b1 :: b0 :: b0 :: b1 :: b0 :: pL 14 :: restL) (b1 :: r')
    | OptList_none =>
      match stripR63 restR with
      | OptList_some r1 =>
        match loopR63 64 r1 (preP14 restL) with
        | OptPair_some r' l' => RState_mk true (b1 :: b0 :: b0 :: b1 :: b0 :: l') (b1 :: r')
        | OptPair_none => pop10E l r
        end
      | OptList_none => pop10E l r
      end
    end
  | b1 :: b0 :: b0 :: b0 :: restL =>
    match restR with
    | b1 :: b1 :: b0 :: wR f :: b1 :: b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: restR12 =>
      match restL with
      | b0 :: b1 :: b0 :: b1 :: b0 :: restL9 =>
        RState_mk true (b1 :: b0 :: b0 :: b1 :: b0 :: b0 :: b0 :: wL f :: b1 :: b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: b0 :: b0 :: b1 :: restL9)
                       (b1 :: b1 :: b1 :: restR12)
      | _ => pop10E l r
      end
    | b0 :: b0 :: b0 :: restR4 =>
      match scanSuperBounce restL with
      | OptList_some l' => RState_mk true (b1 :: b0 :: b0 :: b0 :: l') (b1 :: b0 :: restR4)
      | OptList_none => pop10E l r
      end
    | b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b0 :: restR8 =>
      br6Loop (b0 :: b0 :: b1 :: b0 :: restL) restR8
    | b1 :: b1 :: b0 :: b1 :: restR5 =>
      br4Loop (b0 :: b1 :: b0 :: b0 :: restL) restR5
    | _ => pop10E l r
    end
  | b1 :: b1 :: b0 :: b0 :: restL => br1Loop restL (b0 :: b0 :: b0 :: b1 :: r)
  | b0 :: b1 :: b0 :: b0 :: restL => br2Loop restL (b0 :: b0 :: b0 :: b1 :: r)
  | _ => pop10E l r
  end.

Definition stepE_0 (l r restR : list Chunk) : RState :=
  match l with
  | b0 :: b1 :: b0 :: b0 :: b1 :: b0 :: b1 :: b0 :: restL =>
    match scanPR 66 4 restR with
    | OptList_some r' => RState_mk true (b0 :: b1 :: b0 :: b0 :: b1 :: b0 :: b1 :: b0 :: pL 4 :: restL) (b0 :: r')
    | OptList_none => br2Loop (b1 :: b0 :: b1 :: b0 :: restL) (b0 :: b0 :: b0 :: b1 :: r)
    end
  | b1 :: b1 :: b0 :: b0 :: restL => br1Loop restL (b0 :: b0 :: b0 :: b1 :: r)
  | b0 :: b1 :: b0 :: b0 :: restL => br2Loop restL (b0 :: b0 :: b0 :: b1 :: r)
  | _ => pop10E l r
  end.

Definition stepTrue (l r : list Chunk) : RState :=
  match r with
  | b0 :: b0 :: b0 :: restR => stepE_000 l r restR
  | b1 :: restR => stepE_1 l r restR
  | b0 :: restR => stepE_0 l r restR
  | [] =>
    match l with
    | b1 :: b1 :: b0 :: b0 :: restL => br1Loop restL [b0; b0; b0; b1]
    | b0 :: b1 :: b0 :: b0 :: restL => br2Loop restL [b0; b0; b0; b1]
    | _ => pop10E l []
    end
  | _ => pop10E_fallback l r
  end.

Definition stepFast (s : RState) : RState :=
  match s with
  | RState_mk false l r => stepFalse l r
  | RState_mk true  l r => stepTrue l r
  end.

Definition runPos (p : positive) (s : RState) : RState := Pos.iter stepFast s p.

Fixpoint decodeList (w : list bool) (c : nat) (xs : list Chunk) (lb : side) : side :=
  match xs with
  | [] => lb
  | b0 :: xs' => f0 >> decodeList w c xs' lb
  | b1 :: xs' => f1 >> decodeList w c xs' lb
  | wL f :: xs' => encWL (if f then flipW w else w) (decodeList w c xs' lb)
  | wR f :: xs' => encWR (List.rev (if f then flipW w else w)) (decodeList w c xs' lb)
  | pL r :: xs' => repPL r c (decodeList w c xs' lb)
  | pR r :: xs' => repPR r c (decodeList w c xs' lb)
  end.

Definition decode (w : list bool) (c : nat) (s : RState) : Q * tape :=
  match s with
  | RState_mk false l r => decodeList w c l blank {{A}}> decodeList w c r blank
  | RState_mk true  l r => decodeList w c l blank <{{D}} decodeList w c r blank
  end.

Lemma decodeList_append (w : list bool) (c : nat) (a b : list Chunk) (lb : side) :
  decodeList w c (a ++ b) lb = decodeList w c a (decodeList w c b lb).
Proof.
  induction a as [|x xs IH]; [reflexivity |].
  destruct x; cbn [app decodeList]; rewrite IH; reflexivity.
Qed.

Lemma matchBit_eq {b : bool} {ch : Chunk} (H : matchBit b ch = true)
  (w : list bool) (c : nat) (xs : list Chunk) (lb : side) :
  decodeList w c (ch :: xs) lb = finOfBool b >> decodeList w c xs lb.
Proof. destruct b, ch; try discriminate H; reflexivity. Qed.

Lemma list_strong_ind {X : Type} (P : list X -> Prop) :
  (forall xs, (forall ys, List.length ys < List.length xs -> P ys) -> P xs) ->
  forall xs, P xs.
Proof.
  intros Hstep xs.
  remember (List.length xs) as n eqn:Hn.
  revert xs Hn.
  induction n as [n IH] using strong_induction.
  intros xs ->. apply Hstep. intros ys Hlt. exact (IH (List.length ys) Hlt ys eq_refl).
Qed.

Lemma scanPL_spec (fuel rCur : nat) (Hr : rCur < 66) (xs out : list Chunk)
  (H : scanPL fuel rCur xs = OptList_some out) (w : list bool) (c : nat) (lb : side) :
  decodeList w c xs lb = repPL rCur c (decodeList w c out lb).
Proof.
  revert rCur Hr xs out H.
  induction fuel as [|fuel IH]; intros rCur Hr xs out H.
  - destruct xs as [|[ | | | | r | ] rest]; try discriminate H.
    cbn [scanPL] in H. destruct (Nat.eqb r rCur) eqn:Heq; [| discriminate H].
    apply Nat.eqb_eq in Heq. subst r. inversion H; subst. reflexivity.
  - destruct xs as [|ch rest]; [discriminate H |].
    destruct ch as [ | | | | r | ].
    + cbn [scanPL] in H. destruct (matchBit (plTopIs1 rCur) b0) eqn:Hm; [| discriminate H].
      destruct (scanPL fuel (prev66 rCur) rest) as [|out0] eqn:Hsc; [discriminate H |].
      inversion H; subst.
      rewrite (matchBit_eq Hm), (IH (prev66 rCur) (prev66_lt _ Hr) rest out0 Hsc),
              (repPL_comm rCur Hr), (matchBit_eq Hm). reflexivity.
    + cbn [scanPL] in H. destruct (matchBit (plTopIs1 rCur) b1) eqn:Hm; [| discriminate H].
      destruct (scanPL fuel (prev66 rCur) rest) as [|out0] eqn:Hsc; [discriminate H |].
      inversion H; subst.
      rewrite (matchBit_eq Hm), (IH (prev66 rCur) (prev66_lt _ Hr) rest out0 Hsc),
              (repPL_comm rCur Hr), (matchBit_eq Hm). reflexivity.
    + cbn [scanPL] in H. destruct (plTopIs1 rCur); cbn [matchBit] in H; discriminate H.
    + cbn [scanPL] in H. destruct (plTopIs1 rCur); cbn [matchBit] in H; discriminate H.
    + cbn [scanPL] in H. destruct (Nat.eqb r rCur) eqn:Heq; [| discriminate H].
      apply Nat.eqb_eq in Heq. subst r. inversion H; subst. reflexivity.
    + cbn [scanPL] in H. destruct (plTopIs1 rCur); cbn [matchBit] in H; discriminate H.
Qed.

Lemma scanPR_spec (fuel rCur : nat) (Hr : rCur < 66) (xs out : list Chunk)
  (H : scanPR fuel rCur xs = OptList_some out) (w : list bool) (c : nat) (lb : side) :
  decodeList w c xs lb = repPR rCur c (decodeList w c out lb).
Proof.
  revert rCur Hr xs out H.
  induction fuel as [|fuel IH]; intros rCur Hr xs out H.
  - destruct xs as [|[ | | | | | r ] rest]; try discriminate H.
    cbn [scanPR] in H. destruct (Nat.eqb r rCur) eqn:Heq; [| discriminate H].
    apply Nat.eqb_eq in Heq. subst r. inversion H; subst. reflexivity.
  - destruct xs as [|ch rest]; [discriminate H |].
    destruct ch as [ | | | | | r ].
    + cbn [scanPR] in H. destruct (matchBit (prTopIs1 rCur) b0) eqn:Hm; [| discriminate H].
      destruct (scanPR fuel (prev66 rCur) rest) as [|out0] eqn:Hsc; [discriminate H |].
      inversion H; subst.
      rewrite (matchBit_eq Hm), (IH (prev66 rCur) (prev66_lt _ Hr) rest out0 Hsc),
              (repPR_comm rCur Hr), (matchBit_eq Hm). reflexivity.
    + cbn [scanPR] in H. destruct (matchBit (prTopIs1 rCur) b1) eqn:Hm; [| discriminate H].
      destruct (scanPR fuel (prev66 rCur) rest) as [|out0] eqn:Hsc; [discriminate H |].
      inversion H; subst.
      rewrite (matchBit_eq Hm), (IH (prev66 rCur) (prev66_lt _ Hr) rest out0 Hsc),
              (repPR_comm rCur Hr), (matchBit_eq Hm). reflexivity.
    + cbn [scanPR] in H. destruct (prTopIs1 rCur); cbn [matchBit] in H; discriminate H.
    + cbn [scanPR] in H. destruct (prTopIs1 rCur); cbn [matchBit] in H; discriminate H.
    + cbn [scanPR] in H. destruct (prTopIs1 rCur); cbn [matchBit] in H; discriminate H.
    + cbn [scanPR] in H. destruct (Nat.eqb r rCur) eqn:Heq; [| discriminate H].
      apply Nat.eqb_eq in Heq. subst r. inversion H; subst. reflexivity.
Qed.

Lemma stripBits_eq_preBits (pat : list bool) (xs rest : list Chunk) :
  stripBits pat xs = OptList_some rest -> xs = preBits pat rest.
Proof.
  revert xs. induction pat as [|[|] pat' IH]; intros xs H.
  - cbn [stripBits] in H. inversion H; subst. reflexivity.
  - destruct xs as [|[] xs']; try discriminate H.
    cbn [stripBits matchBit] in H. cbn [preBits]. f_equal. exact (IH xs' H).
  - destruct xs as [|[] xs']; try discriminate H.
    cbn [stripBits matchBit] in H. cbn [preBits]. f_equal. exact (IH xs' H).
Qed.

Lemma preBits_spec (w : list bool) (c : nat) (pat : list bool) (tl : list Chunk) (lb : side) :
  decodeList w c (preBits pat tl) lb = decBits pat (decodeList w c tl lb).
Proof.
  induction pat as [|[|] pat' IH]; [reflexivity | | ];
    cbn [preBits decodeList decBits]; rewrite IH; reflexivity.
Qed.

Lemma stripBits_spec (w : list bool) (c : nat) (pat : list bool) (xs rest : list Chunk) (lb : side) :
  stripBits pat xs = OptList_some rest ->
  decodeList w c xs lb = decBits pat (decodeList w c rest lb).
Proof.
  intros H. rewrite (stripBits_eq_preBits pat xs rest H). apply preBits_spec.
Qed.

Lemma pL0_66_eq  : pL0_66  = pLList 0.  Proof. vm_compute. reflexivity. Qed.
Lemma pL14_66_eq : pL14_66 = pLList 14. Proof. vm_compute. reflexivity. Qed.
Lemma pL16_66_eq : pL16_66 = pLList 16. Proof. vm_compute. reflexivity. Qed.
Lemma pL9_66_eq  : pL9_66  = pLList 9.  Proof. vm_compute. reflexivity. Qed.
Lemma pL29_66_eq : pL29_66 = pLList 29. Proof. vm_compute. reflexivity. Qed.
Lemma pR64_66_eq : pR64_66 = pRList 64. Proof. vm_compute. reflexivity. Qed.
Lemma pR36_66_eq : pR36_66 = pRList 36. Proof. vm_compute. reflexivity. Qed.
Lemma pR14_66_eq : pR14_66 = pRList 14. Proof. vm_compute. reflexivity. Qed.
Lemma pR63_66_eq : pR63_66 = pRList 63. Proof. vm_compute. reflexivity. Qed.

Lemma stripP16_spec (w : list bool) (c : nat) (xs rest : list Chunk) (lb : side) :
  stripP16 xs = OptList_some rest -> decodeList w c xs lb = pLBits 16 (decodeList w c rest lb).
Proof. unfold stripP16, pLBits. rewrite <- pL16_66_eq. apply stripBits_spec. Qed.

Lemma stripP9_spec (w : list bool) (c : nat) (xs rest : list Chunk) (lb : side) :
  stripP9 xs = OptList_some rest -> decodeList w c xs lb = pLBits 9 (decodeList w c rest lb).
Proof. unfold stripP9, pLBits. rewrite <- pL9_66_eq. apply stripBits_spec. Qed.

Lemma stripP29_spec (w : list bool) (c : nat) (xs rest : list Chunk) (lb : side) :
  stripP29 xs = OptList_some rest -> decodeList w c xs lb = pLBits 29 (decodeList w c rest lb).
Proof. unfold stripP29, pLBits. rewrite <- pL29_66_eq. apply stripBits_spec. Qed.

Lemma stripR63_spec (w : list bool) (c : nat) (xs rest : list Chunk) (lb : side) :
  stripR63 xs = OptList_some rest -> decodeList w c xs lb = pRBits 63 (decodeList w c rest lb).
Proof. unfold stripR63, pRBits. rewrite <- pR63_66_eq. apply stripBits_spec. Qed.

Lemma preR64_spec (w : list bool) (c : nat) (tl : list Chunk) (lb : side) :
  decodeList w c (preR64 tl) lb = pRBits 64 (decodeList w c tl lb).
Proof. unfold preR64, pRBits. rewrite <- pR64_66_eq. apply preBits_spec. Qed.

Lemma preR36_spec (w : list bool) (c : nat) (tl : list Chunk) (lb : side) :
  decodeList w c (preR36 tl) lb = pRBits 36 (decodeList w c tl lb).
Proof. unfold preR36, pRBits. rewrite <- pR36_66_eq. apply preBits_spec. Qed.

Lemma preR14_spec (w : list bool) (c : nat) (tl : list Chunk) (lb : side) :
  decodeList w c (preR14 tl) lb = pRBits 14 (decodeList w c tl lb).
Proof. unfold preR14, pRBits. rewrite <- pR14_66_eq. apply preBits_spec. Qed.

Lemma preP14_spec (w : list bool) (c : nat) (tl : list Chunk) (lb : side) :
  decodeList w c (preP14 tl) lb = pLBits 14 (decodeList w c tl lb).
Proof. unfold preP14, pLBits. rewrite <- pL14_66_eq. apply preBits_spec. Qed.

Lemma prePL0_spec (w : list bool) (c : nat) (tl : list Chunk) (lb : side) :
  decodeList w c (prePL0 tl) lb = pLBits 0 (decodeList w c tl lb).
Proof. unfold prePL0, pLBits. rewrite <- pL0_66_eq. apply preBits_spec. Qed.

Lemma loopSweep_sound (strip : list Chunk -> OptList)
  (push : list Chunk -> list Chunk) (view : list Chunk -> list Chunk -> Q * tape)
  (move : forall xs rest acc, strip xs = OptList_some rest ->
      view xs acc -[ tm ]->* view rest (push acc))
  k xs acc l' r' (H : loopSweep strip push k xs acc = OptPair_some l' r') :
  view xs acc -[ tm ]->* view l' r'.
Proof.
  revert xs acc H; induction k as [|k IH]; intros xs acc H; cbn [loopSweep] in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (strip xs) as [|rest] eqn:E.
    + inversion H; subst. apply evstep_refl.
    + eapply evstep_trans; [eapply move; exact E | eapply IH; exact H].
Qed.

Lemma loopP16_sound (w : list bool) (c k : nat) (xs acc l' r' : list Chunk)
  (H : loopP16 k xs acc = OptPair_some l' r') :
  decode w c (RState_mk true xs (b0 :: b0 :: b0 :: acc)) -[ tm ]->*
    decode w c (RState_mk true l' (b0 :: b0 :: b0 :: r')).
Proof.
  eapply (loopSweep_sound stripP16 preR64 (fun xs acc => decode w c (RState_mk true xs (b0 :: b0 :: b0 :: acc)))); [|exact H].
  intros src rest dst E. cbn [decode decodeList].
  rewrite (stripP16_spec w c src rest blank E), preR64_spec. apply p66_L16.
Qed.

Lemma loopP9_sound (w : list bool) (c k : nat) (xs acc l' r' : list Chunk)
  (H : loopP9 k xs acc = OptPair_some l' r') :
  decode w c (RState_mk true xs (b0 :: b0 :: b0 :: acc)) -[ tm ]->*
    decode w c (RState_mk true l' (b0 :: b0 :: b0 :: r')).
Proof.
  eapply (loopSweep_sound stripP9 preR36 (fun xs acc => decode w c (RState_mk true xs (b0 :: b0 :: b0 :: acc)))); [|exact H].
  intros src rest dst E. cbn [decode decodeList].
  rewrite (stripP9_spec w c src rest blank E), preR36_spec. apply p66_L9.
Qed.

Lemma loopP29_sound (w : list bool) (c k : nat) (xs acc l' r' : list Chunk)
  (H : loopP29 k xs acc = OptPair_some l' r') :
  decode w c (RState_mk true xs (b0 :: b0 :: b0 :: b1 :: b1 :: acc)) -[ tm ]->*
    decode w c (RState_mk true l' (b0 :: b0 :: b0 :: b1 :: b1 :: r')).
Proof.
  eapply (loopSweep_sound stripP29 preR14 (fun xs acc => decode w c (RState_mk true xs (b0 :: b0 :: b0 :: b1 :: b1 :: acc)))); [|exact H].
  intros src rest dst E. cbn [decode decodeList].
  rewrite (stripP29_spec w c src rest blank E), preR14_spec. apply p66_L29.
Qed.

Lemma loopR63_sound (w : list bool) (c k : nat) (xs acc r' l' : list Chunk)
  (H : loopR63 k xs acc = OptPair_some r' l') :
  decode w c (RState_mk true (b1 :: b0 :: b0 :: b1 :: b0 :: acc) (b1 :: xs)) -[ tm ]->*
    decode w c (RState_mk true (b1 :: b0 :: b0 :: b1 :: b0 :: l') (b1 :: r')).
Proof.
  eapply (loopSweep_sound stripR63 preP14 (fun xs acc => decode w c (RState_mk true (b1 :: b0 :: b0 :: b1 :: b0 :: acc) (b1 :: xs)))); [|exact H].
  intros src rest dst E. cbn [decode decodeList].
  rewrite (stripR63_spec w c src rest blank E), preP14_spec. apply p66_R63.
Qed.

Local Ltac slb0_true IH H :=
  match type of H with
  | scanLeftB_p0 (S _) (b0 :: b1 :: b0 :: b0 :: ?rem) ?acc = _ =>
    destruct (IH rem (b0 :: b1 :: b1 :: b1 :: acc) H) as [u [HL HR]];
    exists (true :: u); split;
    [ cbn [encWL]; rewrite <- HL; reflexivity
    | cbn [flipW negb List.rev]; rewrite encWR0_append; cbn [encWR0]; rewrite HR; reflexivity ]
  end.

Lemma scanLeftB_p0_spec (w : list bool) (c k : nat) (xs accR restL outR : list Chunk)
  (H : scanLeftB_p0 k xs accR = OptPair_some restL outR) :
  exists u : list bool,
    decodeList w c xs blank = encWL u (f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> decodeList w c restL blank) /\
    decodeList w c outR blank = encWR0 (List.rev (flipW u)) (decodeList w c accR blank).
Proof.
  revert xs accR H.
  induction k as [|k IH]; intros xs accR H.
  - destruct xs as [|[] xs1]; try discriminate H.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct xs4 as [|[] xs5]; try discriminate H.
      destruct xs5 as [|[] xs6]; try discriminate H.
      destruct xs6 as [|[] rest0]; try discriminate H.
      cbn [scanLeftB_p0] in H. inversion H; subst. exists (@nil bool). split; reflexivity.
    + destruct xs1 as [|[] [|[] [|[] ?]]]; discriminate H.
  - destruct xs as [|[] xs1]; try discriminate H.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct xs4 as [|[] xs5]; try (slb0_true IH H).
      destruct xs5 as [|[] xs6]; try (slb0_true IH H).
      destruct xs6 as [|[] rest0]; try (slb0_true IH H).
      cbn [scanLeftB_p0] in H. inversion H; subst. exists (@nil bool). split; reflexivity.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct (IH xs4 (b0 :: b1 :: b0 :: b0 :: accR) H) as [u [HL HR]].
      exists (false :: u). split.
      * cbn [decodeList encWL]. rewrite HL. reflexivity.
      * cbn [flipW negb List.rev]. rewrite encWR0_append; cbn [encWR0]. rewrite HR. reflexivity.
Qed.

Local Ltac slb1_true IH H :=
  match type of H with
  | scanLeftB_p1 (S _) (b0 :: b1 :: b0 :: b0 :: ?rem) ?acc = _ =>
    destruct (IH rem (b1 :: b1 :: b1 :: b0 :: acc) H) as [u [HL HR]];
    exists (true :: u); split;
    [ cbn [encWL]; rewrite <- HL; reflexivity
    | cbn [flipW negb List.rev]; rewrite encWR_append; cbn [encWR]; rewrite HR; reflexivity ]
  end.

Lemma scanLeftB_p1_spec (w : list bool) (c k : nat) (xs accR restL outR : list Chunk)
  (H : scanLeftB_p1 k xs accR = OptPair_some restL outR) :
  exists u : list bool,
    decodeList w c xs blank = encWL u (f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> decodeList w c restL blank) /\
    decodeList w c outR blank = encWR (List.rev (flipW u)) (decodeList w c accR blank).
Proof.
  revert xs accR H.
  induction k as [|k IH]; intros xs accR H.
  - destruct xs as [|[] xs1]; try discriminate H.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct xs4 as [|[] xs5]; try discriminate H.
      destruct xs5 as [|[] xs6]; try discriminate H.
      destruct xs6 as [|[] rest0]; try discriminate H.
      cbn [scanLeftB_p1] in H. inversion H; subst. exists (@nil bool). split; reflexivity.
    + destruct xs1 as [|[] [|[] [|[] ?]]]; discriminate H.
  - destruct xs as [|[] xs1]; try discriminate H.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct xs4 as [|[] xs5]; try (slb1_true IH H).
      destruct xs5 as [|[] xs6]; try (slb1_true IH H).
      destruct xs6 as [|[] rest0]; try (slb1_true IH H).
      cbn [scanLeftB_p1] in H. inversion H; subst. exists (@nil bool). split; reflexivity.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct (IH xs4 (b1 :: b0 :: b0 :: b0 :: accR) H) as [u [HL HR]].
      exists (false :: u). split.
      * cbn [decodeList encWL]. rewrite HL. reflexivity.
      * cbn [flipW negb List.rev]. rewrite encWR_append; cbn [encWR]. rewrite HR. reflexivity.
Qed.

Local Ltac srq1_true IH H :=
  match type of H with
  | scanRightQ1 (S _) (b0 :: b0 :: b0 :: b1 :: ?rem) ?acc = _ =>
    destruct (IH rem (b0 :: b1 :: b0 :: b0 :: acc) H) as [u [HR HL]];
    exists (true :: u); split;
    [ cbn [encWR_q1]; rewrite <- HR; reflexivity
    | cbn [List.rev]; rewrite encWL_append; cbn [encWL]; rewrite HL; reflexivity ]
  end.

Lemma scanRightQ1_spec (w : list bool) (c k : nat) (xs accL outL restR : list Chunk)
  (H : scanRightQ1 k xs accL = OptPair_some outL restR) :
  exists u : list bool,
    decodeList w c xs blank = encWR_q1 u (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> decodeList w c restR blank) /\
    decodeList w c outL blank = encWL (List.rev u) (decodeList w c accL blank).
Proof.
  revert xs accL H.
  induction k as [|k IH]; intros xs accL H.
  - destruct xs as [|[] xs1]; try discriminate H.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct xs4 as [|[] xs5]; try discriminate H.
      destruct xs5 as [|[] xs6]; try discriminate H.
      destruct xs6 as [|[] xs7]; try discriminate H.
      destruct xs7 as [|[] rest0]; try discriminate H.
      cbn [scanRightQ1] in H. inversion H; subst. exists (@nil bool). split; reflexivity.
    + destruct xs1 as [|[] [|[] [|[] ?]]]; discriminate H.
  - destruct xs as [|[] xs1]; try discriminate H.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct xs4 as [|[] xs5]; try (srq1_true IH H).
      destruct xs5 as [|[] xs6]; try (srq1_true IH H).
      destruct xs6 as [|[] xs7]; try (srq1_true IH H).
      destruct xs7 as [|[] rest0]; try (srq1_true IH H).
      cbn [scanRightQ1] in H. inversion H; subst. exists (@nil bool). split; reflexivity.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      destruct (IH xs4 (b1 :: b0 :: b0 :: b0 :: accL) H) as [u [HR HL]].
      exists (false :: u). split.
      * cbn [decodeList encWR_q1]. rewrite HR. reflexivity.
      * cbn [List.rev]. rewrite encWL_append; cbn [encWL]. rewrite HL. reflexivity.
Qed.

Local Ltac csla_base H := cbn [concSafeLeftA] in H; inversion H; subst; apply evstep_refl.

Lemma concSafeLeftA_sound (w : list bool) (c : nat) (l accR l' r' : list Chunk)
  (H : concSafeLeftA l accR = OptPair_some l' r') :
  decode w c (RState_mk true l (b0 :: b0 :: b0 :: accR)) -[ tm ]->*
    decode w c (RState_mk true l' (b0 :: b0 :: b0 :: r')).
Proof.
  revert accR H.
  induction l as [l IH] using list_strong_ind.
  intros accR H.
  destruct l as [|[] l1]; try (csla_base H).
  - destruct l1 as [|[] l2]; try (csla_base H).
    destruct l2 as [|[] l3]; try (csla_base H).
    destruct l3 as [|[] restL]; try (csla_base H).
    eapply evstep_trans; [apply lpa_1 | apply (IH restL ltac:(cbn; lia) (b1 :: b0 :: b0 :: b0 :: accR) H)].
  - destruct l1 as [|[] l2]; try (csla_base H).
    destruct l2 as [|[] l3]; try (csla_base H).
    destruct l3 as [|[] restL]; try (csla_base H).
    eapply evstep_trans; [apply lpa_0 | apply (IH restL ltac:(cbn; lia) (b1 :: b1 :: b1 :: b0 :: accR) H)].
Qed.

Local Ltac csrg_base H := cbn [concSafeRightGo] in H; left; exact H.
Local Ltac csrg_true IH H :=
  match type of H with
  | concSafeRightGo _ (b0 :: b0 :: b0 :: b1 :: ?rem) ?acc ?bst = _ =>
    destruct (IH rem ltac:(cbn; lia) true (b0 :: b1 :: b0 :: b0 :: acc) bst H) as [Hb | [u [HR HL]]];
    [ left; exact Hb
    | right; exists (true :: u); split;
      [ cbn [encWR_q1]; rewrite <- HR; reflexivity
      | cbn [List.rev]; rewrite encWL_append; cbn [encWL]; rewrite HL; reflexivity ] ]
  end.

Lemma concSafeRightGo_spec (w : list bool) (c : nat)
  (had1 : bool) (xs accL : list Chunk) (best : OptPair) (outL restR : list Chunk)
  (H : concSafeRightGo had1 xs accL best = OptPair_some outL restR) :
  best = OptPair_some outL restR \/
    exists u : list bool,
      decodeList w c xs blank = encWR_q1 u (f0 >> f0 >> f0 >> f1 >> f0 >> f0 >> f0 >> f1 >> decodeList w c restR blank) /\
      decodeList w c outL blank = encWL (List.rev u) (decodeList w c accL blank).
Proof.
  revert had1 accL best H.
  induction xs as [xs IH] using list_strong_ind.
  intros had1 accL best H.
  destruct xs as [|[] xs1]; try (csrg_base H).
  - destruct xs1 as [|[] xs2]; try (csrg_base H).
    destruct xs2 as [|[] xs3]; try (csrg_base H).
    destruct xs3 as [|[] xs4]; try (csrg_base H).
    destruct xs4 as [|[] xs5]; try (csrg_true IH H).
    destruct xs5 as [|[] xs6]; try (csrg_true IH H).
    destruct xs6 as [|[] xs7]; try (csrg_true IH H).
    destruct xs7 as [|[] restR0]; try (csrg_true IH H).
    destruct had1.
    + destruct (IH (b0 :: b0 :: b0 :: b1 :: restR0) ltac:(cbn; lia) true
                  (b0 :: b1 :: b0 :: b0 :: accL) (OptPair_some accL restR0) H) as [Hck | [u [HR HL]]].
      * inversion Hck; subst. right. exists (@nil bool). split; reflexivity.
      * right. exists (true :: u). split.
        -- cbn [encWR_q1]; rewrite <- HR; reflexivity.
        -- cbn [List.rev]. rewrite encWL_append; cbn [encWL]. rewrite HL. reflexivity.
    + destruct (IH (b0 :: b0 :: b0 :: b1 :: restR0) ltac:(cbn; lia) true
                  (b0 :: b1 :: b0 :: b0 :: accL) best H) as [Hb | [u [HR HL]]].
      * left; exact Hb.
      * right. exists (true :: u). split.
        -- cbn [encWR_q1]; rewrite <- HR; reflexivity.
        -- cbn [List.rev]. rewrite encWL_append; cbn [encWL]. rewrite HL. reflexivity.
  - destruct xs1 as [|[] xs2]; try (csrg_base H).
    destruct xs2 as [|[] xs3]; try (csrg_base H).
    destruct xs3 as [|[] restR0]; try (csrg_base H).
    destruct (IH restR0 ltac:(cbn; lia) true (b1 :: b0 :: b0 :: b0 :: accL) best H) as [Hb | [u [HR HL]]].
    + left; exact Hb.
    + right. exists (false :: u). split.
      * cbn [decodeList encWR_q1]. rewrite HR. reflexivity.
      * cbn [List.rev]. rewrite encWL_append; cbn [encWL]. rewrite HL. reflexivity.
Qed.

Local Ltac cslbg_base H := cbn [concSafeLeftBGo] in H; left; exact H.
Local Ltac cslbg_true IH H :=
  match type of H with
  | concSafeLeftBGo _ (b0 :: b0 :: b1 :: b0 :: ?rem) ?acc ?bst = _ =>
    destruct (IH rem ltac:(cbn; lia) true (b0 :: b1 :: b1 :: b1 :: acc) bst H) as [Hb | [u [HL HR]]];
    [ left; exact Hb
    | right; exists (true :: u); split;
      [ cbn [encWL_b0]; rewrite <- HL; reflexivity
      | cbn [flipW negb List.rev]; rewrite encWR0_append; cbn [encWR0]; rewrite HR; reflexivity ] ]
  end.

Lemma concSafeLeftBGo_spec (w : list bool) (c : nat)
  (had1 : bool) (xs accR : list Chunk) (best : OptPair) (restL outR : list Chunk)
  (H : concSafeLeftBGo had1 xs accR best = OptPair_some restL outR) :
  best = OptPair_some restL outR \/
    exists u : list bool,
      decodeList w c xs blank = encWL_b0 u (f0 >> f0 >> f1 >> f0 >> f0 >> f1 >> f0 >> f0 >> decodeList w c restL blank) /\
      decodeList w c outR blank = encWR0 (List.rev (flipW u)) (decodeList w c accR blank).
Proof.
  revert had1 accR best H.
  induction xs as [xs IH] using list_strong_ind.
  intros had1 accR best H.
  destruct xs as [|[] xs1]; try (cslbg_base H).
  destruct xs1 as [|[] xs2]; try (cslbg_base H).
  - destruct xs2 as [|[] xs3]; try (cslbg_base H).
    destruct xs3 as [|[] xs4]; try (cslbg_base H).
    destruct xs4 as [|[] xs5]; try (cslbg_true IH H).
    destruct xs5 as [|[] xs6]; try (cslbg_true IH H).
    destruct xs6 as [|[] xs7]; try (cslbg_true IH H).
    destruct xs7 as [|[] restL0]; try (cslbg_true IH H).
    destruct had1.
    + destruct (IH (b0 :: b1 :: b0 :: b0 :: restL0) ltac:(cbn; lia) true
                  (b0 :: b1 :: b1 :: b1 :: accR) (OptPair_some restL0 accR) H) as [Hck | [u [HL HR]]].
      * inversion Hck; subst. right. exists (@nil bool). split; reflexivity.
      * right. exists (true :: u). split.
        -- cbn [encWL_b0]; rewrite <- HL; reflexivity.
        -- cbn [flipW negb List.rev]. rewrite encWR0_append; cbn [encWR0]. rewrite HR. reflexivity.
    + destruct (IH (b0 :: b1 :: b0 :: b0 :: restL0) ltac:(cbn; lia) true
                  (b0 :: b1 :: b1 :: b1 :: accR) best H) as [Hb | [u [HL HR]]].
      * left; exact Hb.
      * right. exists (true :: u). split.
        -- cbn [encWL_b0]; rewrite <- HL; reflexivity.
        -- cbn [flipW negb List.rev]. rewrite encWR0_append; cbn [encWR0]. rewrite HR. reflexivity.
  - destruct xs2 as [|[] xs3]; try (cslbg_base H).
    destruct xs3 as [|[] restL0]; try (cslbg_base H).
    destruct (IH restL0 ltac:(cbn; lia) true (b0 :: b1 :: b0 :: b0 :: accR) best H) as [Hb | [u [HL HR]]].
    + left; exact Hb.
    + right. exists (false :: u). split.
      * cbn [decodeList encWL_b0]. rewrite HL. reflexivity.
      * cbn [flipW negb List.rev]. rewrite encWR0_append; cbn [encWR0]. rewrite HR. reflexivity.
Qed.

Lemma scanSuperBounce_spec (w : list bool) (c : nat) (xs out : list Chunk)
  (H : scanSuperBounce xs = OptList_some out) :
  exists (k : nat) (tail : side),
    decodeList w c xs blank = repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f1 >> f0 >> tail) /\
    decodeList w c out blank = repBits [false; true; false; false] k (f0 >> f1 >> f0 >> f0 >> f0 >> f0 >> f1 >> tail).
Proof.
  revert out H.
  induction xs as [xs IH] using list_strong_ind.
  intros out H.
  destruct xs as [|[] xs1]; try discriminate H.
  destruct xs1 as [|[] xs2]; try discriminate H.
  destruct xs2 as [|[] xs3]; try discriminate H.
  destruct xs3 as [|[] xs4]; try discriminate H.
  - cbn [scanSuperBounce] in H.
    destruct (scanSuperBounce xs4) as [|out0] eqn:Hsc; [discriminate H |].
    inversion H; subst.
    destruct (IH xs4 ltac:(cbn; lia) out0 Hsc) as [k [tail [H1 H2]]].
    exists (S k), tail. split; cbn [decodeList repBits decBits]; [rewrite H1 | rewrite H2]; reflexivity.
  - destruct xs4 as [|[] restL]; try discriminate H.
    cbn [scanSuperBounce] in H. inversion H; subst.
    exists 0, (decodeList w c restL blank). split; reflexivity.
Qed.

Lemma matchBit_literal b x :
  matchBit b x = true -> x = literalChunk b.
Proof. destruct b, x; cbn; congruence. Qed.

Lemma bridgeSweep_sound w c (view : list Chunk -> list Chunk -> RState)
    a b d e out
    (Hop : forall xs acc,
      decode w c (view (literalChunk a :: literalChunk b ::
                        literalChunk d :: literalChunk e :: xs) acc)
      -[ tm ]->* decode w c (view xs (out ++ acc))) :
  forall xs acc, decode w c (view xs acc)
    -[ tm ]->* decode w c (bridgeSweep view a b d e out xs acc).
Proof.
  induction xs as [xs IH] using list_strong_ind; intros acc.
  destruct xs as [|x [|y [|z [|t rest]]]]; try apply evstep_refl.
  cbn [bridgeSweep].
  destruct (_ && _ && _ && _) eqn:H; [|apply evstep_refl].
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[[Hx Hy] Hz] Ht].
  apply matchBit_literal in Hx, Hy, Hz, Ht; subst.
  eapply evstep_trans; [apply Hop | apply IH; cbn; lia].
Qed.

Ltac proveBridge step :=
  lazymatch goal with
  | |- _ -[ _ ]->* decode ?w ?c (bridgeSweep ?v ?a ?b ?d ?e ?out ?xs ?acc) =>
      refine (bridgeSweep_sound w c v a b d e out _ xs acc);
      intros; apply step
  end.

Lemma br1Loop_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (br1Loop l r).
Proof. unfold br1Loop; proveBridge br1_step. Qed.

Lemma br2Loop_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (br2Loop l r).
Proof. unfold br2Loop; proveBridge br2_step. Qed.

Lemma br3Loop_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk false l r) -[ tm ]->* decode w c (br3Loop l r).
Proof. unfold br3Loop; proveBridge br3_step. Qed.

Lemma br4Loop_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b1 :: b0 :: b0 :: b0 :: l) (b1 :: r)) -[ tm ]->* decode w c (br4Loop l r).
Proof. unfold br4Loop; proveBridge br4_step. Qed.

Lemma br5Loop_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk false l (b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: b1 :: r)) -[ tm ]->* decode w c (br5Loop l r).
Proof. unfold br5Loop; proveBridge br5_step. Qed.

Lemma br6Loop_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b1 :: b0 :: b0 :: b0 :: l) (b1 :: b0 :: b1 :: b0 :: r)) -[ tm ]->* decode w c (br6Loop l r).
Proof. unfold br6Loop; proveBridge br6_step. Qed.

Lemma br7Loop_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b0 :: b1 :: b0 :: b1 :: l) (b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: r)) -[ tm ]->* decode w c (br7Loop l r).
Proof. unfold br7Loop; proveBridge br7_step. Qed.

Lemma br1_enter (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b1 :: b1 :: b0 :: b0 :: l) r) -[ tm ]->*
    decode w c (br1Loop l (b0 :: b0 :: b0 :: b1 :: r)).
Proof. eapply evstep_trans; [apply br1_step | exact (br1Loop_sound w c l (b0 :: b0 :: b0 :: b1 :: r))]. Qed.

Lemma br2_enter (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b0 :: b1 :: b0 :: b0 :: l) r) -[ tm ]->*
    decode w c (br2Loop l (b0 :: b0 :: b0 :: b1 :: r)).
Proof. eapply evstep_trans; [apply br2_step | exact (br2Loop_sound w c l (b0 :: b0 :: b0 :: b1 :: r))]. Qed.

Lemma br3_enter (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk false l (b0 :: b0 :: b1 :: b0 :: r)) -[ tm ]->*
    decode w c (br3Loop (b1 :: b0 :: b0 :: b1 :: l) r).
Proof. eapply evstep_trans; [apply br3_step | exact (br3Loop_sound w c (b1 :: b0 :: b0 :: b1 :: l) r)]. Qed.

Lemma br4_enter (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b1 :: b0 :: b0 :: b0 :: l) (b1 :: b1 :: b1 :: b0 :: b1 :: r)) -[ tm ]->*
    decode w c (br4Loop (b0 :: b1 :: b0 :: b0 :: l) r).
Proof. eapply evstep_trans; [apply br4_step | exact (br4Loop_sound w c (b0 :: b1 :: b0 :: b0 :: l) r)]. Qed.

Lemma br5_enter (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk false l (b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: r)) -[ tm ]->*
    decode w c (br5Loop (b0 :: b1 :: b0 :: b0 :: l) r).
Proof. eapply evstep_trans; [apply br5_step | exact (br5Loop_sound w c (b0 :: b1 :: b0 :: b0 :: l) r)]. Qed.

Lemma br6_enter (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b1 :: b0 :: b0 :: b0 :: l) (b1 :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b0 :: r)) -[ tm ]->*
    decode w c (br6Loop (b0 :: b0 :: b1 :: b0 :: l) r).
Proof. eapply evstep_trans; [apply br6_step | exact (br6Loop_sound w c (b0 :: b0 :: b1 :: b0 :: l) r)]. Qed.

Lemma br7_enter (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true (b0 :: b1 :: b0 :: b1 :: b1 :: b0 :: b0 :: b1 :: l)
                             (b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: r)) -[ tm ]->*
    decode w c (br7Loop l (b1 :: b1 :: b0 :: b1 :: r)).
Proof. eapply evstep_trans; [apply br7_step | exact (br7Loop_sound w c l (b1 :: b1 :: b0 :: b1 :: r))]. Qed.

Lemma peelPLStep_eq (w : list bool) (c r : nat) (b : Chunk) (rest out : list Chunk) (lb : side)
  (H : peelPLStep r b rest = OptList_some out) :
  decodeList w c (pL r :: b :: rest) lb = decodeList w c out lb.
Proof.
  unfold peelPLStep in H.
  destruct (Nat.leb r 65) eqn:Hle; [| discriminate H].
  apply Nat.leb_le in Hle. assert (Hr : r < 66) by lia.
  pose proof (repPL_comm r Hr c (decodeList w c rest lb)) as Hc.
  destruct (plTopIs1 r), b; cbn [matchBit] in H; try discriminate H;
    inversion H; subst; cbn [decodeList];
    cbn [finOfBool] in Hc; symmetry; exact Hc.
Qed.

Lemma peelPRStep_eq (w : list bool) (c r : nat) (b : Chunk) (rest out : list Chunk) (lb : side)
  (H : peelPRStep r b rest = OptList_some out) :
  decodeList w c (pR r :: b :: rest) lb = decodeList w c out lb.
Proof.
  unfold peelPRStep in H.
  destruct (Nat.leb r 65) eqn:Hle; [| discriminate H].
  apply Nat.leb_le in Hle. assert (Hr : r < 66) by lia.
  pose proof (repPR_comm r Hr c (decodeList w c rest lb)) as Hc.
  destruct (prTopIs1 r), b; cbn [matchBit] in H; try discriminate H;
    inversion H; subst; cbn [decodeList];
    cbn [finOfBool] in Hc; symmetry; exact Hc.
Qed.

Local Ltac ppl_rec k rest IH H :=
  destruct k as [|k']; [cbn [peelPL] in H; discriminate H |
    cbn [peelPL] in H; destruct (peelPL k' rest) as [|out0] eqn:Hp; [discriminate H |
      inversion H; subst; cbn [decodeList]; rewrite (IH k' out0 Hp); reflexivity ] ].

Lemma peelPL_eq (w : list bool) (c k : nat) (xs out : list Chunk) (lb : side)
  (H : peelPL k xs = OptList_some out) :
  decodeList w c xs lb = decodeList w c out lb.
Proof.
  revert k out H.
  induction xs as [|ch rest IH]; intros k out H; [destruct k; discriminate H |].
  destruct ch as [ | | f | f | r | r ];
    try (ppl_rec k rest IH H).
  destruct k; cbn [peelPL] in H; destruct rest as [|b rest']; try discriminate H;
    exact (peelPLStep_eq w c r b rest' out lb H).
Qed.

Local Ltac ppr_rec k rest IH H :=
  destruct k as [|k']; [cbn [peelPR] in H; discriminate H |
    cbn [peelPR] in H; destruct (peelPR k' rest) as [|out0] eqn:Hp; [discriminate H |
      inversion H; subst; cbn [decodeList]; rewrite (IH k' out0 Hp); reflexivity ] ].

Lemma peelPR_eq (w : list bool) (c k : nat) (xs out : list Chunk) (lb : side)
  (H : peelPR k xs = OptList_some out) :
  decodeList w c xs lb = decodeList w c out lb.
Proof.
  revert k out H.
  induction xs as [|ch rest IH]; intros k out H; [destruct k; discriminate H |].
  destruct ch as [ | | f | f | r | r ];
    try (ppr_rec k rest IH H).
  destruct k; cbn [peelPR] in H; destruct rest as [|b rest']; try discriminate H;
    exact (peelPRStep_eq w c r b rest' out lb H).
Qed.

Lemma pop1B_fallback_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk false l r) -[ tm ]->* decode w c (pop1B_fallback l r).
Proof.
  unfold pop1B_fallback. destruct (peelPR 4 r) as [|r'] eqn:Hp; [apply evstep_refl |].
  cbn [decode]. rewrite (peelPR_eq w c 4 r r' blank Hp). apply evstep_refl.
Qed.

Lemma pop1B_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk false l r) -[ tm ]->* decode w c (pop1B l r).
Proof.
  revert l. induction r as [r IH] using list_strong_ind; intros l.
  destruct r as [|c1 r1].
  - cbn [pop1B decode decodeList].
    pose proof (progress_evstep _ _ _ (stepB_000 (decodeList w c l blank) blank)) as H.
    repeat rewrite z00 in H. repeat rewrite z00. exact H.
  - destruct c1; try exact (pop1B_fallback_sound w c l _).
    + destruct r1 as [|c2 r2].
      * cbn [pop1B decode decodeList].
        pose proof (progress_evstep _ _ _ (stepB_000 (decodeList w c l blank) blank)) as H.
        repeat rewrite z00 in H. repeat rewrite z00. exact H.
      * destruct c2; try exact (pop1B_fallback_sound w c l _).
        -- destruct r2 as [|c3 r3].
           ++ cbn [pop1B decode decodeList].
              pose proof (progress_evstep _ _ _ (stepB_000 (decodeList w c l blank) blank)) as H.
              repeat rewrite z00 in H. repeat rewrite z00. exact H.
           ++ destruct c3; try exact (pop1B_fallback_sound w c l _).
              ** apply progress_evstep, stepB_000.
              ** destruct r3 as [|c4 r4].
                 --- cbn [pop1B decode decodeList].
                     pose proof (progress_evstep _ _ _ (stepB_0010 (decodeList w c l blank) blank)) as H.
                     repeat rewrite z00 in H. repeat rewrite z00. exact H.
                 --- destruct c4; try exact (pop1B_fallback_sound w c l _).
                     +++ apply progress_evstep, stepB_0010.
                     +++ apply progress_evstep, stepB_0011.
        -- apply progress_evstep, stepB_01.
    + cbn [pop1B].
      eapply evstep_trans; [apply progress_evstep, stepB_1 | exact (IH r1 ltac:(cbn; lia) (b0 :: l))].
Qed.

Lemma pop10E_fallback_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (pop10E_fallback l r).
Proof.
  unfold pop10E_fallback.
  destruct (peelPL 4 l) as [|l'] eqn:HpL.
  - destruct (peelPR 4 r) as [|r'] eqn:HpR; [apply evstep_refl |].
    cbn [decode]. rewrite (peelPR_eq w c 4 r r' blank HpR). apply evstep_refl.
  - cbn [decode]. rewrite (peelPL_eq w c 4 l l' blank HpL). apply evstep_refl.
Qed.

Lemma pop10E_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (pop10E l r).
Proof.
  revert r. induction l as [l IH] using list_strong_ind; intros r.
  destruct l as [|c1 l1].
  - destruct r as [|d1 r1].
    + cbn [pop10E decode decodeList].
      pose proof (progress_evstep _ _ _ (stepE_00_0 blank blank)) as H. repeat rewrite z00 in H. repeat rewrite z00. exact H.
    + destruct d1; try exact (pop10E_fallback_sound w c _ _).
      * cbn [pop10E decode decodeList].
        pose proof (progress_evstep _ _ _ (stepE_00_0 blank (decodeList w c r1 blank))) as H.
        repeat rewrite z00 in H. repeat rewrite z00. exact H.
      * cbn [pop10E decode decodeList].
        pose proof (progress_evstep _ _ _ (stepE_00_1 blank (decodeList w c r1 blank))) as H.
        repeat rewrite z00 in H. repeat rewrite z00. exact H.
  - destruct c1; try exact (pop10E_fallback_sound w c _ _).
    + destruct l1 as [|c2 l2].
      * destruct r as [|d1 r1].
        -- cbn [pop10E decode decodeList].
           pose proof (progress_evstep _ _ _ (stepE_00_0 blank blank)) as H. repeat rewrite z00 in H. repeat rewrite z00. exact H.
        -- destruct d1; try exact (pop10E_fallback_sound w c _ _).
           ++ cbn [pop10E decode decodeList].
              pose proof (progress_evstep _ _ _ (stepE_00_0 blank (decodeList w c r1 blank))) as H.
              repeat rewrite z00 in H. repeat rewrite z00. exact H.
           ++ cbn [pop10E decode decodeList].
              pose proof (progress_evstep _ _ _ (stepE_00_1 blank (decodeList w c r1 blank))) as H.
              repeat rewrite z00 in H. repeat rewrite z00. exact H.
      * destruct c2; try exact (pop10E_fallback_sound w c _ _).
        -- destruct r as [|d1 r1].
           ++ cbn [pop10E decode decodeList].
              pose proof (progress_evstep _ _ _ (stepE_00_0 (decodeList w c l2 blank) blank)) as H.
              repeat rewrite z00 in H. repeat rewrite z00. exact H.
           ++ destruct d1; try exact (pop10E_fallback_sound w c _ _).
              ** apply progress_evstep, stepE_00_0.
              ** apply progress_evstep, stepE_00_1.
        -- cbn [pop10E].
           eapply evstep_trans; [apply progress_evstep, stepE_01 | exact (IH l2 ltac:(cbn; lia) (b1 :: b1 :: r))].
    + destruct l1 as [|c2 l2].
      * cbn [pop10E decode decodeList].
        pose proof (progress_evstep _ _ _ (stepE_10 blank (decodeList w c r blank))) as H.
        repeat rewrite z00 in H. repeat rewrite z00. exact H.
      * destruct c2; try exact (pop10E_fallback_sound w c _ _).
        -- apply progress_evstep, stepE_10.
        -- destruct l2 as [|c3 l3].
           ++ cbn [pop10E decode decodeList].
              pose proof (progress_evstep _ _ _ (stepE_1100 blank (decodeList w c r blank))) as H.
              repeat rewrite z00 in H. repeat rewrite z00. exact H.
           ++ destruct c3; try exact (pop10E_fallback_sound w c _ _).
              ** destruct l3 as [|c4 l4].
                 --- cbn [pop10E decode decodeList].
                     pose proof (progress_evstep _ _ _ (stepE_1100 blank (decodeList w c r blank))) as H.
                     repeat rewrite z00 in H. repeat rewrite z00. exact H.
                 --- destruct c4; try exact (pop10E_fallback_sound w c _ _).
                     +++ apply progress_evstep, stepE_1100.
                     +++ apply progress_evstep, stepE_1101.
Qed.

Lemma br5_or_pop1B (w : list bool) (c : nat) (l r restR1 : list Chunk)
  (Hr : r = b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: b1 :: restR1) :
  decode w c (RState_mk false l r) -[ tm ]->*
    decode w c (match restR1 with
                | b0 :: b0 :: b0 :: b1 :: restR5 => br5Loop (b0 :: b1 :: b0 :: b0 :: l) restR5
                | _ => pop1B l r
                end).
Proof.
  destruct restR1 as [|[] r2]; try exact (pop1B_sound w c l r).
  destruct r2 as [|[] r3]; try exact (pop1B_sound w c l r).
  destruct r3 as [|[] r4]; try exact (pop1B_sound w c l r).
  destruct r4 as [|[] restR5]; try exact (pop1B_sound w c l r).
  subst r. exact (br5_enter w c l restR5).
Qed.

Lemma stepB_1111010_sound (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: restR) :
  decode w c (RState_mk false l r) -[ tm ]->* decode w c (stepB_1111010 l r restR).
Proof.
  destruct restR as [|ch1 restR1]; [exact (pop1B_sound w c l r) |].
  destruct ch1 as [ | | | f | | ]; try exact (pop1B_sound w c l r).
  - assert (Hr1 : r = b1 :: b1 :: b1 :: b1 :: b0 :: b1 :: b0 :: b1 :: restR1) by (subst r; reflexivity).
    cbn [stepB_1111010].
    destruct l as [|[] l1]; try exact (br5_or_pop1B w c _ r restR1 Hr1).
    destruct l1 as [|[] l2]; try exact (br5_or_pop1B w c _ r restR1 Hr1).
    destruct l2 as [|[] l3]; try exact (br5_or_pop1B w c _ r restR1 Hr1).
    destruct l3 as [|[] restL]; try exact (br5_or_pop1B w c _ r restR1 Hr1).
    destruct (concSafeRightGo false restR1 (b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: restL) OptPair_none)
      as [|outL restR'] eqn:Hgo.
    + exact (br5_or_pop1B w c _ r restR1 Hr1).
    + destruct (concSafeRightGo_spec w c false restR1 _ OptPair_none outL restR' Hgo)
        as [Hnone | [u [HR HL]]]; [discriminate Hnone |].
      subst r. cbn [decode decodeList] in *. rewrite HR, HL; cbn [decodeList].
      exact (rightPassQ1_reaches u (decodeList w c restL blank) (decodeList w c restR' blank)).
  - destruct restR1 as [|[] restR2]; try exact (pop1B_sound w c l r).
    cbn [stepB_1111010].
    destruct l as [|[] l1]; try exact (pop1B_sound w c _ r).
    destruct l1 as [|[] l2]; try exact (pop1B_sound w c _ r).
    destruct l2 as [|[] l3]; try exact (pop1B_sound w c _ r).
    destruct l3 as [|[] restL]; try exact (pop1B_sound w c _ r).
    destruct (scanRightQ1 64 restR2 (wL f :: b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b0 :: b0 :: restL))
      as [|outL restR'] eqn:Hsc; [exact (pop1B_sound w c _ r) |].
    destruct (scanRightQ1_spec w c 64 restR2 _ outL restR' Hsc) as [u [HR HL]].
    subst r. cbn [decode decodeList] in *.
    rewrite shift_encWR_1, HR, HL; cbn [decodeList].
    pose proof (rightPassQ1_reaches (List.rev (if f then flipW w else w) ++ u)
                  (decodeList w c restL blank) (decodeList w c restR' blank)) as Hmain.
    rewrite encWR_q1_append, List.rev_app_distr, List.rev_involutive, encWL_append in Hmain.
    exact Hmain.
Qed.

Lemma stepFalse_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk false l r) -[ tm ]->* decode w c (stepFalse l r).
Proof.
  destruct r as [|[] r1]; try exact (pop1B_sound w c l _).
  - destruct r1 as [|[] r2]; try exact (pop1B_sound w c l _).
    destruct r2 as [|[] r3]; try exact (pop1B_sound w c l _).
    destruct r3 as [|[] restR]; try exact (pop1B_sound w c l _).
    cbn [stepFalse]. exact (br3_enter w c l restR).
  - destruct r1 as [|[] r2]; try exact (pop1B_sound w c l _).
    destruct r2 as [|[] r3]; try exact (pop1B_sound w c l _).
    destruct r3 as [|[] r4]; try exact (pop1B_sound w c l _).
    destruct r4 as [|[] r5]; try exact (pop1B_sound w c l _).
    destruct r5 as [|[] r6]; try exact (pop1B_sound w c l _).
    destruct r6 as [|[] restR]; try exact (pop1B_sound w c l _).
    cbn [stepFalse]. exact (stepB_1111010_sound w c l _ restR eq_refl).
Qed.

Lemma stepE_000_rest_sound (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b0 :: b0 :: b0 :: restR) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (stepE_000_rest l r restR).
Proof.
  destruct l as [|[] l1]; try exact (pop10E_sound w c _ r).
  - destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ r).
    + destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
      destruct l3 as [|[] l4]; try exact (pop10E_sound w c _ r).
      cbn [stepE_000_rest].
      destruct restR as [|[] rr1]; try exact (pop10E_sound w c _ r).
      destruct rr1 as [|[] rr2]; try exact (pop10E_sound w c _ r).
      destruct rr2 as [|[] rr3]; try exact (pop10E_sound w c _ r).
      destruct rr3 as [|[] rr4]; try exact (pop10E_sound w c _ r).
      destruct rr4 as [|[] restR8]; try exact (pop10E_sound w c _ r).
      destruct (concSafeLeftBGo false (b0 :: b0 :: b1 :: b0 :: l4)
                  (b0 :: b1 :: b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: restR8) OptPair_none)
        as [|l' outR] eqn:Hgo; [exact (pop10E_sound w c _ r) |].
      destruct (concSafeLeftBGo_spec w c false _ _ OptPair_none l' outR Hgo)
        as [Hnone | [u [HL HR]]]; [discriminate Hnone |].
      subst r. cbn [decode]. rewrite HL; cbn [decodeList]. rewrite HR; cbn [decodeList].
      exact (leftPassB_p0_reaches u (decodeList w c l' blank) (decodeList w c restR8 blank)).
    + destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
      destruct l3 as [|[] l4]; try exact (pop10E_sound w c _ r).
      * cbn [stepE_000_rest].
        destruct (concSafeLeftA (b0 :: b1 :: b0 :: b0 :: l4) restR) as [|l' r'] eqn:Hgo;
          [exact (pop10E_sound w c _ r) | subst r; exact (concSafeLeftA_sound w c _ restR l' r' Hgo)].
      * destruct l4 as [|[] l5]; try exact (pop10E_sound w c _ r).
        destruct l5 as [|[] l6]; try exact (pop10E_sound w c _ r).
        destruct l6 as [|[] l7]; try exact (pop10E_sound w c _ r).
        destruct l7 as [|[] restL]; try exact (pop10E_sound w c _ r).
        cbn [stepE_000_rest].
        destruct restR as [|[] rr1]; try exact (pop10E_sound w c _ r).
        destruct rr1 as [|[] rr2]; try exact (pop10E_sound w c _ r).
        destruct rr2 as [|[] rr3]; try exact (pop10E_sound w c _ r).
        destruct rr3 as [|[] rr4]; try exact (pop10E_sound w c _ r).
        destruct rr4 as [|[] restR8]; try exact (pop10E_sound w c _ r).
        subst r. exact (br7_enter w c restL restR8).
  - destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ r).
    + destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
      destruct l3 as [|[] l4]; try exact (pop10E_sound w c _ r).
      cbn [stepE_000_rest].
      destruct (concSafeLeftA (b1 :: b0 :: b0 :: b0 :: l4) restR) as [|l' r'] eqn:Hgo;
        [exact (pop10E_sound w c _ r) | subst r; exact (concSafeLeftA_sound w c _ restR l' r' Hgo)].
    + destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
      destruct l3 as [|[] restL]; try exact (pop10E_sound w c _ r).
      cbn [stepE_000_rest]. exact (br1_enter w c restL r).
Qed.

Lemma stepE_000_p66_b0_fall (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b0 :: b0 :: b0 :: restR) :
  decode w c (RState_mk true l r) -[ tm ]->*
    decode w c (match scanPL 66 16 l with
                | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 64 :: restR)
                | OptList_none => stepE_000_rest l r restR
                end).
Proof.
  destruct (scanPL 66 16 l) as [|l'] eqn:Hsc; [exact (stepE_000_rest_sound w c l r restR Hr) |].
  subst r. cbn [decode decodeList].
  rewrite (scanPL_spec 66 16 ltac:(lia) l l' Hsc w c blank).
  apply p66_L16_rep.
Qed.

Lemma stepE_000_p66_b1_fall (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b0 :: b0 :: b0 :: restR) :
  decode w c (RState_mk true l r) -[ tm ]->*
    decode w c (match scanPL 66 9 l with
                | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: pR 36 :: restR)
                | OptList_none =>
                  match restR with
                  | b1 :: b1 :: restR5 =>
                    match scanPL 66 29 l with
                    | OptList_some l' => RState_mk true l' (b0 :: b0 :: b0 :: b1 :: b1 :: pR 14 :: restR5)
                    | OptList_none => stepE_000_rest l r restR
                    end
                  | _ => stepE_000_rest l r restR
                  end
                end).
Proof.
  destruct (scanPL 66 9 l) as [|l'] eqn:Hsc9.
  - destruct restR as [|[] rr1]; try exact (stepE_000_rest_sound w c l r _ Hr).
    destruct rr1 as [|[] restR5]; try exact (stepE_000_rest_sound w c l r _ Hr).
    destruct (scanPL 66 29 l) as [|l29] eqn:Hsc29; [exact (stepE_000_rest_sound w c l r _ Hr) |].
    subst r. cbn [decode decodeList].
    rewrite (scanPL_spec 66 29 ltac:(lia) l l29 Hsc29 w c blank).
    apply p66_L29_rep.
  - subst r. cbn [decode decodeList].
    rewrite (scanPL_spec 66 9 ltac:(lia) l l' Hsc9 w c blank).
    apply p66_L9_rep.
Qed.

Lemma stepE_000_p66_sound (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b0 :: b0 :: b0 :: restR) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (stepE_000_p66 l r restR).
Proof.
  destruct l as [|ch1 l1]; [exact (stepE_000_rest_sound w c [] r restR Hr) |].
  destruct ch1 as [ | | | | n | ]; try exact (stepE_000_rest_sound w c _ r restR Hr).
  - destruct l1 as [|[] l2]; try exact (stepE_000_p66_b0_fall w c _ r restR Hr).
    destruct l2 as [|[] l3]; try exact (stepE_000_p66_b0_fall w c _ r restR Hr).
    destruct l3 as [|[] l4]; try exact (stepE_000_p66_b0_fall w c _ r restR Hr).
    cbn [stepE_000_p66].
    destruct (scanPL 66 16 (b0 :: b1 :: b1 :: b0 :: l4)) as [|l'] eqn:Hsc.
    + destruct (stripP16 (b0 :: b1 :: b1 :: b0 :: l4)) as [|la] eqn:Hst; [exact (pop10E_sound w c _ r) |].
      destruct (loopP16 64 la (preR64 restR)) as [|l' r'] eqn:Hlp; [exact (pop10E_sound w c _ r) |].
      subst r. eapply evstep_trans; [| exact (loopP16_sound w c 64 la (preR64 restR) l' r' Hlp)].
      cbn [decode]. rewrite (stripP16_spec w c _ la blank Hst).
      cbn [decodeList]. rewrite preR64_spec. apply p66_L16.
    + subst r. cbn [decode].
      rewrite (scanPL_spec 66 16 ltac:(lia) _ l' Hsc w c blank).
      cbn [decodeList]. apply p66_L16_rep.
  - destruct l1 as [|[] l2]; try exact (stepE_000_p66_b1_fall w c _ r restR Hr).
    + destruct l2 as [|[] l3]; try exact (stepE_000_p66_b1_fall w c _ r restR Hr).
      destruct l3 as [|[] l4]; try exact (stepE_000_p66_b1_fall w c _ r restR Hr).
      cbn [stepE_000_p66].
      destruct (scanPL 66 9 (b1 :: b0 :: b0 :: b0 :: l4)) as [|l'] eqn:Hsc.
      * destruct (stripP9 (b1 :: b0 :: b0 :: b0 :: l4)) as [|la] eqn:Hst;
          [exact (stepE_000_rest_sound w c _ r restR Hr) |].
        destruct (loopP9 64 la (preR36 restR)) as [|l' r'] eqn:Hlp;
          [exact (stepE_000_rest_sound w c _ r restR Hr) |].
        subst r. eapply evstep_trans; [| exact (loopP9_sound w c 64 la (preR36 restR) l' r' Hlp)].
        cbn [decode]. rewrite (stripP9_spec w c _ la blank Hst).
        cbn [decodeList]. rewrite preR36_spec. apply p66_L9.
      * subst r. cbn [decode].
        rewrite (scanPL_spec 66 9 ltac:(lia) _ l' Hsc w c blank).
        cbn [decodeList]. apply p66_L9_rep.
    + destruct l2 as [|[] l3]; try exact (stepE_000_p66_b1_fall w c _ r restR Hr).
      destruct l3 as [|[] l4]; try exact (stepE_000_p66_b1_fall w c _ r restR Hr).
      cbn [stepE_000_p66].
      destruct restR as [|[] rr1]; try exact (stepE_000_rest_sound w c _ r _ Hr).
      destruct rr1 as [|[] restR5]; try exact (stepE_000_rest_sound w c _ r _ Hr).
      destruct (scanPL 66 29 (b1 :: b1 :: b0 :: b0 :: l4)) as [|l'] eqn:Hsc.
      * destruct (stripP29 (b1 :: b1 :: b0 :: b0 :: l4)) as [|la] eqn:Hst;
          [exact (stepE_000_rest_sound w c _ r _ Hr) |].
        destruct (loopP29 64 la (preR14 restR5)) as [|l' r'] eqn:Hlp;
          [exact (stepE_000_rest_sound w c _ r _ Hr) |].
        subst r. eapply evstep_trans; [| exact (loopP29_sound w c 64 la (preR14 restR5) l' r' Hlp)].
        cbn [decode]. rewrite (stripP29_spec w c _ la blank Hst).
        cbn [decodeList]. rewrite preR14_spec. apply p66_L29.
      * subst r. cbn [decode].
        rewrite (scanPL_spec 66 29 ltac:(lia) _ l' Hsc w c blank).
        cbn [decodeList]. apply p66_L29_rep.
  - do 29 (destruct n as [|n];
      [ first [ (cbn [stepE_000_p66]; subst r; apply p66_L9_rep)
              | (cbn [stepE_000_p66]; subst r; apply p66_L16_rep)
              | exact (stepE_000_rest_sound w c _ r restR Hr) ] | ]).
    destruct n as [|n]; [| exact (stepE_000_rest_sound w c _ r restR Hr)].
    cbn [stepE_000_p66].
    destruct restR as [|[] rr1]; try exact (pop10E_sound w c _ r).
    destruct rr1 as [|[] restR5]; try exact (pop10E_sound w c _ r).
    subst r. apply p66_L29_rep.
Qed.

Lemma stepE_000_sound (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b0 :: b0 :: b0 :: restR) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (stepE_000 l r restR).
Proof.
  destruct l as [|ch1 l1]; [exact (stepE_000_p66_sound w c [] r restR Hr) |].
  destruct ch1 as [ | | f | | | ]; try exact (stepE_000_p66_sound w c _ r restR Hr).
  - destruct l1 as [|ch2 restL]; [exact (stepE_000_p66_sound w c _ r restR Hr) |].
    destruct ch2 as [ | | f | | | ]; try exact (stepE_000_p66_sound w c _ r restR Hr).
    cbn [stepE_000].
    destruct restR as [|[] rr1]; try exact (pop10E_sound w c _ r).
    destruct rr1 as [|[] rr2]; try exact (pop10E_sound w c _ r).
    destruct rr2 as [|[] rr3]; try exact (pop10E_sound w c _ r).
    destruct rr3 as [|[] rr4]; try exact (pop10E_sound w c _ r).
    destruct rr4 as [|[] restR8]; try exact (pop10E_sound w c _ r).
    destruct (scanLeftB_p0 64 restL (b0 :: wR (negb f) :: b1 :: b0 :: b0 :: b0 :: b1 :: b1 :: b1 :: restR8))
      as [|restL' outR] eqn:Hsc; [exact (pop10E_sound w c _ r) |].
    destruct (scanLeftB_p0_spec w c 64 restL _ restL' outR Hsc) as [u [HL HR]].
    subst r. cbn [decode decodeList]. rewrite HL, HR; cbn [decodeList].
    rewrite !shift_0_encWL, shift_0_encWR.
    pose proof (leftPassB_p0_reaches ((if f then flipW w else w) ++ u)
                  (decodeList w c restL' blank) (decodeList w c restR8 blank)) as Hmain.
    rewrite encWL_b0_append, flipW_append, List.rev_app_distr, encWR0_append, <- flip_cond in Hmain.
    exact Hmain.
  - destruct l1 as [|[] l2]; try exact (stepE_000_p66_sound w c _ r restR Hr).
    destruct l2 as [|[] l3]; try exact (stepE_000_p66_sound w c _ r restR Hr).
    destruct l3 as [|ch4 restL]; [exact (stepE_000_p66_sound w c _ r restR Hr) |].
    destruct ch4 as [ | | f | | | ]; try exact (stepE_000_p66_sound w c _ r restR Hr).
    cbn [stepE_000].
    destruct (scanLeftB_p1 64 restL (wR (negb f) :: b1 :: b1 :: b1 :: b0 :: restR))
      as [|restL' outR] eqn:Hsc; [exact (pop10E_sound w c _ r) |].
    destruct (scanLeftB_p1_spec w c 64 restL _ restL' outR Hsc) as [u [HL HR]].
    subst r. cbn [decode decodeList]. rewrite HL, HR; cbn [decodeList].
    pose proof (leftPassB_p1_reaches ((if f then flipW w else w) ++ u)
                  (decodeList w c restL' blank) (decodeList w c restR blank)) as Hmain.
    rewrite encWL_append, flipW_append, List.rev_app_distr, encWR_append, <- flip_cond in Hmain.
    exact Hmain.
  - cbn [stepE_000]. subst r.
    exact (leftPassA_reaches (if f then flipW w else w) (decodeList w c l1 blank) (decodeList w c restR blank)).
Qed.

Lemma stepE_1_sound (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b1 :: restR) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (stepE_1 l r restR).
Proof.
  destruct l as [|[] l1]; try exact (pop10E_sound w c _ r).
  - destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ r).
    destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
    destruct l3 as [|[] restL]; try exact (pop10E_sound w c _ r).
    cbn [stepE_1]. exact (br2_enter w c restL r).
  - destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ r).
    + destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
      destruct l3 as [|[] l4]; try exact (pop10E_sound w c _ r).
      * cbn [stepE_1].
        destruct restR as [|[] rr1]; try exact (pop10E_sound w c _ r).
        -- destruct rr1 as [|[] rr2]; try exact (pop10E_sound w c _ r).
           ++ destruct rr2 as [|[] restR4]; try exact (pop10E_sound w c _ r).
              destruct (scanSuperBounce l4) as [|l'] eqn:Hsc; [exact (pop10E_sound w c _ r) |].
              destruct (scanSuperBounce_spec w c l4 l' Hsc) as [k [tail [H1 H2]]].
              subst r. cbn [decode decodeList]. rewrite H1, H2.
              exact (superBounce_reaches k tail (decodeList w c restR4 blank)).
           ++ destruct rr2 as [|[] rr3]; try exact (pop10E_sound w c _ r).
              destruct rr3 as [|[] rr4]; try exact (pop10E_sound w c _ r).
              destruct rr4 as [|[] rr5]; try exact (pop10E_sound w c _ r).
              destruct rr5 as [|[] rr6]; try exact (pop10E_sound w c _ r).
              destruct rr6 as [|[] restR8]; try exact (pop10E_sound w c _ r).
              subst r. exact (br6_enter w c l4 restR8).
        -- destruct rr1 as [|[] rr2]; try exact (pop10E_sound w c _ r).
           destruct rr2 as [|[] rr3]; try exact (pop10E_sound w c _ r).
           destruct rr3 as [|ch4 rr4]; [exact (pop10E_sound w c _ r) |].
           destruct ch4 as [ | | | f | | ]; try exact (pop10E_sound w c _ r).
           ++ subst r. exact (br4_enter w c l4 rr4).
           ++ destruct rr4 as [|[] rr5]; try exact (pop10E_sound w c _ r).
              destruct rr5 as [|[] rr6]; try exact (pop10E_sound w c _ r).
              destruct rr6 as [|[] rr7]; try exact (pop10E_sound w c _ r).
              destruct rr7 as [|[] rr8]; try exact (pop10E_sound w c _ r).
              destruct rr8 as [|[] rr9]; try exact (pop10E_sound w c _ r).
              destruct rr9 as [|[] rr10]; try exact (pop10E_sound w c _ r).
              destruct rr10 as [|[] restR12]; try exact (pop10E_sound w c _ r).
              destruct l4 as [|[] ll5]; try exact (pop10E_sound w c _ r).
              destruct ll5 as [|[] ll6]; try exact (pop10E_sound w c _ r).
              destruct ll6 as [|[] ll7]; try exact (pop10E_sound w c _ r).
              destruct ll7 as [|[] ll8]; try exact (pop10E_sound w c _ r).
              destruct ll8 as [|[] restL9]; try exact (pop10E_sound w c _ r).
              subst r. cbn [decode decodeList].
              pose proof (pass4_111_reaches (List.rev (if f then flipW w else w))
                            (decodeList w c restL9 blank) (decodeList w c restR12 blank)) as Hmain.
              rewrite List.rev_involutive in Hmain. exact Hmain.
      * destruct l4 as [|[] restL]; try exact (pop10E_sound w c _ r).
        cbn [stepE_1].
        destruct (scanPR 66 63 restR) as [|r'] eqn:Hsc.
        -- destruct (stripR63 restR) as [|ra] eqn:Hst; [exact (pop10E_sound w c _ r) |].
           destruct (loopR63 64 ra (preP14 restL)) as [|r' l'] eqn:Hlp; [exact (pop10E_sound w c _ r) |].
           subst r. eapply evstep_trans; [| exact (loopR63_sound w c 64 ra (preP14 restL) r' l' Hlp)].
           cbn [decode decodeList]. rewrite (stripR63_spec w c restR ra blank Hst), preP14_spec.
           apply p66_R63.
        -- subst r. cbn [decode decodeList].
           rewrite (scanPR_spec 66 63 ltac:(lia) restR r' Hsc w c blank).
           apply p66_R63_rep.
    + destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
      destruct l3 as [|[] restL]; try exact (pop10E_sound w c _ r).
      cbn [stepE_1]. exact (br1_enter w c restL r).
Qed.

Lemma stepE_0_sound (w : list bool) (c : nat) (l r restR : list Chunk)
  (Hr : r = b0 :: restR) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (stepE_0 l r restR).
Proof.
  destruct l as [|[] l1]; try exact (pop10E_sound w c _ r).
  - destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ r).
    destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
    destruct l3 as [|[] l4]; try exact (pop10E_sound w c _ r).
    destruct l4 as [|[] l5]; try (cbn [stepE_0]; exact (br2_enter w c _ r)).
    destruct l5 as [|[] l6]; try (cbn [stepE_0]; exact (br2_enter w c _ r)).
    destruct l6 as [|[] l7]; try (cbn [stepE_0]; exact (br2_enter w c _ r)).
    destruct l7 as [|[] restL]; try (cbn [stepE_0]; exact (br2_enter w c _ r)).
    cbn [stepE_0].
    destruct (scanPR 66 4 restR) as [|r'] eqn:Hsc.
    + exact (br2_enter w c (b1 :: b0 :: b1 :: b0 :: restL) r).
    + subst r. cbn [decode decodeList].
      rewrite (scanPR_spec 66 4 ltac:(lia) restR r' Hsc w c blank).
      apply p66_R4_rep.
  - destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ r).
    destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ r).
    destruct l3 as [|[] restL]; try exact (pop10E_sound w c _ r).
    cbn [stepE_0]. exact (br1_enter w c restL r).
Qed.

Lemma stepTrue_sound (w : list bool) (c : nat) (l r : list Chunk) :
  decode w c (RState_mk true l r) -[ tm ]->* decode w c (stepTrue l r).
Proof.
  destruct r as [|c1 r1].
  - cbn [stepTrue].
    destruct l as [|[] l1]; try exact (pop10E_sound w c _ []).
    + destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ []).
      destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ []).
      destruct l3 as [|[] restL]; try exact (pop10E_sound w c _ []).
      exact (br2_enter w c restL []).
    + destruct l1 as [|[] l2]; try exact (pop10E_sound w c _ []).
      destruct l2 as [|[] l3]; try exact (pop10E_sound w c _ []).
      destruct l3 as [|[] restL]; try exact (pop10E_sound w c _ []).
      exact (br1_enter w c restL []).
  - destruct c1; try exact (pop10E_fallback_sound w c l _).
    + destruct r1 as [|c2 r2]; [exact (stepE_0_sound w c l _ [] eq_refl) |].
      destruct c2; try exact (stepE_0_sound w c l _ _ eq_refl).
      destruct r2 as [|c3 restR]; [exact (stepE_0_sound w c l _ _ eq_refl) |].
      destruct c3; try exact (stepE_0_sound w c l _ _ eq_refl).
      cbn [stepTrue]. exact (stepE_000_sound w c l _ restR eq_refl).
    + cbn [stepTrue]. exact (stepE_1_sound w c l _ r1 eq_refl).
Qed.

Lemma stepFast_sound (w : list bool) (c : nat) (s : RState) :
  decode w c s -[ tm ]->* decode w c (stepFast s).
Proof.
  destruct s as [[|] l r]; [apply stepTrue_sound | apply stepFalse_sound].
Qed.

Lemma runPos_sound (w : list bool) (c : nat) (p : positive) (s : RState) :
  decode w c s -[ tm ]->* decode w c (runPos p s).
Proof.
  unfold runPos.
  exact (Pos.iter_invariant p RState stepFast
           (fun s' => decode w c s -[ tm ]->* decode w c s')
           (fun x Hx => evstep_trans _ _ _ _ Hx (stepFast_sound w c x))
           s (evstep_refl _ _)).
Qed.

(** ** 8. Structural Equality, Algebraic Handoffs, and Global Closure *)

Fixpoint wLChunks (w : list bool) : list Chunk :=
  match w with
  | [] => []
  | false :: ws => b1 :: b0 :: b0 :: b0 :: wLChunks ws
  | true  :: ws => b0 :: b1 :: b0 :: b0 :: wLChunks ws
  end.

Fixpoint prev66N (k r : nat) : nat :=
  match k with
  | 0 => r
  | S k' => prev66N k' (prev66 r)
  end.

Fixpoint isPureBits (xs : list Chunk) : bool :=
  match xs with
  | [] => true
  | b0 :: xs' => isPureBits xs'
  | b1 :: xs' => isPureBits xs'
  | _ => false
  end.

Fixpoint repPL0Chunks (k : nat) (tl : list Chunk) : list Chunk :=
  match k with
  | 0 => tl
  | S k' => prePL0 (repPL0Chunks k' tl)
  end.

Fixpoint shiftPL (k r : nat) (xs : list Chunk) : OptPair :=
  match k with
  | 0 => OptPair_some [] xs
  | S k' =>
    match xs with
    | [] => OptPair_none
    | b :: xs' =>
      if Nat.leb r 65 then
        if matchBit (plTopIs1 r) b then
          match shiftPL k' (prev66 r) xs' with
          | OptPair_none => OptPair_none
          | OptPair_some pref rest => OptPair_some (b :: pref) rest
          end
        else OptPair_none
      else OptPair_none
    end
  end.

Fixpoint splitAt (n : nat) (xs : list Chunk) : OptPair :=
  match n with
  | 0 => OptPair_some [] xs
  | S n' =>
    match xs with
    | [] => OptPair_none
    | x :: xs' =>
      match splitAt n' xs' with
      | OptPair_none => OptPair_none
      | OptPair_some pre post => OptPair_some (x :: pre) post
      end
    end
  end.

Fixpoint stripRepPL0 (k : nat) (xs : list Chunk) : OptList :=
  match k with
  | 0 => OptList_some xs
  | S k' =>
    match stripBits pL0_66 xs with
    | OptList_none => OptList_none
    | OptList_some xs1 => stripRepPL0 k' xs1
    end
  end.

Fixpoint parseWLChunks (n : nat) (xs : list Chunk) : option (list bool * list Chunk) :=
  match n with
  | 0 => Some ([], xs)
  | S n' =>
    match xs with
    | b1 :: b0 :: b0 :: b0 :: xs' =>
      match parseWLChunks n' xs' with
      | None => None
      | Some (u, rest) => Some (false :: u, rest)
      end
    | b0 :: b1 :: b0 :: b0 :: xs' =>
      match parseWLChunks n' xs' with
      | None => None
      | Some (u, rest) => Some (true :: u, rest)
      end
    | _ => None
    end
  end.

Definition initAt (lenA c0_cnt lenB lenW0 : nat) (s : RState) : option RState :=
  match s with
  | RState_mk false l [] =>
    match splitAt lenA l with
    | OptPair_some chA l1 =>
      match stripRepPL0 c0_cnt l1 with
      | OptList_some l2 =>
        match splitAt lenB l2 with
        | OptPair_some chB l3 =>
          match parseWLChunks lenW0 l3 with
          | Some (_, chC) =>
            if isPureBits chA && isPureBits chB && isPureBits chC then
              Some (RState_mk false (chA ++ [pL 0] ++ chB ++ [wL false] ++ chC) [])
            else None
          | None => None
          end
        | OptPair_none => None
        end
      | OptList_none => None
      end
    | OptPair_none => None
    end
  | _ => None
  end.

Definition repackAt (lenPre lenA k1 k2 m1 m2 dc lenB lenUTop lenUBot : nat) (s : RState) : option RState :=
  match s with
  | RState_mk false l [] =>
    match splitAt lenPre l with
    | OptPair_some pre (pL 14 :: post) =>
      match shiftPL 14 14 post with
      | OptPair_some pref rest =>
        let l_sh := pre ++ pref ++ pL 0 :: rest in
        match splitAt lenA l_sh with
        | OptPair_some chA l1 =>
          match stripRepPL0 k1 l1 with
          | OptList_some (pL 0 :: l3) =>
            match stripRepPL0 k2 l3 with
            | OptList_some l4 =>
              match splitAt lenB l4 with
              | OptPair_some chB l5 =>
                match parseWLChunks lenUTop l5 with
                | Some (_, wL _ :: l7) =>
                  match parseWLChunks lenUBot l7 with
                  | Some (_, chC) =>
                    if Nat.eqb (k1 + k2) (m1 + m2 + dc) &&
                       isPureBits chA && isPureBits chB && isPureBits chC then
                      Some (RState_mk false (chA ++ repPL0Chunks m1 (pL 0 :: repPL0Chunks m2 (chB ++ [wL false] ++ chC))) [])
                    else None
                  | None => None
                  end
                | _ => None
                end
              | OptPair_none => None
              end
            | OptList_none => None
            end
          | _ => None
          end
        | OptPair_none => None
        end
      | OptPair_none => None
      end
    | _ => None
    end
  | _ => None
  end.

Inductive Action : Type :=
  | ActRun : positive -> Action
  | ActInit : N -> N -> N -> N -> Action
  | ActRepack : N -> N -> N -> N -> N -> N -> N -> N -> N -> N -> Action.

Fixpoint execActions (acts : list Action) (s : RState) : option RState :=
  match acts with
  | [] => Some s
  | ActRun p :: acts' => execActions acts' (runPos p s)
  | ActInit la c0 lb lw :: acts' =>
    match initAt (N.to_nat la) (N.to_nat c0) (N.to_nat lb) (N.to_nat lw) s with
    | Some s1 => execActions acts' s1
    | None => None
    end
  | ActRepack lp la k1 k2 m1 m2 dc lb ut ub :: acts' =>
    match repackAt (N.to_nat lp) (N.to_nat la) (N.to_nat k1) (N.to_nat k2)
                   (N.to_nat m1) (N.to_nat m2) (N.to_nat dc) (N.to_nat lb)
                   (N.to_nat ut) (N.to_nat ub) s with
    | Some s1 => execActions acts' s1
    | None => None
    end
  end.

Definition beqChunk (x y : Chunk) : bool :=
  match x, y with
  | b0, b0 => true
  | b1, b1 => true
  | wL a, wL b => Bool.eqb a b
  | wR a, wR b => Bool.eqb a b
  | pL a, pL b => Nat.eqb a b
  | pR a, pR b => Nat.eqb a b
  | _, _ => false
  end.

Fixpoint beqList (xs ys : list Chunk) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => beqChunk x y && beqList xs' ys'
  | _, _ => false
  end.

Definition beqState (s1 s2 : RState) : bool :=
  match s1, s2 with
  | RState_mk d1 l1 r1, RState_mk d2 l2 r2 =>
    Bool.eqb d1 d2 && beqList l1 l2 && beqList r1 r2
  end.

Definition beqOptState (os : option RState) (s2 : RState) : bool :=
  match os with
  | Some s1 => beqState s1 s2
  | None => false
  end.

Lemma beqChunk_eq {x y : Chunk} (H : beqChunk x y = true) : x = y.
Proof.
  destruct x, y; try discriminate H; try reflexivity; cbn [beqChunk] in H.
  - apply Bool.eqb_prop in H; subst; reflexivity.
  - apply Bool.eqb_prop in H; subst; reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
Qed.

Lemma beqList_eq {xs ys : list Chunk} (H : beqList xs ys = true) : xs = ys.
Proof.
  revert ys H. induction xs as [|x xs' IH]; intros [|y ys'] H; try discriminate H; [reflexivity |].
  cbn [beqList] in H. apply Bool.andb_true_iff in H as [Hxy Hrest].
  rewrite (beqChunk_eq Hxy), (IH ys' Hrest). reflexivity.
Qed.

Lemma beqState_eq {s1 s2 : RState} (H : beqState s1 s2 = true) : s1 = s2.
Proof.
  destruct s1 as [d1 l1 r1], s2 as [d2 l2 r2].
  cbn [beqState] in H.
  apply Bool.andb_true_iff in H as [Hdl Hr].
  apply Bool.andb_true_iff in Hdl as [Hd Hl].
  apply Bool.eqb_prop in Hd.
  rewrite Hd, (beqList_eq Hl), (beqList_eq Hr). reflexivity.
Qed.

Lemma beqOptState_eq {os : option RState} {s2 : RState} (H : beqOptState os s2 = true) :
  os = Some s2.
Proof.
  destruct os as [s1|]; [| discriminate H].
  cbn [beqOptState] in H. rewrite (beqState_eq H). reflexivity.
Qed.

Lemma hub_first_step_plus (w : list bool) (c : nat) (l : list Chunk) :
  decode w c (RState_mk false l []) -[ tm ]->+
    decode w c (RState_mk true (b0 :: b1 :: l) [b0]).
Proof.
  cbn [decode decodeList].
  pose proof (stepB_000 (decodeList w c l blank) blank) as H.
  repeat rewrite z00 in H. repeat rewrite z00. exact H.
Qed.

Lemma decodeList_pure (xs : list Chunk) (Hp : isPureBits xs = true)
  (w1 w2 : list bool) (c1 c2 : nat) (lb : side) :
  decodeList w1 c1 xs lb = decodeList w2 c2 xs lb.
Proof.
  induction xs as [|ch rest IH]; [reflexivity |].
  destruct ch; try discriminate Hp; cbn [isPureBits] in Hp;
    cbn [decodeList]; rewrite (IH Hp); reflexivity.
Qed.

Lemma decodeList_wLChunks (w : list bool) (c : nat) (u : list bool) (lb : side) :
  decodeList w c (wLChunks u) lb = encWL u lb.
Proof.
  induction u as [|[|] ws IH]; [reflexivity | | ];
    cbn [wLChunks decodeList encWL]; rewrite IH; reflexivity.
Qed.

Lemma decodeList_repPL0Chunks (w : list bool) (c k : nat) (tl : list Chunk) (lb : side) :
  decodeList w c (repPL0Chunks k tl) lb = repPL 0 k (decodeList w c tl lb).
Proof.
  induction k as [|k IH]; [reflexivity |].
  cbn [repPL0Chunks repPL]. rewrite prePL0_spec, IH. reflexivity.
Qed.

Lemma decode_false_nil_eq (w1 w2 : list bool) (c1 c2 : nat) (l1 l2 : list Chunk) :
  decodeList w1 c1 l1 blank = decodeList w2 c2 l2 blank ->
  decode w1 c1 (RState_mk false l1 []) = decode w2 c2 (RState_mk false l2 []).
Proof.
  intros H. unfold decode. rewrite H. reflexivity.
Qed.

Lemma repack_wp_gen (chA chB chC : list Chunk)
  (HA : isPureBits chA = true) (HB : isPureBits chB = true) (HC : isPureBits chC = true)
  (k1 k2 m1 m2 dc : nat) (Hsum : k1 + k2 = m1 + m2 + dc)
  (uTop uBot : list bool) (f : bool) (w : list bool) (c : nat) :
  decode w c (RState_mk false
    (chA ++ repPL0Chunks k1 (pL 0 :: repPL0Chunks k2 (chB ++ wLChunks uTop ++ [wL f] ++ wLChunks uBot ++ chC))) []) =
  decode (uTop ++ (if f then flipW w else w) ++ uBot) (c + dc)
    (RState_mk false (chA ++ repPL0Chunks m1 (pL 0 :: repPL0Chunks m2 (chB ++ [wL false] ++ chC))) []).
Proof.
  set (w' := uTop ++ (if f then flipW w else w) ++ uBot).
  apply decode_false_nil_eq.
  rewrite !decodeList_append, !decodeList_repPL0Chunks; cbn [decodeList].
  rewrite !decodeList_repPL0Chunks, !decodeList_append, !decodeList_wLChunks; cbn [decodeList].
  subst w'. rewrite !encWL_append.
  rewrite <- !repPL_add.
  replace (k1 + c + k2) with (m1 + (c + dc) + m2) by lia.
  set (w' := uTop ++ (if f then flipW w else w) ++ uBot).
  rewrite (decodeList_pure chA HA w w' c (c + dc)).
  rewrite (decodeList_pure chB HB w w' c (c + dc)).
  rewrite (decodeList_pure chC HC w w' c (c + dc)).
  reflexivity.
Qed.

Lemma init_wp (chA chB chC : list Chunk)
  (HA : isPureBits chA = true) (HB : isPureBits chB = true) (HC : isPureBits chC = true)
  (c0_cnt : nat) (w0 : list bool) (w : list bool) (c : nat) :
  decode w c (RState_mk false (chA ++ repPL0Chunks c0_cnt (chB ++ wLChunks w0 ++ chC)) []) =
  decode w0 c0_cnt (RState_mk false (chA ++ [pL 0] ++ chB ++ [wL false] ++ chC) []).
Proof.
  apply decode_false_nil_eq.
  rewrite !decodeList_append, !decodeList_repPL0Chunks, !decodeList_append, !decodeList_wLChunks; cbn [decodeList].
  rewrite (decodeList_pure chA HA w w0 c c0_cnt).
  rewrite (decodeList_pure chB HB w w0 c c0_cnt).
  rewrite (decodeList_pure chC HC w w0 c c0_cnt).
  reflexivity.
Qed.

Lemma shiftPL_eq (w : list bool) (c k r : nat) (xs pref rest : list Chunk) (lb : side)
  (H : shiftPL k r xs = OptPair_some pref rest) :
  repPL r c (decodeList w c xs lb) =
    decodeList w c pref (repPL (prev66N k r) c (decodeList w c rest lb)).
Proof.
  revert r xs pref rest H.
  induction k as [|k IH]; intros r xs pref rest H.
  - cbn [shiftPL prev66N] in H |- *. inversion H; subst. reflexivity.
  - destruct xs as [|b xs']; [discriminate H |].
    cbn [shiftPL] in H.
    destruct (Nat.leb r 65) eqn:Hle; [| discriminate H].
    apply Nat.leb_le in Hle. assert (Hr : r < 66) by lia.
    pose proof (repPL_comm r Hr c (decodeList w c xs' lb)) as Hc.
    destruct (plTopIs1 r), b; cbn [matchBit] in H; try discriminate H;
      destruct (shiftPL k (prev66 r) xs') as [|pref0 rest0] eqn:Hsh; try discriminate H;
      inversion H; subst; cbn [decodeList prev66N];
      cbn [finOfBool] in Hc;
      (etransitivity; [symmetry; exact Hc | f_equal; exact (IH (prev66 r) xs' _ _ Hsh)]).
Qed.

Lemma decode_shiftPL_mid (w : list bool) (c k r : nat)
  (pre post pref rest : list Chunk)
  (H : shiftPL k r post = OptPair_some pref rest) :
  decode w c (RState_mk false (pre ++ pL r :: post) []) =
  decode w c (RState_mk false (pre ++ pref ++ pL (prev66N k r) :: rest) []).
Proof.
  apply decode_false_nil_eq.
  rewrite !decodeList_append; cbn [decodeList].
  rewrite (shiftPL_eq w c k r post pref rest blank H).
  reflexivity.
Qed.

Lemma splitAt_spec (n : nat) (xs pre post : list Chunk) :
  splitAt n xs = OptPair_some pre post -> xs = pre ++ post.
Proof.
  revert xs pre post. induction n as [|n IH]; intros xs pre post H.
  - cbn [splitAt] in H. inversion H; subst. reflexivity.
  - destruct xs as [|x xs']; [discriminate H |].
    cbn [splitAt] in H. destruct (splitAt n xs') as [|pre0 post0] eqn:Hs; [discriminate H |].
    inversion H; subst. cbn [app]. f_equal. exact (IH xs' pre0 post Hs).
Qed.

Lemma stripRepPL0_spec (k : nat) (xs rest : list Chunk) :
  stripRepPL0 k xs = OptList_some rest -> xs = repPL0Chunks k rest.
Proof.
  revert xs. induction k as [|k IH]; intros xs H.
  - cbn [stripRepPL0] in H. inversion H; subst. reflexivity.
  - cbn [stripRepPL0] in H.
    destruct (stripBits pL0_66 xs) as [|xs1] eqn:Hst; [discriminate H |].
    cbn [repPL0Chunks]. unfold prePL0.
    rewrite (stripBits_eq_preBits pL0_66 xs xs1 Hst), (IH xs1 H). reflexivity.
Qed.

Lemma parseWLChunks_spec (n : nat) (xs rest : list Chunk) (u : list bool) :
  parseWLChunks n xs = Some (u, rest) -> xs = wLChunks u ++ rest.
Proof.
  revert xs u. induction n as [|n IH]; intros xs u H.
  - cbn [parseWLChunks] in H. inversion H; subst. reflexivity.
  - destruct xs as [|[] xs1]; try discriminate H.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      cbn [parseWLChunks] in H.
      destruct (parseWLChunks n xs4) as [[u0 rest0]|] eqn:Hp; [| discriminate H].
      inversion H; subst. cbn [wLChunks app]. rewrite (IH xs4 u0 Hp). reflexivity.
    + destruct xs1 as [|[] xs2]; try discriminate H.
      destruct xs2 as [|[] xs3]; try discriminate H.
      destruct xs3 as [|[] xs4]; try discriminate H.
      cbn [parseWLChunks] in H.
      destruct (parseWLChunks n xs4) as [[u0 rest0]|] eqn:Hp; [| discriminate H].
      inversion H; subst. cbn [wLChunks app]. rewrite (IH xs4 u0 Hp). reflexivity.
Qed.

Lemma initAt_sound (lenA c0_cnt lenB lenW0 : nat) (s s' : RState)
  (H : initAt lenA c0_cnt lenB lenW0 s = Some s') (w : list bool) (c : nat) :
  exists (w' : list bool) (c' : nat), decode w c s = decode w' c' s'.
Proof.
  destruct s as [[|] l [|? ?]]; try discriminate H.
  unfold initAt in H.
  destruct (splitAt lenA l) as [|chA l1] eqn:Hs1; [discriminate H |].
  destruct (stripRepPL0 c0_cnt l1) as [|l2] eqn:Hst; [discriminate H |].
  destruct (splitAt lenB l2) as [|chB l3] eqn:Hs2; [discriminate H |].
  destruct (parseWLChunks lenW0 l3) as [[w0 chC]|] eqn:Hp; [| discriminate H].
  destruct (isPureBits chA && isPureBits chB && isPureBits chC) eqn:Hpure; [| discriminate H].
  inversion H; subst s'.
  apply Bool.andb_true_iff in Hpure as [HpureAB HC].
  apply Bool.andb_true_iff in HpureAB as [HA HB].
  rewrite (splitAt_spec _ _ _ _ Hs1), (stripRepPL0_spec _ _ _ Hst),
          (splitAt_spec _ _ _ _ Hs2), (parseWLChunks_spec _ _ _ _ Hp).
  exists w0, c0_cnt.
  exact (init_wp chA chB chC HA HB HC c0_cnt w0 w c).
Qed.

Lemma repackAt_sound (lenPre lenA k1 k2 m1 m2 dc lenB lenUTop lenUBot : nat) (s s' : RState)
  (H : repackAt lenPre lenA k1 k2 m1 m2 dc lenB lenUTop lenUBot s = Some s')
  (w : list bool) (c : nat) :
  exists (w' : list bool) (c' : nat), decode w c s = decode w' c' s'.
Proof.
  destruct s as [[|] l [|? ?]]; try discriminate H.
  unfold repackAt in H.
  destruct (splitAt lenPre l) as [|pre post0] eqn:Hsp0; [discriminate H |].
  destruct post0 as [|ch0 post]; [discriminate H |].
  destruct ch0 as [ | | | | r0 | ]; try discriminate H.
  do 14 (destruct r0 as [|r0]; [discriminate H | ]).
  destruct r0 as [|r0]; [| discriminate H].
  destruct (shiftPL 14 14 post) as [|pref rest] eqn:Hsh; [discriminate H |].
  set (l_sh := pre ++ pref ++ pL 0 :: rest) in H.
  destruct (splitAt lenA l_sh) as [|chA l1] eqn:HspA; [discriminate H |].
  destruct (stripRepPL0 k1 l1) as [|l2] eqn:Hst1; [discriminate H |].
  destruct l2 as [|ch2 l3]; [discriminate H |].
  destruct ch2 as [ | | | | r2 | ]; try discriminate H.
  destruct r2 as [|r2]; [| discriminate H].
  destruct (stripRepPL0 k2 l3) as [|l4] eqn:Hst2; [discriminate H |].
  destruct (splitAt lenB l4) as [|chB l5] eqn:HspB; [discriminate H |].
  destruct (parseWLChunks lenUTop l5) as [[uTop l6]|] eqn:HpTop; [| discriminate H].
  destruct l6 as [|ch6 l7]; [discriminate H |].
  destruct ch6 as [ | | f | | | ]; try discriminate H.
  destruct (parseWLChunks lenUBot l7) as [[uBot chC]|] eqn:HpBot; [| discriminate H].
  destruct (Nat.eqb (k1 + k2) (m1 + m2 + dc) && isPureBits chA && isPureBits chB && isPureBits chC)
    eqn:Hcond; [| discriminate H].
  inversion H; subst s'.
  apply Bool.andb_true_iff in Hcond as [Hcond1 HC].
  apply Bool.andb_true_iff in Hcond1 as [Hcond2 HB].
  apply Bool.andb_true_iff in Hcond2 as [Hsum HA].
  apply Nat.eqb_eq in Hsum.
  rewrite (splitAt_spec _ _ _ _ Hsp0).
  rewrite (decode_shiftPL_mid w c 14 14 pre post pref rest Hsh).
  change (prev66N 14 14) with 0.
  fold l_sh.
  assert (Hlsh : l_sh = chA ++ repPL0Chunks k1 (pL 0 :: repPL0Chunks k2 (chB ++ wLChunks uTop ++ [wL f] ++ wLChunks uBot ++ chC))).
  { rewrite (splitAt_spec _ _ _ _ HspA), (stripRepPL0_spec _ _ _ Hst1),
            (stripRepPL0_spec _ _ _ Hst2), (splitAt_spec _ _ _ _ HspB),
            (parseWLChunks_spec _ _ _ _ HpTop), (parseWLChunks_spec _ _ _ _ HpBot).
    cbn [app]. reflexivity. }
  rewrite Hlsh.
  exists (uTop ++ (if f then flipW w else w) ++ uBot), (c + dc).
  exact (repack_wp_gen chA chB chC HA HB HC k1 k2 m1 m2 dc Hsum uTop uBot f w c).
Qed.

Lemma execActions_sound (acts : list Action) (s s' : RState) :
  execActions acts s = Some s' ->
  forall (w : list bool) (c : nat),
    exists (w' : list bool) (c' : nat),
      decode w c s -[ tm ]->* decode w' c' s'.
Proof.
  revert s s'. induction acts as [|act acts' IH]; intros s s' H w c.
  - cbn [execActions] in H. inversion H; subst. exists w, c. apply evstep_refl.
  - destruct act as [p | la c0_cnt lb lw | lp la k1 k2 m1 m2 dc lb ut ub]; cbn [execActions] in H.
    + destruct (IH (runPos p s) s' H w c) as [w' [c' Hrest]].
      exists w', c'. eapply evstep_trans; [apply runPos_sound | exact Hrest].
    + destruct (initAt (N.to_nat la) (N.to_nat c0_cnt) (N.to_nat lb) (N.to_nat lw) s) as [s1|] eqn:Hi;
        [| discriminate H].
      destruct (initAt_sound _ _ _ _ s s1 Hi w c) as [w1 [c1 Heq]].
      destruct (IH s1 s' H w1 c1) as [w' [c' Hrest]].
      exists w', c'. rewrite Heq. exact Hrest.
    + destruct (repackAt (N.to_nat lp) (N.to_nat la) (N.to_nat k1) (N.to_nat k2)
                         (N.to_nat m1) (N.to_nat m2) (N.to_nat dc) (N.to_nat lb)
                         (N.to_nat ut) (N.to_nat ub) s) as [s1|] eqn:Hr;
        [| discriminate H].
      destruct (repackAt_sound _ _ _ _ _ _ _ _ _ _ s s1 Hr w c) as [w1 [c1 Heq]].
      destruct (IH s1 s' H w1 c1) as [w' [c' Hrest]].
      exists w', c'. rewrite Heq. exact Hrest.
Qed.

Definition p1_start : RState := RState_mk false [] [].

Definition stageAB_acts : list Action :=
  [ ActRun 572730%positive; ActInit   115   2 6708 2894;
    ActRun 84842%positive;  ActRepack 299 115 3 0 0 0 3 6514  74 271;
    ActRun 84335%positive;  ActRepack 233 115 2 0 0 0 2 5654 257 270;
    ActRun 82915%positive;  ActRepack 233 115 2 0 0 0 2 4378 361 270;
    ActRun 83253%positive;  ActRepack 233 115 2 0 0 0 2 2930 404 270;
    ActRun 83766%positive;  ActRepack 233 115 2 0 0 0 2 1898 300 270;
    ActRun 83401%positive;  ActRepack 233 115 2 0 0 0 2 1814  63 270;
    ActRun 84010%positive;  ActRepack 233 115 2 0 0 0 2 1766  54 270;
    ActRun 118691%positive; ActRepack 299  49 4 0 1 1 2 1680  77 395 ]%N.

Definition stageC_acts : list Action :=
  [ ActRun 81201%positive; ActRepack 299 49 4 0 1 1 2 1680 42 270 ]%N.

Definition gen := execActions stageAB_acts p1_start.
Definition seed_from (x : option RState) :=
  match x with
  | Some (RState_mk false l []) => l
  | _ => []
  end.
Definition cycle_in l := RState_mk true (b0 :: b1 :: l) [b0].
Definition cert_from (x : option RState) :=
  match x with
  | Some (RState_mk false l [] as s) =>
      beqOptState (execActions stageC_acts (cycle_in l)) s
  | _ => false
  end.
Definition seed := seed_from gen.
Definition start := RState_mk false seed [].

Lemma cert_ok : cert_from gen = true.
Proof. vm_compute. reflexivity. Qed.

Opaque execActions beqOptState.

Lemma cert_spec_from x : cert_from x = true ->
  x = Some (RState_mk false (seed_from x) []) /\
  beqOptState (execActions stageC_acts (cycle_in (seed_from x)))
    (RState_mk false (seed_from x) []) = true.
Proof.
  destruct x as [[[] l [|ch r]]|]; try discriminate.
  intros H. split; [reflexivity|exact H].
Qed.

Lemma cert_spec : gen = Some start /\
  beqOptState (execActions stageC_acts (cycle_in seed)) start = true.
Proof. exact (cert_spec_from gen cert_ok). Qed.

Lemma initial : exists w c, c0 -[ tm ]->* decode w c start.
Proof.
  destruct (execActions_sound stageAB_acts p1_start start (proj1 cert_spec) [] 0)
    as [w [c H]]. exists w, c. exact H.
Qed.

Lemma cycle (wc : list bool * nat) : exists wc',
  decode (fst wc) (snd wc) start -[ tm ]->+ decode (fst wc') (snd wc') start.
Proof.
  destruct wc as [w c]; cbn [fst snd].
  pose proof (hub_first_step_plus w c seed) as H1.
  pose proof (beqOptState_eq (proj2 cert_spec)) as Hrun.
  destruct (execActions_sound stageC_acts (cycle_in seed) start Hrun w c)
    as [w' [c' H2]].
  exists (w', c'). cbn [fst snd].
  eapply progress_evstep_trans; [exact H1|exact H2].
Qed.

Lemma core_nonhalt : ~ halts tm c0.
Proof.
  destruct initial as [w [c H]].
  eapply multistep_nonhalt; [exact H|].
  exact (progress_nonhalt_simple tm (list bool * nat)
    (fun wc => decode (fst wc) (snd wc) start) (w, c) cycle).
Qed.

End M390.

Theorem nonhalt : ~ halts tm c0.
Proof. exact M390.core_nonhalt. Qed.

Print Assumptions nonhalt.
