(** * The dip: the Odometer's one move, as an abstract machine.

    Validated against the raw machine 5999/5999 (tools/dipwalk.mjs,
    P-2026-08-14-o): every sweep's inward walk is a six-state machine
    over 4-cell glyphs. Raw spellings (left-to-right, value bits
    reversed): O=0101 e=0111 a=1101 f=1111. *)

From BusyCoq Require Import Individual62 Odometer.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

(** * The missing single-block rules (census rows not yet in Odometer.v). *)

(** F walks left over one e, byte-preserved. *)
Lemma F_e_left1 : forall l r,
  l <* <[0;1;1;1] <{{F}} r -->* l <{{F}} [0;1;1;1] *> r.
Proof. execute. Qed.

(** A walks left over one f, byte-preserved, exits C. *)
Lemma A_f_left1 : forall l r,
  l <* <[1;1;1;1] <{{A}} r -->* l <{{C}} [1;1;1;1] *> r.
Proof. execute. Qed.

(** A meets e: reflect, carry lands (e -> a). *)
Lemma A_e_reflect : forall l r,
  l <* <[0;1;1;1] <{{A}} r -->* l <* <[1;1;0;1] {{E}}> r.
Proof. execute. Qed.

(** A meets a: reflect, a preserved — THE MELT / collapse primitive. *)
Lemma A_a_reflect : forall l r,
  l <* <[1;1;0;1] <{{A}} r -->* l <* <[1;1;0;1] {{E}}> r.
Proof. execute. Qed.

(** C walks left over one a, byte-preserved. *)
Lemma C_a_left1 : forall l r,
  l <* <[1;1;0;1] <{{C}} r -->* l <{{C}} [1;1;0;1] *> r.
Proof. execute. Qed.

(** C meets e: converts it to f and probes deeper as D. *)
Lemma C_e_probe : forall l r,
  l <* <[0;1;1;1] <{{C}} r -->* l <{{D}} [1;1;1;1] *> r.
Proof. execute. Qed.

(** D probes O: carry lands two deep (O -> e), reflect as C. *)
Lemma D_O_reflect : forall l r,
  l <* <[0;1;0;1] <{{D}} r -->* l <* <[0;1;1;1] {{C}}> r.
Proof. execute. Qed.

(** D probes a: a -> f, reflect as C. *)
Lemma D_a_reflect : forall l r,
  l <* <[1;1;0;1] <{{D}} r -->* l <* <[1;1;1;1] {{C}}> r.
Proof. execute. Qed.

(** D probes e: e -> O, reflect as C. *)
Lemma D_e_reflect : forall l r,
  l <* <[0;1;1;1] <{{D}} r -->* l <* <[0;1;0;1] {{C}}> r.
Proof. execute. Qed.

(** The returning C meets the f it made and turns back inward as F. *)
Lemma C_f_redip : forall l r,
  l {{C}}> [1;1;1;1] *> r -->* l <{{F}} [1;1;1;1] *> r.
Proof. execute. Qed.

(** * Glyphs and the abstract dip machine. *)

Inductive glyph := gO | ge | ga | gf.

(** Raw spelling, left-to-right. *)
Definition graw (g : glyph) : list sym :=
  match g with
  | gO => [0;1;0;1] | ge => [0;1;1;1] | ga => [1;1;0;1] | gf => [1;1;1;1]
  end.

(** Reversed spelling, for pushing onto a left stream. *)
Definition grev (g : glyph) : list sym := rev (graw g).

(** A glyph string in walk order (separator first = rightmost on tape),
    interpreted as a left stream on top of a base [bl]. *)
Fixpoint gside (bl : side) (W : list glyph) : side :=
  match W with
  | [] => bl
  | g :: W' => gside bl W' <* grev g
  end.

(** The same cells as a right-side prefix (walk order = nearest first). *)
Fixpoint gright (W : list glyph) (r : side) : side :=
  match W with
  | [] => r
  | g :: W' => graw g *> gright W' r
  end.

(** The E-crossing toggle (value XOR 5). *)
Definition toggle (g : glyph) : glyph :=
  match g with gO => gf | gf => gO | ge => ga | ga => ge end.

(** The out-pass: toggle the crossed cells back onto the result. *)
Fixpoint unwind (sh deep : list glyph) : list glyph :=
  match sh with
  | [] => deep
  | g :: sh' => unwind sh' (toggle g :: deep)
  end.

Inductive wstate := wF | wA | wC | wD | wCr | wE.

Definition is_inward (s : wstate) : bool :=
  match s with wF | wA | wC | wD => true | _ => false end.

(** The inward rule table (the census, sealed over 100M steps). *)
Definition instep (s : wstate) (g : glyph) : option (glyph * wstate) :=
  match s, g with
  | wF, ge => Some (ge, wF) | wF, gf => Some (gf, wA)
  | wF, gO => Some (ge, wE) | wF, ga => Some (gf, wE)
  | wA, gO => Some (gf, wC) | wA, gf => Some (gf, wC)
  | wA, ge => Some (ga, wE) | wA, ga => Some (ga, wE)
  | wC, ga => Some (ga, wC) | wC, gf => Some (gf, wF)
  | wC, gO => Some (gf, wE) | wC, ge => Some (gf, wD)
  | wD, gO => Some (ge, wCr) | wD, ga => Some (gf, wCr) | wD, ge => Some (gO, wCr)
  | _, _ => None
  end.

(** The walk, as a zipper: [deep] = the current cell and everything
    deeper (head = current); [shallow] = crossed cells (head = nearest).
    In [wE] mode, [deep] doubles as the accumulating result. *)
Fixpoint dip_go (fuel : nat) (s : wstate) (deep shallow : list glyph)
    : option (list glyph) :=
  match fuel with
  | O => None
  | S fuel =>
    match s with
    | wE => Some (unwind shallow deep)
    | wCr =>
      match shallow with
      | gf :: _ => dip_go fuel wF deep shallow
      | _ => None
      end
    | _ =>
      match deep with
      | [] => None
      | g :: deep' =>
        match instep s g with
        | Some (g', s') =>
          if is_inward s'
          then dip_go fuel s' deep' (g' :: shallow)
          else dip_go fuel s' (g' :: deep') shallow
        | None => None
        end
      end
    end
  end.

(** The dip: enter at the right end of W in state F. *)
Definition dip (W : list glyph) : option (list glyph) :=
  dip_go (12 * length W + 60) wF W [].

(** * Soundness: the abstract walk is the machine. *)

(** E walks right over any glyph, toggling it (one bridge lemma over
    the four cases). *)
Lemma E_toggle : forall g l r,
  l {{E}}> graw g *> r -->* l <* grev (toggle g) {{E}}> r.
Proof. destruct g; execute. Qed.

Lemma unwind_sound : forall (shallow deep : list glyph) bl r,
  gside bl deep {{E}}> gright shallow r -->*
  gside bl (unwind shallow deep) {{E}}> r.
Proof.
  induction shallow as [| a shallow IHshallow]; introv.
  - cbn. finish.
  - cbn. follow E_toggle.
    change (grev (toggle a) *> gside bl deep)
      with (gside bl (toggle a :: deep)).
    apply IHshallow.
Qed.

(** The tape configuration of a walk state. *)
Definition wcfg (s : wstate) (bl : side) (deep shallow : list glyph)
    (r : side) : Q * tape :=
  match s with
  | wF => gside bl deep <{{F}} gright shallow r
  | wA => gside bl deep <{{A}} gright shallow r
  | wC => gside bl deep <{{C}} gright shallow r
  | wD => gside bl deep <{{D}} gright shallow r
  | wCr => gside bl deep {{C}}> gright shallow r
  | wE => gside bl deep {{E}}> gright shallow r
  end.

Lemma dip_go_sound : forall fuel s deep shallow W' bl r,
  dip_go fuel s deep shallow = Some W' ->
  wcfg s bl deep shallow r -->* gside bl W' {{E}}> r.
Proof.
  induction fuel; introv H. { discriminate. }
  destruct s; cbn in H.
  - (* wF *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow (F_x0_bounce 0). apply (IHfuel _ _ _ _ _ _ H).
    + follow F_e_left1. apply (IHfuel _ _ _ _ _ _ H).
    + follow (F_x0_bounce 1). apply (IHfuel _ _ _ _ _ _ H).
    + follow F_f_left1. apply (IHfuel _ _ _ _ _ _ H).
  - (* wA *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow A_O_left1. apply (IHfuel _ _ _ _ _ _ H).
    + follow A_e_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow A_a_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow A_f_left1. apply (IHfuel _ _ _ _ _ _ H).
  - (* wC *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow sep_bounce. apply (IHfuel _ _ _ _ _ _ H).
    + follow C_e_probe. apply (IHfuel _ _ _ _ _ _ H).
    + follow C_a_left1. apply (IHfuel _ _ _ _ _ _ H).
    + follow C_f_left1. apply (IHfuel _ _ _ _ _ _ H).
  - (* wD *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow D_O_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow D_e_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow D_a_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + discriminate.
  - (* wCr *)
    destruct shallow as [| g sh]; [discriminate |].
    destruct g; try discriminate.
    cbn.
    follow C_f_redip. apply (IHfuel _ _ _ _ _ _ H).
  - (* wE *)
    injection H as <-. apply unwind_sound.
Qed.

(** The dip, from the anchor side: entering the string in state F. *)
Corollary dip_sound : forall W W' bl,
  dip W = Some W' ->
  forall r, gside bl W <{{F}} r -->* gside bl W' {{E}}> r.
Proof.
  introv H. intros r. unfold dip in H.
  apply (dip_go_sound _ _ _ _ _ bl r) in H.
  cbn in H. exact H.
Qed.

(** * The universal sweep theorem. *)

(** An anchor: glyph string (separator-first), tail of n e's, edge O,
    head facing the blank half in state C. *)
Definition anchor (W : list glyph) (n : nat) : Q * tape :=
  gside (const 0) W <* <[0;1;1;1]^^n <* <[0;1;0;1] {{C}}> const 0.

Lemma edge_start_plus : forall l,
  l <* <[0;1;0;1] {{C}}> const 0 -->+ l <* <[0;1;1;1] {{C}}> 1 >> const 0.
Proof. introv. start_progress. Qed.

(** One sweep: if the dip succeeds on the string, the anchor steps to
    the next anchor — tail one longer, separator restored, zone as the
    dip left it. This is the ONLY tape-level theorem the proof needs;
    everything else is arithmetic about [dip]. *)
Theorem sweep_theorem : forall Z Z' n,
  dip (gf :: Z) = Some (gO :: Z') ->
  anchor (gf :: Z) n -->+ anchor (gf :: Z') (S n).
Proof.
  introv H.
  unfold anchor.
  eapply progress_evstep_trans.
  { apply edge_start_plus. }
  step.
  follow (F_es_left (S n)).
  follow (dip_sound _ _ (const 0) H).
  follow (E_es_right (S n)).
  follow virgin_reflect0.
  follow (C_as_left (S n)).
  follow sep_bounce.
  follow (E_as_right (S n)).
  follow virgin_finish.
  finish.
Qed.

(** * The invariant, and non-halt from it. *)

(** A glyph string is safe if its dips succeed forever. *)
CoInductive safe : list glyph -> Prop :=
| safe_step : forall Z Z',
    dip (gf :: Z) = Some (gO :: Z') ->
    safe (gf :: Z') ->
    safe (gf :: Z).

Theorem nonhalt_of_safe : forall Z n,
  safe (gf :: Z) -> ~ halts tm (anchor (gf :: Z) n).
Proof.
  introv HS.
  apply progress_nonhalt_cond with
    (A := (list glyph * nat)%type)
    (C := fun '(Z0, n0) => anchor (gf :: Z0) n0)
    (P := fun '(Z0, n0) => safe (gf :: Z0))
    (i0 := (Z, n)).
  - intros [Z0 n0] HP.
    inversion HP as [? Z' Hdip HS']; subst.
    exists (Z', S n0). split.
    + apply sweep_theorem. exact Hdip.
    + exact HS'.
  - exact HS.
Qed.

(** * The halt direction. *)

(** Falling off the left end of the written tape in state C: one step
    puts D over blank — the halt transition. *)
Lemma death_blank : forall r, halts tm (const 0 <{{C}} r).
Proof.
  introv.
  eapply halts_evstep.
  2: { step. finish. }
  apply halted_halts. reflexivity.
Qed.

(** Death detector: the walk falls off the left end inward in state C.
    (Any reflection means the dip succeeds; wF/wA falloffs do not occur
    on the orbit and are conservatively not-death.) *)
Fixpoint dip_go_dies (fuel : nat) (s : wstate) (deep shallow : list glyph)
    : bool :=
  match fuel with
  | O => false
  | S fuel =>
    match s with
    | wE => false
    | wCr =>
      match shallow with
      | gf :: _ => dip_go_dies fuel wF deep shallow
      | _ => false
      end
    | _ =>
      match deep with
      | [] => match s with wC => true | _ => false end
      | g :: deep' =>
        match instep s g with
        | Some (_, wE) => false
        | Some (g', wCr) => dip_go_dies fuel wCr (g' :: deep') shallow
        | Some (g', s') => dip_go_dies fuel s' deep' (g' :: shallow)
        | None => false
        end
      end
    end
  end.

Lemma dip_go_dies_sound : forall fuel s deep shallow r,
  dip_go_dies fuel s deep shallow = true ->
  halts tm (wcfg s (const 0) deep shallow r).
Proof.
  induction fuel; introv H. { discriminate. }
  destruct s; cbn in H.
  - (* wF *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; try discriminate.
    + eapply halts_evstep.
      * eapply IHfuel. exact H.
      * cbn. follow F_e_left1. finish.
    + eapply halts_evstep.
      * eapply IHfuel. exact H.
      * cbn. follow F_f_left1. finish.
  - (* wA *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; try discriminate.
    + eapply halts_evstep.
      * eapply IHfuel. exact H.
      * cbn. follow A_O_left1. finish.
    + eapply halts_evstep.
      * eapply IHfuel. exact H.
      * cbn. follow A_f_left1. finish.
  - (* wC *)
    destruct deep as [| g deep'].
    + cbn. apply death_blank.
    + destruct g; cbn in H; try discriminate.
      * eapply halts_evstep.
        { eapply IHfuel. exact H. }
        { cbn. follow C_e_probe. finish. }
      * eapply halts_evstep.
        { eapply IHfuel. exact H. }
        { cbn. follow C_a_left1. finish. }
      * eapply halts_evstep.
        { eapply IHfuel. exact H. }
        { cbn. follow C_f_left1. finish. }
  - (* wD *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; try discriminate.
    + eapply halts_evstep.
      * eapply IHfuel. exact H.
      * cbn. follow D_O_reflect. finish.
    + eapply halts_evstep.
      * eapply IHfuel. exact H.
      * cbn. follow D_e_reflect. finish.
    + eapply halts_evstep.
      * eapply IHfuel. exact H.
      * cbn. follow D_a_reflect. finish.
  - (* wCr *)
    destruct shallow as [| g sh]; [discriminate |].
    destruct g; try discriminate.
    eapply halts_evstep.
    + eapply IHfuel. exact H.
    + cbn. follow C_f_redip. finish.
  - (* wE *) discriminate.
Qed.

Definition dip_dies (W : list glyph) : bool :=
  dip_go_dies (12 * length W + 60) wF W [].

(** The fatal sweep: an anchor whose string dies halts the machine. *)
Theorem death_sweep : forall Z n,
  dip_dies (gf :: Z) = true ->
  halts tm (anchor (gf :: Z) n).
Proof.
  introv H.
  eapply halts_evstep.
  - eapply (dip_go_dies_sound _ _ _ _ _ H).
  - unfold anchor.
    follow edge_start. step.
    follow (F_es_left (S n)).
    finish.
Qed.

(** * Iterating sweeps, and the assembled halting theorems. *)

Fixpoint dip_iter (n : nat) (W : list glyph) : option (list glyph) :=
  match n with
  | O => Some W
  | S n' =>
    match dip W with
    | Some (gO :: Z') => dip_iter n' (gf :: Z')
    | _ => None
    end
  end.

Lemma dip_iter_sound : forall n Z W' m,
  dip_iter n (gf :: Z) = Some W' ->
  exists Z', W' = gf :: Z' /\ anchor (gf :: Z) m -->* anchor W' (m + n).
Proof.
  induction n; introv H.
  - injection H as <-. exists Z. split.
    + reflexivity.
    + rewrite PeanoNat.Nat.add_0_r. finish.
  - cbn [dip_iter] in H.
    destruct (dip (gf :: Z)) as [W1 |] eqn:E; [| discriminate].
    destruct W1 as [| g Z1]; [discriminate |].
    destruct g; try discriminate.
    destruct (IHn _ _ (S m) H) as (Z' & -> & Hrun).
    exists Z'. split. { reflexivity. }
    eapply evstep_trans.
    + apply progress_evstep. apply sweep_theorem. exact E.
    + replace (m + S n) with (S m + n) by lia. exact Hrun.
Qed.

(** Halting from any anchor whose orbit reaches a dying string. *)
Theorem halts_of_orbit_death : forall Z m n W',
  dip_iter n (gf :: Z) = Some W' ->
  dip_dies W' = true ->
  halts tm (anchor (gf :: Z) m).
Proof.
  introv Hiter Hdies.
  destruct (dip_iter_sound _ _ _ m Hiter) as (Z' & -> & Hrun).
  eapply halts_evstep.
  - eapply death_sweep. exact Hdies.
  - exact Hrun.
Qed.

(** Halting from the blank tape, given reachability of such an anchor.
    The two hypotheses are the remaining proof obligations for the
    Odometer: (1) is a finite computation (Compute.v + vm_compute);
    (2) needs the orbit acceleration lemmas (N ~ 19*2^279). *)
Theorem halts_c0_of : forall Z nb n W',
  c0 -[ tm ]->* anchor (gf :: Z) nb ->
  dip_iter n (gf :: Z) = Some W' ->
  dip_dies W' = true ->
  halts tm c0.
Proof.
  introv Hreach Hiter Hdies.
  eapply halts_evstep.
  - eapply halts_of_orbit_death; eassumption.
  - exact Hreach.
Qed.

(** * End-to-end validation: the width-6 toy odometer halts.

    Its entire 127-sweep orbit is computed inside Coq by vm_compute;
    the 128th sweep dies. A complete, unconditional halting proof for
    the toy — the same pipeline the real machine's proof will use. *)
Definition toy6 : list glyph :=
  [gf; gO; gO; gO; gO; gO; gO; ga; ga].

Theorem toy6_halts : forall m, halts tm (anchor toy6 m).
Proof.
  intro m.
  eapply (halts_of_orbit_death _ _ 127).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** * A bare (certificate-free) executor over ctapes.

    [cmultistep] accumulates its correctness certificate as it runs,
    which makes vm_compute over 10^5 steps impractical. [brun] computes
    pure data; soundness is proved once, by induction. *)

Definition bstep (c : Q * ctape) : option (Q * ctape) :=
  match c with
  | (q, (l, s, r)) =>
    match tm (q, s) with
    | None => None
    | Some (s', L, q') => Some (q', left (l, s', r))
    | Some (s', R, q') => Some (q', right (l, s', r))
    end
  end.

Fixpoint brun (k : nat) (c : Q * ctape) : option (Q * ctape) :=
  match k with
  | O => Some c
  | S k' =>
    match bstep c with
    | Some c' => brun k' c'
    | None => None
    end
  end.

Lemma bstep_sound : forall c c',
  bstep c = Some c' -> lift c -[ tm ]-> lift c'.
Proof.
  intros [q [[l s] r]] c' H.
  unfold bstep in H.
  destruct (tm (q, s)) as [[[s' []] q'] |] eqn:E; cbn in H;
    try discriminate; injection H as <-; unfold lift.
  - rewrite lift_left. cbn [lift_tape]. apply step_left. exact E.
  - rewrite lift_right. cbn [lift_tape]. apply step_right. exact E.
Qed.

Lemma brun_sound : forall k c c',
  brun k c = Some c' -> lift c -[ tm ]->* lift c'.
Proof.
  induction k; introv H.
  - cbn in H. injection H as <-. finish.
  - cbn in H.
    destruct (bstep c) as [c1 |] eqn:E; [| discriminate].
    eapply evstep_step.
    + apply bstep_sound. exact E.
    + eapply IHk. exact H.
Qed.
