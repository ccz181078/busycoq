(** * TM: Definition of Turing Machines *)

From Coq Require Import Bool.Sumbool.
From Coq Require Import Lists.List. Export ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From BusyCoq Require Export Helper.
From BusyCoq Require Import HashTable.
Set Default Goal Selector "!".

(** The direction a Turing machine can step in. *)
Inductive dir : Type := L | R.

(** We parametrize over... *)
Module Type Ctx.
  (** the type of states [Q]; *)
  Parameter Q : Type.
  (** the type of tape symbols [Sym]; *)
  Parameter Sym : Type.
  (** the starting state [q0]; *)
  Parameter q0 : Q.
  (** and the blank symbol [s0]. *)
  Parameter s0 : Sym.

  (** during enumeration, we also want: *)
  (** distinguished non-starting state *)
  Parameter q1 : Q.
  Parameter q0_neq_q1 : q0 <> q1.

  (** distinguished non-blank symbol *)
  Parameter s1 : Sym.
  Parameter s0_neq_s1 : s0 <> s1.

  (** Moreover we want decidable equality for [Q] and [Sym]. *)
  Parameter eqb_q : forall (a b : Q), {a = b} + {a <> b}.
  Parameter eqb_sym : forall (a b : Sym), {a = b} + {a <> b}.

  Parameter q_eqb : Q->Q->bool.
  Parameter sym_eqb : Sym->Sym->bool.
  Parameter q_eqb_spec : forall a b:Q, Bool.reflect (a=b) (q_eqb a b).
  Parameter sym_eqb_spec : forall a b:Sym, Bool.reflect (a=b) (sym_eqb a b).
  Parameter q_hash : Q->HashConcat.hash_t.
  Parameter sym_hash : Sym->HashConcat.hash_t.

  (** It is also useful, in some situations, to be able to enumerate
      all the symbols and states. *)
  Parameter all_qs : list Q.
  Parameter all_qs_spec : forall a, In a all_qs.
  Parameter all_syms : list Sym.
  Parameter all_syms_spec : forall a, In a all_syms.
End Ctx.

Module TM (Ctx : Ctx).
  Export Ctx.

#[export] Hint Resolve all_qs_spec all_syms_spec : core.

(** A Turing machine is a function mapping each [(state, symbol)] pair
    to one of

    - [None], in which case the machine halts;
    - [Some (s, d, q)], in which case the machine writes [s] on the tape,
      moves in the direction specified by [d], and transitions to state [q].

*)
Definition TM : Type := Q * Sym -> option (Sym * dir * Q).

Notation side := (Stream Sym).

(** The state of the tape is represented abstractly as a tuple [(l, s, r)],
    where [v] is the symbol under the head, while [l] and [r] are infinite
    streams of symbols on the left and right side of the head, respectively. *)
Notation tape := (side * Sym * side)%type.

(** We define a notation for tapes, evocative of a turing machine's head
    hovering over a particular symbol. **)
Notation "l {{ s }} r" := (l, s, r)
  (at level 30, s at next level, only parsing).

Local Example tape_ex (a b c d e : Sym) : tape :=
  const s0 << a << b {{c}} d >> e >> const s0.

(** Helper functions for moving the tape head: *)
Definition move_left (t : tape) : tape :=
  match t with
  | l {{s}} r => tl l {{hd l}} s >> r
  end.

Definition move_right (t : tape) : tape :=
  match t with
  | l {{s}} r => l << s {{hd r}} tl r
  end.

(** Notation for the configuration of a machine. Note that the position
    of the head within the tape is implicit, since the tape is centered
    at the head. *)
Notation "q ;; t" := (q, t) (at level 35, only parsing).

(** For the directed head formulation, we use the following: *)
Notation "l <{{ q }} r" := (q;; tl l {{hd l}} r)  (at level 30, q at next level).
Notation "l {{ q }}> r" := (q;; l {{hd r}} tl r)  (at level 30, q at next level).

(** The small-step semantics of Turing machines: *)
Reserved Notation "c -[ tm ]-> c'" (at level 40).

Inductive step (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | step_left q q' s s' l r :
    tm (q, s) = Some (s', L, q') ->
    q;; l {{s}} r -[ tm ]-> q';; (move_left (l {{s'}} r))
  | step_right q q' s s' l r :
    tm (q, s) = Some (s', R, q') ->
    q;; l {{s}} r -[ tm ]-> q';; (move_right (l {{s'}} r))

  where "c -[ tm ]-> c'" := (step tm c c').

Arguments step_left {tm q q' s s' l r}.
Arguments step_right {tm q q' s s' l r}.

#[export] Hint Constructors step : core.

(** If we have an assumption of the form [tm (q, s) = Some (s', d, q')],
   perform case analysis on [d]. *)
Ltac destruct_dir tm q s :=
  lazymatch goal with
  | H: tm (q, s) = Some (?s', ?d, ?q') |- _ =>
    lazymatch d with
    | L => fail
    | R => fail
    | _ => destruct d
    end
  end.

Local Hint Extern 1 =>
  match goal with
  | |- context [?q;; _ {{?s}} _ -[ ?tm ]-> _] => destruct_dir tm q s
  end : core.

(** Executing a specified number of steps: *)
Reserved Notation "c -[ tm ]->> n / c'" (at level 40, n at next level).

Inductive multistep (tm : TM) : nat -> Q * tape -> Q * tape -> Prop :=
  | multistep_0 c : c -[ tm ]->> 0 / c
  | multistep_S n c c' c'' :
    c  -[ tm ]->  c' ->
    c' -[ tm ]->> n / c'' ->
    c  -[ tm ]->> S n / c''

  where "c -[ tm ]->> n / c'" := (multistep tm n c c').

#[export] Hint Constructors multistep : core.

Local Hint Extern 1 =>
  lazymatch goal with
  | H: _ -[ _ ]->> S _ / _ |- _ => inverts H
  | H: _ -[ _ ]->> O / _ |- _ => inverts H
  end : core.

(** Executing an unspecified number of steps (the "eventually
    reaches" relation): *)
Reserved Notation "c -[ tm ]->* c'" (at level 40).

Inductive evstep (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | evstep_refl c : c -[ tm ]->* c
  | evstep_step c c' c'' :
    c  -[ tm ]->  c'  ->
    c' -[ tm ]->* c'' ->
    c  -[ tm ]->* c''

  where "c -[ tm ]->* c'" := (evstep tm c c').

#[export] Hint Constructors evstep : core.

(** Executing an unspecified, but non-zero number of steps: *)
Reserved Notation "c -[ tm ]->+ c'" (at level 40).

Inductive progress (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | progress_base c c' :
    c -[ tm ]->  c' ->
    c -[ tm ]->+ c'
  | progress_step c c' c'' :
    c  -[ tm ]->  c'  ->
    c' -[ tm ]->+ c'' ->
    c  -[ tm ]->+ c''

  where "c -[ tm ]->+ c'" := (progress tm c c').

Arguments progress_base {tm c c'}.
Arguments progress_step {tm c c' c''}.

#[export] Hint Constructors progress : core.

(* alternative definition for [progress] *)
Lemma progress_intro : forall tm c c' c'',
  c  -[ tm ]->  c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. generalize dependent c. induction H2; eauto.
Qed.

(** The Turing machine has halted if [tm (q, s)] returns [None]. *)
Definition halted (tm : TM) (c : Q * tape) : Prop :=
  match c with
  | (q, l {{s}} r) => tm (q, s) = None
  end.

(** The initial configuration of the machine *)
Definition tape0 : tape := const s0 {{s0}} const s0.
Definition c0 : Q * tape := q0;; tape0.

(** A Turing machine halts if it eventually reaches a halting configuration. *)
Definition halts_in (tm : TM) (c : Q * tape) (n : nat) :=
  exists ch, c -[ tm ]->> n / ch /\ halted tm ch.

Definition halts (tm : TM) (c0 : Q * tape) :=
  exists n, halts_in tm c0 n.

#[export] Hint Unfold halts halts_in : core.

Inductive halts_at: TM->Q*tape->nat->Q*Sym->Prop :=
| halts_at_intro tm c n q l m r:
  c -[ tm ]->> n / (q,(l,m,r)) ->
  halted tm (q,(l,m,r)) ->
  halts_at tm c n (q,m).

Definition halts_at_trans tm c1 tr := exists n, halts_at tm c1 n tr.

Inductive DecideResult :=
| Halt(h:Q*Sym)
| NonHalt
| Unknown
.

Lemma move_left_tape0 :
  move_left tape0 = tape0.
Proof.
  unfold tape0, move_left.
  rewrite <- const_unfold.
  reflexivity.
Qed.

Lemma move_right_tape0 :
  move_right tape0 = tape0.
Proof.
  unfold tape0, move_right.
  rewrite <- const_unfold.
  reflexivity.
Qed.

#[export] Hint Rewrite move_left_tape0 move_right_tape0 : tape.

(** We prove that the "syntactic" notion of [halted] corresponds
    to the behavior of [step]. *)
Lemma halted_no_step : forall tm c c',
  halted tm c ->
  ~ c -[ tm ]-> c'.
Proof.
  introv Hhalted Hstep.
  inverts Hstep; congruence.
Qed.

Lemma no_halted_step : forall tm c,
  ~ halted tm c ->
  exists c',
  c -[ tm ]-> c'.
Proof.
  introv Hhalted.
  destruct c as [q [[l s] r]].
  destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E.
  - (* tm (q, s) = Some (s', d, q') *)
    eauto 6.
  - (* tm (q, s) = None *)
    congruence.
Qed.

(** Other useful lemmas: *)
Lemma step_deterministic : forall tm c c' c'',
  c -[ tm ]-> c'  ->
  c -[ tm ]-> c'' ->
  c' = c''.
Proof.
  introv H1 H2.
  inverts H1; inverts H2; congruence.
Qed.

Ltac step_deterministic :=
  lazymatch goal with
  | H1: ?c -[ ?tm ]-> ?c',
    H2: ?c -[ ?tm ]-> ?c''
    |- _ =>
    pose proof (step_deterministic tm c c' c'' H1 H2); subst c''; clear H2
  end.

Local Hint Extern 1 => step_deterministic : core.

Lemma multistep_trans : forall tm n m c c' c'',
  c  -[ tm ]->> n / c' ->
  c' -[ tm ]->> m / c'' ->
  c  -[ tm ]->> (n + m) / c''.
Proof.
  introv H1 H2.
  induction H1; simpl; eauto.
Qed.

Lemma multistep_deterministic : forall tm n c c' c'',
  c -[ tm ]->> n / c'  ->
  c -[ tm ]->> n / c'' ->
  c' = c''.
Proof.
  introv H1 H2.
  induction H1; inverts H2; auto.
Qed.

Ltac multistep_deterministic :=
  lazymatch goal with
  | H1: ?c -[ ?tm ]->> ?n / ?c',
    H2: ?c -[ ?tm ]->> ?n / ?c''
    |- _ =>
    pose proof (multistep_deterministic tm n c c' c'' H1 H2); subst c''; clear H2
  end.

Local Hint Extern 1 => multistep_deterministic : core.

Ltac deterministic := repeat (step_deterministic || multistep_deterministic).

Lemma multistep_last : forall tm n c c'',
  c -[ tm ]->> S n / c'' ->
  exists c', c -[ tm ]->> n / c' /\ c' -[ tm ]-> c''.
Proof.
  induction n; introv H; inverts H as H1 H2.
  - eauto.
  - apply IHn in H2. destruct H2 as [cmid [H2 H3]].
    eauto.
Qed.

Lemma evstep_one : forall {tm c c'},
  c -[ tm ]->  c' ->
  c -[ tm ]->* c'.
Proof. eauto. Qed.

Lemma evstep_trans : forall tm c c' c'',
  c  -[ tm ]->* c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->* c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma halts_in_S : forall tm c c' n,
  halts_in tm c' n ->
  c -[ tm ]-> c' ->
  halts_in tm c (S n).
Proof.
  introv Hhalts Hstep.
  destruct Hhalts as [ch [Hrun Hhalted]].
  eauto.
Qed.

#[export] Hint Resolve halts_in_S : core.

Lemma halts_step : forall tm c c',
  halts tm c' ->
  c -[ tm ]-> c' ->
  halts tm c.
Proof.
  introv H Hstep. destruct H. eauto.
Qed.

#[export] Hint Resolve halts_step : core.

Lemma halts_multistep : forall tm c c' n,
  halts tm c' ->
  c -[ tm ]->> n / c' ->
  halts tm c.
Proof.
  introv Hhalts Hsteps.
  induction Hsteps; eauto.
Qed.

#[export] Hint Resolve halts_multistep : core.

Lemma halted_halts :
  forall tm c,
  halted tm c ->
  halts tm c.
Proof. eauto 6. Qed.

#[export] Hint Immediate halted_halts : core.

Lemma progress_trans :
  forall tm c c' c'',
  c  -[ tm ]->+ c'  ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma multistep_progress :
  forall tm n c c',
  c -[ tm ]->> S n / c' ->
  c -[ tm ]->+ c'.
Proof.
  induction n; introv H; inverts H; eauto.
Qed.

#[export] Hint Resolve multistep_progress : core.

Lemma progress_multistep :
  forall tm c c',
  c -[ tm ]->+ c' ->
  exists n,
  c -[ tm ]->> S n / c'.
Proof.
  introv H. induction H.
  - eauto.
  - destruct IHprogress as [n IH].
    eauto.
Qed.

Lemma without_counter :
  forall tm n c c',
  c -[ tm ]->> n / c' ->
  c -[ tm ]->* c'.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma with_counter :
  forall {tm c c'},
  c -[ tm ]->* c' ->
  exists n, c -[ tm ]->> n / c'.
Proof.
  introv H. induction H.
  - eauto.
  - destruct IHevstep as [n IH].
    eauto.
Qed.

Lemma evstep_progress :
  forall tm c c',
  c -[ tm ]->* c' ->
  c <> c' ->
  c -[ tm ]->+ c'.
Proof.
  introv Hrun Hneq.
  apply with_counter in Hrun.
  destruct Hrun as [[| n] Hrun].
  - inverts Hrun. contradiction.
  - eauto.
Qed.

Lemma progress_evstep :
  forall tm c c',
  c -[ tm ]->+ c' ->
  c -[ tm ]->* c'.
Proof.
  introv H.
  apply progress_multistep in H. destruct H.
  eauto using without_counter.
Qed.

Lemma evstep_progress_trans :
  forall tm c c' c'',
  c  -[ tm ]->* c'  ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma progress_evstep_trans :
  forall tm c c' c'',
  c  -[ tm ]->+ c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1.
  - apply with_counter in H2.
    destruct H2 as [[| n] H2]; eauto.
  - eauto.
Qed.

Lemma rewind_split:
  forall tm n k c c'',
  c -[ tm ]->> (n + k) / c'' ->
  exists c', c -[ tm ]->> n / c' /\ c' -[ tm ]->> k / c''.
Proof.
  intros tm n k.
  induction n; intros c c'' H.
  - eauto.
  - inverts H as Hstep Hrest.
    apply IHn in Hrest. clear IHn.
    destruct Hrest as [cn [Hn Hk]].
    eauto.
Qed.

(** When using [rewind_split], it is often more convenient to have the arithmetic
    show up as a separate goal, to be easily discharged with [lia]. *)
Lemma rewind_split':
  forall k1 k2 tm n c c'',
  c -[ tm ]->> n / c'' ->
  n = k1 + k2 ->
  exists c', c -[ tm ]->> k1 / c' /\ c' -[ tm ]->> k2 / c''.
Proof.
  introv H E. subst n. apply rewind_split; assumption.
Qed.

Lemma halted_no_multistep:
  forall tm c c' n,
  n > 0 ->
  halted tm c ->
  ~ c -[ tm ]->> n / c'.
Proof.
  introv Hgt0 Hhalted Hrun.
  inverts Hrun as Hstep Hrest.
  - inverts Hgt0.
  - eapply halted_no_step in Hhalted. eauto.
Qed.

Lemma exceeds_halt : forall tm c c' n k,
  halts_in tm c k ->
  n > k ->
  c -[ tm ]->> n / c' ->
  False.
Proof.
  introv [ch [Hch Hhalted]] Hnk Hexec.
  eapply (rewind_split' k (n - k)) in Hexec; try lia.
  destruct Hexec as [ch' [H1 H2]].
  deterministic.
  eapply halted_no_multistep in Hhalted.
  - eauto.
  - lia.
Qed.

Corollary within_halt : forall tm c c' k n,
  halts_in tm c n ->
  c -[ tm ]->> k / c' ->
  k <= n.
Proof.
  introv Hhalts Hrun.
  destruct (Nat.leb_spec k n); try assumption.
  exfalso. eauto using exceeds_halt.
Qed.

Lemma preceeds_halt : forall tm c c' n k,
  halts_in tm c k ->
  c -[ tm ]->> n / c' ->
  n <= k ->
  halts_in tm c' (k - n).
Proof.
  introv Hhalt Hexec Hle.
  destruct Hhalt as [ch [Hrunch Hhalted]].
  apply (rewind_split' n (k - n)) in Hrunch; try lia.
  destruct Hrunch as [cm [H1 H2]].
  deterministic.
  eauto.
Qed.

Lemma skip_halts: forall tm c c' n,
  c -[ tm ]->> n / c' ->
  ~ halts tm c' ->
  ~ halts tm c.
Proof.
  introv Hexec Hnonhalt [k Hhalt].
  destruct (Nat.ltb_spec k n).
  - eauto using exceeds_halt.
  - eauto using preceeds_halt.
Qed.

Corollary multistep_nonhalt : forall tm c c',
  c -[ tm ]->* c' ->
  ~ halts tm c' ->
  ~ halts tm c.
Proof.
  introv Hexec Hnonhalt.
  destruct (with_counter Hexec) as [n Hexec'].
  eauto using skip_halts.
Qed.

Lemma progress_nonhalt' : forall tm (P : Q * tape -> Prop),
  (forall c, P c -> exists c', P c' /\ c -[ tm ]->+ c') ->
  forall k c, P c -> ~ halts_in tm c k.
Proof.
  introv Hstep.
  induction k using strong_induction.
  introv H0 Hhalts.
  apply Hstep in H0. destruct H0 as [c' [HP Hrun]].
  apply progress_multistep in Hrun. destruct Hrun as [n Hrun].
  destruct (Nat.leb_spec (S n) k).
  - assert (Hhalts' : halts_in tm c' (k - S n))
      by eauto using preceeds_halt.
    enough (Hnhalts : ~ halts_in tm c' (k - S n)) by contradiction.
    apply H; intuition lia.
  - eauto using exceeds_halt.
Qed.

Lemma progress_nonhalt : forall tm (P : Q * tape -> Prop) c,
  (forall c, P c -> exists c', P c' /\ c -[ tm ]->+ c') ->
  P c ->
  ~ halts tm c.
Proof.
  introv Hstep H0 Hhalts.
  destruct Hhalts as [k Hhalts].
  enough (Hnhalts : ~ halts_in tm c k) by contradiction.
  eauto using progress_nonhalt'.
Qed.

Corollary progress_nonhalt_simple : forall tm (A : Type) (C : A -> Q * tape) i0,
  (forall i, exists i', C i -[ tm ]->+ C i') ->
  ~ halts tm (C i0).
Proof with eauto.
  introv Hstep.
  apply progress_nonhalt with (P := fun c => exists i, c = C i)...
  - introv [i Hi]. subst c.
    destruct (Hstep i) as [i' Hi']...
Qed.

Corollary progress_nonhalt_cond : forall tm (A : Type) (i0 : A)
  (C : A -> Q * tape) (P : A -> Prop),
  (forall i, P i -> exists i', C i -[ tm ]->+ C i' /\ P i') ->
  P i0 ->
  ~ halts tm (C i0).
Proof with eauto.
  introv Hstep Hi0.
  apply progress_nonhalt with (P := fun c => exists i, c = C i /\ P i)...
  - introv [i [E HP]]. subst c.
    destruct (Hstep i HP) as [i' [Hi' HP']]...
Qed.

Lemma nonhalt_iff {tm c}:
  ~halts tm c <->
  forall n, exists c', c -[ tm ]->> n / c'.
Proof.
  split; intros H.
  - unfold halts,halts_in in H.
    intros n.
    induction n.
    + exists c. constructor.
    + destruct IHn as [c' IHn].
      epose proof (no_halted_step tm c' _) as H0.
      destruct H0 as [c'0 H0].
      eexists.
      replace (S n) with (n+1) by lia.
      eapply multistep_trans; eauto.
      Unshelve.
      intros H0.
      apply H.
      exists n c'; tauto.
  - intros H0.
    destruct H0 as [n H0].
    specialize (H (n+1)).
    destruct H as [c' H].
    eapply exceeds_halt.
    1: apply H0.
    2: apply H.
    lia.
Qed.

Definition step_c(tm:TM)(c:Q*tape):option (Q*tape) :=
let '(q,(l,m,r)):=c in
match tm (q,m) with
| None => None
| Some (m',L,q') => Some (q',move_left (l,m',r))
| Some (m',R,q') => Some (q',move_right (l,m',r))
end.

Fixpoint multistep_c(tm:TM)(n:nat)(c:Q*tape) :=
match n with
| O => Some c
| S n =>
  match step_c tm c with
  | Some c =>multistep_c tm n c
  | None => None
  end
end.

Definition halts_in' tm c n :=
exists ch, multistep_c tm n c = Some ch /\ halted tm ch.

Definition halts' tm c :=
exists n, halts_in' tm c n.

Lemma step_c_spec tm c c':
  step_c tm c = Some c' <->
  c -[ tm ]-> c'.
Proof.
  split; intros H.
  - destruct c as [q [[l m] r]].
    cbn in H.
    destruct (tm (q,m)) as [[[m' d] q']|] eqn:E.
    2: congruence.
    destruct d; inverts H; constructor; auto.
  - inverts H;
    cbn; rewrite H0; reflexivity.
Qed.

Lemma multistep_c_spec tm n c c':
  multistep_c tm n c = Some c' <->
  c -[ tm ]->> n / c'.
Proof.
  gen c c'.
  induction n; intros.
  - split; intros H; inverts H; constructor.
  - split; intros H.
    + cbn in H.
      destruct (step_c tm c) eqn:E; try congruence.
      rewrite step_c_spec in E.
      rewrite IHn in H.
      eauto.
    + inverts H. cbn.
      rewrite <-step_c_spec in H1.
      rewrite H1,IHn.
      assumption.
Qed.

Lemma halts_in_halts_in' {tm c n}:
  halts_in tm c n <-> halts_in' tm c n.
Proof.
  unfold halts_in,halts_in'.
  split; intros [ch [H H0]]; exists ch; (split;[|tauto]).
  - rewrite multistep_c_spec.
    apply H.
  - rewrite <-multistep_c_spec.
    apply H.
Qed.

Lemma halts_halts' {tm c}:
  halts tm c <-> halts' tm c.
Proof.
  unfold halts,halts'.
  split; intros [n H]; exists n.
  - rewrite <-halts_in_halts_in'.
    apply H.
  - rewrite halts_in_halts_in'.
    apply H.
Qed.

Lemma evstep_multistep tm c c':
  c -[ tm ]->* c' ->
  exists n, c -[ tm ]->> n / c'.
Proof.
  intro H.
  induction H.
  - exists O.
    constructor.
  - destruct IHevstep as [n IH].
    exists (S n).
    econstructor; eauto.
Qed.

Lemma halts_evstep tm c c':
  halts tm c' ->
  c -[ tm ]->* c' -> halts tm c.
Proof.
  intros H H0.
  destruct (evstep_multistep _ _ _ H0) as [n H1].
  eapply halts_multistep; eauto.
Qed.


Definition sigma_score_sym: Sym->nat :=
  fun s =>
  (if sym_eqb s s0 then 0 else 1)%nat.

Fixpoint sigma_score_seg(ls:list Sym):nat :=
match ls with
| nil => 0
| h::t => sigma_score_sym h + sigma_score_seg t
end.

Inductive sigma_score_side: side->nat->Prop :=
| sigma_score_side_O:
    sigma_score_side (const s0) 0
| sigma_score_side_S h t n1 n2:
    sigma_score_sym h = n1 ->
    sigma_score_side t n2 ->
    sigma_score_side (h>>t) (n1+n2).

Inductive sigma_score: (Q*tape)->nat->Prop :=
| sigma_score_intro q l m r n1 n2 n3:
    sigma_score_side l n1 ->
    sigma_score_sym m = n2 ->
    sigma_score_side r n3 ->
    sigma_score (q,(l,m,r)) (n1+n2+n3).

Lemma sigma_score_s0:
  sigma_score_sym s0 = O.
Proof.
  unfold sigma_score_sym.
  destruct (sym_eqb_spec s0 s0); congruence.
Qed.

Lemma sigma_score_side_const0_0 n:
  sigma_score_side (const s0) n ->
  n = O.
Proof.
  intro H.
  remember (const s0) as s1.
  induction H.
  1: reflexivity.
  rewrite const_unfold in Heqs1.
  inverts Heqs1.
  rewrite IHsigma_score_side.
  2: reflexivity.
  rewrite <-H.
  rewrite sigma_score_s0.
  reflexivity.
Qed.

Lemma sigma_score_side_unique s1 n1 n2:
  sigma_score_side s1 n1 ->
  sigma_score_side s1 n2 ->
  n1 = n2.
Proof.
  intro H1.
  gen n2.
  induction H1; intros.
  - rewrite sigma_score_side_const0_0; auto.
  - inverts H0.
    + rewrite const_unfold in H3.
      inverts H3.
      rewrite <-H.
      rewrite sigma_score_s0.
      rewrite (sigma_score_side_const0_0 n2); auto.
    + rewrite  <-(IHsigma_score_side _ H6).
      congruence.
Qed.

Lemma sigma_score_unique c1 n1 n2:
  sigma_score c1 n1 ->
  sigma_score c1 n2 ->
  n1 = n2.
Proof.
  intros H1 H2.
  inverts H1.
  inverts H2.
  f_equal.
  2: eapply sigma_score_side_unique; eauto.
  f_equal.
  1: eapply sigma_score_side_unique; eauto.
Qed.

Lemma sigma_score_sym_bounded m:
  (0 <= sigma_score_sym m <= 1)%nat.
Proof.
  unfold sigma_score_sym.
  destruct (sym_eqb m s0); lia.
Qed.

Lemma sigma_score_step_bounded tm c1 c2 n1:
  c1 -[ tm ]-> c2 ->
  sigma_score c1 n1 ->
  exists n2,
  sigma_score c2 n2 /\
  n2 <= n1+1.
Proof.
  intros H H1.
  inverts H1.
  inverts H.
  - inverts H0.
    + cbn.
      eexists. split.
      1: econstructor.
      1: constructor.
      1: reflexivity.
      1: econstructor; eauto.
      cbn.
      pose proof (sigma_score_sym_bounded s').
      rewrite sigma_score_s0.
      lia.
    + cbn.
      eexists. split.
      1: econstructor; eauto.
      1: econstructor; eauto.
      cbn.
      pose proof (sigma_score_sym_bounded s').
      lia.
  - inverts H3.
    + cbn.
      eexists. split.
      1: econstructor.
      1: econstructor; eauto.
      1: reflexivity.
      1: econstructor.
      cbn.
      pose proof (sigma_score_sym_bounded s').
      rewrite sigma_score_s0.
      lia.
    + cbn.
      eexists. split.
      1: econstructor; eauto.
      1: econstructor; eauto.
      cbn.
      pose proof (sigma_score_sym_bounded s').
      lia.
Qed.

Lemma sigma_score_bounded tm c1 c2 n n1 n2:
  c1 -[ tm ]->> n / c2 ->
  sigma_score c1 n1 ->
  sigma_score c2 n2 ->
  n2 <= n1+n.
Proof.
  intro H.
  gen n1 n2.
  induction H; intros.
  - replace n2 with n1 by (eapply sigma_score_unique; eauto).
    lia.
  - epose proof (sigma_score_step_bounded _ _ _ _ H H1) as [n' [Ha Hb]].
    specialize (IHmultistep _ _ Ha H2).
    lia.
Qed.

Lemma sigma_score_bounded_fromc0 tm c2 n n2:
  c0 -[ tm ]->> n / c2 ->
  sigma_score c2 n2 ->
  n2 <= n.
Proof.
  intros H H0.
  eapply sigma_score_bounded with (c1:=c0) (n1:=O); eauto.
  change O with (O+O+O).
  econstructor.
  1,3: econstructor.
  apply sigma_score_s0.
Qed.

Lemma sigma_score_unbounded_nonhalt tm:
  (forall n, exists c1 n', c0 -[ tm ]->* c1 /\ sigma_score c1 n' /\ n<=n') ->
  ~halts tm c0.
Proof.
  intros h [n [c1 [Hm Hh]]].
  destruct (h (S n)) as [c1' [n' [He' [Hs Hle]]]].
  epose proof (evstep_multistep _ _ _ He') as [n'' Hm'].
  epose proof (sigma_score_bounded_fromc0 _ _ _ _ Hm' Hs).
  eapply exceeds_halt with (k:=n).
  3: apply Hm'.
  2: lia.
  eauto.
Qed.

Lemma sigma_score_Str_app a b n1 n2:
  sigma_score_seg a = n1 ->
  sigma_score_side b n2 ->
  sigma_score_side (a *> b) (n1 + n2).
Proof.
  gen b n1 n2.
  induction a; intros.
  - cbn in H.
    rewrite <-H.
    apply H0.
  - cbn.
    cbn in H.
    rewrite <-H.
    rewrite <-Nat.add_assoc.
    econstructor; eauto.
Qed.

Lemma sigma_score_app a b:
  sigma_score_seg (a++b) =
  sigma_score_seg a + sigma_score_seg b.
Proof.
  induction a.
  1: reflexivity.
  cbn.
  lia.
Qed.

Lemma sigma_score_lpow a n n1:
  sigma_score_seg a = n1 ->
  sigma_score_seg (a^^n) = n1*n.
Proof.
  gen a n1.
  induction n; intros.
  1: cbn; lia.
  cbn.
  rewrite sigma_score_app,H.
  erewrite IHn; eauto.
  lia.
Qed.

Lemma sigma_score_headL q a b n1 n2:
  sigma_score_side a n1 ->
  sigma_score_side b n2 ->
  sigma_score (a <{{ q }} b) (n1+n2).
Proof.
  intros.
  inverts H.
  - cbn.
    replace n2 with (O+O+n2) by lia.
    econstructor; eauto.
    2: apply sigma_score_s0.
    constructor.
  - cbn.
    rewrite (Nat.add_comm _ n3).
    econstructor; eauto.
Qed.

Lemma sigma_score_headR q a b n1 n2:
  sigma_score_side a n1 ->
  sigma_score_side b n2 ->
  sigma_score (a {{ q }}> b) (n1+n2).
Proof.
  intros.
  inverts H0.
  - cbn.
    replace n1 with (n1+(O+O)) by lia.
    econstructor; eauto.
    1: apply sigma_score_s0.
    constructor.
  - cbn.
    rewrite (Nat.add_assoc).
    econstructor; eauto.
Qed.

Ltac solve_sigma_score :=
  (apply sigma_score_headL ||
  apply sigma_score_headR ||
  apply sigma_score_intro);
  repeat (
  apply sigma_score_side_O ||
  apply sigma_score_lpow ||
  apply sigma_score_Str_app ||
  (cbn; reflexivity)
  ).



#[export] Instance Q_Eqb:
  Eqb Q.
Proof.
  esplit; intros.
  eapply q_eqb_spec.
Defined.

#[export] Instance Sym_Eqb:
  Eqb Sym.
Proof.
  esplit; intros.
  eapply sym_eqb_spec.
Defined.

Import HashConcat.
#[export] Instance Q_Hash: Hash Q := (ltac:(split; apply q_hash)).
#[export] Instance Sym_Hash: Hash Sym := (ltac:(split; apply sym_hash)).
End TM.

Definition dir_rev(sgn:dir):=
match sgn with
| L => R
| R => L
end.

Definition dir_eqb(d1 d2:dir) :=
match d1,d2 with
| L,L | R,R => true
| _,_ => false
end.

Lemma dir_eqb_spec d1 d2: Bool.reflect (d1=d2) (dir_eqb d1 d2).
Proof.
  destruct d1,d2; solve_Bool_reflect.
Qed.

#[export] Instance dir_Eqb: Eqb dir := Build_Eqb _ dir_eqb dir_eqb_spec.

Definition dir_hash(x:dir) :=
match x with
| L => HashConcat.hv1
| R => HashConcat.hv2
end.

#[export] Instance dir_Hash: HashConcat.Hash dir := HashConcat.Build_Hash _ dir_hash.

