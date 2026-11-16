From Coq Require Import Bool.
From Coq Require Import Lists.List. Export ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import NArith.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From BusyCoq Require Export TM.
From BusyCoq Require Import HashTable.

Module Type Ctx.
  (** the type of states [Q]; *)
  Parameter Q : Type.
  (** the type of tape symbols [Sym]; *)
  Parameter Sym : Type.
  (** the starting state [q0]; *)
  Parameter q0 : Q.
  (** and the blank symbol [s0]. *)
  Parameter s0 : Sym.

  Parameter q_eqb : Q->Q->bool.
  Parameter sym_eqb : Sym->Sym->bool.
  Parameter q_eqb_spec : forall a b:Q, Bool.reflect (a=b) (q_eqb a b).
  Parameter sym_eqb_spec : forall a b:Sym, Bool.reflect (a=b) (sym_eqb a b).
  Parameter q_hash : Q->HashConcat.hash_t.
  Parameter sym_hash : Sym->HashConcat.hash_t.
End Ctx.

Module QHash(Ctx:Ctx) <: HashableType.
Import Ctx.
Definition K := Q.
Definition K_eq := q_eqb.
Definition K_eq_spec := q_eqb_spec.
Definition K_hash := q_hash.
End QHash.

Module SymHash(Ctx:Ctx) <: HashableType.
Import Ctx.
Definition K := Sym.
Definition K_eq := sym_eqb.
Definition K_eq_spec := sym_eqb_spec.
Definition K_hash := sym_hash.
End SymHash.


Module DHTM (Ctx : Ctx).
  Export Ctx.

Definition TM : Type := Q * Sym -> option (Sym * dir * Q).

Notation side := (Stream Sym).
Notation DH_config := (side * side * Q * dir)%type.

Reserved Notation "c -[ tm ]-> c'" (at level 40).

Inductive step (tm:TM): DH_config->DH_config->Prop :=
| step_through l m m' r s s' sgn:
  tm (s,m) = Some (m',sgn,s') ->
  step tm (l,m >> r,s,sgn) (m' >> l,r,s',sgn)
| step_back l m m' r s s' sgn:
  tm (s,m) = Some (m',dir_rev sgn,s') ->
  step tm (l,m >> r,s,sgn) (m' >> r,l,s',dir_rev sgn)
  where "c -[ tm ]-> c'" := (step tm c c').

#[export] Hint Constructors step : core.


Reserved Notation "c -[ tm ]->> n / c'" (at level 40, n at next level).

Inductive multistep (tm : TM) : nat -> DH_config -> DH_config -> Prop :=
  | multistep_0 c : c -[ tm ]->> 0 / c
  | multistep_S n c c' c'' :
    c  -[ tm ]->  c' ->
    c' -[ tm ]->> n / c'' ->
    c  -[ tm ]->> S n / c''

  where "c -[ tm ]->> n / c'" := (multistep tm n c c').

#[export] Hint Constructors multistep : core.


Reserved Notation "c -[ tm ]->* c'" (at level 40).

Inductive evstep (tm : TM) : DH_config -> DH_config -> Prop :=
  | evstep_refl c : c -[ tm ]->* c
  | evstep_step c c' c'' :
    c  -[ tm ]->  c'  ->
    c' -[ tm ]->* c'' ->
    c  -[ tm ]->* c''

  where "c -[ tm ]->* c'" := (evstep tm c c').

#[export] Hint Constructors evstep : core.


Reserved Notation "c -[ tm ]->+ c'" (at level 40).

Inductive progress (tm : TM) : DH_config -> DH_config -> Prop :=
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


Definition halted (tm : TM) (c : DH_config) : Prop :=
  match c with
  | (l,m >> r,s,sgn) => tm (s,m) = None
  end.

Definition halts_in (tm : TM) (c : DH_config) (n : nat) :=
  exists ch, c -[ tm ]->> n / ch /\ halted tm ch.

Definition halts (tm : TM) (c0 : DH_config) :=
  exists n, halts_in tm c0 n.

Definition c0 : DH_config := (const s0,const s0,q0,R).

Lemma step_nonhalt : forall tm (P : DH_config -> Prop) c,
  (forall c, P c -> exists c', P c' /\ c -[ tm ]-> c') ->
  P c ->
  ~ halts tm c.
Proof.
  introv Hstep H0 Hhalts.
  destruct Hhalts as [k [c' [H1 H2]]].
  gen c.
  induction k; intros c Hc.
  - destruct (Hstep c Hc) as [c1 [Hc1 Hs]].
    unfold halted in H2.
    intros Hc'.
    inverts Hc'.
    inverts Hs; congruence.
  - destruct (Hstep c Hc) as [c1 [Hc1 Hs]].
    intros HS.
    inverts HS.
    unshelve eapply (IHk _ _ H1).
    inverts Hs; inverts H0; try congruence.
    + destruct sgn; cbn in H9; congruence.
    + destruct sgn; cbn in H; congruence.
Qed.


Lemma evstep_trans : forall tm c c' c'',
  c  -[ tm ]->* c' ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->* c''.
Proof.
  introv H1 H2.
  induction H1; simpl; eauto.
Qed.

Lemma progress_trans : forall tm c c' c'',
  c  -[ tm ]->+ c' ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2.
  induction H1; simpl; eauto.
Qed.

Lemma evstep_progress_trans : forall tm c c' c'',
  c  -[ tm ]->* c' ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2.
  induction H1; simpl; eauto.
Qed.

Lemma progress_evstep : forall tm c c',
  c -[ tm ]->+ c' ->
  c -[ tm ]->* c'.
Proof.
  introv H.
  induction H; simpl; eauto.
Qed.

Lemma multistep_trans : forall tm n m c c' c'',
  c  -[ tm ]->> n / c' ->
  c' -[ tm ]->> m / c'' ->
  c  -[ tm ]->> (n + m) / c''.
Proof.
  introv H1 H2.
  induction H1; simpl; eauto.
Qed.

Lemma step_deterministic tm c c1 c2:
  c -[ tm ]-> c1 ->
  c -[ tm ]-> c2 ->
  c1 = c2.
Proof.
  intros C1 C2.
  inverts C1.
  inverts C2.
  - congruence.
  - destruct sgn; cbn in H6; congruence.
  - inverts C2;
    destruct sgn; cbn in H; congruence.
Qed.

Lemma no_halted_step : forall tm c,
  ~ halted tm c ->
  exists c',
  c -[ tm ]-> c'.
Proof.
  introv Hhalted.
  destruct c as [[[l [m r]] s] sgn].
  destruct (tm (s,m)) as [[[m' sgn'] s'] |] eqn:E.
  - destruct sgn,sgn'; eexists; constructor; apply E.
  - congruence.
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
    destruct H0 as [n [c'' [H0 H1]]].
    specialize (H (S n)).
    destruct H as [c' H].
    gen c c' c''.
    induction n.
    + introv C' C'' Hh.
      inverts C'. inverts C''.
      inverts H1.
      unfold halted in Hh.
      inverts H0; congruence.
    + intros c c' H2 c'' H3 H4.
      inverts H2. inverts H3.
      eapply IHn; eauto.
      applys_eq H5.
      eapply step_deterministic; eauto.
Qed.


Lemma step_evstep_progress :
  forall tm c c' c'',
  c  -[ tm ]-> c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2.
  gen c H1.
  induction H2.
  - auto.
  - intros.
    eapply progress_step; eauto.
Qed.


Notation DH_cconfig := ((list Sym)*(list Sym)*Q*dir)%type.

Definition DH_cconfig_to_bounded_config(x:DH_cconfig)(l0 r0:side):DH_config :=
let '(l,r,s,sgn):=x in
((match sgn with | R => l0 | L => r0 end) <* l, r *> (match sgn with | R => r0 | L => l0 end), s, sgn).

Definition DH_cconfig_to_config(x:DH_cconfig):DH_config :=
let '(l,r,s,sgn):=x in
(const s0 <* l, r *> const s0, s, sgn).

Section DH_cconfig_ctx.
Hypothesis tm:TM.

Definition DH_cconfig_bounded_step(x:DH_cconfig):option DH_cconfig :=
let '(l,r,s,sgn):=x in
match r with
| nil => None
| m::r0 =>
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    if dir_eqb sgn sgn' then
      Some (m'::l,r0,s',sgn')
    else
      Some (m'::r0,l,s',sgn')
  end
end.

Definition DH_cconfig_bounded_step'(x:DH_cconfig):DH_cconfig+DH_cconfig :=
match DH_cconfig_bounded_step x with
| Some x' => inl x'
| None => inr x
end.

Definition DH_config_bounded_steps(x:DH_cconfig)(T:N):DH_cconfig+DH_cconfig :=
N_iter_until DH_cconfig_bounded_step' (inl x) T.

Definition DH_cconfig_bounded_progress(x:DH_cconfig)(T:N):option DH_cconfig :=
match DH_cconfig_bounded_step x with
| None => None
| Some x =>
  match DH_config_bounded_steps x T with
  | inl x => Some x
  | inr x => Some x
  end
end.

Definition DH_cconfig_step(x:DH_cconfig):option DH_cconfig :=
let '(l,r,s,sgn):=x in
match r with
| nil =>
  match tm (s,s0) with
  | None => None
  | Some (m',sgn',s') =>
    if dir_eqb sgn sgn' then
      Some (m'::l,nil,s',sgn')
    else
      Some (m'::nil,l,s',sgn')
  end
| m::r0 =>
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    if dir_eqb sgn sgn' then
      Some (m'::l,r0,s',sgn')
    else
      Some (m'::r0,l,s',sgn')
  end
end.

Definition DH_cconfig_step'(x:DH_cconfig):DH_cconfig+DH_cconfig :=
match DH_cconfig_step x with
| None => inr x
| Some x0 => inl x0
end.

Definition DH_cconfig_steps(x:DH_cconfig)(T:N):DH_cconfig+DH_cconfig :=
N_iter_until DH_cconfig_step' (inl x) T.

Definition cc0:DH_cconfig := (nil,nil,q0,R).

Definition clength(x:DH_cconfig) :=
let '(l,r,s,sgn):=x in
length l + length r.

Lemma DH_cconfig_bounded_step_spec c c':
  DH_cconfig_bounded_step c = Some c' ->
  (clength c = clength c' /\ forall l0 r0,
  DH_cconfig_to_bounded_config c l0 r0 -[ tm ]-> DH_cconfig_to_bounded_config c' l0 r0).
Proof.
  unfold DH_cconfig_bounded_step.
  destruct c as [[[l r] s] sgn].
  destruct r as [|m r].
  1: congruence.
  destruct (tm (s,m)) as [[[m' sgn'] s']|] eqn:E.
  2: congruence.
  intros Hc'.
  destruct sgn,sgn'; cbn; (split; [|intros l0 r0]; inverts Hc'; cbn; auto).
  all: lia.
Qed.

Lemma DH_cconfig_bounded_steps_spec c T:
  match DH_config_bounded_steps c T with
  | inl c' =>
    clength c = clength c' /\
    forall l0 r0,
    DH_cconfig_to_bounded_config c l0 r0 -[ tm ]->* DH_cconfig_to_bounded_config c' l0 r0
  | inr c' =>
    clength c = clength c' /\
    forall l0 r0,
    DH_cconfig_to_bounded_config c l0 r0 -[ tm ]->* DH_cconfig_to_bounded_config c' l0 r0
  end.
Proof.
  apply N_iter_until_spec.
  2: split; constructor.
  introv [Hlen Hev].
  unfold DH_cconfig_bounded_step'.
  destruct (DH_cconfig_bounded_step x0) eqn:E.
  2: tauto.
  destruct (DH_cconfig_bounded_step_spec _ _ E) as [H H0].
  split.
  1: congruence.
  intros.
  eapply evstep_trans.
  1: apply Hev.
  econstructor.
  1: apply H0.
  constructor.
Qed.

Lemma DH_cconfig_bounded_progress_spec c T:
  match DH_cconfig_bounded_progress c T with
  | Some c' =>
    clength c = clength c' /\
    forall l0 r0,
    DH_cconfig_to_bounded_config c l0 r0 -[ tm ]->+ DH_cconfig_to_bounded_config c' l0 r0
  | None => True
  end.
Proof.
  unfold DH_cconfig_bounded_progress.
  destruct (DH_cconfig_bounded_step c) eqn:E; trivial.
  epose proof (DH_cconfig_bounded_steps_spec p T) as H.
  destruct (DH_config_bounded_steps p T).
  {
  destruct H as [Hlen Hev].
  split.
  + rewrite <-Hlen.
    eapply DH_cconfig_bounded_step_spec,E.
  + intros.
    eapply step_evstep_progress.
    - eapply DH_cconfig_bounded_step_spec,E.
    - eapply Hev.
  }
  destruct H as [Hlen Hev].
  epose proof (DH_cconfig_bounded_step_spec _ _ E) as [H H0].
  split.
  1: congruence.
  intros.
  eapply step_evstep_progress; eauto.
Qed.

Lemma DH_cconfig_step_spec c:
  match DH_cconfig_step c with
  | Some c' => DH_cconfig_to_config c -[ tm ]-> DH_cconfig_to_config c'
  | None => halted tm (DH_cconfig_to_config c)
  end.
Proof.
  unfold DH_cconfig_step.
  destruct c as [[[l r] s] sgn].
  destruct r as [|m r].
  - destruct (tm (s,s0)) as [[[m' sgn'] s']|] eqn:E.
    2: congruence.
    destruct sgn,sgn'; cbn.
    + applys_eq step_through; eauto.
      rewrite <-const_unfold; reflexivity.
    + applys_eq step_back; eauto.
      1: rewrite <-const_unfold; reflexivity.
      1: reflexivity.
      apply E.
    + applys_eq step_back; eauto.
      1: rewrite <-const_unfold; reflexivity.
      1: reflexivity.
      apply E.
    + applys_eq step_through; eauto.
      rewrite <-const_unfold; reflexivity.
  - destruct (tm (s,m)) as [[[m' sgn'] s']|] eqn:E.
    2: congruence.
    destruct sgn,sgn'; cbn; auto.
Qed.

Lemma DH_cconfig_steps_spec c T:
  match DH_cconfig_steps c T with
  | inl c' => DH_cconfig_to_config c -[ tm ]->* DH_cconfig_to_config c'
  | inr c' => halted tm (DH_cconfig_to_config c')
  end.
Proof.
  apply N_iter_until_spec.
  2: constructor.
  intros.
  unfold DH_cconfig_step'.
  pose proof (DH_cconfig_step_spec x0).
  destruct (DH_cconfig_step x0).
  - eapply evstep_trans; eauto.
  - auto.
Qed.

End DH_cconfig_ctx.

Lemma progress_nonhalt : forall tm (P : DH_config -> Prop) c,
  (forall c, P c -> exists c', P c' /\ c -[ tm ]->+ c') ->
  P c ->
  ~ halts tm c.
Proof.
  introv Hstep H0.
  eapply step_nonhalt with (P:=fun c => P c \/ exists c', P c' /\ c -[ tm ]->+ c').
  2: tauto.
  intros c1 [H|H].
  1: destruct (Hstep c1 H) as [c' [H1 H2]].
  2: destruct H as [c' [H1 H2]].
  all: destruct H2;
    [ exists c'; tauto
    | exists c';
      split; try tauto;
      right;
      exists c''; tauto ].
Qed.

Lemma step_nonhalted tm c1 c2:
  c1 -[ tm ]-> c2 ->
  ~ halted tm c1.
Proof.
  unfold halted.
  intros H H0.
  inverts H; congruence.
Qed.

Lemma multistep_nonhalt tm n c1 c2:
  ~halts tm c2 ->
  multistep tm n c1 c2 ->
  ~halts tm c1.
Proof.
  gen c1 c2.
  induction n; introv Hn Hm.
  - inverts Hm. apply Hn.
  - inverts Hm.
    epose proof (IHn c' c2 Hn H1) as Hh.
    intros [n0 [c3 [H2 H3]]].
    apply Hh.
    destruct n0 as [|n0].
    + inverts H2.
      destruct (step_nonhalted _ _ _ H0 H3).
    + inverts H2.
      assert (c'=c'0) by (eapply step_deterministic; eauto); subst c'0.
      exists n0 c3; tauto.
Qed.

Lemma evstep_multistep {tm c1 c2}:
  evstep tm c1 c2 ->
  exists n, multistep tm n c1 c2.
Proof.
  intros.
  induction H.
  - eauto.
  - destruct IHevstep as [n IH].
    eauto.
Qed.

Lemma evstep_nonhalt {tm c1 c2}:
  ~halts tm c2 ->
  evstep tm c1 c2 ->
  ~halts tm c1.
Proof.
  intros Hh He.
  destruct (evstep_multistep He) as [n Hm].
  eapply multistep_nonhalt; eauto.
Qed.

Definition step_c(tm:TM)(c:DH_config):option (DH_config) :=
let '(l,m >> r,s,sgn):=c in
match tm (s,m) with
| None => None
| Some (m',sgn',s') =>
  if dir_eqb sgn sgn' then
    Some (m' >> l,r,s',sgn')
  else
    Some (m' >> r,l,s',sgn')
end.

Fixpoint multistep_c(tm:TM)(n:nat)(c:DH_config) :=
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
  - destruct c as [[[l [m r]] s] sgn].
    cbn in H.
    destruct (tm (s,m)) as [[[m' sgn'] s']|] eqn:E.
    2: congruence.
    destruct sgn,sgn'; inverts H; constructor; auto.
  - inverts H; cbn; rewrite H0; destruct sgn; reflexivity.
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
End DHTM.


