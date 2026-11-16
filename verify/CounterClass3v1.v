From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import SimplTape.

Open Scope list.


Ltac unfold_config' :=
match goal with
| |- ?a -[_]->* ?b -> _ =>
  unfold_config_expr a;
  unfold_config_expr b
end.

Ltac follow' x :=
  pose proof x as Hx;
  gen Hx;
  unfold_config';
  simpl_rotate;
  intro Hx;
  try (
  follow Hx;
  clear Hx).

Section skip_lr_sec.
Hypothesis lw rw: list sym.

Fixpoint skip_lr(l r:side)(T:nat) :=
match T with
| O => (l,r,O)
| S T =>
  match skip_prefix lw l,skip_prefix rw r with
  | Some l,Some r =>
    match skip_lr l r T with
    | (l,r,n) => (l,r,S n)
    end
  | _,_ => (l,r,O)
  end
end.

Lemma skip_lr_spec l r T l0 r0 n:
  skip_lr l r T = (l0,r0,n) ->
  l = lw^^n*>l0 /\
  r = rw^^n*>r0.
Proof.
  gen l r l0 r0 n.
  induction T; cbn[skip_lr]; intros.
  - inverts H; split; trivial.
  - destruct (skip_prefix lw l) as [l'|] eqn:El.
    2: inverts H; split; trivial.
    destruct (skip_prefix rw r) as [r'|] eqn:Er.
    2: inverts H; split; trivial.
    destruct (skip_lr l' r' T) as [[l0' r0'] n'] eqn:E.
    inverts H.
    apply IHT in E.
    eapply skip_prefix_spec in El,Er; subst.
    destruct E as [E1 E2].
    rewrite E1,E2.
    cbn[lpow].
    do 2 rewrite Str_app_assoc.
    split; trivial.
Qed.

End skip_lr_sec.

Lemma step_c_None tm c:
  step_c tm c = None ->
  halts tm c.
Proof.
  unfold step_c.
  intros.
  apply halted_halts.
  destruct c as [q [[l m] r]].
  destruct (tm (q,m)) as [[[o []]]|] eqn:E.
  1,2: inverts H.
  apply E.
Qed.



Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB1LA_1LC1RB_0RD0LA_1LA1RE_---1RF_1RC0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Lemma P0_n n:
  forall l r,
  l <* [0;0]^^n <| [0] *> [1]^^n *> r -->*
  l <| [1;1]^^n *> [0] *> [1]^^n *> r.
Proof.
  induction n; intros.
  1: es.
  follow' (IHn ([0;0]*>l) ([1]*>r)).
  es; er.
  follow IHn.
  es.
Qed.

Import Eqb.

Section mstep_sec.

Hypothesis T:nat.

Definition astep(x:Q*tape):(Q*tape) :=
let '(q,(l,m,r)):=x in
if eqb q B then
match skip_prefix [1;1;0] r with
| None => x
| Some r0 =>
  let '(l1,r1,n) := skip_lr [0;0] [1] (l<<m) r0 T in
  l1 <| [1;1]^^n *> [0] *> r0
end
else x.

Definition mstep x :=
match step_c tm x with
| Some x' => inl (astep x')
| None => inr tt
end.

Lemma astep_spec x:
  x -->* astep x.
Proof.
  unfold astep.
  destruct x as [q [[l m] r]].
  destruct (eqb_spec q B); subst.
  2: finish.
  destruct (skip_prefix [1;1;0] r) as [r0|] eqn:E.
  2: finish.
  destruct (skip_lr [0;0] [1] (l<<m) r0 T) as [[l1 r1] n] eqn:E0.
  eapply skip_prefix_spec in E.
  eapply skip_lr_spec in E0.
  destruct E0 as [E0 E1]; subst.
  eapply evstep_trans.
  2: apply P0_n.
  rewrite <-E0.
  finish.
Qed.

Definition msteps T0 :=
  N_iter_until mstep (inl c0) T0.

Lemma msteps_spec T0:
match msteps T0 with
| inl x => c0 -->* x
| inr _ => halts tm c0
end.
Proof.
  eapply N_iter_until_spec.
  2: finish.
  intros.
  unfold mstep.
  destruct (step_c tm x0) as [x'|] eqn:E.
  - apply step_c_spec in E.
    follow H.
    eapply evstep_step.
    1: apply E.
    apply astep_spec.
  - apply step_c_None in E.
    eapply halts_evstep; eauto 1.
Qed.

Lemma msteps_halt T0:
  msteps T0 = inr tt ->
  halts tm c0.
Proof.
  intros.
  pose proof (msteps_spec T0) as I1.
  rewrite H in I1.
  trivial.
Qed.

End mstep_sec.

Lemma halt: halts tm c0.
Proof.
  eapply (msteps_halt (10^5) (10^10)).
  native_check_eq.
Time Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LC1LE_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{B}}> r) (at level 30).

Lemma P0_n n:
  forall l r,
  l <* [0;0;0]^^n <| [0] *> [1]^^n *> r -->*
  l <| [1;1;1]^^n *> [0] *> [1]^^n *> r.
Proof.
  induction n; intros.
  1: es.
  follow' (IHn ([0;0;0]*>l) ([1]*>r)).
  es; er.
  follow IHn.
  es.
Qed.

Import Eqb.

Section mstep_sec.

Hypothesis T:nat.

Definition astep(x:Q*tape):(Q*tape) :=
let '(q,(l,m,r)):=x in
if eqb q D then
match skip_prefix [1;1;1;0] r with
| None => x
| Some r0 =>
  let '(l1,r1,n) := skip_lr [0;0;0] [1] (l<<m) r0 T in
  l1 <| [1;1;1]^^n *> [0] *> r0
end
else x.

Definition mstep x :=
match step_c tm x with
| Some x' => inl (astep x')
| None => inr tt
end.

Lemma astep_spec x:
  x -->* astep x.
Proof.
  unfold astep.
  destruct x as [q [[l m] r]].
  destruct (eqb_spec q D); subst.
  2: finish.
  destruct (skip_prefix [1;1;1;0] r) as [r0|] eqn:E.
  2: finish.
  destruct (skip_lr [0;0;0] [1] (l<<m) r0 T) as [[l1 r1] n] eqn:E0.
  eapply skip_prefix_spec in E.
  eapply skip_lr_spec in E0.
  destruct E0 as [E0 E1]; subst.
  eapply evstep_trans.
  2: apply P0_n.
  rewrite <-E0.
  finish.
Qed.

Definition msteps T0 :=
  N_iter_until mstep (inl c0) T0.

Lemma msteps_spec T0:
match msteps T0 with
| inl x => c0 -->* x
| inr _ => halts tm c0
end.
Proof.
  eapply N_iter_until_spec.
  2: finish.
  intros.
  unfold mstep.
  destruct (step_c tm x0) as [x'|] eqn:E.
  - apply step_c_spec in E.
    follow H.
    eapply evstep_step.
    1: apply E.
    apply astep_spec.
  - apply step_c_None in E.
    eapply halts_evstep; eauto 1.
Qed.

Lemma msteps_halt T0:
  msteps T0 = inr tt ->
  halts tm c0.
Proof.
  intros.
  pose proof (msteps_spec T0) as I1.
  rewrite H in I1.
  trivial.
Qed.

End mstep_sec.

Lemma halt: halts tm c0.
Proof.
  eapply (msteps_halt (10^5) (10^10)).
  native_check_eq.
Time Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB1LA_1LC1RE_1LD1RC_0RB0LA_---1RF_1RD0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{D}}> r) (at level 30).

Lemma P0_n n:
  forall l r,
  l <* [0;0;0]^^n <| [0] *> [1]^^n *> r -->*
  l <| [1;1;1]^^n *> [0] *> [1]^^n *> r.
Proof.
  induction n; intros.
  1: es.
  follow' (IHn ([0;0;0]*>l) ([1]*>r)).
  es; er.
  follow IHn.
  es.
Qed.

Import Eqb.

Section mstep_sec.

Hypothesis T:nat.

Definition astep(x:Q*tape):(Q*tape) :=
let '(q,(l,m,r)):=x in
if eqb q C then
match skip_prefix [1;1;1;0] r with
| None => x
| Some r0 =>
  let '(l1,r1,n) := skip_lr [0;0;0] [1] (l<<m) r0 T in
  l1 <| [1;1;1]^^n *> [0] *> r0
end
else x.

Definition mstep x :=
match step_c tm x with
| Some x' => inl (astep x')
| None => inr tt
end.

Lemma astep_spec x:
  x -->* astep x.
Proof.
  unfold astep.
  destruct x as [q [[l m] r]].
  destruct (eqb_spec q C); subst.
  2: finish.
  destruct (skip_prefix [1;1;1;0] r) as [r0|] eqn:E.
  2: finish.
  destruct (skip_lr [0;0;0] [1] (l<<m) r0 T) as [[l1 r1] n] eqn:E0.
  eapply skip_prefix_spec in E.
  eapply skip_lr_spec in E0.
  destruct E0 as [E0 E1]; subst.
  eapply evstep_trans.
  2: apply P0_n.
  rewrite <-E0.
  finish.
Qed.

Definition msteps T0 :=
  N_iter_until mstep (inl c0) T0.

Lemma msteps_spec T0:
match msteps T0 with
| inl x => c0 -->* x
| inr _ => halts tm c0
end.
Proof.
  eapply N_iter_until_spec.
  2: finish.
  intros.
  unfold mstep.
  destruct (step_c tm x0) as [x'|] eqn:E.
  - apply step_c_spec in E.
    follow H.
    eapply evstep_step.
    1: apply E.
    apply astep_spec.
  - apply step_c_None in E.
    eapply halts_evstep; eauto 1.
Qed.

Lemma msteps_halt T0:
  msteps T0 = inr tt ->
  halts tm c0.
Proof.
  intros.
  pose proof (msteps_spec T0) as I1.
  rewrite H in I1.
  trivial.
Qed.

End mstep_sec.

Lemma halt: halts tm c0.
Proof.
  eapply (msteps_halt (10^5) (10^10)).
  native_check_eq.
Time Qed.

End TM6.

