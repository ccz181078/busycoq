From BusyCoq Require Import Individual62.
Require Import ZifyNat ZifyN Lia.
Require Import NArith.
Require Import String.
Require Import List.

Open Scope list.

Ltac flia := repeat (lia || f_equal).

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1LC_0LC---_0LA1RD_0RE0RF_1RC1RE_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{E}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [16;7;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM3.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1RC_0LA1RE_0RC0RF_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [16;7;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM5.


Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0RE_1RD1RC_0LA1RB_1LE0RF_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [16;7;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM25.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0LB---_0RA0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Import Eqb.

Fixpoint LOpN_rec(o:Op)(x:list N):option (list N) :=
match o with
| P =>
  match x with
  | n::x => Some ((1+n)::x)
  | [] => Some [1]
  end
| I =>
  match x with
  | n::x =>
    if n mod 2 =? 0 then
    LOpN_rec P x &&& (fun x' => Some (n+4::x'))
    else
    match
      if 5<=?n then
      LOpN_rec I x &&& (fun x' => Some (n::x'))
      else None
    with
    | Some y => Some y
    | None =>
      if eqb x [1] then
      Some [n+3;3;1]
      else None
    end
  | _ => None
  end
end.

Fixpoint LOpsPI_rec(m:N)(x:list N)(T:nat):option (list N) :=
match T with
| O => None
| Datatypes.S T =>
if m=?0 then Some x else
match x with
| n::x =>
  match
    if andb (n mod 2 =? 1) (5<=? n) then
    if m mod 2 =? 0 then
    LOpsPI_rec (m/2) x T &&& (fun x' => Some (n+m/2*6::x'))
    else
    LOpsPI_rec (m-1) (n::x) T &&& (fun x0 =>
    LOpN_rec P x0 &&& (fun x1 =>
    LOpN_rec I x1))
    else None
  with
  | Some y => Some y
  | None =>
    LOpN_rec P (n::x) &&& (fun x0 =>
    LOpN_rec I x0 &&& (fun x1 =>
    LOpsPI_rec (m-1) x1 T))
  end
| _ => None
end
end.

Definition maxT:nat := 1000.

Definition BigStep_rec(x:list N):option (list N) :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT))
  else None
  else
  LOpN_rec P x &&& (fun x0 =>
  LOpsPI_rec (n/2+2) x0 maxT)
| _ => None
end.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Definition StbN_rec(x:list N):option unit :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT &&& (fun x' =>
  if eqb x' (n*2-2::n+1::x) then Some tt else None )))
  else None
  else None
| _ => None
end.

Ltac cg := try congruence.

Lemma LOpN_rec_spec o x x':
  LOpN_rec o x = Some x' ->
  LOpN o x x'.
Proof.
  gen o x'.
  induction x; cbn[LOpN_rec]; unfold if_Some; intros.
  - destruct o; cg.
    inverts H.
    constructor.
  - destruct o.
    + destruct (N.eqb_spec (a mod 2) 0) as [E|E].
      * destruct (LOpN_rec P x) eqn:E0; cg.
        inverts H.
        econstructor; eauto.
      * destruct (N.leb_spec 5 a) as [E0|E0].
        -- destruct (LOpN_rec I x) eqn:E1; cg.
           2: shelve.
           inverts H.
           econstructor; eauto; lia.
        -- shelve.
    + inverts H.
      constructor.
  Unshelve.
  all:
    destruct (eqb_spec x [1]); cg; subst;
    inverts H;
    econstructor; eauto; lia.
Qed.

Lemma LOpsPI_rec_spec m x x' T:
  LOpsPI_rec m x T = Some x' ->
  LOpsPI m x x'.
Proof.
  gen m x x'.
  induction T; cbn[LOpsPI_rec]; unfold if_Some; intros; cg.
  destruct (N.eqb_spec m 0) as [E|E].
  1: subst; inverts H; econstructor.
  destruct x as [|n x]; cg.
  destruct (andb (n mod 2 =? 1) (5 <=? n)) eqn:E0.
  - rewrite Bool.andb_true_iff in E0.
    destruct E0 as [E0 E1].
    destruct (N.eqb_spec (n mod 2) 1); cg.
    destruct (N.leb_spec 5 n); cg.
    destruct (N.eqb_spec (m mod 2) 0) as [E2|E2].
    + destruct (LOpsPI_rec (m/2) x T) eqn:E3; cg.
      2: shelve.
      inverts H.
      econstructor; eauto.
    + destruct (LOpsPI_rec (m-1) (n::x) T) eqn:E3; cg.
      2: shelve.
      apply IHT in E3.
      destruct (LOpN_rec P l) eqn:E4; cg.
      2: shelve.
      destruct (LOpN_rec I l0) eqn:E5; cg.
      2: shelve.
      apply LOpN_rec_spec in E4,E5.
      inverts H.
      econstructor; eauto; lia.
  - shelve.
  Unshelve.
  all:
    destruct (LOpN_rec P (n::x)) as [l'|] eqn:E1'; cg;
    destruct (LOpN_rec I l') eqn:E2'; cg;
    apply LOpN_rec_spec in E1',E2';
    apply IHT in H;
    econstructor; eauto; lia.
Qed.

Lemma BigStep_rec_spec x x':
  BigStep_rec x = Some x' ->
  BigStep x x'.
Proof.
  unfold BigStep_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0).
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
  - destruct (LOpN_rec P x) eqn:E; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E.
    econstructor; eauto; lia.
Qed.

Lemma StbN_rec_spec x:
  StbN_rec x = Some tt ->
  StbN x.
Proof.
  unfold StbN_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0); cg.
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    destruct (LOpsPI_rec ((n-4)/2) l0 maxT) eqn:E1; cg.
    destruct (eqb_spec l1 (n*2-2::n+1::x)); cg.
    apply LOpsPI_rec_spec in E1.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
Qed.



Ltac solve_ctor :=
match goal with
| |- BigStep _ _ =>
  eapply BigStep_rec_spec;
  vm_compute; reflexivity
| |- StbN _ =>
  eapply StbN_rec_spec;
  vm_compute; reflexivity
end.

Ltac solve_step :=
  eapply multistep_nonhalt;
  [ apply BigStep_spec; try solve_ctor | ].

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  solve_step; solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [10;3;1]).
  1: unfold S',S; esx.
  time do 140 solve_step.
  time solve_loop.
Time Qed.

End TM4.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_0RA0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Import Eqb.

Fixpoint LOpN_rec(o:Op)(x:list N):option (list N) :=
match o with
| P =>
  match x with
  | n::x => Some ((1+n)::x)
  | [] => Some [1]
  end
| I =>
  match x with
  | n::x =>
    if n mod 2 =? 0 then
    LOpN_rec P x &&& (fun x' => Some (n+4::x'))
    else
    match
      if 5<=?n then
      LOpN_rec I x &&& (fun x' => Some (n::x'))
      else None
    with
    | Some y => Some y
    | None =>
      if eqb x [1] then
      Some [n+3;3;1]
      else None
    end
  | _ => None
  end
end.

Fixpoint LOpsPI_rec(m:N)(x:list N)(T:nat):option (list N) :=
match T with
| O => None
| Datatypes.S T =>
if m=?0 then Some x else
match x with
| n::x =>
  match
    if andb (n mod 2 =? 1) (5<=? n) then
    if m mod 2 =? 0 then
    LOpsPI_rec (m/2) x T &&& (fun x' => Some (n+m/2*6::x'))
    else
    LOpsPI_rec (m-1) (n::x) T &&& (fun x0 =>
    LOpN_rec P x0 &&& (fun x1 =>
    LOpN_rec I x1))
    else None
  with
  | Some y => Some y
  | None =>
    LOpN_rec P (n::x) &&& (fun x0 =>
    LOpN_rec I x0 &&& (fun x1 =>
    LOpsPI_rec (m-1) x1 T))
  end
| _ => None
end
end.

Definition maxT:nat := 1000.

Definition BigStep_rec(x:list N):option (list N) :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT))
  else None
  else
  LOpN_rec P x &&& (fun x0 =>
  LOpsPI_rec (n/2+2) x0 maxT)
| _ => None
end.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Definition StbN_rec(x:list N):option unit :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT &&& (fun x' =>
  if eqb x' (n*2-2::n+1::x) then Some tt else None )))
  else None
  else None
| _ => None
end.

Ltac cg := try congruence.

Lemma LOpN_rec_spec o x x':
  LOpN_rec o x = Some x' ->
  LOpN o x x'.
Proof.
  gen o x'.
  induction x; cbn[LOpN_rec]; unfold if_Some; intros.
  - destruct o; cg.
    inverts H.
    constructor.
  - destruct o.
    + destruct (N.eqb_spec (a mod 2) 0) as [E|E].
      * destruct (LOpN_rec P x) eqn:E0; cg.
        inverts H.
        econstructor; eauto.
      * destruct (N.leb_spec 5 a) as [E0|E0].
        -- destruct (LOpN_rec I x) eqn:E1; cg.
           2: shelve.
           inverts H.
           econstructor; eauto; lia.
        -- shelve.
    + inverts H.
      constructor.
  Unshelve.
  all:
    destruct (eqb_spec x [1]); cg; subst;
    inverts H;
    econstructor; eauto; lia.
Qed.

Lemma LOpsPI_rec_spec m x x' T:
  LOpsPI_rec m x T = Some x' ->
  LOpsPI m x x'.
Proof.
  gen m x x'.
  induction T; cbn[LOpsPI_rec]; unfold if_Some; intros; cg.
  destruct (N.eqb_spec m 0) as [E|E].
  1: subst; inverts H; econstructor.
  destruct x as [|n x]; cg.
  destruct (andb (n mod 2 =? 1) (5 <=? n)) eqn:E0.
  - rewrite Bool.andb_true_iff in E0.
    destruct E0 as [E0 E1].
    destruct (N.eqb_spec (n mod 2) 1); cg.
    destruct (N.leb_spec 5 n); cg.
    destruct (N.eqb_spec (m mod 2) 0) as [E2|E2].
    + destruct (LOpsPI_rec (m/2) x T) eqn:E3; cg.
      2: shelve.
      inverts H.
      econstructor; eauto.
    + destruct (LOpsPI_rec (m-1) (n::x) T) eqn:E3; cg.
      2: shelve.
      apply IHT in E3.
      destruct (LOpN_rec P l) eqn:E4; cg.
      2: shelve.
      destruct (LOpN_rec I l0) eqn:E5; cg.
      2: shelve.
      apply LOpN_rec_spec in E4,E5.
      inverts H.
      econstructor; eauto; lia.
  - shelve.
  Unshelve.
  all:
    destruct (LOpN_rec P (n::x)) as [l'|] eqn:E1'; cg;
    destruct (LOpN_rec I l') eqn:E2'; cg;
    apply LOpN_rec_spec in E1',E2';
    apply IHT in H;
    econstructor; eauto; lia.
Qed.

Lemma BigStep_rec_spec x x':
  BigStep_rec x = Some x' ->
  BigStep x x'.
Proof.
  unfold BigStep_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0).
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
  - destruct (LOpN_rec P x) eqn:E; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E.
    econstructor; eauto; lia.
Qed.

Lemma StbN_rec_spec x:
  StbN_rec x = Some tt ->
  StbN x.
Proof.
  unfold StbN_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0); cg.
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    destruct (LOpsPI_rec ((n-4)/2) l0 maxT) eqn:E1; cg.
    destruct (eqb_spec l1 (n*2-2::n+1::x)); cg.
    apply LOpsPI_rec_spec in E1.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
Qed.



Ltac solve_ctor :=
match goal with
| |- BigStep _ _ =>
  eapply BigStep_rec_spec;
  vm_compute; reflexivity
| |- StbN _ =>
  eapply StbN_rec_spec;
  vm_compute; reflexivity
end.

Ltac solve_step :=
  eapply multistep_nonhalt;
  [ apply BigStep_spec; try solve_ctor | ].

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  solve_step; solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [10;3;1]).
  1: unfold S',S; esx.
  time do 140 solve_step.
  time solve_loop.
Time Qed.

End TM6.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_1LC0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Import Eqb.

Fixpoint LOpN_rec(o:Op)(x:list N):option (list N) :=
match o with
| P =>
  match x with
  | n::x => Some ((1+n)::x)
  | [] => Some [1]
  end
| I =>
  match x with
  | n::x =>
    if n mod 2 =? 0 then
    LOpN_rec P x &&& (fun x' => Some (n+4::x'))
    else
    match
      if 5<=?n then
      LOpN_rec I x &&& (fun x' => Some (n::x'))
      else None
    with
    | Some y => Some y
    | None =>
      if eqb x [1] then
      Some [n+3;3;1]
      else None
    end
  | _ => None
  end
end.

Fixpoint LOpsPI_rec(m:N)(x:list N)(T:nat):option (list N) :=
match T with
| O => None
| Datatypes.S T =>
if m=?0 then Some x else
match x with
| n::x =>
  match
    if andb (n mod 2 =? 1) (5<=? n) then
    if m mod 2 =? 0 then
    LOpsPI_rec (m/2) x T &&& (fun x' => Some (n+m/2*6::x'))
    else
    LOpsPI_rec (m-1) (n::x) T &&& (fun x0 =>
    LOpN_rec P x0 &&& (fun x1 =>
    LOpN_rec I x1))
    else None
  with
  | Some y => Some y
  | None =>
    LOpN_rec P (n::x) &&& (fun x0 =>
    LOpN_rec I x0 &&& (fun x1 =>
    LOpsPI_rec (m-1) x1 T))
  end
| _ => None
end
end.

Definition maxT:nat := 1000.

Definition BigStep_rec(x:list N):option (list N) :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT))
  else None
  else
  LOpN_rec P x &&& (fun x0 =>
  LOpsPI_rec (n/2+2) x0 maxT)
| _ => None
end.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Definition StbN_rec(x:list N):option unit :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT &&& (fun x' =>
  if eqb x' (n*2-2::n+1::x) then Some tt else None )))
  else None
  else None
| _ => None
end.

Ltac cg := try congruence.

Lemma LOpN_rec_spec o x x':
  LOpN_rec o x = Some x' ->
  LOpN o x x'.
Proof.
  gen o x'.
  induction x; cbn[LOpN_rec]; unfold if_Some; intros.
  - destruct o; cg.
    inverts H.
    constructor.
  - destruct o.
    + destruct (N.eqb_spec (a mod 2) 0) as [E|E].
      * destruct (LOpN_rec P x) eqn:E0; cg.
        inverts H.
        econstructor; eauto.
      * destruct (N.leb_spec 5 a) as [E0|E0].
        -- destruct (LOpN_rec I x) eqn:E1; cg.
           2: shelve.
           inverts H.
           econstructor; eauto; lia.
        -- shelve.
    + inverts H.
      constructor.
  Unshelve.
  all:
    destruct (eqb_spec x [1]); cg; subst;
    inverts H;
    econstructor; eauto; lia.
Qed.

Lemma LOpsPI_rec_spec m x x' T:
  LOpsPI_rec m x T = Some x' ->
  LOpsPI m x x'.
Proof.
  gen m x x'.
  induction T; cbn[LOpsPI_rec]; unfold if_Some; intros; cg.
  destruct (N.eqb_spec m 0) as [E|E].
  1: subst; inverts H; econstructor.
  destruct x as [|n x]; cg.
  destruct (andb (n mod 2 =? 1) (5 <=? n)) eqn:E0.
  - rewrite Bool.andb_true_iff in E0.
    destruct E0 as [E0 E1].
    destruct (N.eqb_spec (n mod 2) 1); cg.
    destruct (N.leb_spec 5 n); cg.
    destruct (N.eqb_spec (m mod 2) 0) as [E2|E2].
    + destruct (LOpsPI_rec (m/2) x T) eqn:E3; cg.
      2: shelve.
      inverts H.
      econstructor; eauto.
    + destruct (LOpsPI_rec (m-1) (n::x) T) eqn:E3; cg.
      2: shelve.
      apply IHT in E3.
      destruct (LOpN_rec P l) eqn:E4; cg.
      2: shelve.
      destruct (LOpN_rec I l0) eqn:E5; cg.
      2: shelve.
      apply LOpN_rec_spec in E4,E5.
      inverts H.
      econstructor; eauto; lia.
  - shelve.
  Unshelve.
  all:
    destruct (LOpN_rec P (n::x)) as [l'|] eqn:E1'; cg;
    destruct (LOpN_rec I l') eqn:E2'; cg;
    apply LOpN_rec_spec in E1',E2';
    apply IHT in H;
    econstructor; eauto; lia.
Qed.

Lemma BigStep_rec_spec x x':
  BigStep_rec x = Some x' ->
  BigStep x x'.
Proof.
  unfold BigStep_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0).
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
  - destruct (LOpN_rec P x) eqn:E; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E.
    econstructor; eauto; lia.
Qed.

Lemma StbN_rec_spec x:
  StbN_rec x = Some tt ->
  StbN x.
Proof.
  unfold StbN_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0); cg.
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    destruct (LOpsPI_rec ((n-4)/2) l0 maxT) eqn:E1; cg.
    destruct (eqb_spec l1 (n*2-2::n+1::x)); cg.
    apply LOpsPI_rec_spec in E1.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
Qed.



Ltac solve_ctor :=
match goal with
| |- BigStep _ _ =>
  eapply BigStep_rec_spec;
  vm_compute; reflexivity
| |- StbN _ =>
  eapply StbN_rec_spec;
  vm_compute; reflexivity
end.

Ltac solve_step :=
  eapply multistep_nonhalt;
  [ apply BigStep_spec; try solve_ctor | ].

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  solve_step; solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [10;3;1]).
  1: unfold S',S; esx.
  time do 140 solve_step.
  time solve_loop.
Time Qed.

End TM19.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_1LE0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Import Eqb.

Fixpoint LOpN_rec(o:Op)(x:list N):option (list N) :=
match o with
| P =>
  match x with
  | n::x => Some ((1+n)::x)
  | [] => Some [1]
  end
| I =>
  match x with
  | n::x =>
    if n mod 2 =? 0 then
    LOpN_rec P x &&& (fun x' => Some (n+4::x'))
    else
    match
      if 5<=?n then
      LOpN_rec I x &&& (fun x' => Some (n::x'))
      else None
    with
    | Some y => Some y
    | None =>
      if eqb x [1] then
      Some [n+3;3;1]
      else None
    end
  | _ => None
  end
end.

Fixpoint LOpsPI_rec(m:N)(x:list N)(T:nat):option (list N) :=
match T with
| O => None
| Datatypes.S T =>
if m=?0 then Some x else
match x with
| n::x =>
  match
    if andb (n mod 2 =? 1) (5<=? n) then
    if m mod 2 =? 0 then
    LOpsPI_rec (m/2) x T &&& (fun x' => Some (n+m/2*6::x'))
    else
    LOpsPI_rec (m-1) (n::x) T &&& (fun x0 =>
    LOpN_rec P x0 &&& (fun x1 =>
    LOpN_rec I x1))
    else None
  with
  | Some y => Some y
  | None =>
    LOpN_rec P (n::x) &&& (fun x0 =>
    LOpN_rec I x0 &&& (fun x1 =>
    LOpsPI_rec (m-1) x1 T))
  end
| _ => None
end
end.

Definition maxT:nat := 1000.

Definition BigStep_rec(x:list N):option (list N) :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT))
  else None
  else
  LOpN_rec P x &&& (fun x0 =>
  LOpsPI_rec (n/2+2) x0 maxT)
| _ => None
end.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Definition StbN_rec(x:list N):option unit :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT &&& (fun x' =>
  if eqb x' (n*2-2::n+1::x) then Some tt else None )))
  else None
  else None
| _ => None
end.

Ltac cg := try congruence.

Lemma LOpN_rec_spec o x x':
  LOpN_rec o x = Some x' ->
  LOpN o x x'.
Proof.
  gen o x'.
  induction x; cbn[LOpN_rec]; unfold if_Some; intros.
  - destruct o; cg.
    inverts H.
    constructor.
  - destruct o.
    + destruct (N.eqb_spec (a mod 2) 0) as [E|E].
      * destruct (LOpN_rec P x) eqn:E0; cg.
        inverts H.
        econstructor; eauto.
      * destruct (N.leb_spec 5 a) as [E0|E0].
        -- destruct (LOpN_rec I x) eqn:E1; cg.
           2: shelve.
           inverts H.
           econstructor; eauto; lia.
        -- shelve.
    + inverts H.
      constructor.
  Unshelve.
  all:
    destruct (eqb_spec x [1]); cg; subst;
    inverts H;
    econstructor; eauto; lia.
Qed.

Lemma LOpsPI_rec_spec m x x' T:
  LOpsPI_rec m x T = Some x' ->
  LOpsPI m x x'.
Proof.
  gen m x x'.
  induction T; cbn[LOpsPI_rec]; unfold if_Some; intros; cg.
  destruct (N.eqb_spec m 0) as [E|E].
  1: subst; inverts H; econstructor.
  destruct x as [|n x]; cg.
  destruct (andb (n mod 2 =? 1) (5 <=? n)) eqn:E0.
  - rewrite Bool.andb_true_iff in E0.
    destruct E0 as [E0 E1].
    destruct (N.eqb_spec (n mod 2) 1); cg.
    destruct (N.leb_spec 5 n); cg.
    destruct (N.eqb_spec (m mod 2) 0) as [E2|E2].
    + destruct (LOpsPI_rec (m/2) x T) eqn:E3; cg.
      2: shelve.
      inverts H.
      econstructor; eauto.
    + destruct (LOpsPI_rec (m-1) (n::x) T) eqn:E3; cg.
      2: shelve.
      apply IHT in E3.
      destruct (LOpN_rec P l) eqn:E4; cg.
      2: shelve.
      destruct (LOpN_rec I l0) eqn:E5; cg.
      2: shelve.
      apply LOpN_rec_spec in E4,E5.
      inverts H.
      econstructor; eauto; lia.
  - shelve.
  Unshelve.
  all:
    destruct (LOpN_rec P (n::x)) as [l'|] eqn:E1'; cg;
    destruct (LOpN_rec I l') eqn:E2'; cg;
    apply LOpN_rec_spec in E1',E2';
    apply IHT in H;
    econstructor; eauto; lia.
Qed.

Lemma BigStep_rec_spec x x':
  BigStep_rec x = Some x' ->
  BigStep x x'.
Proof.
  unfold BigStep_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0).
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
  - destruct (LOpN_rec P x) eqn:E; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E.
    econstructor; eauto; lia.
Qed.

Lemma StbN_rec_spec x:
  StbN_rec x = Some tt ->
  StbN x.
Proof.
  unfold StbN_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0); cg.
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    destruct (LOpsPI_rec ((n-4)/2) l0 maxT) eqn:E1; cg.
    destruct (eqb_spec l1 (n*2-2::n+1::x)); cg.
    apply LOpsPI_rec_spec in E1.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
Qed.



Ltac solve_ctor :=
match goal with
| |- BigStep _ _ =>
  eapply BigStep_rec_spec;
  vm_compute; reflexivity
| |- StbN _ =>
  eapply StbN_rec_spec;
  vm_compute; reflexivity
end.

Ltac solve_step :=
  eapply multistep_nonhalt;
  [ apply BigStep_spec; try solve_ctor | ].

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  solve_step; solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [10;3;1]).
  1: unfold S',S; esx.
  time do 140 solve_step.
  time solve_loop.
Time Qed.

End TM20.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RD_1RD1LB_0RE0RF_---1RA_1LF0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Import Eqb.

Fixpoint LOpN_rec(o:Op)(x:list N):option (list N) :=
match o with
| P =>
  match x with
  | n::x => Some ((1+n)::x)
  | [] => Some [1]
  end
| I =>
  match x with
  | n::x =>
    if n mod 2 =? 0 then
    LOpN_rec P x &&& (fun x' => Some (n+4::x'))
    else
    match
      if 5<=?n then
      LOpN_rec I x &&& (fun x' => Some (n::x'))
      else None
    with
    | Some y => Some y
    | None =>
      if eqb x [1] then
      Some [n+3;3;1]
      else None
    end
  | _ => None
  end
end.

Fixpoint LOpsPI_rec(m:N)(x:list N)(T:nat):option (list N) :=
match T with
| O => None
| Datatypes.S T =>
if m=?0 then Some x else
match x with
| n::x =>
  match
    if andb (n mod 2 =? 1) (5<=? n) then
    if m mod 2 =? 0 then
    LOpsPI_rec (m/2) x T &&& (fun x' => Some (n+m/2*6::x'))
    else
    LOpsPI_rec (m-1) (n::x) T &&& (fun x0 =>
    LOpN_rec P x0 &&& (fun x1 =>
    LOpN_rec I x1))
    else None
  with
  | Some y => Some y
  | None =>
    LOpN_rec P (n::x) &&& (fun x0 =>
    LOpN_rec I x0 &&& (fun x1 =>
    LOpsPI_rec (m-1) x1 T))
  end
| _ => None
end
end.

Definition maxT:nat := 1000.

Definition BigStep_rec(x:list N):option (list N) :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT))
  else None
  else
  LOpN_rec P x &&& (fun x0 =>
  LOpsPI_rec (n/2+2) x0 maxT)
| _ => None
end.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Definition StbN_rec(x:list N):option unit :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT &&& (fun x' =>
  if eqb x' (n*2-2::n+1::x) then Some tt else None )))
  else None
  else None
| _ => None
end.

Ltac cg := try congruence.

Lemma LOpN_rec_spec o x x':
  LOpN_rec o x = Some x' ->
  LOpN o x x'.
Proof.
  gen o x'.
  induction x; cbn[LOpN_rec]; unfold if_Some; intros.
  - destruct o; cg.
    inverts H.
    constructor.
  - destruct o.
    + destruct (N.eqb_spec (a mod 2) 0) as [E|E].
      * destruct (LOpN_rec P x) eqn:E0; cg.
        inverts H.
        econstructor; eauto.
      * destruct (N.leb_spec 5 a) as [E0|E0].
        -- destruct (LOpN_rec I x) eqn:E1; cg.
           2: shelve.
           inverts H.
           econstructor; eauto; lia.
        -- shelve.
    + inverts H.
      constructor.
  Unshelve.
  all:
    destruct (eqb_spec x [1]); cg; subst;
    inverts H;
    econstructor; eauto; lia.
Qed.

Lemma LOpsPI_rec_spec m x x' T:
  LOpsPI_rec m x T = Some x' ->
  LOpsPI m x x'.
Proof.
  gen m x x'.
  induction T; cbn[LOpsPI_rec]; unfold if_Some; intros; cg.
  destruct (N.eqb_spec m 0) as [E|E].
  1: subst; inverts H; econstructor.
  destruct x as [|n x]; cg.
  destruct (andb (n mod 2 =? 1) (5 <=? n)) eqn:E0.
  - rewrite Bool.andb_true_iff in E0.
    destruct E0 as [E0 E1].
    destruct (N.eqb_spec (n mod 2) 1); cg.
    destruct (N.leb_spec 5 n); cg.
    destruct (N.eqb_spec (m mod 2) 0) as [E2|E2].
    + destruct (LOpsPI_rec (m/2) x T) eqn:E3; cg.
      2: shelve.
      inverts H.
      econstructor; eauto.
    + destruct (LOpsPI_rec (m-1) (n::x) T) eqn:E3; cg.
      2: shelve.
      apply IHT in E3.
      destruct (LOpN_rec P l) eqn:E4; cg.
      2: shelve.
      destruct (LOpN_rec I l0) eqn:E5; cg.
      2: shelve.
      apply LOpN_rec_spec in E4,E5.
      inverts H.
      econstructor; eauto; lia.
  - shelve.
  Unshelve.
  all:
    destruct (LOpN_rec P (n::x)) as [l'|] eqn:E1'; cg;
    destruct (LOpN_rec I l') eqn:E2'; cg;
    apply LOpN_rec_spec in E1',E2';
    apply IHT in H;
    econstructor; eauto; lia.
Qed.

Lemma BigStep_rec_spec x x':
  BigStep_rec x = Some x' ->
  BigStep x x'.
Proof.
  unfold BigStep_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0).
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
  - destruct (LOpN_rec P x) eqn:E; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E.
    econstructor; eauto; lia.
Qed.

Lemma StbN_rec_spec x:
  StbN_rec x = Some tt ->
  StbN x.
Proof.
  unfold StbN_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0); cg.
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    destruct (LOpsPI_rec ((n-4)/2) l0 maxT) eqn:E1; cg.
    destruct (eqb_spec l1 (n*2-2::n+1::x)); cg.
    apply LOpsPI_rec_spec in E1.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
Qed.



Ltac solve_ctor :=
match goal with
| |- BigStep _ _ =>
  eapply BigStep_rec_spec;
  vm_compute; reflexivity
| |- StbN _ =>
  eapply StbN_rec_spec;
  vm_compute; reflexivity
end.

Ltac solve_step :=
  eapply multistep_nonhalt;
  [ apply BigStep_spec; try solve_ctor | ].

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  solve_step; solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [10;3;1]).
  1: unfold S',S; esx.
  time do 140 solve_step.
  time solve_loop.
Time Qed.

End TM24.


Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RD_1RD1LB_0RA0RE_1LE0RF_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+1;1] [n*2+4;3;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  LOpN I [n;1] [n+3;3;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-1)/2*2+1) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Import Eqb.

Fixpoint LOpN_rec(o:Op)(x:list N):option (list N) :=
match o with
| P =>
  match x with
  | n::x => Some ((1+n)::x)
  | [] => Some [1]
  end
| I =>
  match x with
  | n::x =>
    if n mod 2 =? 0 then
    LOpN_rec P x &&& (fun x' => Some (n+4::x'))
    else
    match
      if 5<=?n then
      LOpN_rec I x &&& (fun x' => Some (n::x'))
      else None
    with
    | Some y => Some y
    | None =>
      if eqb x [1] then
      Some [n+3;3;1]
      else None
    end
  | _ => None
  end
end.

Fixpoint LOpsPI_rec(m:N)(x:list N)(T:nat):option (list N) :=
match T with
| O => None
| Datatypes.S T =>
if m=?0 then Some x else
match x with
| n::x =>
  match
    if andb (n mod 2 =? 1) (5<=? n) then
    if m mod 2 =? 0 then
    LOpsPI_rec (m/2) x T &&& (fun x' => Some (n+m/2*6::x'))
    else
    LOpsPI_rec (m-1) (n::x) T &&& (fun x0 =>
    LOpN_rec P x0 &&& (fun x1 =>
    LOpN_rec I x1))
    else None
  with
  | Some y => Some y
  | None =>
    LOpN_rec P (n::x) &&& (fun x0 =>
    LOpN_rec I x0 &&& (fun x1 =>
    LOpsPI_rec (m-1) x1 T))
  end
| _ => None
end
end.

Definition maxT:nat := 1000.

Definition BigStep_rec(x:list N):option (list N) :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT))
  else None
  else
  LOpN_rec P x &&& (fun x0 =>
  LOpsPI_rec (n/2+2) x0 maxT)
| _ => None
end.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Definition StbN_rec(x:list N):option unit :=
match x with
| n::x =>
  if n mod 2 =? 0 then
  if 4 <=? n then
  LOpN_rec I x &&& (fun x0 =>
  LOpN_rec I x0 &&& (fun x1 =>
  LOpsPI_rec ((n-4)/2) x1 maxT &&& (fun x' =>
  if eqb x' (n*2-2::n+1::x) then Some tt else None )))
  else None
  else None
| _ => None
end.

Ltac cg := try congruence.

Lemma LOpN_rec_spec o x x':
  LOpN_rec o x = Some x' ->
  LOpN o x x'.
Proof.
  gen o x'.
  induction x; cbn[LOpN_rec]; unfold if_Some; intros.
  - destruct o; cg.
    inverts H.
    constructor.
  - destruct o.
    + destruct (N.eqb_spec (a mod 2) 0) as [E|E].
      * destruct (LOpN_rec P x) eqn:E0; cg.
        inverts H.
        econstructor; eauto.
      * destruct (N.leb_spec 5 a) as [E0|E0].
        -- destruct (LOpN_rec I x) eqn:E1; cg.
           2: shelve.
           inverts H.
           econstructor; eauto; lia.
        -- shelve.
    + inverts H.
      constructor.
  Unshelve.
  all:
    destruct (eqb_spec x [1]); cg; subst;
    inverts H;
    econstructor; eauto; lia.
Qed.

Lemma LOpsPI_rec_spec m x x' T:
  LOpsPI_rec m x T = Some x' ->
  LOpsPI m x x'.
Proof.
  gen m x x'.
  induction T; cbn[LOpsPI_rec]; unfold if_Some; intros; cg.
  destruct (N.eqb_spec m 0) as [E|E].
  1: subst; inverts H; econstructor.
  destruct x as [|n x]; cg.
  destruct (andb (n mod 2 =? 1) (5 <=? n)) eqn:E0.
  - rewrite Bool.andb_true_iff in E0.
    destruct E0 as [E0 E1].
    destruct (N.eqb_spec (n mod 2) 1); cg.
    destruct (N.leb_spec 5 n); cg.
    destruct (N.eqb_spec (m mod 2) 0) as [E2|E2].
    + destruct (LOpsPI_rec (m/2) x T) eqn:E3; cg.
      2: shelve.
      inverts H.
      econstructor; eauto.
    + destruct (LOpsPI_rec (m-1) (n::x) T) eqn:E3; cg.
      2: shelve.
      apply IHT in E3.
      destruct (LOpN_rec P l) eqn:E4; cg.
      2: shelve.
      destruct (LOpN_rec I l0) eqn:E5; cg.
      2: shelve.
      apply LOpN_rec_spec in E4,E5.
      inverts H.
      econstructor; eauto; lia.
  - shelve.
  Unshelve.
  all:
    destruct (LOpN_rec P (n::x)) as [l'|] eqn:E1'; cg;
    destruct (LOpN_rec I l') eqn:E2'; cg;
    apply LOpN_rec_spec in E1',E2';
    apply IHT in H;
    econstructor; eauto; lia.
Qed.

Lemma BigStep_rec_spec x x':
  BigStep_rec x = Some x' ->
  BigStep x x'.
Proof.
  unfold BigStep_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0).
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
  - destruct (LOpN_rec P x) eqn:E; cg.
    apply LOpsPI_rec_spec in H.
    apply LOpN_rec_spec in E.
    econstructor; eauto; lia.
Qed.

Lemma StbN_rec_spec x:
  StbN_rec x = Some tt ->
  StbN x.
Proof.
  unfold StbN_rec,if_Some.
  intros H.
  destruct x as [|n x]; cg.
  destruct (N.eqb_spec (n mod 2) 0); cg.
  - destruct (N.leb_spec 4 n); cg.
    destruct (LOpN_rec I x) eqn:E; cg.
    destruct (LOpN_rec I l) eqn:E0; cg.
    destruct (LOpsPI_rec ((n-4)/2) l0 maxT) eqn:E1; cg.
    destruct (eqb_spec l1 (n*2-2::n+1::x)); cg.
    apply LOpsPI_rec_spec in E1.
    apply LOpN_rec_spec in E,E0.
    econstructor; eauto.
Qed.



Ltac solve_ctor :=
match goal with
| |- BigStep _ _ =>
  eapply BigStep_rec_spec;
  vm_compute; reflexivity
| |- StbN _ =>
  eapply StbN_rec_spec;
  vm_compute; reflexivity
end.

Ltac solve_step :=
  eapply multistep_nonhalt;
  [ apply BigStep_spec; try solve_ctor | ].

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  solve_step; solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [10;3;1]).
  1: unfold S',S; esx.
  time do 140 solve_step.
  time solve_loop.
Time Qed.

End TM26.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1RC_0LA1RE_0RF0LD_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+5;4;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+2;4;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [14;7;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM1.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1RC_0LA1RE_1LD0RF_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+5;4;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+2;4;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [14;7;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM14.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1RC_0LA1RE_0RF0RF_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+5;4;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+2;4;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [14;7;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM22.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_0RF0LB_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+5;4;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+2;4;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [9;4;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM2.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_1LB0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+5;4;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+2;4;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [9;4;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM13.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_0RF0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+5;4;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+2;4;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [9;4;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM23.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_0LD1RC_0LA1RE_1RD0RF_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+5;1] [n*2+5;6;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I [n;1] [n;6;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    solve[constructor].
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [7;6;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC1RA_1RD1LB_0RE---_1RB1RE_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{E}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+5;1] [n*2+5;6;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I [n;1] [n;6;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    solve[constructor].
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [7;6;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM8.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_0LA0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+5;1] [n*2+5;6;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I [n;1] [n;6;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    solve[constructor].
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [7;6;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM11.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1RC_0LA1RE_1RD0RF_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+5;1] [n*2+5;6;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I [n;1] [n;6;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    solve[constructor].
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [11;6;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1RC_0LA1RE_0LC0RF_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+5;1] [n*2+5;6;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I [n;1] [n;6;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    solve[constructor].
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [11;6;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM10.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_1RC0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+4;5;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+1;5;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [8;5;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM15.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_1RE0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+4;5;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+1;5;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [8;5;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM18.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1RC_0LA1RE_1RA0RF_1LF0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+4;5;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+1;5;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [17;8;5;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1LE_0RD---_1RE1RD_0LB1RA_1LF0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{D}}> r) (at level 30).

Fixpoint LC(x:list nat):side :=
match x with
| [] => 0inf
| n::t => LC t <* [0] <* [1]^^n
end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp: Op -> (list nat) -> (list nat) -> Prop :=
| LPush1 n t: LOp P (n::t) ((1+n)::t)
| LPush1_0: LOp P [] [1]
| LInc0 n t t':
  LOp P t t' ->
  LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t':
  LOp I t t' ->
  LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n:
  LOp I [n*2+3;1] [n*2+4;5;1]
.

Inductive LOps: (list Op) -> (list nat) -> (list nat) -> Prop :=
| LOps_O x: LOps [] x x
| LOps_S h t x x0 x1:
  LOp h x x0 ->
  LOps t x0 x1 ->
  LOps (h::t) x x1
.

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H.
  inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r,
  LC x <| r -->* LC x' |> r.
Proof.
  gen x'.
  induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    + rewrite (LPush1_spec H2).
      es.
    + specialize (IHx _ H2).
      es; er.
      follow IHx.
      es.
    + es.
Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'.
  induction n; intros.
  - inverts H.
    finish.
  - cbn in H.
    solve_v1.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply H1.
    rewrite H2.
    es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er.
  follow H2.
  es; er.
  follow H1.
  es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H.
  cbn in H.
  solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2.
  es.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x',
  LOps h2 x x' ->
  LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'',
  LOps h1 x x'' /\
  LOps h2 x'' x'.
Proof.
  gen h2 x x'.
  induction h1; intros.
  - exists x; split.
    1: constructor.
    apply H.
  - cbn in H.
    inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [I1 I2]].
    eexists; split.
    + econstructor; eassumption.
    + eassumption.
Qed.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  gen h2 x x'' x'.
  induction h1; intros.
  - inverts H.
    apply H0.
  - inverts H.
    cbn.
    econstructor.
    1: eassumption.
    eapply IHh1; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1.
  intros.
  eapply LOps_split in H1.
  destruct H1 as [x'' [I1 I2]].
  eapply H in I1.
  eapply H0 in I2.
  eapply LOps_trans; eassumption.
Qed.

Lemma LOps1_O n:
  LOps1 [] [] n n.
Proof.
  unfold LOps1.
  intros.
  inverts H.
  constructor.
Qed.

Ltac solve_P :=
  econstructor; [ constructor | ].

Ltac solve_I x :=
  econstructor; [ applys_eq x; [ f_equal; lia | eassumption ] | ].

Ltac solve_I' :=
  econstructor; [ econstructor; eassumption | ].

Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma LIncs_1_0 n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m) (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n.
  induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H.
    cbn in *.
    solve_v2.
    solve_P.
    solve_I (LInc0 (n+3)).
    solve_P.
    solve_I (LInc1 (n+3)).
    solve_nil.
Qed.

Lemma LIncs_1_1' n m:
  LOps1 ([I;I]++[P;I]^^(m*2+1)) ([I;I]++[P;I]^^m++[P]) (n*2+5) ((n+m*3+3)*2+4).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - intros x x' H.
    solve_v2.
    solve_I'.
    solve_I'.
    solve_nil.
  - eapply LOps1_trans.
    1: apply LIncs_1_0.
    econstructor.
    1: econstructor.
    solve_v2.
    solve_I (LInc0 (n+m*3+3)).
    solve_nil.
Qed.

Definition S x := LC x |> 0inf.

Inductive Stb: (list nat) -> Prop :=
| Stb_intro n x:
  LOps (I::I::[P;I]^^n) x (((n*2+1)*2+4)::(n*2+5)::x) ->
  Stb ((n*2+4)::x).

Lemma Stb_spec x:
  Stb x ->
  exists x',
  S x -->+ S x' /\
  Stb x'.
Proof.
  intros HP.
  inverts HP.
  eexists; split.
  - unfold S.
    apply LIncs_0,H.
  - constructor.
    epose proof (LIncs_1_1' n n _ _ _) as I1.
    applys_eq I1; flia.
    Unshelve.
    rewrite app_assoc.
    eapply LOps_trans.
    1: eassumption.
    solve_P.
    solve_nil.
Qed.

Local Coercion N.to_nat : N >-> nat.

Open Scope N.

Inductive LOpN: Op -> (list N) -> (list N) -> Prop :=
| LPush1N n t: LOpN P (n::t) ((1+n)::t)
| LPush1N_0: LOpN P [] [1]
| LInc0N n t t':
  n mod 2 = 0 ->
  LOpN P t t' ->
  LOpN I (n::t) ((n+4)::t')
| LInc1N n t t':
  n mod 2 = 1 ->
  5 <= n ->
  LOpN I t t' ->
  LOpN I (n::t) (n::t')
| LInchN n:
  n mod 2 = 1 ->
  3 <= n ->
  LOpN I [n;1] [n+1;5;1]
.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite N2Nat.inj_add in * ||
  rewrite N2Nat.inj_sub in * ||
  rewrite N2Nat.inj_mul in * ||
  rewrite N2Nat.inj_div in * ||
  rewrite N2Nat.inj_mod in *
  ).


Lemma LOpN_spec [o x x']:
  LOpN o x x' ->
  LOp o (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - simpl_N_to_nat.
    constructor.
  - constructor.
  - replace n with (n/2*2) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    constructor; assumption.
  - replace n with ((n-3)/2*2+3) in * by lia.
    rewrite <-N.add_assoc.
    simpl_N_to_nat.
    constructor.
Qed.

Inductive LOpsPI: N -> (list N) -> (list N) -> Prop :=
| LOpsPI_1_0 m n x x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 0 ->
  LOpsPI (m/2) x x' ->
  LOpsPI m (n::x) ((n+m/2*6)::x')
| LOpsPI_1_1 m n x x0 x1 x':
  n mod 2 = 1 ->
  5 <= n ->
  m mod 2 = 1 ->
  LOpsPI (m-1) (n::x) x0 ->
  LOpN P x0 x1 ->
  LOpN I x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_S m n x x0 x1 x':
  1 <= m ->
  LOpN P (n::x) x0 ->
  LOpN I x0 x1 ->
  LOpsPI (m-1) x1 x' ->
  LOpsPI m (n::x) x'
| LOpsPI_O x:
  LOpsPI 0 x x
.

Ltac ee :=
  econstructor; try eassumption.

Lemma LOpsPI_spec [m x x']:
  LOpsPI m x x' ->
  LOps ([P;I]^^m) (map N.to_nat x) (map N.to_nat x').
Proof.
  intros H.
  induction H; cbn[map]; intros.
  - remember (m/2) as m1.
    replace m with (m1*2) in * by lia.
    replace n with ((n-5)/2*2+5) in * by lia.
    simpl_N_to_nat.
    applys_eq LIncs_1_0.
    1: flia.
    assumption.
  - remember (m/2) as m1.
    replace m with (m1*2+1) in * by lia.
    rewrite N.add_sub in IHLOpsPI.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    1: eassumption.
    apply LOpN_spec in H3,H4.
    repeat ee.
  - replace m with (1+(m-1)) by lia.
    simpl_N_to_nat.
    rewrite lpow_add.
    eapply LOps_trans.
    2: eassumption.
    apply LOpN_spec in H0,H1.
    repeat ee.
  - ee.
Qed.


Inductive BigStep: (list N) -> (list N) -> Prop :=
| BigStep_0 n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  BigStep (n::x) x'
| BigStep_1 n x x0 x':
  n mod 2 = 1 ->
  LOpN P x x0 ->
  LOpsPI (n/2+2) x0 x' ->
  BigStep (n::x) x'
.

Definition S' x := S (map N.to_nat x).

Lemma BigStep_spec [x x']:
  BigStep x x' ->
  S' x -->* S' x'.
Proof.
  unfold S'.
  intros H.
  inverts H; cbn[map].
  - eapply progress_evstep.
    remember ((n-4)/2) as n'.
    replace n with (n'*2+4) in * by lia.
    apply LOpN_spec in H2,H3.
    apply LOpsPI_spec in H4.
    simpl_N_to_nat.
    eapply LIncs_0.
    repeat ee.
  - eapply progress_evstep.
    remember (n/2) as n'.
    replace n with (n'*2+1) in * by lia.
    apply LOpN_spec in H1.
    apply LOpsPI_spec in H2.
    simpl_N_to_nat.
    eapply LIncs_1.
    repeat ee.
Qed.

Inductive StbN: (list N) -> Prop :=
| StbN_intro n x x0 x1 x':
  n mod 2 = 0 ->
  4 <= n ->
  LOpN I x x0 ->
  LOpN I x0 x1 ->
  LOpsPI ((n-4)/2) x1 x' ->
  x' = (n*2-2)::(n+1)::x ->
  StbN (n::x).

Lemma StbN_spec [x]:
  StbN x ->
  ~halts tm (S' x).
Proof.
  unfold S'.
  intros H.
  eapply progress_nonhalt_cond with (P:=Stb).
  1: eapply Stb_spec.
  inverts H.
  cbn[map].
  remember ((n-4)/2) as n'.
  replace n with (n'*2+4) in * by lia.
  apply LOpN_spec in H2,H3.
  apply LOpsPI_spec in H4.
  simpl_N_to_nat.
  econstructor.
  do 2 ee.
  applys_eq H4; cbn[map]; flia.
Qed.

Ltac solve_ctor :=
match goal with
| |- (_ = _) =>
  vm_compute; reflexivity
| |- (_ <= _) => 
  apply N.leb_le;
  vm_compute; reflexivity
| _ =>
  vm_compute;
  solve[econstructor; solve_ctor]
end.

Ltac solve_loop :=
  solve[
  eapply StbN_spec; solve_ctor |
  eapply multistep_nonhalt;
  [ apply BigStep_spec; solve_ctor | ];
  solve_loop ].


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [16;7;1]).
  1: unfold S',S; esx.
  solve_loop.
Qed.

End TM17.


