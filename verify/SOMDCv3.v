From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require Import DivModCases.
From BusyCoq Require Import BinaryCounter_v2.


Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.


Ltac flia := repeat (lia || f_equal).


Lemma sideRLs_trans_add tm h n1 n2 w1 w2 w3:
  sideRLs tm (h^^n1) w1 w3 ->
  sideRLs tm (h^^n2) w3 w2 ->
  sideRLs tm (h^^(n1+n2)) w1 w2.
Proof.
  intros.
  rewrite lpow_add.
  eapply sideRLs_trans; eassumption.
Qed.

Lemma segRLs_addmul_v2 a a' x b b' tm h w1 w2:
  segRLs tm (h^^b) (h^^b') w1 w2 ->
  segRLs tm (h^^a) (h^^a') w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^(x*a'+b')) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ b).
  rewrite (Nat.add_comm _ b').
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x; cbn[Nat.mul].
  - cbn.
    constructor.
  - cbn[lpow].
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    2: apply IHx.
    apply H0.
Qed.

Notation ld := [0;1;1;0].
Notation rd0 := [0;0].
Notation rd1 := [0;1].

Inductive RD := DX|D0|D1.

Inductive RD' := DX'|DX1|D0'|D01|D11.

Fixpoint toRD ls :=
match ls with
| [] => []
| DX'::t => DX::toRD t
| DX1::t => DX::D1::toRD t
| D0'::t => D0::toRD t
| D01::t => D0::D1::toRD t
| D11::t => D1::D1::toRD t
end.

Ltac eex := repeat eexists.
Ltac cg := congruence.

Inductive RIncs: nat->(list RD')->(list RD)->Prop :=
| RIncs_X n r r':
  RIncs (n*2+2) r r' ->
  RIncs (n+1) (DX'::r) (DX::r')
| RIncs_0_0 n r r':
  RIncs n r r' ->
  RIncs (n*2) (D0'::r) (D0::r')
| RIncs_0_1 n r r':
  RIncs n r r' ->
  RIncs (n*2+1) (D0'::r) (D1::r')
| RIncs_X1_0 n r r':
  RIncs (n*2+1) r r' ->
  RIncs (n*2+1) (DX1::r) (D0::DX::r')
| RIncs_X1_1 n r r':
  RIncs (n*2+1) r r' ->
  RIncs (n*2+2) (DX1::r) (D1::DX::r')
| RIncs_01 n r r':
  RIncs (n*2) r r' ->
  RIncs (n+1) (D01::r) (DX::r')
| RIncs_11 n r r':
  RIncs (n*2+1) r r' ->
  RIncs (n+1) (D11::r) (DX::r')
| RIncs_O' n r':
  RIncs (n+1) [D0'] r' ->
  RIncs (n+1) [] r'
| RIncs_O:
  RIncs 0 [] []
  .

Fixpoint toRC ls :=
match ls with
| [] => 0inf
| DX::t => ld *> toRC t
| D0::t => rd0 *> toRC t
| D1::t => rd1 *> toRC t
end.

Fixpoint toRC' ls :=
match ls with
| [] => 0inf
| DX'::t => [1;1;0;0] *> toRC' t
| DX1::t => [1;1;0;0;1;0] *> toRC' t
| D0'::t => rd0 *> toRC' t
| D01::t => [0;0;1;0] *> toRC' t
| D11::t => [1;0;1;0] *> toRC' t
end.

Lemma toRC'_spec ls:
  0 >> toRC' ls = toRC (toRD ls).
Proof.
  induction ls as [|[] ls]; st; cg.
Qed.

Ltac ssc H :=
  eapply segRLs_sideRLs_concat; [|apply H].

Ltac flia' := unfold DH0; solve[flia|esx].

Ltac des H :=
  let ls:=fresh "ls" in
  let I1:=fresh "I" in
  let I2:=fresh "I" in
  let I3:=fresh "I" in
  let I4:=fresh "I" in
  destruct H as [ls [[I1 I2]|[I1 [I2 [I3 I4]]]]].

Lemma RIncs_nil m:
  exists r', RIncs m [] r'.
Proof.
  induction m using lt_wf_ind.
  divmod2_cases m.
  - destruct n'.
    + eex.
      apply RIncs_O.
    + destruct (H (S n')) as [r' I].
      1: lia.
      eex.
      applys_eq (RIncs_O' (n'*2+1)).
      1: lia.
      applys_eq (RIncs_0_0 (S n')).
      1: lia.
      apply I.
  - destruct (H n') as [r' I].
    1: lia.
    eex.
    apply RIncs_O',RIncs_0_1,I.
Qed.

Lemma RIncs_RIncs n r r':
  RIncs n r r' ->
  exists r0,
  (
    r' = toRD r0 /\
    (forall m, m>=n*2 -> exists r0', RIncs m r0 r0')
  ) \/
  (
    r' = D1::toRD r0 /\
    (forall m, m>=n -> exists r0', RIncs m (DX1::r0) r0') /\
    (forall m, m>=n*4 -> exists r0', RIncs m (D01::r0) r0') /\
    (forall m, m>=n*4+2 -> exists r0', RIncs m (D11::r0) r0')
  ).
Proof.
  intro H.
  induction H.
  - des IHRIncs; subst r'.
    + exists (DX'::ls); cbn.
      left.
      split; [trivial|intros].
      destruct (I0 (m*2)) as [r0' I1].
      1: lia.
      eex.
      applys_eq (RIncs_X (m-1)).
      1: lia.
      applys_eq I1; flia.
    + exists (DX1::ls); cbn.
      left.
      split; [trivial|intros].
      apply I0; lia.
  - des IHRIncs; subst r'.
    + exists (D0'::ls); cbn.
      left.
      split; [trivial|intros].
      divmod2_cases m.
      * destruct (I0 n') as [r0' I1].
        1: lia.
        eex.
        apply RIncs_0_0,I1.
      * destruct (I0 n') as [r0' I1].
        1: lia.
        eex.
        apply RIncs_0_1,I1.
    + exists (D01::ls); cbn.
      left.
      split; [trivial|intros].
      apply I1; lia.
  - des IHRIncs; subst r'.
    + exists (ls); cbn.
      right.
      split; [trivial | split; [intros | split; intros]].
      {
        divmod2_cases m.
        - destruct (I0 (n'*2-1)) as [r0' I1].
          1: lia.
          eex.
          applys_eq (RIncs_X1_1 (n'-1)).
          1: lia.
          applys_eq I1; flia.
        - destruct (I0 (n'*2+1)) as [r0' I1].
          1: lia.
          eex.
          apply (RIncs_X1_0),I1.
      }
      {
        destruct (I0 ((m-1)*2)) as [r0' I1].
        1: lia.
        eex.
        applys_eq (RIncs_01 (m-1)).
        1: lia.
        apply I1.
      }
      {
        destruct (I0 ((m-1)*2+1)) as [r0' I1].
        1: lia.
        eex.
        applys_eq (RIncs_11 (m-1)).
        1: lia.
        apply I1.
      }
    + exists (D11::ls); cbn.
      left.
      split; [trivial|intros].
      apply I2; lia.
  - des IHRIncs; subst r'.
    + exists (D0'::DX'::ls); cbn.
      left.
      split; [trivial|intros].
      divmod2_cases m.
      {
        destruct (I0 (n'*2)) as [r0' I1].
        1: lia.
        eex.
        apply (RIncs_0_0).
        applys_eq (RIncs_X (n'-1)).
        1: lia.
        applys_eq I1; flia.
      }
      {
        destruct (I0 (n'*2)) as [r0' I1].
        1: lia.
        eex.
        apply (RIncs_0_1).
        applys_eq (RIncs_X (n'-1)).
        1: lia.
        applys_eq I1; flia.
      }
    + exists (D0'::DX1::ls); cbn.
      left.
      split; [trivial|intros].
      divmod2_cases m.
      {
        destruct (I0 (n')) as [r0' I3].
        1: lia.
        eex.
        apply (RIncs_0_0).
        applys_eq I3; flia.
      }
      {
        destruct (I0 (n')) as [r0' I3].
        1: lia.
        eex.
        apply (RIncs_0_1).
        applys_eq I3; flia.
      }
  - des IHRIncs; subst r'.
    + exists (DX'::ls); cbn.
      right.
      split; [trivial | split; [intros | split; intros]].
      {
        divmod2_cases m.
        {
          destruct (I0 (n'*4-2)) as [r0' I1].
          1: lia.
          eex.
          applys_eq (RIncs_X1_1 (n'-1)).
          1: lia.
          apply RIncs_X.
          applys_eq I1; flia.
        }
        {
          destruct (I0 (n'*4+2)) as [r0' I1].
          1: lia.
          eex.
          apply (RIncs_X1_0).
          apply RIncs_X.
          applys_eq I1; flia.
        }
      }
      {
        destruct (I0 (m*4-4)) as [r0' I1].
        1: lia.
        eex.
        applys_eq (RIncs_01 (m-1)).
        1: lia.
        applys_eq (RIncs_X (m*2-3)).
        1: lia.
        applys_eq I1; flia.
      }
      {
        destruct (I0 (m*4-2)) as [r0' I1].
        1: lia.
        eex.
        applys_eq (RIncs_11 (m-1)).
        1: lia.
        applys_eq (RIncs_X (m*2-2)).
        1: lia.
        applys_eq I1; flia.
      }
    + exists (DX1::ls); cbn.
      right.
      split; [trivial | split; [intros | split; intros]].
      {
        divmod2_cases m.
        {
          destruct (I0 (n'*2-1)) as [r0' I3].
          1: lia.
          eex.
          applys_eq (RIncs_X1_1 (n'-1)).
          1: lia.
          applys_eq I3; flia.
        }
        {
          destruct (I0 (n'*2+1)) as [r0' I3].
          1: lia.
          eex.
          apply (RIncs_X1_0 (n')).
          applys_eq I3; flia.
        }
      }
      {
        destruct (I0 (m*2-2)) as [r0' I3].
        1: lia.
        eex.
        applys_eq (RIncs_01 (m-1)).
        1: lia.
        applys_eq I3; flia.
      }
      {
        destruct (I0 (m*2-1)) as [r0' I3].
        1: lia.
        eex.
        applys_eq (RIncs_11 (m-1)).
        1: lia.
        applys_eq I3; flia.
      }
  - des IHRIncs; subst r'.
    + exists (DX'::ls); cbn.
      left.
      split; [trivial|intros].
      destruct (I0 (m*2)) as [r0' I1].
      1: lia.
      eex.
      applys_eq (RIncs_X (m-1)).
      1: lia.
      applys_eq I1; flia.
    + exists (DX1::ls); cbn.
      left.
      split; [trivial|intros].
      apply I0; lia.
  - des IHRIncs; subst r'.
    + exists (DX'::ls); cbn.
      left.
      split; [trivial|intros].
      destruct (I0 (m*2)) as [r0' I1].
      1: lia.
      eex.
      applys_eq (RIncs_X (m-1)).
      1: lia.
      applys_eq I1; flia.
    + exists (DX1::ls); cbn.
      left.
      split; [trivial|intros].
      apply I0; lia.
  - apply IHRIncs.
  - eexists [].
    left.
    split; [trivial|intros].
    apply RIncs_nil.
Qed.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC0LC_1RD0RE_1LA1RC_1RC0RF_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs_spec n r r':
  RIncs n r r' ->
  sideRLs tm (hRL^^n) (toRC' r) (toRC r').
Proof.
  intros.
  induction H; cbn[toRC']; cbn[toRC].
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 2); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 0 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 1 0); flia'.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 1); flia'.
  - applys_eq IHRIncs.
    cbn.
    solve_const0_eq.
  - esx.
Qed.

Definition S' r := 0inf {{{ (hL,L) }}} toRC (DX::r).

Definition P r' :=
  exists r, RIncs 1 r (DX::r').

Lemma BigStep r':
  P r' ->
  exists r0',
  S' r' -->+
  S' r0' /\
  P r0'.
Proof.
  intros [r H].
  apply RIncs_RIncs in H.
  unfold S',to_DH_config.
  des H.
  2: cg.
  rewrite I.
  rewrite <-toRC'_spec.
  destruct (I0 2) as [r0' I1].
  1: lia.
  exists r0'.
  split.
  2:{
    eex.
    apply (RIncs_X O),I1.
  }
  apply RIncs_spec in I1.
  mid10 (0inf {{{ (hR,R) }}} ld *> toRC' ls).
  1: es.
  assert (I2:sideRLs tm hRL (ld*>toRC' ls) (toRC (DX::r0'))).
  {
    cbn[toRC].
    ssc I1.
    esx.
  }
  eapply sideRLs_1 in I2.
  follow100 I2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [D0;D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  1: intros r' H; apply BigStep,H.
  unfold P.
  eexists [DX'].
  apply (RIncs_X 0).
  apply (RIncs_O' 1).
  apply (RIncs_0_0 1).
  apply (RIncs_O' 0).
  apply (RIncs_0_1 0).
  apply RIncs_O.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs_spec n r r':
  RIncs n r r' ->
  sideRLs tm (hRL^^n) (toRC' r) (toRC r').
Proof.
  intros.
  induction H; cbn[toRC']; cbn[toRC].
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 2); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 0 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 1 0); flia'.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 1); flia'.
  - applys_eq IHRIncs.
    cbn.
    solve_const0_eq.
  - esx.
Qed.

Definition S' r := 0inf {{{ (hL,L) }}} toRC (DX::r).

Definition P r' :=
  exists r, RIncs 1 r (DX::r').

Lemma BigStep r':
  P r' ->
  exists r0',
  S' r' -->+
  S' r0' /\
  P r0'.
Proof.
  intros [r H].
  apply RIncs_RIncs in H.
  unfold S',to_DH_config.
  des H.
  2: cg.
  rewrite I.
  rewrite <-toRC'_spec.
  destruct (I0 2) as [r0' I1].
  1: lia.
  exists r0'.
  split.
  2:{
    eex.
    apply (RIncs_X O),I1.
  }
  apply RIncs_spec in I1.
  mid10 (0inf {{{ (hR,R) }}} ld *> toRC' ls).
  1: es.
  assert (I2:sideRLs tm hRL (ld*>toRC' ls) (toRC (DX::r0'))).
  {
    cbn[toRC].
    ssc I1.
    esx.
  }
  eapply sideRLs_1 in I2.
  follow100 I2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [DX;DX;D1;D1;D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  1: intros r' H; apply BigStep,H.
  unfold P.
  eexists [DX';DX';D11].
  apply (RIncs_X 0).
  apply (RIncs_X 1).
  apply (RIncs_11 3).
  apply (RIncs_O' 6).
  apply (RIncs_0_1 3).
  apply (RIncs_O' 2).
  apply (RIncs_0_1 1).
  apply (RIncs_O' 0).
  apply (RIncs_0_1 0).
  apply RIncs_O.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC0RE_1LD1RB_1LA0LD_1RB0RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs_spec n r r':
  RIncs n r r' ->
  sideRLs tm (hRL^^n) (toRC' r) (toRC r').
Proof.
  intros.
  induction H; cbn[toRC']; cbn[toRC].
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 2); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 0 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 1 0); flia'.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 1); flia'.
  - applys_eq IHRIncs.
    cbn.
    solve_const0_eq.
  - esx.
Qed.

Definition S' r := 0inf {{{ (hL,L) }}} toRC (DX::r).

Definition P r' :=
  exists r, RIncs 1 r (DX::r').

Lemma BigStep r':
  P r' ->
  exists r0',
  S' r' -->+
  S' r0' /\
  P r0'.
Proof.
  intros [r H].
  apply RIncs_RIncs in H.
  unfold S',to_DH_config.
  des H.
  2: cg.
  rewrite I.
  rewrite <-toRC'_spec.
  destruct (I0 2) as [r0' I1].
  1: lia.
  exists r0'.
  split.
  2:{
    eex.
    apply (RIncs_X O),I1.
  }
  apply RIncs_spec in I1.
  mid10 (0inf {{{ (hR,R) }}} ld *> toRC' ls).
  1: es.
  assert (I2:sideRLs tm hRL (ld*>toRC' ls) (toRC (DX::r0'))).
  {
    cbn[toRC].
    ssc I1.
    esx.
  }
  eapply sideRLs_1 in I2.
  follow100 I2.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [DX;D0;D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  1: intros r' H; apply BigStep,H.
  unfold P.
  eexists [DX';D01].
  apply (RIncs_X 0).
  apply (RIncs_01 1).
  apply (RIncs_O' 1).
  apply (RIncs_0_0 1).
  apply (RIncs_O' 0).
  apply (RIncs_0_1 0).
  apply RIncs_O.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_0LD0LF_1RE---_1RF0RB_1RA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs_spec n r r':
  RIncs n r r' ->
  sideRLs tm (hRL^^n) (toRC' r) (toRC r').
Proof.
  intros.
  induction H; cbn[toRC']; cbn[toRC].
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 2); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 0 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 1 0); flia'.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 1); flia'.
  - applys_eq IHRIncs.
    cbn.
    solve_const0_eq.
  - esx.
Qed.

Definition S' r := 0inf {{{ (hL,L) }}} toRC (DX::r).

Definition P r' :=
  exists r, RIncs 1 r (DX::r').

Lemma BigStep r':
  P r' ->
  exists r0',
  S' r' -->+
  S' r0' /\
  P r0'.
Proof.
  intros [r H].
  apply RIncs_RIncs in H.
  unfold S',to_DH_config.
  des H.
  2: cg.
  rewrite I.
  rewrite <-toRC'_spec.
  destruct (I0 2) as [r0' I1].
  1: lia.
  exists r0'.
  split.
  2:{
    eex.
    apply (RIncs_X O),I1.
  }
  apply RIncs_spec in I1.
  mid10 (0inf <* <[1;1;0;1] {{{ (hR,R) }}} toRC' ls).
  1: es.
  cbn[lpow] in I1.
  eapply sideRLs_split in I1.
  destruct I1 as [r3 [I1 I1a]].
  eapply sideRLs_1 in I1,I1a.
  follow100 I1.
  er.
  follow100 I1a.
  er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [D0;DX;DX;D0;D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  1: intros r' H; apply BigStep,H.
  unfold P.
  eexists [DX';D0';DX';D01].
  apply (RIncs_X 0).
  apply (RIncs_0_0 1).
  apply (RIncs_X 0).
  apply (RIncs_01 1).
  apply (RIncs_O' 1).
  apply (RIncs_0_0 1).
  apply (RIncs_O' 0).
  apply (RIncs_0_1 0).
  apply RIncs_O.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RE_1RD0RB_1LE1RC_1LF0LE_0LA0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[]).
Notation hL := (E,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma RIncs_spec n r r':
  RIncs n r r' ->
  sideRLs tm (hRL^^n) (toRC' r) (toRC r').
Proof.
  intros.
  induction H; cbn[toRC']; cbn[toRC].
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 2); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 0 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 2 1 n 1 0); flia'.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - rewrite <-Str_app_assoc.
    ssc IHRIncs.
    apply segRLs_addmul_v2; esx.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 0); flia'.
  - ssc IHRIncs.
    applys_eq (segRLs_addmul_v2 1 2 n 1 1); flia'.
  - applys_eq IHRIncs.
    cbn.
    solve_const0_eq.
  - esx.
Qed.

Definition S' r := 0inf {{{ (hL,L) }}} toRC (DX::r).

Definition P r' :=
  exists r, RIncs 1 r (DX::r').

Lemma BigStep r':
  P r' ->
  exists r0',
  S' r' -->+
  S' r0' /\
  P r0'.
Proof.
  intros [r H].
  apply RIncs_RIncs in H.
  unfold S',to_DH_config.
  des H.
  2: cg.
  rewrite I.
  rewrite <-toRC'_spec.
  destruct (I0 2) as [r0' I1].
  1: lia.
  exists r0'.
  split.
  2:{
    eex.
    apply (RIncs_X O),I1.
  }
  apply RIncs_spec in I1.
  mid10 (0inf <* <[1;1;0;1] {{{ (hR,R) }}} toRC' ls).
  1: es.
  cbn[lpow] in I1.
  eapply sideRLs_split in I1.
  destruct I1 as [r3 [I1 I1a]].
  eapply sideRLs_1 in I1,I1a.
  follow100 I1.
  er.
  follow100 I1a.
  er.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [DX;D0;D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  1: intros r' H; apply BigStep,H.
  unfold P.
  eexists [DX';D01].
  apply (RIncs_X 0).
  apply (RIncs_01 1).
  apply (RIncs_O' 1).
  apply (RIncs_0_0 1).
  apply (RIncs_O' 0).
  apply (RIncs_0_1 0).
  apply RIncs_O.
Qed.

End TM5.


