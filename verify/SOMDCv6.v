From BusyCoq Require Import Individual62 Longitudinal DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RC_1RD0LE_0RA0LB_1RF0LD_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;0;0;1;0;0].
Notation d0 := [0;0;0;0].
Notation d1 := [1;0;0;0].
Notation hR := (A,[0]).
Notation hL := (C,[0]).
Notation h := [(hR,hL)].

Inductive RD := LD|D0|D1.
Inductive H := h100|h000|h0.

Fixpoint toRC ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Definition toH x :=
match x with
| h100 => [1;0;0]
| h000 => [0;0;0]
| h0 => [0]
end.

Inductive RIncs: H->nat->(list RD)->(list RD)->Prop :=
| RIncs_100_ld k r r':
  RIncs h100 (k*2) r r' ->
  RIncs h100 k (LD::r) (LD::r')
| RIncs_000_ld k r r':
  RIncs h100 (k*2) r r' ->
  RIncs h000 (1+k) (LD::r) (LD::r')
| RIncs_0_ld_0 k r r':
  RIncs h100 k r r' ->
  RIncs h0 (2+k*2) (LD::r) (D0::r')
| RIncs_0_ld_1 k r r':
  RIncs h100 k r r' ->
  RIncs h0 (3+k*2) (LD::r) (D1::r')

| RIncs_100_d0_0 k r r':
  RIncs h000 k r r' ->
  RIncs h100 (k*2) (D0::r) (D1::r')
| RIncs_100_d0_1 k r r':
  RIncs h000 (1+k) r r' ->
  RIncs h100 (1+k*2) (D0::r) (D0::r')
| RIncs_000_d0_0 k r r':
  RIncs h000 k r r' ->
  RIncs h000 (k*2) (D0::r) (D0::r')
| RIncs_000_d0_1 k r r':
  RIncs h000 k r r' ->
  RIncs h000 (1+k*2) (D0::r) (D1::r')
| RIncs_0_d0_0 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (k*2) (D0::r) (D0::r')
| RIncs_0_d0_1 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (1+k*2) (D0::r) (D1::r')

| RIncs_100_d1 k r r':
  RIncs h0 (k*2) r r' ->
  RIncs h100 k (D1::r) (LD::r')
| RIncs_000_d1 k r r':
  RIncs h0 (k*2) r r' ->
  RIncs h000 (1+k) (D1::r) (LD::r')
| RIncs_0_d1_0 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (2+k*2) (D1::r) (D0::r')
| RIncs_0_d1_1 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (3+k*2) (D1::r) (D1::r')

| RIncs_100_rh:
  RIncs h100 0 [] [D1]
| RIncs_100_rh':
  RIncs h100 1 [] [D0;D1]
| RIncs_000_rh:
  RIncs h000 0 [] []
| RIncs_0_rh:
  RIncs h0 0 [] []

| RIncs_100_rh_0 k r':
  RIncs h000 (1+k) [] r' ->
  RIncs h100 (2+k*2) [] (D1::r')
| RIncs_100_rh_1 k r':
  RIncs h000 (2+k) [] r' ->
  RIncs h100 (3+k*2) [] (D0::r')
| RIncs_000_rh_0 k r':
  RIncs h000 (1+k) [] r' ->
  RIncs h000 (2+k*2) [] (D0::r')
| RIncs_000_rh_1 k r':
  RIncs h000 k [] r' ->
  RIncs h000 (1+k*2) [] (D1::r')
| RIncs_0_rh_0 k r':
  RIncs h0 (1+k) [] r' ->
  RIncs h0 (2+k*2) [] (D0::r')
| RIncs_0_rh_1 k r':
  RIncs h0 k [] r' ->
  RIncs h0 (1+k*2) [] (D1::r')
.

Ltac cat6 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_;_;_]) (w2:=[_;_;_;_;_;_]); [|eauto 1].

Ltac cat4 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_]) (w2:=[_;_;_;_]); [|eauto 1].

Ltac cat4' :=
  do 4 rewrite const_unfold; cat4.

Open Scope nat.

Lemma RIncs_spec tp k r r':
  RIncs tp k r r' ->
  sideRLs tm (h^^k) (toH tp*>toRC r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toH toRC] in *.
  - cat6. am 1 2 k 0 0.
  - cat6. am 1 2 k 1 0.
  - cat4. am 2 1 k 2 0.
  - cat4. am 2 1 k 3 0.

  - cat4. am 2 1 k 0 0.
  - cat4. am 2 1 k 1 1.
  - cat4. am 2 1 k 0 0.
  - cat4. am 2 1 k 1 0.
  - cat4. am 2 1 k 0 0.
  - cat4. am 2 1 k 1 0.

  - cat6. am 1 2 k 0 0.
  - cat6. am 1 2 k 1 0.
  - cat4. am 2 1 k 2 0.
  - cat4. am 2 1 k 3 0.

  - esc.
  - esc.
  - esc.
  - esc.
  - cat4'. am 2 1 (1+k) 0 0.
  - cat4'. am 2 1 (1+k) 1 1.
  - cat4'. am 2 1 (1+k) 0 0.
  - cat4'. am 2 1 k 1 0.
  - cat4'. am 2 1 (1+k) 0 0.
  - cat4'. am 2 1 k 1 0.
Qed.


Lemma RIncs_nxt_0 k:
  exists r, RIncs h0 k [] r.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  + ec. ec.
  + destruct (mod2 k); subst.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
  Unshelve. all: lia.
Qed.

Lemma RIncs_nxt_000 k:
  exists r, RIncs h000 k [] r.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  + ec. ec.
  + destruct (mod2 k); subst.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
  Unshelve. all: lia.
Qed.

Lemma RIncs_nxt_100 k:
  exists r, RIncs h100 k [] r.
Proof.
  destruct k as [|[|k]].
  - ec. ec.
  - ec. ec.
  - destruct (mod2 k); subst.
    * epose proof (RIncs_nxt_000 _) as [r I].
      ec. ec. apply I.
    * epose proof (RIncs_nxt_000 _) as [r I].
      ec. ec. apply I.
Qed.

Ltac solve_v2 :=
  (epose proof (RIncs_nxt_0 _) as [r I]; repeat ec; apply I) ||
  (epose proof (RIncs_nxt_000 _) as [r I]; repeat ec; apply I) ||
  (epose proof (RIncs_nxt_100 _) as [r I]; repeat ec; apply I).

Ltac solve_v1 H tp'0 k'0 H' :=
  eapply H with (tp':=tp'0) (k':=k'0) in H';
  try lia;
  try (
  destruct H' as [r'' I1];
  repeat ec; try apply I1).

Lemma RIncs_nxt tp k r r' tp' k':
  RIncs tp k r r' ->
  match tp,tp' with
  | h100,h100 => k<=k'
  | h100,h000 => 1+k<=k'
  | h000,h000 => k<=k'
  | h000,h0 => k*4<=k'
  | h100,h0 => 4+k*4<=k'
  | h0,h100 => k<=k'
  | h0,h000 => k<=k'
  | h0,h0 => k*4<=k'
  | _,_ => False
  end ->
  exists r'',
  RIncs tp' k' r' r''.
Proof.
  gen tp k r' tp' k'.
  induction r; intros.
  {
    gen tp r' tp' k'.
    induction k using lt_wf_ind.
    intros.
    inverts H1; destruct tp'.
    all: try lia.
    - solve_v2.
    - destruct (sub k' 1); [subst|lia].
      solve_v2.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v2.
      + solve_v2.
    - destruct (mod2 k'); subst.
      + destruct (sub a 1); [subst|lia].
        solve_v2.
      + solve_v2.
    - destruct (mod2 k'); subst.
      + destruct (sub a 1); [subst|lia].
        solve_v2.
      + destruct (sub a 1); [subst|lia].
        solve_v2.
    - destruct (mod2 k'); subst.
      + destruct (sub a 2); [subst|lia].
        destruct (mod2 c); subst.
        * solve_v2.
        * solve_v2.
      + destruct (sub a 2); [subst|lia].
        destruct (mod2 c); subst.
        * solve_v2.
        * solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v1 H0 h0 (k'*2) H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h0 (c*2) H3.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 (1+a) H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h0 (c*2) H3.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 (1+a) H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - solve_v1 H0 h0 (k'*2) H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h0 (c*2) H3.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
  }
  {
    inverts H0; destruct tp'.
    all: try lia.
    - solve_v1 IHr h100 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h100 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
  }
Qed.

Open Scope sym.

Notation lh := (0inf<*<[1]).
Notation lh' := (0inf<*<[1;1]).

Lemma LRst:
  sideRLs (flip tm) [(hL,hR)] lh lh'.
Proof.
  esc.
Qed.

Definition S' r :=
  lh {{{ (hR,R) }}} toH h100 *> toRC r.

Lemma BigStep r r':
  RIncs h100 2 r r' ->
  S' r -->+ S' r'.
Proof.
  intros H.
  apply RIncs_spec in H.
  follow10 (sideRLs_concat LRst H).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD;D0;D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs h100 2 r r').
  2: {
    do 5 ec.
    change (1+0) with (1+0*2).
    do 2 ec.
  }
  intros r [r' I1].
  pose proof I1 as I2.
  eapply RIncs_nxt with (tp':=h100) (k':=2) in I2.
  2: lia.
  exists r'; split.
  - apply BigStep,I1.
  - apply I2.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LE_0RA0LB_1RF0LD_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;0;0;1;0;0].
Notation d0 := [0;0;0;0].
Notation d1 := [1;0;0;0].
Notation hR := (A,[0]).
Notation hL := (C,[0]).
Notation h := [(hR,hL)].

Inductive RD := LD|D0|D1.
Inductive H := h100|h000|h0.

Fixpoint toRC ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Definition toH x :=
match x with
| h100 => [1;0;0]
| h000 => [0;0;0]
| h0 => [0]
end.

Inductive RIncs: H->nat->(list RD)->(list RD)->Prop :=
| RIncs_100_ld k r r':
  RIncs h100 (k*2) r r' ->
  RIncs h100 k (LD::r) (LD::r')
| RIncs_000_ld k r r':
  RIncs h100 (k*2) r r' ->
  RIncs h000 (1+k) (LD::r) (LD::r')
| RIncs_0_ld_0 k r r':
  RIncs h100 k r r' ->
  RIncs h0 (2+k*2) (LD::r) (D0::r')
| RIncs_0_ld_1 k r r':
  RIncs h100 k r r' ->
  RIncs h0 (3+k*2) (LD::r) (D1::r')

| RIncs_100_d0_0 k r r':
  RIncs h000 k r r' ->
  RIncs h100 (k*2) (D0::r) (D1::r')
| RIncs_100_d0_1 k r r':
  RIncs h000 (1+k) r r' ->
  RIncs h100 (1+k*2) (D0::r) (D0::r')
| RIncs_000_d0_0 k r r':
  RIncs h000 k r r' ->
  RIncs h000 (k*2) (D0::r) (D0::r')
| RIncs_000_d0_1 k r r':
  RIncs h000 k r r' ->
  RIncs h000 (1+k*2) (D0::r) (D1::r')
| RIncs_0_d0_0 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (k*2) (D0::r) (D0::r')
| RIncs_0_d0_1 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (1+k*2) (D0::r) (D1::r')

| RIncs_100_d1 k r r':
  RIncs h0 (k*2) r r' ->
  RIncs h100 k (D1::r) (LD::r')
| RIncs_000_d1 k r r':
  RIncs h0 (k*2) r r' ->
  RIncs h000 (1+k) (D1::r) (LD::r')
| RIncs_0_d1_0 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (2+k*2) (D1::r) (D0::r')
| RIncs_0_d1_1 k r r':
  RIncs h0 k r r' ->
  RIncs h0 (3+k*2) (D1::r) (D1::r')

| RIncs_100_rh:
  RIncs h100 0 [] [D1]
| RIncs_100_rh':
  RIncs h100 1 [] [D0;D1]
| RIncs_000_rh:
  RIncs h000 0 [] []
| RIncs_0_rh:
  RIncs h0 0 [] []

| RIncs_100_rh_0 k r':
  RIncs h000 (1+k) [] r' ->
  RIncs h100 (2+k*2) [] (D1::r')
| RIncs_100_rh_1 k r':
  RIncs h000 (2+k) [] r' ->
  RIncs h100 (3+k*2) [] (D0::r')
| RIncs_000_rh_0 k r':
  RIncs h000 (1+k) [] r' ->
  RIncs h000 (2+k*2) [] (D0::r')
| RIncs_000_rh_1 k r':
  RIncs h000 k [] r' ->
  RIncs h000 (1+k*2) [] (D1::r')
| RIncs_0_rh_0 k r':
  RIncs h0 (1+k) [] r' ->
  RIncs h0 (2+k*2) [] (D0::r')
| RIncs_0_rh_1 k r':
  RIncs h0 k [] r' ->
  RIncs h0 (1+k*2) [] (D1::r')
.

Ltac cat6 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_;_;_]) (w2:=[_;_;_;_;_;_]); [|eauto 1].

Ltac cat4 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_]) (w2:=[_;_;_;_]); [|eauto 1].

Ltac cat4' :=
  do 4 rewrite const_unfold; cat4.

Open Scope nat.

Lemma RIncs_spec tp k r r':
  RIncs tp k r r' ->
  sideRLs tm (h^^k) (toH tp*>toRC r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toH toRC] in *.
  - cat6. am 1 2 k 0 0.
  - cat6. am 1 2 k 1 0.
  - cat4. am 2 1 k 2 0.
  - cat4. am 2 1 k 3 0.

  - cat4. am 2 1 k 0 0.
  - cat4. am 2 1 k 1 1.
  - cat4. am 2 1 k 0 0.
  - cat4. am 2 1 k 1 0.
  - cat4. am 2 1 k 0 0.
  - cat4. am 2 1 k 1 0.

  - cat6. am 1 2 k 0 0.
  - cat6. am 1 2 k 1 0.
  - cat4. am 2 1 k 2 0.
  - cat4. am 2 1 k 3 0.

  - esc.
  - esc.
  - esc.
  - esc.
  - cat4'. am 2 1 (1+k) 0 0.
  - cat4'. am 2 1 (1+k) 1 1.
  - cat4'. am 2 1 (1+k) 0 0.
  - cat4'. am 2 1 k 1 0.
  - cat4'. am 2 1 (1+k) 0 0.
  - cat4'. am 2 1 k 1 0.
Qed.


Lemma RIncs_nxt_0 k:
  exists r, RIncs h0 k [] r.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  + ec. ec.
  + destruct (mod2 k); subst.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
  Unshelve. all: lia.
Qed.

Lemma RIncs_nxt_000 k:
  exists r, RIncs h000 k [] r.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  + ec. ec.
  + destruct (mod2 k); subst.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
  Unshelve. all: lia.
Qed.

Lemma RIncs_nxt_100 k:
  exists r, RIncs h100 k [] r.
Proof.
  destruct k as [|[|k]].
  - ec. ec.
  - ec. ec.
  - destruct (mod2 k); subst.
    * epose proof (RIncs_nxt_000 _) as [r I].
      ec. ec. apply I.
    * epose proof (RIncs_nxt_000 _) as [r I].
      ec. ec. apply I.
Qed.

Ltac solve_v2 :=
  (epose proof (RIncs_nxt_0 _) as [r I]; repeat ec; apply I) ||
  (epose proof (RIncs_nxt_000 _) as [r I]; repeat ec; apply I) ||
  (epose proof (RIncs_nxt_100 _) as [r I]; repeat ec; apply I).

Ltac solve_v1 H tp'0 k'0 H' :=
  eapply H with (tp':=tp'0) (k':=k'0) in H';
  try lia;
  try (
  destruct H' as [r'' I1];
  repeat ec; try apply I1).

Lemma RIncs_nxt tp k r r' tp' k':
  RIncs tp k r r' ->
  match tp,tp' with
  | h100,h100 => k<=k'
  | h100,h000 => 1+k<=k'
  | h000,h000 => k<=k'
  | h000,h0 => k*4<=k'
  | h100,h0 => 4+k*4<=k'
  | h0,h100 => k<=k'
  | h0,h000 => k<=k'
  | h0,h0 => k*4<=k'
  | _,_ => False
  end ->
  exists r'',
  RIncs tp' k' r' r''.
Proof.
  gen tp k r' tp' k'.
  induction r; intros.
  {
    gen tp r' tp' k'.
    induction k using lt_wf_ind.
    intros.
    inverts H1; destruct tp'.
    all: try lia.
    - solve_v2.
    - destruct (sub k' 1); [subst|lia].
      solve_v2.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v2.
      + solve_v2.
    - destruct (mod2 k'); subst.
      + destruct (sub a 1); [subst|lia].
        solve_v2.
      + solve_v2.
    - destruct (mod2 k'); subst.
      + destruct (sub a 1); [subst|lia].
        solve_v2.
      + destruct (sub a 1); [subst|lia].
        solve_v2.
    - destruct (mod2 k'); subst.
      + destruct (sub a 2); [subst|lia].
        destruct (mod2 c); subst.
        * solve_v2.
        * solve_v2.
      + destruct (sub a 2); [subst|lia].
        destruct (mod2 c); subst.
        * solve_v2.
        * solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v2.
    - solve_v1 H0 h0 (k'*2) H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h0 (c*2) H3.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 (1+a) H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h0 (c*2) H3.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 (1+a) H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h000 a H3.
      + solve_v1 H0 h000 a H3.
    - destruct (mod2 k'); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
    - solve_v1 H0 h0 (k'*2) H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h0 (c*2) H3.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h0 a H3.
      + solve_v1 H0 h0 a H3.
  }
  {
    inverts H0; destruct tp'.
    all: try lia.
    - solve_v1 IHr h100 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h100 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h100 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h100 a H7.
      + solve_v1 IHr h100 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 (1+a) H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h000 a H7.
      + solve_v1 IHr h000 a H7.
    - destruct (mod2 k'); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
    - solve_v1 IHr h0 (k'*2) H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h0 (c*2) H7.
    - destruct (sub k' 2); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h0 a H7.
      + solve_v1 IHr h0 a H7.
  }
Qed.

Open Scope sym.

Notation lh := (0inf<*<[1]).
Notation lh' := (0inf<*<[1;1]).

Lemma LRst:
  sideRLs (flip tm) [(hL,hR)] lh lh'.
Proof.
  esc.
Qed.

Definition S' r :=
  lh {{{ (hR,R) }}} toH h100 *> toRC r.

Lemma BigStep r r':
  RIncs h100 2 r r' ->
  S' r -->+ S' r'.
Proof.
  intros H.
  apply RIncs_spec in H.
  follow10 (sideRLs_concat LRst H).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD;D0;D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs h100 2 r r').
  2: {
    do 5 ec.
    change (1+0) with (1+0*2).
    do 2 ec.
  }
  intros r [r' I1].
  pose proof I1 as I2.
  eapply RIncs_nxt with (tp':=h100) (k':=2) in I2.
  2: lia.
  exists r'; split.
  - apply BigStep,I1.
  - apply I2.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RE_0LC1LB_1RD1LB_1RA0LB_0RD0RF_---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1;1].
Notation d0 := [1;0;1].
Notation d1 := [1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (A,[]).
Notation hL := (B,[]).
Notation h := [(hR,hL)].

Inductive RD := LD|D0|D1.

Fixpoint toRC ls :=
match ls with
| [] => [1]*>0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Fixpoint toRC' ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC' ls
| D0::ls => [0;1;1]*>toRC' ls
| D1::ls => [0;0;1]*>toRC' ls
end.

Lemma toRC_shift ls:
  toRC ls = [1] *> toRC' ls.
Proof.
  induction ls as [|[] ls]; cbn in *; congruence.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} [1] *> r -->*
  lh {{{ (hR,R) }}} ld *> r.
Proof.
  er.
Qed.


Inductive RIncs: nat->(list RD)->(list RD)->Prop :=
| RIncs_LD k r r':
  RIncs (k*2) r r' ->
  RIncs k (LD::r) (LD::r')
| RIncs_D0 k r r':
  RIncs (k*2) r r' ->
  RIncs (1+k) (D0::r) (LD::r')
| RIncs_D1_0 k r r':
  RIncs (k) r r' ->
  RIncs (1+k*2) (D1::r) (D0::r')
| RIncs_D1_1 k r r':
  RIncs (k) r r' ->
  RIncs (2+k*2) (D1::r) (D1::r')
| RIncs_rh_0:
  RIncs 1 [] []
| RIncs_rh_1 k r:
  RIncs k [] r ->
  RIncs (1+k*2) [] (D1::r)
| RIncs_rh_2 k r:
  RIncs (1+k) [] r ->
  RIncs (2+k*2) [] (D0::r)
.

Ltac cat' :=
  eapply segRLs_sideRLs_concat; [|eauto 1].

Ltac cat'' :=
  replace 0inf with ([0;0;0]*>0inf) by (st; reflexivity); cat'.

Open Scope nat.

Lemma RIncs_spec k r r':
  RIncs k r r' ->
  sideRLs tm (h^^k) (toRC' r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toRC toRC'] in *.
  - cat'. am 1 2 k 0 0.
  - cat'. am 1 2 k 1 0.
  - cat'. am 2 1 k 1 0.
  - cat'. am 2 1 k 2 0.
  - esc.
  - cat''. am 2 1 k 1 0.
  - cat''. am 2 1 k 2 1.
Qed.

Ltac solve_v1 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _) as [r'' I1]; [lia|repeat ec; apply I1].

Ltac solve_v2 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _ _) as [r'' I1]; [lia|lia|repeat ec; apply I1].


Lemma RIncs_nxt k r r' k':
  RIncs k r r' ->
  k<=k' ->
  exists r'',
  RIncs k' r' r''.
Proof.
  intro H.
  gen k'.
  induction H; intros.
  - solve_v1 IHRIncs (k'*2).
  - solve_v1 IHRIncs (k'*2).
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - gen H.
    induction k' using lt_wf_ind; intros.
    destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + destruct a.
      * ec; ec.
      * solve_v2 H (S a).
    + solve_v2 H (1+a).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
Qed.

Definition S' ls := lh {{{ (hR,R) }}} toRC' ls.

Lemma RIncs' r r':
  RIncs 1 r r' ->
  S' r -->+
  S' (LD::r').
Proof.
  unfold S'.
  intros.
  epose proof H as H'.
  apply RIncs_spec in H'.
  eapply sideRLs_1 in H'.
  follow10 H'.
  rewrite toRC_shift.
  follow LRst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD;D0]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs 1 r r').
  2: repeat ec.
  intros r [r' I1].
  epose proof I1 as I2.
  apply RIncs' in I2.
  ec; ec.
  1: apply I2.
  eapply RIncs_nxt in I1.
  destruct I1 as [r'' I1].
  ec. ec.
  - apply I1.
  - lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC0LD_1RD1RE_0LA1LD_0RB0RF_---0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1;1].
Notation d0 := [1;0;1].
Notation d1 := [1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (C,[]).
Notation hL := (D,[]).
Notation h := [(hR,hL)].

Inductive RD := LD|D0|D1.

Fixpoint toRC ls :=
match ls with
| [] => [1]*>0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Fixpoint toRC' ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC' ls
| D0::ls => [0;1;1]*>toRC' ls
| D1::ls => [0;0;1]*>toRC' ls
end.

Lemma toRC_shift ls:
  toRC ls = [1] *> toRC' ls.
Proof.
  induction ls as [|[] ls]; cbn in *; congruence.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} [1] *> r -->*
  lh {{{ (hR,R) }}} ld *> r.
Proof.
  er.
Qed.


Inductive RIncs: nat->(list RD)->(list RD)->Prop :=
| RIncs_LD k r r':
  RIncs (k*2) r r' ->
  RIncs k (LD::r) (LD::r')
| RIncs_D0 k r r':
  RIncs (k*2) r r' ->
  RIncs (1+k) (D0::r) (LD::r')
| RIncs_D1_0 k r r':
  RIncs (k) r r' ->
  RIncs (1+k*2) (D1::r) (D0::r')
| RIncs_D1_1 k r r':
  RIncs (k) r r' ->
  RIncs (2+k*2) (D1::r) (D1::r')
| RIncs_rh_0:
  RIncs 1 [] []
| RIncs_rh_1 k r:
  RIncs k [] r ->
  RIncs (1+k*2) [] (D1::r)
| RIncs_rh_2 k r:
  RIncs (1+k) [] r ->
  RIncs (2+k*2) [] (D0::r)
.

Ltac cat' :=
  eapply segRLs_sideRLs_concat; [|eauto 1].

Ltac cat'' :=
  replace 0inf with ([0;0;0]*>0inf) by (st; reflexivity); cat'.

Open Scope nat.

Lemma RIncs_spec k r r':
  RIncs k r r' ->
  sideRLs tm (h^^k) (toRC' r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toRC toRC'] in *.
  - cat'. am 1 2 k 0 0.
  - cat'. am 1 2 k 1 0.
  - cat'. am 2 1 k 1 0.
  - cat'. am 2 1 k 2 0.
  - esc.
  - cat''. am 2 1 k 1 0.
  - cat''. am 2 1 k 2 1.
Qed.

Ltac solve_v1 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _) as [r'' I1]; [lia|repeat ec; apply I1].

Ltac solve_v2 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _ _) as [r'' I1]; [lia|lia|repeat ec; apply I1].


Lemma RIncs_nxt k r r' k':
  RIncs k r r' ->
  k<=k' ->
  exists r'',
  RIncs k' r' r''.
Proof.
  intro H.
  gen k'.
  induction H; intros.
  - solve_v1 IHRIncs (k'*2).
  - solve_v1 IHRIncs (k'*2).
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - gen H.
    induction k' using lt_wf_ind; intros.
    destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + destruct a.
      * ec; ec.
      * solve_v2 H (S a).
    + solve_v2 H (1+a).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
Qed.

Definition S' ls := lh {{{ (hR,R) }}} toRC' ls.

Lemma RIncs' r r':
  RIncs 1 r r' ->
  S' r -->+
  S' (LD::r').
Proof.
  unfold S'.
  intros.
  epose proof H as H'.
  apply RIncs_spec in H'.
  eapply sideRLs_1 in H'.
  follow10 H'.
  rewrite toRC_shift.
  follow LRst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs 1 r r').
  2: repeat ec.
  intros r [r' I1].
  epose proof I1 as I2.
  apply RIncs' in I2.
  ec; ec.
  1: apply I2.
  eapply RIncs_nxt in I1.
  destruct I1 as [r'' I1].
  ec. ec.
  - apply I1.
  - lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC1LB_1RD1LB_1RA0LB_0RD0RF_---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1;1].
Notation d0 := [1;0;1].
Notation d1 := [1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (A,[]).
Notation hL := (B,[]).
Notation h := [(hR,hL)].

Inductive RD := LD|D0|D1.

Fixpoint toRC ls :=
match ls with
| [] => [1]*>0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Fixpoint toRC' ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC' ls
| D0::ls => [0;1;1]*>toRC' ls
| D1::ls => [0;0;1]*>toRC' ls
end.

Lemma toRC_shift ls:
  toRC ls = [1] *> toRC' ls.
Proof.
  induction ls as [|[] ls]; cbn in *; congruence.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} [1] *> r -->*
  lh {{{ (hR,R) }}} ld *> r.
Proof.
  er.
Qed.


Inductive RIncs: nat->(list RD)->(list RD)->Prop :=
| RIncs_LD k r r':
  RIncs (k*2) r r' ->
  RIncs k (LD::r) (LD::r')
| RIncs_D0 k r r':
  RIncs (k*2) r r' ->
  RIncs (1+k) (D0::r) (LD::r')
| RIncs_D1_0 k r r':
  RIncs (k) r r' ->
  RIncs (1+k*2) (D1::r) (D0::r')
| RIncs_D1_1 k r r':
  RIncs (k) r r' ->
  RIncs (2+k*2) (D1::r) (D1::r')
| RIncs_rh_0:
  RIncs 1 [] []
| RIncs_rh_1 k r:
  RIncs k [] r ->
  RIncs (1+k*2) [] (D1::r)
| RIncs_rh_2 k r:
  RIncs (1+k) [] r ->
  RIncs (2+k*2) [] (D0::r)
.

Ltac cat' :=
  eapply segRLs_sideRLs_concat; [|eauto 1].

Ltac cat'' :=
  replace 0inf with ([0;0;0]*>0inf) by (st; reflexivity); cat'.

Open Scope nat.

Lemma RIncs_spec k r r':
  RIncs k r r' ->
  sideRLs tm (h^^k) (toRC' r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toRC toRC'] in *.
  - cat'. am 1 2 k 0 0.
  - cat'. am 1 2 k 1 0.
  - cat'. am 2 1 k 1 0.
  - cat'. am 2 1 k 2 0.
  - esc.
  - cat''. am 2 1 k 1 0.
  - cat''. am 2 1 k 2 1.
Qed.

Ltac solve_v1 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _) as [r'' I1]; [lia|repeat ec; apply I1].

Ltac solve_v2 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _ _) as [r'' I1]; [lia|lia|repeat ec; apply I1].


Lemma RIncs_nxt k r r' k':
  RIncs k r r' ->
  k<=k' ->
  exists r'',
  RIncs k' r' r''.
Proof.
  intro H.
  gen k'.
  induction H; intros.
  - solve_v1 IHRIncs (k'*2).
  - solve_v1 IHRIncs (k'*2).
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - gen H.
    induction k' using lt_wf_ind; intros.
    destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + destruct a.
      * ec; ec.
      * solve_v2 H (S a).
    + solve_v2 H (1+a).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
Qed.

Definition S' ls := lh {{{ (hR,R) }}} toRC' ls.

Lemma RIncs' r r':
  RIncs 1 r r' ->
  S' r -->+
  S' (LD::r').
Proof.
  unfold S'.
  intros.
  epose proof H as H'.
  apply RIncs_spec in H'.
  eapply sideRLs_1 in H'.
  follow10 H'.
  rewrite toRC_shift.
  follow LRst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD;D0]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs 1 r r').
  2: repeat ec.
  intros r [r' I1].
  epose proof I1 as I2.
  apply RIncs' in I2.
  ec; ec.
  1: apply I2.
  eapply RIncs_nxt in I1.
  destruct I1 as [r'' I1].
  ec. ec.
  - apply I1.
  - lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC0LD_1LD1RE_0LA1LD_0RB0RF_---0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1;1].
Notation d0 := [1;0;1].
Notation d1 := [1;0;0].
Notation lh := (0inf<*<[1;1]).

Notation hR := (C,[]).
Notation hL := (D,[]).
Notation h := [(hR,hL)].

Inductive RD := LD|D0|D1.

Fixpoint toRC ls :=
match ls with
| [] => [1]*>0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Fixpoint toRC' ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC' ls
| D0::ls => [0;1;1]*>toRC' ls
| D1::ls => [0;0;1]*>toRC' ls
end.

Lemma toRC_shift ls:
  toRC ls = [1] *> toRC' ls.
Proof.
  induction ls as [|[] ls]; cbn in *; congruence.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} [1] *> r -->*
  lh {{{ (hR,R) }}} ld *> r.
Proof.
  er.
Qed.


Inductive RIncs: nat->(list RD)->(list RD)->Prop :=
| RIncs_LD k r r':
  RIncs (k*2) r r' ->
  RIncs k (LD::r) (LD::r')
| RIncs_D0 k r r':
  RIncs (k*2) r r' ->
  RIncs (1+k) (D0::r) (LD::r')
| RIncs_D1_0 k r r':
  RIncs (k) r r' ->
  RIncs (1+k*2) (D1::r) (D0::r')
| RIncs_D1_1 k r r':
  RIncs (k) r r' ->
  RIncs (2+k*2) (D1::r) (D1::r')
| RIncs_rh_0:
  RIncs 1 [] []
| RIncs_rh_1 k r:
  RIncs k [] r ->
  RIncs (1+k*2) [] (D1::r)
| RIncs_rh_2 k r:
  RIncs (1+k) [] r ->
  RIncs (2+k*2) [] (D0::r)
.

Ltac cat' :=
  eapply segRLs_sideRLs_concat; [|eauto 1].

Ltac cat'' :=
  replace 0inf with ([0;0;0]*>0inf) by (st; reflexivity); cat'.

Open Scope nat.

Lemma RIncs_spec k r r':
  RIncs k r r' ->
  sideRLs tm (h^^k) (toRC' r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toRC toRC'] in *.
  - cat'. am 1 2 k 0 0.
  - cat'. am 1 2 k 1 0.
  - cat'. am 2 1 k 1 0.
  - cat'. am 2 1 k 2 0.
  - esc.
  - cat''. am 2 1 k 1 0.
  - cat''. am 2 1 k 2 1.
Qed.

Ltac solve_v1 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _) as [r'' I1]; [lia|repeat ec; apply I1].

Ltac solve_v2 H k :=
  let I1:=fresh "I" in
  unshelve epose proof (H k _ _) as [r'' I1]; [lia|lia|repeat ec; apply I1].


Lemma RIncs_nxt k r r' k':
  RIncs k r r' ->
  k<=k' ->
  exists r'',
  RIncs k' r' r''.
Proof.
  intro H.
  gen k'.
  induction H; intros.
  - solve_v1 IHRIncs (k'*2).
  - solve_v1 IHRIncs (k'*2).
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - gen H.
    induction k' using lt_wf_ind; intros.
    destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + destruct a.
      * ec; ec.
      * solve_v2 H (S a).
    + solve_v2 H (1+a).
  - destruct (sub k' 1); [subst|lia].
    destruct (mod2 c); subst.
    + solve_v1 IHRIncs a.
    + solve_v1 IHRIncs a.
  - destruct (sub k' 1); [subst|lia].
    solve_v1 IHRIncs (c*2).
Qed.

Definition S' ls := lh {{{ (hR,R) }}} toRC' ls.

Lemma RIncs' r r':
  RIncs 1 r r' ->
  S' r -->+
  S' (LD::r').
Proof.
  unfold S'.
  intros.
  epose proof H as H'.
  apply RIncs_spec in H'.
  eapply sideRLs_1 in H'.
  follow10 H'.
  rewrite toRC_shift.
  follow LRst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs 1 r r').
  2: repeat ec.
  intros r [r' I1].
  epose proof I1 as I2.
  apply RIncs' in I2.
  ec; ec.
  1: apply I2.
  eapply RIncs_nxt in I1.
  destruct I1 as [r'' I1].
  ec. ec.
  - apply I1.
  - lia.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1;0].
Notation d0 := [0;0;0].
Notation d1 := [1;0;0].
Notation hR := (B,@nil Sym).
Notation hR' := (D,[1]).
Notation hL := (C,@nil Sym).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].

Inductive RD := LD|D0|D1.
Inductive H := hx|h1.

Fixpoint toRC ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Definition toH' x :=
match x with
| hx => []
| h1 => [1]
end.

Definition toH x :=
match x with
| hx => h'
| h1 => []
end.

Inductive RIncs: H->nat->(list RD)->(list RD)->Prop :=
| RIncs_hx_ld k r r':
  RIncs hx (1+k) r r' ->
  RIncs hx k (LD::r) (LD::r')

| RIncs_hx_d1 k r r':
  RIncs h1 k r r' ->
  RIncs hx k (D1::r) (LD::r')

| RIncs_hx_d0 k r r':
  RIncs hx (1+k) r r' ->
  RIncs hx k (D0::r) (LD::r')

| RIncs_h1_ld k r r':
  RIncs hx (1+k) r r' ->
  RIncs h1 (1+k) (LD::r) (LD::r')

| RIncs_h1_d1 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (1+k) (D1::r) (LD::r')

| RIncs_h1_d0_0 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (1+k*2) (D0::r) (D0::r')

| RIncs_h1_d0_1 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (2+k*2) (D0::r) (D1::r')

| RIncs_h1_rh_0:
  RIncs h1 0 [] [D1]

| RIncs_h1_rh_1 k r':
  RIncs h1 k [] r' ->
  RIncs h1 (1+k*2) [] (D0::r')
| RIncs_h1_rh_2 k r':
  RIncs h1 k [] r' ->
  RIncs h1 (2+k*2) [] (D1::r')
.

Ltac cat3 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_]) (w2:=[_;_;_]); [|eauto 1].

Ltac tr1 :=
  rewrite lpow_add,app_assoc;
  eapply segRLs_trans; [esx | ].

Ltac wal :=
  eapply segRLs_wall''; esx.

Ltac tr2 :=
  eapply sideRLs_trans; [esx | ].

Open Scope nat.

Lemma RIncs_spec tp k r r':
  RIncs tp k r r' ->
  sideRLs tm (toH tp++h^^k) (toH' tp*>toRC r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toH toH' toRC] in *.
  - cat3; tr1; wal.
  - tr2.
    cat3; wal.
  - cat3; tr1; wal.
  - rewrite lpow_add,app_assoc.
    eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_]) (w2:=[_;_;_]); [|eauto 1].
    tr1; wal.
  - rewrite lpow_add,app_assoc.
    tr2.
    cat3; wal.
  - cat3.
    rewrite app_nil_l.
    am 2 1 k 1 1.
    rewrite Nat.add_comm,lpow_add,Nat.mul_1_r.
    tr2; eauto 1.
  - cat3.
    rewrite Nat.add_comm.
    am 2 1 k 2 1.
    rewrite Nat.add_comm,lpow_add,Nat.mul_1_r.
    tr2; eauto 1.
  - esc.
  - rewrite lpow_add,app_assoc.
    tr2.
    cat3.
    rewrite app_nil_l.
    am 2 1 k 0 0.
  - change (2+k*2) with (1+(1+k*2)).
    rewrite lpow_add,app_assoc.
    tr2.
    cat3.
    rewrite app_nil_l.
    am 2 1 k 1 0.
Qed.

Lemma RIncs_nxt_1 k:
  exists r, RIncs h1 k [] r.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  + ec. ec.
  + destruct (mod2 k); subst.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
  Unshelve. all: lia.
Qed.


Ltac solve_v2 :=
  (epose proof (RIncs_nxt_1 _) as [r I]; repeat ec; try apply I).

Ltac solve_v1 H tp'0 k'0 H' :=
  eapply H with (tp':=tp'0) (k':=k'0) in H';
  try lia;
  try (
  destruct H' as [r'' I1];
  repeat ec; try apply I1).

Lemma RIncs_nxt tp k r r' tp' k':
  RIncs tp k r r' ->
  match tp,tp' with
  | hx,hx => k<=k'
  | h1,h1 => k*2+1<=k'
  | h1,hx => k+1<=k'
  | _,_ => False
  end ->
  exists r'',
  RIncs tp' k' r' r''.
Proof.
  gen tp k r' tp' k'.
  induction r; intros.
  {
    gen tp r' tp' k'.
    induction k using lt_wf_ind.
    intros.
    inverts H1; destruct tp'.
    all: try lia.
    - solve_v2.
    - destruct (sub k' 1); [subst|lia].
      solve_v2.
    - solve_v1 H0 hx (1+k') H3.
    - destruct (sub k' 1); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h1 (a) H3.
      + solve_v1 H0 h1 (a) H3.
    - solve_v1 H0 h1 (k') H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h1 (c) H3.
  }
  {
    inverts H0; destruct tp'.
    all: try lia.
    - solve_v1 IHr hx (1+k') H7.
    - solve_v1 IHr hx (1+k') H7.
    - solve_v1 IHr hx (1+k') H7.
    - solve_v1 IHr hx (1+k') H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr hx (1+c) H7.
    - solve_v1 IHr hx (1+k') H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr hx (1+c) H7.
    - solve_v1 IHr hx (1+k') H7.
    - destruct (sub k' 1); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h1 (a) H7.
      + solve_v1 IHr h1 (a) H7.
    - solve_v1 IHr h1 k' H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h1 (c) H7.
  }
Qed.

Open Scope sym.

Notation lh := (0inf<*<[1]).

Definition S' r :=
  lh {{{ (hR',R) }}} toH' hx *> toRC r.

Lemma BigStep r r':
  RIncs hx 0 r r' ->
  S' r -->+ S' r'.
Proof.
  intros H.
  apply RIncs_spec in H.
  unfold S'.
  eapply sideRLs_1 in H.
  follow10 H.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs hx 0 r r').
  2: repeat ec.
  intros r [r' I1].
  pose proof I1 as I2.
  eapply RIncs_nxt with (tp':=hx) (k':=O) in I2.
  2: lia.
  exists r'; split.
  - apply BigStep,I1.
  - apply I2.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1;0].
Notation d0 := [0;0;0].
Notation d1 := [1;0;0].
Notation hR := (B,@nil Sym).
Notation hR' := (D,[1]).
Notation hL := (C,@nil Sym).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].

Inductive RD := LD|D0|D1.
Inductive H := hx|h1.

Fixpoint toRC ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Definition toH' x :=
match x with
| hx => []
| h1 => [1]
end.

Definition toH x :=
match x with
| hx => h'
| h1 => []
end.

Inductive RIncs: H->nat->(list RD)->(list RD)->Prop :=
| RIncs_hx_ld k r r':
  RIncs hx (1+k) r r' ->
  RIncs hx k (LD::r) (LD::r')

| RIncs_hx_d1 k r r':
  RIncs h1 k r r' ->
  RIncs hx k (D1::r) (LD::r')

| RIncs_hx_d0 k r r':
  RIncs hx (1+k) r r' ->
  RIncs hx k (D0::r) (LD::r')

| RIncs_h1_ld k r r':
  RIncs hx (1+k) r r' ->
  RIncs h1 (1+k) (LD::r) (LD::r')

| RIncs_h1_d1 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (1+k) (D1::r) (LD::r')

| RIncs_h1_d0_0 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (1+k*2) (D0::r) (D0::r')

| RIncs_h1_d0_1 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (2+k*2) (D0::r) (D1::r')

| RIncs_h1_rh_0:
  RIncs h1 0 [] [D1]

| RIncs_h1_rh_1 k r':
  RIncs h1 k [] r' ->
  RIncs h1 (1+k*2) [] (D0::r')
| RIncs_h1_rh_2 k r':
  RIncs h1 k [] r' ->
  RIncs h1 (2+k*2) [] (D1::r')
.

Ltac cat3 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_]) (w2:=[_;_;_]); [|eauto 1].

Ltac tr1 :=
  rewrite lpow_add,app_assoc;
  eapply segRLs_trans; [esx | ].

Ltac wal :=
  eapply segRLs_wall''; esx.

Ltac tr2 :=
  eapply sideRLs_trans; [esx | ].

Open Scope nat.

Lemma RIncs_spec tp k r r':
  RIncs tp k r r' ->
  sideRLs tm (toH tp++h^^k) (toH' tp*>toRC r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toH toH' toRC] in *.
  - cat3; tr1; wal.
  - tr2.
    cat3; wal.
  - cat3; tr1; wal.
  - rewrite lpow_add,app_assoc.
    eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_]) (w2:=[_;_;_]); [|eauto 1].
    tr1; wal.
  - rewrite lpow_add,app_assoc.
    tr2.
    cat3; wal.
  - cat3.
    rewrite app_nil_l.
    am 2 1 k 1 1.
    rewrite Nat.add_comm,lpow_add,Nat.mul_1_r.
    tr2; eauto 1.
  - cat3.
    rewrite Nat.add_comm.
    am 2 1 k 2 1.
    rewrite Nat.add_comm,lpow_add,Nat.mul_1_r.
    tr2; eauto 1.
  - esc.
  - rewrite lpow_add,app_assoc.
    tr2.
    cat3.
    rewrite app_nil_l.
    am 2 1 k 0 0.
  - change (2+k*2) with (1+(1+k*2)).
    rewrite lpow_add,app_assoc.
    tr2.
    cat3.
    rewrite app_nil_l.
    am 2 1 k 1 0.
Qed.

Lemma RIncs_nxt_1 k:
  exists r, RIncs h1 k [] r.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  + ec. ec.
  + destruct (mod2 k); subst.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
  Unshelve. all: lia.
Qed.


Ltac solve_v2 :=
  (epose proof (RIncs_nxt_1 _) as [r I]; repeat ec; try apply I).

Ltac solve_v1 H tp'0 k'0 H' :=
  eapply H with (tp':=tp'0) (k':=k'0) in H';
  try lia;
  try (
  destruct H' as [r'' I1];
  repeat ec; try apply I1).

Lemma RIncs_nxt tp k r r' tp' k':
  RIncs tp k r r' ->
  match tp,tp' with
  | hx,hx => k<=k'
  | h1,h1 => k*2+1<=k'
  | h1,hx => k+1<=k'
  | _,_ => False
  end ->
  exists r'',
  RIncs tp' k' r' r''.
Proof.
  gen tp k r' tp' k'.
  induction r; intros.
  {
    gen tp r' tp' k'.
    induction k using lt_wf_ind.
    intros.
    inverts H1; destruct tp'.
    all: try lia.
    - solve_v2.
    - destruct (sub k' 1); [subst|lia].
      solve_v2.
    - solve_v1 H0 hx (1+k') H3.
    - destruct (sub k' 1); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 H0 h1 (a) H3.
      + solve_v1 H0 h1 (a) H3.
    - solve_v1 H0 h1 (k') H3.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 H0 h1 (c) H3.
  }
  {
    inverts H0; destruct tp'.
    all: try lia.
    - solve_v1 IHr hx (1+k') H7.
    - solve_v1 IHr hx (1+k') H7.
    - solve_v1 IHr hx (1+k') H7.
    - solve_v1 IHr hx (1+k') H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr hx (1+c) H7.
    - solve_v1 IHr hx (1+k') H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr hx (1+c) H7.
    - solve_v1 IHr hx (1+k') H7.
    - destruct (sub k' 1); [subst|lia].
      destruct (mod2 c); subst.
      + solve_v1 IHr h1 (a) H7.
      + solve_v1 IHr h1 (a) H7.
    - solve_v1 IHr h1 k' H7.
    - destruct (sub k' 1); [subst|lia].
      solve_v1 IHr h1 (c) H7.
  }
Qed.

Open Scope sym.

Notation lh := (0inf<*<[1]).

Definition S' r :=
  lh {{{ (hR',R) }}} toH' hx *> toRC r.

Lemma BigStep r r':
  RIncs hx 0 r r' ->
  S' r -->+ S' r'.
Proof.
  intros H.
  apply RIncs_spec in H.
  unfold S'.
  eapply sideRLs_1 in H.
  follow10 H.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [D1]).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs hx 0 r r').
  2: repeat ec.
  intros r [r' I1].
  pose proof I1 as I2.
  eapply RIncs_nxt with (tp':=hx) (k':=O) in I2.
  2: lia.
  exists r'; split.
  - apply BigStep,I1.
  - apply I2.
Qed.

End TM8.


