From BusyCoq Require Import Individual62.

Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Inductive RD :=
| D00101
| D0011
| D0011001
| D001101
| D00111

| D00001

| D001
| D01

| D0011_011001
| D001111001
| D00101001

| D0011_011
| D001111

| D00011

| D0011_01101
| D00111101
| D0010101

| D0011_0111
| D0011111
| D001011

| D0011_000101
| D0011_00101
| D0011_0101
| D0011101

| D0000101
.

Inductive RT :=
| D001T
.

Inductive RC :=
| RC_S(x:RD)(n:N)(r:RC)
| RC_O(x:RT).

Definition toRD(x:RD) :=
match x with
| D00101 => [0;0;1;0;1]
| D0011 => [0;0;1;1]
| D0011001 => [0;0;1;1;0;0;1]
| D001101 => [0;0;1;1;0;1]
| D00111 => [0;0;1;1;1]

| D00001 => [0;0;0;0;1]

| D001 => [0;0;1]
| D01 => [0;1]

| D0011_011001 => [0;0;1;1;0;1;1;0;0;1]
| D001111001 => [0;0;1;1;1;1;0;0;1]
| D00101001 => [0;0;1;0;1;0;0;1]

| D0011_011 => [0;0;1;1;0;1;1]
| D001111 => [0;0;1;1;1;1]

| D00011 => [0;0;0;1;1]

| D0011_01101 => [0;0;1;1;0;1;1;0;1]
| D00111101 => [0;0;1;1;1;1;0;1]
| D0010101 => [0;0;1;0;1;0;1]

| D0011_0111 => [0;0;1;1;0;1;1;1]
| D0011111 => [0;0;1;1;1;1;1]
| D001011 => [0;0;1;0;1;1]

| D0011_000101 => [0;0;1;1;0;0;0;1;0;1]
| D0011_00101 => [0;0;1;1;0;0;1;0;1]
| D0011_0101 => [0;0;1;1;0;1;0;1]
| D0011101 => [0;0;1;1;1;0;1]

| D0000101 => [0;0;0;0;1;0;1]
end.

Definition toRT(x:RT):side :=
match x with
| D001T => [0;0;1] *> 0inf
end.

Notation w := [0;0;0;1].

Fixpoint toRC(x:RC):side :=
match x with
| RC_S x0 n x1 => toRD x0 *> w^^N.to_nat n *> toRC x1
| RC_O x0 => toRT x0
end.

Inductive Tp :=
| Tp0 | Tp1 | Tp2.

Definition N_OS(a:N):=
  if (a=?0)%N then None else Some (N.pred a).

Lemma N_OS_spec a:
  match N_OS a with
  | Some c => (a=1+c)%N
  | None => a = 0%N
  end.
Proof.
  unfold N_OS.
  destruct (N.eqb_spec a 0); lia.
Qed.

Fixpoint RInc(x:RC)(dep:nat){struct dep}:RC*N*Tp+RC :=
(match dep with
| O => inr x
| S dep =>
match x with
| RC_S a n r =>
  match a with
  | D00101 => 
    match N_OS n with
    | Some n => inl (RC_S D0011 n r,1,Tp0)
    | None =>
      match r with
      | RC_S D00101 n0 r0 =>
        match N_OS n0 with
        | Some n0 => inl (RC_S D0000101 n0 r0,1,Tp1)
        | None => inr x
        end
      | RC_S D0011001 n0 r0 => inl (RC_S D001 n0 r0,2,Tp0)
      | RC_S D001101 n0 r0 => inl (RC_S D01 n0 r0,2,Tp0)
      | RC_S D00111 n0 r0 => inl (RC_S D00011 n0 r0,1,Tp0)
      | _ => inr x
      end
    end
  | D0011 => 
    match N_OS n with
    | Some n => inl (RC_S D0011001 n r,0,Tp0)
    | None =>
      match r with
      | RC_S D01 n0 r0 => inl (RC_S D00111 n0 r0,0,Tp0)
      | RC_S D00101 n0 r0 => inl (RC_S D0011_0101 n0 r0,0,Tp0)
      | RC_S D0011 n0 r0 => inl (RC_S D0011_011 n0 r0,0,Tp0)
      | RC_S D0011001 n0 r0 => inl (RC_S D0011_011001 n0 r0,0,Tp0)
      | RC_S D001101 n0 r0 => inl (RC_S D0011_01101 n0 r0,0,Tp0)
      | RC_S D00111 n0 r0 => inl (RC_S D0011_0111 n0 r0,0,Tp0)
      | RC_S D0000101 n0 r0 => inl (RC_S D0011_000101 n0 r0,0,Tp0)
      | _ => inr x
      end
    end
  | D0011001 => inl (RC_S D001101 n r,0,Tp0)
  | D001101 => inl (RC_S D00111 n r,0,Tp0)
  | D00111 =>
    match RInc r dep with
    | inl (r,dn,Tp0) => inl (RC_S D00101 (n+dn) r,0,Tp0)
    | inl (r,dn,Tp1) => inl (r,1+n+dn,Tp2)
    | inl (r,dn,Tp2) =>
      match N_OS n with
      | Some n => inl (RC_S D00001 dn r,1+n,Tp2)
      | None => inr x
      end
    | inr e => inr e
    end
  | D00001 => inl (RC_S D0011 n r,0,Tp0)
  | D001 =>
    match N_OS n with
    | Some n => inl (RC_S D0011 n r,0,Tp1)
    | None => inr x
    end
  | D01 =>
    match N_OS n with
    | Some n => inl (RC_S D01 n r,0,Tp2)
    | None => inr x
    end

  | D0011_011001 => inl (RC_S D001111001 n r,0,Tp0)
  | D001111001 => inl (RC_S D00101001 n r,0,Tp0)
  | D00101001 =>
    match RInc r dep with
    | inl (r,dn,Tp0) => inl (r,2+n+dn,Tp0)
    | inr e => inr e
    | _ => inr x
    end

  | D0011_011 => inl (RC_S D001111 n r,0,Tp0)
  | D001111 => inl (RC_S D00101 n r,0,Tp0)
  | D00011 => inl (r,1+n,Tp0)

  | D0011_01101 => inl (RC_S D00111101 n r,0,Tp0)
  | D00111101 => inl (RC_S D0010101 n r,0,Tp0)
  | D0010101 =>
    match N_OS n with
    | Some n => inl (RC_S D0011 n r,1,Tp1)
    | None => inr x
    end

  | D0011_0111 => inl (RC_S D0011111 n r,0,Tp0)
  | D0011111 => inl (RC_S D001011 n r,0,Tp0)
  | D001011 =>
    match N_OS n with
    | Some n => inl (RC_S D0011001 n r,0,Tp1)
    | None => inr x
    end

  | D0011_000101 => inl (RC_S D0011_00101 n r,0,Tp0)
  | D0011_00101 => inl (RC_S D0011_0101 n r,0,Tp0)
  | D0011_0101 => inl (RC_S D0011101 n r,0,Tp0)
  | D0011101 =>
    match N_OS n with
    | Some n => inl (RC_S D0000101 n r,0,Tp2)
    | None => inr x
    end

  | D0000101 => inl (RC_S D001101 n r,0,Tp0)
  end
| RC_O a =>
  match a with
  | D001T => inl (RC_O D001T,0,Tp1)
  end
end
end)%N.

Definition maxD := 1000%nat.

Definition Inc(x:N*RC):N*RC+RC :=
match x with
| (n,r) =>
  match RInc r maxD with
  | inl (r,dn,Tp0) => inl ((n+dn+1)%N,r)
  | inl (r,dn,Tp1) => inl (1%N,(RC_S D0011 (n+dn)%N r))
  | inl (r,dn,Tp2) =>
    match N_OS n with
    | Some n => inl (1%N,(RC_S D0011 n (RC_S D00001 dn r)))
    | None => inr r
    end
  | inr e => inr e
  end
end.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0RC_0LC0LB_1RD0LE_0RE1RF_1RA0RB_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition toC(x:N*RC) :=
match x with
| (n,r) => 0inf {{C}}> w^^N.to_nat n *> toRC r
end.

Ltac solve_N_OS :=
  repeat
  match goal with
  | |- match match N_OS ?a with _ => _ end with _ => _ end =>
    let I:=fresh "I" in
    epose proof (N_OS_spec a) as I;
    destruct (N_OS a);
    subst
  end.

Ltac solve_v1 :=
  trivial;
  intros;
  solve_N_OS;
  trivial;
  cbn[toRC];
  cbn[toC];
  repeat rewrite Nnat.N2Nat.inj_add;
  try solve[es].

Lemma RInc_spec x dep:
  match RInc x dep with
  | inl (x',n,Tp0) => forall l, l {{C}}> toRC x -->* l <{{E}} [0] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp1) => forall l, l {{C}}> toRC x -->* l <{{B}} [0;0;1] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp2) => forall l, l {{C}}> toRC x -->* l <{{B}} [0;0;0;1] *> w^^N.to_nat n *> toRC x'
  | inr _ => True
  end.
Proof.
  gen x.
  induction dep; cbn[RInc]; intros.
  1: trivial.
  destruct x as [[] n x|[]]; solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow IHdep. solve_v1.
    + es; er. follow IHdep. solve_v1.
    + es; er. follow IHdep. solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow IHdep. solve_v1.
Qed.

Lemma Inc_spec x:
  match Inc x with
  | inl x' => toC x -->+ toC x'
  | _ => True
  end.
Proof.
  destruct x as [n r].
  unfold Inc.
  epose proof (RInc_spec r maxD).
  destruct (RInc r maxD) as [[[x' dn] []]|]; solve_v1.
  - es; er. follow H. solve_v1.
  - es; er. follow H. solve_v1.
  - es; er. follow H. solve_v1.
Qed.

Definition x0:N*RC := (1,RC_S D0011 14 (RC_S D0011 5 (RC_O D001T)))%N.

Lemma init:
  c0 -->* toC x0.
Proof.
  esx.
Qed.

Import Eqb.

Definition S' r :=
  toC (1%N, RC_S D0011 33 (RC_S D00001 416889 (RC_S D00001 0 (RC_S D0000101 31217 r)))).

Definition Inc_n n x :=
  N_iter_until Inc x n.

Lemma Inc_n_spec n x:
  match Inc_n n (inl x) with
  | inl x' => toC x -->* toC x'
  | _ => True
  end.
Proof.
  unfold Inc_n.
  eapply N_iter_until_spec.
  2: finish.
  intros.
  pose proof (Inc_spec x1).
  destruct (Inc x1); trivial.
  follow H.
  follow100 H0.
  finish.
Qed.

Definition Inc_Sn n x :=
  match Inc x with
  | inl x => Inc_n n (inl x)
  | inr x => inr x
  end.

Lemma Inc_Sn_spec n x x':
  Inc_Sn n x = inl x' ->
  toC x -->+ toC x'.
Proof.
  unfold Inc_Sn.
  intros.
  pose proof (Inc_spec x).
  destruct (Inc x); try congruence.
  epose proof (Inc_n_spec _ _) as I1.
  rewrite H in I1.
  follow10 H0.
  apply I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply multistep_nonhalt.
  1: eapply progress_evstep.
  1: eapply (Inc_Sn_spec 1333816).
  1: time native_compute; reflexivity.
  eapply progress_nonhalt_simple with (C:=S').
  intros x.
  eexists.
  eapply (Inc_Sn_spec 669179).
  time native_compute; reflexivity.
Time Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition toC(x:N*RC) :=
match x with
| (n,r) => 0inf {{D}}> w^^N.to_nat n *> toRC r
end.

Ltac solve_N_OS :=
  repeat
  match goal with
  | |- match match N_OS ?a with _ => _ end with _ => _ end =>
    let I:=fresh "I" in
    epose proof (N_OS_spec a) as I;
    destruct (N_OS a);
    subst
  end.

Ltac solve_v1 :=
  trivial;
  intros;
  solve_N_OS;
  trivial;
  cbn[toRC];
  cbn[toC];
  repeat rewrite Nnat.N2Nat.inj_add;
  try solve[es].

Lemma RInc_spec x dep:
  match RInc x dep with
  | inl (x',n,Tp0) => forall l, l {{D}}> toRC x -->* l <{{A}} [0] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp1) => forall l, l {{D}}> toRC x -->* l <{{C}} [0;0;1] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp2) => forall l, l {{D}}> toRC x -->* l <{{C}} [0;0;0;1] *> w^^N.to_nat n *> toRC x'
  | inr _ => True
  end.
Proof.
  gen x.
  induction dep; cbn[RInc]; intros.
  1: trivial.
  destruct x as [[] n x|[]]; solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow IHdep. solve_v1.
    + es; er. follow IHdep. solve_v1.
    + es; er. follow IHdep. solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow IHdep. solve_v1.
Qed.

Lemma Inc_spec x:
  match Inc x with
  | inl x' => toC x -->+ toC x'
  | _ => True
  end.
Proof.
  destruct x as [n r].
  unfold Inc.
  epose proof (RInc_spec r maxD).
  destruct (RInc r maxD) as [[[x' dn] []]|]; solve_v1.
  - es; er. follow H. solve_v1.
  - es; er. follow H. solve_v1.
  - es; er. follow H. solve_v1.
Qed.

Definition x0:N*RC := (1,RC_S D0011 27 (RC_S D00001 8 (RC_O D001T)))%N.

Lemma init:
  c0 -->* toC x0.
Proof.
  esx.
Qed.

Import Eqb.

Definition S' r :=
  toC (1%N, RC_S D0011 33 (RC_S D00001 416889 (RC_S D00001 0 (RC_S D0000101 31217 r)))).

Definition Inc_n n x :=
  N_iter_until Inc x n.

Lemma Inc_n_spec n x:
  match Inc_n n (inl x) with
  | inl x' => toC x -->* toC x'
  | _ => True
  end.
Proof.
  unfold Inc_n.
  eapply N_iter_until_spec.
  2: finish.
  intros.
  pose proof (Inc_spec x1).
  destruct (Inc x1); trivial.
  follow H.
  follow100 H0.
  finish.
Qed.

Definition Inc_Sn n x :=
  match Inc x with
  | inl x => Inc_n n (inl x)
  | inr x => inr x
  end.

Lemma Inc_Sn_spec n x x':
  Inc_Sn n x = inl x' ->
  toC x -->+ toC x'.
Proof.
  unfold Inc_Sn.
  intros.
  pose proof (Inc_spec x).
  destruct (Inc x); try congruence.
  epose proof (Inc_n_spec _ _) as I1.
  rewrite H in I1.
  follow10 H0.
  apply I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply multistep_nonhalt.
  1: eapply progress_evstep.
  1: eapply (Inc_Sn_spec 1339069).
  1: time native_compute; reflexivity.
  eapply progress_nonhalt_simple with (C:=S').
  intros x.
  eexists.
  eapply (Inc_Sn_spec 669179).
  time native_compute; reflexivity.
Time Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition toC(x:N*RC) :=
match x with
| (n,r) => 0inf {{A}}> w^^N.to_nat n *> toRC r
end.

Ltac solve_N_OS :=
  repeat
  match goal with
  | |- match match N_OS ?a with _ => _ end with _ => _ end =>
    let I:=fresh "I" in
    epose proof (N_OS_spec a) as I;
    destruct (N_OS a);
    subst
  end.

Ltac solve_v1 :=
  trivial;
  intros;
  solve_N_OS;
  trivial;
  cbn[toRC];
  cbn[toC];
  repeat rewrite Nnat.N2Nat.inj_add;
  try solve[es].

Lemma RInc_spec x dep:
  match RInc x dep with
  | inl (x',n,Tp0) => forall l, l {{A}}> toRC x -->* l <{{C}} [0] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp1) => forall l, l {{A}}> toRC x -->* l <{{E}} [0;0;1] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp2) => forall l, l {{A}}> toRC x -->* l <{{E}} [0;0;0;1] *> w^^N.to_nat n *> toRC x'
  | inr _ => True
  end.
Proof.
  gen x.
  induction dep; cbn[RInc]; intros.
  1: trivial.
  destruct x as [[] n x|[]]; solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow IHdep. solve_v1.
    + es; er. follow IHdep. solve_v1.
    + es; er. follow IHdep. solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow IHdep. solve_v1.
Qed.

Lemma Inc_spec x:
  match Inc x with
  | inl x' => toC x -->+ toC x'
  | _ => True
  end.
Proof.
  destruct x as [n r].
  unfold Inc.
  epose proof (RInc_spec r maxD).
  destruct (RInc r maxD) as [[[x' dn] []]|]; solve_v1.
  - es; er. follow H. solve_v1.
  - es; er. follow H. solve_v1.
  - es; er. follow H. solve_v1.
Qed.

Definition x0:N*RC := (1,RC_S D0011 15 (RC_O D001T))%N.

Lemma init:
  c0 -->* toC x0.
Proof.
  esx.
Qed.

Import Eqb.

Definition S' r :=
  toC (1%N, RC_S D0011 33 (RC_S D00001 416889 (RC_S D00001 0 (RC_S D0000101 31217 r)))).

Definition Inc_n n x :=
  N_iter_until Inc x n.

Lemma Inc_n_spec n x:
  match Inc_n n (inl x) with
  | inl x' => toC x -->* toC x'
  | _ => True
  end.
Proof.
  unfold Inc_n.
  eapply N_iter_until_spec.
  2: finish.
  intros.
  pose proof (Inc_spec x1).
  destruct (Inc x1); trivial.
  follow H.
  follow100 H0.
  finish.
Qed.

Definition Inc_Sn n x :=
  match Inc x with
  | inl x => Inc_n n (inl x)
  | inr x => inr x
  end.

Lemma Inc_Sn_spec n x x':
  Inc_Sn n x = inl x' ->
  toC x -->+ toC x'.
Proof.
  unfold Inc_Sn.
  intros.
  pose proof (Inc_spec x).
  destruct (Inc x); try congruence.
  epose proof (Inc_n_spec _ _) as I1.
  rewrite H in I1.
  follow10 H0.
  apply I1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply multistep_nonhalt.
  1: eapply progress_evstep.
  1: eapply (Inc_Sn_spec 1333831).
  1: time native_compute; reflexivity.
  eapply progress_nonhalt_simple with (C:=S').
  intros x.
  eexists.
  eapply (Inc_Sn_spec 669179).
  time native_compute; reflexivity.
Time Qed.

End TM3.

