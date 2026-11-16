From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.

Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Definition Nsubge(a b:N) :=
(if b <=? a then Some (a-b) else None)%N.

Lemma Nsubge_spec a b c:
  Nsubge a b = Some c ->
  (a=c+b)%N.
Proof.
  unfold Nsubge.
  intros.
  destruct (N.leb_spec b a);
  inverts H; lia.
Qed.

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



Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

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
        | Some n0 =>
          match RInc r0 dep with
          | inl (r1,dn,Tp0) => inl (RC_S D0011 (n0+dn) r1,2,Tp1)
          | inr e => inr e
          | _ => inr x
          end
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
      | RC_S D00101 n0 r0 => inl (RC_S D0011_0101 n0 r0,0,Tp0)
      | RC_S D0011 n0 r0 => inl (RC_S D0011_011 n0 r0,0,Tp0)
      | RC_S D0011001 n0 r0 => inl (RC_S D0011_011001 n0 r0,0,Tp0)
      | RC_S D001101 n0 r0 => inl (RC_S D0011_01101 n0 r0,0,Tp0)
      | RC_S D00111 n0 r0 => inl (RC_S D0011_0111 n0 r0,0,Tp0)
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
    | Some n =>
      match RInc r dep with
      | inl (r,dn,Tp0) => inl (RC_S D0011 (n+dn) r,0,Tp1)
      | inr e => inr e
      | _ => inr x
      end
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

  | D0011_0101 => inl (RC_S D0011101 n r,0,Tp0)
  | D0011101 =>
    match N_OS n with
    | Some n =>
      match RInc r dep with
      | inl (r,dn,Tp0) => inl (RC_S D0011 (n+dn) r,1,Tp2)
      | inr e => inr e
      | _ => inr x
      end
    | None => inr x
    end
  | _ => inr x
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
  | inl (x',n,Tp0) => forall l, l {{D}}> toRC x -->+ l <{{A}} [0] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp1) => forall l, l {{D}}> toRC x -->+ l <{{C}} [0;0;1] *> w^^N.to_nat n *> toRC x'
  | inl (x',n,Tp2) => forall l, l {{D}}> toRC x -->+ l <{{C}} [0;0;0;1] *> w^^N.to_nat n *> toRC x'
  | inr _ => True
  end.
Proof.
  gen x.
  induction dep; cbn[RInc]; intros.
  1: trivial.
  destruct x as [[] n x|[]]; solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
    specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow100 IHdep. solve_v1.
  - destruct x as [[] n x|[]]; solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow100 IHdep. solve_v1.
    + es; er. follow100 IHdep. solve_v1.
    + es; er. follow100 IHdep. solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow100 IHdep. solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow100 IHdep. solve_v1.
  - specialize (IHdep x).
    destruct (RInc x dep) as [[[r dn] []]|]; solve_v1.
    + es; er. follow100 IHdep. solve_v1.
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
  - es; er. follow10 H. solve_v1.
  - es; er. follow10 H. solve_v1.
  - es; er. follow100 H. solve_v1.
Qed.

Definition is_digit(x:RD):bool :=
match x with
| D00101 => true
| D0011 => true
| D0011001 => true
| D001101 => true
| D00111 => true
| _ => false
end.

Notation hRL := [((D,[]),(A,[0]))].

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity).

Lemma is_digit_spec x:
  is_digit x = true ->
  segRLs tm (hRL^^5) hRL (toRD x++w^^2) (w++toRD x).
Proof.
  intro H.
  destruct x; inverts H; esc.
Qed.

Lemma is_digit_spec' k x:
  is_digit x = true ->
  segRLs tm (hRL^^(k*5)) (hRL^^k) (toRD x++w^^(k*2)) (w^^k++toRD x).
Proof.
  intro H.
  apply is_digit_spec in H.
  induction k.
  - rewrite app_nil_r.
    esx.
  - assert (segRLs tm (hRL^^(k*5+5)) (hRL^^(k+1)) (toRD x++w^^(k*2+2)) (w^^(k+1)++toRD x)) as I1. {
      repeat rewrite lpow_add.
      eapply segRLs_trans.
      - rewrite app_assoc.
        eapply segRLs_concat.
        1: apply IHk.
        apply segRLs_wall''; esc.
      - do 2 rewrite <-app_assoc.
        eapply segRLs_concat.
        2: apply H.
        apply segRLs_wall''; esx.
    }
    applys_eq I1; flia.
Qed.

Fixpoint RIncs(x:RC)(k:nat){struct k}:RC*N+RC :=
(match k with
| O =>
  match RInc x maxD with
  | inl (x',dn,Tp0) => inl (x',dn)
  | _ => inr x
  end
| S k0 =>
match x with
| RC_S a n r =>
  if is_digit a then
    let v:=5^(N.of_nat k0) in
    let v2:=v*2 in
    match Nsubge n v2 with
    | Some n =>
      match RIncs r k0 with
      | inl (x',dn) => inl (RC_S a (n+dn) x',v)
      | inr e => inr e
      end
    | _ => inr x
    end
  else inr x
| _ => inr x
end
end)%N.

Lemma RIncs_spec x k x' dn:
  RIncs x k = inl (x',dn) ->
  sideRLs tm (hRL^^(5^k)) (toRC x) (w^^(N.to_nat dn)*>toRC x').
Proof with (try congruence).
  gen x x' dn.
  induction k; cbn[RIncs] in *; intros.
  - pose proof (RInc_spec x maxD) as I1.
    destruct (RInc x maxD) as [[[x'0 dn0] []]|]...
    inverts H.
    econstructor.
    2: econstructor.
    exact I1.
  - destruct x...
    destruct (is_digit x) eqn:E...
    apply (is_digit_spec' (5^k)) in E.
    destruct (Nsubge n (5^(N.of_nat k)*2)) eqn:E1...
    apply Nsubge_spec in E1.
    subst n.
    destruct (RIncs x0 k) as [[x'0 dn0]|] eqn:E0...
    inverts H.
    cbn[toRC Nat.pow].
    apply IHk in E0.
    eassert (I1:_). {
      eapply segRLs_sideRLs_concat.
      1: apply E.
      eapply segRLs_sideRLs_concat.
      2: apply E0.
      eapply @segRLs_wall'' with (w:=w^^(N.to_nat n0)).
      esx.
    }
    repeat rewrite Str_app_assoc in I1.
    repeat rewrite lpow_add' in I1.
    applys_eq I1; flia.
Qed.

Lemma RIncs_Incs k r r':
  sideRLs tm (hRL^^k) r r' ->
  0inf {{D}}> r -->*
  0inf {{D}}> w^^k*>r'.
Proof.
  gen r r'.
  induction k; intros.
  - inverts H.
    esx.
  - replace (S k) with (k+1) in H by lia.
    rewrite lpow_add in H.
    apply sideRLs_split in H.
    destruct H as [r3 [I1 I2]].
    apply IHk in I1.
    follow I1.
    eapply sideRLs_1 in I2.
    es; er. follow100 I2. es.
Qed.

Lemma RIncs_spec' x k x' dn n:
  RIncs x k = inl (x',dn) ->
  toC (n,x) -->*
  toC ((n+dn+5^(N.of_nat k))%N,x').
Proof.
  intros H.
  apply RIncs_spec in H.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    2: apply H.
    eapply @segRLs_wall'' with (h1:=hRL) (w:=w^^(N.to_nat n)).
    esx.
  }
  apply RIncs_Incs in I1.
  unfold toC.
  repeat rewrite lpow_add' in I1.
  applys_eq I1; flia.
Qed.

Definition Incs(x:N*RC)(k:nat):N*RC+RC :=
(match k with
| O => Inc x
| _ =>
match x with
| (n,r) =>
  match RIncs r k with
  | inl (r',dn) => inl (n+dn+5^(N.of_nat k),r')
  | inr e => inr e
  end
end
end)%N.

Lemma Incs_spec x k x':
  Incs x k = inl x' ->
  toC x -->* toC x'.
Proof.
  unfold Incs.
  destruct k.
  - intro H.
    epose proof (Inc_spec _) as I1.
    rewrite H in I1.
    follow100 I1.
    finish.
  - destruct x as [n r].
    destruct (RIncs r (S k)) as [[r' dn]|] eqn:E.
    2: congruence.
    intro H.
    inverts H.
    eapply RIncs_spec' in E.
    apply E.
Qed.

Definition Incss(w:N*RC*N*nat):N*RC*N*nat+N*RC :=
(let '(x,T,k):=w in
let v := 5^(N.of_nat k) in
if v<=?T then
  match Incs x k with
  | inl x' => inl (x',T-v,S k)
  | inr e =>
    match k with
    | S k0 => inl (x,T,k0)
    | O => inr (123456789,e)
    end
  end
else
  match k with
  | O => inl (x,T,k)
  | S k0 => inl (x,T,k0)
  end)%N.

Lemma Incss_spec x T k:
  match Incss (x,T,k) with
  | inl (x',T',k') => toC x -->* toC x'
  | _ => True
  end.
Proof.
  unfold Incss.
  destruct (N.leb_spec (5^(N.of_nat k)) T).
  - destruct (Incs x k) eqn:E.
    + apply Incs_spec in E.
      apply E.
    + destruct k; trivial.
  - destruct k; trivial.
Qed.

Import Eqb.

Definition msteps x T T0 :=
  N_iter_until Incss (inl (x,T,O)) T0.

Lemma msteps_spec x T T0:
  match msteps x T T0 with
  | inl (x',T',k') => toC x -->* toC x'
  | _ => True
  end.
Proof.
  unfold msteps.
  apply N_iter_until_spec.
  2: finish.
  intros.
  destruct x0 as [[x' T'] k'].
  destruct (Incss (x',T',k')) as [[[x'0 T'0] k'0]|] eqn:E; trivial.
  epose proof (Incss_spec _ _ _) as I1.
  rewrite E in I1.
  follow H.
  apply I1.
Qed.

Definition msteps' x T T0 :=
match msteps x (T-1) T0 with
| inl (x',_,_) =>
  match Inc x' with
  | inl x'0 => Some x'0
  | _ => None
  end
| _ => None
end.

Lemma msteps_spec' x T T0 x':
  msteps' x T T0 = Some x' ->
  toC x -->+ toC x'.
Proof.
  unfold msteps'.
  intros.
  pose proof (msteps_spec x (T-1) T0) as I1.
  destruct (msteps x (T-1) T0) as [[[x'0 T'0] k'0]|].
  2: congruence.
  follow I1.
  pose proof (Inc_spec x'0).
  destruct (Inc x'0); congruence.
Qed.

Definition x0:N*RC := (1,RC_S D0011 27 (RC_S D00001 8 (RC_O D001T)))%N.

Lemma init:
  c0 -->* toC x0.
Proof.
  esx.
Qed.

Definition S' r := toC (406%N,
  RC_S D00111 12 (RC_S D001101 402 (RC_S D001101 391 (RC_S D00111 389 (RC_S D00101 390 (RC_S D0011 389 r)))))).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply multistep_nonhalt.
  1: eapply progress_evstep.
  1: eapply (msteps_spec') with (T:=17340200000%N) (T0:=10000%N).
  1: time native_compute; reflexivity.
  eapply progress_nonhalt_simple with (C:=S').
  intros x.
  eexists.
  eapply (msteps_spec') with (T:=518%N) (T0:=100%N).
  time native_compute; reflexivity.
Time Qed.

End TM1.

