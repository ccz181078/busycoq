From BusyCoq Require Import Individual62 DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import List.
Require Import String.
From BigInt Require Import BigIntMul BigIntMulProof BigIntMulOpsProof BigIntMulTests BigIntMulFProof.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RC_0LC0LB_0LD1LC_0LE1LA_0LF---_1RF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <{{F}} [0]^^a *> [0;1]^^b *> [1]^^c *> 0inf.

Lemma Inc1 a b c:
  S1 a (2+b) c -->*
  S1 (9+a) b c.
Proof.
  es.
Qed.

Lemma Incs1 n a b c:
  S1 a (n*2+b) c -->*
  S1 (n*9+a) b c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1_1_0 a c:
  S1 (1+a*2) 0 (3+c) -->*
  S1 6 (2+a) c.
Proof.
  es.
Qed.

Lemma Ov1_0_0 a c:
  S1 (a*2) 0 (3+c) -->*
  S1 2 (2+a) c.
Proof.
  es.
Qed.

Lemma S1_1 a c:
  S1 a 1 c -->*
  S1 (1+a) 0 (1+c).
Proof.
  es.
Qed.

Definition S0 '(a,c) :=
  S1 a 0 c.

Lemma S0_0 a c:
  S0 (a*4,3+c) -->*
  S0 (11+a*9,c).
Proof.
  unfold S0.
  mid (S1 (a*2*2) 0 (3+c)).
  1: es.
  follow Ov1_0_0.
  follow (Incs1 (1+a) 2 0 c).
  finish.
Qed.

Lemma S0_1 a c:
  S0 (1+a*4,3+c) -->*
  S0 (15+a*9,c).
Proof.
  unfold S0.
  mid (S1 (1+a*2*2) 0 (3+c)).
  1: es.
  follow Ov1_1_0.
  follow (Incs1 (1+a) 6 0 c).
  finish.
Qed.

Lemma S0_2 a c:
  S0 (2+a*4,3+c) -->*
  S0 (12+a*9,1+c).
Proof.
  unfold S0.
  mid (S1 ((1+a*2)*2) 0 (3+c)).
  1: es.
  follow Ov1_0_0.
  follow (Incs1 (1+a) 2 1 c).
  follow S1_1.
  finish.
Qed.

Lemma S0_3 a c:
  S0 (3+a*4,3+c) -->*
  S0 (16+a*9,1+c).
Proof.
  unfold S0.
  mid (S1 (1+(1+a*2)*2) 0 (3+c)).
  1: es.
  follow Ov1_1_0.
  follow (Incs1 (1+a) 6 1 c).
  follow S1_1.
  finish.
Qed.

Close Scope sym.

Lemma S0_Ov1 a:
  S0 (a,1) -->*
  S0 (3,3+a).
Proof.
  es.
Qed.

Lemma S0_Ov2 a:
  halts tm (S0 (a,2)).
Proof.
  esx.
Qed.

Lemma powpow2S a n:
  a^2^(S n)=(a^2^n)*(a^2^n).
Proof.
  cbn[Nat.pow Nat.mul].
  rewrite Nat.add_0_r,Nat.pow_add_r.
  lia.
Qed.

Local Opaque Nat.div Nat.modulo.

Lemma F_spec a c d a' c' k:
  F (a,c) d = Some (a',c') ->
  S0 (a+k*4^2^d,c) -->* S0 (a'+k*9^2^d,c').
Proof with try congruence.
  gen a c a' c' k.
  induction d; cbn[F]; unfold pow4pow2_nat,pow9pow2_nat in *; intros.
  - destruct (Nat.ltb_spec c 3)...
    change (4^2^0) with 4 in *.
    destruct (a mod 4) as [|[|[|]]] eqn:E; inverts H.
    + applys_eq (S0_0 (a/4+k) (c-3)); flia.
    + applys_eq (S0_1 (a/4+k) (c-3)); flia.
    + applys_eq (S0_2 (a/4+k) (c-3)); flia.
    + applys_eq (S0_3 (a/4+k) (c-3)); flia.
  - repeat rewrite powpow2S in *.
    remember (4^2^d) as b.
    remember (9^2^d) as b'.
    destruct (F (a mod (b*b),c)) as [[a0 c0]|] eqn:E...
    eapply IHd with (k:=k*b+a/(b*b)*b) in E.
    follow E. clear E.
    destruct (F (a0,c0)) as [[a1 c1]|] eqn:E0...
    eapply IHd with (k:=(k+a/(b*b))*9^2^d) in E0.
    follow E0.
    inverts H.
    finish.
Qed.

Lemma F_spec' x d x':
  F x d = Some x' ->
  S0 x -->* S0 x'.
Proof.
  destruct x as [a c].
  destruct x' as [a' c'].
  intros.
  apply F_spec with (k:=0) in H.
  applys_eq H; flia.
Qed.

Lemma F0_spec x n d x':
  F0 x n d = Some x' ->
  S0 x -->* S0 x'.
Proof with try congruence.
  gen x d x'.
  induction n; cbn[F0]; intros.
  - destruct (F x d) eqn:E...
    eapply F_spec' in E.
    eapply IHn in H.
    follow E.
    apply H.
  - eapply IHn in H.
    apply H.
  - eapply F_spec' in H.
    apply H.
Qed.

Definition S0' '(a,c) := S0 (N.to_nat a,N.to_nat c).

Lemma F0_bigint_spec' a c n d a' c':
  F0_bigint (bigint_of_N a, c) n d = Some (a', c') ->
  S0' (a, c) -->*
  S0' (bigint_to_N a', c').
Proof.
  unfold S0'.
  intros.
  eapply F0_bigint_spec in H.
  2: apply bigint_of_N_canonical.
  rewrite bigint_to_N_bigint_of_N in H.
  eapply F0_spec,H.
Qed.

Lemma S0'_Ov1 a:
  S0' (a,1)%N -->*
  S0' (3,3+a)%N.
Proof.
  unfold S0'.
  applys_eq (S0_Ov1); flia.
Qed.

Definition F1 a c n :=
  match F0_bigint (bigint_of_N a,c) n 0 with
  | Some (a',c') => (c' =? 2)%N
  | _ => false
  end.

Lemma F1_spec a c n:
  F1 a c n = true ->
  c0 -->* S0' (a,c) ->
  halts tm c0.
Proof.
  intros.
  unfold F1 in H.
  destruct (F0_bigint (bigint_of_N a, c) n 0) as [[a' c']|] eqn:E.
  2: congruence.
  destruct (N.eqb_spec c' 2).
  2: congruence.
  subst.
  apply F0_bigint_spec' in E.
  eapply halts_evstep.
  2: follow H0; apply E.
  apply S0_Ov2.
Qed.

Lemma init:
  c0 -->*
  S0' (3,119114451)%N.
Proof.
  eassert (I1:_). {
    eapply (F0_bigint_spec' 3 50 20 0 _ _).
    vm_compute; reflexivity.
  }
  mid (S0' (3,50)%N).
  1: unfold S0',S0,S1; esx.
  mid (S0' (119114448,1)%N).
  1: apply I1.
  apply S0'_Ov1.
Qed.

Lemma halt:
  halts tm c0.
Proof.
  eapply F1_spec with (n:=47648066%positive).
  2: apply init.
  native_check_eq.
Time Qed.

End TM1.

