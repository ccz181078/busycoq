From BusyCoq Require Import Individual62.

Require Import ZArith Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3 DivModCases.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1LA_0RD0LB_0RE1RC_1LB0RF_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint RC ls :=
match ls with
| [] => 0inf
| (true,a)::ls => [1] *> [0;1]^^a *> RC ls
| (false,a)::ls => [0] *> [0;1]^^a *> RC ls
end.

Fixpoint T (ls:list nat) :=
match ls with
| [] => []
| a::ls => (true,2+a)::T ls
end.

Definition S1 a b c d r :=
  0inf <{{A}} [1;0] *> [1;0;1;0;1;0;1;0;0]^^a *> [1;0;1;0] *> [1;0;1;0;0]^^b *> [1;0;1;0;1;0;1;1;0]^^c *> [1;0;1;0] *> [1;0;1;1;0]^^d *> RC (T r).

Definition S2 a b c d e r :=
  0inf <{{A}} [1;0] *> [1;0;1;0;1;0;1;0;0]^^a *> [1;0;1;0] *> [1;0;1;0;0]^^b *> [1;0;1;0]^^(1+c) *> [0] *> [1;0;1;0]^^(1+d) *> [0;1;0;1;0;0;0] *> [1;0;1;1;0]^^e *> RC (T r).

Fixpoint LC ls l :=
match ls with
| [] => l
| n::ls => [1;0]^^n *> [1;1;0;0;0] *> LC ls l
end.

Definition L0 a b :=
  [1;1;0;0;0]^^b *> [1;0;1;0;1;1;0;0;0]^^a *> [1;0;1;0;1;0] *> 0inf.

Definition S3 a b ls rs :=
  LC ls (L0 a b) {{C}}> RC rs.

Definition S4 a b ls rs :=
  LC ls (L0 a b) <{{B}} [0;1;0;1] *> RC rs.

Definition S5 a b ls rs :=
  LC ls (L0 a b) <{{C}} [1;0;1] *> RC (T rs).

Ltac uf := unfold S1,S2,S3,S4,S5,L0; cbn[LC RC T].

Ltac ES_v3.es_v3_pre ::= uf.

Lemma Inc1 a b c d r:
  S1 a b (1+c) d r -->*
  S1 (1+a) (1+b) c d r.
Proof.
  es' a b c d & (RC (T r)).
Qed.

Lemma Incs1 a b c d r:
  S1 a b c d r -->*
  S1 (c+a) (c+b) 0 d r.
Proof.
  gen a b.
  ind c Inc1.
Qed.

Lemma Inc2 a b c d e r:
  S2 a b c d (4+e) r -->*
  S2 (2+a) b (2+c) (1+d) e r.
Proof.
  es' a b c d e & (RC (T r)).
Qed.

Lemma Incs2 n a b c d e r:
  S2 a b c d (n*4+e) r -->*
  S2 (n*2+a) b (n*2+c) (n+d) e r.
Proof.
  gen a c d e.
  ind n Inc2.
Qed.

Lemma Ov1 a b d r:
  S1 a (2+b) 0 (2+d) r -->*
  S2 (2+a) b 0 0 d r.
Proof.
  es' a b d & (RC (T r)).
Qed.

Lemma Incs12 a b n rs:
  S1 0 1 (1+a) (2+n*4+b) rs -->*
  S2 (3+n*2+a) a (n*2) n b rs.
Proof.
  follow Incs1.
  follow (Ov1 (1+a) a (n*4+b) rs).
  follow Incs2.
  finish.
Qed.

Lemma Ov2_0 a b c d e ls:
  S2 a (1+b) c d 0 (e::ls) -->*
  S3 (1+a) b [2+e;2+d*2;c*2] (T ls).
Proof.
  es' a b c d e & (RC (T ls)).
Qed.

Lemma Ov2_1 a b c d e f ls:
  S2 a (1+b) c d 1 (1+e*2::f::ls) -->*
  S3 (2+a) b [f;e*2;O;1+d*2;2+c*2] (T ls).
Proof.
  es' a b c d e f & (RC (T ls)).
Qed.

Lemma Ov2_2 a b c d e ls:
  S2 a (1+b) c d 2 (e::ls) -->*
  S3 (2+a) b [2+e;3+d*2;2+c*2] (T ls).
Proof.
  es' a b c d e & (RC (T ls)).
Qed.

Lemma Ov2_3 a b c d e f ls:
  S2 a (1+b) c d 3 (1+e*2::f::ls) -->*
  S3 (3+a) b [f;e*2;O;2+d*2;4+c*2] (T ls).
Proof.
  es' a b c d e f & (RC (T ls)).
Qed.

Lemma S3_1 a b c d ls rs:
  S3 a b (2+d::ls) ((true,c)::rs) -->+
  S4 a b (d::ls) ((false,c)::rs).
Proof.
  uf; es.
Qed.

Lemma S3_0 a b c ls rs:
  S3 a b ls ((false,2+c)::rs) -->*
  S3 a b (c::ls) rs.
Proof.
  uf; es.
Qed.

Lemma S3_1_0 a b c ls rs:
  S3 a b (O::ls) ((true,c)::rs) -->+
  S4 a b ls ((false,O)::(false,c)::rs).
Proof.
  uf; es.
Qed.

Lemma S3_0_0_0 a b c d e ls rs:
  S3 a b (d*2::e::ls) ((false,O)::(false,1+c)::rs) -->*
  S3 a b (c+d*2::2+e::ls) rs.
Proof.
  uf; es.
Qed.

Lemma S3_0_0_1 a b c d ls rs:
  S3 a b (1+d*2::ls) ((false,O)::(false,1+c)::rs) -->*
  S4 a b ls ((false,3+d*2+c)::rs).
Proof.
  uf; es.
Qed.

Lemma S4_0 a b c ls rs:
  S4 a b (c*2::ls) rs -->*
  S4 a b ls ((false,2+c*2)::rs).
Proof.
  uf; es.
Qed.

Lemma S4_1 a b c d ls rs:
  S4 a b (1+c*2::d::ls) rs -->*
  S3 a b (1+c*2::2+d::ls) rs.
Proof.
  uf; es.
Qed.

Lemma S4_O a b rs:
  S4 a b [] rs -->*
  S3 (1+a) b [] rs.
Proof.
  uf; es.
Qed.

Lemma S3_rh a b c ls:
  S3 a b (1+c::ls) [] -->+
  S4 a b (c::ls) [].
Proof.
  uf; es.
Qed.

Lemma S3_rh_0 a b c ls:
  S3 a b (O::c::ls) [] -->+
  S5 a b ls [3+c].
Proof.
  uf; es.
Qed.

Lemma S5_S a b c ls rs:
  S5 a b (c::ls) (rs) -->+
  S5 a b ls ((c::rs)).
Proof.
  uf; es.
Qed.

Lemma S5_O a b c rs:
  S5 (1+a) b [] ((1+c::rs)) -->+
  S1 0 1 a (1+b) ((c::rs)).
Proof.
  es' a b c & (RC (T rs)).
Qed.

Lemma RInc_1 a b c d e ls:
  S3 a b (3+c*2::1+d*2::e::ls) [] -->*
  S3 a b (1+c*2::3+d*2::2+e::ls) [].
Proof.
  change (3+c*2) with (1+((1+c)*2)).
  follow100 S3_rh.
  follow S4_0.
  follow S4_1.
  follow S3_0.
  change ((1+c)*2) with (1+(1+c*2)).
  follow100 S3_rh.
  follow S4_1.
  finish.
Qed.

Fixpoint mul2 ls :=
match ls with
| [] => []
| a::ls => a*2::mul2 ls
end.

Lemma S43_Incs a b c d ls ls0 rs:
  S4 a b ((mul2 ls)++1+c*2::d::ls0) rs -->*
  S3 a b ((mul2 ls)++1+c*2::2+d::ls0) rs.
Proof.
  gen rs.
  induction ls; intros.
  - apply S4_1.
  - cbn[mul2 app].
    follow S4_0.
    follow IHls.
    apply S3_0.
Qed.

Lemma S43_Incs_O a b ls rs:
  S4 a b (mul2 ls) rs -->*
  S3 (1+a) b (mul2 ls) rs.
Proof.
  gen rs.
  induction ls; intros.
  - apply S4_O.
  - cbn[mul2 app].
    follow S4_0.
    follow IHls.
    apply S3_0.
Qed.

Lemma RInc_2 a b c d ds e f ls:
  S3 a b (3+c*2::d*2::(mul2 ds)++1+e*2::f::ls) [] -->*
  S3 a b (1+c*2::2+d*2::(mul2 ds)++1+e*2::2+f::ls) [].
Proof.
  change (3+c*2) with (1+((1+c)*2)).
  follow100 S3_rh.
  follow S4_0.
  follow S4_0.
  follow S43_Incs.
  follow S3_0.
  follow S3_0.
  change ((1+c)*2) with (1+(1+c*2)).
  follow100 S3_rh.
  follow S4_1.
  finish.
Qed.

Lemma RInc_2_O a b c d ds:
  S3 a b (3+c*2::d*2::(mul2 ds)) [] -->*
  S3 (1+a) b (1+c*2::2+d*2::(mul2 ds)) [].
Proof.
  change (3+c*2) with (1+((1+c)*2)).
  follow100 S3_rh.
  follow S4_0.
  follow S4_0.
  follow S43_Incs_O.
  follow S3_0.
  follow S3_0.
  change ((1+c)*2) with (1+(1+c*2)).
  follow100 S3_rh.
  follow S4_1.
  finish.
Qed.


Lemma RIncs_1 a b c d e ls:
  S3 a b (1+c*2::1+d*2::e::ls) [] -->+
  S3 a b (O::1+c*2+d*2::2+c*2+e::ls) [].
Proof.
  gen d e.
  induction c; intros.
  1:{
  follow10 S3_rh.
  follow S4_0.
  follow S4_1.
  follow S3_0.
  finish.
  }
  follow RInc_1.
  follow10 (IHc (1+d)).
  finish.
Qed.

Lemma RIncs_2 a b c d ds e f ls:
  S3 a b (1+c*2::d*2::(mul2 ds)++1+e*2::f::ls) [] -->+
  S3 a b (O::c*2+d*2::(mul2 ds)++1+e*2::2+c*2+f::ls) [].
Proof.
  gen d f.
  induction c; intros.
  1:{
  follow10 S3_rh.
  follow S4_0.
  follow S4_0.
  follow S43_Incs.
  follow S3_0.
  follow S3_0.
  finish.
  }
  follow RInc_2.
  follow10 (IHc (1+d)).
  finish.
Qed.

Lemma RIncs_2_O a b c d ds:
  S3 a b (1+c*2::d*2::(mul2 ds)) [] -->+
  S3 (1+c+a) b (O::c*2+d*2::(mul2 ds)) [].
Proof.
  gen a d.
  induction c; intros.
  1:{
  follow10 S3_rh.
  follow S4_0.
  follow S4_0.
  follow S43_Incs_O.
  follow S3_0.
  follow S3_0.
  finish.
  }
  follow RInc_2_O.
  follow10 (IHc (1+a) (1+d)).
  finish.
Qed.

Lemma S3_rh' a b c d ls:
  S3 a b (2+c*2::d::ls) [] -->+
  S3 a b (1+c*2::2+d::ls) [].
Proof.
  change (2+c*2) with (1+(1+c*2)).
  follow10 S3_rh.
  follow (S43_Incs a b c d []).
  finish.
Qed.


Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Lemma init:
  c0 -->*
  S1 0 1 43 30 [19;10;O;70;96].
Proof.
  uf.
  stepn' 160416%N; st; reflexivity.
Qed.


Lemma S3T_2_O a b c d ls rs:
  S3 a b (2+c*2::mul2 ls) (T (d::rs)) -->+
  S3 (1+a) b (d::c*2::mul2 ls) (T rs).
Proof.
  cbn[T].
  follow10 S3_1.
  follow (S43_Incs_O a b (c::ls)).
  follow S3_0.
  finish.
Qed.

Lemma S3T_2 a b c d e f ls ls0 rs:
  S3 a b (2+c*2::mul2 ls++1+d*2::e::ls0) (T (f::rs)) -->+
  S3 a b (f::c*2::mul2 ls++1+d*2::2+e::ls0) (T rs).
Proof.
  cbn[T].
  follow10 S3_1.
  follow (S43_Incs a b d e (c::ls)).
  follow S3_0.
  finish.
Qed.

Lemma S3T_3 a b c d e ls rs:
  S3 a b (3+c*2::d::ls) (T (e::rs)) -->+
  S3 a b (e::1+c*2::2+d::ls) (T rs).
Proof.
  cbn[T].
  change (3+c*2) with (2+(1+c*2)).
  follow10 S3_1.
  follow (S43_Incs a b c d []).
  follow S3_0.
  finish.
Qed.

Lemma S3T_000 a b c c' d e f ls ls0 rs:
  S3 a b (O::c*2::c'*2::mul2 ls++1+d*2::e::ls0) (T (f::rs)) -->+
  S3 a b (1+c*2+f::2+c'*2::mul2 ls++1+d*2::2+e::ls0) (T rs).
Proof.
  cbn[T].
  follow10 S3_1_0.
  follow (S43_Incs a b d e (c::c'::ls)).
  cbn[mul2 app].
  change (2+f) with (1+(1+f)).
  follow S3_0_0_0.
  finish.
Qed.

Lemma S3T_000_O a b c c' f ls rs:
  S3 a b (O::c*2::c'*2::mul2 ls) (T (f::rs)) -->+
  S3 (1+a) b (1+c*2+f::2+c'*2::mul2 ls) (T rs).
Proof.
  cbn[T].
  follow10 S3_1_0.
  follow (S43_Incs_O a b (c::c'::ls)).
  cbn[mul2 app].
  change (2+f) with (1+(1+f)).
  follow S3_0_0_0.
  finish.
Qed.

Lemma S3T_001 a b c d e f ls rs:
  S3 a b (O::c*2::1+d*2::e::ls) (T (f::rs)) -->+
  S3 a b (1+c*2+f::3+d*2::2+e::ls) (T rs).
Proof.
  cbn[T].
  follow10 S3_1_0.
  follow (S43_Incs a b d e [c]).
  cbn[mul2 app].
  change (2+f) with (1+(1+f)).
  follow S3_0_0_0.
  finish.
Qed.

Lemma S3T_010 a b c d d0 d1 e ls ls0 rs:
  S3 a b (O::1+c*2::d*2::mul2 ls++1+d0*2::d1::ls0) (T (e::rs)) -->+
  S3 a b (2+c*2+e::2+d*2::mul2 ls++1+d0*2::2+d1::ls0) (T rs).
Proof.
  cbn[T].
  follow10 S3_1_0.
  follow (S43_Incs a b c (d*2) []).
  cbn[mul2 app].
  change (2+e) with (1+(1+e)).
  follow S3_0_0_1.
  follow (S43_Incs a b d0 d1 (1+d::ls)).
  cbn[mul2 app].
  replace (3+c*2+(1+e)) with (2+(2+c*2+e)) by lia.
  follow S3_0.
  finish.
Qed.

Lemma S3T_010_O a b c d e ls rs:
  S3 a b (O::1+c*2::d*2::mul2 ls) (T (e::rs)) -->+
  S3 (1+a) b (2+c*2+e::2+d*2::mul2 ls) (T rs).
Proof.
  cbn[T].
  follow10 S3_1_0.
  follow (S43_Incs a b c (d*2) []).
  cbn[mul2 app].
  change (2+e) with (1+(1+e)).
  follow S3_0_0_1.
  follow (S43_Incs_O a b (1+d::ls)).
  cbn[mul2 app].
  replace (3+c*2+(1+e)) with (2+(2+c*2+e)) by lia.
  follow S3_0.
  finish.
Qed.

Lemma S3T_011 a b c d d0 e ls rs:
  S3 a b (O::1+c*2::1+d*2::d0::ls) (T (e::rs)) -->+
  S3 a b (2+c*2+e::3+d*2::2+d0::ls) (T rs).
Proof.
  cbn[T].
  follow10 S3_1_0.
  follow (S43_Incs a b c (1+d*2) []).
  cbn[mul2 app].
  change (2+e) with (1+(1+e)).
  follow S3_0_0_1.
  follow (S43_Incs a b (1+d) d0 []).
  cbn[mul2 app].
  replace (3+c*2+(1+e)) with (2+(2+c*2+e)) by lia.
  follow S3_0.
  finish.
Qed.

Inductive Config :=
| cfg3(a b:nat)(ls rs:list nat)
| cfg5(a b:nat)(ls rs:list nat)
.

Definition to_config x :=
match x with
| cfg3 a b ls rs => S3 a b ls (T rs)
| cfg5 a b ls rs => S5 a b ls rs
end.

Inductive RWF: nat->(list nat)->Prop :=
| RWF_O:
  RWF 0 []
| RWF_S n rs x:
  RWF n rs ->
  n*2+2<=x ->
  RWF (S n) (x::rs).

Inductive LWF: nat->nat->(list nat)->Prop :=
| LWF_O n x:
  n*2<=x*2 ->
  LWF n 1 [x*2]
| LWF_O' n x x0 x1:
  n*2<=x*2 ->
  n*2+2<=x0 ->
  n*2+4<=x1*2 ->
  LWF n 3 [x*2;O;x0;x1*2]
| LWF_S n m x ls:
  LWF (S n) m ls ->
  n*2<=x ->
  LWF n (S m) (x::ls)
.

Inductive LWF_mul2: nat->nat->(list nat)->Prop :=
| LWF_mul2_O n m ls:
  LWF_mul2 n m (mul2 ls)
| LWF_mul2_S n m ls c d ls0:
  (forall i, LWF n m (mul2 ls++1+c*2::i*2+d::ls0)) ->
  LWF_mul2 n m (mul2 ls++1+c*2::d::ls0)
.

Lemma LWF_mul2_cases {n m ls}:
  LWF n m ls ->
  LWF_mul2 n m ls.
Proof.
  intro H.
  induction H; intros.
  - apply LWF_mul2_O with (ls:=[x]).
  - destruct (mod2 x0); subst.
    + apply LWF_mul2_O with (ls:=[x;O;a;x1]).
    + apply LWF_mul2_S with (ls:=[x;O]).
      intros; cbn.
      applys_eq (LWF_O' n x (1+a*2) (i+x1)); flia.
  - destruct (mod2 x); subst.
    + inverts IHLWF.
      * apply LWF_mul2_O with (ls:=a::ls0).
      * apply LWF_mul2_S with (ls:=a::ls0).
        intros; cbn.
        apply LWF_S; auto 1.
    + inverts H.
      * apply LWF_mul2_S with (ls:=[]).
        intros.
        apply LWF_S; [|lia].
        applys_eq (LWF_O (S n) (i+x)); flia.
      * apply LWF_mul2_S with (ls:=[]).
        intros; cbn.
        apply LWF_S; [|lia].
        applys_eq (LWF_O' (S n) (i+x) x0 x1); flia.
      * apply LWF_mul2_S with (ls:=[]).
        intros.
        apply LWF_S; [|lia].
        apply LWF_S; [auto 1|lia].
Qed.

Ltac ec := econstructor.

Inductive LWF_add2: nat->nat->(list nat)->Prop :=
| LWF_add2_intro n m a ls:
  (forall i, LWF n m (i*2+a::ls)) ->
  LWF_add2 n m (a::ls).

Lemma LWF_add2_cases {n m ls}:
  LWF n m ls ->
  LWF_add2 n m ls.
Proof.
  intros H.
  inverts H; ec; intros.
  - applys_eq (LWF_O n (i+x)); flia.
  - applys_eq (LWF_O' n (i+x) x0 x1); flia.
  - apply LWF_S; [auto 1|lia].
Qed.

Ltac ex5 :=
  eexists (cfg5 _ _ _ _); cbn[to_config]; split.
Ltac ex3 :=
  eexists (cfg3 _ _ _ _); cbn[to_config]; split.
Ltac ex3' :=
  eexists (cfg3 _ _ _ []); cbn[to_config]; split.

Inductive P: Config->Prop :=
| P3 a b c ls rs n m
  (Hrs:RWF n rs)
  (Hls:LWF (1+n) m ls)
  (Hc:rs=[]\/(1+n)*2<=c)
  (Hm:4<=m+n)
  (Hb:(m+n)*4<=b/\7+b<=a):
  P (cfg3 a b (c::ls) rs)
| P5 a b ls rs n m
  (Hrs:RWF n rs)
  (Hls:LWF (1+n) m ls)
  (Hm:4<=m+n)
  (Hb:(m+n)*4<=b/\7+b<=a):
  P (cfg5 a b ls rs)
.

Lemma BigStep x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  intro HP.
  inverts HP.
  { cbn[to_config].
    destruct rs as [|d rs].
    { clear Hc.
      destruct c as [|c].
      { pose (LWF_add2_cases Hls) as x.
        inverts x.
        inverts Hrs.
        inverts Hls.
        1,2: lia.
        ex5.
        1: apply S3_rh_0.
        eapply P5.
        - apply RWF_S; [ec|].
          lia.
        - apply H4.
        - lia.
        - lia.
      }
      destruct (mod2 c); subst.
      { pose (LWF_mul2_cases Hls) as x.
        inverts x.
        { pose (LWF_add2_cases Hls) as x.
          inverts x.
          destruct ls0 as [|a2 ls0]; inverts H.
          ex3'.
          1: apply RIncs_2_O.
          eapply P3.
          - apply Hrs.
          - apply (H2 a0).
          - left; trivial.
          - lia.
          - lia.
        }
        destruct ls0 as [|a1 ls0].
        { specialize (H (1+a0)).
          pose (LWF_add2_cases H) as x.
          inverts x.
          ex3'.
          1: apply RIncs_1.
          eapply P3.
          - apply Hrs.
          - applys_eq (H3 a0); flia.
          - left; trivial.
          - lia.
          - lia.
        }
        { specialize (H (1+a0)).
          pose (LWF_add2_cases H) as x.
          inverts x.
          ex3'.
          1: apply RIncs_2.
          eapply P3.
          - apply Hrs.
          - applys_eq (H3 a0); flia.
          - left; trivial.
          - lia.
          - lia.
        } }
      { pose (LWF_add2_cases Hls) as x.
        inverts x.
        eexists (cfg3 _ _ _ []); cbn[to_config]; split.
        1: apply S3_rh'.
        eapply P3.
        - apply Hrs.
        - apply (H 1%nat).
        - left; trivial.
        - lia.
        - lia.
      }
    }
    { destruct Hc as [Hc|Hc]; [congruence|].
      destruct (sub c 2); [subst|lia].
      destruct (mod2 c1); subst.
      { pose (LWF_mul2_cases Hls) as x.
        inverts x.
        { ex3.
          1: apply S3T_2_O.
          inverts Hrs.
          eapply P3.
          - apply H2.
          - eapply LWF_S.
            1: apply Hls.
            lia.
          - lia.
          - lia.
          - lia. }
        { ex3.
          1: apply S3T_2.
          inverts Hrs.
          eapply P3.
          - apply H3.
          - eapply LWF_S.
            1: apply (H 1%nat).
            lia.
          - lia.
          - lia.
          - lia. } }
      { pose (LWF_add2_cases Hls) as x.
        inverts x.
        inverts Hrs.
        ex3.
        1: apply S3T_3.
        eapply P3.
        - apply H3.
        - eapply LWF_S.
          1: apply (H 1%nat).
          lia.
        - lia.
        - lia.
        - lia. } } }
  { inverts Hls.
    {
      destruct (sub a 3) as [a0|]; [subst|lia].
      destruct (sub b 1) as [b0|]; [subst|lia].
      destruct (sub x 1) as [x0|]; [subst|lia].
      destruct (mod4 b0) as [b1|b1|b1|b1]; subst.
      {
        ex3.
        1:{
          follow10 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 0 b1 (1+x0*2::rs)).
          apply Ov2_0.
        }
        eapply P3.
        - apply Hrs.
        - eapply LWF_S.
          1: apply LWF_O; lia.
          lia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        inverts Hrs.
        1: lia.
        ex3.
        1:{
          follow10 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 1 b1 (1+x0*2::x::rs0)).
          apply Ov2_1.
        }
        eapply P3.
        - apply H0.
        - eapply LWF_O' with (x1:=1+b1*2); lia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        ex3.
        1:{
          follow10 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 2 b1 (1+x0*2::rs)).
          apply Ov2_2.
        }
        eapply P3.
        - apply Hrs.
        - eapply LWF_S.
          1: apply LWF_O with (x:=1+b1*2); lia.
          lia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        inverts Hrs.
        1: lia.
        ex3.
        1:{
          follow10 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 3 b1 (1+x0*2::x::rs0)).
          apply Ov2_3.
        }
        eapply P3.
        - apply H0.
        - eapply LWF_O' with (x1:=2+b1*2); lia.
        - right.
          lia.
        - lia.
        - lia.
      }
    }
    {
      destruct (sub a 3) as [a0|]; [subst|lia].
      destruct (sub b 1) as [b0|]; [subst|lia].
      destruct (sub x1 1) as [x1'|]; [subst|lia].
      destruct (mod4 b0) as [b1|b1|b1|b1]; subst;
      destruct (mod2 x0) as [x0'|x0']; subst.
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 0 b1 (1+x1'*2::2+x0*2::O::x*2::rs)).
          follow Ov2_0.
          follow100 S3T_3.
          epose proof (S3T_2 _ _ x0 x1' _ _ [] _ _) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          follow100 S3T_001.
          finish.
        }
        eapply P3.
        - apply Hrs.
        - apply LWF_S; [|lia].
          apply LWF_S; [|lia].
          apply LWF_O; lia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 0 b1 (1+x1'*2::3+x0*2::O::x*2::rs)).
          follow Ov2_0.
          follow100 S3T_3.
          follow100 S3T_3.
          change (2+(1+x1'*2)) with (1+(1+x1')*2).
          follow100 S3T_011.
          finish.
        }
        eapply P3.
        - apply Hrs.
        - apply LWF_S; [|lia].
          apply LWF_S; [|lia].
          apply LWF_O; lia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 1 b1 (1+x1'*2::2+x0*2::O::x*2::rs)).
          follow Ov2_1.
          epose proof (S3T_2 _ _ _ _ _ _ [x1';O]) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          epose proof (S3T_000 _ _ _ _ _ _ _ [O]) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          finish.
        }
        eapply P3.
        - apply Hrs.
        - applys_eq (LWF_O' (1+n) (1+x1') (1+b1*2) (3+b1*2)); flia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 1 b1 (1+x1'*2::3+x0*2::O::x*2::rs)).
          follow Ov2_1.
          follow100 S3T_3.
          epose proof (S3T_010 _ _ _ (1+x1') _ _ _ [O]) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          finish.
        }
        eapply P3.
        - apply Hrs.
        - applys_eq (LWF_O' (1+n) (2+x1') (1+b1*2) (2+b1*2)); flia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 2 b1 (1+x1'*2::2+x0*2::O::x*2::rs)).
          follow Ov2_2.
          follow100 S3T_3.
          epose proof (S3T_2 _ _ _ _ _ _ []) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          follow100 S3T_001.
          finish.
        }
        eapply P3.
        - apply Hrs.
        - apply LWF_S; [|lia].
          apply LWF_S; [|lia].
          apply LWF_O with (x:=1+b1*2); lia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 2 b1 (1+x1'*2::3+x0*2::O::x*2::rs)).
          follow Ov2_2.
          follow100 S3T_3.
          follow100 S3T_3.
          change (2+(1+x1'*2)) with (1+(1+x1')*2).
          follow100 S3T_011.
          finish.
        }
        eapply P3.
        - apply Hrs.
        - apply LWF_S; [|lia].
          apply LWF_S; [|lia].
          apply LWF_O with (x:=1+b1*2); lia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 3 b1 (1+x1'*2::2+x0*2::O::x*2::rs)).
          follow Ov2_3.
          epose proof (S3T_2_O _ _ _ _ [x1';O;1+b1;2+b1*2]) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          epose proof (S3T_000_O _ _ _ _ _ [_;_;_]) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          finish.
        }
        eapply P3.
        - apply Hrs.
        - applys_eq (LWF_O' (1+n) (1+x1') (2+b1*2) (2+b1*2)); flia.
        - right.
          lia.
        - lia.
        - lia.
      }
      {
        destruct x0' as [|x0]; [lia|].
        ex3.
        1:{
          follow10 S5_S.
          do 3 follow100 S5_S.
          cbn.
          follow100 S5_O.
          follow (Incs12 (1+a0) 3 b1 (1+x1'*2::3+x0*2::O::x*2::rs)).
          follow Ov2_3.
          follow100 S3T_3.
          epose proof (S3T_010_O _ _ _ (1+x1') _ [O;1+b1;2+b1*2]) as I1.
          follow100 I1; clear I1; cbn[mul2 app].
          finish.
        }
        eapply P3.
        - apply Hrs.
        - applys_eq (LWF_O' (1+n) (2+x1') (2+b1*2) (2+b1*2)); flia.
        - right.
          lia.
        - lia.
        - lia.
      }
    }
    {
      ex5.
      1: apply S5_S.
      eapply P5.
      - ec; [apply Hrs|lia].
      - apply H.
      - lia.
      - lia.
    }
  }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfg3 _ _ _ _)).
  1:{
    follow init.
    follow (Incs12 42 0 7).
    follow Ov2_0.
    epose proof (S3T_3 _ _ 9) as I1.
    follow100 I1; clear I1; cbn[mul2 app].
    epose proof (S3T_2 _ _ 4 _ _ _ []) as I1.
    follow100 I1; clear I1; cbn[mul2 app].
    follow100 S3T_001.
    finish.
  }
  eapply progress_nonhalt_cond with (P:=P).
  2:{
    ec.
    - ec; [ec|lia].
    - eapply LWF_S; [|lia].
      eapply LWF_S; [|lia].
      apply LWF_O; lia.
    - lia.
    - lia.
    - lia.
  }
  exact BigStep.
Qed.

End TM1.




