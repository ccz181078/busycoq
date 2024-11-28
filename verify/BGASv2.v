From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC1RF_0LA1RB_1LA0RE_1LE1RD_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k+1)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+14).
Proof.
  remember (S0 (S n) (n*6+14)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 0) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  halts tm (S0 n (n*3+3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold S0.
    follow LInc.
    repeat step1.
    finish.
  }
  apply halted_halts.
  constructor.
Qed.

Definition config '(n,k) := S0 (S n) (k*6+2).

Lemma init:
  c0 -->* config (0,1)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k*6+2 <= (S n)*3+2 \/ k*6+2 >= (S n)*3+4) as E by lia.
  destruct E as [E|E].
  - eexists (n,n+2).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (S n,k*2-n-2).
    epose proof (BigStep1 (S n) (k*6+2-(S n*3+4))).
    applys_eq H;
    f_equal; lia.
Qed.

End TM1.



Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0RF_0RC0LA_1RE1RD_0RE---_0LB1RC_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{E}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+8).
Proof.
  remember (S0 (S n) (n*4+8)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 0) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0 (S n) (n*4+9).
Proof.
  remember (S0 (S n) (n*4+9)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,8)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM2.

Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0RF_0RC0LA_1RE1RD_0RE---_0LF1RC_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{E}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+9).
Proof.
  remember (S0 (S n) (n*4+9)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow]. cbn[Str_app].
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,9)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LA_1RE0RD_1RE---_0LA1RC_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{E}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+k) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  unfold S1 in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,8)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+2) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+2))).
    applys_eq H;
    f_equal; lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0RF_0RC0LA_1RE1RD_0RE---_0RF1RC_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{E}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+k) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  unfold S1 in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,8)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+2) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+2))).
    applys_eq H;
    f_equal; lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RA_0RA0LD_1LC0RF_0RB---_1LF1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+9).
Proof.
  remember (S0 (S n) (n*4+9)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow]. cbn[Str_app].
  finish.
Qed.

Definition S0' l :=
  l <* [0] {{B}}> const 0.

Lemma BigStep3 n:
  exists l,
  S0 (S n) (S n*2+2) -->+
  S0' l.
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  unfold S0.
  remember (S n) as n'.
  eexists.
  follow LInc.
  do 4 step1.
  finish.
Qed.

Definition config(x:_+_) :=
match x with
| inl (n,k) => S0 (S n) k
| inr l => S0' l
end.

Lemma init:
  c0 -->* config (inl (0,5)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [[n k]|l].
  2:{
    eexists (inr _).
    do 4 step1.
    finish.
  }
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (inl (_,_)).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (inl (_,_)).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - rewrite E.
    destruct (BigStep3 n) as [l I3].
    eexists (inr _).
    follow10 I3.
    finish.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1RA_1LC1RD_1LE0RC_0RA0LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+9).
Proof.
  remember (S0 (S n) (n*4+9)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow]. cbn[Str_app].
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,5)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RA_1LC1RD_1LE0RC_0RA0LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2+2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow]. cbn[Str_app].
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,10)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1RA_1LC1RD_1LE0RC_1LA0LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k+2)) -->+
  S0 (S n) (k*2+3).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 3) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+15).
Proof.
  remember (S0 (S n) (n*6+15)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*3+3) -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  replace (S n'*3+2) with (1+(S n'*3+1)) by lia.
  remember (S n'*3+1) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Lemma BigStep4 n:
  S0 (S n) (S n*3+4) -->+
  S0 (S n) (n*6+17).
Proof.
  remember (S0 (S n) (n*6+17)) as tg.
  unfold S0.
  remember (S n) as n'.
  replace (n'*3+4) with ((n'*3+3)+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  replace (S n'*3+2) with (1+(S n'*3+1)) by lia.
  remember (S n'*3+1) as v1.
  es; er.
  epose proof (Incs1 _ v1 3) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,11)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+5 \/ k=(S n)*3+3 \/ k=(S n)*3+4) as E by lia.
  destruct E as [E|[E|[E|E]]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (S n,_).
    epose proof (BigStep1 (S n) (k-(S n*3+5))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 (BigStep3).
    finish.
  - eexists (_,_).
    rewrite E.
    follow10 (BigStep4).
    finish.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LA_---0RD_1RE1RB_1RA1RD_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 1) with (n*3+4+0) by lia.
  replace (S n * 3 + 2) with (n*3+4+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+4)*2+0) with ((n*3+2)+(n*3+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+2)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+13).
Proof.
  remember (S0 (S n) (n*6+13)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+2)+(n*3+7))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+7) with (1+(n*3+6)) by lia.
  remember (n*3+6) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config(x:_+_) :=
match x with
| inl (n,k) => S0 (S n) (k*3)
| inr (n,k) => S0 (S n) (k*3+1)
end.

Lemma init:
  c0 -->* config (inl (0,3)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  unfold config.
  intros [[n k]|[n k]].
  + assert (k*3 <= (S n)*3+1 \/ k*3 >= (S n)*3+3) as E by lia.
    destruct E as [E|E].
    - eexists (inr (n,n*2+4)).
      follow10 (BigStep2 _ _ E).
      finish.
    - eexists (inr (S n,(k-n-2)*2)).
      epose proof (BigStep1 (S n) (k*3-(S n*3+3))).
      applys_eq H;
      f_equal; lia.
  + assert (k*3+1 <= (S n)*3+1 \/ k*3+1 >= (S n)*3+3) as E by lia.
    destruct E as [E|E].
    - eexists (inr (n,n*2+4)).
      follow10 (BigStep2 _ _ E).
      finish.
    - eexists (inl (S n,(k-n-2)*2+1)).
      epose proof (BigStep1 (S n) (k*3+1-(S n*3+3))).
      applys_eq H;
      f_equal; try lia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LA_---0RD_1RE1RB_0LA1RD_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 1) with (n*3+4+0) by lia.
  replace (S n * 3 + 2) with (n*3+4+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+4)*2+0) with ((n*3+2)+(n*3+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+2)+(k+1)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  follow Ov2.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+12).
Proof.
  remember (S0 (S n) (n*6+12)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+2)+(n*3+7))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+7) with (1+(n*3+6)) by lia.
  remember (n*3+6) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 0) as I1.
  unfold S1 in I1. cbn in I1. 
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) (k*6).

Lemma init:
  c0 -->* config ((0,1)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  unfold config.
  intros [n k].
  assert (k*6 <= (S n)*3+1 \/ k*6 >= (S n)*3+3) as E by lia.
  destruct E as [E|E].
  - eexists ((n,n+2)).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists ((S n,(k*2-n-2))).
    epose proof (BigStep1 (S n) (k*6-(S n*3+3))).
    applys_eq H;
    f_equal; try lia.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LA_---0RD_1RE1RB_1LD1RD_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 1) with (n*3+4+0) by lia.
  replace (S n * 3 + 2) with (n*3+4+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+4)*2+0) with ((n*3+2)+(n*3+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+2)+(k+1)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  follow Ov2.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+12).
Proof.
  remember (S0 (S n) (n*6+12)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+2)+(n*3+7))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+7) with (1+(n*3+6)) by lia.
  remember (n*3+6) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 0) as I1.
  unfold S1 in I1. cbn in I1. 
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) (k*6).

Lemma init:
  c0 -->* config ((0,1)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  unfold config.
  intros [n k].
  assert (k*6 <= (S n)*3+1 \/ k*6 >= (S n)*3+3) as E by lia.
  destruct E as [E|E].
  - eexists ((n,n+2)).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists ((S n,(k*2-n-2))).
    epose proof (BigStep1 (S n) (k*6-(S n*3+3))).
    applys_eq H;
    f_equal; try lia.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LA_1RD1RE_0RF1RC_0RD---_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{D}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) (k).

Lemma init:
  c0 -->* config (0,14)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+3) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*3+3))).
    applys_eq H;
    f_equal; try lia.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC1RF_1LA1RB_1LA0RE_1LE1RD_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+15).
Proof.
  remember (S0 (S n) (n*6+15)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  halts tm (S0 n (n*3+3)).
Proof.
  eapply halts_evstep.
  2:{
    unfold S0.
    follow LInc.
    repeat step1.
    finish.
  }
  apply halted_halts.
  constructor.
Qed.

Definition config '(n,i) := S0 (S n) ((S n)*6+13-2^i*4).
Definition P '(n,i) := (S n)*6+13 >= 2^i*4.

Lemma init:
  c0 -->* config (0,0)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma R0 n i:
  2^i*4 < (S n)*3+10 ->
  P (n,i) ->
  (P (S n,S i) /\
  config (n,i) -->+ config (S n,S i)).
Proof.
  unfold config,P.
  intros H HP.
  split.
  1: cbn[Nat.pow]; lia.
  applys_eq (BigStep1 (S n) ((S n)*3+9-2^i*4)).
  all: f_equal; cbn[Nat.pow]; try lia.
Qed.

Lemma R1 n i:
  2^i*4 = (S n)*3+10 ->
  P (n,i) ->
  halts tm (config (n,i)).
Proof.
  unfold config,P.
  intros H HP.
  applys_eq (BigStep3 (S n)).
  f_equal; try lia.
Qed.

Lemma R2 n i:
  2^i*4 > (S n)*3+10 ->
  P (n,i) ->
  (P (n,0) /\
  config (n,i) -->+ config (n,0))%nat.
Proof.
  unfold config,P.
  intros H HP.
  split.
  1: cbn[Nat.pow]; lia.
  applys_eq (BigStep2 (n) ((S n)*6+13-2^i*4)).
  all: f_equal; cbn[Nat.pow]; try lia.
Qed.

Lemma R0s n i:
  2^i*4 < (S n)*3+10 ->
  P (n,O) ->
  (P (i+n,i) /\
  config (n,O) -->* config (i+n,i)).
Proof.
  gen n.
  induction i; intros.
  1: split; [ apply H0 | constructor ].
  cbn[Nat.pow] in H.
  epose proof (R0 (i+n) i _) as [HP Hs].
  1: apply IHi; auto; lia.
  split; auto.
  epose proof (IHi n _ _) as [IHP IHs].
  follow IHs.
  follow100 Hs.
  finish.
  Unshelve. all: auto; lia.
Qed.

Lemma R0s' n i:
  2^i*4 < (S n)*3+10 ->
  2^(S i)*4 > (S ((S i)+n))*3+10 ->
  P (n,O) ->
  (P ((S i)+n,O) /\
  config (n,O) -->+ config ((S i)+n,O)).
Proof.
  intros H0 H1 HP.
  epose proof (R0s _ _ H0 HP) as [HP0 Hs0].
  epose proof (R0 (i+n) i _ _) as [HP1 Hs1].
  epose proof (R2 _ _ H1 _) as [HP2 Hs2].
  split; auto.
  follow Hs0.
  follow10 Hs1.
  follow100 Hs2.
  finish.
  Unshelve. all: auto; try lia.
Qed.

Lemma R0s'' n i c:
  2^i*4 < (S n)*3+10 ->
  2^(S i)*4 > (S ((S i)*c+n))*3+10 ->
  P (n,O) ->
  (P (c*(S i)+n,O) /\
  config (n,O) -->* config (c*(S i)+n,O)).
Proof.
  gen n i.
  induction c; intros n i H0 H1 HP.
  1: cbn; split; auto.
  epose proof (IHc n i _ _ _) as [HP0 Hs0].
  epose proof (R0s' (c*(S i)+n) i _ _ _) as [HP1 Hs1].
  split.
  1: applys_eq HP1; f_equal; lia.
  follow Hs0.
  follow100 Hs1.
  finish.
  Unshelve. all: auto; try lia.
Qed.

Definition to_nat2(x:N*N):nat*nat :=
let '(n,i):=x in (N.to_nat n,N.to_nat i).

From BusyCoq Require Import Eqb.

Definition next_rule(x:N*N):N*N+N*N :=
(let '(n,i):=x in
let n' := (N.succ n)*3+10 in
let v := 2^i*4 in
match v ?= n' with
| Eq => inr x
| Lt => inl (N.succ n,N.succ i)
| Gt => 
    let i0:=N.pred i in
    let i1:=N.succ i0 in
    let c:=N.pred (((2^i1*4-n')/3)/i1) in
    if ((2^i0*4 <? n') && ((N.succ (i1*c+n))*3+10 <? 2^i1*4))%bool then
      inl (c*i1+n,0)
    else
    inl (n,0)
end)%N.


Definition simulate T :=
N_iter_until next_rule (inl (0,0))%N T.

Ltac simpl_N2nat := repeat (
  rewrite Nnat.N2Nat.inj_pow ||
  rewrite Nnat.N2Nat.inj_mul ||
  rewrite Nnat.N2Nat.inj_add ||
  rewrite Nnat.N2Nat.inj_succ).

Lemma N2nat_inj_lt(a b:N):
  (a < b)%N <-> (N.to_nat a < N.to_nat b).
Proof.
  rewrite N2Z.inj_lt,Z2Nat.inj_lt; try lia.
Qed.

Lemma next_rule_spec x:
  P (to_nat2 x) ->
  match next_rule x with
  | inl x' => P (to_nat2 x') /\ config (to_nat2 x) -->* config (to_nat2 x')
  | inr x' => x=x' /\ halts tm (config (to_nat2 x))
  end.
Proof.
destruct x as [n i].
unfold next_rule.
unfold to_nat2.
destruct (N.compare_spec (2^i*4) (N.succ n*3+10))%N as [E|E|E].
- intros HP.
  split; auto.
  apply R1; auto.
  generalize (f_equal N.to_nat E).
  simpl_N2nat.
  exact (fun x => x).
- intros HP.
  epose proof (R0 (N.to_nat n) (N.to_nat i) _ HP) as [HP' Hs'].
  simpl_N2nat.
  split; auto.
  apply progress_evstep,R0; auto.
  rewrite N2nat_inj_lt in E.
  gen E.
  simpl_N2nat.
  exact (fun x => x).
  Unshelve.
  rewrite N2nat_inj_lt in E.
  gen E.
  simpl_N2nat.
  exact (fun x => x).
- intros HP.
  remember (N.succ n * 3 + 10)%N as n'.
  remember (N.pred i) as i0.
  remember (N.succ i0) as i1.
  remember (N.pred (((2^i1*4-n')/3)/i1))%N as c.
  assert (P (N.to_nat n, O) /\ config (N.to_nat n,N.to_nat i) -->* config (N.to_nat n,N.to_nat 0)) as [HP' Hs']. {
    epose proof (R2 (N.to_nat n) (N.to_nat i) _ _) as [HP' Hs'].
    split.
    1: apply HP'.
    apply progress_evstep,Hs'.
    Unshelve.
    2: auto.
    subst n'.
    rewrite N2nat_inj_lt in E. gen E.
    simpl_N2nat.
    change (N.to_nat 2) with 2.
    lia.
  }
  destruct (N.ltb_spec (2^i0*4) n')%N; cbn[andb].
  2: split; auto.
  destruct (N.ltb_spec ((N.succ (i1*c+n))*3+10) (2^i1*4))%N; cbn[andb].
  2: split; auto.
  epose proof (R0s'' (N.to_nat n) (N.to_nat i0) (N.to_nat c) _ _ HP') as [HP'' Hs''].
  split.
  1: applys_eq HP''; f_equal; try lia.
  follow Hs'.
  follow Hs''.
  finish.
  Unshelve.
  + gen H.
    subst n'.
    rewrite N2nat_inj_lt.
    simpl_N2nat.
    exact (fun x => x).
  + unfold gt.
    gen H0.
    subst i1.
    rewrite N2nat_inj_lt.
    simpl_N2nat.
    exact (fun x => x).
Qed.

Lemma simulate_spec T:
match simulate T with
| inl x => P (to_nat2 x) /\ c0 -->* config (to_nat2 x)
| inr x => halts tm c0
end.
Proof.
  apply N_iter_until_spec.
  2: split; [cbn; lia | apply init].
  intros x0 [HP Hs].
  pose proof (next_rule_spec x0 HP) as H.
  destruct (next_rule x0) as [x'|x'].
  - destruct H as [HP' Hs'].
    split; auto.
    follow Hs. apply Hs'.
  - destruct H as [Hx' Hs'].
    eapply halts_evstep; eauto.
Qed.

Lemma halts: halts tm c0.
Proof.
  native_cast_no_check (simulate_spec (10^6)%N).
Time Qed.


End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1RF_0LD1RB_1LD1RE_1LA0RD_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+15).
Proof.
  remember (S0 (S n) (n*6+15)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*3+3) -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  replace (S n'*3+2) with (1+(S n'*3+1)) by lia.
  remember (S n'*3+1) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,15)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+4 \/ k = (S n)*3+3) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*3+4))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1RF_0RD1RB_1LD1RE_1LA0RD_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,10)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+3) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*3+3))).
    applys_eq H;
    f_equal; lia.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1RF_1LD1RB_1LD1RE_1LA0RD_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k+1)) -->+
  S0 (S n) (k*2+2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*3+3) -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  replace (S n'*3+2) with (1+(S n'*3+1)) by lia.
  remember (S n'*3+1) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,10)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+4 \/ k = (S n)*3+3) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*3+4))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LA_1RD1RE_0LF1RC_0RD---_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{D}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+15).
Proof.
  remember (S0 (S n) (n*6+15)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*3+3) -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  replace (S n'*3+2) with (1+(S n'*3+1)) by lia.
  remember (S n'*3+1) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,7)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+4 \/ k = (S n)*3+3) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*3+4))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0RC1RA_1LC1RD_1LE0RC_1LA0LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,16)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+3) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*3+3))).
    applys_eq H;
    f_equal; lia.
Qed.

End TM19.



Module TM20.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RA_1LC1RD_1LE0RC_1LA0LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+3) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 2) with (n*3+5+0) by lia.
  replace (S n * 3 + 3) with (n*3+5+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+5)*2+0) with ((n*3+3)+(n*3+7)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+3)+(k+1)) -->+
  S0 (S n) (k*2+2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+3)+(n*3+8))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+8) with (1+(n*3+7)) by lia.
  remember (n*3+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*3+3) -->+
  S0 (S n) (n*6+16).
Proof.
  remember (S0 (S n) (n*6+16)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  replace (S n'*3+2) with (1+(S n'*3+1)) by lia.
  remember (S n'*3+1) as v1.
  es; er.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,16)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*3+2 \/ k >= (S n)*3+4 \/ k = (S n)*3+3) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*3+4))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0RC1RA_1LC1RD_1LE0RC_0RA0LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow]. cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,11)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+2) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+2))).
    applys_eq H;
    f_equal; lia.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RF_1RD0LB_---0RE_1RA1RC_1LF1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{D}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*3+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*3+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 3 + 1) with (n*3+4+0) by lia.
  replace (S n * 3 + 2) with (n*3+4+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*3+4)*2+0) with ((n*3+2)+(n*3+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*3+2)+(k+1)) -->+
  S0 (S n) (k*2+1).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 3 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*6+13).
Proof.
  remember (S0 (S n) (n*6+13)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*3+2)+(n*3+7))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*3+7) with (1+(n*3+6)) by lia.
  remember (n*3+6) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config(x:_+_) :=
match x with
| inl (n,k) => S0 (S n) (k*3)
| inr (n,k) => S0 (S n) (k*3+1)
end.

Lemma init:
  c0 -->* config (inr (0,4)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  unfold config.
  intros [[n k]|[n k]].
  + assert (k*3 <= (S n)*3+1 \/ k*3 >= (S n)*3+3) as E by lia.
    destruct E as [E|E].
    - eexists (inr (n,n*2+4)).
      follow10 (BigStep2 _ _ E).
      finish.
    - eexists (inr (S n,(k-n-2)*2)).
      epose proof (BigStep1 (S n) (k*3-(S n*3+3))).
      applys_eq H;
      f_equal; lia.
  + assert (k*3+1 <= (S n)*3+1 \/ k*3+1 >= (S n)*3+3) as E by lia.
    destruct E as [E|E].
    - eexists (inr (n,n*2+4)).
      follow10 (BigStep2 _ _ E).
      finish.
    - eexists (inl (S n,(k-n-2)*2+1)).
      epose proof (BigStep1 (S n) (k*3+1-(S n*3+3))).
      applys_eq H;
      f_equal; try lia.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_0LD1RB_1LA0RE_1LE1RD_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[0] <* <[1;1]^^0 <| r -->*
  l <| [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1]
| S n0 => L n0 <* <[0] <* <[1;1]^^(n*2+1)
end.

Lemma LInc r n:
  L n <| [1;0]^^0 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 1) with (n*2+3+0) by lia.
  replace (S n * 2 + 2) with (n*2+3+1) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+3)*2+0) with ((n*2+2)+(n*2+4)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^0 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 0) as I1.
  follow I1.
  unfold S1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+0) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  replace (k0*2+(1+k1)) with (((n*2+2)+(n*2+5))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+5) with (1+(n*2+4)) by lia.
  remember (n*2+4) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 2) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,11)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+2) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+2))).
    applys_eq H;
    f_equal; lia.
Qed.

End TM23.

Module TM24.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0LD_1LB0RB_1RA1LE_1LB0RA_1RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> [1;0] *> [1;0;1]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r n:
  l <* <[1;0] <* <[1;1;1]^^0 <| [1;0;1]^^(n+1) *> r -->*
  l <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^n *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]^^2
| S n0 => L n0 <* <[1;0] <* <[1;1;1]^^(n*2+2)
end.

Lemma LInc r n:
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 2) with (n*2+4+0) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+4)*2) with ((n*2+2)+(n*2+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  replace k with (k+0) by lia.
  rewrite Hk.
  replace (k+k0+1) with (k+(k0+1)) by lia.
  follow Incs2.
  unfold S2.
  remember (k*2+1) as k1.
  es; er.
  epose proof (Incs1 _ k0 (2+k1)) as I1.
  follow I1.
  unfold S1.
  replace (k0*2+(2+k1)) with ((n*2+2)+(n*2+6)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+6) with (1+(n*2+5)) by lia.
  remember (n*2+5) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0 (S n) (n*4+11).
Proof.
  remember (S0 (S n) (n*4+11)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  epose proof (Incs1 _ v1 4) as I1.
  follow I1.
  unfold S1.
  replace (v1*2+4) with (v1*2+3+1) by lia.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,8)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC1RF_1RD0LA_1LC0RC_1LC0RB_1RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{D}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> [1;0] *> [1;0;1]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r n:
  l <* <[1;0] <* <[1;1;1]^^0 <| [1;0;1]^^(n+1) *> r -->*
  l <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^n *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]^^2
| S n0 => L n0 <* <[1;0] <* <[1;1;1]^^(n*2+2)
end.

Lemma LInc r n:
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 2) with (n*2+4+0) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+4)*2) with ((n*2+2)+(n*2+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  replace k with (k+0) by lia.
  rewrite Hk.
  replace (k+k0+1) with (k+(k0+1)) by lia.
  follow Incs2.
  unfold S2.
  remember (k*2+1) as k1.
  es; er.
  epose proof (Incs1 _ k0 (2+k1)) as I1.
  follow I1.
  unfold S1.
  replace (k0*2+(2+k1)) with ((n*2+2)+(n*2+6)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+6) with (1+(n*2+5)) by lia.
  remember (n*2+5) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0 (S n) (n*4+11).
Proof.
  remember (S0 (S n) (n*4+11)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  epose proof (Incs1 _ v1 4) as I1.
  follow I1.
  unfold S1.
  replace (v1*2+4) with (v1*2+3+1) by lia.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,6)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC0LD_1LB0RB_1RE1LA_1RB1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> [1;0] *> [1;0;1]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r n:
  l <* <[1;0] <* <[1;1;1]^^0 <| [1;0;1]^^(n+1) *> r -->*
  l <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^n *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]^^2
| S n0 => L n0 <* <[1;0] <* <[1;1;1]^^(n*2+2)
end.

Lemma LInc r n:
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 2) with (n*2+4+0) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+4)*2) with ((n*2+2)+(n*2+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+1)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 1 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+10).
Proof.
  remember (S0 (S n) (n*4+10)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  replace k with (k+0) by lia.
  rewrite Hk.
  replace (k+k0+1) with (k+(k0+1)) by lia.
  follow Incs2.
  unfold S2.
  remember (k*2+1) as k1.
  es; er.
  epose proof (Incs1 _ k0 (2+k1)) as I1.
  follow I1.
  unfold S1.
  replace (k0*2+(2+k1)) with ((n*2+2)+(n*2+6)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+6) with (1+(n*2+5)) by lia.
  remember (n*2+5) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  follow I1.
  unfold S1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0 (S n) (n*4+11).
Proof.
  remember (S0 (S n) (n*4+11)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  epose proof (Incs1 _ v1 4) as I1.
  follow I1.
  unfold S1.
  replace (v1*2+4) with (v1*2+3+1) by lia.
  follow Ov2.
  subst.
  unfold S0.
  cbn[lpow].
  cbn[Str_app].
  finish.
Qed.

Definition config '(n,k) := S0 (S n) k.

Lemma init:
  c0 -->* config (0,2)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
  destruct E as [E|[E|E]].
  - eexists (_,_).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k-(S n*2+3))).
    applys_eq H;
    f_equal; lia.
  - eexists (_,_).
    rewrite E.
    follow10 BigStep3.
    finish.
Qed.

End TM26.


Module TM27.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC0LD_0LB0RB_1RE1LA_1RB1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> const 0.

Definition S1' l a b :=
  l <* <[1;1;1]^^a <| [1;0] *> [1;1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (2+a) b -->* S1 l a (3+b).
Proof.
  es.
Qed.

Lemma Incs1 n l a b:
  S1 l (n*2+a) b -->* S1 l a (n*3+b).
Proof.
  gen l a b.
  ind n Inc1.
Qed.

Lemma Inc1' l a b:
  S1' l (2+a) b -->* S1' l a (3+b).
Proof.
  es.
Qed.

Lemma Incs1' n l a b:
  S1' l (n*2+a) b -->* S1' l a (n*3+b).
Proof.
  gen l a b.
  ind n Inc1'.
Qed.

Lemma Incs11 n l b:
  S1 l (n*2+1) b -->* S1' l 0 (n*3+b+1).
Proof.
  follow Incs1.
  es.
Qed.

Lemma Incs1'1 n l b:
  S1' l (n*2+1) b -->* S1 l 0 (n*3+b+2).
Proof.
  follow Incs1'.
  es.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1;1]^^a <| [1;0;1]^^b *> [1;0] *> [1;0;1]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r n:
  l <* <[1;0] <* <[1;1;1]^^0 <| [1;0;1]^^(n+1) *> r -->*
  l <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^n *> r.
Proof.
  er.
Qed.

Lemma Ov2' l r n:
  l <* <[1;0] <* <[1;1;1]^^0 <| [1;0] *> [1;1;0]^^(n+1) *> r -->*
  l <| [1;0;1]^^1 *> [1;0] *> [1;0] *> [1;1;0]^^n *> r.
Proof.
  er.
Qed.

Lemma Ov2'' l r n:
  l <* <[1;0] <* <[1;1;1]^^0 <| [1;0] *> [1;1;0]^^(n+1) *> r -->*
  l <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^n *> [1;0] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;1;1]^^2
| S n0 => L n0 <* <[1;0] <* <[1;1;1]^^(n*2+2)
end.

Lemma LInc r n:
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 2) with (n*2+4+0) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((n*2+4)*2) with ((n*2+2)+(n*2+6)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^m *> const 0.

Definition S0' n m :=
  L n <| [1;0;1]^^1 *> [1;0] *> [1;0;1]^^m *> [1;0] *> const 0.

Lemma BigStep11 n k:
  S0 n ((n*2+2)+(k*2+1)) -->+
  S0 (S n) (k*3).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  remember (k*2) as k2.
  es. er.
  epose proof (Incs1 k _ 0 1) as I1.
  replace k2 with (k*2+0) by lia.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep12 n k:
  S0 n ((n*2+2)+(k*2+2)) -->+
  S0' (S n) (k*3+1).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k*2+2) with (k*2+1+1) by lia.
  remember (k*2+1) as k2.
  es. er.
  epose proof (Incs1 k _ _ 1) as I1.
  replace k2 with (k*2+1) by lia.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep11' n k:
  S0' n ((n*2+2)+(k*2+1)) -->+
  S0 (S n) (k*3).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  remember (k*2) as k2.
  es. er.
  epose proof (Incs1 k _ 0 1) as I1.
  replace k2 with (k*2+0) by lia.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep12' n k:
  S0' n ((n*2+2)+(k*2+2)) -->+
  S0' (S n) (k*3+1).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k*2+2) with (k*2+1+1) by lia.
  remember (k*2+1) as k2.
  es. er.
  epose proof (Incs1 k _ _ 1) as I1.
  replace k2 with (k*2+1) by lia.
  unfold S1 in I1. cbn in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2_12 n k k0:
  (k*2+1) + (k0*4+2) = S n * 2 + 1 ->
  S0 (S n) (k*2+1) -->+
  S0 (S n) ((k0+k+2)*3).
Proof.
  remember (S0 (S n) ((k0+k+2)*3)) as tg.
  intros Hk.
  unfold S0.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+1) with (k*2+1+0) by lia.
  replace (k*2+1+0+(k0*4+2)+1) with (k*2+1+(k0*4+3)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*4+3) as k2.
  es; er.
  subst k2.
  replace (k0*4+3) with ((k0*2+1)*2+1) by lia.
  remember (k0*2+1) as k0'.
  epose proof (Incs1'1 (k0')) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+k1+2) with ((n*2+2)+(k0'+k*2+4)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+4) with (1+(k0'+k*2+3)) by lia.
  remember (k0'+k*2+3) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+2)*2+0) by lia.
  epose proof (Incs1 (k0+k+2) _ 0 1)%nat as I1.
  unfold S1 in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep2_10 n k k0:
  (k*2+1) + (k0*4+0) = S n * 2 + 1 ->
  S0 (S n) (k*2+1) -->+
  S0' (S n) ((k0+k+1)*3+1).
Proof.
  remember (S0' (S n) ((k0+k+1)*3+1)) as tg.
  intros Hk.
  unfold S0.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+1) with (k*2+1+0) by lia.
  replace (k*2+1+0+(k0*4+0)+1) with (k*2+1+(k0*4+1)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*4+1) as k2.
  es; er.
  subst k2.
  replace (k0*4+1) with ((k0*2+0)*2+1) by lia.
  remember (k0*2+0) as k0'.
  epose proof (Incs1'1 (k0')) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+k1+2) with ((n*2+2)+(k0'+k*2+4)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+4) with (1+(k0'+k*2+3)) by lia.
  remember (k0'+k*2+3) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+1)*2+1) by lia.
  epose proof (Incs11 (k0+k+1) _ 1)%nat as I1.
  unfold S1,S1' in I1.
  follow I1.
  follow Ov2'.
  subst.
  unfold S0,S0'.
  cbn.
  simpl_rotate.
  finish.
Qed.

Lemma BigStep2_03 n k k0:
  (k*2+0) + (k0*4+3) = S n * 2 + 1 ->
  S0 (S n) (k*2+0) -->+
  S0' (S n) ((k0+k+1)*3+1).
Proof.
  remember (S0' (S n) ((k0+k+1)*3+1)) as tg.
  intros Hk.
  unfold S0.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+0) with (k*2+0+0) by lia.
  replace (k*2+0+0+(k0*4+3)+1) with (k*2+0+(k0*4+4)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*4+4) as k2.
  es; er.
  subst k2.
  replace (k0*4+4) with ((k0*2+2)*2+0) by lia.
  remember (k0*2+2) as k0'.
  epose proof (Incs1' (k0')) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+k1) with ((n*2+2)+(k0'+k*2+2)+1) by lia.
  follow Ov2''.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+2) with (1+(k0'+k*2+1)) by lia.
  remember (k0'+k*2+1) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+1)*2+1) by lia.
  epose proof (Incs11 (k0+k+1) _ 1)%nat as I1.
  unfold S1,S1' in I1.
  follow I1.
  follow Ov2''.
  subst.
  unfold S0,S0'.
  cbn.
  finish.
Qed.

Lemma BigStep2_01 n k k0:
  (k*2+0) + (k0*4+1) = S n * 2 + 1 ->
  S0 (S n) (k*2+0) -->+
  S0 (S n) ((k0+k+1)*3).
Proof.
  remember (S0 (S n) ((k0+k+1)*3)) as tg.
  intros Hk.
  unfold S0.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+0) with (k*2+0+0) by lia.
  replace (k*2+0+0+(k0*4+1)+1) with (k*2+0+(k0*4+2)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*4+2) as k2.
  es; er.
  subst k2.
  replace (k0*4+2) with ((k0*2+1)*2+0) by lia.
  remember (k0*2+1) as k0'.
  epose proof (Incs1' (k0')) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+k1) with ((n*2+2)+(k0'+k*2+2)+1) by lia.
  follow Ov2''.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+2) with (1+(k0'+k*2+1)) by lia.
  remember (k0'+k*2+1) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+1)*2+0) by lia.
  epose proof (Incs1 (k0+k+1) _ 0 1)%nat as I1.
  unfold S1,S1' in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  cbn.
  finish.
Qed.

Lemma BigStep2'_12 n k k0:
  (k*2+1) + (k0*4+2) = S n * 2 + 1 ->
  S0' (S n) (k*2+1) -->+
  S0 (S n) ((k0+k+2)*3).
Proof.
  remember (S0 (S n) ((k0+k+2)*3)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+1) with (k*2+1+0) by lia.
  replace (k*2+1+0+(k0*4+2)+1) with (k*2+1+(k0*4+3)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*4+3) as k2.
  es; er.
  subst k2.
  replace (k0*4+3) with ((k0*2+1)*2+1) by lia.
  remember (k0*2+1) as k0'.
  epose proof (Incs11 (k0') _ (1+k1)) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+(1+k1)+1) with ((n*2+2)+(k0'+k*2+4)+1) by lia.
  follow Ov2''.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+4) with (1+(k0'+k*2+3)) by lia.
  remember (k0'+k*2+3) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+2)*2+0) by lia.
  epose proof (Incs1 (k0+k+2) _ 0 1)%nat as I1.
  unfold S1 in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Lemma BigStep2'_10 n k k0:
  (k*2+1) + (k0*4+0) = S n * 2 + 1 ->
  S0' (S n) (k*2+1) -->+
  S0' (S n) ((k0+k+1)*3+1).
Proof.
  remember (S0' (S n) ((k0+k+1)*3+1)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+1) with (k*2+1+0) by lia.
  replace (k*2+1+0+(k0*4+0)+1) with (k*2+1+(k0*4+1)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*4+1) as k2.
  es; er.
  subst k2.
  replace (k0*4+1) with ((k0*2+0)*2+1) by lia.
  remember (k0*2+0) as k0'.
  epose proof (Incs11 (k0') _ (1+k1)) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+(1+k1)+1) with ((n*2+2)+(k0'+k*2+4)+1) by lia.
  follow Ov2''.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+4) with (1+(k0'+k*2+3)) by lia.
  remember (k0'+k*2+3) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+1)*2+1) by lia.
  epose proof (Incs11 (k0+k+1) _ 1)%nat as I1.
  unfold S1,S1' in I1.
  follow I1.
  follow Ov2'.
  subst.
  unfold S0,S0'.
  cbn.
  simpl_rotate.
  finish.
Qed.

Lemma BigStep2'_03 n k k0:
  (k*2+0) + (k0*4+3) = S n * 2 + 1 ->
  S0' (S n) (k*2+0) -->+
  S0 (S n) ((k0+k+2)*3).
Proof.
  remember (S0 (S n) ((k0+k+2)*3)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+0) with (k*2+0+0) by lia.
  replace (k*2+0+0+(k0*4+3)+1) with (k*2+0+(k0*4+4)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*4+4) as k2.
  es; er.
  subst k2.
  replace (k0*4+4) with ((k0*2+2)*2+0) by lia.
  remember (k0*2+2) as k0'.
  epose proof (Incs1 (k0') _ 0 (1+k1)) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+(1+k1)) with ((n*2+2)+(k0'+k*2+3)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+3) with (1+(k0'+k*2+2)) by lia.
  remember (k0'+k*2+2) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+2)*2+0) by lia.
  epose proof (Incs1 (k0+k+2) _ 0 1)%nat as I1.
  unfold S1,S1' in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  cbn.
  finish.
Qed.

Lemma BigStep2'_01 n k k0:
  (k*2+0) + (k0*4+1) = S n * 2 + 1 ->
  S0' (S n) (k*2+0) -->+
  S0' (S n) ((k0+k+1)*3+1).
Proof.
  remember (S0' (S n) ((k0+k+1)*3+1)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (S n*2+2) with (S n*2+1+1) by lia.
  rewrite <-Hk.
  replace (k*2+0) with (k*2+0+0) by lia.
  replace (k*2+0+0+(k0*4+1)+1) with (k*2+0+(k0*4+2)) by lia.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*4+2) as k2.
  es; er.
  subst k2.
  replace (k0*4+2) with ((k0*2+1)*2+0) by lia.
  remember (k0*2+1) as k0'.
  epose proof ((Incs1 k0' _ 0 (1+k1))) as I1.
  unfold S1,S1' in I1.
  follow I1.
  replace (k0'*3+(1+k1)) with ((n*2+2)+(k0'+k*2+3)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k0'+k*2+3) with (1+(k0'+k*2+2)) by lia.
  remember (k0'+k*2+2) as v1.
  es. er.
  clear I1.
  replace v1 with ((k0+k+1)*2+1) by lia.
  epose proof (Incs11 (k0+k+1) _ 1)%nat as I1.
  unfold S1,S1' in I1.
  follow I1.
  follow Ov2''.
  subst.
  unfold S0,S0'.
  cbn.
  finish.
Qed.

Lemma BigStep3 n:
  S0 (S n) (S n*2+2) -->+
  S0' (S n) ((S n)*3+4).
Proof.
  remember (S0' (S n) (n*4+11)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2) as v1.
  es; er.
  replace v1 with (S n'*2+0) by lia.
  epose proof (Incs1' (S n')_ 0 2) as I1.
  unfold S1,S1' in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  subst.
  unfold S0'.
  es.
Qed.

Lemma BigStep3' n:
  S0' (S n) (S n*2+2) -->+
  S0 (S n) ((S n)*3+6).
Proof.
  remember (S0 (S n) ((S n)*3+6)) as tg.
  unfold S0.
  remember (S n) as n'.
  follow LInc.
  cbn[L].
  remember (S n'*2+2) as v1.
  es; er.
  replace v1 with ((S n'+1)*2+0) by lia.
  epose proof (Incs1 (S n'+1)_ 0 1) as I1.
  unfold S1,S1' in I1. cbn in I1.
  follow I1.
  remember ((n'+1)*3+1) as n''.
  er.
  subst.
  unfold S0.
  es.
Qed.

Definition config(x:_+_) :=
match x with
| inl (n,k) => S0 (S n) k
| inr (n,k) => S0' (S n) k
end.

Lemma init:
  c0 -->* config (inl (0,9)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma mod2_cases x:
  exists x0, x=x0*2+0 \/ x=x0*2+1.
Proof.
  exists (x/2).
  pose proof (Nat.Div0.div_mod x 2).
  pose proof (Nat.mod_upper_bound x 2).
  lia.
Qed.

Lemma mod4_cases x:
  exists x0, x=x0*4+0 \/ x=x0*4+1 \/ x=x0*4+2 \/ x=x0*4+3.
Proof.
  exists (x/4).
  pose proof (Nat.Div0.div_mod x 4).
  pose proof (Nat.mod_upper_bound x 4).
  lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  unfold config.
  intros [[n k]|[n k]].
  + assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
    destruct E as [E|[E|E]].
    - remember (S n*2+1-k) as k0'.
      pose proof (mod2_cases k) as Hk.
      pose proof (mod4_cases k0') as Hk0.
      destruct Hk as [k' [Hk|Hk]];
      destruct Hk0 as [k0 [Hk0|[Hk0|[Hk0|Hk0]]]];
      try lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2_01 n k' k0).
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep2_03 n k' k0).
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep2_10 n k' k0).
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2_12 n k' k0).
        2: lia.
        f_equal; lia.
    - remember (k-(S n*2+3)) as k0.
      destruct (mod2_cases k0) as [k' [Hk|Hk]].
      * eexists (inl (_,_)).
        applys_eq (BigStep11 (S n) k').
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep12 (S n) k').
        f_equal; lia.
    - eexists (inr (_,_)).
      applys_eq (BigStep3 (n)).
      f_equal; lia.
  + assert (k <= (S n)*2+1 \/ k >= (S n)*2+3 \/ k = (S n)*2+2) as E by lia.
    destruct E as [E|[E|E]].
    - remember (S n*2+1-k) as k0'.
      pose proof (mod2_cases k) as Hk.
      pose proof (mod4_cases k0') as Hk0.
      destruct Hk as [k' [Hk|Hk]];
      destruct Hk0 as [k0 [Hk0|[Hk0|[Hk0|Hk0]]]];
      try lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep2'_01 n k' k0).
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2'_03 n k' k0).
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep2'_10 n k' k0).
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2'_12 n k' k0).
        2: lia.
        f_equal; lia.
    - remember (k-(S n*2+3)) as k0.
      destruct (mod2_cases k0) as [k' [Hk|Hk]].
      * eexists (inl (_,_)).
        applys_eq (BigStep11' (S n) k').
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep12' (S n) k').
        f_equal; lia.
    - eexists (inl (_,_)).
      applys_eq (BigStep3' (n)).
      f_equal; lia.
Qed.

End TM27.


Module TM28.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LA_---0RD_1RE0RB_1RA1RD_1LF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} <[1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;1] {{D}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r n:
  l <* <[1;1;0;1;0] <* <[1;1]^^0 <| [1;0]^^(n+1) *> r -->*
      l <| [1;0]^^3 *> [1] *> [1;0]^^n *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;0;1;1;1;1]
| S n0 => L n0 <* <[1;1;0;1;0] <* <[1;1]^^(n*2+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^3 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 2) with (n*2+4+0) by lia.
  follow Incs2.
  unfold S2.
  replace ((n*2+4)*2+3) with ((n*2+2)+(n*2+8)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^3 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+2)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+14).
Proof.
  remember (S0 (S n) (n*4+14)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+3) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  replace (k0*2+(1+k1)) with ((n*2+2)+(n*2+9)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+9) with (2+(n*2+7)) by lia.
  remember (n*2+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) (k*2).

Lemma init:
  c0 -->* config (0,4)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k*2 <= (S n)*2+2 \/ k*2 >= (S n)*2+4) as E by lia.
  destruct E as [E|E].
  - eexists (n,n*2+7).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k*2-(S n*2+4))).
    applys_eq H;
    f_equal; try lia.
Qed.

End TM28.


Module TM29.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0RF_1RD0LB_---0RE_1RA0RC_1LF1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} <[1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;1] {{E}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;1]^^a <| [1;0]^^b *> const 0.

Lemma Inc1 l a b:
  S1 l (1+a) b -->* S1 l a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l a b -->* S1 l 0 (a*2+b).
Proof.
  gen l b.
  ind a Inc1.
Qed.

Definition S2 l r a b c :=
  l <* <[1;1]^^a <| [1;0]^^b *> [1] *> [1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r n:
  l <* <[1;1;0;1;0] <* <[1;1]^^0 <| [1;0]^^(n+1) *> r -->*
      l <| [1;0]^^3 *> [1] *> [1;0]^^n *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;0;1;1;1;1]
| S n0 => L n0 <* <[1;1;0;1;0] <* <[1;1]^^(n*2+2)
end.

Lemma LInc r n:
  L n <| [1;0]^^3 *> [1] *> [1;0]^^(n*2+2) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n * 2 + 2) with (n*2+4+0) by lia.
  follow Incs2.
  unfold S2.
  replace ((n*2+4)*2+3) with ((n*2+2)+(n*2+8)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;0]^^3 *> [1] *> [1;0]^^m *> const 0.

Lemma BigStep1 n k:
  S0 n ((n*2+2)+(k+2)) -->+
  S0 (S n) (k*2).
Proof.
  unfold S0.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  epose proof (Incs1 _ k 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  es.
Qed.

Lemma BigStep2 n k:
  k <= S n * 2 + 2 ->
  S0 (S n) k -->+
  S0 (S n) (n*4+14).
Proof.
  remember (S0 (S n) (n*4+14)) as tg.
  intros Hk'.
  destruct (Nat.le_exists_sub _ _ Hk') as [k0 [Hk _]].
  rewrite (Nat.add_comm k0) in Hk.
  unfold S0.
  cbn[L].
  replace k with (k+0) by lia.
  rewrite Hk.
  follow Incs2.
  unfold S2.
  remember (k*2+3) as k1.
  es; er.
  epose proof (Incs1 _ k0 (1+k1)) as I1.
  follow I1.
  unfold S1.
  replace (k0*2+(1+k1)) with ((n*2+2)+(n*2+9)+1) by lia.
  follow Ov2.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (n*2+9) with (2+(n*2+7)) by lia.
  remember (n*2+7) as v1.
  es. er.
  clear I1.
  epose proof (Incs1 _ v1 1) as I1.
  unfold S1 in I1. cbn in I1. rewrite <-const_unfold in I1.
  follow I1.
  follow Ov2.
  subst.
  unfold S0.
  cbn.
  finish.
Qed.

Definition config '(n,k) := S0 (S n) (k*2).

Lemma init:
  c0 -->* config (0,6)%nat.
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n k].
  unfold config.
  assert (k*2 <= (S n)*2+2 \/ k*2 >= (S n)*2+4) as E by lia.
  destruct E as [E|E].
  - eexists (n,n*2+7).
    follow10 (BigStep2 _ _ E).
    finish.
  - eexists (_,_).
    epose proof (BigStep1 (S n) (k*2-(S n*2+4))).
    applys_eq H;
    f_equal; try lia.
Qed.

End TM29.


Module TM30.

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC0RC_1RA0LD_1LC1RE_0RF---_0RC1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;0] {{B}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;0;0]^^a <| [1;1;0]^^b *> const 0.

Definition S1' l a b :=
  l <* <[1;0;0]^^a <| [1;1;0]^^b *> [1;0;1] *> const 0.

Lemma Inc1 l a b:
  S1 l (2+a) b -->* S1 l a (4+b).
Proof.
  es.
Qed.

Lemma Incs1 n l a b:
  S1 l (n*2+a) b -->* S1 l a (n*4+b).
Proof.
  gen l a b.
  ind n Inc1.
Qed.

Lemma Inc1' l a b:
  S1' l (2+a) b -->* S1' l a (4+b).
Proof.
  es.
Qed.

Lemma Incs1' n l a b:
  S1' l (n*2+a) b -->* S1' l a (n*4+b).
Proof.
  gen l a b.
  ind n Inc1'.
Qed.

Lemma Incs10 n b l:
  S1 l (n*2+0) b -->* S1 l 0 (n*4+b).
Proof.
  follow Incs1.
  finish.
Qed.

Lemma Incs11 n b l:
  S1 l (n*2+1) b -->* S1' l 0 (n*4+b+1).
Proof.
  follow Incs1.
  es.
Qed.

Lemma Incs1'0 n b l:
  S1' l (n*2+0) b -->* S1' l 0 (n*4+b).
Proof.
  follow Incs1'.
  finish.
Qed.

Lemma Incs1'1 n b l:
  S1' l (n*2+1) b -->* S1 l 0 (n*4+b+3).
Proof.
  follow Incs1'.
  es.
Qed.


Definition S2 l r a b c :=
  l <* <[1;0;0]^^a <| [1;1;0]^^b *> [1] *> [1;1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[1;1;0;1] <* <[1;0;0]^^0 <| r -->*
  l <| [1;1;0]^^1 *> [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;0]
| S n0 => L n0 <* <[1;1;0;1] <* <[1;0;0]^^n
end.

Lemma LInc r n:
  L n <| [1;1;0]^^1 *> [1] *> [1;1;0]^^(n) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n) with (S n+0) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((S n)*2+1) with ((n)+(n+3)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;1;0]^^1 *> [1] *> [1;1;0]^^m *> const 0.

Definition S0' n m :=
  L n <| [1;1;0]^^1 *> [1] *> [1;1;0]^^m *> [1;0;1] *> const 0.

Lemma BigStep12 n k:
  S0 n (n+(k*2+2)) -->+
  S0' (S n) (k*4).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  remember (k*2) as k0.
  es. er.
  replace k0 with (k*2+0) by lia.
  follow (Incs1'0 k 0).
  unfold S1.
  es.
Qed.

Lemma BigStep13 n k:
  S0 n (n+(k*2+3)) -->+
  S0 (S n) (k*4+3).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k*2+3) with (k*2+1+2) by lia.
  remember (k*2+1) as k0.
  es. er.
  subst k0.
  follow (Incs1'1 k 0).
  unfold S1.
  es.
Qed.

Lemma BigStep1'2 n k:
  S0' n (n+(k*2+2)) -->+
  S0' (S n) (k*4+3).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  remember (k*2) as k0.
  es. er.
  replace k0 with (k*2+0) by lia.
  follow (Incs1'0 k 3).
  unfold S1'.
  es.
Qed.

Lemma BigStep1'3 n k:
  S0' n (n+(k*2+3)) -->+
  S0 (S n) (k*4+6).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k*2+3) with (k*2+1+2) by lia.
  remember (k*2+1) as k0.
  es. er.
  subst k0.
  follow (Incs1'1 k 3).
  unfold S1.
  es.
Qed.

Lemma BigStep211 n k k0:
  (k*2+1) + (k0*2+1) = S n ->
  S0 (S n) (k*2+1) -->+
  S0' (S n) (n*2+2).
Proof.
  remember (S0' (S n) (n*2+2)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (2+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(2+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  rewrite const_unfold.
  replace n with ((k+k0)*2+1) by lia.
  follow (Incs11 (k+k0) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma rot1101 n r:
  [1;1;0]^^n *> 1 >> r =
  1 >> [1;0;1]^^n *> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep212 n k k0:
  (k*2+1) + (k0*2+2) = S n ->
  S0 (S n) (k*2+1) -->+
  S0' (S n) (n*2+3).
Proof.
  remember (S0' (S n) (n*2+3)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (3+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+2))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0+1)*2+0) by lia.
  follow (Incs1'0 (k+k0+1) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep201 n k k0:
  (k*2+0) + (k0*2+1) = S n ->
  S0 (S n) (k*2+0) -->+
  S0 (S n) (n*2+3).
Proof.
  remember (S0 (S n) (n*2+3)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (2+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(2+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  rewrite const_unfold.
  replace n with ((k+k0)*2+0) by lia.
  follow (Incs10 (k+k0) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep202 n k k0:
  (k*2+0) + (k0*2+2) = S n ->
  S0 (S n) (k*2+0) -->+
  S0 (S n) (n*2+4).
Proof.
  remember (S0 (S n) (n*2+4)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (3+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+2))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+1) by lia.
  follow (Incs1'1 (k+k0) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'11 n k k0:
  (k*2+1) + (k0*2+1) = S n ->
  S0' (S n) (k*2+1) -->+
  S0 (S n) (n*2+5).
Proof.
  remember (S0 (S n) (n*2+5)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (3+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+4))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+1) by lia.
  follow (Incs1'1 (k+k0) 4).
  unfold S1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'12 n k k0:
  (k*2+1) + (k0*2+2) = S n ->
  S0' (S n) (k*2+1) -->+
  S0 (S n) (n*2+6).
Proof.
  remember (S0 (S n) (n*2+6)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (4+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(4+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0+1)*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 (k+k0+1) 6).
  unfold S1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'01 n k k0:
  (k*2+0) + (k0*2+1) = S n ->
  S0' (S n) (k*2+0) -->+
  S0' (S n) (n*2+4).
Proof.
  remember (S0' (S n) (n*2+4)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (3+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+4))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+0) by lia.
  follow (Incs1'0 (k+k0) 4).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'02 n k k0:
  (k*2+0) + (k0*2+2) = S n ->
  S0' (S n) (k*2+0) -->+
  S0' (S n) (n*2+5).
Proof.
  remember (S0' (S n) (n*2+5)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (4+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(4+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+1) by lia.
  rewrite const_unfold.
  follow (Incs11 (k+k0) 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep310 n:
  S0 (n*2+1) (n*2+1) -->+
  S0' (n*2+1) (n*4+3).
Proof.
  remember (S0' (n*2+1) (n*4+3)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep311 n:
  S0 (n*2+1) (n*2+2) -->+
  S0 (n*2+1) (n*4+5).
Proof.
  remember (S0 (n*2+1) (n*4+5)) as tg.
  unfold S0,S0'.
  replace (n*2+2) with (n*2+1+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 5).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep320 n:
  S0 (n*2+2) (n*2+2) -->+
  S0 (n*2+2) (n*4+6).
Proof.
  remember (S0 (n*2+2) (n*4+6)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep321 n:
  S0 (n*2+2) (n*2+3) -->+
  S0' (n*2+2) (n*4+6).
Proof.
  remember (S0' (n*2+2) (n*4+6)) as tg.
  unfold S0,S0'.
  replace (n*2+3) with (n*2+2+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'10 n:
  S0' (n*2+1) (n*2+1) -->+
  S0 (n*2+1) (n*4+6).
Proof.
  remember (S0 (n*2+1) (n*4+6)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 6).
  unfold S1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'11 n:
  S0' (n*2+1) (n*2+2) -->+
  S0' (n*2+1) (n*4+6).
Proof.
  remember (S0' (n*2+1) (n*4+6)) as tg.
  unfold S0,S0'.
  replace (n*2+2) with (n*2+1+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'20 n:
  S0' (n*2+2) (n*2+2) -->+
  S0' (n*2+2) (n*4+7).
Proof.
  remember (S0' (n*2+2) (n*4+7)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 7).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'21 n:
  S0' (n*2+2) (n*2+3) -->+
  S0 (n*2+2) (n*4+9).
Proof.
  remember (S0 (n*2+2) (n*4+9)) as tg.
  unfold S0,S0'.
  replace (n*2+3) with (n*2+2+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 9).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Definition config(x:_+_) :=
match x with
| inl (n,k) => S0 (S n) k
| inr (n,k) => S0' (S n) k
end.

Lemma init:
  c0 -->* config (inl (0,3)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma mod2_cases x:
  exists x0, x=x0*2+0 \/ x=x0*2+1.
Proof.
  exists (x/2).
  pose proof (Nat.Div0.div_mod x 2).
  pose proof (Nat.mod_upper_bound x 2).
  lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  unfold config.
  intros [[n k]|[n k]].
  + assert (k <= n \/ k >= n+3 \/ k = n+1 \/ k = n+2) as E by lia.
    destruct E as [E|[E|[E|E]]].
    - remember (n-k) as k0.
      destruct (mod2_cases k) as [k' [Hk|Hk]];
      destruct (mod2_cases k0) as [k0' [Hk0|Hk0]].
      * eexists (inl (_,_)).
        applys_eq (BigStep201 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep202 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep211 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep212 n k' k0').
        2: lia.
        f_equal; lia.
    - remember (k-(n+3)) as k0.
      destruct (mod2_cases k0) as [k' [Hk|Hk]].
      * eexists (inr (_,_)).
        applys_eq (BigStep12 (S n) k').
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep13 (S n) k').
        f_equal; lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inr (n'*2,_)).
        applys_eq (BigStep310 n').
        all: f_equal; try lia.
      * eexists (inl (n'*2+1,_)).
        applys_eq (BigStep320 n').
        all: f_equal; try lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inl (n'*2,_)).
        applys_eq (BigStep311 n').
        all: f_equal; try lia.
      * eexists (inr (n'*2+1,_)).
        applys_eq (BigStep321 n').
        all: f_equal; try lia.
  + assert (k <= n \/ k >= n+3 \/ k = n+1 \/ k = n+2) as E by lia.
    destruct E as [E|[E|[E|E]]].
    - remember (n-k) as k0.
      destruct (mod2_cases k) as [k' [Hk|Hk]];
      destruct (mod2_cases k0) as [k0' [Hk0|Hk0]].
      * eexists (inr (_,_)).
        applys_eq (BigStep2'01 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep2'02 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2'11 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2'12 n k' k0').
        2: lia.
        f_equal; lia.
    - remember (k-(n+3)) as k0.
      destruct (mod2_cases k0) as [k' [Hk|Hk]].
      * eexists (inr (_,_)).
        applys_eq (BigStep1'2 (S n) k').
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep1'3 (S n) k').
        f_equal; lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inl (n'*2,_)).
        applys_eq (BigStep3'10 n').
        all: f_equal; try lia.
      * eexists (inr (n'*2+1,_)).
        applys_eq (BigStep3'20 n').
        all: f_equal; try lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inr (n'*2,_)).
        applys_eq (BigStep3'11 n').
        all: f_equal; try lia.
      * eexists (inl (n'*2+1,_)).
        applys_eq (BigStep3'21 n').
        all: f_equal; try lia.
Qed.

End TM30.


Module TM31.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC0RC_1RA0RA_1LA1RE_0RF---_0RA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;0] {{C}}> r) (at level 30).

Definition S1 l a b :=
  l <* <[1;0;0]^^a <| [1;1;0]^^b *> const 0.

Definition S1' l a b :=
  l <* <[1;0;0]^^a <| [1;1;0]^^b *> [1;0;1] *> const 0.

Lemma Inc1 l a b:
  S1 l (2+a) b -->* S1 l a (4+b).
Proof.
  es.
Qed.

Lemma Incs1 n l a b:
  S1 l (n*2+a) b -->* S1 l a (n*4+b).
Proof.
  gen l a b.
  ind n Inc1.
Qed.

Lemma Inc1' l a b:
  S1' l (2+a) b -->* S1' l a (4+b).
Proof.
  es.
Qed.

Lemma Incs1' n l a b:
  S1' l (n*2+a) b -->* S1' l a (n*4+b).
Proof.
  gen l a b.
  ind n Inc1'.
Qed.

Lemma Incs10 n b l:
  S1 l (n*2+0) b -->* S1 l 0 (n*4+b).
Proof.
  follow Incs1.
  finish.
Qed.

Lemma Incs11 n b l:
  S1 l (n*2+1) b -->* S1' l 0 (n*4+b+1).
Proof.
  follow Incs1.
  es.
Qed.

Lemma Incs1'0 n b l:
  S1' l (n*2+0) b -->* S1' l 0 (n*4+b).
Proof.
  follow Incs1'.
  finish.
Qed.

Lemma Incs1'1 n b l:
  S1' l (n*2+1) b -->* S1 l 0 (n*4+b+3).
Proof.
  follow Incs1'.
  es.
Qed.


Definition S2 l r a b c :=
  l <* <[1;0;0]^^a <| [1;1;0]^^b *> [1] *> [1;1;0]^^c *> r.

Lemma Inc2 l r a b c:
  S2 l r (1+a) b (1+c) -->* S2 l r a (2+b) c.
Proof.
  es.
Qed.

Lemma Incs2 n l r a b c:
  S2 l r (n+a) b (n+c) -->* S2 l r a (n*2+b) c.
Proof.
  gen l r a b c.
  ind n Inc2.
Qed.

Lemma Ov2 l r:
  l <* <[1;1;0;1] <* <[1;0;0]^^0 <| r -->*
  l <| [1;1;0]^^1 *> [1] *> r.
Proof.
  er.
Qed.

Fixpoint L n :=
match n with
| O => const 0 <* <[1;0]
| S n0 => L n0 <* <[1;1;0;1] <* <[1;0;0]^^n
end.

Lemma LInc r n:
  L n <| [1;1;0]^^1 *> [1] *> [1;1;0]^^(n) *> r -->*
  L (S n) |> r.
Proof.
  gen r.
  induction n; intros.
  1: step1s.
  cbn[L].
  replace (S n) with (S n+0) by lia.
  follow Incs2.
  unfold S2.
  follow Ov2.
  replace ((S n)*2+1) with ((n)+(n+3)) by lia.
  rewrite lpow_add,Str_app_assoc.
  cbn in IHn.
  follow IHn.
  es.
Qed.

Definition S0 n m :=
  L n <| [1;1;0]^^1 *> [1] *> [1;1;0]^^m *> const 0.

Definition S0' n m :=
  L n <| [1;1;0]^^1 *> [1] *> [1;1;0]^^m *> [1;0;1] *> const 0.

Lemma BigStep12 n k:
  S0 n (n+(k*2+2)) -->+
  S0' (S n) (k*4).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  remember (k*2) as k0.
  es. er.
  replace k0 with (k*2+0) by lia.
  follow (Incs1'0 k 0).
  unfold S1.
  es.
Qed.

Lemma BigStep13 n k:
  S0 n (n+(k*2+3)) -->+
  S0 (S n) (k*4+3).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k*2+3) with (k*2+1+2) by lia.
  remember (k*2+1) as k0.
  es. er.
  subst k0.
  follow (Incs1'1 k 0).
  unfold S1.
  es.
Qed.

Lemma BigStep1'2 n k:
  S0' n (n+(k*2+2)) -->+
  S0' (S n) (k*4+3).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  remember (k*2) as k0.
  es. er.
  replace k0 with (k*2+0) by lia.
  follow (Incs1'0 k 3).
  unfold S1'.
  es.
Qed.

Lemma BigStep1'3 n k:
  S0' n (n+(k*2+3)) -->+
  S0 (S n) (k*4+6).
Proof.
  unfold S0,S0'.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  replace (k*2+3) with (k*2+1+2) by lia.
  remember (k*2+1) as k0.
  es. er.
  subst k0.
  follow (Incs1'1 k 3).
  unfold S1.
  es.
Qed.

Lemma BigStep211 n k k0:
  (k*2+1) + (k0*2+1) = S n ->
  S0 (S n) (k*2+1) -->+
  S0' (S n) (n*2+2).
Proof.
  remember (S0' (S n) (n*2+2)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (2+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(2+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  rewrite const_unfold.
  replace n with ((k+k0)*2+1) by lia.
  follow (Incs11 (k+k0) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma rot1101 n r:
  [1;1;0]^^n *> 1 >> r =
  1 >> [1;0;1]^^n *> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Lemma BigStep212 n k k0:
  (k*2+1) + (k0*2+2) = S n ->
  S0 (S n) (k*2+1) -->+
  S0' (S n) (n*2+3).
Proof.
  remember (S0' (S n) (n*2+3)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (3+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+2))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0+1)*2+0) by lia.
  follow (Incs1'0 (k+k0+1) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep201 n k k0:
  (k*2+0) + (k0*2+1) = S n ->
  S0 (S n) (k*2+0) -->+
  S0 (S n) (n*2+3).
Proof.
  remember (S0 (S n) (n*2+3)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (2+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(2+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  rewrite const_unfold.
  replace n with ((k+k0)*2+0) by lia.
  follow (Incs10 (k+k0) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep202 n k k0:
  (k*2+0) + (k0*2+2) = S n ->
  S0 (S n) (k*2+0) -->+
  S0 (S n) (n*2+4).
Proof.
  remember (S0 (S n) (n*2+4)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (3+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+2))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+1) by lia.
  follow (Incs1'1 (k+k0) 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'11 n k k0:
  (k*2+1) + (k0*2+1) = S n ->
  S0' (S n) (k*2+1) -->+
  S0 (S n) (n*2+5).
Proof.
  remember (S0 (S n) (n*2+5)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (3+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+4))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+1) by lia.
  follow (Incs1'1 (k+k0) 4).
  unfold S1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'12 n k k0:
  (k*2+1) + (k0*2+2) = S n ->
  S0' (S n) (k*2+1) -->+
  S0 (S n) (n*2+6).
Proof.
  remember (S0 (S n) (n*2+6)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+1) with (k*2+1+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+1)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (4+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(4+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0+1)*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 (k+k0+1) 6).
  unfold S1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'01 n k k0:
  (k*2+0) + (k0*2+1) = S n ->
  S0' (S n) (k*2+0) -->+
  S0' (S n) (n*2+4).
Proof.
  remember (S0' (S n) (n*2+4)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  follow (Incs10 k0 (3+k1)).
  unfold S1.
  follow Ov2.
  replace (k0*4+(3+k1)) with (((n)+(n+4))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+0) by lia.
  follow (Incs1'0 (k+k0) 4).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep2'02 n k k0:
  (k*2+0) + (k0*2+2) = S n ->
  S0' (S n) (k*2+0) -->+
  S0' (S n) (n*2+5).
Proof.
  remember (S0' (S n) (n*2+5)) as tg.
  intros Hk.
  unfold S0,S0'.
  cbn[L].
  replace (k*2+0) with (k*2+0+0) by lia.
  rewrite <-Hk.
  follow Incs2.
  unfold S2.
  remember ((k*2+0)*2+1) as k1.
  remember (k0*2) as k0'.
  es; er.
  replace k0' with (k0*2+0) by lia.
  rewrite <-rot1101.
  follow (Incs1'0 k0 (4+k1)).
  unfold S1'.
  follow Ov2.
  replace (k0*4+(4+k1)) with (((n)+(n+3))) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  remember (L (S n)) as l.
  es. er.
  replace n with ((k+k0)*2+1) by lia.
  rewrite const_unfold.
  follow (Incs11 (k+k0) 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep310 n:
  S0 (n*2+1) (n*2+1) -->+
  S0' (n*2+1) (n*4+3).
Proof.
  remember (S0' (n*2+1) (n*4+3)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 3).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep311 n:
  S0 (n*2+1) (n*2+2) -->+
  S0 (n*2+1) (n*4+5).
Proof.
  remember (S0 (n*2+1) (n*4+5)) as tg.
  unfold S0,S0'.
  replace (n*2+2) with (n*2+1+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 5).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep320 n:
  S0 (n*2+2) (n*2+2) -->+
  S0 (n*2+2) (n*4+6).
Proof.
  remember (S0 (n*2+2) (n*4+6)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep321 n:
  S0 (n*2+2) (n*2+3) -->+
  S0' (n*2+2) (n*4+6).
Proof.
  remember (S0' (n*2+2) (n*4+6)) as tg.
  unfold S0,S0'.
  replace (n*2+3) with (n*2+2+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'10 n:
  S0' (n*2+1) (n*2+1) -->+
  S0 (n*2+1) (n*4+6).
Proof.
  remember (S0 (n*2+1) (n*4+6)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 6).
  unfold S1.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'11 n:
  S0' (n*2+1) (n*2+2) -->+
  S0' (n*2+1) (n*4+6).
Proof.
  remember (S0' (n*2+1) (n*4+6)) as tg.
  unfold S0,S0'.
  replace (n*2+2) with (n*2+1+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+1)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 6).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'20 n:
  S0' (n*2+2) (n*2+2) -->+
  S0' (n*2+2) (n*4+7).
Proof.
  remember (S0' (n*2+2) (n*4+7)) as tg.
  unfold S0,S0'.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  follow (Incs1'0 n 7).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Lemma BigStep3'21 n:
  S0' (n*2+2) (n*2+3) -->+
  S0 (n*2+2) (n*4+9).
Proof.
  remember (S0 (n*2+2) (n*4+9)) as tg.
  unfold S0,S0'.
  replace (n*2+3) with (n*2+2+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow LInc.
  cbn[L].
  remember (L (n*2+2)) as l.
  es; er.
  replace (n*2) with (n*2+0) by lia.
  rewrite const_unfold.
  follow (Incs10 n 9).
  unfold S1'.
  follow Ov2.
  subst.
  unfold S0,S0'.
  finish.
Qed.

Definition config(x:_+_) :=
match x with
| inl (n,k) => S0 (S n) k
| inr (n,k) => S0' (S n) k
end.

Lemma init:
  c0 -->* config (inl (0,6)%nat).
Proof.
  unfold config,S0; cbn.
  solve_init.
Qed.

Lemma mod2_cases x:
  exists x0, x=x0*2+0 \/ x=x0*2+1.
Proof.
  exists (x/2).
  pose proof (Nat.Div0.div_mod x 2).
  pose proof (Nat.mod_upper_bound x 2).
  lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  unfold config.
  intros [[n k]|[n k]].
  + assert (k <= n \/ k >= n+3 \/ k = n+1 \/ k = n+2) as E by lia.
    destruct E as [E|[E|[E|E]]].
    - remember (n-k) as k0.
      destruct (mod2_cases k) as [k' [Hk|Hk]];
      destruct (mod2_cases k0) as [k0' [Hk0|Hk0]].
      * eexists (inl (_,_)).
        applys_eq (BigStep201 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep202 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep211 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep212 n k' k0').
        2: lia.
        f_equal; lia.
    - remember (k-(n+3)) as k0.
      destruct (mod2_cases k0) as [k' [Hk|Hk]].
      * eexists (inr (_,_)).
        applys_eq (BigStep12 (S n) k').
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep13 (S n) k').
        f_equal; lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inr (n'*2,_)).
        applys_eq (BigStep310 n').
        all: f_equal; try lia.
      * eexists (inl (n'*2+1,_)).
        applys_eq (BigStep320 n').
        all: f_equal; try lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inl (n'*2,_)).
        applys_eq (BigStep311 n').
        all: f_equal; try lia.
      * eexists (inr (n'*2+1,_)).
        applys_eq (BigStep321 n').
        all: f_equal; try lia.
  + assert (k <= n \/ k >= n+3 \/ k = n+1 \/ k = n+2) as E by lia.
    destruct E as [E|[E|[E|E]]].
    - remember (n-k) as k0.
      destruct (mod2_cases k) as [k' [Hk|Hk]];
      destruct (mod2_cases k0) as [k0' [Hk0|Hk0]].
      * eexists (inr (_,_)).
        applys_eq (BigStep2'01 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inr (_,_)).
        applys_eq (BigStep2'02 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2'11 n k' k0').
        2: lia.
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep2'12 n k' k0').
        2: lia.
        f_equal; lia.
    - remember (k-(n+3)) as k0.
      destruct (mod2_cases k0) as [k' [Hk|Hk]].
      * eexists (inr (_,_)).
        applys_eq (BigStep1'2 (S n) k').
        f_equal; lia.
      * eexists (inl (_,_)).
        applys_eq (BigStep1'3 (S n) k').
        f_equal; lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inl (n'*2,_)).
        applys_eq (BigStep3'10 n').
        all: f_equal; try lia.
      * eexists (inr (n'*2+1,_)).
        applys_eq (BigStep3'20 n').
        all: f_equal; try lia.
    - subst k.
      destruct (mod2_cases n) as [n' [Hn|Hn]].
      * eexists (inr (n'*2,_)).
        applys_eq (BigStep3'11 n').
        all: f_equal; try lia.
      * eexists (inl (n'*2+1,_)).
        applys_eq (BigStep3'21 n').
        all: f_equal; try lia.
Qed.

End TM31.


