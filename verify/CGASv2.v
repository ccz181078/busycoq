From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import SeqTape.


Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac es :=
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc;
  repeat rewrite lpow_mul;
  execute_with_shift_rule.



Open Scope list.


Section CGASv2.
Hypothesis tm:TM.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Hypothesis QL QR QL':Q.
Hypothesis qL qR qL':list sym.
Hypothesis f0 f0' d0 d1 d1' d1a:list sym.
Hypothesis w0 w1 w2:list sym.
Hypothesis a0:nat.

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Notation "l <|' r" :=
  (l <{{QL'}} qL' *> r) (at level 30).

Hypothesis R_carry:
  forall l r n,
  l |> f0^^n *> d1 *> r -->*
  l <* f0'^^n <* d1' |> r.

Hypothesis RL:
  forall l r n,
  l |> f0^^n *> d0 *> r -->+
  l <| f0^^n *> d1 *> r.

Hypothesis R_return:
  forall l r n,
  l <* f0'^^n <* d1' <| r -->*
  l <| f0^^n *> d0 *> r.

Hypothesis RInc0:
  forall l n,
  l |> f0^^n *> const 0 -->+
  l <| f0^^n *> d1a *> const 0.

Hypothesis RInc1:
  forall l n,
  l |> f0^^n *> d1a *> const 0 -->+
  l <| f0^^(1+n) *> const 0.

Definition R n :=
  f0^^(n/2) *> (
    match n mod 2 with
    | O => []
    | S O => d1a
    | _ => []
    end
  ) *> const 0.

Lemma RInc l n:
  l |> R n -->+
  l <| R (1+n).
Proof.
  unfold R.
  pose proof (Nat.mod_upper_bound n 2) as H.
  pose proof (Nat.div_mod_eq n 2) as H0.
  remember (n/2) as n0.
  remember (n mod 2) as n1.
  clear Heqn1 Heqn0.
  subst n.
  assert (n1=0\/n1=1)%nat as E by lia.
  destruct E as [E|E]; subst n1.
  - follow10 RInc0.
    replace (1+(2*n0+0)) with (n0*2+1) by lia.
    rewrite Nat.div_add_l. 2: lia.
    replace (n0*2+1) with (1+n0*2) by lia.
    rewrite Nat.Div0.mod_add.
    cbn.
    finish.
  - follow10 RInc1.
    replace (1+(2*n0+1)) with ((1+n0)*2+0) by lia.
    rewrite Nat.div_add_l. 2: lia.
    replace ((1+n0)*2+0) with (0+(1+n0)*2) by lia.
    rewrite Nat.Div0.mod_add.
    cbn.
    finish.
Qed.

Lemma Rsub2 n:
  R (2+n) = f0 *> R n.
Proof.
  unfold R.
  replace ((2+n)/2) with (1+n/2). 2:{
    remember (n/2) as n0.
    rewrite (Nat.div_mod_eq n 2).
    rewrite <-Heqn0.
    replace (2+(2*n0+n mod 2)) with ((n0+1)*2+n mod 2) by lia.
    rewrite Nat.div_add_l. 2: lia.
    pose proof (Nat.mod_upper_bound n 2).
    rewrite Nat.div_small; lia.
  }
  replace ((2+n) mod 2) with (n mod 2) by (rewrite <-Nat.Div0.add_mod_idemp_l; reflexivity).
  simpl_tape.
  reflexivity.
Qed.

Opaque R.


Fixpoint RCounter (ls:list nat)(n:nat) :=
match ls with
| nil => R n
| h::t => f0^^h *> (if Nat.even n then d0 else d1) *> RCounter t (n/2)
end.

Lemma RC_Inc l ls n:
  l |> RCounter ls n -->+
  l <| RCounter ls (S n).
Proof.
  gen l n.
  induction ls as [|h t]; intros.
  1: apply RInc.
  cbn[RCounter].
  pose proof (even_div2 n) as E0.
  destruct (Nat.even n) eqn:E.
  - follow10 RL.
    rewrite Nat.even_succ.
    unfold Nat.odd.
    rewrite E.
    cbn[negb].
    rewrite even_S_div2; auto.
  - follow R_carry.
    follow10 IHt.
    follow R_return.
    rewrite Nat.even_succ.
    unfold Nat.odd.
    rewrite E.
    cbn[negb].
    rewrite odd_S_div2; auto.
Qed.



Hypothesis LR1:
  forall l r,
  l <* w0 <| f0 *> r -->+
  l <* w1 <* w0 |> r.

Hypothesis LR2:
  forall l r,
  l <* w0 |> d0 *> r -->+
  l <* w2 <* w0 |> r.

Lemma RC_Halve l xs n:
  l <* w0 |> RCounter (O::xs) (n*2) -->+
  l <* w2 <* w0 |> RCounter xs n.
Proof.
  cbn[RCounter].
  rewrite Nat.div_mul. 2: lia.
  replace (Nat.even (n*2)) with true.
  2: symmetry; rewrite Nat.even_spec; exists n; lia.
  follow10 LR2.
  finish.
Qed.

Lemma RC_LR l n x xs:
  l <* w0 <| RCounter ((S x)::xs) n -->+
  l <* w1 <* w0 |> RCounter (x::xs) n.
Proof.
  cbn[RCounter].
  cbn[lpow].
  rewrite Str_app_assoc.
  follow10 LR1.
  finish.
Qed.

Lemma R_LR l n:
  l <* w0 <| R (2+n) -->+
  l <* w1 <* w0 |> R n.
Proof.
  rewrite Rsub2.
  follow10 LR1.
  finish.
Qed.

Lemma RC_Incs l n x xs:
  l <* w0 |> RCounter (x::xs) n -->*
  l <* w1^^x <* w0 |> RCounter (O::xs) (x+n).
Proof.
  gen l n.
  induction x; intros.
  - finish.
  - follow100 RC_Inc.
    follow100 RC_LR.
    follow IHx.
    rewrite lpow_shift'.
    cbn[lpow].
    rewrite Str_app_assoc.
    finish.
Qed.

Lemma RC_Incs_Halve l x xs c:
  l <* w0 |> RCounter ((2+x)::xs) (x+c*2) -->*
  l <* w1^^(2+x) <* w2 <* w0 |> RCounter xs (1+x+c).
Proof.
  follow RC_Incs.
  replace (2+x+(x+c*2)) with ((1+x+c)*2) by lia.
  follow100 RC_Halve.
  finish.
Qed.


Definition LBlock i := w2++w1^^i.

Lemma RC_IHs l x0 n c:
  l <* w0 |> RCounter (arith_seq_inc (2+x0) n 1) (x0+c*2^n) -->*
  l <* LBlock^^^(arith_seq_dec (1+n+x0) n 1) <* w0 |> R (n+x0+c).
Proof.
  gen x0 l.
  induction n; intros.
  - cbn.
    finish.
  - cbn[arith_seq_inc].
    cbn[Nat.pow].
    replace (c*(2*2^n)) with (c*2^n*2) by lia.
    follow RC_Incs_Halve.
    specialize (IHn (1+x0)).
    follow IHn.
    rewrite arith_seq_dec_tail.
    2: lia.
    rewrite flat_map_app.
    cbn[flat_map].
    repeat rewrite Str_app_assoc.
    replace (1+S n+x0-1*n) with (2+x0) by lia.
    unfold LBlock.
    rewrite Str_app_assoc.
    finish.
Qed.


Lemma R_Incs l n:
  l <* w0 |> R n -->*
  l <* w1^^n <* w0 <| R 1.
Proof.
  gen l.
  induction n; intros.
  - follow100 RInc.
    finish.
  - follow100 RInc.
    follow100 R_LR.
    follow IHn.
    rewrite lpow_shift'.
    cbn[lpow].
    rewrite Str_app_assoc.
    finish.
Qed.

Transparent R.

Hypothesis R_Rst:
  forall l n,
  l <* w1^^n <* w0 <| R 1 -->*
  l <|' f0^^(1+n) *> d0 *> R 1.

Hypothesis RC_Rst:
  forall l r n,
  l <* LBlock n <|' r -->*
  l <|' f0^^n *> d0 *> r.

Lemma RC_Rsts l n n0:
  l <* LBlock^^^arith_seq_dec (1+n) n 1 <|' RCounter (arith_seq_inc (2+n) n0 1) (2^(n0)) -->*
  l <|' RCounter (arith_seq_inc 2 (n+n0) 1) (2^(n+n0)).
Proof.
  gen n0.
  induction n; intros.
  1: cbn; finish.
  cbn[arith_seq_dec].
  cbn[flat_map].
  rewrite Str_app_assoc.
  follow RC_Rst.
  specialize (IHn (S n0)).
  cbn[arith_seq_inc] in IHn.
  cbn[RCounter] in IHn.
  replace (1+S n0) with (S (1+n0)) in IHn by lia.
  cbn[Nat.pow] in IHn.
  rewrite (Nat.mul_comm 2 (2^(n0))) in IHn.
  rewrite even_mul2,Nat.div_mul in IHn. 2: lia.
  follow IHn.
  finish.
Qed.

Definition l0 := w2 *> w1 *> const 0.
Hypothesis l0_LR:
  forall r,
  l0 <|' r -->+
  l0 <* w0 |> r.

Definition config n :=
  l0 <* w0 |> RCounter (arith_seq_inc (2+0) n 1) (0+1*2^n).

Hypothesis init:
  c0 -->* config 0.

Lemma BigStep n:
  config n -->+
  config (S n).
Proof.
  follow RC_IHs.
  follow R_Incs.
  follow R_Rst.
  repeat rewrite Nat.add_0_r.
  pose proof (RC_Rsts l0 n 1) as H.
  cbn[arith_seq_inc] in H.
  cbn[RCounter] in H.
  follow H.
  follow10 l0_LR.
  unfold config.
  replace (n+1) with (1+n) by lia.
  cbn[Nat.add].
  finish.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  eexists.
  apply BigStep.
Qed.


End CGASv2.


Inductive Cert :=
| cert1
  (QL QR QL': Q)
  (qL qR qL' f0 f0' d0 d1 d1' d1a w0 w1 w2 : list Sym).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL ?QR ?QL'
  ?qL ?qR ?qL' ?f0 ?f0' ?d0 ?d1 ?d1' ?d1a ?w0 ?w1 ?w2) =>
  eapply (nonhalt _
    QL QR QL'
    qL qR qL'
    f0 f0' d0 d1 d1' d1a
    w0 w1 w2);
  [ try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | unfold config; cbn; try (solve_init; fail)
  ]
end.



Definition tm0 := Eval compute in (TM_from_str "1LB0RF_0LC0LB_1RD1RA_0RC0RE_0RA---_1RA1LF").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 B A B [0] [1] [0;1;0]
  [1;0;1;0] [0;1;0;1] [0;1;0] [1;1;0] [0;1;1] [1;0]
  [0;1;0;0] [0;1;0;1] [1;0;1]).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1LB0RF_0LC0LB_1RD1RA_0RC0RE_0RA---_1RA0RA").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 B A B [0] [1] [0;1;0]
  [1;0;1;0] [0;1;0;1] [0;1;0] [1;1;0] [0;1;1] [1;0]
  [0;1;0;0] [0;1;0;1] [1;0;1]).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1LB0RF_0LC0LB_1RD1RA_0RC1RE_1LA---_1RA0RA").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 B A B [0] [1] [0;1;0]
  [1;0;1;0] [0;1;0;1] [0;1;0] [1;1;0] [0;1;1] [1;0]
  [0;1;0;0] [0;1;0;1] [1;0;1]).
Qed.






