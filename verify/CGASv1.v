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


Section CGASv1.
Hypothesis tm:TM.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Hypothesis QL QR:Q.
Hypothesis qL qR:list sym.
Hypothesis f0 f0' d0 d1 d1' d1a:list sym.
Hypothesis w0 w1 w2:list sym.
Hypothesis a0:nat.

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

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
  l <* w0 <| d0 *> f0 *> r -->+
  l <* w2 <* w0 |> r.

Lemma RC_Halve l x xs n:
  l <* w0 <| RCounter (O::S x::xs) (n*2) -->+
  l <* w2 <* w0 |> RCounter (x::xs) n.
Proof.
  cbn[RCounter].
  rewrite Nat.div_mul. 2: lia.
  rewrite even_mul2.
  cbn[lpow].
  rewrite Str_app_assoc.
  follow10 LR2.
  finish.
Qed.

Lemma RC_Halve' l n:
  l <* w0 <| RCounter (O::nil) ((2+n)*2) -->+
  l <* w2 <* w0 |> R n.
Proof.
  cbn[RCounter].
  rewrite Nat.div_mul. 2: lia.
  rewrite even_mul2.
  rewrite Rsub2.
  cbn[lpow].
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
    repeat rewrite Str_app_assoc.
    finish.
Qed.

Lemma RC_Incs_Halve l x y xs c:
  l <* w0 |> RCounter ((1+x)::(S y)::xs) (x+c*2) -->*
  l <* w1^^(1+x) <* w2 <* w0 |> RCounter (y::xs) (1+x+c).
Proof.
  follow RC_Incs.
  follow100 RC_Inc.
  replace (S(1+x+(x+c*2))) with ((1+x+c)*2) by lia.
  follow100 RC_Halve.
  finish.
Qed.

Lemma RC_Incs_Halve' l x c:
  c>0 ->
  l <* w0 |> RCounter ((1+x)::nil) (x+c*2) -->*
  l <* w1^^(1+x) <* w2 <* w0 |> R (x+c-1).
Proof.
  intro H.
  follow RC_Incs.
  follow100 RC_Inc.
  replace (S(1+x+(x+c*2))) with ((1+x+c)*2) by lia.
  replace (1+x+c) with (2+(x+c-1)) by lia.
  follow100 RC_Halve'.
  finish.
Qed.

Definition LBlock i := w2++w1^^i.

Lemma RC_IHs l x0 n c:
  c>0 ->
  l <* w0 |> RCounter ((1+x0)::arith_seq_inc (3+x0) n 1) (x0+c*2^(1+n)) -->*
  l <* LBlock^^^(arith_seq_dec (1+n+x0) (1+n) 1) <* w0 |> R (n+x0+c-1).
Proof.
  intro Hc.
  gen x0 l.
  induction n; intros.
  - cbn[Nat.add].
    cbn[arith_seq_inc].
    cbn[arith_seq_dec].
    follow RC_Incs_Halve'.
    cbn[flat_map].
    unfold LBlock.
    repeat rewrite Str_app_assoc.
    finish.
  - cbn[arith_seq_inc].
    cbn[Nat.add].
    cbn[Nat.pow].
    replace (c*(2*(2*2^n))) with (c*(2*(2^n))*2) by lia.
    follow RC_Incs_Halve.
    specialize (IHn (1+x0)).
    follow IHn.
    repeat (rewrite arith_seq_dec_tail;[|lia]).
    repeat rewrite flat_map_app.
    cbn[flat_map].
    replace (1+n+(1+x0)-1*n) with (2+x0) by lia.
    unfold LBlock.
    repeat rewrite Str_app_assoc.
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
    simpl_tape.
    finish.
Qed.

Transparent R.
Hypothesis R_Rst:
  forall l n,
  l <* w1^^n <* w0 <| R 1 -->*
  l <| f0^^(2+n) *> d1 *> R 1.

Hypothesis RC_Rst:
  forall l r n,
  l <* LBlock n <| r -->*
  l <| f0^^(1+n) *> d1 *> r.


Lemma RC_Rsts x0 l n n0:
  l <* LBlock^^^arith_seq_dec (n+x0) n 1 <| RCounter (arith_seq_inc (2+n+x0) n0 1) (2^(1+n0)-1) -->*
  l <| RCounter (arith_seq_inc (2+x0) (n+n0) 1) (2^(1+n+n0)-1).
Proof.
  gen n0.
  induction n; intros.
  1: finish.
  cbn[arith_seq_dec].
  cbn[flat_map].
  repeat rewrite Str_app_assoc.
  follow RC_Rst.
  specialize (IHn (S n0)).
  cbn[arith_seq_inc] in IHn.
  cbn[RCounter] in IHn.
  cbn[Nat.add] in IHn.
  cbn[Nat.add].
  rewrite pow2sub1_odd,pow2sub1_div2 in IHn.
  follow IHn.
  finish.
Qed.

Lemma RCsub1 x xs n:
  RCounter (S x::xs) n = f0 *> RCounter (x::xs) n.
Proof.
  cbn[RCounter].
  cbn[lpow].
  simpl_tape.
  reflexivity.
Qed.

Lemma RCounter_fold_d1 n0 xs n:
  f0^^n0 *> d1 *> RCounter xs n =
  RCounter (n0::xs) (1+n*2).
Proof.
  cbn[RCounter].
  rewrite odd_mul2add1.
  rewrite Nat.div_add. 2: lia.
  reflexivity.
Qed.

Definition l1 := w1 *> const 0.
Definition l0 := LBlock (a0*2) *> l1.

Hypothesis l0_LR:
  forall r,
  l0 <| r -->+
  l1 <* w0 |> f0^^(a0*2) *> d1 *> r.


Definition config n :=
  l0 <* w0 |> RCounter ((1+a0)::arith_seq_inc (3+a0) n 1) (a0+2*2^(1+n)).

Hypothesis init:
  c0 -->* config 0.

Lemma BigStep n:
  config n -->+
  config (S n).
Proof.
  unfold config.
  follow (RC_IHs l0 a0).
  follow R_Incs.
  follow R_Rst.
  pose proof (RC_Rsts a0 l0 (1+n) 1) as H.
  cbn[arith_seq_inc] in H.
  cbn[RCounter] in H.
  follow H.
  follow10 l0_LR.
  rewrite RCounter_fold_d1.
  pose proof RC_Incs.
  follow RC_Incs.
  follow100 RC_Inc.
  replace (1+n+1) with (S(n+1)) by lia.
  cbn[arith_seq_inc].
  pose proof RC_Halve.
  replace (1+(1+n)+1) with (3+n) by lia.
  pose proof (Nat.pow_nonzero 2 (3+n)) as H2.
  replace (S (a0*2 + (1 + (2 ^ (3+n) - 1) * 2))) with
  ((2 ^ (3+n) + a0) * 2) by lia.
  cbn[Nat.add].
  follow100 RC_Halve.
  unfold l0,LBlock.
  repeat rewrite Str_app_assoc.
  cbn[Nat.add].
  rewrite (Nat.add_comm n 1).
  cbn[Nat.add].
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n).
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


End CGASv1.


Inductive Cert :=
| cert1
  (QL QR : Q)
  (qL qR f0 f0' d0 d1 d1' d1a w0 w1 w2 : list Sym)
  (a0:nat).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL ?QR
  ?qL ?qR ?f0 ?f0' ?d0 ?d1 ?d1' ?d1a ?w0 ?w1 ?w2
  ?a0) =>
  eapply (nonhalt _
    QL QR
    qL qR
    f0 f0' d0 d1 d1' d1a
    w0 w1 w2
    a0);
  [ try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | try (es; fail)
  | unfold LBlock; try (es; fail)
  | try (es; fail)
  | unfold config; cbn; try (solve_init; fail)
  ]
end.



Definition tm0 := Eval compute in (TM_from_str "1RB0RD_0RC0RE_1LD1RF_1LE0RE_1RB0LE_---1RA").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 E A [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1RB0RB_0RC0RE_1LD1RF_1LE---_1RB0LE_---1RA").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 E A [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1RB0RB_0RC0RE_1LD1RF_1LD0LE_1RB0LE_---1RA").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 E A [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB0LA_0RC0RA_1LD1RD_1LE1RF_---0LA_1RB0RB").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 A F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1RB0LA_0RC0RA_1LD1RD_1LA1RE_1RB0RF_---0RA").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 A E [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB1RF_1LC---_1RD0LC_0RE0RC_1LB1RA_1RD0RD").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 C F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  1).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1LB1RF_1LC---_1RD0LC_0RE0RC_1LB1RA_1RD0RD").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 C F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1LB1RE_1LC0RC_1RD0LC_0RA0RC_---1RF_1RD0RB").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 C F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1LB1RE_1LC---_1RD0LC_0RA0RC_---1RF_1RD0RD").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 C F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm9 := Eval compute in (TM_from_str "1LB1RB_1LC1RE_1RD0LC_0RA0RC_1RD0RF_---0RC").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 C E [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm10 := Eval compute in (TM_from_str "1LB1RE_1RC0LB_0RD0RB_1LA1RA_1RC0RF_---0RB").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 B E [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  3).
Qed.

Definition tm11 := Eval compute in (TM_from_str "1LB0RB_1RC0LB_0RD0RB_1LA1RE_---1RF_1RC0RA").
Lemma nonhalt11: ~halts tm11 c0.
Proof.
  solve_cert (cert1 B F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  3).
Qed.

Definition tm12 := Eval compute in (TM_from_str "1LB---_1RC0LB_0RD0RB_1LA1RE_---1RF_1RC0RC").
Lemma nonhalt12: ~halts tm12 c0.
Proof.
  solve_cert (cert1 B F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  3).
Qed.

Definition tm13 := Eval compute in (TM_from_str "1LB1RE_1LC1RC_1RD0LC_0RA0RC_---1RF_0LB0RD").
Lemma nonhalt13: ~halts tm13 c0.
Proof.
  solve_cert (cert1 C D [0] [1]
  [0;1;1;0] [1;1;0;1] [0;0;1;1;0] [1;1;1;1;0] [1;1;0;1;1] [1;1;0]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm14 := Eval compute in (TM_from_str "1LB1RF_1RC0LB_0RD0RB_1LE1RA_0LD---_1RC0RC").
Lemma nonhalt14: ~halts tm14 c0.
Proof.
  solve_cert (cert1 B F [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  3).
Qed.

Definition tm15 := Eval compute in (TM_from_str "1LB1RB_1RC0LB_0RD0RB_1LA1RE_---1RF_0LA0RC").
Lemma nonhalt15: ~halts tm15 c0.
Proof.
  solve_cert (cert1 B C [0] [1]
  [0;1;1;0] [1;1;0;1] [0;0;1;1;0] [1;1;1;1;0] [1;1;0;1;1] [1;1;0]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  3).
Qed.

Definition tm16 := Eval compute in (TM_from_str "1LB---_1RC0LB_0LD0RB_1LA1RE_0RD1RF_1RC0RC").
Lemma nonhalt16: ~halts tm16 c0.
Proof.
  solve_cert (cert1 B C [0] [1]
  [0;1;1;0] [1;1;0;1] [0;0;1;1;0] [1;1;1;1;0] [1;1;0;1;1] [1;1;0]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  3).
Qed.

Definition tm17 := Eval compute in (TM_from_str "1LB0RF_1RC0RE_1LD0RD_1RB1LE_1RF0LA_---0RA").
Lemma nonhalt17: ~halts tm17 c0.
Proof.
  solve_cert (cert1 B A [1] [0]
  [0;0;0;1;1] [1;1;1;0;1] [0;0;0;0;1;1] [0;0;1;1;1;1] [1;1;1;0;1;1] [0;0;1;1]
  [1;1;1;0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;1;1;0;1]
  0).
Qed.

Definition tm18 := Eval compute in (TM_from_str "1RB1RC_1LC1RE_---1LD_1RA0LE_1LF0RE_1RF0RD").
Lemma nonhalt18: ~halts tm18 c0.
Proof.
  solve_cert (cert1 F E [1] [0]
  [0;0;0;1;1] [1;1;1;0;1] [0;0;0;0;1;1] [0;0;1;1;1;1] [1;1;1;0;1;1] [0;0;1;1]
  [1;1;1;0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;1;1;0;1]
  0).
Qed.

Definition tm19 := Eval compute in (TM_from_str "1LB1LE_1RC0RE_1LA0RD_1RB0RF_---0LA_0LA1RC").
Lemma nonhalt19: ~halts tm19 c0.
Proof.
  solve_cert (cert1 B F [1;0] [0;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm20 := Eval compute in (TM_from_str "1LB1LC_1RC0RF_1LE0RD_1RE1RA_1RB1LE_---0LA").
Lemma nonhalt20: ~halts tm20 c0.
Proof.
  solve_cert (cert1 B A [1;0] [1;0]
  [0;0;0;1;1] [1;1;1;0;1] [0;0;0;0;1;1] [0;0;1;1;1;1] [1;1;1;0;1;1] [0;0;1;1]
  [1;1;1;0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;1;1;0;1]
  0).
Qed.

Definition tm21 := Eval compute in (TM_from_str "1LB0RD_1LC1LF_1RA0RF_1RC0RE_0LB1RA_---0LB").
Lemma nonhalt21: ~halts tm21 c0.
Proof.
  solve_cert (cert1 C E [1;0] [0;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm22 := Eval compute in (TM_from_str "1RB0RE_1LC0RF_1RA0RD_1LA1LB_---0LD_1RC1RD").
Lemma nonhalt22: ~halts tm22 c0.
Proof.
  solve_cert (cert1 A D [1;0] [1;0]
  [0;0;0;1;1] [1;1;1;0;1] [0;0;0;0;1;1] [0;0;1;1;1;1] [1;1;1;0;1;1] [0;0;1;1]
  [1;1;1;0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;1;1;0;1]
  0).
Qed.

Definition tm23 := Eval compute in (TM_from_str "1LB1RC_1RC0RE_1LE0RD_1RB0RF_---0LA_0LA1RC").
Lemma nonhalt23: ~halts tm23 c0.
Proof.
  solve_cert (cert1 B F [1;0] [0;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm24 := Eval compute in (TM_from_str "1LB0LD_1RC0RE_1LE0RD_1RB0RF_---0LA_0LA1RC").
Lemma nonhalt24: ~halts tm24 c0.
Proof.
  solve_cert (cert1 B F [1;0] [0;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm25 := Eval compute in (TM_from_str "1LB0LF_1RC0RE_1LE0RD_1RB1RA_---0LA_0RB0RB").
Lemma nonhalt25: ~halts tm25 c0.
Proof.
  solve_cert (cert1 B A [1;0] [1;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm26 := Eval compute in (TM_from_str "1RB1RE_1RC0RD_1LD0RA_---0LE_1LB0LF_0RB0RB").
Lemma nonhalt26: ~halts tm26 c0.
Proof.
  solve_cert (cert1 B E [1;0] [1;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm27 := Eval compute in (TM_from_str "1RB1RD_0LC1RC_0RD1LD_0LE0RE_1RF0LE_0RA---").
Lemma nonhalt27: ~halts tm27 c0.
Proof.
  solve_cert (cert1 E D [0] [0]
  [0;0;1;0] [1;1;0;1] [0;0;0;1;0] [0;1;0;1;0] [1;1;0;1;1] [0;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm28 := Eval compute in (TM_from_str "1RB0LE_0LC1RC_0RD1LD_0LE0RE_1RF0LE_0RA---").
Lemma nonhalt28: ~halts tm28 c0.
Proof.
  solve_cert (cert1 E D [0] [0]
  [0;0;1;0] [1;1;0;1] [0;0;0;1;0] [0;1;0;1;0] [1;1;0;1;1] [0;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm29 := Eval compute in (TM_from_str "1RB1RE_1LC1RF_---1LD_0LE0RB_1RF0LE_0RA0RD").
Lemma nonhalt29: ~halts tm29 c0.
Proof.
  solve_cert (cert1 E D [0] [0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm30 := Eval compute in (TM_from_str "1RB0RB_0LC0RF_1LE1RD_0RC1RA_1LF---_1RB0LF").
Lemma nonhalt30: ~halts tm30 c0.
Proof.
  solve_cert (cert1 F A [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm31 := Eval compute in (TM_from_str "1RB0LA_0RC---_1RD0LA_0LE1RE_0RF1LF_0LA0RA").
Lemma nonhalt31: ~halts tm31 c0.
Proof.
  solve_cert (cert1 A F [0] [0]
  [0;0;1;0] [1;1;0;1] [0;0;0;1;0] [0;1;0;1;0] [1;1;0;1;1] [0;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm32 := Eval compute in (TM_from_str "1RB0LA_0RC---_1RD0LE_0LE1RE_0RF1LF_0LA0RA").
Lemma nonhalt32: ~halts tm32 c0.
Proof.
  solve_cert (cert1 A F [0] [0]
  [0;0;1;0] [1;1;0;1] [0;0;0;1;0] [0;1;0;1;0] [1;1;0;1;1] [0;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm33 := Eval compute in (TM_from_str "1RB0LA_0RC---_1RD1RF_0LE1RE_0RF1LF_0LA0RA").
Lemma nonhalt33: ~halts tm33 c0.
Proof.
  solve_cert (cert1 A F [0] [0]
  [0;0;1;0] [1;1;0;1] [0;0;0;1;0] [0;1;0;1;0] [1;1;0;1;1] [0;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm34 := Eval compute in (TM_from_str "1RB0LA_0RC0RF_1RD1RA_1LE1RB_---1LF_0LA0RD").
Lemma nonhalt34: ~halts tm34 c0.
Proof.
  solve_cert (cert1 A F [0] [0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm35 := Eval compute in (TM_from_str "1RB0LA_0RC0RA_1LD1RE_1LA1RA_---1RF_0LD0RB").
Lemma nonhalt35: ~halts tm35 c0.
Proof.
  solve_cert (cert1 A B [0] [1]
  [0;1;1;0] [1;1;0;1] [0;0;1;1;0] [1;1;1;1;0] [1;1;0;1;1] [1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm36 := Eval compute in (TM_from_str "1RB0RB_0RC0RF_1LD1RE_0LC---_1LF1RA_1RB0LF").
Lemma nonhalt36: ~halts tm36 c0.
Proof.
  solve_cert (cert1 F A [] []
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm37 := Eval compute in (TM_from_str "1RB0RA_1LC---_1RE0RD_1RA0LB_1LF0RF_1RC1LD").
Lemma nonhalt37: ~halts tm37 c0.
Proof.
  solve_cert (cert1 C B [1;0] [1;0]
  [0;0;1;1;0] [1;1;1;0;1] [0;0;0;1;1;0] [0;1;1;1;1;0] [1;1;1;0;1;1] [0;1;1]
  [1;1;1;0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;1;1;0;1]
  0).
Qed.

Definition tm38 := Eval compute in (TM_from_str "1RB0LC_0LC1RC_0RD1LD_0LE0RE_1RF0LE_0RA---").
Lemma nonhalt38: ~halts tm38 c0.
Proof.
  solve_cert (cert1 E D [0] [0]
  [0;0;1;0] [1;1;0;1] [0;0;0;1;0] [0;1;0;1;0] [1;1;0;1;1] [0;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm39 := Eval compute in (TM_from_str "1LB1RE_1LC---_1RD0LC_0LA0RC_0RA1RF_1RD0RD").
Lemma nonhalt39: ~halts tm39 c0.
Proof.
  solve_cert (cert1 C D [0] [1]
  [0;1;1;0] [1;1;0;1] [0;0;1;1;0] [1;1;1;1;0] [1;1;0;1;1] [1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.

Definition tm40 := Eval compute in (TM_from_str "1RB0RE_1LC---_1RD1RC_0LE1RE_0RA1LF_0LE0LF").
Lemma nonhalt40: ~halts tm40 c0.
Proof.
  solve_cert (cert1 E E [] []
  [0;0;0;0;1] [1;1;1;1;0] [0;0;0;0;0;1] [0;0;0;1;0;1] [1;1;1;1;1;0] [0;0;0;1]
  [1;1;1;1;0;0;0] [1;1;1;1;0] [1;1;1;1;0;0;1;1;1;1;0]
  0).
Qed.

Definition tm41 := Eval compute in (TM_from_str "1LB0LA_0RC1RB_0LF1RD_0LE1RE_0RF0RB_1LA---").
Lemma nonhalt41: ~halts tm41 c0.
Proof.
  solve_cert (cert1 B C [1;0;0] [0;0;0]
  [0;0;0;1;0] [1;1;1;1;0] [0;0;0;0;1;0] [0;0;1;0;1;0] [1;1;1;1;1;0] [0;0;1]
  [1;1;1;1;0;0;0] [1;1;1;1;0] [1;1;1;1;0;0;1;1;1;1;0]
  0).
Qed.

Definition tm42 := Eval compute in (TM_from_str "1LB0LA_0RC1LE_0LD0RB_1LA---_1RE1RF_0RD1RB").
Lemma nonhalt42: ~halts tm42 c0.
Proof.
  solve_cert (cert1 B C [1;0;0] [0;0;0]
  [0;0;0;1;0] [1;1;1;1;0] [0;0;0;0;1;0] [0;0;1;0;1;0] [1;1;1;1;1;0] [0;0;1]
  [1;1;1;1;0;0;0] [1;1;1;1;0] [1;1;1;1;0;0;1;1;1;1;0]
  0).
Qed.

Definition tm43 := Eval compute in (TM_from_str "1LB0LE_1RC1RE_1LA0RD_1RB0RF_---0LD_0LA1RC").
Lemma nonhalt43: ~halts tm43 c0.
Proof.
  solve_cert (cert1 B F [1;0] [0;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  0).
Qed.

Definition tm44 := Eval compute in (TM_from_str "1RB0RF_1RC0RD_1LD0RA_---0LE_1LB1RC_0LE1RC").
Lemma nonhalt44: ~halts tm44 c0.
Proof.
  solve_cert (cert1 B F [1;0] [0;0]
  [0;0;1;1] [1;1;0;1] [0;0;0;1;1] [0;1;1;1;1] [1;1;0;1;1] [0;1;1]
  [1;1;0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;1;0;1]
  2).
Qed.








