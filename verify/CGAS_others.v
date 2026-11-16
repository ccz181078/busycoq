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

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0LC_1LD1RF_0LE1LB_0RA0LB_1RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Notation "l |> r" :=
  (l {{A}}> r) (at level 30).

Notation "l <| r" :=
  (l <{{C}} r) (at level 30).

Definition f0 := [0;1;1;0;1;1].
Definition f0' := [0;1;1;0;1;1].
Definition d0 := [0;0;0;1;0;1;1].
Definition d1 := [0;1;1;1;0;1;1].
Definition d1' := [0;1;1;0;0;1;1].
Definition d1a := [0;1;1].

Lemma R_carry l r n:
  l |> f0^^n *> d1 *> r -->*
  l <* f0'^^n <* d1' |> r.
Proof.
  unfold f0,f0',d0,d1,d1'.
  es.
Qed.

Lemma RL l r n:
  l |> f0^^n *> d0 *> r -->+
  l <| f0^^n *> d1 *> r.
Proof.
  unfold f0,f0',d0,d1,d1'.
  es.
Qed.

Lemma R_return l r n:
  l <* f0'^^n <* d1' <| r -->*
  l <| f0^^n *> d0 *> r.
Proof.
  unfold f0,f0',d0,d1,d1'.
  es.
Qed.

Lemma RInc0 l n:
  l |> f0^^n *> const 0 -->+
  l <| f0^^n *> d1a *> const 0.
Proof.
  unfold f0,d1a.
  es.
Qed.

Lemma RInc1 l n:
  l |> f0^^n *> d1a *> const 0 -->+
  l <| f0^^(1+n) *> const 0.
Proof.
  unfold f0,d1a.
  es.
Qed.

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


Definition w0 := [0;1;1;0;0;1;1;1].
Definition w1 := [0;1;1;0;1;1].
Definition w2 := [0;1;1;0;1;1;1;0;1;1;0;1;1].

Lemma LR1 l r:
  l <* w0 <| f0 *> r -->+
  l <* w1 <* w0 |> r.
Proof.
  unfold w0,w1,f0.
  es.
Qed.

Lemma LR2 l r:
  l <* w0 <| d0 *> f0 *> r -->+
  l <* w2 <* w0 |> r.
Proof.
  unfold w0,w2,d0,f0.
  es.
Qed.

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
    rewrite lpow_shift'.
    finish.
Qed.

Notation "l <|' r" :=
  (l <{{C}} d0 *> r) (at level 30).

Definition w3 := [0;1;1;0;1;1;1].
Definition LBlock' n := w1^^(1+n) ++ w3.
Transparent R.
Lemma R_Rst l n:
  l <* w3 <* w1^^n <* w0 <| R 1 -->*
  l <|' f0^^(2+n) *> d1 *> R 1.
Proof.
  unfold R,f0,d0,d1,w0,w1,w3.
  es.
Qed.

Lemma RC_Rst l r n:
  l <* LBlock' n <|' r -->*
  l <|' f0^^(1+n) *> d1 *> r.
Proof.
  unfold LBlock',f0,d0,d1,w0,w1,w2,w3.
  es.
Qed.

Definition l1 := w3 *> [0;1;1] *> const 0.
Definition l0 := LBlock (0*2) *> l1.

Lemma LBlock_rotate xs:
  LBlock ^^^ xs *> l0 =
  w3 *> LBlock' ^^^ xs *> w1 *> l1.
Proof.
  unfold l0.
  induction xs.
  - reflexivity.
  - cbn[flat_map].
    repeat rewrite Str_app_assoc.
    rewrite IHxs.
    unfold LBlock,LBlock'.
    repeat rewrite Str_app_assoc.
    reflexivity.
Qed.

Lemma RC_Rsts x0 l n n0:
  l <* LBlock' ^^^ arith_seq_dec (n+x0) n 1 <|' RCounter (arith_seq_inc (2+n+x0) n0 1) (2^(1+n0)-1) -->*
  l <|' RCounter (arith_seq_inc (2+x0) (n+n0) 1) (2^(1+n+n0)-1).
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

Definition l2 := d1' *> w0 *> l1.
Lemma l0_LR:
  forall r,
  l1 <* w1 <|' r -->+
  l2 |> r.
Proof.
  es.
Qed.

Lemma l2_LR:
  forall r,
  l2 <| f0 *> r -->+
  l0 <* w0 |> r.
Proof.
  es.
Qed.


Definition config n :=
  l0 <* w0 |> RCounter ((1+0)::arith_seq_inc (3+0) n 1) (0+2*2^(1+n)).

Lemma init:
  c0 -->* config 0.
Proof.
  unfold config; cbn.
  solve_init.
Qed.

Lemma BigStep n:
  config n -->+
  config (S n).
Proof.
  unfold config.
  follow (RC_IHs l0 0).
  follow R_Incs.
  rewrite LBlock_rotate.
  follow R_Rst.
  epose proof (RC_Rsts 0 _ (1+n) 1) as H.
  cbn[arith_seq_inc] in H.
  cbn[RCounter] in H.
  follow H.
  follow10 l0_LR.
  repeat rewrite Nat.add_0_r.
  change (1+n+1) with (S(n+1)).
  cbn[arith_seq_inc].
  follow100 RC_Inc.
  rewrite RCsub1.
  follow100 l2_LR.
  replace (n+1) with (S(n)) by lia.
  cbn[arith_seq_inc].
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

End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0LC1LE_0RD0LE_1RE0RB_1RA0LA_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Notation "l |> r" :=
  (l {{D}}> r) (at level 30).

Notation "l <| r" :=
  (l <{{A}} r) (at level 30).

Definition f0 := [0;1;1;0;1;1].
Definition f0' := [0;1;1;0;1;1].
Definition d0 := [0;0;0;1; 0;1;1; 0;1;1].
Definition d1 := [0;1;1;1; 0;1;1; 0;1;1].
Definition d1' := [0;1;1; 0;1;1; 0;0;1;1].
Definition d1a := [0;1;1].

Lemma R_carry l r n:
  l |> f0^^n *> d1 *> r -->*
  l <* f0'^^n <* d1' |> r.
Proof.
  unfold f0,f0',d0,d1,d1'.
  es.
Qed.

Lemma RL l r n:
  l |> f0^^n *> d0 *> r -->+
  l <| f0^^n *> d1 *> r.
Proof.
  unfold f0,f0',d0,d1,d1'.
  es.
Qed.

Lemma R_return l r n:
  l <* f0'^^n <* d1' <| r -->*
  l <| f0^^n *> d0 *> r.
Proof.
  unfold f0,f0',d0,d1,d1'.
  es.
Qed.

Lemma RInc0 l n:
  l |> f0^^n *> const 0 -->+
  l <| f0^^n *> d1a *> const 0.
Proof.
  unfold f0,d1a.
  es.
Qed.

Lemma RInc1 l n:
  l |> f0^^n *> d1a *> const 0 -->+
  l <| f0^^(1+n) *> const 0.
Proof.
  unfold f0,d1a.
  es.
Qed.

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


Definition w0 := [0;1;1;0;0;1;1;1].
Definition w1 := [0;1;1;0;1;1].
Definition w2 := [0;1;1;1; 0;1;1;0;1;1].

Lemma LR1 l r:
  l <* w0 <| f0 *> r -->+
  l <* w1 <* w0 |> r.
Proof.
  unfold w0,w1,f0.
  es.
Qed.

Lemma LR2 l r:
  l <* w0 |> d0 *> r -->+
  l <* w2 <* w0 |> r.
Proof.
  unfold w0,w2,d0,f0.
  es.
Qed.


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
    finish.
Qed.



Definition LBlock i := w2++w1^^i.

Lemma RC_IHs l x0 n:
  l <* w0 |> RCounter (arith_seq_inc (1+x0) n 1) (x0+2^n-1) -->*
  l <* LBlock^^^(arith_seq_dec (n+x0) n 1) <* w0 |> R (n+x0).
Proof.
  gen x0 l.
  induction n; intros.
  - cbn.
    finish.
  - cbn[arith_seq_inc].
    cbn[Nat.pow].
    pose proof (Nat.pow_nonzero 2 n).
    follow RC_Incs.
    replace (1 + x0 + (x0 + 2 * 2 ^ n - 1)) with ((x0+2^n)*2) by lia.
    follow100 RC_Halve.
    specialize (IHn (1+x0)).
    replace (x0+2^n) with (1+x0+2^n-1) by lia.
    follow IHn.
    rewrite arith_seq_dec_tail.
    2: lia.
    rewrite flat_map_app.
    cbn[flat_map].
    repeat rewrite Str_app_assoc.
    replace (S n+x0-1*n) with (1+x0) by lia.
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
    finish.
Qed.

Transparent R.

Notation "l <|' r" :=
  (l <{{A}} d0 *> r) (at level 30).

Definition w3 := [0;1;1;1].
Definition LBlock' n := w1^^(1+n) ++ w3.
Transparent R.
Lemma R_Rst l n:
  l <* w3 <* w1^^n <* w0 <| R 1 -->*
  l <|' f0^^(1+n) *> d1 *> R 0.
Proof.
  unfold R,f0,d0,d1,w0,w1,w3.
  es.
Qed.

Lemma RC_Rst l r n:
  l <* LBlock' n <|' r -->*
  l <|' f0^^n *> d1 *> r.
Proof.
  unfold LBlock',f0,d0,d1,w0,w1,w2,w3.
  es.
Qed.

Definition l1 := [0;1;1] *> const 0.
Definition l0 := LBlock (0*2) *> l1.

Lemma LBlock_rotate xs:
  LBlock ^^^ xs *> l0 =
  w3 *> LBlock' ^^^ xs *> w1 *> l1.
Proof.
  unfold l0.
  induction xs.
  - reflexivity.
  - cbn[flat_map].
    repeat rewrite Str_app_assoc.
    rewrite IHxs.
    unfold LBlock,LBlock'.
    repeat rewrite Str_app_assoc.
    reflexivity.
Qed.


Lemma RC_Rsts l n n0:
  l <* LBlock' ^^^ arith_seq_dec (n) n 1 <|' RCounter (arith_seq_inc (1+n) n0 1) (2^(n0)-1) -->*
  l <|' RCounter (arith_seq_inc (1) (n+n0) 1) (2^(n+n0)-1).
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

Lemma l0_LR:
  forall r,
  l1 <* w1 <|' r -->+
  l0 <* w0 |> r.
Proof.
  es.
Qed.

Definition config n :=
  l0 <* w0 |> RCounter (arith_seq_inc (1+0) n 1) (2^n-1).

Lemma init:
  c0 -->* config 0.
Proof.
  unfold config; cbn.
  solve_init.
Qed.

Lemma BigStep n:
  config n -->+
  config (S n).
Proof.
  unfold config.
  follow (RC_IHs l0 0).
  follow R_Incs.
  rewrite LBlock_rotate.
  follow R_Rst.
  epose proof (RC_Rsts _ (n) 1) as H.
  cbn[arith_seq_inc] in H.
  cbn[RCounter] in H.
  follow H.
  follow10 l0_LR.
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

End TM3.

