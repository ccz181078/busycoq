From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal.

Open Scope list.

Ltac flia := repeat (lia || f_equal).

Lemma segRLs_trans_add tm h h' n1 n2 n1' n2' w1 w2 w3:
  segRLs tm (h^^n1) (h'^^n1') w1 w3 ->
  segRLs tm (h^^n2) (h'^^n2') w3 w2 ->
  segRLs tm (h^^(n1+n2)) (h'^^(n1'+n2')) w1 w2.
Proof.
  intros.
  do 2 rewrite lpow_add.
  eapply segRLs_trans; eassumption.
Qed.

Lemma sideRLs_trans_add tm h n1 n2 w1 w2 w3:
  sideRLs tm (h^^n1) w1 w3 ->
  sideRLs tm (h^^n2) w3 w2 ->
  sideRLs tm (h^^(n1+n2)) w1 w2.
Proof.
  intros.
  rewrite lpow_add.
  eapply sideRLs_trans; eassumption.
Qed.

Lemma sideRLs_trans_S tm h n w1 w2 w3:
  sideRLs tm (h^^n) w1 w3 ->
  sideRLs tm h w3 w2 ->
  sideRLs tm (h^^(S n)) w1 w2.
Proof.
  intros.
  replace (S n) with (n+1) by lia.
  eapply sideRLs_trans_add.
  - apply H.
  - cbn.
    rewrite app_nil_r.
    apply H0.
Qed.

Ltac sideRLs_ind k :=
  induction k;
  [ try esx |
    eapply sideRLs_trans_S;
    [ eassumption | ];
    try esx ].


Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA1LF_0RD1RC_0RE---_1RA1RE_0LF1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (F,[]).
Definition hL:DH0 := (E,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0;0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0;0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  unfold LC.
  sideRLs_ind b.
Qed.

Definition S0 n := RC0 n {{E}}> 0inf.

Lemma RRst n r:
  RC1 n <{{F}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0RD_0LB1LC_1RA1LB_0RE1RD_0RF---_1RA1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (F,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0;0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0;0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  unfold LC.
  sideRLs_ind b.
Qed.

Definition S0 n := RC0 n {{F}}> 0inf.

Lemma RRst n r:
  RC1 n <{{B}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC---_0LC1LD_1RA1LC_0RF1RE_1RA1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (F,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  unfold LC.
  sideRLs_ind b.
Qed.

Definition S0 n := RC0 n {{F}}> 0inf.

Lemma RRst n r:
  RC1 n <{{C}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC---_0LC1LD_1RA1LC_0RF1RE_1RA1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (F,[]).
Definition hRL := [(hR,hL)].
Definition hLR := [(hL,hR)].

Definition C0 a b := [0] ++ [1;1]^^a ++ [1;0;1] ++ [1;1]^^b.
Definition C1 a b := [0] ++ [1;1]^^a ++ [0] ++ [1;1]^^b.

Lemma CIncs a b:
  segRLs tm' (hRL^^(a*2+1)) (hRL^^a) (C0 a b) (C1 0 (1+a+b)).
Proof.
  gen b.
  induction a; intros.
  - solve_segRLs.
  - replace (S a*2+1) with (2+(a*2+1)) by lia.
    replace (S a) with (1+a) by lia.
    rewrite (lpow_add _ 2 (a*2+1)).
    rewrite (lpow_add _ 1 a).
    eapply segRLs_trans.
    2: applys_eq (IHa (1+b)); f_equal; lia.
    unfold C0,C1.
    solve_segRLs.
Qed.

Fixpoint pow2' n:nat :=
match n with
| O => 0
| S n0 => (pow2' n0)*2+1
end.

Fixpoint RC0 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C0 (pow2' n0) 0 *> RC0 n0
end.

Fixpoint RC1 n :=
match n with
| O => [0;0;1]*>0inf
| S n0 => C1 0 (1+(pow2' n0)) *> RC1 n0
end.

Lemma RIncs n:
  sideRLs tm' (hRL^^(pow2' n)) (RC0 n) (RC1 n).
Proof.
  induction n.
  - solve_sideRLs.
  - cbn[pow2']; cbn[RC0]; cbn[RC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (CIncs (pow2' n) 0); f_equal; lia.
Qed.

Definition LC n := 0inf <* <[1;1]^^n.

Lemma LIncs b:
  sideRLs tm (hLR^^b) (LC 0) (LC (b)).
Proof.
  unfold LC.
  sideRLs_ind b.
Qed.

Definition S0 n := RC0 n {{F}}> 0inf.

Lemma RRst n r:
  RC1 n <{{C}} r -->*
  RC0 n <* [1] {{A}}> r.
Proof.
  gen r.
  induction n; intros; cbn.
  1: es.
  es; er; follow IHn; es.
Qed.


Lemma BigStep n:
  S0 n -->+
  S0 (S n).
Proof.
  unfold S0.
  epose proof (LIncs (1+pow2' n)) as HL.
  unfold hLR in HL.
  rewrite <-lrcons_lpow1 in HL by lia.
  replace (1+pow2' n-1) with (pow2' n) in HL by lia.
  epose proof (sideRLs_concat (RIncs n) HL) as H.
  unfold LC in H.
  cbn in H.
  follow10 H.
  follow RRst.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i; eexists; apply BigStep.
Qed.

End TM4.



Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0RF_1RD1LD_1LA0RB_0RF0LD_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l |> r" := (l {{D}}> r) (at level 30).

Notation hL := (A,[]).
Notation hR := (D,[]).
Notation hLR2 := ([(hL,hR)]^^2).
Notation hRL2 := ([(hR,hL)]^^2).

Definition C0 n m := <[0;1;1]^^n <+ <[0;0] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].
Definition C1 n m := <[0;1;1]^^n <+ <[0;1] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].

Notation lh := (0inf <* <[1;0;1;0;1;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(O,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a:
  exists r0,
  (forall r,
  LC1 x <| [1;0;0]^^(1+a) *> [0;0] *> r -->+
  r0 |> r) /\
  (forall r,
  r0 <| r -->*
  LC0 (cons x a) |> r).
Proof.
  gen a.
  induction x; intros; cbn.
  - eexists; split.
    + es.
    + es.
  - destruct a as [n m].
    destruct (IHx n) as [r0 [I1 I2]].
    eexists; split.
    + es; er.
      follow100 I1.
      es; er.
      follow I2.
      es.
    + es.
Qed.

Definition RC n := [1;0;0]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  LC1 x |> RC a -->+
  LC0 (cons x a) |> RC 1.
Proof.
  unfold RC.
  epose proof (Ov x a) as [r0 [I1 I2]].
  specialize (I1 0inf).
  cbn in I1.
  repeat rewrite <-const_unfold in I1.
  es; er.
  follow100 I1.
  er.
  follow I2.
  er.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x |> RC 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(2,1)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=LWF).
  2: repeat econstructor.
  intros x HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 1) as I2.
    rewrite <-lpow_mul in I1',I2.
    follow (sideRLs_concat_1 I2 I1').
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LF_1RD0RA_1RE1LE_1LB0RC_0RA0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{B}} r) (at level 30).
Notation "l |> r" := (l {{E}}> r) (at level 30).

Notation hL := (B,[]).
Notation hR := (E,[]).
Notation hLR2 := ([(hL,hR)]^^2).
Notation hRL2 := ([(hR,hL)]^^2).

Definition C0 n m := <[0;1;1]^^n <+ <[0;0] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].
Definition C1 n m := <[0;1;1]^^n <+ <[0;1] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].

Notation lh := (0inf <* <[1;0;1;0;1;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(O,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a:
  exists r0,
  (forall r,
  LC1 x <| [1;0;0]^^(1+a) *> [0;0] *> r -->+
  r0 |> r) /\
  (forall r,
  r0 <| r -->*
  LC0 (cons x a) |> r).
Proof.
  gen a.
  induction x; intros; cbn.
  - eexists; split.
    + es.
    + es.
  - destruct a as [n m].
    destruct (IHx n) as [r0 [I1 I2]].
    eexists; split.
    + es; er.
      follow100 I1.
      es; er.
      follow I2.
      es.
    + es.
Qed.

Definition RC n := [1;0;0]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  LC1 x |> RC a -->+
  LC0 (cons x a) |> RC 1.
Proof.
  unfold RC.
  epose proof (Ov x a) as [r0 [I1 I2]].
  specialize (I1 0inf).
  cbn in I1.
  repeat rewrite <-const_unfold in I1.
  es; er.
  follow100 I1.
  er.
  follow I2.
  er.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x |> RC 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(0,3)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=LWF).
  2: repeat econstructor.
  intros x HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 1) as I2.
    rewrite <-lpow_mul in I1',I2.
    follow (sideRLs_concat_1 I2 I1').
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1LC_1LD0RA_1RA0LE_0RF0LC_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{D}} r) (at level 30).
Notation "l |> r" := (l {{C}}> r) (at level 30).

Notation hL := (D,[]).
Notation hR := (C,[]).
Notation hLR2 := ([(hL,hR)]^^2).
Notation hRL2 := ([(hR,hL)]^^2).

Definition C0 n m := <[0;1;1]^^n <+ <[0;0] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].
Definition C1 n m := <[0;1;1]^^n <+ <[0;1] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].

Notation lh := (0inf <* <[1;0;1;0;1;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(O,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a:
  exists r0,
  (forall r,
  LC1 x <| [1;0;0]^^(1+a) *> [0;0] *> r -->+
  r0 |> r) /\
  (forall r,
  r0 <| r -->*
  LC0 (cons x a) |> r).
Proof.
  gen a.
  induction x; intros; cbn.
  - eexists; split.
    + es.
    + es.
  - destruct a as [n m].
    destruct (IHx n) as [r0 [I1 I2]].
    eexists; split.
    + es; er.
      follow100 I1.
      es; er.
      follow I2.
      es.
    + es.
Qed.

Definition RC n := [1;0;0]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  LC1 x |> RC a -->+
  LC0 (cons x a) |> RC 1.
Proof.
  unfold RC.
  epose proof (Ov x a) as [r0 [I1 I2]].
  specialize (I1 0inf).
  cbn in I1.
  repeat rewrite <-const_unfold in I1.
  es; er.
  follow100 I1.
  er.
  follow I2.
  er.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x |> RC 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(1,1)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=LWF).
  2: repeat econstructor.
  intros x HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 1) as I2.
    rewrite <-lpow_mul in I1',I2.
    follow (sideRLs_concat_1 I2 I1').
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB1LB_1LC0RF_1RF0LD_0RE0LB_1RC---_1RA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Notation hL := (C,[]).
Notation hR := (B,[]).
Notation hLR2 := ([(hL,hR)]^^2).
Notation hRL2 := ([(hR,hL)]^^2).

Definition C0 n m := <[0;1;1]^^n <+ <[0;0] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].
Definition C1 n m := <[0;1;1]^^n <+ <[0;1] <+ <[0;1;1]^^m <+ <[0;1;0;1;1].

Notation lh := (0inf <* <[1;0;1;0;1;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(O,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a:
  exists r0,
  (forall r,
  LC1 x <| [1;0;0]^^(1+a) *> [0;0] *> r -->+
  r0 |> r) /\
  (forall r,
  r0 <| r -->*
  LC0 (cons x a) |> r).
Proof.
  gen a.
  induction x; intros; cbn.
  - eexists; split.
    + es.
    + es.
  - destruct a as [n m].
    destruct (IHx n) as [r0 [I1 I2]].
    eexists; split.
    + es; er.
      follow100 I1.
      es; er.
      follow I2.
      es.
    + es.
Qed.

Definition RC n := [1;0;0]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  LC1 x |> RC a -->+
  LC0 (cons x a) |> RC 1.
Proof.
  unfold RC.
  epose proof (Ov x a) as [r0 [I1 I2]].
  specialize (I1 0inf).
  cbn in I1.
  repeat rewrite <-const_unfold in I1.
  es; er.
  follow100 I1.
  er.
  follow I2.
  er.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x |> RC 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(0,1)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=LWF).
  2: repeat econstructor.
  intros x HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 1) as I2.
    rewrite <-lpow_mul in I1',I2.
    follow (sideRLs_concat_1 I2 I1').
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RF_1RD1LC_0RA1LE_1RF0LC_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l |> r" := (l {{A}}> r) (at level 30).

Notation hL := (C,[]).
Notation hR := (A,[]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1]^^(1+n) <+ <[0] <+ <[1]^^m <+ <[0;0;1].
Definition C1 n m := <[1]^^(1+n) <+ <[0] <+ <[1]^^m <+ <[1;0;1].

Notation lh := (0inf <* <[1;0;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(O,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [1]^^(1+a) *> [0;1] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n := [1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  x<>nil ->
  LC1 x <| RC (1+a) -->+
  LC0 (cons x a) <| RC 1.
Proof.
  unfold RC.
  intros Hx.
  destruct x as [|[n m] x].
  1: congruence.
  cbn.
  es; er.
  follow100 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x <| RC 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(0,2)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun x => LWF x /\ x<>[]).
  2: repeat econstructor; congruence.
  intros x [HP Hx].
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 1) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    rewrite Nat.add_comm.
    apply Ov'.
    pose proof (length_LIncs_y _ _ _ I1).
    destruct x,y; cbn in *; congruence.
  - split.
    + eapply LWF_step; eauto; lia.
    + destruct y as [|[n0 m0] y]; cbn; congruence.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC1LB_0RE1LD_1RF0LB_1RA1RE_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{B}} r) (at level 30).
Notation "l |> r" := (l {{E}}> r) (at level 30).

Notation hL := (B,[]).
Notation hR := (E,[]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1]^^(1+n) <+ <[0] <+ <[1]^^m <+ <[0;0;1].
Definition C1 n m := <[1]^^(1+n) <+ <[0] <+ <[1]^^m <+ <[1;0;1].

Notation lh := (0inf <* <[1;0;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(O,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [1]^^(1+a) *> [0;1] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n := [1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  x<>nil ->
  LC1 x <| RC (1+a) -->+
  LC0 (cons x a) <| RC 1.
Proof.
  unfold RC.
  intros Hx.
  destruct x as [|[n m] x].
  1: congruence.
  cbn.
  es; er.
  follow100 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x <| RC 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(0,1)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun x => LWF x /\ x<>[]).
  2: repeat econstructor; congruence.
  intros x [HP Hx].
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 1) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    rewrite Nat.add_comm.
    apply Ov'.
    pose proof (length_LIncs_y _ _ _ I1).
    destruct x,y; cbn in *; congruence.
  - split.
    + eapply LWF_step; eauto; lia.
    + destruct y as [|[n0 m0] y]; cbn; congruence.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1LE_1RD1RC_1LA0RF_1RF0LA_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{A}} r) (at level 30).
Notation "l |> r" := (l {{C}}> r) (at level 30).

Notation hL := (A,[]).
Notation hR := (C,[]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1]^^(1+n) <+ <[0] <+ <[1]^^m <+ <[0;0;1].
Definition C1 n m := <[1]^^(1+n) <+ <[0] <+ <[1]^^m <+ <[1;0;1].

Notation lh := (0inf <* <[1;0;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(O,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [1]^^(1+a) *> [0;1] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n := [1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  x<>nil ->
  LC1 x <| RC (1+a) -->+
  LC0 (cons x a) <| RC 1.
Proof.
  unfold RC.
  intros Hx.
  destruct x as [|[n m] x].
  1: congruence.
  cbn.
  es; er.
  follow100 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x <| RC 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(0,0)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun x => LWF x /\ x<>[]).
  2: repeat econstructor; congruence.
  intros x [HP Hx].
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 1) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    rewrite Nat.add_comm.
    apply Ov'.
    pose proof (length_LIncs_y _ _ _ I1).
    destruct x,y; cbn in *; congruence.
  - split.
    + eapply LWF_step; eauto; lia.
    + destruct y as [|[n0 m0] y]; cbn; congruence.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB1RA_0LC1RD_1RC0LB_0RA0RE_1RF---_0RD1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{B}} [0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{F}}> r) (at level 30).

Notation hL := (B,[0;0]).
Notation hR := (F,[1]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1]^^(n) <+ <[1;0;0;1] <+ <[1]^^m <+ <[0].
Definition C1 n m := <[1]^^(n) <+ <[1;1;0;1] <+ <[1]^^m <+ <[0].


Notation lh := (0inf <* <[1;1;1;1;0;1;1;0]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(1%nat,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [1]^^(1+a) *> [0;0] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n := [1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*3+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  LC1 x <| RC (1+a) -->+
  LC0 (cons x a) <| RC 3.
Proof.
  unfold RC.
  replace 0inf with ([0;0]*>0inf) by solve_const0_eq.
  follow10 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,2+k*3+m)) (y<:(3+k*4+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)*3-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (3+m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    1: applys_eq IHk; flia.
    st.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x*3-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k*3+2<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (3+k0*4+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x <| RC 3.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(0,2)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun x => LWF x).
  2: repeat econstructor.
  intros x HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 3) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    replace (k*3+3) with (1+(2+k*3)) by lia.
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RB_0RD0RA_1LE1RD_0LF1RC_1RF0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{E}} [0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).

Notation hL := (E,[0;0]).
Notation hR := (B,[1]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1]^^(n) <+ <[1;0;0;1] <+ <[1]^^m <+ <[0].
Definition C1 n m := <[1]^^(n) <+ <[1;1;0;1] <+ <[1]^^m <+ <[0].


Notation lh := (0inf <* <[1;1;1;1;0;1;1;0]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(1%nat,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [1]^^(1+a) *> [0;0] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n := [1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*3+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  LC1 x <| RC (1+a) -->+
  LC0 (cons x a) <| RC 3.
Proof.
  unfold RC.
  replace 0inf with ([0;0]*>0inf) by solve_const0_eq.
  follow10 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,2+k*3+m)) (y<:(3+k*4+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)*3-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (3+m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    1: applys_eq IHk; flia.
    st.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x*3-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k*3+2<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (3+k0*4+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x <| RC 3.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(1,2)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun x => LWF x).
  2: repeat econstructor.
  intros x HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 3) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    replace (k*3+3) with (1+(2+k*3)) by lia.
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB1RA_0LC1RD_1RC0LB_0RA1RE_0RF---_0RD1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{B}} [0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{F}}> r) (at level 30).

Notation hL := (B,[0;0]).
Notation hR := (F,[]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1]^^(n) <+ <[1;0;0;1;1] <+ <[1]^^m <+ <[0].
Definition C1 n m := <[1]^^(n) <+ <[1;1;0;1;1] <+ <[1]^^m <+ <[0].


Notation lh := (0inf <* <[1;1;1;1;0;1;1;1;0]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(1%nat,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [1]^^(1+a) *> [0;0] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n := [1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL2^^n) (RC m) (RC (n*2+m)).
Proof.
  unfold RC.
  sideRLs_ind n.
Qed.

Lemma Ov' x a:
  LC1 x <| RC (1+a) -->+
  LC0 (cons x a) <| RC 2.
Proof.
  unfold RC.
  replace 0inf with ([0;0]*>0inf) by solve_const0_eq.
  follow10 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,1+k+m)) (y<:(3+k*3+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (1+m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    1: applys_eq IHk; flia.
    st.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k+1<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (3+k0*3+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S x := LC0 x <| RC 2.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S [(0,1)]).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun x => LWF x).
  2: repeat econstructor.
  intros x HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists; split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k 2) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    replace (k*2+2) with (1+(1+k*2)) by lia.
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB1LB_0LC1RD_0RA1LC_0RB1RE_0RD0RF_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{C}} [] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{E}}> r) (at level 30).

Notation hL := (C,[]).
Notation hR := (E,[]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[0;1]^^(n) <+ <[0;0;1] <+ <[0;1]^^m <+ <[1].
Definition C1 n m := <[0;1]^^(n) <+ <[0;1;1] <+ <[0;1]^^m <+ <[1].


Notation lh := (0inf <* <[1;1;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(0%nat,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [0;1]^^(1+a) *> [1] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n m := [0;1]^^n *> [1] *> [0;1]^^m *> 0inf.

Lemma RIncs k n m:
  sideRLs tm (hRL2^^k) (RC n m) (RC (k+n) (k+m)).
Proof.
  unfold RC.
  sideRLs_ind k.
Qed.

Lemma Ov' x a b:
  LC1 x <| RC (1+a) b -->+
  LC0 (cons x a) <| RC (1+b) 1.
Proof.
  unfold RC.
  follow10 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S '(x,a) := LC0 x <| RC (1+a) 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S([(0,1)],1)).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(x,a) => LWF x).
  2: repeat econstructor.
  intros [x a] HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists (_,_); split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k _ _) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    replace (k+(1+a)) with (1+(k+a)) by lia.
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB1LB_0LC1RD_0RA1LC_0RB1RE_0RD0RF_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{C}} [] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{E}}> r) (at level 30).

Notation hL := (C,[]).
Notation hR := (E,[]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[0;1]^^(n) <+ <[0;0;1] <+ <[0;1]^^m <+ <[1].
Definition C1 n m := <[0;1]^^(n) <+ <[0;1;1] <+ <[0;1]^^m <+ <[1].


Notation lh := (0inf <* <[1;1;1]).
Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC1 t <* C1 n m
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| (n,m)::t => LC0 t <* C0 n m
end.

Fixpoint cons(x:LS)(a:nat) :=
match x with
| [] => [(0%nat,a)]
| t<:(n,m) => (cons t n)<:(m,a)
end.

Lemma Ov x a r:
  LC1 x <| [0;1]^^(1+a) *> [1] *> r -->+
  LC0 (cons x a) |> r.
Proof.
  gen a r.
  induction x; intros; cbn.
  - es.
  - destruct a as [n m].
    specialize (IHx n).
    es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n m := [0;1]^^n *> [1] *> [0;1]^^m *> 0inf.

Lemma RIncs k n m:
  sideRLs tm (hRL2^^k) (RC n m) (RC (k+n) (k+m)).
Proof.
  unfold RC.
  sideRLs_ind k.
Qed.

Lemma Ov' x a b:
  LC1 x <| RC (1+a) b -->+
  LC0 (cons x a) <| RC (1+b) 1.
Proof.
  unfold RC.
  follow10 Ov.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Inductive LWF: LS->Prop :=
| LWF_O:
  LWF []
| LWF_S x n m:
  LWF x ->
  2^(length x)-1<=m ->
  LWF (x<:(n,m))
.

Lemma LIncs_spec x y k:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x) (LC1 y).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Lemma length_LIncs_y x y k:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_cons x a:
  length (cons x a) =
  S (length x).
Proof.
  gen a.
  induction x as [|[]]; intros; cbn.
  - reflexivity.
  - rewrite IHx.
    reflexivity.
Qed.

Lemma LWF_spec x:
  LWF x ->
  exists y, LIncs x y (2^(length x)-1).
Proof.
  intros H.
  induction H.
  - eexists.
    constructor.
  - destruct IHLWF as [y I1].
    cbn.
    eexists.
    applys_eq (LIncs_S _ _ _ n (m-(2^length x-1)) I1); flia.
Qed.

Lemma LWF_step x y k a:
  LWF x ->
  LIncs x y k ->
  k<=a ->
  LWF (cons y a).
Proof.
  gen y k a.
  induction x; intros.
  - inverts H0.
    econstructor; eauto.
  - inverts H.
    inverts H0.
    unshelve epose proof (IHx _ _ (k0+n) H4 H8 _) as I1.
    1: lia.
    cbn.
    econstructor; eauto.
    rewrite length_cons.
    erewrite length_LIncs_y by eauto.
    epose proof (LIncs_k _ _ _ H8).
    cbn; lia.
Qed.

Definition S '(x,a) := LC0 x <| RC (1+a) 1.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S([(0,1)],1)).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(x,a) => LWF x).
  2: repeat econstructor.
  intros [x a] HP.
  destruct (LWF_spec _ HP) as [y I1].
  remember (2^length x-1) as k.
  unfold S.
  eexists (_,_); split.
  - epose proof (LIncs_spec _ _ _ I1) as I1'.
    epose proof (RIncs k _ _) as I2.
    follow (sideRLs_concat_1L I2 I1').
    unfold to_DH_config.
    replace (k+(1+a)) with (1+(k+a)) by lia.
    apply Ov'.
  - eapply LWF_step; eauto; lia.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_0LA1RA_1LE1RD_0LE0RF_1LC1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{E}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{F}}> r) (at level 30).

Notation hL := (E,[0]).
Notation hR := (F,[1]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1;1]^^(n) <+ <[1;0;1] <+ <[1;1]^^m <+ <[0].
Definition C1 n m := <[1;1]^^(n) <+ <[1;1;0] <+ <[1;1]^^m <+ <[0].

Lemma Incs01 k n m:
  segRLs tm' (hLR2^^(k*2+1)) (hLR2^^k) (C0 n ((k*2+1)+m)) (C1 ((k*2+1)+n) m).
Proof.
  gen n m.
  induction k; intros.
  1: esx.
  remember (k*2+1) as k2.
  replace (S k*2+1) with (k2+2) by lia.
  replace (S k) with (k+1) by lia.
  eapply segRLs_trans_add.
  1: applys_eq (IHk n (2+m)); flia.
  unfold C0,C1.
  st.
  esx.
Qed.


Notation lh := (0inf <* <[1;1;1;0;0]).
Notation LS := (list (nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| n::t => LC1 t <* C1 n 0
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| n::t => LC0 t <* C0 0 n
end.

Lemma Ov x r:
  LC1 x <| r -->+
  LC0 x <* <[1;0] {{D}}> r.
Proof.
  gen r.
  induction x; intros; cbn.
  - es.
  - es; er.
    follow100 IHx.
    es.
Qed.

Definition RC0 n := [1;1]^^n *> [1] *> 0inf.
Definition RC1 n m := [1;1]^^n *> [0;1] *> [1;1]^^m *> 0inf.

Lemma RIncs0 k n:
  sideRLs tm (hRL2^^k) (RC0 n) (RC0 (k+n)).
Proof.
  unfold RC0.
  sideRLs_ind k.
Qed.

Lemma RIncs1 k n m:
  sideRLs tm (hRL2^^k) (RC1 n m) (RC1 (k*2+n) (k*2+m)).
Proof.
  unfold RC1.
  sideRLs_ind k.
Qed.

Lemma Ov0 x n:
  LC1 x <| RC0 n -->+
  LC0 x <| RC1 2 (2+n).
Proof.
  unfold RC0,RC1.
  follow10 Ov.
  es.
Qed.

Lemma Ov1 x n m:
  LC1 x <| RC1 (1+n) m -->+
  LC0 (x<:n) <| RC0 (1+m).
Proof.
  unfold RC0,RC1.
  follow10 Ov.
  es.
Qed.

Fixpoint Ln n :=
match n with
| O => []
| S n0 => Ln n0 <: (2^n0*2-1)
end.

Lemma LIncs n:
  sideRLs tm' (hLR2^^(2^n-1)) (LC0 (Ln n)) (LC1 (Ln n)).
Proof.
  induction n; cbn[Ln]; cbn[LC0]; cbn[LC1].
  - esx.
  - remember (2^n-1) as k.
    replace (2^n*2-1) with (k*2+1) by lia.
    replace (2^S n-1) with (k*2+1) by (cbn; lia).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (Incs01 k 0 0); flia.
Qed.

Lemma BigStep k n:
  LC0 (Ln k) <| RC0 n -->+
  LC0 (Ln (S k)) <| RC0 (2^k*3+n).
Proof.
  epose proof (sideRLs_concat_1L (RIncs0 _ _) (LIncs _)) as I1.
  follow I1. clear I1.
  unfold to_DH_config.
  follow10 Ov0.
  epose proof (sideRLs_concat_1L (RIncs1 _ _ _) (LIncs _)) as I1.
  follow I1. clear I1.
  unfold to_DH_config.
  replace ((2^k-1)*2+2) with (1+(2^k*2-1)) by (cbn; lia).
  follow100 Ov1.
  cbn[Ln].
  finish.
Qed.

Definition S '(x,a) := LC0 (Ln x) <| RC0 a.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,6)).
  1: unfold S; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros [x a].
  eexists (_,_).
  apply BigStep.
Qed.
  
End TM17.

From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.

Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB1LF_0LC0RD_1LB1LA_1RE0RE_1LB1RD_---1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{A}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{D}}> r) (at level 30).

Notation hL := (A,[1;0]).
Notation hR := (D,<[0;1]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1;0;1;1]^^(n) <+ <[0;1;0] <+ <[1;1;1;0]^^m <+ <[1;1;1].
Definition C1 n m := <[1;0;1;1]^^(n) <+ <[1;0;1] <+ <[1;1;1;0]^^m <+ <[1;1;1].


Lemma Incs01 k n m:
  segRLs tm' (hLR2^^(k*2+1)) (hLR2^^k) (C0 n (k+m)) (C1 (k+n) m).
Proof.
  gen n m.
  induction k; intros.
  1: esx.
  remember (k*2+1) as k2.
  replace (S k*2+1) with (k2+2) by lia.
  replace (S k) with (k+1) by lia.
  eapply segRLs_trans_add.
  1: applys_eq (IHk n (1+m)); flia.
  unfold C0,C1.
  st.
  esx.
Qed.


Notation lh := (0inf <* <[1;0;1;1;1;1]).
Notation LS := (list (nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| n::t => LC1 t <* C1 n 0
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| n::t => LC0 t <* C0 0 n
end.

Lemma Ov x r:
  LC1 x <| r -->+
  LC0 x <* <[0;1;0] {{E}}> r.
Proof.
  gen r.
  induction x; intros; cbn.
  - es.
  - es; er.
    follow100 IHx.
    es.
Qed.

Definition RC0 n := [1] *> [0;1;1;1]^^n *> 0inf.
Definition RC1 n m := [1;0;1;1]^^n *> [1;1] *> [0;1;1;1]^^m *> 0inf.

Lemma RIncs0 k n:
  sideRLs tm (hRL2^^k) (RC0 n) (RC0 (k+n)).
Proof.
  unfold RC0.
  sideRLs_ind k.
Qed.

Lemma RIncs1 k n m:
  sideRLs tm (hRL2^^k) (RC1 n m) (RC1 (k+n) m).
Proof.
  unfold RC1.
  sideRLs_ind k.
Qed.

Lemma Ov0 x n:
  LC1 x <| RC0 n -->+
  LC0 x <| RC1 1 n.
Proof.
  unfold RC0,RC1.
  follow10 Ov.
  es.
Qed.


Lemma Ov1 x n m:
  LC1 x <| RC1 (1+n) m -->+
  LC0 (x<:n) <| RC0 (1+m).
Proof.
  unfold RC0,RC1.
  follow10 Ov.
  es_v2.
Qed.

Fixpoint Ln n :=
match n with
| O => []
| S n0 => Ln n0 <: (2^n0-1)
end.

Lemma LIncs n:
  sideRLs tm' (hLR2^^(2^n-1)) (LC0 (Ln n)) (LC1 (Ln n)).
Proof.
  induction n; cbn[Ln]; cbn[LC0]; cbn[LC1].
  - esx.
  - remember (2^n-1) as k.
    replace (2^S n-1) with (k*2+1) by (cbn; lia).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (Incs01 k 0 0); flia.
Qed.

Lemma BigStep k n:
  LC0 (Ln k) <| RC0 n -->+
  LC0 (Ln (S k)) <| RC0 (2^k+n).
Proof.
  epose proof (sideRLs_concat_1L (RIncs0 _ _) (LIncs _)) as I1.
  follow I1. clear I1.
  unfold to_DH_config.
  follow10 Ov0.
  epose proof (sideRLs_concat_1L (RIncs1 _ _ _) (LIncs _)) as I1.
  follow I1. clear I1.
  unfold to_DH_config.
  rewrite Nat.add_comm.
  follow100 Ov1.
  cbn[Ln].
  finish.
Qed.

Definition S '(x,a) := LC0 (Ln x) <| RC0 a.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,1)).
  1: unfold S; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros [x a].
  eexists (_,_).
  apply BigStep.
Qed.
 
End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1RB1LF_0LC0RD_1LB1LA_1RE0RE_1LB1RD_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{A}} [1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{D}}> r) (at level 30).

Notation hL := (A,[1;0]).
Notation hR := (D,<[0;1]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[1;0;1;1]^^(n) <+ <[0;1;0] <+ <[1;1;1;0]^^m <+ <[1;1;1].
Definition C1 n m := <[1;0;1;1]^^(n) <+ <[1;0;1] <+ <[1;1;1;0]^^m <+ <[1;1;1].


Lemma Incs01 k n m:
  segRLs tm' (hLR2^^(k*2+1)) (hLR2^^k) (C0 n (k+m)) (C1 (k+n) m).
Proof.
  gen n m.
  induction k; intros.
  1: esx.
  remember (k*2+1) as k2.
  replace (S k*2+1) with (k2+2) by lia.
  replace (S k) with (k+1) by lia.
  eapply segRLs_trans_add.
  1: applys_eq (IHk n (1+m)); flia.
  unfold C0,C1.
  st.
  esx.
Qed.


Notation lh := (0inf <* <[1;0;1;1;1;1]).
Notation LS := (list (nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh
| n::t => LC1 t <* C1 n 0
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh
| n::t => LC0 t <* C0 0 n
end.

Lemma Ov x r:
  LC1 x <| r -->+
  LC0 x <* <[0;1;0] {{E}}> r.
Proof.
  gen r.
  induction x; intros; cbn.
  - es.
  - es; er.
    follow100 IHx.
    es.
Qed.

Definition RC0 n := [1] *> [0;1;1;1]^^n *> 0inf.
Definition RC1 n m := [1;0;1;1]^^n *> [1;1] *> [0;1;1;1]^^m *> 0inf.

Lemma RIncs0 k n:
  sideRLs tm (hRL2^^k) (RC0 n) (RC0 (k+n)).
Proof.
  unfold RC0.
  sideRLs_ind k.
Qed.

Lemma RIncs1 k n m:
  sideRLs tm (hRL2^^k) (RC1 n m) (RC1 (k+n) m).
Proof.
  unfold RC1.
  sideRLs_ind k.
Qed.

Lemma Ov0 x n:
  LC1 x <| RC0 n -->+
  LC0 x <| RC1 1 n.
Proof.
  unfold RC0,RC1.
  follow10 Ov.
  es.
Qed.


Lemma Ov1 x n m:
  LC1 x <| RC1 (1+n) m -->+
  LC0 (x<:n) <| RC0 (1+m).
Proof.
  unfold RC0,RC1.
  follow10 Ov.
  es_v2.
Qed.

Fixpoint Ln n :=
match n with
| O => []
| S n0 => Ln n0 <: (2^n0-1)
end.

Lemma LIncs n:
  sideRLs tm' (hLR2^^(2^n-1)) (LC0 (Ln n)) (LC1 (Ln n)).
Proof.
  induction n; cbn[Ln]; cbn[LC0]; cbn[LC1].
  - esx.
  - remember (2^n-1) as k.
    replace (2^S n-1) with (k*2+1) by (cbn; lia).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (Incs01 k 0 0); flia.
Qed.

Lemma BigStep k n:
  LC0 (Ln k) <| RC0 n -->+
  LC0 (Ln (S k)) <| RC0 (2^k+n).
Proof.
  epose proof (sideRLs_concat_1L (RIncs0 _ _) (LIncs _)) as I1.
  follow I1. clear I1.
  unfold to_DH_config.
  follow10 Ov0.
  epose proof (sideRLs_concat_1L (RIncs1 _ _ _) (LIncs _)) as I1.
  follow I1. clear I1.
  unfold to_DH_config.
  rewrite Nat.add_comm.
  follow100 Ov1.
  cbn[Ln].
  finish.
Qed.

Definition S '(x,a) := LC0 (Ln x) <| RC0 a.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,1)).
  1: unfold S; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros [x a].
  eexists (_,_).
  apply BigStep.
Qed.
 
End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB1RA_1RC0LD_1RD0RB_0LA0RE_1RF---_0RC0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{D}} [] *> r) (at level 30).
Notation "l |c> r" := (l <* <[] {{C}}> r) (at level 30).
Notation "l |e> r" := (l <* <[] {{E}}> r) (at level 30).

Notation hL := (D,[]).
Notation hR := (C,<[]).
Notation hR' := (E,<[]).
Notation hLR := [(hL,hR)].
Notation hLR' := [(hL,hR')].
Notation hLR2 := [(hL,hR);(hL,hR')].
Notation hRL2 := [(hR,hL);(hR',hL)].

Definition C0 n m := <[1;0]^^(1+n) <+ <[0] <+ <[1;0]^^m <+ <[1;1;0].
Definition C3 n := <[1;0]^^n <+ <[1;1;0;0;1;0].



Lemma Incs01 k n:
  segRLs tm' (hLR2^^(k*2+2)++hLR) (hLR2^^k++hLR) (C0 (n*2) (k*2+1)) (C3 (k*2+n*2+1)).
Proof.
  unfold C0,C3.
  gen n.
  induction k; intros.
  1: esx.
  remember (k*2+2) as k2.
  replace (S k*2+2) with (2+k2) by lia.
  replace (S k) with (1+k) by lia.
  do 2 rewrite lpow_add,<-app_assoc.
  eapply segRLs_trans.
  2: applys_eq (IHk (S n)); flia.
  esx.
Qed.

Notation lh0 := (0inf <* <[1;0;1;1;0]).
Notation lh1 := (0inf <* <[1;0;0;1;0]).
Notation LS := (list (nat)).

Fixpoint LC1(x:LS):side :=
match x with
| [] => lh1
| n::t => LC1 t <* C3 (1+n)
end.

Fixpoint LC0(x:LS):side :=
match x with
| [] => lh0
| n::t => LC0 t <* C0 0 (1+n)
end.

Lemma Ov x r:
  LC1 x <| r -->+
  LC0 x <* <[1;0;0] {{B}}> r.
Proof.
  gen r.
  induction x; intros; cbn.
  - es.
  - es; er.
    follow100 IHx.
    es.
Qed.

Definition RC n := [0;1]^^n *> 0inf.

Lemma RIncs k:
  sideRLs tm (hRL2^^k) (RC 0) (RC (k*2)).
Proof.
  unfold RC.
  sideRLs_ind k.
Qed.

Lemma Ov' x n:
  LC1 x <| RC (1+n) -->+
  LC0 (x<:n) <| RC 0.
Proof.
  unfold RC.
  follow10 Ov.
  es.
Qed.

Fixpoint Ln n :=
match n with
| O => []
| S n0 => Ln n0 <: ((2^n0*2-2)*2)
end.

Lemma LIncs n:
  sideRLs tm' (hLR2^^(2^n*2-2) ++ hLR) (LC0 (Ln n)) (LC1 (Ln n)).
Proof.
  induction n; cbn[Ln]; cbn[LC0]; cbn[LC1].
  - esx.
  - remember (2^n*2-2) as k.
    replace (2^S n*2-2) with (k*2+2) by (cbn; lia).
    eapply segRLs_sideRLs_concat.
    2: apply IHn.
    applys_eq (Incs01 k 0); flia.
Qed.

Lemma BigStep k:
  LC0 (Ln k) <| RC 0 -->+
  LC0 (Ln (S k)) <| RC 0.
Proof.
  epose proof (LIncs k) as HL.
  remember (2^k*2-2) as v1.
  replace (hLR2^^v1++hLR) with (lrcons hL (hRL2^^v1) hR) in HL.
  2:{
    clear.
    induction v1; cbn.
    1: trivial.
    rewrite IHv1; trivial.
  }
  epose proof (sideRLs_concat_L HL (RIncs _)) as I1.
  follow10 I1. clear I1.
  unfold to_DH_config.
  unfold RC.
  es; er.
  epose proof (Ov' (Ln k) (v1*2)) as I2.
  eapply evstep_trans.
  2: follow100 I2.
  1: cbn; es.
  clear I2.
  cbn.
  subst.
  es.
Qed.

Definition S x := LC0 (Ln x) <| RC 0.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S 0).
  1: unfold S; esx.
  eapply progress_nonhalt_simple.
  unfold S.
  intros x.
  eexists.
  apply BigStep.
Qed.
 
End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1RB1LB_0LC1RD_0RA1LC_0RB1RE_0RD0LF_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{C}} [] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{E}}> r) (at level 30).

Notation hL := (C,[]).
Notation hR := (E,[]).
Notation hLR2 := [(hL,hR)].
Notation hRL2 := [(hR,hL)].

Definition C0 n m := <[0;1]^^(n) <+ <[0;0;1] <+ <[0;1]^^m <+ <[1].
Definition C1 n m := <[0;1]^^(n) <+ <[0;1;1] <+ <[0;1]^^m <+ <[1].

Inductive LH := LH1|LH2|LH3.

Definition toLH x :=
match x with
| LH1 => 0inf
| LH2 => 0inf <* <[1;1;0;1;0;1;1]
| LH3 => 0inf <* <[1;1;1]
end.

Notation LS := (list (nat*nat)).

Fixpoint LC1(x:LS)(y:LH):side :=
match x with
| [] => toLH y
| (n,m)::t => LC1 t y <* C1 n m
end.

Fixpoint LC0(x:LS)(y:LH):side :=
match x with
| [] => toLH y
| (n,m)::t => LC0 t y <* C0 n m
end.

Inductive Ov: LS->LH->nat->LS->LH->Prop :=
| Ov_1 m a:
  m<>O ->
  Ov [(2,m)] LH1 a [(m,a)] LH2
| Ov_2 a:
  Ov [] LH2 a [(2,a)] LH3
| Ov_3 a:
  Ov [] LH3 a [(2,a)] LH1
| Ov_S x y n m a x' y':
  Ov x y n x' y' ->
  m<>O ->
  Ov (x<:(n,m)) y a (x'<:(m,a)) y'
.

Lemma Ov_spec x y a x' y':
  Ov x y a x' y' ->
  forall r,
  LC1 x y <| [0;1]^^(1+a) *> [1] *> r -->+
  LC0 x' y' |> r.
Proof.
  intro H.
  induction H; intros.
  - destruct m. 1: lia.
    es.
  - es.
  - es.
  - cbn[LC0 LC1].
    unfold C0,C1.
    destruct m. 1: lia.
    es; er.
    follow100 IHOv.
    es.
Qed.

Definition RC n m := [0;1]^^(1+n) *> [1] *> [0;1]^^m *> 0inf.

Lemma RIncs k n m:
  sideRLs tm (hRL2^^k) (RC n m) (RC (k+n) (k+m)).
Proof.
  unfold RC.
  sideRLs_ind k.
Qed.

Lemma Ov' x y a x' y' b:
  Ov x y a x' y' ->
  LC1 x y <| RC a b -->+
  LC0 x' y' <| RC b 1.
Proof.
  unfold RC.
  intro H.
  eapply Ov_spec in H.
  follow10 H.
  es.
Qed.

Inductive LIncs: LS->LS->nat->Prop :=
| LIncs_O:
  LIncs [] [] 0
| LIncs_S x y k n m:
  LIncs x y k ->
  LIncs (x<:(n,k+m)) (y<:(k+n,m)) (k*2+1)
.

Lemma LIncs_spec x y k z:
  LIncs x y k ->
  sideRLs tm' (hLR2^^k) (LC0 x z) (LC1 y z).
Proof.
  intros H.
  induction H.
  - esx.
  - cbn[LC0]; cbn[LC1].
    eapply segRLs_sideRLs_concat.
    2: apply IHLIncs.
    clear.
    unfold C0,C1.
    gen n m.
    induction k; intros.
    1: esx.
    specialize (IHk n (S m)).
    replace (S k*2+1) with ((k*2+1)+2) by lia.
    replace (S k) with (k+1) by lia.
    remember (k*2+1) as k2.
    do 2 rewrite lpow_add.
    replace (k+1+m) with (k+S m) by lia.
    eapply segRLs_trans.
    1: apply IHk.
    simpl_tape; cbn.
    esx.
Qed.

Definition S' '(x,y,z) := LC0 x y <| RC z 1.

Lemma BigStep x y z x0 x1 y0 k:
  LIncs x x0 k ->
  Ov x0 y (k+z) x1 y0 ->
  S' (x,y,z) -->+
  S' (x1,y0,k+1).
Proof.
  unfold S'.
  intros I1 I2.
  eapply LIncs_spec in I1.
  eapply Ov' in I2.
  epose proof (sideRLs_concat_1L (RIncs k _ _) I1) as I1'.
  follow I1'.
  apply I2.
Qed.

Lemma init:
  c0 -->*
  S' (<[(2,2);(1%nat,3);(2,5)],LH1,4).
Proof.
  esx.
Qed.

Lemma length_LIncs {x y k}:
  LIncs x y k ->
  length y = length x.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma LIncs_k x y k:
  LIncs x y k ->
  k = 2^(length x)-1.
Proof.
  intros H.
  induction H; cbn; lia.
Qed.

Lemma length_Ov {x y a x' y'}:
  Ov x y a x' y' ->
  length x' = length x + (match y with LH1 => 0 | _ => 1 end).
Proof.
  intro H.
  induction H; cbn; trivial.
  rewrite IHOv; trivial.
Qed.

Inductive LWF: LS->LH->Prop :=
| LWF_S x y n m
  (Ha:LWF x y)
  (Hb:2^(length x)<=m)
  (Hc:n<>O):
  LWF (x<:(n,m)) y
| LWF_O_1:
  LWF [(2,2)] LH1
| LWF_O_2 a:
  2<=a ->
  LWF [(2,a)] LH2
| LWF_O_3 a a0:
  2<=a ->
  2<=a0 ->
  LWF [(a,a0);(2,2)] LH3
.

Notation len := length.

Inductive aWF: LS->LH->nat->Prop :=
| aWF_intro x y a
  (HaWF:2^(len x) <= a):
  aWF x y a
.

Lemma LWF_spec x y a:
  LWF x y ->
  aWF x y a ->
  exists x0 k,
  LIncs x x0 k /\
  exists x1 y0,
  Ov x0 y a x1 y0 /\
  LWF x1 y0.
Proof.
  intro H.
  gen a.
  induction H.
  - intros.
    epose proof (IHLWF _ _) as [x0 [k [I1 [x1 [y0 [I2 I3]]]]]].
    epose proof (LIncs_k _ _ _ I1); subst.
    eexists _,_; split.
    { applys_eq (LIncs_S _ _ _ n (m-(2^(length x)-1)) I1).
      flia. }
    eexists _,_; split.
    { apply Ov_S.
      2: lia.
      apply I2. }
    eapply LWF_S.
    + apply I3.
    + inverts H0.
      cbn in HaWF.
      epose proof (length_LIncs I1).
      epose proof (length_Ov I2).
      rewrite H1,H0.
      destruct y; rewrite Nat.pow_add_r; lia.
    + lia.
    Unshelve.
    { econstructor; lia. }
  - intros.
    inverts H.
    cbn in HaWF.
    eexists _,_; split.
    { eapply LIncs_S with (k:=O) (m:=2).
      apply LIncs_O. }
    eexists _,_; split.
    { apply Ov_1; lia. }
    apply LWF_O_2,HaWF.
  - intros.
    inverts H0.
    cbn in HaWF.
    eexists _,_; split.
    { eapply LIncs_S with (k:=O) (m:=a).
      apply LIncs_O. }
    eexists _,_; split.
    { apply Ov_S. 2: lia.
      apply Ov_2. }
    apply LWF_O_3; lia.
  - intros.
    inverts H1.
    cbn in HaWF.
    eexists _,_; split.
    { epose proof (LIncs_O) as I1.
      apply LIncs_S with (n:=2) (m:=2) in I1.
      apply LIncs_S with (n:=a) (m:=a0-1) in I1.
      cbn in I1.
      applys_eq I1; flia. }
    eexists _,_; split.
    { apply Ov_S. 2: lia.
      apply Ov_S. 2: lia.
      apply Ov_3. }
    apply LWF_S.
    2,3: cbn; lia.
    apply LWF_S.
    2,3: cbn; lia.
    apply LWF_O_1.
Qed.

Close Scope sym.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(x,y,z) => LWF x y /\ 1<=z).
  2:{
    split.
    - apply LWF_S. 2,3: cbn; lia.
      apply LWF_S. 2,3: cbn; lia.
      apply LWF_O_1.
    - lia.
  }
  intros [[x y] z] [HP HP0].
  epose proof (LWF_spec _ _ (2^len x-1+z) HP _) as [x0 [k [I1 [x1 [y0 [I2 I3]]]]]].
  epose proof (LIncs_k _ _ _ I1); subst.
  eapply BigStep in I1.
  2: apply I2.
  eexists (_,_,_); split.
  1: apply I1.
  split.
  1: apply I3.
  lia.
  Unshelve.
  apply aWF_intro; lia.
Qed.

End TM21.

