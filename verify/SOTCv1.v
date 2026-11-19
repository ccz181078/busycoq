From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import NatMod NatMod_v2 Longitudinal BinaryCounter_v2.
From BusyCoq Require NatMod_v3.


Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1RC0RC_1LD0RA_---0LE_1RF1LE_1RA0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (F,[1]).
Notation hR'' := (C,[0]).
Notation hR := (A,[0]).
Notation hL := (E,[]).
Notation hRL := [(hR,hL)].
Notation hLR' := [(hL,hR')].
Notation hLR'' := [(hL,hR'')].
Notation hLR := [(hL,hR)].
Notation w0 := <[0;1;1;1].
Notation w1 := <[1;1;1].

Definition tm' := flip tm.

Definition P1 len n :=
  sideRLs tm' (hLR^^n++hLR') (w1^^len*>0inf) (w1^^len*>0inf).

Lemma P1_S len n:
  P1 len n ->
  P1 (1+len) (n+1+n).
Proof.
  unfold P1.
  intros HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2:{
    eapply sideRLs_trans.
    - apply HP1.
    - apply HP1.
  }
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  destruct n.
  1: esx.
  replace (S n) with (1+n) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  rewrite (app_assoc hLR').
  eapply segRLs_trans.
  1: esx.
  rewrite app_assoc,<-lpow_add,Nat.add_comm,lpow_add,<-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_n len:
  P1 len (2^len-1).
Proof.
  induction len.
  - unfold P1; esx.
  - apply P1_S in IHlen.
    cbn.
    applys_eq IHlen; lia.
Qed.

Lemma P1_S_2 len n:
  n<>O ->
  P1 len n ->
  sideRLs tm' (hLR^^(n+n)++hLR'') ([1;1]*>w1^^len*>0inf) (w1^^(1+len)*>0inf).
Proof.
  unfold P1.
  intros Hn HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2:{
    eapply sideRLs_trans.
    - apply HP1.
    - apply HP1.
  }
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  destruct n.
  1: lia.
  replace (S n) with (1+n) by lia.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  rewrite (app_assoc hLR').
  eapply segRLs_trans.
  1: esx.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  esx.
Qed.

Definition RC a b := [1]^^a *> [0;0;0] *> [1]^^b *> 0inf.

Lemma RIncs n a b:
  sideRLs tm (hRL^^n) (RC a b) (RC a (n+b)).
Proof.
  unfold RC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma hLR'_lrcons n h:
  (hLR^^n++[(hL,h)]) = lrcons hL (hRL^^n) h.
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma Halt_2 len b:
  len<>O ->
  halts tm (0inf <* w1^^len <* <[1;1] {{{ (hL,L) }}} RC 0 b).
Proof.
  intros.
  eapply halts_evstep.
  2:{
    epose proof (sideRLs_concat_L) as I1.
    erewrite <-hLR'_lrcons in I1.
    epose proof (I1 (P1_S_2 _ _ _ (P1_n _)) (RIncs _ _ _)) as I1.
    follow100 I1.
    finish.
  }
  remember (2^len-1) as v1.
  esx.
  Unshelve.
  destruct len; cbn; lia.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  1: apply (Halt_2 45 1); lia.
  esx.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC1RE_1LE0RD_1RC0RF_---0LA_0LA0RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (D,<[1;0]).
Notation hR := (C,[1]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR' := [(hL,hR')].
Notation hLR := [(hL,hR)].
Notation w0 := <[1;1;0].
Notation w1 := <[1;0].

Definition tm' := flip tm.

Goal segRLs tm' hLR hLR w0 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR w1 w1.
Proof. esx. Qed.

Goal segRLs tm' (hLR++hLR') hLR' w0 w1.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR' w1 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR' [] [0;0] [].
Proof. esx. Qed.

Definition P1 len n x :=
  sideRLs tm' (hLR^^n++hLR') x (w1^^len*>0inf).

Definition P1' len n := P1 len n (w1^^len*>0inf).

Lemma P1_S len n:
  P1' len n ->
  P1' (1+len) (n+1+(n+1)).
Proof.
  unfold P1',P1.
  intros HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2:{
    eapply sideRLs_trans.
    - apply HP1.
    - apply HP1.
  }
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  - rewrite lpow_add.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
  - rewrite lpow_add,<-app_assoc.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
Qed.

Lemma P1'_n len:
  P1' len ((2^len-1)*2).
Proof.
  induction len.
  - unfold P1',P1; esx.
  - apply P1_S in IHlen.
    cbn.
    applys_eq IHlen; lia.
Qed.

Lemma P1_S0 len n x:
  P1 len n x ->
  P1 (1+len) (n+1) (w0*>x).
Proof.
  unfold P1',P1 in *.
  intros HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  rewrite lpow_add,<-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_S1 len n x:
  P1 len n x ->
  P1 (1+len) (n+1+((2^len-1)*2+1)) (w1*>x).
Proof.
  epose proof (P1'_n len) as HP1'.
  unfold P1',P1 in *.
  intros HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2:{
    eapply sideRLs_trans.
    - apply HP1.
    - apply HP1'.
  }
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  - rewrite lpow_add.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
  - rewrite lpow_add,<-app_assoc.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
Qed.

Definition RC n := [0] *> [1]^^n *> 0inf.

Lemma RIncs n k:
  sideRLs tm (hRL^^n) (RC k) (RC (n+k)).
Proof.
  unfold RC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma ROv_0 l n:
  l {{{ (hR',R) }}} RC (0+n*5) -->*
  l <* w1 <* (w1<+w0)^^n {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_1 l n:
  l {{{ (hR',R) }}} RC (1+n*5) -->*
  l <* w1 <* (w1<+w0)^^n <* w1 {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_2 l n:
  l {{{ (hR',R) }}} RC (2+n*5) -->*
  l <* w1 <* (w1<+w0)^^n <* w0 {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_3 l n:
  l {{{ (hR',R) }}} RC (3+n*5) -->*
  l <* w1 <* (w1<+w0)^^n <* w1 <* w1 <* w1 {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_4 l n:
  halts tm (l {{{ (hR',R) }}} RC (4+n*5)).
Proof.
  unfold RC.
  esx.
Qed.

Definition S1 a b :=
  0inf <* w1^^a {{{ (hR',R) }}} RC b.

Lemma lcons_hRL_hRL' n:
  lcons hR (hLR^^n++hLR') = (hRL^^(n+1),hR').
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma app_not_nil_r {A} (a b:list A):
  b <> [] ->
  (a++b) <> [].
Proof.
  induction a; cbn; congruence.
Qed.

Lemma Incs len n x:
  P1 len n x ->
  x {{{ (hR,R) }}} RC 0 -->*
  0inf <* w1^^len {{{ (hR',R) }}} RC (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hRL_hRL' in I1.
  unshelve epose proof (I1 eq_refl _ HP1 (RIncs _ 0)) as I1.
  1: apply app_not_nil_r; congruence.
  rewrite Nat.add_0_r in I1.
  apply progress_evstep.
  apply I1.
Qed.

Local Opaque Nat.div Nat.modulo.

Lemma pow4_mod3 k:
  2^(k*2) mod 3 = 1%nat.
Proof.
  induction k; cbn; lia.
Qed.

Ltac rw_pa :=
  repeat rewrite Nat.pow_add_r by lia.

Lemma P1_01s len n x k:
  P1 len n x ->
  P1 (k*2+len) (2^len*(2^(k*2)/3)*2+n+k) ((w0++w1)^^k*>x).
Proof.
  gen len n x.
  induction k; intros.
  - cbn.
    applys_eq H; lia.
  - apply IHk in H.
    apply P1_S1 in H.
    apply P1_S0 in H.
    applys_eq H.
    pose proof (pow4_mod3 k).
    replace (2^(S k*2)/3) with (2^(k*2)/3*4+1) by (cbn; lia).
    rw_pa; lia.
Qed.

Lemma BigStep0 a b:
  S1 a (0+b*5) -->*
  S1 (b*2+a+1) ((2^(b*2)/3*4+4)*2^a+b-1).
Proof.
  unfold S1.
  follow ROv_0.
  follow Incs.
  - apply P1_01s,P1_S1,P1'_n.
  - rw_pa.
    finish.
Qed.

Lemma BigStep1 a b:
  S1 a (1+b*5) -->*
  S1 (b*2+a+2) ((2^(b*2)/3*16+8)*2^a+b-1).
Proof.
  unfold S1.
  follow ROv_1.
  follow Incs.
  - apply P1_S1,P1_01s,P1_S1,P1'_n.
  - rw_pa.
    pose proof (pow4_mod3 b).
    finish.
Qed.

Lemma BigStep2 a b:
  S1 a (2+b*5) -->*
  S1 (b*2+a+2) ((2^(b*2)/3*4+4)*2^a+b).
Proof.
  unfold S1.
  follow ROv_2.
  follow Incs.
  - apply P1_S0,P1_01s,P1_S1,P1'_n.
  - rw_pa.
    finish.
Qed.

Lemma BigStep3 a b:
  S1 a (3+b*5) -->*
  S1 (b*2+a+4) ((2^(b*2)/3*88+32)*2^a+b-1).
Proof.
  unfold S1.
  follow ROv_3.
  follow Incs.
  - apply P1_S1,P1_S1,P1_S1,P1_01s,P1_S1,P1'_n.
  - rw_pa.
    pose proof (pow4_mod3 b).
    finish.
Qed.

Lemma BigStep4 a b:
  halts tm (S1 a (4+b*5)).
Proof.
  intros.
  unfold S1.
  apply ROv_4.
Qed.

Lemma init:
  c0 -->* S1 5 63.
Proof.
  esx.
Qed.

Definition S' '(a,b) := S1 a b.

Close Scope sym.
Import PairIter.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep with (c':=S' (_,_)).
  2: apply init.
  eapply halts_if_simple with
    (C:=S')
    (f:=fun '(a,b0) =>
    let b:=b0/5 in
    match b0 mod 5 with
    | 0 => Some (b*2+a+1,(2^(b*2)/3*4+4)*2^a+b-1)
    | 1 => Some (b*2+a+2,(2^(b*2)/3*16+8)*2^a+b-1)
    | 2 => Some (b*2+a+2,(2^(b*2)/3*4+4)*2^a+b)
    | 3 => Some (b*2+a+4,(2^(b*2)/3*88+32)*2^a+b-1)
    | _ => None
    end).
  - intros [a b0].
    epose proof (div_mod' b0 5 (b0 mod 5) (eq_refl)) as I1.
    remember (b0/5) as b.
    unfold S'.
    destruct (b0 mod 5) as [|[|[|[|[|]]]]]; subst b0.
    + apply BigStep0. 
    + apply BigStep1. 
    + apply BigStep2. 
    + apply BigStep3. 
    + apply BigStep4. 
    + lia.
  - eapply pair_iter_halts_if with (g:=fun ls =>
    let a := Nvar 0 in
    let b0 := Nvar 1 in
    let b:=(b0/5)%Nexpr in
    match Nmod'' (2^30) b0 ls 5 with
    | None => Some ls
    | Some b1 =>
      (match b1 with
      | 0 => (cons2 (b*2+a+1,(2^(b*2)/3*4+4)*2^a+b-1) ls)
      | 1 => (cons2 (b*2+a+2,(2^(b*2)/3*16+8)*2^a+b-1) ls)
      | 2 => (cons2 (b*2+a+2,(2^(b*2)/3*4+4)*2^a+b) ls)
      | 3 => (cons2 (b*2+a+4,(2^(b*2)/3*88+32)*2^a+b-1) ls)
      | _ => None
      end)%Nexpr
    end).
    2:{
      apply iter_halts_c_spec with (T:=16).
      vm_compute; reflexivity.
    }
    solve_v1.
    destruct (z mod 5) as [|[|[|[|[|]]]]].
    6: lia.
    all: solve_v2.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RA_---0LD_1LE1LD_1RB1RC_0LD0RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (A,<[1;0]).
Notation hR := (B,[1]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR' := [(hL,hR')].
Notation hLR := [(hL,hR)].
Notation w0 := <[1;1;0].
Notation w1 := <[1;0].

Definition tm' := flip tm.

Goal segRLs tm' hLR hLR w0 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR w1 w1.
Proof. esx. Qed.

Goal segRLs tm' (hLR++hLR') hLR' w0 w1.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR' w1 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR' [] [0;0] [].
Proof. esx. Qed.

Definition P1 len n x :=
  sideRLs tm' (hLR^^n++hLR') x (w1^^len*>0inf).

Definition P1' len n := P1 len n (w1^^len*>0inf).

Lemma P1_S len n:
  P1' len n ->
  P1' (1+len) (n+1+(n+1)).
Proof.
  unfold P1',P1.
  intros HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2:{
    eapply sideRLs_trans.
    - apply HP1.
    - apply HP1.
  }
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  - rewrite lpow_add.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
  - rewrite lpow_add,<-app_assoc.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
Qed.

Lemma P1'_n len:
  P1' len ((2^len-1)*2).
Proof.
  induction len.
  - unfold P1',P1; esx.
  - apply P1_S in IHlen.
    cbn.
    applys_eq IHlen; lia.
Qed.

Lemma P1_S0 len n x:
  P1 len n x ->
  P1 (1+len) (n+1) (w0*>x).
Proof.
  unfold P1',P1 in *.
  intros HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  rewrite lpow_add,<-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_S1 len n x:
  P1 len n x ->
  P1 (1+len) (n+1+((2^len-1)*2+1)) (w1*>x).
Proof.
  epose proof (P1'_n len) as HP1'.
  unfold P1',P1 in *.
  intros HP1.
  rewrite <-(lpow_add' _ 1).
  eapply segRLs_sideRLs_concat.
  2:{
    eapply sideRLs_trans.
    - apply HP1.
    - apply HP1'.
  }
  rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  - rewrite lpow_add.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
  - rewrite lpow_add,<-app_assoc.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    esx.
Qed.

Definition RC n := [0] *> [1]^^n *> 0inf.

Lemma RIncs n k:
  sideRLs tm (hRL^^n) (RC k) (RC (n+k)).
Proof.
  unfold RC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma ROv_0 l n:
  l {{{ (hR',R) }}} RC (0+n*5) -->*
  l <* w1 <* (w1<+w0)^^n {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_1 l n:
  l {{{ (hR',R) }}} RC (1+n*5) -->*
  l <* w1 <* (w1<+w0)^^n <* w1 {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_2 l n:
  l {{{ (hR',R) }}} RC (2+n*5) -->*
  l <* w1 <* (w1<+w0)^^n <* w0 {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_3 l n:
  l {{{ (hR',R) }}} RC (3+n*5) -->*
  l <* w1 <* (w1<+w0)^^n <* w1 <* w1 <* w1 {{{ (hR,R) }}} RC 0.
Proof.
  unfold RC.
  es.
Qed.

Lemma ROv_4 l n:
  halts tm (l {{{ (hR',R) }}} RC (4+n*5)).
Proof.
  unfold RC.
  esx.
Qed.

Definition S1 a b :=
  0inf <* w1^^a {{{ (hR',R) }}} RC b.

Lemma lcons_hRL_hRL' n:
  lcons hR (hLR^^n++hLR') = (hRL^^(n+1),hR').
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma app_not_nil_r {A} (a b:list A):
  b <> [] ->
  (a++b) <> [].
Proof.
  induction a; cbn; congruence.
Qed.

Lemma Incs len n x:
  P1 len n x ->
  x {{{ (hR,R) }}} RC 0 -->*
  0inf <* w1^^len {{{ (hR',R) }}} RC (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hRL_hRL' in I1.
  unshelve epose proof (I1 eq_refl _ HP1 (RIncs _ 0)) as I1.
  1: apply app_not_nil_r; congruence.
  rewrite Nat.add_0_r in I1.
  apply progress_evstep.
  apply I1.
Qed.

Local Opaque Nat.div Nat.modulo.

Lemma pow4_mod3 k:
  2^(k*2) mod 3 = 1%nat.
Proof.
  induction k; cbn; lia.
Qed.

Ltac rw_pa :=
  repeat rewrite Nat.pow_add_r by lia.

Lemma P1_01s len n x k:
  P1 len n x ->
  P1 (k*2+len) (2^len*(2^(k*2)/3)*2+n+k) ((w0++w1)^^k*>x).
Proof.
  gen len n x.
  induction k; intros.
  - cbn.
    applys_eq H; lia.
  - apply IHk in H.
    apply P1_S1 in H.
    apply P1_S0 in H.
    applys_eq H.
    pose proof (pow4_mod3 k).
    replace (2^(S k*2)/3) with (2^(k*2)/3*4+1) by (cbn; lia).
    rw_pa; lia.
Qed.

Lemma BigStep0 a b:
  S1 a (0+b*5) -->*
  S1 (b*2+a+1) ((2^(b*2)/3*4+4)*2^a+b-1).
Proof.
  unfold S1.
  follow ROv_0.
  follow Incs.
  - apply P1_01s,P1_S1,P1'_n.
  - rw_pa.
    finish.
Qed.

Lemma BigStep1 a b:
  S1 a (1+b*5) -->*
  S1 (b*2+a+2) ((2^(b*2)/3*16+8)*2^a+b-1).
Proof.
  unfold S1.
  follow ROv_1.
  follow Incs.
  - apply P1_S1,P1_01s,P1_S1,P1'_n.
  - rw_pa.
    pose proof (pow4_mod3 b).
    finish.
Qed.

Lemma BigStep2 a b:
  S1 a (2+b*5) -->*
  S1 (b*2+a+2) ((2^(b*2)/3*4+4)*2^a+b).
Proof.
  unfold S1.
  follow ROv_2.
  follow Incs.
  - apply P1_S0,P1_01s,P1_S1,P1'_n.
  - rw_pa.
    finish.
Qed.

Lemma BigStep3 a b:
  S1 a (3+b*5) -->*
  S1 (b*2+a+4) ((2^(b*2)/3*88+32)*2^a+b-1).
Proof.
  unfold S1.
  follow ROv_3.
  follow Incs.
  - apply P1_S1,P1_S1,P1_S1,P1_01s,P1_S1,P1'_n.
  - rw_pa.
    pose proof (pow4_mod3 b).
    finish.
Qed.

Lemma BigStep4 a b:
  halts tm (S1 a (4+b*5)).
Proof.
  intros.
  unfold S1.
  apply ROv_4.
Qed.

Lemma init:
  c0 -->* S1 6 33.
Proof.
  esx.
Qed.

Definition S' '(a,b) := S1 a b.

Close Scope sym.
Import PairIter.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep with (c':=S' (_,_)).
  2: apply init.
  eapply halts_if_simple with
    (C:=S')
    (f:=fun '(a,b0) =>
    let b:=b0/5 in
    match b0 mod 5 with
    | 0 => Some (b*2+a+1,(2^(b*2)/3*4+4)*2^a+b-1)
    | 1 => Some (b*2+a+2,(2^(b*2)/3*16+8)*2^a+b-1)
    | 2 => Some (b*2+a+2,(2^(b*2)/3*4+4)*2^a+b)
    | 3 => Some (b*2+a+4,(2^(b*2)/3*88+32)*2^a+b-1)
    | _ => None
    end).
  - intros [a b0].
    epose proof (div_mod' b0 5 (b0 mod 5) (eq_refl)) as I1.
    remember (b0/5) as b.
    unfold S'.
    destruct (b0 mod 5) as [|[|[|[|[|]]]]]; subst b0.
    + apply BigStep0. 
    + apply BigStep1. 
    + apply BigStep2. 
    + apply BigStep3. 
    + apply BigStep4. 
    + lia.
  - eapply pair_iter_halts_if with (g:=fun ls =>
    let a := Nvar 0 in
    let b0 := Nvar 1 in
    let b:=(b0/5)%Nexpr in
    match Nmod'' (2^30) b0 ls 5 with
    | None => Some ls
    | Some b1 =>
      (match b1 with
      | 0 => (cons2 (b*2+a+1,(2^(b*2)/3*4+4)*2^a+b-1) ls)
      | 1 => (cons2 (b*2+a+2,(2^(b*2)/3*16+8)*2^a+b-1) ls)
      | 2 => (cons2 (b*2+a+2,(2^(b*2)/3*4+4)*2^a+b) ls)
      | 3 => (cons2 (b*2+a+4,(2^(b*2)/3*88+32)*2^a+b-1) ls)
      | _ => None
      end)%Nexpr
    end).
    2:{
      apply iter_halts_c_spec with (T:=16).
      vm_compute; reflexivity.
    }
    solve_v1.
    destruct (z mod 5) as [|[|[|[|[|]]]]].
    6: lia.
    all: solve_v2.
Qed.

End TM3.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0LC_1LD0RF_1LE0LD_1RA0RB_1LE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (E,<[1;0]).
Notation hR := (A,[1]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].
Notation hLR' := [(hL,hR')].
Notation hLR := [(hL,hR)].
Notation w0 := <[1;0;1;0].
Notation w1 := <[1;1;0].
Notation wa := <[1;0;1;1;0;1;0].
Notation wb := <[1;0;0;1].

Definition tm' := flip tm.

Goal segRLs tm' hLR hLR w0 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR w1 w1.
Proof. esx. Qed.

Goal segRLs tm' hLR [] wb w1.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR' w1 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR' hLR' w0 wb.
Proof. esx. Qed.

Goal segRLs tm' hLR' hLR' wa (wb++w1).
Proof. esx. Qed.

Goal sideRLs tm' hLR' 0inf 0inf.
Proof. esx. Qed.

Goal segRLs tm hRL [] [0;0;0] [0;0;0; 1].
Proof. esx. Qed.

Definition P1 n x x' :=
  sideRLs tm' (hLR^^n++hLR') x x'.

Lemma P1_S0 n x x':
  P1 n x x' ->
  P1 n (w0*>x) (wb*>x').
Proof.
  unfold P1.
  intros HP1.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_S0s k n x x':
  P1 n x x' ->
  P1 n (w0^^k*>x) (wb^^k*>x').
Proof.
  intros HP1.
  induction k.
  - apply HP1.
  - apply P1_S0,IHk.
Qed.

Lemma P1_S1 n n' x x' x'':
  P1 n x x' ->
  P1 n' x' x'' ->
  P1 (n+1+n') (w1*>x) (wb*>x'').
Proof.
  unfold P1.
  intros HP1 HP1'.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  2: apply P1_S0,HP1'.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_Sb n n' x x' x'':
  P1 n x x' ->
  P1 n' x' x'' ->
  P1 (1+(n+1+n')) (wb*>x) (wb*>x'').
Proof.
  unfold P1.
  intros HP1 HP1'.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  2: eapply P1_S1; [apply HP1|apply HP1'].
  esx.
Qed.

Lemma P1_Sa n x x':
  P1 n x x' ->
  P1 n (wa*>x) (wb*>w1*>x').
Proof.
  unfold P1.
  intros HP1.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Definition P1' len n x := P1 n x (wb^^len*>0inf).

Lemma P1'_n len:
  P1' len ((2^len-1)*2) (wb^^len*>0inf).
Proof.
  unfold P1'.
  induction len.
  - unfold P1.
    esx.
  - cbn[lpow].
    rewrite Str_app_assoc.
    cbn[Nat.pow].
    applys_eq (P1_Sb _ _ _ _ _ IHlen IHlen); lia.
Qed.

Lemma P1'_Sb len n x:
  P1' len n x ->
  P1' (1+len) (2^len*2+n) (wb*>x).
Proof.
  unfold P1'.
  intros HP1'.
  applys_eq (P1_Sb _ _ _ _ _ HP1' (P1'_n _)); lia.
Qed.

Ltac rw_pa :=
  repeat rewrite Nat.pow_add_r by lia.

Lemma P1'_Sbs k len n x:
  P1' len n x ->
  P1' (k+len) ((2^k-1)*2^len*2+n) (wb^^k*>x).
Proof.
  intros HP1'.
  induction k.
  - apply HP1'.
  - cbn[Nat.pow].
    cbn[Nat.add].
    cbn[lpow].
    rewrite Str_app_assoc.
    apply P1'_Sb in IHk.
    replace (2*2^k-1) with (2^k+(2^k-1)) by lia.
    applys_eq IHk; rw_pa; lia.
Qed.

Lemma P1'_S1 len n x:
  P1' len n x ->
  P1' (1+len) (2^len*2+n-1) (w1*>x).
Proof.
  unfold P1'.
  intros HP1'.
  applys_eq (P1_S1 _ _ _ _ _ HP1' (P1'_n _)); lia.
Qed.

Definition RC n := [1;0;0;0;0] *> [1]^^n *> 0inf.
Definition RC0 n := [0;0;0] *> [1]^^n *> 0inf.

Lemma RIncs n k:
  sideRLs tm (hRL^^n) (RC k) (RC (n+k)).
Proof.
  unfold RC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs0 n k:
  sideRLs tm (hRL^^n) (RC0 k) (RC0 (n+k)).
Proof.
  unfold RC0.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Definition RC' n k :=
  [0;1;0] *> [1;0;0;1;0;1;0] *> [1;0;1;0]^^n *> [1]^^k *> 0inf.

Ltac flia := repeat (lia||f_equal).

Lemma ROv n k:
  sideRLs tm (hRL'++hRL^^n) (RC (3+n*3+k)) (RC' n k).
Proof.
  unfold RC,RC'.
  gen k.
  induction n; intros.
  - esx.
  - specialize (IHn (3+k)).
    replace (S n) with (n+1) by lia.
    rewrite lpow_add,app_assoc.
    eapply sideRLs_trans.
    1: applys_eq IHn; flia.
    esx.
Qed.

Lemma lcons_hR_hLR n:
  lcons hR (hLR^^n++hLR') = (hRL^^(n+1),hR').
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma lcons_hR'_hLR n:
  lcons hR' (hLR^^(1+n)) = (hRL'++hRL^^n,hR).
Proof.
  assert (lcons hR (hLR^^n) = (hRL^^n,hR)). {
    induction n; cbn; trivial.
    rewrite IHn; trivial.
  }
  cbn.
  rewrite H.
  trivial.
Qed.

Lemma Ov [len n x b b0]:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  exists x',
  x {{{ (hR',R) }}} RC (b0+b*3) -->*
  x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} [1]^^b0 *> 0inf /\
  P1' len (n-b) x'.
Proof.
  intros Hb Hn HP1'.
  unfold P1',P1 in HP1'.
  replace (b0+b*3) with (3+(b-1)*3+b0) by lia.
  replace n with (1+(b-1)+(n-b)) in HP1' by lia.
  rewrite lpow_add,<-app_assoc in HP1'.
  apply sideRLs_split in HP1'.
  destruct HP1' as [x' [I2 I3]].
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR'_hLR in I1.
  unshelve epose proof (I1 eq_refl _ I2 (ROv (b-1) b0)) as I1.
  1: cbn; congruence.
  exists x'; split.
  - follow100 I1.
    es.
  - apply I3.
Qed.

Lemma app_not_nil_r {A} (a b:list A):
  b <> [] ->
  (a++b) <> [].
Proof.
  induction a; cbn; congruence.
Qed.

Lemma Incs n x x':
  P1 n x x' ->
  x {{{ (hR,R) }}} RC 0 -->*
  x' {{{ (hR',R) }}} RC (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR_hLR in I1.
  epose proof (I1 eq_refl _ HP1 (RIncs _ _)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  apply app_not_nil_r; congruence.
Qed.

Lemma Incs0 n x x':
  P1 n x x' ->
  x {{{ (hR,R) }}} RC0 0 -->*
  x' {{{ (hR',R) }}} RC0 (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR_hLR in I1.
  epose proof (I1 eq_refl _ HP1 (RIncs0 _ _)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  apply app_not_nil_r; congruence.
Qed.

Lemma Ov2 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  x {{{ (hR',R) }}} RC (2+b*3) -->*
  0inf <* wb^^(b+len+3) {{{ (hR',R) }}} RC ((2^(b+2)+1)*(2^(len+1)) + (n-b) - 2).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) <* w1 {{{ (hR,R) }}} RC 0).
  1: es.
  follow Incs.
  - eapply P1_S1.
    + apply P1_S0s,P1_Sa,P1'_S1,I2.
    + rewrite (lpow_add' wb (b-1) 1).
      replace (b-1+1) with b by lia.
      apply P1'_Sbs,P1'_S1,P1'_n.
  - rewrite (lpow_add' wb 1).
    rw_pa.
    zify_pow2sub1.
    finish.
Qed.

Lemma Ov1 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  x {{{ (hR',R) }}} RC (1+b*3) -->*
  0inf <* wb^^(len+1) <* w1 <* wb^^b {{{ (hR',R) }}} RC (2^(len+1) + (n-b)).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} RC 0).
  1: es.
  follow Incs.
  - apply P1_S0s,P1_Sa,P1'_S1,I2.
  - rewrite (lpow_add' wb _ 1).
    rw_pa.
    finish.
Qed.

Lemma Ov0 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  halts tm (x {{{ (hR',R) }}} RC (0+b*3)).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  eapply halts_evstep.
  2:{
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} RC0 0).
  1: es.
  follow Incs0.
  - apply P1_S0s,P1_Sa,P1'_S1,I2.
  - finish.
  }
  replace (2^len*2+(n-b)-1+1) with (2+(2^len*2-2+(n-b))) by lia.
  esx.
Qed.

Definition S' (w:nat*nat*nat*side) :=
  let '(len,n,b,x):=w in
  x {{{ (hR',R) }}} RC b.

Definition P (w:nat*nat*nat*side) :=
  let '(len,n,b,x):=w in
  b>=3 /\
  n>=b/3 /\
  n<=2^len*2 /\
  len>=1 /\
  P1' len n x.

Lemma BigStep2 [len n b x]:
  let w:=(len,n,2+b*3,x) in
  let w':=(b+len+3,(2^(b+len+4)-2),((2^(b+2)+1)*(2^(len+1)) + (n-b) - 2),0inf<*wb^^(b+len+3)) in
  P w ->
  (S' w -->* S' w' /\ P w').
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  split.
  - apply Ov2; auto; lia.
  - repeat split.
    + rw_pa; lia.
    + rw_pa.
      zify_pow2sub1; lia.
    + rw_pa; lia.
    + lia.
    + applys_eq P1'_n; rw_pa; lia.
Qed.

Lemma BigStep1 [len n b x]:
  let w:=(len,n,1+b*3,x) in
  let w':=(b+len+2,2^(b+len+3)-3,((2^(len+1)) + (n-b)),0inf<*wb^^(len+1)<*w1<*wb^^b) in
  P w ->
  (S' w -->* S' w' /\ P w').
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  split.
  - apply Ov1; auto; lia.
  - repeat split.
    + replace len with (len-1+1) by lia.
      rw_pa; lia.
    + rw_pa; zify_pow2sub1; lia.
    + rw_pa; lia.
    + lia.
    + epose proof (P1'_n (len+1)) as I.
      apply P1'_S1 in I.
      apply (P1'_Sbs b) in I.
      applys_eq I.
      1: lia.
      rw_pa; zify_pow2sub1; lia.
Qed.

Lemma BigStep0 [len n b x]:
  let w:=(len,n,0+b*3,x) in
  P w ->
  halts tm (S' w).
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  apply (Ov0 len n); auto; lia.
Qed.

Lemma init:
  let w:=(7,254,1+51*3,0inf<*wb^^7)%nat in
  c0 -->* S' w /\ P w.
Proof.
  split.
  1: esx.
  repeat split.
  5: apply P1'_n.
  all: lia.
Qed.

Ltac R_mod :=
match goal with
| |- halts _ (S' (_,_,?b,_)) =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  epose proof init as [I1 P1].
  eapply halts_evstep.
  2: apply I1.
  epose proof (BigStep1 P1) as [I2 P2].
  eapply halts_evstep.
  2: apply I2.
  R_mod.
  apply (BigStep0 P2).
  Unshelve.
  all: lia.
Qed.

End TM6.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD0RF_1RF0LA_0RC---_1RA0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (C,<[1;0]).
Notation hR := (D,[1]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].
Notation hLR' := [(hL,hR')].
Notation hLR := [(hL,hR)].
Notation w0 := <[1;0;1;0].
Notation w1 := <[1;1;0].
Notation wa := <[1;0;1;1;0;1;0].
Notation wb := <[1;0;0;1].

Definition tm' := flip tm.

Goal segRLs tm' hLR hLR w0 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR w1 w1.
Proof. esx. Qed.

Goal segRLs tm' hLR [] wb w1.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR' w1 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR' hLR' w0 wb.
Proof. esx. Qed.

Goal segRLs tm' hLR' hLR' wa (wb++w1).
Proof. esx. Qed.

Goal sideRLs tm' hLR' 0inf 0inf.
Proof. esx. Qed.

Goal segRLs tm hRL [] [0;0;0] [0;0;0; 1].
Proof. esx. Qed.

Definition P1 n x x' :=
  sideRLs tm' (hLR^^n++hLR') x x'.

Lemma P1_S0 n x x':
  P1 n x x' ->
  P1 n (w0*>x) (wb*>x').
Proof.
  unfold P1.
  intros HP1.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_S0s k n x x':
  P1 n x x' ->
  P1 n (w0^^k*>x) (wb^^k*>x').
Proof.
  intros HP1.
  induction k.
  - apply HP1.
  - apply P1_S0,IHk.
Qed.

Lemma P1_S1 n n' x x' x'':
  P1 n x x' ->
  P1 n' x' x'' ->
  P1 (n+1+n') (w1*>x) (wb*>x'').
Proof.
  unfold P1.
  intros HP1 HP1'.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  2: apply P1_S0,HP1'.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_Sb n n' x x' x'':
  P1 n x x' ->
  P1 n' x' x'' ->
  P1 (1+(n+1+n')) (wb*>x) (wb*>x'').
Proof.
  unfold P1.
  intros HP1 HP1'.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  2: eapply P1_S1; [apply HP1|apply HP1'].
  esx.
Qed.

Lemma P1_Sa n x x':
  P1 n x x' ->
  P1 n (wa*>x) (wb*>w1*>x').
Proof.
  unfold P1.
  intros HP1.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Definition P1' len n x := P1 n x (wb^^len*>0inf).

Lemma P1'_n len:
  P1' len ((2^len-1)*2) (wb^^len*>0inf).
Proof.
  unfold P1'.
  induction len.
  - unfold P1.
    esx.
  - cbn[lpow].
    rewrite Str_app_assoc.
    cbn[Nat.pow].
    applys_eq (P1_Sb _ _ _ _ _ IHlen IHlen); lia.
Qed.

Lemma P1'_Sb len n x:
  P1' len n x ->
  P1' (1+len) (2^len*2+n) (wb*>x).
Proof.
  unfold P1'.
  intros HP1'.
  applys_eq (P1_Sb _ _ _ _ _ HP1' (P1'_n _)); lia.
Qed.

Ltac rw_pa :=
  repeat rewrite Nat.pow_add_r by lia.

Lemma P1'_Sbs k len n x:
  P1' len n x ->
  P1' (k+len) ((2^k-1)*2^len*2+n) (wb^^k*>x).
Proof.
  intros HP1'.
  induction k.
  - apply HP1'.
  - cbn[Nat.pow].
    cbn[Nat.add].
    cbn[lpow].
    rewrite Str_app_assoc.
    apply P1'_Sb in IHk.
    replace (2*2^k-1) with (2^k+(2^k-1)) by lia.
    applys_eq IHk; rw_pa; lia.
Qed.

Lemma P1'_S1 len n x:
  P1' len n x ->
  P1' (1+len) (2^len*2+n-1) (w1*>x).
Proof.
  unfold P1'.
  intros HP1'.
  applys_eq (P1_S1 _ _ _ _ _ HP1' (P1'_n _)); lia.
Qed.

Definition RC n := [1;0;0;0;0] *> [1]^^n *> 0inf.
Definition RC0 n := [0;0;0] *> [1]^^n *> 0inf.

Lemma RIncs n k:
  sideRLs tm (hRL^^n) (RC k) (RC (n+k)).
Proof.
  unfold RC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs0 n k:
  sideRLs tm (hRL^^n) (RC0 k) (RC0 (n+k)).
Proof.
  unfold RC0.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Definition RC' n k :=
  [0;1;0] *> [1;0;0;1;0;1;0] *> [1;0;1;0]^^n *> [1]^^k *> 0inf.

Ltac flia := repeat (lia||f_equal).

Lemma ROv n k:
  sideRLs tm (hRL'++hRL^^n) (RC (3+n*3+k)) (RC' n k).
Proof.
  unfold RC,RC'.
  gen k.
  induction n; intros.
  - esx.
  - specialize (IHn (3+k)).
    replace (S n) with (n+1) by lia.
    rewrite lpow_add,app_assoc.
    eapply sideRLs_trans.
    1: applys_eq IHn; flia.
    esx.
Qed.

Lemma lcons_hR_hLR n:
  lcons hR (hLR^^n++hLR') = (hRL^^(n+1),hR').
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma lcons_hR'_hLR n:
  lcons hR' (hLR^^(1+n)) = (hRL'++hRL^^n,hR).
Proof.
  assert (lcons hR (hLR^^n) = (hRL^^n,hR)). {
    induction n; cbn; trivial.
    rewrite IHn; trivial.
  }
  cbn.
  rewrite H.
  trivial.
Qed.

Lemma Ov [len n x b b0]:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  exists x',
  x {{{ (hR',R) }}} RC (b0+b*3) -->*
  x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} [1]^^b0 *> 0inf /\
  P1' len (n-b) x'.
Proof.
  intros Hb Hn HP1'.
  unfold P1',P1 in HP1'.
  replace (b0+b*3) with (3+(b-1)*3+b0) by lia.
  replace n with (1+(b-1)+(n-b)) in HP1' by lia.
  rewrite lpow_add,<-app_assoc in HP1'.
  apply sideRLs_split in HP1'.
  destruct HP1' as [x' [I2 I3]].
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR'_hLR in I1.
  unshelve epose proof (I1 eq_refl _ I2 (ROv (b-1) b0)) as I1.
  1: cbn; congruence.
  exists x'; split.
  - follow100 I1.
    es.
  - apply I3.
Qed.

Lemma app_not_nil_r {A} (a b:list A):
  b <> [] ->
  (a++b) <> [].
Proof.
  induction a; cbn; congruence.
Qed.

Lemma Incs n x x':
  P1 n x x' ->
  x {{{ (hR,R) }}} RC 0 -->*
  x' {{{ (hR',R) }}} RC (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR_hLR in I1.
  epose proof (I1 eq_refl _ HP1 (RIncs _ _)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  apply app_not_nil_r; congruence.
Qed.

Lemma Incs0 n x x':
  P1 n x x' ->
  x {{{ (hR,R) }}} RC0 0 -->*
  x' {{{ (hR',R) }}} RC0 (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR_hLR in I1.
  epose proof (I1 eq_refl _ HP1 (RIncs0 _ _)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  apply app_not_nil_r; congruence.
Qed.

Lemma Ov2 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  x {{{ (hR',R) }}} RC (2+b*3) -->*
  0inf <* wb^^(b+len+3) {{{ (hR',R) }}} RC ((2^(b+2)+1)*(2^(len+1)) + (n-b) - 2).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) <* w1 {{{ (hR,R) }}} RC 0).
  1: es.
  follow Incs.
  - eapply P1_S1.
    + apply P1_S0s,P1_Sa,P1'_S1,I2.
    + rewrite (lpow_add' wb (b-1) 1).
      replace (b-1+1) with b by lia.
      apply P1'_Sbs,P1'_S1,P1'_n.
  - rewrite (lpow_add' wb 1).
    rw_pa.
    zify_pow2sub1.
    finish.
Qed.

Lemma Ov1 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  x {{{ (hR',R) }}} RC (1+b*3) -->*
  0inf <* wb^^(len+1) <* w1 <* wb^^b {{{ (hR',R) }}} RC (2^(len+1) + (n-b)).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} RC 0).
  1: es.
  follow Incs.
  - apply P1_S0s,P1_Sa,P1'_S1,I2.
  - rewrite (lpow_add' wb _ 1).
    rw_pa.
    finish.
Qed.

Lemma Ov0 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  halts tm (x {{{ (hR',R) }}} RC (0+b*3)).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  eapply halts_evstep.
  2:{
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} RC0 0).
  1: es.
  follow Incs0.
  - apply P1_S0s,P1_Sa,P1'_S1,I2.
  - finish.
  }
  replace (2^len*2+(n-b)-1+1) with (2+(2^len*2-2+(n-b))) by lia.
  esx.
Qed.

Definition S' (w:nat*nat*nat*side) :=
  let '(len,n,b,x):=w in
  x {{{ (hR',R) }}} RC b.

Definition P (w:nat*nat*nat*side) :=
  let '(len,n,b,x):=w in
  b>=3 /\
  n>=b/3 /\
  n<=2^len*2 /\
  len>=1 /\
  P1' len n x.

Lemma BigStep2 [len n b x]:
  let w:=(len,n,2+b*3,x) in
  let w':=(b+len+3,(2^(b+len+4)-2),((2^(b+2)+1)*(2^(len+1)) + (n-b) - 2),0inf<*wb^^(b+len+3)) in
  P w ->
  (S' w -->* S' w' /\ P w').
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  split.
  - apply Ov2; auto; lia.
  - repeat split.
    + rw_pa; lia.
    + rw_pa.
      zify_pow2sub1; lia.
    + rw_pa; lia.
    + lia.
    + applys_eq P1'_n; rw_pa; lia.
Qed.

Lemma BigStep1 [len n b x]:
  let w:=(len,n,1+b*3,x) in
  let w':=(b+len+2,2^(b+len+3)-3,((2^(len+1)) + (n-b)),0inf<*wb^^(len+1)<*w1<*wb^^b) in
  P w ->
  (S' w -->* S' w' /\ P w').
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  split.
  - apply Ov1; auto; lia.
  - repeat split.
    + replace len with (len-1+1) by lia.
      rw_pa; lia.
    + rw_pa; zify_pow2sub1; lia.
    + rw_pa; lia.
    + lia.
    + epose proof (P1'_n (len+1)) as I.
      apply P1'_S1 in I.
      apply (P1'_Sbs b) in I.
      applys_eq I.
      1: lia.
      rw_pa; zify_pow2sub1; lia.
Qed.

Lemma BigStep0 [len n b x]:
  let w:=(len,n,0+b*3,x) in
  P w ->
  halts tm (S' w).
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  apply (Ov0 len n); auto; lia.
Qed.

Lemma init:
  let w:=(7,252,2+4*3,0inf<*wb^^3<*w1<*wb^^2<*w1)%nat in
  c0 -->* S' w /\ P w.
Proof.
  split.
  1: esx.
  repeat split.
  5: {
    epose proof (P1'_n 3) as I.
    apply P1'_S1,(P1'_Sbs 2),P1'_S1 in I.
    apply I.
  }
  all: lia.
Qed.

Close Scope sym.

Import NatMod_v3.

Notation "a [ b ]" := (Neval (Nevals a) b) : Nexpr_scope.

Inductive P': (list Nexpr)->Prop :=
| P'_intro x ls:
  (c0 -->* S' (ls[Nvar 0],ls[Nvar 1],ls[Nvar 2],x) ->
  P (ls[Nvar 0],ls[Nvar 1],ls[Nvar 2],x) ->
  Nexprs_WF ls ->
  P' ls)%Nexpr.

Definition max_lb := (2^60)%N.

Lemma P'_S0 ls:
  (P' ls ->
  let b0:=Nvar 2 in
  Nmod'' max_lb b0 ls 3 = Some 0 ->
  halts tm c0)%Nexpr.
Proof.
  cbn.
  intros HP' Hmod.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite Hmod in I1.
  clear Hmod.
  inverts HP'.
  unshelve epose proof (I1 _) as I1.
  1: econstructor; [econstructor|assumption].
  replace (ls[Nvar 2])%Nexpr with (0+(ls[Nvar 2])%Nexpr/3*3) in H,H0 by lia.
  eapply halts_evstep.
  1: apply (BigStep0 H0).
  apply H.
Qed.

Lemma P'_S1 ls:
  (P' ls ->
  let len:=Nvar 0 in
  let n:=Nvar 1 in
  let b0:=Nvar 2 in
  Nmod'' max_lb b0 ls 3 = Some 1 ->
  let b:=b0/3 in
  P' (cons3 (b+len+2,2^(b+len+3)-3,((2^(len+1)) + (Nsub' n b))) ls))%Nexpr.
Proof.
  cbn.
  intros HP' Hmod.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite Hmod in I1.
  clear Hmod.
  inverts HP'.
  unshelve epose proof (I1 _) as I1.
  1: econstructor; [econstructor|assumption].
  replace (ls[Nvar 2])%Nexpr with (1+(ls[Nvar 2])%Nexpr/3*3) in H,H0 by lia.
  epose proof (BigStep1 H0) as [I2 I3].
  econstructor.
  - follow H.
    apply I2.
  - apply I3.
  - repeat constructor; try assumption.
    unfold P in H0.
    cbn[Neval] in *.
    lia.
Qed.

Lemma P'_S2 ls:
  (P' ls ->
  let len:=Nvar 0 in
  let n:=Nvar 1 in
  let b0:=Nvar 2 in
  Nmod'' max_lb b0 ls 3 = Some 2 ->
  let b:=b0/3 in
  P' (cons3 (b+len+3,2^(b+len+4)-2,(2^(b+2)+1)*(2^(len+1)) + (Nsub' n b) - 2) ls))%Nexpr.
Proof.
  cbn.
  intros HP' Hmod.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite Hmod in I1.
  clear Hmod.
  inverts HP'.
  unshelve epose proof (I1 _) as I1.
  1: econstructor; [econstructor|assumption].
  replace (ls[Nvar 2])%Nexpr with (2+(ls[Nvar 2])%Nexpr/3*3) in H,H0 by lia.
  epose proof (BigStep2 H0) as [I2 I3].
  econstructor.
  - follow H.
    apply I2.
  - apply I3.
  - repeat constructor; try assumption.
    unfold P in H0.
    cbn[Neval] in *.
    lia.
Qed.

Lemma P'_0:
  P' (cons3 (Nconst 7,Nconst 252,Nconst 14) nil).
Proof.
  epose proof init as [I2 I3].
  econstructor.
  - apply I2.
  - apply I3.
  - repeat constructor.
Qed.

Lemma halt: halts tm c0.
Proof.
  epose proof P'_0 as HP'.
  repeat (
  (apply P'_S2 in HP'; [|vm_compute; reflexivity]) ||
  (apply P'_S1 in HP'; [|vm_compute; reflexivity]) ||
  (apply P'_S0 in HP'; [|vm_compute; reflexivity]) ).
  apply HP'.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RD_1RD0RB_1RE0LE_1LA1RF_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (B,<[1;0]).
Notation hR := (C,[1]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].
Notation hLR' := [(hL,hR')].
Notation hLR := [(hL,hR)].
Notation w0 := <[1;0;1;0].
Notation w1 := <[1;1;0].
Notation wa := <[1;0;1;1;0;1;0].
Notation wb := <[1;0;0;1].

Definition tm' := flip tm.

Goal segRLs tm' hLR hLR w0 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR w1 w1.
Proof. esx. Qed.

Goal segRLs tm' hLR [] wb w1.
Proof. esx. Qed.

Goal segRLs tm' hLR hLR' w1 w0.
Proof. esx. Qed.

Goal segRLs tm' hLR' hLR' w0 wb.
Proof. esx. Qed.

Goal segRLs tm' hLR' hLR' wa (wb++w1).
Proof. esx. Qed.

Goal sideRLs tm' hLR' 0inf 0inf.
Proof. esx. Qed.

Goal segRLs tm hRL [] [0;0;0] [0;0;0; 1].
Proof. esx. Qed.

Definition P1 n x x' :=
  sideRLs tm' (hLR^^n++hLR') x x'.

Lemma P1_S0 n x x':
  P1 n x x' ->
  P1 n (w0*>x) (wb*>x').
Proof.
  unfold P1.
  intros HP1.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_S0s k n x x':
  P1 n x x' ->
  P1 n (w0^^k*>x) (wb^^k*>x').
Proof.
  intros HP1.
  induction k.
  - apply HP1.
  - apply P1_S0,IHk.
Qed.

Lemma P1_S1 n n' x x' x'':
  P1 n x x' ->
  P1 n' x' x'' ->
  P1 (n+1+n') (w1*>x) (wb*>x'').
Proof.
  unfold P1.
  intros HP1 HP1'.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  2: apply P1_S0,HP1'.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma P1_Sb n n' x x' x'':
  P1 n x x' ->
  P1 n' x' x'' ->
  P1 (1+(n+1+n')) (wb*>x) (wb*>x'').
Proof.
  unfold P1.
  intros HP1 HP1'.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  2: eapply P1_S1; [apply HP1|apply HP1'].
  esx.
Qed.

Lemma P1_Sa n x x':
  P1 n x x' ->
  P1 n (wa*>x) (wb*>w1*>x').
Proof.
  unfold P1.
  intros HP1.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply HP1.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  esx.
Qed.

Definition P1' len n x := P1 n x (wb^^len*>0inf).

Lemma P1'_n len:
  P1' len ((2^len-1)*2) (wb^^len*>0inf).
Proof.
  unfold P1'.
  induction len.
  - unfold P1.
    esx.
  - cbn[lpow].
    rewrite Str_app_assoc.
    cbn[Nat.pow].
    applys_eq (P1_Sb _ _ _ _ _ IHlen IHlen); lia.
Qed.

Lemma P1'_Sb len n x:
  P1' len n x ->
  P1' (1+len) (2^len*2+n) (wb*>x).
Proof.
  unfold P1'.
  intros HP1'.
  applys_eq (P1_Sb _ _ _ _ _ HP1' (P1'_n _)); lia.
Qed.

Ltac rw_pa :=
  repeat rewrite Nat.pow_add_r by lia.

Lemma P1'_Sbs k len n x:
  P1' len n x ->
  P1' (k+len) ((2^k-1)*2^len*2+n) (wb^^k*>x).
Proof.
  intros HP1'.
  induction k.
  - apply HP1'.
  - cbn[Nat.pow].
    cbn[Nat.add].
    cbn[lpow].
    rewrite Str_app_assoc.
    apply P1'_Sb in IHk.
    replace (2*2^k-1) with (2^k+(2^k-1)) by lia.
    applys_eq IHk; rw_pa; lia.
Qed.

Lemma P1'_S1 len n x:
  P1' len n x ->
  P1' (1+len) (2^len*2+n-1) (w1*>x).
Proof.
  unfold P1'.
  intros HP1'.
  applys_eq (P1_S1 _ _ _ _ _ HP1' (P1'_n _)); lia.
Qed.

Definition RC n := [1;0;0;0;0] *> [1]^^n *> 0inf.
Definition RC0 n := [0;0;0] *> [1]^^n *> 0inf.

Lemma RIncs n k:
  sideRLs tm (hRL^^n) (RC k) (RC (n+k)).
Proof.
  unfold RC.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Lemma RIncs0 n k:
  sideRLs tm (hRL^^n) (RC0 k) (RC0 (n+k)).
Proof.
  unfold RC0.
  induction n.
  1: esx.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  esx.
Qed.

Definition RC' n k :=
  [0;1;0] *> [1;0;0;1;0;1;0] *> [1;0;1;0]^^n *> [1]^^k *> 0inf.

Ltac flia := repeat (lia||f_equal).

Lemma ROv n k:
  sideRLs tm (hRL'++hRL^^n) (RC (3+n*3+k)) (RC' n k).
Proof.
  unfold RC,RC'.
  gen k.
  induction n; intros.
  - esx.
  - specialize (IHn (3+k)).
    replace (S n) with (n+1) by lia.
    rewrite lpow_add,app_assoc.
    eapply sideRLs_trans.
    1: applys_eq IHn; flia.
    esx.
Qed.

Lemma lcons_hR_hLR n:
  lcons hR (hLR^^n++hLR') = (hRL^^(n+1),hR').
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma lcons_hR'_hLR n:
  lcons hR' (hLR^^(1+n)) = (hRL'++hRL^^n,hR).
Proof.
  assert (lcons hR (hLR^^n) = (hRL^^n,hR)). {
    induction n; cbn; trivial.
    rewrite IHn; trivial.
  }
  cbn.
  rewrite H.
  trivial.
Qed.

Lemma Ov [len n x b b0]:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  exists x',
  x {{{ (hR',R) }}} RC (b0+b*3) -->*
  x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} [1]^^b0 *> 0inf /\
  P1' len (n-b) x'.
Proof.
  intros Hb Hn HP1'.
  unfold P1',P1 in HP1'.
  replace (b0+b*3) with (3+(b-1)*3+b0) by lia.
  replace n with (1+(b-1)+(n-b)) in HP1' by lia.
  rewrite lpow_add,<-app_assoc in HP1'.
  apply sideRLs_split in HP1'.
  destruct HP1' as [x' [I2 I3]].
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR'_hLR in I1.
  unshelve epose proof (I1 eq_refl _ I2 (ROv (b-1) b0)) as I1.
  1: cbn; congruence.
  exists x'; split.
  - follow100 I1.
    es.
  - apply I3.
Qed.

Lemma app_not_nil_r {A} (a b:list A):
  b <> [] ->
  (a++b) <> [].
Proof.
  induction a; cbn; congruence.
Qed.

Lemma Incs n x x':
  P1 n x x' ->
  x {{{ (hR,R) }}} RC 0 -->*
  x' {{{ (hR',R) }}} RC (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR_hLR in I1.
  epose proof (I1 eq_refl _ HP1 (RIncs _ _)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  apply app_not_nil_r; congruence.
Qed.

Lemma Incs0 n x x':
  P1 n x x' ->
  x {{{ (hR,R) }}} RC0 0 -->*
  x' {{{ (hR',R) }}} RC0 (n+1).
Proof.
  unfold P1.
  intros HP1.
  epose proof (sideRLs_concat_v2) as I1.
  erewrite lcons_hR_hLR in I1.
  epose proof (I1 eq_refl _ HP1 (RIncs0 _ _)) as I1.
  follow100 I1.
  finish.
  Unshelve.
  apply app_not_nil_r; congruence.
Qed.

Lemma Ov2 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  x {{{ (hR',R) }}} RC (2+b*3) -->*
  0inf <* wb^^(b+len+3) {{{ (hR',R) }}} RC ((2^(b+2)+1)*(2^(len+1)) + (n-b) - 2).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) <* w1 {{{ (hR,R) }}} RC 0).
  1: es.
  follow Incs.
  - eapply P1_S1.
    + apply P1_S0s,P1_Sa,P1'_S1,I2.
    + rewrite (lpow_add' wb (b-1) 1).
      replace (b-1+1) with b by lia.
      apply P1'_Sbs,P1'_S1,P1'_n.
  - rewrite (lpow_add' wb 1).
    rw_pa.
    zify_pow2sub1.
    finish.
Qed.

Lemma Ov1 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  x {{{ (hR',R) }}} RC (1+b*3) -->*
  0inf <* wb^^(len+1) <* w1 <* wb^^b {{{ (hR',R) }}} RC (2^(len+1) + (n-b)).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} RC 0).
  1: es.
  follow Incs.
  - apply P1_S0s,P1_Sa,P1'_S1,I2.
  - rewrite (lpow_add' wb _ 1).
    rw_pa.
    finish.
Qed.

Lemma Ov0 len n x b:
  b>=1 ->
  n>=b ->
  P1' len n x ->
  halts tm (x {{{ (hR',R) }}} RC (0+b*3)).
Proof.
  intros Hb Hn HP1'.
  epose proof (Ov Hb Hn HP1') as [x' [I1 I2]].
  eapply halts_evstep.
  2:{
  follow I1.
  mid (x' <* w1 <* wa <* w0^^(b-1) {{{ (hR,R) }}} RC0 0).
  1: es.
  follow Incs0.
  - apply P1_S0s,P1_Sa,P1'_S1,I2.
  - finish.
  }
  replace (2^len*2+(n-b)-1+1) with (2+(2^len*2-2+(n-b))) by lia.
  esx.
Qed.

Definition S' (w:nat*nat*nat*side) :=
  let '(len,n,b,x):=w in
  x {{{ (hR',R) }}} RC b.

Definition P (w:nat*nat*nat*side) :=
  let '(len,n,b,x):=w in
  b>=3 /\
  n>=b/3 /\
  n<=2^len*2 /\
  len>=1 /\
  P1' len n x.

Lemma BigStep2 [len n b x]:
  let w:=(len,n,2+b*3,x) in
  let w':=(b+len+3,(2^(b+len+4)-2),((2^(b+2)+1)*(2^(len+1)) + (n-b) - 2),0inf<*wb^^(b+len+3)) in
  P w ->
  (S' w -->* S' w' /\ P w').
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  split.
  - apply Ov2; auto; lia.
  - repeat split.
    + rw_pa; lia.
    + rw_pa.
      zify_pow2sub1; lia.
    + rw_pa; lia.
    + lia.
    + applys_eq P1'_n; rw_pa; lia.
Qed.

Lemma BigStep1 [len n b x]:
  let w:=(len,n,1+b*3,x) in
  let w':=(b+len+2,2^(b+len+3)-3,((2^(len+1)) + (n-b)),0inf<*wb^^(len+1)<*w1<*wb^^b) in
  P w ->
  (S' w -->* S' w' /\ P w').
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  split.
  - apply Ov1; auto; lia.
  - repeat split.
    + replace len with (len-1+1) by lia.
      rw_pa; lia.
    + rw_pa; zify_pow2sub1; lia.
    + rw_pa; lia.
    + lia.
    + epose proof (P1'_n (len+1)) as I.
      apply P1'_S1 in I.
      apply (P1'_Sbs b) in I.
      applys_eq I.
      1: lia.
      rw_pa; zify_pow2sub1; lia.
Qed.

Lemma BigStep0 [len n b x]:
  let w:=(len,n,0+b*3,x) in
  P w ->
  halts tm (S' w).
Proof.
  unfold P,S'.
  intros [I1 [I2 [I3 [I4 I5]]]].
  apply (Ov0 len n); auto; lia.
Qed.

Lemma init:
  let w:=(12,2^13-3,2+(2^10+178)*3,0inf<*wb^^11<*w1)%nat in
  c0 -->* S' w /\ P w.
Proof.
  split.
  1: stepn' 489942%N.
  repeat split.
  5: {
    epose proof (P1'_n 11) as I1.
    apply P1'_S1 in I1.
    apply I1.
  }
  all: lia.
Qed.

Close Scope sym.

Import NatMod_v3.

Notation "a [ b ]" := (Neval (Nevals a) b) : Nexpr_scope.

Inductive P': (list Nexpr)->Prop :=
| P'_intro x ls:
  (c0 -->* S' (ls[Nvar 0],ls[Nvar 1],ls[Nvar 2],x) ->
  P (ls[Nvar 0],ls[Nvar 1],ls[Nvar 2],x) ->
  Nexprs_WF ls ->
  P' ls)%Nexpr.

Definition max_lb := (2^60)%N.

Lemma P'_S0 ls:
  (P' ls ->
  let b0:=Nvar 2 in
  Nmod'' max_lb b0 ls 3 = Some 0 ->
  halts tm c0)%Nexpr.
Proof.
  cbn.
  intros HP' Hmod.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite Hmod in I1.
  clear Hmod.
  inverts HP'.
  unshelve epose proof (I1 _) as I1.
  1: econstructor; [econstructor|assumption].
  replace (ls[Nvar 2])%Nexpr with (0+(ls[Nvar 2])%Nexpr/3*3) in H,H0 by lia.
  eapply halts_evstep.
  1: apply (BigStep0 H0).
  apply H.
Qed.

Lemma P'_S1 ls:
  (P' ls ->
  let len:=Nvar 0 in
  let n:=Nvar 1 in
  let b0:=Nvar 2 in
  Nmod'' max_lb b0 ls 3 = Some 1 ->
  let b:=b0/3 in
  P' (cons3 (b+len+2,2^(b+len+3)-3,((2^(len+1)) + (Nsub' n b))) ls))%Nexpr.
Proof.
  cbn.
  intros HP' Hmod.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite Hmod in I1.
  clear Hmod.
  inverts HP'.
  unshelve epose proof (I1 _) as I1.
  1: econstructor; [econstructor|assumption].
  replace (ls[Nvar 2])%Nexpr with (1+(ls[Nvar 2])%Nexpr/3*3) in H,H0 by lia.
  epose proof (BigStep1 H0) as [I2 I3].
  econstructor.
  - follow H.
    apply I2.
  - apply I3.
  - repeat constructor; try assumption.
    unfold P in H0.
    cbn[Neval] in *.
    lia.
Qed.

Lemma P'_S2 ls:
  (P' ls ->
  let len:=Nvar 0 in
  let n:=Nvar 1 in
  let b0:=Nvar 2 in
  Nmod'' max_lb b0 ls 3 = Some 2 ->
  let b:=b0/3 in
  P' (cons3 (b+len+3,2^(b+len+4)-2,(2^(b+2)+1)*(2^(len+1)) + (Nsub' n b) - 2) ls))%Nexpr.
Proof.
  cbn.
  intros HP' Hmod.
  epose proof (Nmod''_spec _ _ _ _) as I1.
  rewrite Hmod in I1.
  clear Hmod.
  inverts HP'.
  unshelve epose proof (I1 _) as I1.
  1: econstructor; [econstructor|assumption].
  replace (ls[Nvar 2])%Nexpr with (2+(ls[Nvar 2])%Nexpr/3*3) in H,H0 by lia.
  epose proof (BigStep2 H0) as [I2 I3].
  econstructor.
  - follow H.
    apply I2.
  - apply I3.
  - repeat constructor; try assumption.
    unfold P in H0.
    cbn[Neval] in *.
    lia.
Qed.

Lemma P'_0:
  P' (cons3 (Nconst 12,Nconst (2^13-3),Nconst 3608) nil).
Proof.
  epose proof init as [I2 I3].
  econstructor.
  - apply I2.
  - apply I3.
  - repeat constructor.
Qed.

Lemma halt: halts tm c0.
Proof.
  epose proof P'_0 as HP'.
  repeat (
  (apply P'_S2 in HP'; [|vm_compute; reflexivity]) ||
  (apply P'_S1 in HP'; [|vm_compute; reflexivity]) ||
  (apply P'_S0 in HP'; [|vm_compute; reflexivity]) ).
  apply HP'.
Qed.

End TM5.


