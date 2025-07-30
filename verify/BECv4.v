From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LC_1LC1LC_1RD1LA_0LE0RD_1RC1LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{D}}> r) (at level 30).

Definition LC0 n := BinInc <[0;1;0] n <* [0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;1;0] m).
Definition R n m := [1;0]^^(n) *> [0] *> [1;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[]) (qR:=[]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LIncsOv1 len m n0 m0:
  LC1 len 0 m <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 (m/2) <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  assert (m=m/2*2+m mod 2) by lia.
  remember (m/2) as m1.
  remember (m mod 2) as m2.
  rewrite H.
  destruct m2 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    follow LOv1_0.
    follow RInc.
    epose proof (Incs1 _ _ _ _ _) as I1.
    follow I1.
    1: cbn; lia.
    finish.
  - follow LOv1_1.
    follow RInc.
    epose proof (Incs1 _ _ _ _ _) as I1.
    follow I1.
    1: cbn; lia.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 (2^len) |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  es.
Qed.

Lemma ROv n m:
  LC0 (n) |> R 0 m -->+
  LC1 0 0 (n) <| R m 1.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  es.
Qed.

Lemma LIncsOv1s len m n0 m0:
  LC1 0 0 m <| R (2^len-1+n0) m0 -->*
  LC1 (len) 0 (m/2^len) <| R n0 (2^len-1+m0).
Proof.
  gen m n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len-1+n0) with (2^len-1+(2^len+n0)) by (cbn; lia).
  follow IHlen.
  follow LIncsOv1.
  replace (2^S len) with (2^len*2) by (cbn; lia).
  rewrite Nat.Div0.div_div.
  finish.
Qed.

Close Scope sym.

Definition S0 a :=
  LC1 0 0 a <| R a 1.

Lemma BigStep len m:
  2^len<=m<2^len*2 ->
  S0 (m) -->+
  S0 (1+m).
Proof.
  unfold S0.
  intros.
  replace (R m 1) with (R (2^len-1+(1+(m-2^len))) 1) by (f_equal; lia).
  follow LIncsOv1s.
  assert (m/2^len*2^len+(m mod 2^len)=m) by lia.
  remember (m/2^len) as v1.
  assert (v1=1) by (destruct v1 as [|[|v1]]; lia).
  rewrite H1.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  follow LInc0.
  follow10 ROv.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 1).
  1: unfold S0; esx.
  eapply progress_nonhalt_cond with (P:=fun x => exists i, 2^i<=x<2^i*2).
  2: exists 0; lia.
  intros a [i Hi].
  eexists; split.
  1: apply (BigStep _ _ Hi).
  assert (2^i<=1+a<2^i*2 \/ 1+a=2^i*2) as [E|E] by lia.
  - exists i; lia.
  - exists (1+i); cbn; lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1LE_0LC1RA_0LD1LC_1LA0LF_1LD0RB_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{A}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [0] *> [1;1;0]^^(n) *> [0] *> [1;1;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1]) (qR:=[1]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (1+m) -->+
  LC1 1 0 (1+n) <| R m 2.
Proof.
  mid10 (LC0 n <| [1] *> R (2+m) 0).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  mid (BinInc [1;0;0] n0 <*<[1;0;0;1;1]<*<[0;1;1]^^m<{{D}} [0;1;1;0;1;1]*>0inf).
  1: es.
  sr; er.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R m 2.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 (1+(1+m)) -->+
  LC1 1 0 n <| R m 3.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Definition S1 x := S0 (x*2+1) (x*4+7).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  mid01 (S0 (x*2+1) (1+(x*2+1+(x*2+5)))).
  1: finish.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  mid (LC0 ((x+3)*2) |> R 0 (1+(1+(x*4+6)))).
  1: finish.
  follow100 ROv_0'.
  mid (LC1 1 0 (x+2+1) <| R ((x+2)*2+1+(x*2+1)) 3).
  1: finish.
  follow LOvIncss''.
  follow LInc0.
  mid (LC0 ((x+1)*2) |> R 0 (1+(1+(((x)*2+1+(x*2+6)))))).
  1: finish.
  follow100 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  mid (LC0 ((x+3)*2+1) |> R 0 (1+(x*4+9))).
  1: finish.
  follow100 ROv_1.
  mid (LC1 1 0 ((x+3)+1) <| R ((x+3)*2+1+(x*2+2)) 2).
  1: finish.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LE_0LD1RB_0LA1LD_1LA0RC_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{B}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [0] *> [1;1;0]^^(n) *> [0] *> [1;1;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1]) (qR:=[1]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (1+m) -->+
  LC1 1 0 (1+n) <| R m 2.
Proof.
  mid10 (LC0 n <| [1] *> R (2+m) 0).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  mid (BinInc [1;0;0] n0 <*<[1;0;0;1;1]<*<[0;1;1]^^m<{{A}} [0;1;1;0;1;1]*>0inf).
  1: es.
  sr; er.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R m 2.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 (1+(1+m)) -->+
  LC1 1 0 n <| R m 3.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Definition S1 x := S0 (x*2+5) (x*4+7).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  mid01 (S0 ((x+2)*2+1) (1+((x+2)*2+1+(x*2+1)))).
  1: finish.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  mid (LC0 ((x+1)*2) |> R 0 (1+(1+(x*4+6)))).
  1: finish.
  follow100 ROv_0'.
  mid (LC1 1 0 (x+1) <| R (x*2+1+(x*2+5)) 3).
  1: finish.
  follow LOvIncss''.
  follow LInc0.
  mid (LC0 ((x+2+1)*2) |> R 0 (1+(1+(((x+2)*2+1+(x*2+2)))))).
  1: finish.
  follow100 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  mid (LC0 ((x+1)*2+1) |> R 0 (1+(x*4+9))).
  1: finish.
  follow100 ROv_1.
  mid (LC1 1 0 ((x+1)+1) <| R ((x+1)*2+1+(x*2+6)) 2).
  1: finish.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC1LD_1RD1LC_1LA0RE_0LA1RB_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{B}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [1;0;0] *> [1;1;1;0;0]^^(n) *> [1;0;0] *> [1;1;1;0;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1;1]) (qR:=[1;0]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (m) -->+
  LC1 1 0 (1+n) <| R (m) 1.
Proof.
  mid10 (LC0 n <| [1;1;0;0] *> [1;1;1;0;0]^^(1+m) *> 0inf).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R (1+m) 1.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 ((1+m)) -->+
  LC1 1 0 n <| R m 2.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Lemma BigStep0 n m:
  S0 ((n+1)*2) (1+(n*2+1+m)) -->+
  S0 (m+1) (n*2+m+3).
Proof.
  unfold S0.
  follow10 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Lemma BigStep1 n m:
  S0 ((n+1)*2+1) (((n+1)*2+1+m)) -->+
  S0 (m+1) (n*2+m+4).
Proof.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Definition S1 x := S0 (x*2+6) (x*4+8).

Ltac follow' H :=
  (eapply evstep_progress_trans || eapply evstep_trans); [|follow100 H || follow10 H || follow H]; [finish|].

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  follow' (BigStep0 (x+2) (x*2+2)).
  follow' (BigStep1 x (x*2+6)).
  follow' (BigStep1 (x+2) (x*2+3)).
  follow' (BigStep0 (x+1) (x*2+7)).
  finish.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RF_1LE0LD_0LB---_0RA1LB_0LC1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [1;0;0] *> [1;1;1;0;0]^^(n) *> [1;0;0] *> [1;1;1;0;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1;1]) (qR:=[1;0]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (m) -->+
  LC1 1 0 (1+n) <| R (m) 1.
Proof.
  mid10 (LC0 n <| [1;1;0;0] *> [1;1;1;0;0]^^(1+m) *> 0inf).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R (1+m) 1.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 ((1+m)) -->+
  LC1 1 0 n <| R m 2.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Lemma BigStep0 n m:
  S0 ((n+1)*2) (1+(n*2+1+m)) -->+
  S0 (m+1) (n*2+m+3).
Proof.
  unfold S0.
  follow10 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Lemma BigStep1 n m:
  S0 ((n+1)*2+1) (((n+1)*2+1+m)) -->+
  S0 (m+1) (n*2+m+4).
Proof.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Definition S1 x := S0 (x*2+7) (x*4+9).

Ltac follow' H :=
  (eapply evstep_progress_trans || eapply evstep_trans); [|follow100 H || follow10 H || follow H]; [finish|].

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  follow' (BigStep1 (x+2) (x*2+2)).
  follow' (BigStep1 x (x*2+7)).
  follow' (BigStep0 (x+3) (x*2+3)).
  follow' (BigStep0 (x+1) (x*2+8)).
  finish.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1LC0LF_0RD1LA_1RA1LD_0LB1RC_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{C}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [1;0;0] *> [1;1;1;0;0]^^(n) *> [1;0;0] *> [1;1;1;0;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1;1]) (qR:=[1;0]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (m) -->+
  LC1 1 0 (1+n) <| R (m) 1.
Proof.
  mid10 (LC0 n <| [1;1;0;0] *> [1;1;1;0;0]^^(1+m) *> 0inf).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R (1+m) 1.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 ((1+m)) -->+
  LC1 1 0 n <| R m 2.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Lemma BigStep0 n m:
  S0 ((n+1)*2) (1+(n*2+1+m)) -->+
  S0 (m+1) (n*2+m+3).
Proof.
  unfold S0.
  follow10 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Lemma BigStep1 n m:
  S0 ((n+1)*2+1) (((n+1)*2+1+m)) -->+
  S0 (m+1) (n*2+m+4).
Proof.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Definition S1 x := S0 (x*2+4) (x*4+7).

Ltac follow' H :=
  (eapply evstep_progress_trans || eapply evstep_trans); [|follow100 H || follow10 H || follow H]; [finish|].

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  follow' (BigStep0 (x+1) (x*2+3)).
  follow' (BigStep0 (x+1) (x*2+4)).
  follow' (BigStep1 (x+1) (x*2+4)).
  follow' (BigStep1 (x+1) (x*2+5)).
  finish.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB1LB_1LC0RE_1LA0LD_0LB---_0LC1RF_0RA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{F}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [1;0;0] *> [1;1;1;0;0]^^(n) *> [1;0;0] *> [1;1;1;0;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1;1]) (qR:=[1;0]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (m) -->+
  LC1 1 0 (1+n) <| R (m) 1.
Proof.
  mid10 (LC0 n <| [1;1;0;0] *> [1;1;1;0;0]^^(1+m) *> 0inf).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R (1+m) 1.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 ((1+m)) -->+
  LC1 1 0 n <| R m 2.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Lemma BigStep0 n m:
  S0 ((n+1)*2) (1+(n*2+1+m)) -->+
  S0 (m+1) (n*2+m+3).
Proof.
  unfold S0.
  follow10 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Lemma BigStep1 n m:
  S0 ((n+1)*2+1) (((n+1)*2+1+m)) -->+
  S0 (m+1) (n*2+m+4).
Proof.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Definition S1 x := S0 (x*2+3) (x*4+10).

Ltac follow' H :=
  (eapply evstep_progress_trans || eapply evstep_trans); [|follow100 H || follow10 H || follow H]; [finish|].

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  follow' (BigStep1 (x) (x*2+7)).
  follow' (BigStep0 (x+3) (x*2+3)).
  follow' (BigStep0 (x+1) (x*2+8)).
  follow' (BigStep1 (x+3) (x*2+4)).
  finish.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC0LF_1RA1LA_0LB1RE_0RC1LA_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [1;0;0] *> [1;1;1;0;0]^^(n) *> [1;0;0] *> [1;1;1;0;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1;1]) (qR:=[1;0]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (m) -->+
  LC1 1 0 (1+n) <| R (m) 1.
Proof.
  mid10 (LC0 n <| [1;1;0;0] *> [1;1;1;0;0]^^(1+m) *> 0inf).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R (1+m) 1.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 ((1+m)) -->+
  LC1 1 0 n <| R m 2.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Lemma BigStep0 n m:
  S0 ((n+1)*2) (1+(n*2+1+m)) -->+
  S0 (m+1) (n*2+m+3).
Proof.
  unfold S0.
  follow10 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Lemma BigStep1 n m:
  S0 ((n+1)*2+1) (((n+1)*2+1+m)) -->+
  S0 (m+1) (n*2+m+4).
Proof.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Definition S1 x := S0 (x*2+5) (x*4+10).

Ltac follow' H :=
  (eapply evstep_progress_trans || eapply evstep_trans); [|follow100 H || follow10 H || follow H]; [finish|].

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  follow' (BigStep1 (x+1) (x*2+5)).
  follow' (BigStep0 (x+2) (x*2+5)).
  follow' (BigStep0 (x+2) (x*2+6)).
  follow' (BigStep1 (x+2) (x*2+6)).
  finish.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LC_1LA0RD_0LA1RE_0RB1LC_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition LC0 n := BinInc <[0;0;1] n <* <[0;0].
Definition LC1 len n m := BinDec <[0;0;0] <[1;0;0] len n (BinInc <[0;0;1] m).
Definition R n m := [1;0;0] *> [1;1;1;0;0]^^(n) *> [1;0;0] *> [1;1;1;0;0]^^(m) *> const 0.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[1;1]) (qR:=[1;0]); es.
  er.
Qed.

Lemma LInc1 r len n m:
  1+n<2^len ->
  LC1 len (1+n) m <| r -->*
  LC1 len n m |> r.
Proof.
  intros.
  unfold LC1.
  eapply progress_evstep.
  apply LBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RInc l n m:
  l |> R (1+n) m -->*
  l <| R n (1+m).
Proof.
  unfold R; es.
Qed.

Lemma Incs1 len n m n0 m0:
  n < 2^len ->
  LC1 len n m <| R (n+n0) m0 -->*
  LC1 len 0 m <| R n0 (n+m0).
Proof.
  gen len m n0 m0.
  induction n; intros.
  1: finish.
  follow LInc1.
  follow RInc.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Incs0 n n0 m0:
  LC0 n <| R n0 m0 -->*
  LC0 (n0+n) <| R 0 (n0+m0).
Proof.
  gen n m0.
  induction n0; intros.
  1: finish.
  follow LInc0.
  follow RInc.
  follow IHn0.
  finish.
Qed.


Lemma LOv1_0 r len m:
  LC1 len 0 (m*2) <| r -->*
  LC1 (1+len) ((0*2+1)*2^len-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  2: solve_pow2_lt.
  es.
Qed.

Lemma LOv1_1 r len m:
  LC1 len 0 (m*2+1) <| r -->*
  LC1 (1+len) (2^(1+len)-1) m |> r.
Proof.
  unfold LC1.
  rw_Bin.
  es.
Qed.

Lemma LOv1Incs_0 len m n0 m0:
  LC1 len 0 (m*2) <| R (2^len+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^len+m0).
Proof.
  replace (2^len+n0) with (1+(2^len-1+n0)) by lia.
  follow LOv1_0.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOv1Incs_1 len m n0 m0:
  LC1 len 0 (m*2+1) <| R (2^(1+len)+n0) m0 -->*
  LC1 (1+len) 0 m <| R n0 (2^(1+len)+m0).
Proof.
  replace (2^(1+len)+n0) with (1+(2^(1+len)-1+n0)) by lia.
  follow LOv1_1.
  follow RInc.
  epose proof (Incs1 _ _ _ _ _) as I1.
  follow I1.
  1: cbn; lia.
  finish.
Qed.

Lemma LOvIncss len m1 m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (m1*2^len+m2) <| R ((m2+(2^len-1))*2+n0) m0 -->*
  LC1 (1+len) 0 m1 <| R n0 ((m2+(2^len-1))*2+m0).
Proof.
  gen m1 m2 n0 m0.
  induction len; intros.
  1: finish.
  replace (2^S len) with (2^len*2) in * by (cbn; lia).
  unshelve epose proof (Nat.div_mod m2 (2^len) _) as E1.
  1: lia.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ H) as E2.
  remember (m2/2^len) as v1.
  remember (m2 mod 2^len) as v2.
  pose proof (Nat.mod_upper_bound m2 (2^len)) as E3.
  rewrite E1.
  mid (LC1 1 0 ((m1*2+v1)*2^len+v2) <| R ((v2+(2^len-1))*2+(2^len*2*(v1+1)+n0)) m0).
  1: finish.
  follow IHlen.
  1: lia.
  destruct v1 as [|[|]]. 3: lia.
  - rewrite Nat.add_0_r.
    replace (2^len*2*(0+1)) with (2^(1+len)) by (cbn; lia).
    follow LOv1Incs_0.
    rewrite Nat.pow_add_r.
    finish.
  - replace (2^len*2*(1+1)) with (2^(1+(1+len))) by (cbn; lia).
    follow LOv1Incs_1.
    repeat rewrite Nat.pow_add_r.
    finish.
Qed.

Lemma LOv1_h r len:
  LC1 len 0 1 <| r -->*
  LC0 0 |> r.
Proof.
  unfold LC1,LC0.
  rw_Bin.
  er; sr.
  er; use_shift_rule.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LOvIncss' len m2 n0 m0:
  m2<2^len ->
  LC1 1 0 (1*2^len+m2) <| R ((m2+(2^len-1))*2+(1+n0)) m0 -->*
  LC0 n0 <| R 0 ((m2+(2^len-1))*2+1+n0+m0).
Proof.
  intros.
  follow LOvIncss.
  follow LOv1_h.
  follow RInc.
  follow Incs0.
  finish.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LOvIncss'' n n0 m0:
  LC1 1 0 (n+1) <| R (n*2+1+n0) m0 -->*
  LC0 n0 <| R 0 (n*2+1+n0+m0).
Proof.
  unshelve epose proof (highbit (n+1) _) as [len [m2 I1]].
  1: lia.
  eapply evstep_trans.
  2: follow (LOvIncss' len m2 n0 m0).
  1: finish.
  1: lia.
  finish.
Qed.

Lemma ROv_1 n m:
  LC0 (n*2+1) |> R 0 (m) -->+
  LC1 1 0 (1+n) <| R (m) 1.
Proof.
  mid10 (LC0 n <| [1;1;0;0] *> [1;1;1;0;0]^^(1+m) *> 0inf).
  1: unfold LC1,LC0,R; rw_Bin; es.
  follow LInc0.
  remember (1+n) as n0.
  unfold LC1,LC0,R; rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0 n m:
  LC0 (n*2) |> R 0 (1+m) -->+
  LC1 1 1 n <| R (1+m) 1.
Proof.
  unfold LC1,LC0,R.
  rw_Bin.
  remember (1+m) as v1.
  do 3 (er; sr).
  er.
  replace v1 with (m+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  sr.
  es.
Qed.

Lemma ROv_0' n m:
  LC0 (n*2) |> R 0 ((1+m)) -->+
  LC1 1 0 n <| R m 2.
Proof.
  follow10 ROv_0.
  follow LInc1.
  follow RInc.
  finish.
Qed.

Definition S0 n m := LC0 n |> R 0 m. 

Lemma BigStep0 n m:
  S0 ((n+1)*2) (1+(n*2+1+m)) -->+
  S0 (m+1) (n*2+m+3).
Proof.
  unfold S0.
  follow10 ROv_0'.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Lemma BigStep1 n m:
  S0 ((n+1)*2+1) (((n+1)*2+1+m)) -->+
  S0 (m+1) (n*2+m+4).
Proof.
  unfold S0.
  follow10 ROv_1.
  rewrite Nat.add_comm.
  follow LOvIncss''.
  follow LInc0.
  finish.
Qed.

Definition S1 x := S0 (x*2+3) (x*4+9).

Ltac follow' H :=
  (eapply evstep_progress_trans || eapply evstep_trans); [|follow100 H || follow10 H || follow H]; [finish|].

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1 0).
  1: unfold S1,S0; esx.
  eapply progress_nonhalt_simple.
  intros x.
  exists (x+1).
  unfold S1.
  follow' (BigStep1 (x) (x*2+6)).
  follow' (BigStep1 (x+2) (x*2+3)).
  follow' (BigStep0 (x+1) (x*2+7)).
  follow' (BigStep0 (x+3) (x*2+4)).
  finish.
Qed.

End TM9.


