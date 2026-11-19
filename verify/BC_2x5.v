From BusyCoq Require Import Individual25.
From BusyCoq Require Import BinaryCounter25_v2.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Ltac flia := repeat (lia || f_equal).

Ltac lia' :=
  repeat rewrite pow2_S; lia.

Lemma pow4_ge i:
  2^(i*2)>=i+1.
Proof.
  induction i; cbn; lia.
Qed.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB3LB3LA0RB---_2LA0LA4RA1RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC len n := BinDec [3;2] [3;3] len n 0inf.

Lemma RC_Inc len n l:
  1+n<2^len ->
  l {{B}}> RC len (1+n) -->+
  l <{{B}} RC len n.
Proof.
  intros H.
  apply RBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Lemma RC_Ov len n l:
  n<2^len ->
  l {{A}}> RC len n -->*
  l <{{B}} RC (len+1) ((2^len-1-n)*2+1).
Proof.
  unfold RC.
  gen n l.
  induction len; intros.
  - cbn in H.
    replace n with O by lia.
    er.
  - replace (S len) with (len+1) by lia.
    cbn in H.
    rw_Bin.
    2: repeat rewrite pow2_S; lia.
    pose proof (Nat.Div0.div_mod n 2).
    pose proof (Nat.mod_upper_bound n 2).
    remember (n/2) as n0; clear Heqn0.
    destruct (n mod 2) as [|[|]]; subst n.
    3: lia.
    + replace (2*n0+0) with (n0*2) by lia.
      replace (2^(len+1)-1-n0*2) with ((2^len-1-n0)*2+1) by lia'.
      rw_Bin.
      2,3: lia'.
      er.
      follow IHlen.
      1: lia'.
      rw_Bin.
      2: lia'.
      er.
    + replace (2*n0+1) with (n0*2+1) by lia.
      replace (2^(len+1)-1-(n0*2+1)) with ((2^len-1-n0)*2) by lia'.
      rw_Bin.
      2,3: lia'.
      er.
      follow IHlen.
      1: lia'.
      rw_Bin.
      2: lia'.
      er.
Qed.

Opaque RC.

Definition S0 a b c len :=
  0inf <* <[1;4]^^a <* <[1;1]^^b <{{B}} RC len c.

Lemma Inc a b c len:
  1+c<2^len ->
  S0 (1+a) b (1+c) len -->*
  S0 a (1+b) c len.
Proof.
  intros H.
  unfold S0.
  es; er.
  epose proof (RC_Inc _ _ _ H) as HR.
  follow100 HR.
  finish.
Qed.

Lemma Incs a b c len:
  a+c<2^len ->
  S0 a b (a+c) len -->*
  S0 0 (a+b) c len.
Proof.
  gen len b c.
  induction a; intros.
  1: finish.
  follow Inc.
  follow IHa.
  1: lia.
  finish.
Qed.

Lemma BigStep b c len:
  c<2^len ->
  b<=(2^len-1-c)*2 ->
  S0 0 b c len -->+
  S0 0 (1+b) ((2^len-1-c)*2-b) (len+1).
Proof.
  intros H H0.
  unfold S0.
  es; er.
  follow RC_Ov.
  remember ((2^len-1-c)*2) as v1.
  mid (S0 (1+b) 0 (v1+1) (len+1)).
  1: finish.
  replace (v1+1) with ((1+b)+(v1-b)) by lia.
  follow Incs.
  1: lia'.
  es.
Qed.

Definition config '(b,c) :=
  S0 0 b c (b+1).

Transparent RC.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(b,c) => exists i, b=i*2 /\ c*9+i*6+5=2^(i*2)*14 \/ b=i*2+1 /\ c*9+i*6+8=2^(i*2)*8).
  2: exists O; cbn; lia.
  intros [b c] [i [[Hb Hc]|[Hb Hc]]].
  - eexists (i*2+1,_).
    unfold config.
    split.
    + applys_eq (BigStep b c (b+1)).
      1: flia.
      * subst b.
        lia'.
      * subst b.
        pose proof (pow4_ge i).
        lia'.
    + exists i; right; split.
      1: lia.
      subst b.
      pose proof (pow4_ge i).
      lia'.
  - eexists (i*2+2,_).
    unfold config.
    split.
    + applys_eq (BigStep b c (b+1)).
      1: flia.
      * subst b.
        lia'.
      * subst b.
        pose proof (pow4_ge i).
        lia'.
    + exists (i+1); left; split.
      1: lia.
      subst b.
      replace ((i+1)*2) with (i*2+1+1) by lia.
      lia'.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB3RB0LB2RA2RB_2RA4LB4LA---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC len n := BinDec [4;1] [4;4] len n 0inf.

Lemma RC_Inc len n l:
  1+n<2^len ->
  l {{A}}> RC len (1+n) -->+
  l <{{A}} RC len n.
Proof.
  intros H.
  apply RBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Lemma RC_Ov len n l:
  n<2^len ->
  l {{B}}> RC len n -->*
  l <{{A}} RC (len+1) ((2^len-1-n)*2+1).
Proof.
  unfold RC.
  gen n l.
  induction len; intros.
  - cbn in H.
    replace n with O by lia.
    er.
  - replace (S len) with (len+1) by lia.
    cbn in H.
    rw_Bin.
    2: repeat rewrite pow2_S; lia.
    pose proof (Nat.Div0.div_mod n 2).
    pose proof (Nat.mod_upper_bound n 2).
    remember (n/2) as n0; clear Heqn0.
    destruct (n mod 2) as [|[|]]; subst n.
    3: lia.
    + replace (2*n0+0) with (n0*2) by lia.
      replace (2^(len+1)-1-n0*2) with ((2^len-1-n0)*2+1) by lia'.
      rw_Bin.
      2,3: lia'.
      er.
      follow IHlen.
      1: lia'.
      rw_Bin.
      2: lia'.
      er.
    + replace (2*n0+1) with (n0*2+1) by lia.
      replace (2^(len+1)-1-(n0*2+1)) with ((2^len-1-n0)*2) by lia'.
      rw_Bin.
      2,3: lia'.
      er.
      follow IHlen.
      1: lia'.
      rw_Bin.
      2: lia'.
      er.
Qed.

Opaque RC.

Definition S0 a b c len :=
  0inf <* <[2;3]^^a <* <[2;2]^^b <{{A}} RC len c.

Lemma Inc a b c len:
  1+c<2^len ->
  S0 (1+a) b (1+c) len -->*
  S0 a (1+b) c len.
Proof.
  intros H.
  unfold S0.
  es; er.
  epose proof (RC_Inc _ _ _ H) as HR.
  follow100 HR.
  finish.
Qed.

Lemma Incs a b c len:
  a+c<2^len ->
  S0 a b (a+c) len -->*
  S0 0 (a+b) c len.
Proof.
  gen len b c.
  induction a; intros.
  1: finish.
  follow Inc.
  follow IHa.
  1: lia.
  finish.
Qed.

Lemma BigStep b c len:
  c<2^len ->
  b<=(2^len-1-c)*2 ->
  S0 0 b c len -->+
  S0 0 (1+b) ((2^len-1-c)*2-b) (len+1).
Proof.
  intros H H0.
  unfold S0.
  es; er.
  follow RC_Ov.
  remember ((2^len-1-c)*2) as v1.
  mid (S0 (1+b) 0 (v1+1) (len+1)).
  1: finish.
  replace (v1+1) with ((1+b)+(v1-b)) by lia.
  follow Incs.
  1: lia'.
  es.
Qed.

Definition config '(b,c) :=
  S0 0 b c b.

Transparent RC.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,0)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(b,c) => exists i, b=i*2 /\ c*9+i*6+5=2^(i*2)*5 \/ b=i*2+1 /\ c*9+i*6+8=2^(i*2)*8).
  2: exists O; cbn; lia.
  intros [b c] [i [[Hb Hc]|[Hb Hc]]].
  - eexists (i*2+1,_).
    unfold config.
    split.
    + applys_eq (BigStep b c (b)).
      1: flia.
      * subst b.
        lia'.
      * subst b.
        pose proof (pow4_ge i).
        lia'.
    + exists i; right; split.
      1: lia.
      subst b.
      pose proof (pow4_ge i).
      lia'.
  - eexists (i*2+2,_).
    unfold config.
    split.
    + applys_eq (BigStep b c (b)).
      1: flia.
      * subst b.
        lia'.
      * subst b.
        pose proof (pow4_ge i).
        lia'.
    + exists (i+1); left; split.
      1: lia.
      subst b.
      replace ((i+1)*2) with (i*2+1+1) by lia.
      lia'.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB---3RB4LB0RB_2LB2RA3RA0LA4RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC r len n := BinDec [4;0] [2;2] len n (r*>0inf).

Lemma RC_Inc l r len n:
  n+1<2^len ->
  l {{A}}> RC r len (n+1) -->*
  l <{{B}} RC r len n.
Proof.
  rewrite (Nat.add_comm n 1).
  intros H.
  eapply progress_evstep.
  apply RBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Lemma Eat0 l r len n:
  n+2<2^len ->
  l <* <[4;1] <{{B}} RC r len (n+2) -->*
  l <{{B}} RC r (len+1) (n*2).
Proof.
  intros H.
  replace (n+2) with (n+1+1) by lia.
  er.
  follow RC_Inc.
  1: lia.
  er.
  follow RC_Inc.
  1: lia.
  unfold RC.
  rw_Bin.
  2: rewrite pow2_S; lia.
  er.
Qed.

Lemma Eat1 l r len n:
  n<2^len ->
  l <* <[3;3] <{{B}} RC r len (n) -->*
  l <{{B}} RC r (len+1) (n*2+1).
Proof.
  intros H.
  unfold RC.
  rw_Bin.
  2: rewrite pow2_S; lia.
  er.
Qed.

Definition lh := 0inf <* [2] <* [3]^^5.

Lemma LR r len n:
  n<2^len ->
  lh <{{B}} RC r len n -->*
  lh {{B}}> RC r (len+1) (n*2+1).
Proof.
  intros H.
  unfold RC.
  rw_Bin.
  2: rewrite pow2_S; lia.
  er.
Qed.

Lemma Uneat0 l r len n:
  n<2^len ->
  l {{B}}> RC r (len+1) (n*2+1) -->*
  l <* <[4;1] {{B}}> RC r len n.
Proof.
  intros H.
  unfold RC.
  rw_Bin.
  2: rewrite pow2_S; lia.
  er.
Qed.

Lemma Uneat1 l r len n:
  n<2^len ->
  l {{B}}> RC r (len+1) (n*2) -->*
  l <* <[3;3] {{B}}> RC r len n.
Proof.
  intros H.
  unfold RC.
  rw_Bin.
  2: rewrite pow2_S; lia.
  er.
Qed.

Fixpoint Ln ls :=
match ls with
| nil => O
| true::ls0 => Ln ls0
| false::ls0 => Ln ls0 + 2^(List.length ls0)
end.

Fixpoint LC ls :=
match ls with
| nil => lh
| false::ls0 => LC ls0 <* <[4;1]
| true::ls0 => LC ls0 <* <[3;3]
end.

Inductive DivMod2: nat->Prop :=
| mod2eq0(n n':nat)(Hn':n=n'*2):DivMod2 n
| mod2eq1(n n':nat)(Hn':n=n'*2+1):DivMod2 n
.

Lemma divmod2 n: DivMod2 n.
Proof.
  pose proof (Nat.Div0.div_mod n 2).
  pose proof (Nat.mod_upper_bound n 2).
  destruct (n mod 2) as [|[|]]. 3: lia.
  - eapply (mod2eq0 n (n/2)).
    lia.
  - eapply (mod2eq1 n (n/2)).
    lia.
Qed.

Lemma Uneats ls r len n:
  n<2^len ->
  exists ls',
  LC ls {{B}}> RC r len n -->*
  LC ls' {{B}}> RC r 0 0 /\
  List.length ls' = List.length ls + len /\
  Ln ls' = Ln ls + n*2^(List.length ls).
Proof.
  gen n ls.
  induction len; intros; cbn in H.
  1:{
    exists ls.
    split.
    1: finish.
    replace n with O by lia.
    cbn; lia.
  }
  destruct (divmod2 n).
  - replace (S len) with (len+1) by lia.
    subst n.
    epose proof (IHlen n' (true::ls) _) as [ls' [I I0]].
    exists (ls').
    split.
    2: cbn in I0; lia.
    follow Uneat1.
    1: lia.
    follow I.
    finish.
  - replace (S len) with (len+1) by lia.
    subst n.
    epose proof (IHlen n' (false::ls) _) as [ls' [I I0]].
    exists (ls').
    split.
    2: cbn in I0; lia.
    follow Uneat0.
    1: lia.
    follow I.
    finish.
Unshelve.
all: lia.
Qed.

Lemma and1 (P Q:Prop):
  P ->
  (P->Q) ->
  P /\ Q.
Proof. tauto. Qed.

Lemma LR_bound ls len n r:
  4<=n<2^len ->
  exists ls' n',
  LC ls <{{B}} RC r len n -->*
  LC ls' {{B}}> RC r len n' /\
  n'<=n<=n'+4 /\
  List.length ls' = S (List.length ls) /\
  Ln ls' + (Ln ls)*10 + 1 = 2^(List.length ls)*((n-n')*2+2).
Proof.
  gen len n.
  induction ls; intros.
  - eexists [false],n.
    split.
    2: cbn; lia.
    cbn[LC].
    follow LR.
    1: lia.
    unfold RC.
    rw_Bin.
    2: rewrite pow2_S; lia.
    er.
  - cbn[LC].
    destruct a.
    + epose proof (IHls (len+1) (n*2+1) _) as [ls' [n' [I [I0 [I1 I2]]]]].
      pose proof (divmod2 n') as Hdm2.
      inverts Hdm2.
      * eexists (true::ls'),(n'0).
        split.
        2:{
          apply and1.
          1: lia.
          intro Hn'0.
          split.
          1: cbn; lia.
          cbn[Ln]. cbn[List.length].
          cbn[Nat.pow].
          rewrite (Nat.mul_comm 2).
          rewrite <-Nat.mul_assoc.
          rewrite I2.
          f_equal.
          lia.
        }
        follow Eat1.
        1: lia.
        follow I.
        follow Uneat1.
        1: lia.
        cbn[LC].
        finish.
      * eexists (false::ls'),n'0.
        split.
        2:{
          apply and1.
          1: lia.
          intro Hn'0.
          split.
          1: cbn; lia.
          cbn[Ln]. cbn[List.length].
          rewrite I1.
          cbn[Nat.pow].
          rewrite (Nat.mul_comm 2).
          rewrite <-Nat.mul_assoc.
          remember (2^(List.length ls)) as v1.
          replace (Ln ls'+v1*2+Ln ls*10+1) with (Ln ls'+Ln ls*10+1+v1*2) by lia.
          rewrite I2.
          rewrite <-Nat.mul_add_distr_l.
          f_equal.
          lia.
        }
        follow Eat1.
        1: lia.
        follow I.
        follow Uneat0.
        1: lia.
        cbn[LC].
        finish.
    + epose proof (IHls (len+1) ((n-2)*2) _) as [ls' [n' [I [I0 [I1 I2]]]]].
      pose proof (divmod2 n') as Hdm2.
      inverts Hdm2.
      * eexists (true::ls'),n'0.
        split.
        2:{
          apply and1.
          1: lia.
          intro Hn'0.
          split.
          1: cbn; lia.
          cbn[Ln]. cbn[List.length].
          cbn[Nat.pow].
          rewrite (Nat.mul_comm 2).
          rewrite <-Nat.mul_assoc.
          remember (2^(List.length ls)) as v1.
          replace (Ln ls'+(Ln ls+v1)*10+1) with (Ln ls'+Ln ls*10+1+v1*10) by lia.
          rewrite I2.
          rewrite <-Nat.mul_add_distr_l.
          f_equal.
          lia.
        }
        replace n with ((n-2)+2) by lia.
        follow Eat0.
        1: lia.
        follow I.
        follow Uneat1.
        1: lia.
        cbn[LC].
        finish.
      * eexists (false::ls'),n'0.
        split.
        2:{
          apply and1.
          1: lia.
          intro Hn'0.
          split.
          1: cbn; lia.
          cbn[Ln]. cbn[List.length].
          rewrite I1.
          cbn[Nat.pow].
          rewrite (Nat.mul_comm 2).
          rewrite <-Nat.mul_assoc.
          remember (2^(List.length ls)) as v1.
          replace (Ln ls'+v1*2+(Ln ls+v1)*10+1) with (Ln ls'+Ln ls*10+1+v1*12) by lia.
          rewrite I2.
          rewrite <-Nat.mul_add_distr_l.
          f_equal.
          lia.
        }
        replace n with ((n-2)+2) by lia.
        follow Eat0.
        1: lia.
        follow I.
        follow Uneat0.
        1: lia.
        cbn[LC].
        finish.
Unshelve.
all: rewrite pow2_S; lia.
Qed.

Lemma RIncs l r len n:
  n<2^len ->
  l <* [4] <{{B}} RC r len n -->*
  l <* [4] <{{B}} RC r len 0.
Proof.
  induction n; intros.
  1: finish.
  step1.
  replace (S n) with (n+1) by lia.
  follow RC_Inc.
  1: lia.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Step ls len n r:
  4<=n<2^len ->
  exists ls',
  LC ls <{{B}} RC r len n -->*
  LC ls' {{B}}> r *> 0inf /\
  List.length ls' = List.length ls + len + 1 /\
  Ln ls' + (Ln ls)*10 + 1 = (2^(List.length ls))*(n*2+2).
Proof.
  intros Hn.
  epose proof (LR_bound _ _ _ _ _) as [ls' [n' [H H']]].
  epose proof (Uneats _ _ _ _ _) as [ls'0 H0].
  eexists ls'0.
  split.
  - follow H.
    follow H0.
    er.
  - apply and1.
    1: lia.
    intros Hlen.
    destruct H' as [H'1 [H'2 H'3]].
    destruct H0 as [H'4 [H'5 H'6]].
    rewrite H'2 in *.
    cbn[Nat.pow] in H'6.
    remember (2^(List.length ls)) as v1.
    rewrite H'6.
    replace (Ln ls'+n'*(2*v1)+Ln ls*10+1) with (v1*((n-n')*2+2+n'*2)) by lia.
    f_equal.
    lia.
Unshelve.
all: lia.
Qed.

Lemma Ln_lt ls:
  Ln ls < 2^(List.length ls).
Proof.
  induction ls.
  - cbn; lia.
  - cbn.
    destruct a; lia.
Qed.

Lemma Ln_d0 ls n:
  List.length ls = S n ->
  Ln ls < 2^n ->
  exists ls', ls = true::ls'.
Proof.
  destruct ls; cbn.
  1: lia.
  intros.
  destruct b.
  - exists ls; reflexivity.
  - replace (List.length ls) with n in H0 by lia.
    lia.
Qed.

Lemma Ln_d1 ls n:
  List.length ls = S n ->
  Ln ls >= 2^n ->
  exists ls', ls = false::ls'.
Proof.
  destruct ls; cbn.
  1: lia.
  intros.
  destruct b.
  - pose proof (Ln_lt ls).
    replace (List.length ls) with n in H1 by lia.
    lia.
  - exists ls; reflexivity.
Qed.

Lemma Ln_29 ls n:
  List.length ls = 6+n ->
  2^n*29 <= Ln ls < 2^n*30 ->
  exists ls', ls = true::false::false::false::true::false::ls'.
Proof.
  cbn.
  intros Hlen HLn.
  unshelve epose proof (Ln_d0 ls _ Hlen _) as [ls' E].
  1: cbn; lia.
  subst ls.
  cbn in *.
  inverts Hlen.
  unshelve epose proof (Ln_d1 ls' _ H0 _) as [ls E].
  1: cbn; lia.
  subst ls'.
  cbn in *.
  inverts H0.
  rewrite H1 in HLn.
  cbn[Nat.pow] in HLn.
  unshelve epose proof (Ln_d1 ls _ H1 _) as [ls' E].
  1: cbn; lia.
  subst ls.
  cbn in H1.
  cbn[Ln] in HLn.
  inverts H1.
  rewrite H0 in HLn.
  cbn[Nat.pow] in HLn.
  unshelve epose proof (Ln_d1 ls' _ H0 _) as [ls E].
  1: cbn; lia.
  subst ls'.
  cbn in H0.
  cbn[Ln] in HLn.
  inverts H0.
  rewrite H1 in HLn.
  cbn[Nat.pow] in HLn.
  unshelve epose proof (Ln_d0 ls _ H1 _) as [ls' E].
  1: cbn; lia.
  subst ls.
  cbn in H1.
  cbn[Ln] in HLn.
  inverts H1.
  unshelve epose proof (Ln_d1 ls' _ H0 _) as [ls E].
  1: cbn; lia.
  subst ls'.
  eexists; reflexivity.
Qed.

Ltac nextStep n :=
  let n1 := fresh "Hlen" in
  let n2 := fresh "HLn" in
  let n0 := fresh "H" in
  epose proof (Step _ _ _ _ _) as [n [n0 [n1 n2]]].

Ltac followc H :=
  follow H; clear H.

Definition config ls :=
  LC ls <{{B}} [2;2] *> [4;0]^^10 *> [2] *> 0inf.

Lemma test ls:
  exists ls',
  config ls -->+ config ls'.
Proof.
  unfold config.
  nextStep ls'0.
  nextStep ls'2.
  nextStep ls'4.
  nextStep ls'6.
  nextStep ls'8.
  nextStep ls'10.
  nextStep ls'12.
  nextStep ls'14.
  nextStep ls'16.
  epose proof (Ln_29 ls'16 (List.length ls + 10+10+10+4) _ _) as [ls'' E].
  exists ls''.
  mid01 (LC ls <{{B}} RC ([4;0]^^8++[2]) 3 6).
  1: finish.
  followc H.
  mid10 (LC ls'0 <{{B}} RC ([2;2]^^5++[4;0;2;2;4;0;4;0;2;2]) 3 4).
  1: er.
  followc H0.
  mid (LC ls'2 <{{B}} RC ([4;0;4;0;2;2]++[4;0]^^4++[2;2;2]) 3 7).
  1: er.
  followc H1.
  do 352 step1.
  remember (RC [] 13 1175) as v1.
  remember Heqv1 as Heqv1'.
  vm_compute in Heqv1'.
  mid (LC ls'4 <* [1;4] <* [4] <{{B}} v1).
  1: rewrite Heqv1'; finish.
  rewrite Heqv1.
  follow RIncs.
  1: cbv; lia.
  clear HeqHeqv1' Heqv1'.
  remember (RC [] 13 0) as v2.
  vm_compute in Heqv2.
  subst v2.
  mid (LC ls'4 <{{B}} RC ([4;0]^^11++[2;2]) 4 8).
  1: er.
  followc H2.
  mid (LC ls'6 <{{B}} RC ([2;2]^^8++[4;0;2;2;2]) 3 4).
  1: er.
  followc H3.
  mid (LC ls'8 <{{B}} RC ([4;0]^^5++[2;2;4;0;2;2;2;2]) 3 7).
  1: er.
  followc H4.
  mid (LC ls'10 <{{B}} RC ([2;2;2;2;4;0;2;2;2;2;2;2;2]) 3 4).
  1: er.
  followc H5.
  mid (LC ls'12 <{{B}} RC ([2;2;4;0;4;0;2;2]) 4 11).
  1: er.
  followc H6.
  mid (LC ls'14 <{{B}} RC ([2]) 5 17).
  1: er.
  followc H7.
  er.
  rewrite E.
  er.
Unshelve.
1-9: cbn; lia.
  1: lia.
  1:{
    rewrite Hlen in *.
    rewrite Hlen0 in *.
    rewrite Hlen1 in *.
    rewrite Hlen2 in *.
    rewrite Hlen3 in *.
    rewrite Hlen4 in *.
    rewrite Hlen5 in *.
    rewrite Hlen6 in *.
    repeat rewrite Nat.pow_add_r in *.
    change (2^3) with 8 in *.
    change (2^4) with 16 in *.
    change (2^1) with 2%nat in *.
    remember (2^List.length ls) as c1.
    pose proof (Ln_lt ls) as Hls.
    repeat rewrite Nat.pow_add_r.
    change (2^10) with 1024.
    change (2^4) with 16.
    lia.
  }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (List.map negb (List.rev [true;false;true;true;true;false;true;false;false;false;false;true;false;true;true;false;true;false;true;false;true;true;false]))).
  1: shelve.
  eapply progress_nonhalt_simple.
  intros.
  apply test.
  Unshelve.
  time do 5240 step1.
  unfold config; cbn.
  finish.
Time Qed.

End TM3.


