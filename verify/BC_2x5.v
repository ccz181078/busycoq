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

