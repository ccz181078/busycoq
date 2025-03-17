From BusyCoq Require Import Individual25.
From BusyCoq Require Import BinaryCounter25_v2.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Ltac flia := repeat (lia || f_equal).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB3RB---1LB0LA_2LA4RA3LA4RB1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive RDigits :=
| rd0(x:RDigits)
| rd1(x:RDigits)
| rd2(x:RDigits)
| rh1 | rh2.

Fixpoint R x :=
match x with
| rd0 x0 => [0] *> R x0
| rd1 x0 => [2] *> R x0
| rd2 x0 => [3] *> R x0
| rh1 => [2] *> 0inf
| rh2 => [3] *> 0inf
end.

Fixpoint RS x :=
match x with
| rd0 x0 => rd1 x0
| rd1 x0 => rd2 x0
| rd2 x0 => rd0 (RS x0)
| rh1 => rh2
| rh2 => rd0 rh1
end.

Fixpoint Rn n :=
match n with
| O => rh1
| S n0 => RS (Rn n0)
end.

Lemma Rn_spec n:
  rd0 (Rn n) = Rn (n*3+2) /\
  rd1 (Rn n) = Rn (n*3+3) /\
  rd2 (Rn n) = Rn (n*3+4).
Proof.
  induction n; cbn.
  1: tauto.
  destruct IHn as [I0 [I1 I2]].
  repeat split.
  - rewrite <-I0; reflexivity.
  - rewrite <-I1; reflexivity.
  - rewrite <-I2; reflexivity.
Qed.

Lemma RInc l n:
  l {{B}}> R (Rn n) -->*
  l <{{A}} R (Rn (1+n)).
Proof.
  cbn.
  gen l.
  induction (Rn n); intros; cbn; er.
  follow IHr; er.
Qed.

Definition LC l len n := BinDec <[4;3] <[4;4] len n (0inf <* l).

Lemma LC_Inc l len n r:
  1+n<2^len ->
  LC l len (1+n) <{{B}} r -->+
  LC l len n {{B}}> r.
Proof.
  intros H.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S l len n m :=
  LC l len n <{{B}} [1;1] *> R (Rn m).

Lemma Inc l len n m:
  1+n<2^len ->
  S l len (1+n) m -->+
  S l len n (1+m).
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc l _ _ _ H) as HL.
  follow10 HL.
  er.
  follow RInc.
  er.
Qed.

Lemma Incs l len n m:
  n<2^len ->
  S l len n m -->*
  S l len 0 (n+m).
Proof.
  gen l len m.
  induction n; intros.
  1: finish.
  epose proof (Inc l _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Opaque Rn.

Lemma Ov0_0 len m:
  S <[3;4] len 0 (m*3+2) -->*
  S <[4] (len+1) (2^(len+1)-1) (2+m).
Proof.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  unfold S,LC.
  rewrite <-I0.
  cbn.
  rw_Bin.
  es; er.
  follow RInc.
  er.
  follow RInc.
  er.
Qed.

Lemma Ov1_0 len m:
  S <[4] len 0 (m*3+2) -->*
  S <[3;4] (len+1) (2^(len+1)-1) (2+m).
Proof.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  unfold S,LC.
  rewrite <-I0.
  cbn.
  rw_Bin.
  es; er.
  follow RInc.
  er.
  follow RInc.
  er.
Qed.

Lemma Ov1_2 len m:
  S <[4] len 0 (m*3+4) -->+
  S <[3;4] (len+1) (2^(len+1)-1) m.
Proof.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  unfold S,LC.
  rewrite <-I2.
  cbn.
  rw_Bin.
  es.
Qed.

Lemma BigStep len m m0 m1 m2 m3:
  2^(len+1)-1+(2+m) = m0*3+2 ->
  2^(len+1+1)-1+(2+m0) = m1*3+4 ->
  2^(len+1+1+1)-1+(m1) = m2*3+2 ->
  2^(len+1+1+1+1)-1+(2+m2) = m3*3+2 ->
  S <[4] len 0 (m*3+2) -->+
  S <[4] (len+4) 0 (m3*3+2).
Proof.
  intros Hm0 Hm1 Hm2 Hm3.
  pose proof (Nat.pow_nonzero 2 len).
  follow Ov1_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm0.
  follow Ov0_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm1.
  follow10 Ov1_2.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm2.
  follow Ov0_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm3.
  finish.
Qed.

Definition config '(len,m) :=
  S <[4] len 0 (m*3+2).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,0)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(len,m) => m*5+4=2^len*2).
  2: reflexivity.
  intros [len m].
  intros Hz.
  exists (len+4,m*16+12).
  split.
  2: rewrite Nat.pow_add_r; cbn; lia.
  unfold config.
  epose proof (BigStep len m (m*2+1) (m*4+2) (m*8+5) (m*16+12) _ _ _ _) as H.
  follow10 H.
  finish.
  Unshelve.
  all: repeat rewrite pow2_S; lia.
Qed.

End TM1.


Lemma pow2'_S' i:
  2^(i+1)-1 = (2^i-1)*2+1.
Proof.
  rewrite Nat.pow_add_r; cbn.
  pose proof (Nat.pow_nonzero 2 i).
  lia.
Qed.

Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB1RA4LB2RB1LB_2RA2LB3LB0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive RDigits :=
| rd0(x:RDigits)
| rd1(x:RDigits)
| rd2(x:RDigits)
| rh.

Fixpoint R x :=
match x with
| rd0 x0 => [2] *> R x0
| rd1 x0 => [4] *> R x0
| rd2 x0 => [1] *> R x0
| rh => [1] *> 0inf
end.

Fixpoint RS x :=
match x with
| rd0 x0 => rd1 x0
| rd1 x0 => rd2 x0
| rd2 x0 => rd0 (RS x0)
| rh => rd0 rh
end.

Fixpoint Rn n :=
match n with
| O => rh
| S n0 => RS (Rn n0)
end.

Lemma Rn_spec n:
  rd0 (Rn n) = Rn (n*3+1) /\
  rd1 (Rn n) = Rn (n*3+2) /\
  rd2 (Rn n) = Rn (n*3+3).
Proof.
  induction n; cbn.
  1: tauto.
  destruct IHn as [I0 [I1 I2]].
  repeat split.
  - rewrite <-I0; reflexivity.
  - rewrite <-I1; reflexivity.
  - rewrite <-I2; reflexivity.
Qed.

Lemma RInc l n:
  l {{A}}> R (Rn n) -->*
  l <{{B}} R (Rn (1+n)).
Proof.
  cbn.
  gen l.
  induction (Rn n); intros; cbn; er.
  follow IHr; er.
Qed.

Definition LC len n := BinDec <[2;0] <[2;2] len n (0inf <* [2]).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <{{B}} r -->+
  LC len n {{A}}> r.
Proof.
  intros H.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S len n m :=
  LC len n <{{B}} R (Rn m).

Lemma Inc len n m:
  1+n<2^len ->
  S len (1+n) m -->+
  S len n (1+m).
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc _ _ _ H) as HL.
  follow10 HL.
  follow RInc.
  finish.
Qed.

Lemma Incs len n m:
  n<2^len ->
  S len n m -->*
  S len 0 (n+m).
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Opaque Rn.

Lemma Ov_0 len m:
  S (len+1) 0 (m*3+1) -->*
  S (len+1+1) ((2^len-1)*2*2+1) (1+m).
Proof.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  unfold S,LC.
  rewrite <-I0.
  cbn.
  rw_Bin.
  2,3: repeat rewrite pow2_S; pose proof (Nat.pow_nonzero 2 len); lia.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov_2 len m:
  S (len+1+1) 0 (m*3+3) -->+
  S (len+1+1+1) (((2^len-1)*2*2+1)*2+1) (1+m).
Proof.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  unfold S,LC.
  rewrite <-I2.
  cbn.
  rw_Bin.
  2,3,4: repeat rewrite pow2_S; pose proof (Nat.pow_nonzero 2 len); lia.
  es; er.
  follow RInc.
  er.
Qed.

Lemma BigStep len m m0 m1 m2 m3:
  ((2^(len)-1)*2*2+1)*2+1+(1+m) = m0*3+1 ->
  ((2^(len+1+1)-1)*2*2+1)+(1+m0) = m1*3+1 ->
  ((2^(len+1+1+1)-1)*2*2+1)+(1+m1) = m2*3+1 ->
  ((2^(len+1+1+1+1)-1)*2*2+1)+(1+m2) = m3*3+3 ->
  S (len+1+1) 0 (m*3+3) -->+
  S (len+4+1+1) 0 (m3*3+3).
Proof.
  intros Hm0 Hm1 Hm2 Hm3.
  pose proof (Nat.pow_nonzero 2 len).
  follow10 Ov_2.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm0.
  follow Ov_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm1.
  follow Ov_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm2.
  follow Ov_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm3.
  finish.
Qed.

Definition config '(len,m) :=
  S (len+1+1) 0 (m*3+3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(len,m) => m*5+3=(2^len-1)*8).
  2: reflexivity.
  intros [len m].
  intros Hz.
  exists (len+4,m*16+33).
  split.
  2: rewrite Nat.pow_add_r; cbn; lia.
  unfold config.
  epose proof (BigStep len m (m*2+2) (m*4+7) (m*8+16) (m*16+33) _ _ _ _) as H.
  follow10 H.
  finish.
  Unshelve.
  all: repeat rewrite pow2'_S'; lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB3LA1LA0RB---_2LA4LA2RB1RA2LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive RDigits :=
| rd0(x:RDigits)
| rd1(x:RDigits)
| rd2(x:RDigits)
| rh.

Fixpoint R x :=
match x with
| rd0 x0 => [1] *> R x0
| rd1 x0 => [4] *> R x0
| rd2 x0 => [2] *> R x0
| rh => [2] *> 0inf
end.

Fixpoint RS x :=
match x with
| rd0 x0 => rd1 x0
| rd1 x0 => rd2 x0
| rd2 x0 => rd0 (RS x0)
| rh => rd0 rh
end.

Fixpoint Rn n :=
match n with
| O => rh
| S n0 => RS (Rn n0)
end.

Lemma Rn_spec n:
  rd0 (Rn n) = Rn (n*3+1) /\
  rd1 (Rn n) = Rn (n*3+2) /\
  rd2 (Rn n) = Rn (n*3+3).
Proof.
  induction n; cbn.
  1: tauto.
  destruct IHn as [I0 [I1 I2]].
  repeat split.
  - rewrite <-I0; reflexivity.
  - rewrite <-I1; reflexivity.
  - rewrite <-I2; reflexivity.
Qed.

Lemma RInc l n:
  l {{B}}> R (Rn n) -->*
  l <{{A}} R (Rn (1+n)).
Proof.
  cbn.
  gen l.
  induction (Rn n); intros; cbn; er.
  follow IHr; er.
Qed.

Definition LC len n := BinDec <[1;0] <[1;1] len n (0inf <* [1]).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <{{A}} r -->+
  LC len n {{B}}> r.
Proof.
  intros H.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S len n m :=
  LC len n <{{A}} R (Rn m).

Lemma Inc len n m:
  1+n<2^len ->
  S len (1+n) m -->+
  S len n (1+m).
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc _ _ _ H) as HL.
  follow10 HL.
  follow RInc.
  finish.
Qed.

Lemma Incs len n m:
  n<2^len ->
  S len n m -->*
  S len 0 (n+m).
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Opaque Rn.

Lemma Ov_0 len m:
  S (len+1) 0 (m*3+1) -->*
  S (len+1+1) ((2^len-1)*2*2+1) (1+m).
Proof.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  unfold S,LC.
  rewrite <-I0.
  cbn.
  rw_Bin.
  2,3: repeat rewrite pow2_S; pose proof (Nat.pow_nonzero 2 len); lia.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov_2 len m:
  S (len+1+1) 0 (m*3+3) -->+
  S (len+1+1+1) (((2^len-1)*2*2+1)*2+1) (1+m).
Proof.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  unfold S,LC.
  rewrite <-I2.
  cbn.
  rw_Bin.
  2,3,4: repeat rewrite pow2_S; pose proof (Nat.pow_nonzero 2 len); lia.
  es; er.
  follow RInc.
  er.
Qed.

Lemma BigStep len m m0 m1 m2 m3:
  ((2^(len)-1)*2*2+1)*2+1+(1+m) = m0*3+1 ->
  ((2^(len+1+1)-1)*2*2+1)+(1+m0) = m1*3+1 ->
  ((2^(len+1+1+1)-1)*2*2+1)+(1+m1) = m2*3+1 ->
  ((2^(len+1+1+1+1)-1)*2*2+1)+(1+m2) = m3*3+3 ->
  S (len+1+1) 0 (m*3+3) -->+
  S (len+4+1+1) 0 (m3*3+3).
Proof.
  intros Hm0 Hm1 Hm2 Hm3.
  pose proof (Nat.pow_nonzero 2 len).
  follow10 Ov_2.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm0.
  follow Ov_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm1.
  follow Ov_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm2.
  follow Ov_0.
  follow Incs.
  1: repeat rewrite pow2_S; lia.
  rewrite Hm3.
  finish.
Qed.

Definition config '(len,m) :=
  S (len+1+1) 0 (m*3+3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(len,m) => m*5+3=(2^len-1)*8).
  2: reflexivity.
  intros [len m].
  intros Hz.
  exists (len+4,m*16+33).
  split.
  2: rewrite Nat.pow_add_r; cbn; lia.
  unfold config.
  epose proof (BigStep len m (m*2+2) (m*4+7) (m*8+16) (m*16+33) _ _ _ _) as H.
  follow10 H.
  finish.
  Unshelve.
  all: repeat rewrite pow2'_S'; lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB3RA0LB4LA3RB_2LA---2RA3LA1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive RDigits :=
| rd0(x:RDigits)
| rd1(x:RDigits)
| rd2(x:RDigits)
| rh.

Fixpoint R x :=
match x with
| rd0 x0 => [3;0] *> R x0
| rd1 x0 => [4;0] *> R x0
| rd2 x0 => [4;2] *> R x0
| rh => 0inf
end.

Fixpoint RS x :=
match x with
| rd0 x0 => rd1 x0
| rd1 x0 => rd2 x0
| rd2 x0 => rd0 (RS x0)
| rh => rd0 rh
end.

Fixpoint Rn n :=
match n with
| O => rh
| S n0 => RS (Rn n0)
end.

Lemma Rn_spec n:
  rd0 (Rn n) = Rn (n*3+1) /\
  rd1 (Rn n) = Rn (n*3+2) /\
  rd2 (Rn n) = Rn (n*3+3).
Proof.
  induction n; cbn.
  1: tauto.
  destruct IHn as [I0 [I1 I2]].
  repeat split.
  - rewrite <-I0; reflexivity.
  - rewrite <-I1; reflexivity.
  - rewrite <-I2; reflexivity.
Qed.

Lemma RInc l n:
  l {{A}}> R (Rn n) -->*
  l <{{A}} R (Rn (1+n)).
Proof.
  cbn.
  gen l.
  induction (Rn n); intros; cbn; er.
  follow IHr; er.
Qed.

Definition LC l len n := BinDec <[3;1] <[3;3] len n (0inf <* l).

Lemma LC_Inc l len n r:
  1+n<2^len ->
  LC l len (1+n) <{{A}} r -->+
  LC l len n {{A}}> r.
Proof.
  intros H.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S l len n m :=
  LC l len n <{{A}} R (Rn m).

Definition S' l len n m :=
  LC l len n <{{A}} [4;3;0] *> R (Rn m).

Lemma Inc l len n m:
  1+n<2^len ->
  S l len (1+n) m -->+
  S l len n (1+m).
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc l _ _ _ H) as HL.
  follow10 HL.
  follow RInc.
  finish.
Qed.

Lemma Incs l len n m:
  n<2^len ->
  S l len n m -->*
  S l len 0 (n+m).
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc l _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Inc' l len n m:
  1+n<2^len ->
  S' l len (1+n) m -->+
  S' l len n m.
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc l _ _ _ H) as HL.
  follow10 HL.
  es.
Qed.

Lemma Incs' l len n m:
  n<2^len ->
  S' l len n m -->*
  S' l len 0 m.
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc' l _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Opaque Rn.

Lemma Ov1 len m:
  S <[3] len 0 m -->*
  S <[1;1] len (2^len-1) (1+m).
Proof.
  unfold S,LC.
  rw_Bin.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov2 len m:
  S <[1;1] len 0 m -->*
  S <[1;3] len (2^len-1) (1+m).
Proof.
  unfold S,LC.
  rw_Bin.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov3 len m:
  S <[1;3] len 0 (m*3+1) -->+
  S' <[3] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  rewrite <-I0.
  rw_Bin.
  es.
Qed.

Lemma Ov1' len m:
  S' <[3] len 0 m -->*
  S' <[1;1] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  rw_Bin.
  es.
Qed.

Lemma Ov2' len m:
  S' <[1;1] len 0 m -->*
  S' <[1;3] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  rw_Bin.
  es.
Qed.

Lemma Ov3' len m:
  S' <[1;3] len 0 m -->*
  S <[3] (len+1) (2^(len+1)-1) (m*3+2).
Proof.
  unfold S,S',LC.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  rewrite <-I1.
  rw_Bin.
  es.
Qed.

Definition config '(len,m) :=
  S <[1;3] len 0 (m*3+1).

Lemma BigStep len m:
  config (len,m) -->+
  config (len+1,m+2^(len+1)).
Proof.
  unfold config.
  pose proof (Nat.pow_nonzero 2 len).
  pose proof (Nat.pow_nonzero 2 (len+1)).
  follow10 Ov3.
  follow Incs'.
  1: lia.
  follow Ov1'.
  follow Incs'.
  1: lia.
  follow Ov2'.
  follow Incs'.
  1: lia.
  follow Ov3'.
  follow Incs.
  1: lia.
  follow Ov1.
  follow Incs.
  1: lia.
  follow Ov2.
  follow Incs.
  1: lia.
  finish.
Qed.

Transparent Rn.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,1)%nat).
  1: unfold config,S; cbn; es.
  eapply progress_nonhalt_simple.
  intros [len m].
  eexists (_,_).
  apply BigStep.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB3RA2LB4LA3RB_2LA---3LA2RA1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive RDigits :=
| rd0(x:RDigits)
| rd1(x:RDigits)
| rd2(x:RDigits)
| rh.

Fixpoint R x :=
match x with
| rd0 x0 => [3;2] *> R x0
| rd1 x0 => [4;2] *> R x0
| rd2 x0 => [4;3] *> R x0
| rh => 0inf
end.

Fixpoint RS x :=
match x with
| rd0 x0 => rd1 x0
| rd1 x0 => rd2 x0
| rd2 x0 => rd0 (RS x0)
| rh => rd0 rh
end.

Fixpoint Rn n :=
match n with
| O => rh
| S n0 => RS (Rn n0)
end.

Lemma Rn_spec n:
  rd0 (Rn n) = Rn (n*3+1) /\
  rd1 (Rn n) = Rn (n*3+2) /\
  rd2 (Rn n) = Rn (n*3+3).
Proof.
  induction n; cbn.
  1: tauto.
  destruct IHn as [I0 [I1 I2]].
  repeat split.
  - rewrite <-I0; reflexivity.
  - rewrite <-I1; reflexivity.
  - rewrite <-I2; reflexivity.
Qed.

Lemma RInc l n:
  l {{A}}> R (Rn n) -->*
  l <{{A}} R (Rn (1+n)).
Proof.
  cbn.
  gen l.
  induction (Rn n); intros; cbn; er.
  follow IHr; er.
Qed.

Definition LC l len n := BinDec <[3;1] <[3;3] len n (0inf <* l).

Lemma LC_Inc l len n r:
  1+n<2^len ->
  LC l len (1+n) <{{A}} r -->+
  LC l len n {{A}}> r.
Proof.
  intros H.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S l len n m :=
  LC l len n <{{A}} R (Rn m).

Definition S' l len n m :=
  LC l len n <{{A}} [4;3;2] *> R (Rn m).

Lemma Inc l len n m:
  1+n<2^len ->
  S l len (1+n) m -->+
  S l len n (1+m).
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc l _ _ _ H) as HL.
  follow10 HL.
  follow RInc.
  finish.
Qed.

Lemma Incs l len n m:
  n<2^len ->
  S l len n m -->*
  S l len 0 (n+m).
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc l _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Inc' l len n m:
  1+n<2^len ->
  S' l len (1+n) m -->+
  S' l len n m.
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc l _ _ _ H) as HL.
  follow10 HL.
  es.
Qed.

Lemma Incs' l len n m:
  n<2^len ->
  S' l len n m -->*
  S' l len 0 m.
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc' l _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Opaque Rn.

Lemma Ov1 len m:
  S <[3] len 0 m -->*
  S <[1;1] len (2^len-1) (1+m).
Proof.
  unfold S,LC.
  rw_Bin.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov2 len m:
  S <[1;1] len 0 m -->*
  S <[1;3] len (2^len-1) (1+m).
Proof.
  unfold S,LC.
  rw_Bin.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov3 len m:
  S <[1;3] len 0 (m*3+1) -->+
  S' <[3] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  rewrite <-I0.
  rw_Bin.
  es.
Qed.

Lemma Ov1' len m:
  S' <[3] len 0 m -->*
  S' <[1;1] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  rw_Bin.
  es.
Qed.

Lemma Ov2' len m:
  S' <[1;1] len 0 m -->*
  S' <[1;3] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  rw_Bin.
  es.
Qed.

Lemma Ov3' len m:
  S' <[1;3] len 0 m -->*
  S <[3] (len+1) (2^(len+1)-1) (m*3+2).
Proof.
  unfold S,S',LC.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  rewrite <-I1.
  rw_Bin.
  es.
Qed.

Definition config '(len,m) :=
  S <[1;3] len 0 (m*3+1).

Lemma BigStep len m:
  config (len,m) -->+
  config (len+1,m+2^(len+1)).
Proof.
  unfold config.
  pose proof (Nat.pow_nonzero 2 len).
  pose proof (Nat.pow_nonzero 2 (len+1)).
  follow10 Ov3.
  follow Incs'.
  1: lia.
  follow Ov1'.
  follow Incs'.
  1: lia.
  follow Ov2'.
  follow Incs'.
  1: lia.
  follow Ov3'.
  follow Incs.
  1: lia.
  follow Ov1.
  follow Incs.
  1: lia.
  follow Ov2.
  follow Incs.
  1: lia.
  finish.
Qed.

Transparent Rn.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (0,1)%nat).
  1: unfold config,S; cbn; es.
  eapply progress_nonhalt_simple.
  intros [len m].
  eexists (_,_).
  apply BigStep.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB3LB---1RB2RB_2RA1LA3RB4LB3RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive RDigits :=
| rd0(x:RDigits)
| rd1(x:RDigits)
| rd2(x:RDigits)
| rh.

Fixpoint R x :=
match x with
| rd0 x0 => [3;1] *> R x0
| rd1 x0 => [4;1] *> R x0
| rd2 x0 => [4;3] *> R x0
| rh => 0inf
end.

Fixpoint RS x :=
match x with
| rd0 x0 => rd1 x0
| rd1 x0 => rd2 x0
| rd2 x0 => rd0 (RS x0)
| rh => rd0 rh
end.

Fixpoint Rn n :=
match n with
| O => rh
| S n0 => RS (Rn n0)
end.

Lemma Rn_spec n:
  rd0 (Rn n) = Rn (n*3+1) /\
  rd1 (Rn n) = Rn (n*3+2) /\
  rd2 (Rn n) = Rn (n*3+3).
Proof.
  induction n; cbn.
  1: tauto.
  destruct IHn as [I0 [I1 I2]].
  repeat split.
  - rewrite <-I0; reflexivity.
  - rewrite <-I1; reflexivity.
  - rewrite <-I2; reflexivity.
Qed.

Lemma RInc l n:
  l {{B}}> R (Rn n) -->*
  l <{{B}} R (Rn (1+n)).
Proof.
  cbn.
  gen l.
  induction (Rn n); intros; cbn; er.
  follow IHr; er.
Qed.

Definition LC l len n := BinDec <[3;2] <[3;3] len n (0inf <* l).

Lemma LC_Inc l len n r:
  1+n<2^len ->
  LC l len (1+n) <{{B}} r -->+
  LC l len n {{B}}> r.
Proof.
  intros H.
  apply LBinDec_spec with (qL:=[]) (qR:=[]); try assumption.
  es.
Qed.

Definition S l len n m :=
  LC l len n <{{B}} R (Rn m).

Definition S' l len n m :=
  LC l len n <{{B}} [4;3;1] *> R (Rn m).

Lemma Inc l len n m:
  1+n<2^len ->
  S l len (1+n) m -->+
  S l len n (1+m).
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc l _ _ _ H) as HL.
  follow10 HL.
  follow RInc.
  finish.
Qed.

Lemma Incs l len n m:
  n<2^len ->
  S l len n m -->*
  S l len 0 (n+m).
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc l _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Lemma Inc' l len n m:
  1+n<2^len ->
  S' l len (1+n) m -->+
  S' l len n m.
Proof.
  intros H.
  unfold S.
  epose proof (LC_Inc l _ _ _ H) as HL.
  follow10 HL.
  es.
Qed.

Lemma Incs' l len n m:
  n<2^len ->
  S' l len n m -->*
  S' l len 0 m.
Proof.
  gen len m.
  induction n; intros.
  1: finish.
  epose proof (Inc' l _ _ _ H) as HL.
  follow100 HL.
  follow IHn.
  1: lia.
  finish.
Qed.

Opaque Rn.

Lemma Ov1 len m:
  S <[3] len 0 m -->*
  S <[2;2] len (2^len-1) (1+m).
Proof.
  unfold S,LC.
  rw_Bin.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov2 len m:
  S <[2;2] len 0 m -->*
  S <[2;3] len (2^len-1) (1+m).
Proof.
  unfold S,LC.
  rw_Bin.
  es; er.
  follow RInc.
  er.
Qed.

Lemma Ov3 len m:
  S <[2;3] len 0 (m*3+1) -->+
  S' <[3] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  rewrite <-I0.
  rw_Bin.
  es.
Qed.

Lemma Ov1' len m:
  S' <[3] len 0 m -->*
  S' <[2;2] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  rw_Bin.
  es.
Qed.

Lemma Ov2' len m:
  S' <[2;2] len 0 m -->*
  S' <[2;3] len (2^len-1) m.
Proof.
  unfold S,S',LC.
  rw_Bin.
  es.
Qed.

Lemma Ov3' len m:
  S' <[2;3] len 0 m -->*
  S <[3] (len+1) (2^(len+1)-1) (m*3+2).
Proof.
  unfold S,S',LC.
  pose proof (Rn_spec m) as [I0 [I1 I2]].
  rewrite <-I1.
  rw_Bin.
  es.
Qed.

Definition config '(len,m) :=
  S <[2;3] len 0 (m*3+1).

Lemma BigStep len m:
  config (len,m) -->+
  config (len+1,m+2^(len+1)).
Proof.
  unfold config.
  pose proof (Nat.pow_nonzero 2 len).
  pose proof (Nat.pow_nonzero 2 (len+1)).
  follow10 Ov3.
  follow Incs'.
  1: lia.
  follow Ov1'.
  follow Incs'.
  1: lia.
  follow Ov2'.
  follow Incs'.
  1: lia.
  follow Ov3'.
  follow Incs.
  1: lia.
  follow Ov1.
  follow Incs.
  1: lia.
  follow Ov2.
  follow Incs.
  1: lia.
  finish.
Qed.

Transparent Rn.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (3,8)%nat).
  1: unfold config,S; cbn; es.
  eapply progress_nonhalt_simple.
  intros [len m].
  eexists (_,_).
  apply BigStep.
Qed.

End TM6.


