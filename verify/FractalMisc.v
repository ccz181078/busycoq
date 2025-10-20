From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import PeanoNat.
Require Import String.
Require Import List.

Lemma pow2_ge n:
  2^n>=n+1.
Proof.
  induction n; cbn; lia.
Qed.

Ltac fc H :=
  gen H; st; intro H;
  follow H; clear H.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RF_0RD0LB_1LA1RE_0RA0RB_0RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c d r :=
  l <* [1]^^a <* [0;0] <* <[1;0]^^b {{A}}> [1;0] *> [0;1]^^c *> [0]^^d *> r.

Lemma Inc1 l a b c d r:
  S1 l a b (1+c) (4+d) r -->*
  S1 l (4+a) (1+b) c d r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c d r:
  S1 l a b (n+c) (n*4+d) r -->*
  S1 l (n*4+a) (n+b) c d r.
Proof.
  gen a b c d.
  ind n Inc1.
Qed.

Definition P1 a b c d :=
  forall l r,
  l <* [0]^^a <{{A}} [1;0;1] *> [0]^^b *> r -->*
  l <* [1]^^c <* [0;0] <* <[1;0]^^d {{A}}> r.

Lemma P1_S a b d:
  P1 a (1+b) (1+b) d ->
  P1 (a+1+a) (1+b+2+d*4) (3+d*4+b) (d+d).
Proof.
  remember (d*4) as d4.
  unfold P1.
  intros HP1 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  es; er.
  follow HP1.
  mid (S1 l (1+b) d d d4 r).
  1: es.
  follow (Incs1 d l (1+b) d 0 0 r).
  subst.
  unfold S1.
  es.
Qed.

Lemma P1_n n:
  P1 (2^n*2-1) (1+(2^n*4+n*2-3)) (1+(2^n*4+n*2-3)) (2^n).
Proof.
  induction n.
  1: unfold P1; es.
  cbn[Nat.pow].
  eapply P1_S in IHn.
  applys_eq IHn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P1_n n 0inf 0inf) as HP1.
  unfold P1 in HP1.
  do 2 rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC---_1LD0RF_0LA0LD_0LC0RA_1RC1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* [1]^^a <* [0] <* <[0;1]^^b {{C}}> [0] *> [1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a (1+b) c r -->*
  S1 l (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 l a b c r:
  S1 l a b c r -->*
  S1 l (b+a) 0 (b+c) r.
Proof.
  gen a c.
  ind b Inc1.
Qed.

Definition P1 a b c d :=
  forall l r k,
  l <* [0] <* <[0;1]^^k <* [0]^^a <* [1] {{B}}> [0]^^b *> r -->*
  l <* [1]^^c <* [0] <* <[0;1]^^(d+k) {{C}}> r.

Lemma P1_S c d:
  P1 (1+d*2) (2+c+d*2) c (2+d*2) ->
  P1 ((1+d*2)+3+(1+d*2)) ((2+c+d*2)+2+(2+c+d*2)) (c+c) (6+d*2+d*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  repeat rewrite lpow_add,Str_app_assoc.
  epose proof (HP1 _ _ O) as I1.
  repeat rewrite lpow_add,Str_app_assoc in I1.
  follow I1. clear I1.
  mid (S1 (l<*[0]<*<[0;1]^^k<*[0]^^(2+(1+d*2))) c (2+d*2) 0 ([0]^^(1+(2+c+d*2))*>r)).
  1: es.
  follow Incs1.
  unfold S1.
  do 2 (er; sr).
  do 2 step1.
  epose proof (HP1 _ _ k) as I1.
  repeat rewrite lpow_add,Str_app_assoc in I1.
  follow I1. clear I1.
  st.
  er. sr.
  step1.
  epose proof (HP1 _ _ (4+d*2+k)) as I1.
  gen I1.
  st.
  intros I1.
  follow I1.
  es.
Qed.

Lemma P1_n n:
  P1 (2^n*4-3) (2^n*5-2) (2^n) (2^n*4-2).
Proof.
  induction n.
  1: unfold P1; es.
  cbn[Nat.pow].
  epose proof (P1_S (2^n) (2^n*2-2)) as I1.
  applys_eq I1; try lia.
  applys_eq IHn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P1_n n 0inf 0inf O) as HP1.
  unfold P1 in HP1.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    cbn.
    simpl_tape.
    do 2 rewrite lpow_all0 by solve_const0_eq.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1LD0RE_0LA0LD_1RC1RF_1RB0RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* [1]^^a <* [0] <* <[0;1]^^b {{C}}> [0] *> [1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a (1+b) c r -->*
  S1 l (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 l a b c r:
  S1 l a b c r -->*
  S1 l (b+a) 0 (b+c) r.
Proof.
  gen a c.
  ind b Inc1.
Qed.

Definition P1 a b c d :=
  forall l r k,
  l <* [0] <* <[0;1]^^k <* [0]^^a <* [1] {{B}}> [0]^^b *> r -->*
  l <* [1]^^c <* [0] <* <[0;1]^^(d+k) {{C}}> r.

Lemma P1_S c d:
  P1 (1+d*2) (2+c+d*2) c (2+d*2) ->
  P1 ((1+d*2)+3+(1+d*2)) ((2+c+d*2)+2+(2+c+d*2)) (c+c) (6+d*2+d*2).
Proof.
  unfold P1.
  intros HP1 l r k.
  repeat rewrite lpow_add,Str_app_assoc.
  epose proof (HP1 _ _ O) as I1.
  repeat rewrite lpow_add,Str_app_assoc in I1.
  follow I1. clear I1.
  mid (S1 (l<*[0]<*<[0;1]^^k<*[0]^^(2+(1+d*2))) c (2+d*2) 0 ([0]^^(1+(2+c+d*2))*>r)).
  1: es.
  follow Incs1.
  unfold S1.
  do 2 (er; sr).
  do 2 step1.
  epose proof (HP1 _ _ k) as I1.
  repeat rewrite lpow_add,Str_app_assoc in I1.
  follow I1. clear I1.
  st.
  er. sr.
  step1.
  epose proof (HP1 _ _ (4+d*2+k)) as I1.
  gen I1.
  st.
  intros I1.
  follow I1.
  es.
Qed.

Lemma P1_n n:
  P1 (2^n*4-3) (2^n*5-2) (2^n) (2^n*4-2).
Proof.
  induction n.
  1: unfold P1; es.
  cbn[Nat.pow].
  epose proof (P1_S (2^n) (2^n*2-2)) as I1.
  applys_eq I1; try lia.
  applys_eq IHn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P1_n n 0inf 0inf O) as HP1.
  unfold P1 in HP1.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    cbn.
    simpl_tape.
    do 2 rewrite lpow_all0 by solve_const0_eq.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC1LB_0LC1LD_1LE0LC_1RF1LF_---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* [1]^^a <* [0] <* [1]^^b {{B}}> [1;0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (2+a) b (1+c) r -->*
  S1 l a (4+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n*2+a) b (n+c) r -->*
  S1 l a (n*4+b) c r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition P1 a b c d :=
  forall l r,
  l <* [0]^^a <* [1] <{{C}} [0]^^b *> r -->*
  l <* [1] <* [0]^^c <* [1]^^d <* [0] {{C}}> r.

Lemma P1_S a c d:
  P1 a (1+c) c (2+d*2) ->
  P1 (a+a) ((1+c)+1) (1+c) (4+d*4).
Proof.
  unfold P1.
  intros HP1 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  st.
  do 2 (er; sr).
  follow HP1.
  mid (S1 (l<*[1]<*[0]^^c) (d*2) 4 d ([0]*>r)).
  1: es.
  epose proof (Incs1 d _ O _ O _) as I1.
  follow I1. clear I1.
  es.
Qed.

Lemma P1_n n:
  P1 (2^n*2) (2+n) (1+n) (2+(2^n-1)*2).
Proof.
  induction n.
  1: unfold P1; es.
  cbn[Nat.pow].
  apply P1_S in IHn.
  applys_eq IHn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P1_n n 0inf 0inf) as HP1.
  unfold P1 in HP1.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    cbn.
    simpl_tape.
    do 2 rewrite lpow_all0 by solve_const0_eq.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC1RD_0RD1LA_1RE1RF_---0RA_0RD0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[1;0]^^a <* [1] <* <[1;0]^^(1+b) {{A}}> [0;1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (1+a) b (1+c) r -->*
  S1 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n+a) b (n+c) r -->*
  S1 l a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition P1 a b c d :=
  forall l r,
  l <* [0]^^a <{{A}} [0]^^b *> r -->*
  l <* [0] <* [1]^^c <* <[1;0]^^d {{A}}> r.

Lemma P1_S c d:
  P1 (3+d*2) c c (1+d) ->
  P1 (3+d*2+2+d*2) (c+1) (1+c) (2+d*2).
Proof.
  unfold P1.
  intros HP1 l r.
  repeat rewrite lpow_add,Str_app_assoc.
  follow HP1.
  st.
  do 2 (er; sr).
  epose proof (HP1 _ _) as I1.
  gen I1. st. intro I1.
  follow I1. clear I1.
  mid (S1 (l<*[0]<*[1]^^c) d 1 d r).
  1: es.
  epose proof (Incs1 d _ O _ O _) as I1.
  follow I1. clear I1.
  es.
Qed.

Lemma P1_n n:
  P1 (3+(2^n-1)*2) n n (1+(2^n-1)).
Proof.
  induction n.
  1: unfold P1; es.
  cbn[Nat.pow].
  apply P1_S in IHn.
  applys_eq IHn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P1_n n 0inf 0inf) as HP1.
  unfold P1 in HP1.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    cbn.
    simpl_tape.
    do 2 rewrite lpow_all0 by solve_const0_eq.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC0LB_0RD1RF_1LE0LA_1LD0RE_---0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[1;0]^^a <{{D}} [1;1]^^b *> [0;1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (1+a) b (1+c) r -->*
  S1 l a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n+a) b (n+c) r -->*
  S1 l a (n*2+b) c r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.


Fixpoint LC(n:nat):side :=
match n with
| O => 0inf
| S n0 => LC n0 <* <[1;1] <* <[1;0]^^(2^n0)
end.

Lemma LInc n r:
  LC n <{{B}} [0;0] *> r -->*
  LC (S n) {{C}}> r.
Proof.
  gen r.
  induction n; intros; cbn[LC] in *.
  1: es.
  cbn[Nat.pow].
  remember (2^n-1) as v1.
  rewrite Nat.mul_comm.
  replace (2^n) with (1+v1) in * by lia.
  es; er.
  follow IHn.
  mid (S1 (LC n<*<[1;1]) v1 3 v1 r).
  1: es.
  follow (Incs1 v1 (LC n<*<[1;1]) 0 3 0 r).
  unfold S1.
  es; er.
  follow IHn.
  es.
Qed.

Definition S' n := LC n {{C}}> [0;1] *> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 1).
  1: unfold S'; esx.
  eapply progress_nonhalt_simple.
  intros n.
  exists (S n).
  unfold S'.
  er.
  follow LInc.
  es.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC---_1RA1LC_0RE1RD_1LF1LE_0LF0LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[1]^^a <* [0] <* <[1]^^b {{D}}> [0;0] *> [1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a (2+b) c r -->*
  S1 l (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l a (n*2+b) c r -->*
  S1 l (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 l a b c r :=
  l <* <[1]^^a <* [0] <* <[1]^^b {{D}}> [0;1] *> [1]^^c *> r.

Lemma Inc2 l a b c r:
  S2 l a (2+b) c r -->*
  S2 l (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs2 n l a b c r:
  S2 l a (n*2+b) c r -->*
  S2 l (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc2.
Qed.

Definition P1 a :=
  forall r,
  0inf <* <[1;0] <* [1]^^a {{D}}> [0;0] *> r -->+
  0inf <* <[1;0] <* [1]^^(2+a*2) {{D}}> r.

Lemma P1_S a:
  P1 a ->
  P1 (2+a*2).
Proof.
  unfold P1.
  intros HP1 r.
  mid01 (S1 0inf 1 ((1+a)*2+0) 0 r).
  1: es.
  follow Incs1.
  unfold S1.
  do 2 (er; sr).
  follow100 HP1.
  mid (S2 0inf 1 ((1+a)*2+0) (1+a) r).
  1: es.
  follow Incs2.
  unfold S2.
  do 2 (er; sr).
  follow100 HP1.
  replace (a*2*2) with (a+a+a*2) by lia.
  es.
Qed.

Definition S' a :=
  0inf <* <[1;0] <* [1]^^a {{D}}> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 1).
  1: unfold S'; esx.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold S'.
  intros n HP1.
  eexists; split.
  1: applys_eq (HP1 0inf); st; reflexivity.
  apply P1_S,HP1.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB0LB_0LC0LE_1RD0LB_0RE0RD_1RA1LF_1LC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{A}}> r) (at level 30).

Definition P1 a b c d :=
  forall l r k,
  l <* [0]^^a <* <[0;1;0;1] <* [0]^^(4+k) |> [0]^^b *> r -->*
  l <* <[0;1]^^c <* <[0;0;0;0;0;1;0;1] <* [0]^^(d+k) |> r.

Lemma P1_S1 a b:
  P1 a (1+b*2) b (1+a) ->
  P1 (a+4+a) (1+b*2+6+1+b*2) (4+b+b) (4+a+a).
Proof.
  unfold P1.
  intros HP1 l r k.
  st.
  epose proof (HP1 _ _ k) as I1.
  fc I1.
  do 7 (er; sr).
  do 22 step1.
  epose proof (HP1 _ _ O) as I1.
  fc I1.
  do 4 (er; sr).
  do 2 step1.
  epose proof (HP1 _ _ (3+a+k)) as I1.
  fc I1.
  es.
Qed.

Lemma P1_S0 a b:
  P1 a (b*2) b a ->
  P1 (a+4+a) (b*2+9+b*2) (4+b+b) (5+a+a).
Proof.
  unfold P1.
  intros HP1 l r k.
  st.
  epose proof (HP1 _ _ k) as I1.
  fc I1.
  do 7 (er; sr).
  rewrite <-lpow_shift21.
  do 22 step1.
  epose proof (HP1 _ _ O) as I1.
  fc I1.
  do 8 (er; sr).
  do 2 step1.
  epose proof (HP1 _ _ (5+a+k)) as I1.
  fc I1.
  es.
Qed.

Definition P2 a c d :=
  forall l k,
  l <* [0]^^a <* <[0;1;0;1;0;0;1;0;0;1] <* [0]^^(k) |> 0inf -->*
  l <{{C}} [0]^^c *> [1;1;0]^^3 *> [1]^^(k+d) *> 0inf.

Lemma P2_S0 a b d0:
  P2 (a) (6+b*2) (1+d0) ->
  P1 (a) (b*2) b a ->
  P2 (a+4+a) (14+b*2+b*2) (10+d0+d0).
Proof.
  unfold P1,P2.
  intros HP2 HP1 l k.
  st.
  follow HP2.
  st.
  rewrite <-lpow_shift21.
  do 22 step1.
  epose proof (HP1 _ _ O) as I1.
  fc I1.
  do 12 (er; sr).
  do 2 step1.
  epose proof (HP2 _ (9+d0+k)) as I1.
  replace (9+d0+k+(1+d0)) with (10+k+d0+d0) in I1 by lia.
  fc I1.
  es.
Qed.

Lemma P2_S1 a b d0:
  P2 (a) (6+b*2) (1+d0) ->
  P1 (a) (1+b*2) b (1+a) ->
  P2 (a+4+a) (14+b*2+b*2) (4+d0+d0).
Proof.
  unfold P1,P2.
  intros HP2 HP1 l k.
  st.
  follow HP2.
  st.
  do 22 step1.
  epose proof (HP1 _ _ O) as I1.
  fc I1.
  do 4 (er; sr).
  do 2 step1.
  epose proof (HP2 _ (3+d0+k)) as I1.
  replace (3+d0+k+(1+d0)) with (4+k+d0+d0) in I1 by lia.
  fc I1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro a b d0 n
  (Hn:n<=d0)
  (HP2:P2 a (6+b*2) (1+d0))
  (HP1:P1 a (b*2) b a):
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  1: eapply (P_intro 4 0 9); try lia; unfold P1,P2; es.
  inverts IHn.
  epose proof (P2_S0 _ _ _ HP2 HP1) as HP2'.
  epose proof (P1_S0 _ _ HP1) as HP1'.
  epose proof (P1_S1 (a*2+4) (b*2+4)) as HP1''.
  epose proof (P2_S1 (a*2+4) (b*2+4) (d0*2+9)) as HP2''.
  eapply (P_intro (a*4+12) (b*4+12) (d0*4+21)).
  - lia.
  - applys_eq HP2''; try lia.
    + applys_eq HP2'; lia.
    + applys_eq HP1'; lia.
  - applys_eq HP1''; try lia.
    applys_eq HP1'; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP2 0inf 6) as HP2.
  unfold P1 in HP1.
  rewrite lpow_all0 in HP2 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP2; finish.
    es.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC---_1RD1LE_1RC0LD_0RF0RE_1LF1LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} r) (at level 30).

Definition P1 a b c d :=
  forall l r k,
  l <* [0]^^a <* <[1;1] <* [0]^^(2+k) |> [0]^^b *> r -->*
  l <| [0]^^c *> [1]^^(2+k+d) *> r.

Lemma P1_S a c:
  P1 a (c*2) (2+c*2) a ->
  P1 (a+5+a+1) (c*2+2+c*2) (4+c*2+c*2) (6+a+a).
Proof.
  unfold P1.
  intros HP1 l r k.
  st.
  epose proof (HP1 _ _ k) as I1.
  fc I1.
  do 6 (er; sr).
  rewrite <-(lpow_rotate [0] 0).
  do 11 step1.
  epose proof (HP1 _ _ O) as I1.
  rewrite <-lpow_shift1.
  fc I1.
  do 4 (er; sr).
  epose proof (HP1 _ _ (6+a+k)) as I1.
  replace (2+(6+a+k)+a) with (8+k+a+a) in I1 by lia.
  fc I1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro a c n
  (Hn:n<=a)
  (HP1:P1 a (c*2) (2+c*2) a):
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  1: eapply (P_intro 4 1); try lia; unfold P1; es.
  inverts IHn.
  apply P1_S in HP1.
  eapply (P_intro (a*2+6) (c*2+1)).
  - lia.
  - applys_eq HP1; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP1 0inf 0inf O) as HP1.
  do 2 rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC---_0RD0RC_1LD1RA_1RA0LF_0LA0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* [0]^^a <* [1;1] <* [0]^^b {{C}}> [0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (1+a) b (2+c) r -->*
  S1 l a (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n+a) b (n*2+c) r -->*
  S1 l a (n*3+b) c r.
Proof.
  gen l a b c r.
  ind n Inc1.
Qed.

Notation w := <[0;0;0;0;1;1;0;0;0;1;1;1;0;0;1;1;1;1;1;1;1;1;1;0].

Definition P1 a b c m :=
  forall l r,
  l <* [0]^^21 <{{F}} [0]^^a *> r -->*
  S1 (l <* <[1;1]^^c <* w <* m) 0 b 0 r.

Definition P2 c1 c2 m bm :=
  forall l r b,
  b mod 2 = bm ->
  S1 (l <* w <* m) 0 b c1 r -->*
  l <* <[1;1] <* [0]^^21 <{{F}} [0]^^(c2+b) *> [1]^^9 *> r.

Lemma P1_O: P1 54 49 0 [].
Proof.
  unfold P1.
  intros.
  eapply without_counter with (n:=2037).
  eapply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma P2_O: P2 12 6 [] 1.
Proof.
  unfold P2,S1.
  intros.
  replace b with (1+b/2*2) by lia.
  es.
Qed.

Definition P3 c1 c2 m bm :=
  forall l r b,
  b mod 2 = bm ->
  S1 (l <* w <* m <* [1;1]) 0 b c1 r -->*
  l <* <[1;1] <* [0]^^21 <{{F}} [0]^^(c2+b) *> [1]^^9 *> r.

Lemma P3_O: P3 10 6 [] 1.
Proof.
  unfold P3,S1.
  intros.
  replace b with (1+b/2*2) by lia.
  es.
Qed.

Lemma P1_S a b c m c1 c2 bm c3 a0:
  P1 a b c m ->
  P2 c1 c2 m bm ->
  c2+b=a+1 ->
  6<=b ->
  b mod 2 = bm ->
  a0+c3=(b-6) ->
  P1 (a+c1+8+a0*2) (a0*3+22) (1+c+c) ([0]^^c3++[1;1]++m).
Proof.
  unfold P1,P2,S1.
  intros HP1 HP2 Ha Hb Hbm Ha0 l r.
  st.
  follow HP1.
  follow HP2.
  rewrite Ha.
  st.
  follow HP1.
  replace b with (6+(b-6)) by lia.
  er.
  mid (S1 (l <* <[1;1]^^(1+c+c) <* w <* m <* <[1;1]) ((b-6)) 22 (a0*2) r).
  1: es.
  epose proof (Incs1 a0 _ c3 _ 0 _) as I1.
  follow I1.
  es.
Qed.

Lemma P2_S c1 c2 bm c3 m bm':
  P3 c1 c2 m bm ->
  ((c3 + bm') mod 2 = bm) ->
  P2 (c3*2+c1) (c2+c3*3) ([0]^^c3++[1;1]++m) bm'.
Proof.
  unfold P2,P3.
  intros HP3 Hb l r b Hb'.
  mid (S1 ([1;1]*>m*>w*>l) (c3+0) b (c3*2+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  1: lia.
  es.
Qed.

Lemma P3_S c1 c2 bm c3 m bm':
  P3 c1 c2 m bm ->
  ((c3 + bm') mod 2 = bm) ->
  P3 (2+c3*2+c1) (6+c2+c3*3) ([0]^^(2+c3)++[1;1]++m) bm'.
Proof.
  unfold P3.
  intros HP3 Hb l r b Hb'.
  mid (S1 ([1;1]*>m*>w*>l) (c3+0) (6+b) (c3*2+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  1: lia.
  es.
Qed.

Definition P1' b c m :=
  c0 -->*
  S1 (0inf <* <[1;1]^^c <* w <* m) 0 b 0 0inf.

Lemma P1'_O: P1' 49 0 [].
Proof.
  unfold P1',S1.
  esx.
Qed.

Lemma P1'_S a b c m c1 c2 bm c3 a0:
  P1' b c m ->
  P1 a b c m ->
  P2 c1 c2 m bm ->
  c2+b=a+1 ->
  6<=b ->
  b mod 2 = bm ->
  a0+c3=(b-6) ->
  P1' (a0*3+22) (1+c+c) ([0]^^c3++[1;1]++m).
Proof.
  unfold P1,P1',P2,S1.
  intros HP1' HP1 HP2 Ha Hb Hbm Ha0.
  st.
  follow HP1'.
  epose proof (HP2 _ 0inf _) as HP2.
  rewrite lpow_all0 in HP2 by solve_const0_eq.
  follow HP2.
  rewrite Ha.
  st.
  follow HP1.
  replace b with (6+(b-6)) by lia.
  do 220 step1.
  mid (S1 (0inf <* <[1;1]^^(1+c+c) <* w <* m <* <[1;1]) ((b-6)) 22 (a0*2) 0inf).
  1: unfold S1.
  1: rewrite (lpow_all0 [0]) by solve_const0_eq.
  1: es.
  epose proof (Incs1 a0 _ c3 _ 0 _) as I1.
  follow I1.
  es.
Qed.


Definition P4 b c m c1 c2 bm :=
  P1' (6+b) c m /\ P1 (5+b+c2) (6+b) c m /\ P2 (6+c1) c2 m bm /\ P3 (4+c1) c2 m bm.

Lemma P4_O:
  P4 43 0 [] 6 6 1.
Proof.
  unfold P4; repeat split.
  - apply P1'_O.
  - apply P1_O.
  - apply P2_O.
  - apply P3_O.
Qed.

Ltac flia := repeat (lia||f_equal).

Lemma P4_S b c m c1 c2 bm (c3 a0:nat):
  P4 b c m c1 c2 bm ->
  b mod 2 = bm ->
  a0+c3 = b ->
  c1 = c3*2+2 ->
  2<=c3 ->
  P4 (16+a0*3) (1+c*2) ([0]^^c3++[1;1]++m) (c3*4) (c2+c3*3) ((c3+bm) mod 2).
Proof.
  intros [HP1' [HP1 [HP2 HP3]]] Hb Ha0 Hc3 Hc3'.
  unshelve epose proof (P1'_S _ _ _ _ _ _ _ c3 a0 HP1' HP1 HP2 _ _ _ _) as I1'.
  1,2,3,4: lia.
  unshelve epose proof (P1_S _ _ _ _ _ _ _ c3 a0 HP1 HP2 _ _ _ _) as I1.
  1,2,3,4: lia.
  unshelve epose proof (P2_S _ _ _ c3 _ ((c3+bm) mod 2) HP3 _) as I2.
  1: lia.
  unshelve epose proof (P3_S _ _ _ (c3-2) _ ((c3+bm) mod 2) HP3 _) as I3.
  1: lia.
  repeat split.
  - applys_eq I1'; flia.
  - applys_eq I1; flia.
  - applys_eq I2; flia.
  - applys_eq I3; flia.
Qed.

Inductive P: nat->Prop :=
| P_intro b c m c1 c2 bm a0 c3 n:
  P4 b c m c1 c2 bm ->
  b mod 2 = bm ->
  a0+c3 = b ->
  c1 = c3*2+2 ->
  2<=c3 ->
  n<=c ->
  c3*10<=20+a0 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (c3:=2) (a0:=41).
    1: apply P4_O.
    all: lia.
  - inverts IHn.
    eapply P4_S with (a0:=a0) (c3:=c3) in H; try lia.
    eapply P_intro with (c3:=c3*2-1) (a0:=16+a0*3-(c3*2-1)).
    1: apply H.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  destruct H as [HP1' _].
  eexists _,_; split.
  - apply HP1'.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC---_0RD0RC_1LD1RE_0RA1LF_1RE0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* [0]^^a <* [1;1] <* [0]^^b {{C}}> [0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (1+a) b (2+c) r -->*
  S1 l a (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n+a) b (n*2+c) r -->*
  S1 l a (n*3+b) c r.
Proof.
  gen l a b c r.
  ind n Inc1.
Qed.

Notation w := <[0;0;0;0;1;1;0;0;0;1;1;1;0;0;1;1;1;1;1;1;1;1;1;0].

Definition P1 a b c m :=
  forall l r,
  l <* [0]^^21 <{{A}} [0]^^a *> r -->*
  S1 (l <* <[1;1]^^c <* w <* m) 0 b 0 r.

Definition P2 c1 c2 m bm :=
  forall l r b,
  b mod 2 = bm ->
  S1 (l <* w <* m) 0 b c1 r -->*
  l <* <[1;1] <* [0]^^21 <{{A}} [0]^^(c2+b) *> [1]^^9 *> r.

Lemma P1_O: P1 54 49 0 [].
Proof.
  unfold P1.
  intros.
  eapply without_counter with (n:=2139).
  eapply multistep_c_spec; vm_compute; reflexivity.
Qed.

Lemma P2_O: P2 12 6 [] 1.
Proof.
  unfold P2,S1.
  intros.
  replace b with (1+b/2*2) by lia.
  es.
Qed.

Definition P3 c1 c2 m bm :=
  forall l r b,
  b mod 2 = bm ->
  S1 (l <* w <* m <* [1;1]) 0 b c1 r -->*
  l <* <[1;1] <* [0]^^21 <{{A}} [0]^^(c2+b) *> [1]^^9 *> r.

Lemma P3_O: P3 10 6 [] 1.
Proof.
  unfold P3,S1.
  intros.
  replace b with (1+b/2*2) by lia.
  es.
Qed.

Lemma P1_S a b c m c1 c2 bm c3 a0:
  P1 a b c m ->
  P2 c1 c2 m bm ->
  c2+b=a+1 ->
  6<=b ->
  b mod 2 = bm ->
  a0+c3=(b-6) ->
  P1 (a+c1+8+a0*2) (a0*3+22) (1+c+c) ([0]^^c3++[1;1]++m).
Proof.
  unfold P1,P2,S1.
  intros HP1 HP2 Ha Hb Hbm Ha0 l r.
  st.
  follow HP1.
  follow HP2.
  rewrite Ha.
  st.
  follow HP1.
  replace b with (6+(b-6)) by lia.
  er.
  mid (S1 (l <* <[1;1]^^(1+c+c) <* w <* m <* <[1;1]) ((b-6)) 22 (a0*2) r).
  1: es.
  epose proof (Incs1 a0 _ c3 _ 0 _) as I1.
  follow I1.
  es.
Qed.

Lemma P2_S c1 c2 bm c3 m bm':
  P3 c1 c2 m bm ->
  ((c3 + bm') mod 2 = bm) ->
  P2 (c3*2+c1) (c2+c3*3) ([0]^^c3++[1;1]++m) bm'.
Proof.
  unfold P2,P3.
  intros HP3 Hb l r b Hb'.
  mid (S1 ([1;1]*>m*>w*>l) (c3+0) b (c3*2+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  1: lia.
  es.
Qed.

Lemma P3_S c1 c2 bm c3 m bm':
  P3 c1 c2 m bm ->
  ((c3 + bm') mod 2 = bm) ->
  P3 (2+c3*2+c1) (6+c2+c3*3) ([0]^^(2+c3)++[1;1]++m) bm'.
Proof.
  unfold P3.
  intros HP3 Hb l r b Hb'.
  mid (S1 ([1;1]*>m*>w*>l) (c3+0) (6+b) (c3*2+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  1: lia.
  es.
Qed.

Definition P1' b c m :=
  c0 -->*
  S1 (0inf <* <[1;1]^^c <* w <* m) 0 b 0 0inf.

Lemma P1'_O: P1' 49 0 [].
Proof.
  unfold P1',S1.
  esx.
Qed.

Lemma P1'_S a b c m c1 c2 bm c3 a0:
  P1' b c m ->
  P1 a b c m ->
  P2 c1 c2 m bm ->
  c2+b=a+1 ->
  6<=b ->
  b mod 2 = bm ->
  a0+c3=(b-6) ->
  P1' (a0*3+22) (1+c+c) ([0]^^c3++[1;1]++m).
Proof.
  unfold P1,P1',P2,S1.
  intros HP1' HP1 HP2 Ha Hb Hbm Ha0.
  st.
  follow HP1'.
  epose proof (HP2 _ 0inf _) as HP2.
  rewrite lpow_all0 in HP2 by solve_const0_eq.
  follow HP2.
  rewrite Ha.
  st.
  follow HP1.
  replace b with (6+(b-6)) by lia.
  do 220 step1.
  mid (S1 (0inf <* <[1;1]^^(1+c+c) <* w <* m <* <[1;1]) ((b-6)) 22 (a0*2) 0inf).
  1: unfold S1.
  1: rewrite (lpow_all0 [0]) by solve_const0_eq.
  1: es.
  epose proof (Incs1 a0 _ c3 _ 0 _) as I1.
  follow I1.
  es.
Qed.


Definition P4 b c m c1 c2 bm :=
  P1' (6+b) c m /\ P1 (5+b+c2) (6+b) c m /\ P2 (6+c1) c2 m bm /\ P3 (4+c1) c2 m bm.

Lemma P4_O:
  P4 43 0 [] 6 6 1.
Proof.
  unfold P4; repeat split.
  - apply P1'_O.
  - apply P1_O.
  - apply P2_O.
  - apply P3_O.
Qed.

Ltac flia := repeat (lia||f_equal).

Lemma P4_S b c m c1 c2 bm (c3 a0:nat):
  P4 b c m c1 c2 bm ->
  b mod 2 = bm ->
  a0+c3 = b ->
  c1 = c3*2+2 ->
  2<=c3 ->
  P4 (16+a0*3) (1+c*2) ([0]^^c3++[1;1]++m) (c3*4) (c2+c3*3) ((c3+bm) mod 2).
Proof.
  intros [HP1' [HP1 [HP2 HP3]]] Hb Ha0 Hc3 Hc3'.
  unshelve epose proof (P1'_S _ _ _ _ _ _ _ c3 a0 HP1' HP1 HP2 _ _ _ _) as I1'.
  1,2,3,4: lia.
  unshelve epose proof (P1_S _ _ _ _ _ _ _ c3 a0 HP1 HP2 _ _ _ _) as I1.
  1,2,3,4: lia.
  unshelve epose proof (P2_S _ _ _ c3 _ ((c3+bm) mod 2) HP3 _) as I2.
  1: lia.
  unshelve epose proof (P3_S _ _ _ (c3-2) _ ((c3+bm) mod 2) HP3 _) as I3.
  1: lia.
  repeat split.
  - applys_eq I1'; flia.
  - applys_eq I1; flia.
  - applys_eq I2; flia.
  - applys_eq I3; flia.
Qed.

Inductive P: nat->Prop :=
| P_intro b c m c1 c2 bm a0 c3 n:
  P4 b c m c1 c2 bm ->
  b mod 2 = bm ->
  a0+c3 = b ->
  c1 = c3*2+2 ->
  2<=c3 ->
  n<=c ->
  c3*10<=20+a0 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (c3:=2) (a0:=41).
    1: apply P4_O.
    all: lia.
  - inverts IHn.
    eapply P4_S with (a0:=a0) (c3:=c3) in H; try lia.
    eapply P_intro with (c3:=c3*2-1) (a0:=16+a0*3-(c3*2-1)).
    1: apply H.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  destruct H as [HP1' _].
  eexists _,_; split.
  - apply HP1'.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RF_1RD0RB_1LE0RC_0LA0LD_---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[0;1]^^a <* <[0;0;1;0;1;1] <* <[0;1]^^b {{D}}> [0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (1+a) b (4+c) r -->*
  S1 l a (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n+a) b (n*4+c) r -->*
  S1 l a (n*3+b) c r.
Proof.
  gen l a b c r.
  ind n Inc1.
Qed.

Definition P1 a b c m :=
  forall l r,
  l <* <[0;0;1;0] <{{A}} [0]^^a *> r -->*
  l <* <[1;1;1;0;0;0;1;1]^^c <* m <* <[0;0;1;0;1;1] <* <[0;1]^^b <* [0] {{C}}> r.

Definition P2 c1 c2 m :=
  forall l r b,
  l <* m <* <[0;0;1;0;1;1] <* <[0;1]^^b <* [0] {{C}}> [0]^^c1 *> r -->*
  l <* <[1;1;1;0;0;0;1;1] <* <[0;0;1;0] <{{A}} [0]^^(c2+b*2) *> [1;0;1;0;1] *> r.

Notation w1 := <[1;1;1;0;0;0;1;0;0;1].

Lemma P1_O: P1 29 8 0 w1.
Proof.
  unfold P1.
  es.
Qed.

Lemma P2_O: P2 13 13 w1.
Proof.
  unfold P2,S1.
  es.
Qed.

Definition P3 c1 c2 m :=
  forall l r b,
  l <* m <* <[0;0;1;0;1;1]^^2 <* <[0;1]^^b {{D}}> [0]^^c1 *> r -->*
  l <* <[1;1;1;0;0;0;1;1] <* <[0;0;1;0] <{{A}} [0]^^(c2+b*2) *> [1;0;1;0;1] *> r.

Lemma P3_O: P3 12 17 w1.
Proof.
  unfold P3,S1.
  es.
Qed.

Lemma P1_S a b c m c1 c2 c3 a0:
  P1 a b c m ->
  P2 c1 c2 m ->
  c2+b*2=a ->
  a0+c3+3=b ->
  P1 (a+c1+8+a0*4+3) (a0*3+8) (1+c+c) ([1;0]^^c3++[1;1;0;1;0;0]++m).
Proof.
  unfold P1,P2,S1.
  intros HP1 HP2 Ha Ha0 l r.
  st.
  follow HP1.
  follow HP2.
  rewrite Ha.
  follow HP1.
  replace b with (2+(b-2)) by lia.
  mid (S1 (l <* <[1;1;1;0;0;0;1;1]^^(1+c+c) <* m <* <[0;0;1;0;1;1]) ((b-2)) 6 (a0*4+3) r).
  1: es.
  epose proof (Incs1 a0 _ (1+c3) _ 3 _) as I1.
  follow I1.
  es.
Qed.

Lemma P2_S c1 c2 c3 m:
  P3 c1 c2 m ->
  P2 (1+c3*4+c1) (c2+c3*6+2) ([1;0]^^c3++[1;1;0;1;0;0]++m).
Proof.
  unfold P2,P3.
  intros HP3 l r b.
  mid (S1 ([1;1;0;1;0;0]*>m*>l) (c3+0) (1+b) (c3*4+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  finish.
Qed.

Lemma P3_S c1 c2 c3 m:
  P3 c1 c2 m ->
  P3 (8+c3*4+c1) (c2+c3*6+18) ([1;0]^^(2+c3)++[1;1;0;1;0;0]++m).
Proof.
  unfold P3.
  intros HP3 l r b.
  mid (S1 ([1;1;0;1;0;0]*>m*>l) (c3+0) (9+b) (c3*4+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  finish.
Qed.

Definition P1' b c m :=
  c0 -->*
  0inf <* <[1;1;1;0;0;0;1;1]^^c <* m <* <[0;0;1;0;1;1] <* <[0;1]^^b <* [0] {{C}}> 0inf.

Lemma P1'_O: P1' 8 0 w1.
Proof.
  unfold P1',S1.
  esx.
Qed.

Lemma P1'_S a b c m c1 c2 c3 a0:
  P1' b c m ->
  P1 a b c m ->
  P2 c1 c2 m ->
  c2+b*2=a ->
  a0+c3+3=b ->
  P1' (a0*3+8) (1+c+c) ([1;0]^^c3++[1;1;0;1;0;0]++m).
Proof.
  unfold P1',P1,P2,S1.
  intros HP1' HP1 HP2 Ha Ha0.
  eapply evstep_trans.
  1:{
  st.
  follow HP1'.
  epose proof (HP2 _ 0inf _) as HP2.
  rewrite lpow_all0 in HP2 by solve_const0_eq.
  follow HP2.
  rewrite Ha.
  follow HP1.
  replace b with (2+(b-2)) by lia.
  mid (S1 (0inf <* <[1;1;1;0;0;0;1;1]^^(1+c+c) <* m <* <[0;0;1;0;1;1]) ((b-2)) 6 (a0*4+3) 0inf).
  1: unfold S1.
  1: rewrite (lpow_all0 [0]) by solve_const0_eq.
  1: es.
  epose proof (Incs1 a0 _ (1+c3) _ 3 _) as I1.
  follow I1.
  finish.
  }
  remember 0inf as r'.
  es.
Qed.

Definition P4 b c m c1 c2 :=
  P1' b c m /\
  P1 (c2+b*2) b c m /\
  P2 (1+c1) c2 m /\
  P3 c1 (4+c2) m.

Lemma P4_O:
  P4 8 0 w1 12 13.
Proof.
  unfold P4; repeat split.
  - apply P1'_O.
  - apply P1_O.
  - apply P2_O.
  - apply P3_O.
Qed.

Ltac flia := repeat (lia||f_equal).

Lemma P4_S b c m c1 c2 (c3 a0:nat):
  P4 b c m c1 c2 ->
  a0+c3+3 = b ->
  c1 = c3*4+4 ->
  2<=c3 ->
  P4 (8+a0*3) (1+c*2) ([1;0]^^c3++[1;1;0;1;0;0]++m) (c3*4+c1) (c2+c3*6+6).
Proof.
  intros [HP1' [HP1 [HP2 HP3]]] Hb Hc3 Hc3'.
  unshelve epose proof (P1'_S _ _ _ _ _ _ c3 a0 HP1' HP1 HP2 _ _) as I1'.
  1,2: lia.
  unshelve epose proof (P1_S _ _ _ _ _ _ c3 a0 HP1 HP2 _ _) as I1.
  1,2: lia.
  epose proof (P2_S _ _ c3 _ HP3) as I2.
  epose proof (P3_S _ _ (c3-2) _ HP3) as I3.
  repeat split.
  - applys_eq I1'; flia.
  - applys_eq I1; flia.
  - applys_eq I2; flia.
  - applys_eq I3; flia.
Qed.

Inductive P: nat->Prop :=
| P_intro b c m c1 c2 a0 c3 n:
  P4 b c m c1 c2 ->
  a0+c3+3 = b ->
  c1 = c3*4+4 ->
  2<=c3 ->
  n<=c ->
  c3*4 <= 5+a0*2 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (c3:=2) (a0:=3).
    1: apply P4_O.
    all: lia.
  - inverts IHn.
    eapply P4_S with (a0:=a0) (c3:=c3) in H; try lia.
    eapply P_intro with (c3:=c3*2) (a0:=5+a0*3-(c3*2)).
    1: apply H.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  destruct H as [HP1' _].
  eexists _,_; split.
  - apply HP1'.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RA_0LD0LB_1LE0LC_1RA0RF_---0RD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[0;1]^^a <* <[0;0;1;0;1;1] <* <[0;1]^^b {{B}}> [0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l (1+a) b (4+c) r -->*
  S1 l a (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l (n+a) b (n*4+c) r -->*
  S1 l a (n*3+b) c r.
Proof.
  gen l a b c r.
  ind n Inc1.
Qed.

Definition P1 a b c m :=
  forall l r,
  l <* <[0;0;1;0] <{{D}} [0]^^a *> r -->*
  l <* <[1;1;1;0;0;0;1;1]^^c <* m <* <[0;0;1;0;1;1] <* <[0;1]^^b <* [0] {{A}}> r.

Definition P2 c1 c2 m :=
  forall l r b,
  l <* m <* <[0;0;1;0;1;1] <* <[0;1]^^b <* [0] {{A}}> [0]^^c1 *> r -->*
  l <* <[1;1;1;0;0;0;1;1] <* <[0;0;1;0] <{{D}} [0]^^(c2+b*2) *> [1;0;1;0;1] *> r.

Notation w1 := <[1;1;1;0;0;0;1;0;0;1].

Lemma P1_O: P1 29 8 0 w1.
Proof.
  unfold P1.
  es.
Qed.

Lemma P2_O: P2 13 13 w1.
Proof.
  unfold P2,S1.
  es.
Qed.

Definition P3 c1 c2 m :=
  forall l r b,
  l <* m <* <[0;0;1;0;1;1]^^2 <* <[0;1]^^b {{B}}> [0]^^c1 *> r -->*
  l <* <[1;1;1;0;0;0;1;1] <* <[0;0;1;0] <{{D}} [0]^^(c2+b*2) *> [1;0;1;0;1] *> r.

Lemma P3_O: P3 12 17 w1.
Proof.
  unfold P3,S1.
  es.
Qed.

Lemma P1_S a b c m c1 c2 c3 a0:
  P1 a b c m ->
  P2 c1 c2 m ->
  c2+b*2=a ->
  a0+c3+3=b ->
  P1 (a+c1+8+a0*4+3) (a0*3+8) (1+c+c) ([1;0]^^c3++[1;1;0;1;0;0]++m).
Proof.
  unfold P1,P2,S1.
  intros HP1 HP2 Ha Ha0 l r.
  st.
  follow HP1.
  follow HP2.
  rewrite Ha.
  follow HP1.
  replace b with (2+(b-2)) by lia.
  mid (S1 (l <* <[1;1;1;0;0;0;1;1]^^(1+c+c) <* m <* <[0;0;1;0;1;1]) ((b-2)) 6 (a0*4+3) r).
  1: es.
  epose proof (Incs1 a0 _ (1+c3) _ 3 _) as I1.
  follow I1.
  es.
Qed.

Lemma P2_S c1 c2 c3 m:
  P3 c1 c2 m ->
  P2 (1+c3*4+c1) (c2+c3*6+2) ([1;0]^^c3++[1;1;0;1;0;0]++m).
Proof.
  unfold P2,P3.
  intros HP3 l r b.
  mid (S1 ([1;1;0;1;0;0]*>m*>l) (c3+0) (1+b) (c3*4+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  finish.
Qed.

Lemma P3_S c1 c2 c3 m:
  P3 c1 c2 m ->
  P3 (8+c3*4+c1) (c2+c3*6+18) ([1;0]^^(2+c3)++[1;1;0;1;0;0]++m).
Proof.
  unfold P3.
  intros HP3 l r b.
  mid (S1 ([1;1;0;1;0;0]*>m*>l) (c3+0) (9+b) (c3*4+0) ([0]^^c1*>r)).
  1: es.
  follow Incs1.
  follow HP3.
  finish.
Qed.

Definition P1' b c m :=
  c0 -->*
  0inf <* <[1;1] <* <[1;1;1;0;0;0;1;1]^^c <* m <* <[0;0;1;0;1;1] <* <[0;1]^^b <* [0] {{A}}> 0inf.

Lemma P1'_O: P1' 8 0 w1.
Proof.
  unfold P1',S1.
  esx.
Qed.

Lemma P1'_S a b c m c1 c2 c3 a0:
  P1' b c m ->
  P1 a b c m ->
  P2 c1 c2 m ->
  c2+b*2=a ->
  a0+c3+3=b ->
  P1' (a0*3+8) (1+c+c) ([1;0]^^c3++[1;1;0;1;0;0]++m).
Proof.
  unfold P1',P1,P2,S1.
  intros HP1' HP1 HP2 Ha Ha0.
  eapply evstep_trans.
  1:{
  st.
  follow HP1'.
  epose proof (HP2 _ 0inf _) as HP2.
  rewrite lpow_all0 in HP2 by solve_const0_eq.
  follow HP2.
  rewrite Ha.
  follow HP1.
  replace b with (2+(b-2)) by lia.
  mid (S1 (0inf <* <[1;1] <* <[1;1;1;0;0;0;1;1]^^(1+c+c) <* m <* <[0;0;1;0;1;1]) ((b-2)) 6 (a0*4+3) 0inf).
  1: unfold S1.
  1: rewrite (lpow_all0 [0]) by solve_const0_eq.
  1: es.
  epose proof (Incs1 a0 _ (1+c3) _ 3 _) as I1.
  follow I1.
  finish.
  }
  remember 0inf as r'.
  es.
Qed.

Definition P4 b c m c1 c2 :=
  P1' b c m /\
  P1 (c2+b*2) b c m /\
  P2 (1+c1) c2 m /\
  P3 c1 (4+c2) m.

Lemma P4_O:
  P4 8 0 w1 12 13.
Proof.
  unfold P4; repeat split.
  - apply P1'_O.
  - apply P1_O.
  - apply P2_O.
  - apply P3_O.
Qed.

Ltac flia := repeat (lia||f_equal).

Lemma P4_S b c m c1 c2 (c3 a0:nat):
  P4 b c m c1 c2 ->
  a0+c3+3 = b ->
  c1 = c3*4+4 ->
  2<=c3 ->
  P4 (8+a0*3) (1+c*2) ([1;0]^^c3++[1;1;0;1;0;0]++m) (c3*4+c1) (c2+c3*6+6).
Proof.
  intros [HP1' [HP1 [HP2 HP3]]] Hb Hc3 Hc3'.
  unshelve epose proof (P1'_S _ _ _ _ _ _ c3 a0 HP1' HP1 HP2 _ _) as I1'.
  1,2: lia.
  unshelve epose proof (P1_S _ _ _ _ _ _ c3 a0 HP1 HP2 _ _) as I1.
  1,2: lia.
  epose proof (P2_S _ _ c3 _ HP3) as I2.
  epose proof (P3_S _ _ (c3-2) _ HP3) as I3.
  repeat split.
  - applys_eq I1'; flia.
  - applys_eq I1; flia.
  - applys_eq I2; flia.
  - applys_eq I3; flia.
Qed.

Inductive P: nat->Prop :=
| P_intro b c m c1 c2 a0 c3 n:
  P4 b c m c1 c2 ->
  a0+c3+3 = b ->
  c1 = c3*4+4 ->
  2<=c3 ->
  n<=c ->
  c3*4 <= 5+a0*2 ->
  P n.

Lemma P_n n: P n.
Proof.
  induction n.
  - eapply P_intro with (c3:=2) (a0:=3).
    1: apply P4_O.
    all: lia.
  - inverts IHn.
    eapply P4_S with (a0:=a0) (c3:=c3) in H; try lia.
    eapply P_intro with (c3:=c3*2) (a0:=5+a0*3-(c3*2)).
    1: apply H.
    all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  destruct H as [HP1' _].
  eexists _,_; split.
  - apply HP1'.
  - split.
    + solve_sigma_score.
    + lia.
Qed.

End TM13.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC---_0RD1RC_1LE1LD_0LE0LF_0RA1LF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[1]^^a <* [0] <* <[1]^^b {{C}}> [0;0] *> [1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a (2+b) c r -->*
  S1 l (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 l a (n*2+b) c r -->*
  S1 l (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 l a b c r :=
  l <* <[1]^^a <* [0] <* <[1]^^b {{C}}> [0;1] *> [1]^^c *> r.

Lemma Inc2 l a b c r:
  S2 l a (2+b) c r -->*
  S2 l (1+a) b (1+c) r.
Proof.
  es.
Qed.

Lemma Incs2 n l a b c r:
  S2 l a (n*2+b) c r -->*
  S2 l (n+a) b (n+c) r.
Proof.
  gen a b c.
  ind n Inc2.
Qed.

Definition P1 a :=
  forall r,
  0inf <* <[1;0] <* [1]^^a {{C}}> [0;0] *> r -->+
  0inf <* <[1;0] <* [1]^^(2+a*2) {{C}}> r.

Lemma P1_S a:
  P1 a ->
  P1 (2+a*2).
Proof.
  unfold P1.
  intros HP1 r.
  mid01 (S1 0inf 1 ((1+a)*2+0) 0 r).
  1: es.
  follow Incs1.
  unfold S1.
  do 2 (er; sr).
  follow100 HP1.
  mid (S2 0inf 1 ((1+a)*2+0) (1+a) r).
  1: es.
  follow Incs2.
  unfold S2.
  do 2 (er; sr).
  follow100 HP1.
  replace (a*2*2) with (a+a+a*2) by lia.
  es.
Qed.

Definition S' a :=
  0inf <* <[1;0] <* [1]^^a {{C}}> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 6).
  1: unfold S'; esx.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  unfold S'.
  intros n HP1.
  eexists; split.
  1: applys_eq (HP1 0inf); st; reflexivity.
  apply P1_S,HP1.
Qed.

End TM14.


