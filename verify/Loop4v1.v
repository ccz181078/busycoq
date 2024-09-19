From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Module Loop4v1.
Section Loop4v1.

Hypothesis tm:TM.
Hypothesis config:nat*nat->Q*tape.
Hypothesis c1 c2 c3 c4 c5 c6:nat.

Hypothesis Inc:
  forall a b,
    c3+b <= a ->
    config (a,b) -[tm]->+
    config (a-(b+c1),c2+b*2).

Hypothesis Ov:
  forall a b,
    a <= c6+b ->
    config (a,b) -[tm]->+
    config (c4+b*2,c5).

Hypothesis init:
  c0 -[tm]->*
  config (c4+c5*2,c5).

Hypothesis Hc12:
  c1<=c2.

Hypothesis Hc13:
  c1<=c3.

Hypothesis Hc345:
  c3<=c4+c5.

Hypothesis Hc4:
  c4<=c6+c1+c2.

Fixpoint bi i :=
match i with
| O => c5
| S i0 => c2+(bi i0)*2
end.

Fixpoint dai i :=
match i with
| O => O
| S i0 => (dai i0)+((bi i0)+c1)
end.

Definition ai i :=
  c4 + (bi i)*2.

Lemma bi_spec i:
  (bi i)+c2 = (c5+c2)*2^i.
Proof.
  induction i; cbn; lia.
Qed.

Lemma dai_spec i:
  (dai i)+c2*i+(c5+c2) = (c5+c2)*2^i+c1*i.
Proof.
  induction i; cbn.
  - lia.
  - pose proof (bi_spec i).
    lia.
Qed.


Lemma cmp1 i:
  c3+(bi i) + (dai i) <= (ai i).
Proof.
  unfold ai.
  pose proof (bi_spec i).
  pose proof (dai_spec i).
  pose proof (Nat.mul_le_mono_r _ _ i Hc12).
  lia.
Qed.

Lemma cmp2 i:
  ai i <= c6 + (bi (1+i)) + (dai (1+i)).
Proof.
  unfold ai.
  cbn.
  lia.
Qed.

Lemma nat_func_mono(f:nat->nat):
  (forall i, f i <= f (S i)) ->
  forall j i, j<=i -> f j <= f i.
Proof.
  intros H j i.
  gen j.
  induction i; intros.
  - assert (j=O) by lia. subst.
    lia.
  - specialize (IHi j).
    assert (j<=i\/j=S i) as Hji by lia.
    destruct Hji.
    + specialize (H i). lia.
    + subst. lia.
Qed.

Lemma dai_mono i j:
  j<=i ->
  dai j <= dai i.
Proof.
  apply nat_func_mono.
  intros. cbn. lia.
Qed.

Lemma bi_mono i j:
  j<=i ->
  bi j <= bi i.
Proof.
  apply nat_func_mono.
  intros. cbn. lia.
Qed.

Definition config'(x:nat*nat):=
  let '(i,j):=x in
  config ((ai i)-(dai j),bi j).

Lemma Inc' i j:
  j<=i ->
  config' (i,j) -[tm]->+
  config' (i,1+j).
Proof.
  unfold config'.
  intro H.
  cbn.
  epose proof (Inc _ _ _) as H0.
  follow10 H0.
  finish.
Unshelve.
  pose proof (cmp1 i) as Hi.
  pose proof (dai_mono _ _ H) as Hda.
  pose proof (bi_mono _ _ H) as Hb.
  lia.
Qed.

Lemma Ov' i:
  config' (i,1+i) -[tm]->+
  config' (1+i,O).
Proof.
  unfold config'.
  epose proof (Ov _ _ _) as H0.
  follow10 H0.
  unfold ai.
  cbn.
  finish.
Unshelve.
  pose proof (cmp2 i).
  lia.
Qed.

Definition P(x:nat*nat):Prop :=
  let '(i,j):=x in j<=1+i.

Lemma init':
  c0 -[tm]->* config' (0,0)%nat.
Proof.
  cbn.
  unfold ai,bi.
  follow init.
  finish.
Qed.


Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init'.
  apply (progress_nonhalt_cond tm _ _ _ P).
  2: unfold P; lia.
  intro i.
  destruct i as [i j].
  unfold P.
  intro HP.
  assert (j<=i\/j=1+i) as E by lia.
  destruct E as [E|E].
  - eexists (_,_).
    split.
    + apply Inc',E.
    + lia.
  - subst.
    eexists (_,_).
    split.
    + apply Ov'.
    + lia.
Qed.
End Loop4v1.
End Loop4v1.





Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac es :=
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc;
  repeat rewrite lpow_mul;
  execute_with_shift_rule.

Ltac ind n H :=
  induction n as [|n IHn]; intros;
  [ finish |
    cbn[Nat.add];
    follow H;
    follow IHn;
    finish ].

Ltac simpl_add_mul :=
  repeat (
    rewrite Nat.mul_add_distr_r ||
    rewrite Nat.mul_sub_distr_r ||
    rewrite Nat.add_assoc ||
    rewrite <-Nat.mul_assoc
    ).





Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LD_0RA1LB_---1RE_1LF0RF_0LC0LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{F}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{F}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 b 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(2+b*2)) 2 0.
Proof.
  intro H.
  follow10 ROv0.
  replace (2+b) with (2+b-a+a) by lia.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(2+(a*2+0))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

(*

(a,b) --> (a-b-3,2b+4),  3+b<=a
(a,b) --> (2b+2,2),  a<=b+1
start: (0,2)

b[0]=2
b[i+1]=b[i]*2+4

b'[i]=b[i]+3

a[i,j+1] = a[i,j]-b'[j], 3+b[j]<=a[i,j], j<=i

3+b[i] <= a[i,i]

a[i,i+1] <= b[i+1]+1

a[i+1,0] = b[i]*2+2

bi: 2,8,20,44
ai: 6,18,42

6,2  1,8
18,2 13,8 2,20

*)

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM5.



Module TM6. (* from TM5 *)

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_1RF1LC_0LB1RF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 b 0 -->*
  S0 b 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(3+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  replace (2+b) with (2+b-a+a) by lia.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM6.


Module TM7. (* from TM6 *)

Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC1RB_---1RD_1LE0RE_1RF0LD_1LA0LB").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{E}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{E}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 b 0 -->*
  S0 (1+b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(4+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  replace (2+b) with (2+b-a+a) by lia.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM7.



Module TM10. (* from TM7 *)

Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC1LA_0LF1LD_---1RE_0RB1RB_1RB1LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1;0]^^b {{E}}> [0;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^b {{E}}> [0;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (2+a) (b) 0 -->+
  S0 (1+a) 1 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 b 0 -->*
  S0 (1+b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (2+a) (1+b) 0 -->+
  S0 (2+(a-(b+3))) (1+(4+b*2)) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-1) 1 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 0+b ->
  S0 (2+a) (1+b) 0 -->+
  S0 (2+(4+b*2)) (1+0) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (1+(b-a)) (1+a)).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (2+a) (1+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM10.

Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1LF_0RD1LB_0RE1RD_1LA0RA_---1RE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{A}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (1+b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(4+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM12.


Module TM13. (* from TM12 *)

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_0RF1LC_0LA1RF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(3+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM13.


Module TM14. (* same rules as TM13 *)

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_0RF1LC_0LC1RF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(3+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM14.


Module TM15. (* same rules as TM12 *)

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC0LA_1LF0LD_---1RE_0RB1RE_1RD1LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (1+b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(4+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM15.


Module TM17. (* same rules as TM12 *)

Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC1RB_1RD0LF_1LA0LE_---1RB_1LC0RC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{C}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (1+b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(4+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM17.

Module TM18. (* same rules as TM12 *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RD_1LA0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{A}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (1+b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(4+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM18.


Module TM19. (* same rules as TM12 *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC1LE_1RD1LB_0RA1RD_---1RF_1LA0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{A}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (1+b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(4+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM19.


Module TM20. (* same rules as TM12 *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC1LE_1RD1LB_1LE1RD_---1RF_1LA0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{A}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (1+b) 0 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(4+b*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1RA_1LD0RF_1RE1LA_1LB1LE_---0LA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1;1]^^b {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [1;1]^^b <* [1] {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (2+b) 0 -->*
  S0 (b) 5 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(0+b*2)) 5 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(1+(a*2+0))) with (2+(1+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM21.


Module TM22. (* same rules as TM21 *)

Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1RA_1LD1RF_1RE1LA_1LB1LE_---0RC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1;1]^^b {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [1;1]^^b <* [1] {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (2+b) 0 -->*
  S0 (b) 5 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(0+b*2)) 5 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(1+(a*2+0))) with (2+(1+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM22.

Module TM25. (* from TM19 *)

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LD_0RA1LB_---1RE_1LF0RF_1RB0LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{F}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{F}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(2+b*2)) 2 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(2+(a*2+0))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM25.

Module TM26. (* from TM25 *)

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC1RB_1RD0LF_1LA1LE_---1RF_1LC0RC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{C}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (b) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(3+b*2)) 2 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM26.


Module TM27. (* same rules as TM25 *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC1LE_1RD1LB_1LC1RD_---1RF_1LA0RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{A}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(2+b*2)) 2 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(2+(a*2+0))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM27.

Module TM28. (* from TM25 *)

Definition tm := Eval compute in (TM_from_str "1LB1RA_1LC0RC_1RD0LB_1LF1LE_---1RB_0RA1LD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{C}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(2+b*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(2+(a*2+0))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM28.

Module TM29. (* same rules as TM28 *)

Definition tm := Eval compute in (TM_from_str "1LB1RA_1LC1LD_0RA1LB_---1RE_1LF0RF_1RB0LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{F}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{F}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(2+b*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(2+(a*2+0))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM29.


Module TM30. (* from TM28 *)

Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC0LA_1LE1LD_---1RA_1RF1LC_1LB1RF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(3+b*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM30.


Module TM31. (* same rules as TM28 *)

Definition tm := Eval compute in (TM_from_str "1RB1LC_0LA1RB_1LA1LD_---1RE_1LF0RF_1RC0LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{F}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{F}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(2+b*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(2+(a*2+0))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM31.

Module TM32. (* same rules as TM30 *)

Definition tm := Eval compute in (TM_from_str "1RB1LF_0LC1RB_---1RD_1LE0RE_1RF0LD_1LA1LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{E}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{E}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(3+b*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM32.


Module TM33. (* same rules as TM30 *)

Definition tm := Eval compute in (TM_from_str "1LB1LF_0RC1LA_1RD1RC_1LE0RE_1RA0LD_---1RD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^b <* [0;1] {{E}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b {{E}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(3+b*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


End TM33.

Module TM49.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA1LA_1RD1RA_0LE0LF_1RC1LD_---1RE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^(1+b) {{C}}> [1;0]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^(1+b) {{C}}> [1;0]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 (a) 1 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (1+b) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  2+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+2))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-1) 1 0 (1+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 0+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(2+b*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (1+b-a) a).
  replace (1+b-a) with (1+(b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM49.


Module TM54. (* from TM21 *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_1RD1LA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1;1]^^b {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [1;1]^^(b) <* [1] {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 4 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(1+b*2)) 4 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(1+(a*2+0))) with (1+(2+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM54.


Module TM55. (* same rules as TM54 *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_1RF1LA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1;1]^^b {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [1;1]^^(b) <* [1] {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 4 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(1+b*2)) 4 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(1+(a*2+0))) with (1+(2+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM55.


Module TM56. (* same rules as TM54 *)

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LB1LD_---1RC_1LA1LA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1;1]^^b {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [1;1]^^(b) <* [1] {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 4 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(1+b*2)) 4 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(1+(a*2+0))) with (1+(2+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM56.



Module TM57.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC1LA_0LE0LD_---1RE_1RB1LC_1LC1RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^(b) {{F}}> [1;0]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^(b) {{F}}> [1;0]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 (a) 1 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 3 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  2+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+2))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-1) 1 0 (1+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 0+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(0+b*2)) 3 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (1+b-a) a).
  replace (1+b-a) with (1+(b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((b-a)*2+(1+(a*2+1))) with (1+(1+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM57.



Module TM58. (* same rules as TM57 *)

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC1LA_0LE0LD_---1RE_1RB1LC_1RC1RA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1;1]^^a <* [1] <* [0;1]^^(b) {{F}}> [1;0]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^(b) {{F}}> [1;0]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 (a) 1 (1+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 3 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  2+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+2))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-1) 1 0 (1+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 0+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(0+b*2)) 3 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (1+b-a) a).
  replace (1+b-a) with (1+(b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((b-a)*2+(1+(a*2+1))) with (1+(1+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM58.



Module TM59. (* from TM57 *)

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RF_1RD0LB_1LE0RC_1LA1LD_1RD1RF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1] <* [1;1]^^a <* [1] <* [0;1]^^(1+b) {{C}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^(1+b) {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 (a) 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (3+c) -->*
  S1 (4+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (b) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b <= a ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(a-(b+4))) (6+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-3) 0 0 (3+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 0+b ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(3+b*2)) (1+1) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (3+b-a) a).
  replace (3+b-a) with (3+(b-a-0)) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) (1+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM59.




Module TM62. (* from TM54 *)

Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1RA_1LD0RF_1RE1LA_1LB1LE_---1RC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1;1]^^b {{B}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [1;1]^^(b) <* [1] {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (2+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (2+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (b) 0 -->+
  S0 a 0 (2+b).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b) 3 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b <= a ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(a-(b+3))) (4+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b-2) 0 0 (2+b)).
  finish.
Qed.

Lemma Ov a b:
  a <= 1+b ->
  S0 (1+a) (b) 0 -->+
  S0 (1+(1+b*2)) 3 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 0 (2+b-a) a).
  replace (2+b-a) with (1+(1+b-a)) by lia.
  follow LOv0.
  follow Inc1s.
  replace ((1+b-a)*2+(1+(a*2+0))) with (1+(2+b*2)) by lia.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v1.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) b 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM62.










