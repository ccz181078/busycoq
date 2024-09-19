From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Module Loop4v2.
Section Loop4v2.

Hypothesis tm:TM.
Hypothesis config:nat*nat->Q*tape.
Hypothesis c1 c2 c3 c4 c5 c6:nat.

Hypothesis Inc:
  forall a b,
    c3+b*2 <= a ->
    config (a,b) -[tm]->+
    config (a-(b*2+c1),c2+b*2).

Hypothesis Ov:
  forall a b,
    c6+a <= b*2 ->
    config (a,b) -[tm]->+
    config (c4+b*4,c5).


Hypothesis init:
  c0 -[tm]->*
  config (c4+c5*4,c5).

Hypothesis Hc12:
  c1<=c2*2.

Hypothesis Hc13:
  c1<=c3.

Hypothesis Hc345:
  c3<=c4+c5*2.

Hypothesis Hc4:
  c6+c4<=c1+c2*2.

Fixpoint bi i :=
match i with
| O => c5
| S i0 => c2+(bi i0)*2
end.

Fixpoint dai i :=
match i with
| O => O
| S i0 => (dai i0)+((bi i0)*2+c1)
end.

Definition ai i :=
  c4 + (bi i)*4.

Lemma bi_spec i:
  (bi i)+c2 = (c5+c2)*2^i.
Proof.
  induction i; cbn; lia.
Qed.

Lemma dai_spec i:
  (dai i)+c2*2*i+(c5+c2)*2 = (c5+c2)*2*2^i+c1*i.
Proof.
  induction i; cbn.
  - lia.
  - pose proof (bi_spec i).
    lia.
Qed.


Lemma cmp1 i:
  c3+(bi i)*2 + (dai i) <= (ai i).
Proof.
  unfold ai.
  pose proof (bi_spec i).
  pose proof (dai_spec i).
  pose proof (Nat.mul_le_mono_r _ _ i Hc12).
  lia.
Qed.

Lemma cmp2 i:
  c6 + ai i <= (bi (1+i))*2 + (dai (1+i)).
Proof.
  unfold ai.
  cbn.
  lia.
Qed.

Lemma cmp3 i:
  dai (1+i) <= ai i.
Proof.
  unfold ai.
  cbn.
  pose proof (bi_spec i).
  pose proof (dai_spec i).
  pose proof (Nat.mul_le_mono_r _ _ i Hc12).
  lia.
Qed.

(*
bi = (c5+c2)<<i - c2
dai = (c5+c2)*2 << i  + (c1-c2*2)*i - (c5+c2)*2
*)

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
  pose proof (cmp3 i).
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
End Loop4v2.
End Loop4v2.





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






Module TM8. (* from test1 *)

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1LD_1RA1RB_1RE0LB_1LF0RC_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (1+b) 0 -->+
  S0 (a) 1 (2+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 1 -->*
  S0 (1+b*2) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b*2 <= a ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(a-(b*2+3))) (1+(2+b*2)) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-2) 1 0 (2+b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= b*2 ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(4+b*4)) (1+0) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (2+b*2-a) a).
  replace (2+b*2-a) with (2+(1+(b*2-a-1))) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) (1+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.


(*
(a,b) --> (a-2b-3,2b+2), 2b+3<=a
(a,b) --> (4b+4,0),  a+3<=2b
start: (2,0)

bi = 0,2,6,14,30,...
ai = 4,12,28,60,...
dai = 0,3,10,25,...

4,0 1,2
12,0 9,2 2,6
28,0 25,2 18,6 3,14
60,0 58,2 ...

*)

End TM8.


Module TM9. (* same rules as TM8 *)

Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC1RA_1RA0RB_1RE0LA_1LF0RD_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (1+b) 0 -->+
  S0 (a) 1 (2+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 1 -->*
  S0 (1+b*2) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b*2 <= a ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(a-(b*2+3))) (1+(2+b*2)) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-2) 1 0 (2+b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= b*2 ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(4+b*4)) (1+0) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (2+b*2-a) a).
  replace (2+b*2-a) with (2+(1+(b*2-a-1))) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) (1+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM9.

Module TM16. (* from TM8 *)

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0RA_1LA1LD_1RE0LC_1LF0RD_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (1+b) 0 -->+
  S0 (a) 1 (2+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 1 -->*
  S0 (b*2) 1 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b*2 <= a ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(a-(b*2+3))) (1+(2+b*2)) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-2) 1 0 (2+b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= b*2 ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(3+b*4)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (2+b*2-a) a).
  replace (2+b*2-a) with (2+(1+(b*2-a-1))) by lia.
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) (1+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM16.


Module TM23. (* = test1*)

Definition tm := Eval compute in (TM_from_str "1RB1RC_0RC0RD_1LA1LD_1RE0LC_1LF0RA_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (1+b) 0 -->+
  S0 (a) 1 (2+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 0 -->*
  S0 (b*2) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b*2 <= a ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(a-(b*2+3))) (1+(2+b*2)) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-2) 1 0 (2+b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= b*2 ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(3+b*4)) 2 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (2+b*2-a) a).
  replace (2+b*2-a) with (2+(1+(b*2-a-1))) by lia.
  follow LOv0.
  follow Inc1s.
  rewrite <-Nat.add_assoc.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) (1+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM23.

Module TM24. (* from TM23 *)

Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC1RA_0LA0RB_1RE0LA_1LF0RD_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (1+a) (1+b) 0 -->+
  S0 (a) 1 (2+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (2+b) 0 -->*
  S0 (1+b*2) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b c -->*
  S1 (c+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  3+b*2 <= a ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(a-(b*2+3))) (1+(2+b*2)) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-2) 1 0 (2+b*2)).
  finish.
Qed.

Lemma Ov a b:
  2+a <= b*2 ->
  S0 (1+a) (1+b) 0 -->+
  S0 (1+(2+b*4)) 2 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 1 (2+b*2-a) a).
  replace (2+b*2-a) with (2+(2+(b*2-a-2))) by lia.
  follow LOv0.
  follow Inc1s.
  rewrite <-Nat.add_assoc.
  follow ROv1.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (1+a) (1+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: lia.
Qed.

End TM24.


Module TM50. (* from TM8 *)

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC1LD_1RA0LB_1RE0LB_1LF0RD_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (2+a) (1+b) 0 -->+
  S0 (a) 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (2+b) 1 -->*
  S0 (1+b*2) 3 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  5+b*2 <= a ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(a-(b*2+5))) (2+(3+b*2)) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  2+a <= b*2 ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(3+b*4)) (2+1) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  replace (3+b*2-a) with (2+(1+(b*2-a-0))) by lia.
  follow LOv0.
  follow Inc1s.
  replace (b*2-a-0+(2+(a+2))) with (2+(2+b*2)) by lia.
  follow ROv1.
  finish.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (2+a) (2+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: try lia.
Qed.

End TM50.

Module TM51. (* same rules as TM50 *)

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LD_1RA0LB_1RE0LB_1LF0RC_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (2+a) (1+b) 0 -->+
  S0 (a) 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (2+b) 1 -->*
  S0 (1+b*2) 3 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  5+b*2 <= a ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(a-(b*2+5))) (2+(3+b*2)) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  2+a <= b*2 ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(3+b*4)) (2+1) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  replace (3+b*2-a) with (2+(1+(b*2-a-0))) by lia.
  follow LOv0.
  follow Inc1s.
  replace (b*2-a-0+(2+(a+2))) with (2+(2+b*2)) by lia.
  follow ROv1.
  finish.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (2+a) (2+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: try lia.
Qed.

End TM51.


Module TM52. (* from TM50 *)

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1LD_1RA0LB_1RE0LB_1LF0RC_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{C}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (2+a) (1+b) 0 -->+
  S0 (a) 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 1 -->*
  S0 (b*2) 3 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  5+b*2 <= a ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(a-(b*2+5))) (2+(3+b*2)) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  2+a <= b*2 ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(4+b*4)) (2+1) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  replace (3+b*2-a) with (2+(1+(b*2-a-0))) by lia.
  follow LOv0.
  follow Inc1s.
  replace (b*2-a-0+(2+(a+2))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (2+a) (2+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: try lia.
Qed.

End TM52.


Module TM53. (* same rules as TM52 *)

Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0LA_1RA0RB_1RE0LA_1LF0RD_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (2+a) (1+b) 0 -->+
  S0 (a) 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 1 -->*
  S0 (b*2) 3 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  5+b*2 <= a ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(a-(b*2+5))) (2+(3+b*2)) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  2+a <= b*2 ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(4+b*4)) (2+1) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  replace (3+b*2-a) with (2+(1+(b*2-a-0))) by lia.
  follow LOv0.
  follow Inc1s.
  replace (b*2-a-0+(2+(a+2))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (2+a) (2+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: try lia.
Qed.

End TM53.




Module TM60. (* from TM52 *)

Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC0RD_1LA1LD_1RE0LC_1LF0RA_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{A}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (2+a) (1+b) 0 -->+
  S0 (a) 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 1 -->*
  S0 (b*2) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  5+b*2 <= a ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(a-(b*2+5))) (2+(3+b*2)) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  2+a <= b*2 ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(6+b*4)) (2+0) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  replace (3+b*2-a) with (2+(1+(b*2-a-0))) by lia.
  follow LOv0.
  follow Inc1s.
  replace (b*2-a-0+(2+(a+2))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (2+a) (2+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: try lia.
Qed.

End TM60.



Module TM61. (* from TM60 *)

Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0LA_0LA0RB_1RE0LA_1LF0RD_---1LE").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [0;1]^^a <* [1] <* [0;1;0;1]^^b {{D}}> [1;1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1;0;1]^^b {{B}}> [1;1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
Proof.
  unfold S0.
  es.
Qed.

Lemma Inc1 b c:
  S1 b (1+c) -->*
  S1 (1+b) c.
Proof.
  unfold S1.
  es.
Qed.

Lemma ROv0 a b:
  S0 (2+a) (1+b) 0 -->+
  S0 (a) 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b (2+c) -->*
  S1 (2+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (1+b) 1 -->*
  S0 (1+b*2) 2 0.
Proof.
  unfold S0,S1.
  es.
Qed.


Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s b c:
  S1 b (1+c) -->*
  S1 (c+b) 1.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  5+b*2 <= a ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(a-(b*2+5))) (2+(3+b*2)) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  2+a <= b*2 ->
  S0 (2+a) (2+b) 0 -->+
  S0 (2+(5+b*4)) (2+0) 0.
Proof.
  intro H.
  replace (2+b) with (1+(1+b)) by lia.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  replace (3+b*2-a) with (2+(1+(b*2-a-0))) by lia.
  follow LOv0.
  follow Inc1s.
  replace (b*2-a-0+(2+(a+2))) with (1+(3+b*2)) by lia.
  follow ROv1.
  finish.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply Loop4v2.nonhalt with
  (config := fun x => let '(a,b):=x in S0 (2+a) (2+b) 0).
  1: apply Inc.
  1: apply Ov.
  1: unfold S0; solve_init.
  all: try lia.
Qed.

End TM61.







