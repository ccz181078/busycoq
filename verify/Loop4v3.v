From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Section Loop4v3.

Hypothesis tm:TM.
Hypothesis config:nat*nat->Q*tape.
Hypothesis c1 c2 c3 c4 c5 c6 c6' c7:nat.

Hypothesis Inc:
  forall a b,
    c3+b*2 <= a ->
    config (a,b) -[tm]->+
    config (a-(b*2+c1),c2+b*2).

Hypothesis Ov:
  forall a b,
    c6+a <= c6'+b*2 ->
    config (a,b) -[tm]->+
    config (c4+b*8-a*2,c5).

Hypothesis init:
  c0 -[tm]->*
  config (c7,c5).

(*
Hypothesis Hc12:
  c1<=c2*2.

Hypothesis Hc13:
  c1<=c3.

Hypothesis Hc345:
  c3<=c4+c5*2.

Hypothesis Hc4:
  c6+c4<=c1+c2*2.
*)

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

Fixpoint ai i :=
match i with
| O => c7
| S i0 => c4 + (bi (1+i0))*8 + (dai (1+i0))*2 - (ai i0)*2
end.


Lemma bi_spec i:
  (bi i)+c2 = 2^i*(c5+c2).
Proof.
  induction i; cbn; lia.
Qed.

Lemma dai_spec i:
  (dai i)+c2*2*i+(c5+c2)*2 = 2^i*(c5+c2)*2+c1*i.
Proof.
  induction i; cbn.
  - lia.
  - pose proof (bi_spec i).
    lia.
Qed.


Hypothesis ai_spec:
  (forall i, (bi i)+c2 = 2^i*(c5+c2)) ->
  (forall i, (dai i)+c2*2*i+(c5+c2)*2 = 2^i*(c5+c2)*2+c1*i) ->
  forall i,
  dai (1+i) <= ai i /\
  (ai i)*2 <= c4 + (bi (1+i))*8 + (dai (1+i))*2 /\
  dai (2+i) <= ai (1+i) /\
  (ai (1+i))*2 <= c4 + (bi (2+i))*8 + (dai (2+i))*2 /\
  c3 + (bi i)*2 + (dai i) <= (ai i) /\
  c6 + ai i <= c6' + (bi (1+i))*2 + (dai (1+i)) /\
  c3 + (bi (1+i))*2 + (dai (1+i)) <= (ai (1+i)) /\
  c6 + ai (1+i) <= c6' + (bi (2+i))*2 + (dai (2+i)).

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
  specialize (ai_spec bi_spec dai_spec i).
  pose proof (dai_mono _ _ H) as Hda.
  pose proof (bi_mono _ _ H) as Hb.
  lia.
Qed.

Lemma Ov' i:
  config' (i,1+i) -[tm]->+
  config' (1+i,O).
Proof.
  specialize (ai_spec bi_spec dai_spec i).
  cbn in ai_spec.
  unfold config'.
  epose proof (Ov _ _ _) as H0.
  follow10 H0.
  cbn.
  finish.
Unshelve.
  cbn.
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
  intros [i j].
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

End Loop4v3.





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


Ltac solve_ai_spec :=
intros Hb Hda i;
induction i as [|i IHi];
[ cbn; lia |
specialize (Hb i);
specialize (Hda i);
gen Hb Hda IHi;
cbn[Nat.add];
cbn[Loop4v3.ai];
cbn[Nat.add];
cbn[Loop4v3.dai];
cbn[Nat.add];
cbn[Loop4v3.bi];
intros Hb Hda IHi;
destruct IHi as [H0 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]];
repeat split; lia ].




Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LF_1LD1RC_---0LE_1LA1RF_0RE0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^b <* [1] {{F}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{F}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (4+a) (0+b) 0 -->+
  S0 a 3 (b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 b c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2) 3 0 (b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= 0+b*2 ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(5+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 3 (b*2-a) a).
  follow LOv0.
  follow Inc1s.
  replace ((b*2-a-1)*2+(2+(a+3))) with (3+4*b-a) by lia.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 (4+11) 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (4+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.
End TM1.


Module TM2. (* same rules as TM1 *)

Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LD_1LA1RC_0RF1LE_---0LF_1LA1RD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^b <* [1] {{D}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{D}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (4+a) (0+b) 0 -->+
  S0 a 3 (b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 b c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2) 3 0 (b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= 0+b*2 ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(5+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 3 (b*2-a) a).
  follow LOv0.
  follow Inc1s.
  replace ((b*2-a-1)*2+(2+(a+3))) with (3+4*b-a) by lia.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 (4+11) 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (4+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.
End TM2.

Module TM3. (* same rules as TM1 *)

Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LE_1LD1RC_1LA1RE_0RD1LF_---0LD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (4+a) (0+b) 0 -->+
  S0 a 3 (b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 b c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2) 3 0 (b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= 0+b*2 ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(5+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 3 (b*2-a) a).
  follow LOv0.
  follow Inc1s.
  replace ((b*2-a-1)*2+(2+(a+3))) with (3+4*b-a) by lia.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 (4+11) 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (4+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM3.

Module TM4. (* same rules as TM1 *)

Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LF_1LD1RC_---0LE_1LA1RF_0RE1LD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^b <* [1] {{F}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{F}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (4+a) (0+b) 0 -->+
  S0 a 3 (b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 b c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2) 3 0 (b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= 0+b*2 ->
  S0 (4+a) (b) 0 -->+
  S0 (4+(5+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 3 (b*2-a) a).
  follow LOv0.
  follow Inc1s.
  replace ((b*2-a-1)*2+(2+(a+3))) with (3+4*b-a) by lia.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 (4+11) 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (4+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM4.

Module TM11. (* from TM1 *)

Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RB_1LA0LD_1LC1RE_0RD1LF_---0LB").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^(1+b) <* [1] {{E}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (5+a) (0+b) 0 -->+
  S0 (a) 2 (3+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 0 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  8+b*2 <= a ->
  S0 (5+a) (0+b) 0 -->+
  S0 (5+(a-(b*2+8))) (5+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 3+b*2 ->
  S0 (5+a) (0+b) 0 -->+
  S0 (5+(16+b*8-a*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.


Lemma init:
  c0 -->*
  S0 17 0 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (5+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM11.

Module TM34. (* from TM11 *)

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LE_1LA1RC_1LA1RE_0RD1LF_---0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^(1+b) <* [1] {{E}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (5+a) (0+b) 0 -->+
  S0 (a) 2 (3+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 (1+b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 0 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  8+b*2 <= a ->
  S0 (5+a) (0+b) 0 -->+
  S0 (5+(a-(b*2+8))) (5+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-3) 2 0 (3+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 3+b*2 ->
  S0 (5+a) (0+b) 0 -->+
  S0 (5+(16+b*8-a*2)) 0 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (3+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.


Lemma init:
  c0 -->*
  S0 21 0 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (5+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.
End TM34.


Module TM39. (* from TM33 *)

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LF_0LD1RC_---1RE_1LA1RF_0RE0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^(1+a) <* [1;0]^^(b) {{F}}> [1]^^(c) *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^(1+b) {{F}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (3+a) (b) 0 -->+
  S0 a 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 (b) c -->*
  S1 (b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-1) 2 0 (1+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 1+b*2 ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(8+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (1+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (3+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.
End TM39.

Module TM40. (* same rules as TM39 *)

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LE_1LA1RC_1LA1RE_0RD0LF_---1RC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^(1+a) <* [1;0]^^(b) {{E}}> [1]^^(c) *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^(1+b) {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (3+a) (b) 0 -->+
  S0 a 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 (b) c -->*
  S1 (b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-1) 2 0 (1+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 1+b*2 ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(8+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (1+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (3+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM40.

Module TM41. (* same rules as TM39 *)

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LE_1LA1RC_1LA1RE_0RD0LF_---1RD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^(1+a) <* [1;0]^^(b) {{E}}> [1]^^(c) *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^(1+b) {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (3+a) (b) 0 -->+
  S0 a 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 (b) c -->*
  S1 (b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-1) 2 0 (1+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 1+b*2 ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(8+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (1+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (3+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM41.

Module TM42. (* same rules as TM39 *)

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LE_1LD1RC_1LA1RE_0RD0LF_---1RD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^(1+a) <* [1;0]^^(b) {{E}}> [1]^^(c) *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^(1+b) {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (3+a) (b) 0 -->+
  S0 a 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 (b) c -->*
  S1 (b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-1) 2 0 (1+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 1+b*2 ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(8+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (1+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (3+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM42.

Module TM43. (* same rules as TM39 *)

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LF_---1RD_1LA1RD_1LA1RF_0RE0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^(1+a) <* [1;0]^^(b) {{F}}> [1]^^(c) *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^(1+b) {{F}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (3+a) (b) 0 -->+
  S0 a 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 (b) c -->*
  S1 (b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-1) 2 0 (1+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 1+b*2 ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(8+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (1+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (3+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM43.

Module TM44. (* same rules as TM39 *)

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LF_0LD1RC_---1RE_1LA1RF_0RE0LD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^(1+a) <* [1;0]^^(b) {{F}}> [1]^^(c) *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^(1+b) {{F}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (3+a) (b) 0 -->+
  S0 a 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 (b) c -->*
  S1 (b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-1) 2 0 (1+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 1+b*2 ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(8+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (1+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (3+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM44.

Module TM45. (* same rules as TM39 *)

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LF_1LD1RC_---0LE_1LA1RF_0RE0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^(1+a) <* [1;0]^^(b) {{F}}> [1]^^(c) *> const 0.

Definition S1 b c :=
  const 0 <* [1;0]^^(1+b) {{F}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (3+a) (b) 0 -->+
  S0 a 2 (1+b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 (b) c -->*
  S1 (b) c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2-1) 2 0 (1+b*2)).
  finish.
Qed.

Lemma Ov a b:
  0+a <= 1+b*2 ->
  S0 (3+a) (b) 0 -->+
  S0 (3+(8+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s 0 2 (1+b*2-a) a).
  follow LOv0.
  follow Inc1s.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (3+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM45.

Module TM46. (* same rules as TM1 *)

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LE_1LA1RC_1LA1RE_0RD1LF_---0LD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (4+a) (0+b) 0 -->+
  S0 a 3 (b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 b c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (4+a) (0+b) 0 -->+
  S0 (4+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2) 3 0 (b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= 0+b*2 ->
  S0 (4+a) (0+b) 0 -->+
  S0 (4+(5+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  replace (b*2) with (b*2-a+a) by lia.
  follow (Inc0s 0 3 (b*2-a) a).
  follow LOv0.
  follow Inc1s.
  replace ((b*2-a-1)*2+(2+(a+3))) with (3+4*b-a) by lia.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (4+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.
End TM46.

Module TM47. (* same rules as TM1 *)

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LE_1LD1RC_1LA1RE_0RD1LF_---0LD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{E}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (4+a) (0+b) 0 -->+
  S0 a 3 (b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 b c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (4+a) (0+b) 0 -->+
  S0 (4+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2) 3 0 (b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= 0+b*2 ->
  S0 (4+a) (0+b) 0 -->+
  S0 (4+(5+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  replace (b*2) with (b*2-a+a) by lia.
  follow (Inc0s 0 3 (b*2-a) a).
  follow LOv0.
  follow Inc1s.
  replace ((b*2-a-1)*2+(2+(a+3))) with (3+4*b-a) by lia.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (4+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM47.

Module TM48. (* same rules as TM1 *)

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LF_1LD1RC_---0LE_1LA1RF_0RE1LD").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b c :=
  const 0 <* [1]^^a <* [0;1]^^b <* [1] {{F}}> [1]^^c *> const 0.

Definition S1 b c :=
  const 0 <* [0;1]^^b <* [1] {{F}}> [1]^^c *> const 0.

Lemma Inc0 a b c:
  S0 (1+a) b (1+c) -->*
  S0 a (1+b) c.
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
  S0 (4+a) (0+b) 0 -->+
  S0 a 3 (b*2).
Proof.
  unfold S0.
  es.
Qed.

Lemma LOv0 b c:
  S0 0 b c -->*
  S1 b c.
Proof.
  unfold S0,S1.
  es.
Qed.

Lemma ROv1 b:
  S1 (b) 0 -->*
  S0 (3+b*2) 1 0.
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
  S1 (c*2+b) 0.
Proof.
  gen b.
  ind c Inc1.
Qed.

Lemma Inc a b:
  4+b*2 <= a ->
  S0 (4+a) (0+b) 0 -->+
  S0 (4+(a-(b*2+4))) (3+b*2) 0.
Proof.
  intro H.
  follow10 ROv0.
  follow (Inc0s (a-b*2) 3 0 (b*2)).
  finish.
Qed.

Lemma Ov a b:
  1+a <= 0+b*2 ->
  S0 (4+a) (0+b) 0 -->+
  S0 (4+(5+b*8-a*2)) 1 0.
Proof.
  intro H.
  follow10 ROv0.
  replace (b*2) with (b*2-a+a) by lia.
  follow (Inc0s 0 3 (b*2-a) a).
  follow LOv0.
  follow Inc1s.
  replace ((b*2-a-1)*2+(2+(a+3))) with (3+4*b-a) by lia.
  follow ROv1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 15 1 0.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt with (config := fun '(a,b) => S0 (4+a) b 0).
  - apply Inc.
  - apply Ov.
  - apply init.
  - solve_ai_spec.
Qed.

End TM48.



