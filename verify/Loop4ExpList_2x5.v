From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB2LA1RA2LB---_0LA4RB3RB1LA2RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Definition S1 a b c l r :=
  l <* <[3;4]^^a <| [2]^^b *> [2;1]^^c *> r.

Lemma Inc1 a b c l r:
  S1 (1+a) b (2+c) l r -->*
  S1 a (6+b) c l r.
Proof. es. Qed.

Lemma Incs1 n a b c l r:
  S1 (n+a) b (n*2+c) l r -->*
  S1 a (n*6+b) c l r.
Proof.
  gen a b c l r.
  ind n Inc1.
Qed.

Definition S2 a b l :=
  l <* <[3;4]^^a <| [2]^^b *> 0inf.

Lemma Inc2 a b l:
  S2 (1+a) b l -->*
  S2 a (4+b) l.
Proof. es. Qed.

Lemma Incs2 a b l:
  S2 a b l -->*
  S2 0 (a*4+b) l.
Proof.
  gen b l.
  ind a Inc2.
Qed.

Fixpoint L l ls :=
match ls with
| (a,b)::ls0 => L l ls0 <* <[3;4]^^a <* [3;3]^^b
| nil => l
end.

Lemma Lstep a b l r:
  l <* <[3;4]^^a <* [3;3]^^(a*2+b) <| r -->*
  l <| [2;2]^^(a*3) *> [2;1]^^b *> r.
Proof.
  remember (a*2+b) as v1.
  es; er.
  subst v1.
  pose proof (Incs1 a 0 0 b l r) as H1.
  unfold S1 in H1.
  follow H1.
  es.
Qed.

Definition P l1 l2 ls1 ls2 n :=
  forall r,
  L l1 ls1 <| r -->*
  L l2 ls2 <* <[3;4]^^n |> r.

Definition lh0 := 0inf <* [4] <* [3]^^18.
Definition lh1 := 0inf <* [1] <* [3]^^5.
Definition lh2 := 0inf <* [1].

Lemma P_0:
  P lh0 lh1 [] [] 7.
Proof.
  unfold P.
  es.
Qed.

Lemma P_1:
  P lh1 lh2 [] [] 3.
Proof.
  unfold P.
  es.
Qed.

Lemma P_2:
  P lh2 lh0 [(3,21)]%nat [] 15.
Proof.
  unfold P.
  es.
Qed.

Lemma P_S {l1 l2 ls1 ls2 n} a b:
  P l1 l2 ls1 ls2 n ->
  P l1 l2 ((a,a*2+b)::ls1) ((n,a*3)::ls2) b.
Proof.
  unfold P.
  intros HP r.
  cbn[L].
  follow Lstep.
  follow HP.
  es.
Qed.

Definition S0 l ls a :=
  L l ls <| [2;2]^^a *> [2] *> 0inf.

Lemma BigStep_1 {l1 l2 ls1 ls2 n a}:
  P l1 l2 ls1 ls2 n ->
  S0 l1 ls1 a -->*
  S0 l2 ((n,a)::ls2) 0.
Proof.
  intros HP.
  unfold S0.
  follow HP.
  es.
Qed.

Lemma BigStep_2 {l1 ls1} a:
  S0 l1 ((a+1,a*2)::ls1) 0 -->+
  S0 l1 ls1 (a*3+2).
Proof.
  unfold S0.
  cbn[L].
  rewrite <-lpow_add'.
  epose proof (Lstep a 0 _ _).
  follow H.
  es.
Qed.

Lemma BigStep_3 {l1 l2 ls1 ls2 n} a b:
  P l1 l2 ls1 ls2 n ->
  S0 l1 ((a,a*2+b)::ls1) 0 -->*
  S0 l2 ((n,a*3)::ls2) (b*2).
Proof.
  intros HP.
  unfold S0.
  cbn[L].
  follow (P_S a b HP).
  er.
  follow (Incs2 b 1).
  es.
Qed.

Fixpoint F (n:nat) :=
match n with
| O => O
| S n0 => (F n0)*8+7
end.

Fixpoint F0 (n:nat) :=
match n with
| O => []
| S n0 => ((F n0)*16+15,(F n0)*96+93)::(F0 n0)
end.

Fixpoint F1 (n:nat) :=
match n with
| O => []
| S n0 => ((F n0)*8+7,(F n0)*48+45)::(F1 n0)
end.

Fixpoint F2 (n:nat) :=
match n with
| O => []
| S n0 => ((F n0)*4+3,(F n0)*24+21)::(F2 n0)
end.

Ltac flia := repeat (lia || f_equal).

Lemma F0_n n:
  P lh0 lh1 (F0 n) (F1 n) ((F n)*8+7).
Proof.
  induction n.
  1: apply P_0.
  cbn[F0]; cbn[F1]; cbn[F].
  epose proof (P_S ((F n)*16+15) ((F n)*64+63) IHn).
  applys_eq H; flia.
Qed.

Lemma F1_n n:
  P lh1 lh2 (F1 n) (F2 n) ((F n)*4+3).
Proof.
  induction n.
  1: apply P_1.
  cbn[F1]; cbn[F2]; cbn[F].
  epose proof (P_S ((F n)*8+7) ((F n)*32+31) IHn).
  applys_eq H; flia.
Qed.

Lemma F2_n n:
  P lh2 lh0 (F2 (S n)) (F0 n) ((F n)*16+15).
Proof.
  induction n.
  1: apply P_2.
  cbn[F0]; cbn[F2]; cbn[F].
  epose proof (P_S ((F n)*32+31) ((F n)*128+127) IHn).
  applys_eq H; flia.
Qed.

Definition config n :=
  S0 lh2 (((F n)*32+31,(F n)*64+60)::F2 (S n)) 0.

Ltac follow' H :=
  match goal with
  | |- _ -[ _ ]->* _ => eapply progress_evstep
  | _ => idtac
  end;
  match type of H with
  | _ -[ _ ]->+ _ =>
    eapply progress_evstep_trans; [ eapply evstep_progress_trans; [| apply H]; finish | ]
  | _ -[ _ ]->* _ =>
    eapply evstep_trans; [ eapply evstep_trans; [| apply H]; finish | ]
  end.

Lemma BigStep n:
  config n -->+
  config (S n).
Proof.
  unfold config.

  epose proof (BigStep_2 ((F n)*32+30)) as H.
  follow' H. clear H.
  epose proof (BigStep_1 (F2_n n)) as H.
  follow H. clear H.
  epose proof (BigStep_3 ((F n)*16+15) ((F n)*64+62) (F0_n n)) as H.
  follow H. clear H.
  epose proof (BigStep_1 (F1_n (S n))) as H.
  cbn[F1] in H.
  follow H. clear H.
  cbn[F].
  epose proof (BigStep_3 ((F n)*32+31) ((F n)*64+62) (F2_n n)) as H.
  follow H. clear H.
  epose proof (BigStep_1 (F0_n (S n))) as H.
  cbn[F0] in H.
  follow H. clear H.
  cbn[F].

  epose proof (BigStep_2 ((F n)*64+62)) as H.
  follow' H. clear H.
  remember (S n) as n0.
  assert (HFn0:F n0 = (F n)*8+7) by (subst n0; cbn; lia).
  replace ((F n*64+62)) with ((F n0)*8+6) by lia.
  epose proof (BigStep_1 (F1_n n0)) as H.
  follow H. clear H.
  epose proof (BigStep_3 ((F n0)*4+3) ((F n0)*16+14) (F2_n n)) as H.
  follow H. clear H.
  replace ((F n)*16+15) with ((F n0)*2+1) by lia.
  epose proof (BigStep_1 (F0_n (S n))) as H.
  cbn[F0] in H.
  follow H. clear H.
  rewrite <-Heqn0.
  epose proof (BigStep_3 ((F n0)*8+7) ((F n0)*16+14) (F1_n n0)) as H.
  follow H. clear H.
  epose proof (BigStep_1 (F2_n (n0))) as H.
  cbn[F2] in H.
  follow H. clear H.

  epose proof (BigStep_2 ((F n0)*16+14)) as H.
  follow' H. clear H.
  epose proof (BigStep_1 (F0_n n0)) as H.
  follow H. clear H.
  epose proof (BigStep_3 ((F n0)*8+7) ((F n0)*32+30) (F1_n n0)) as H.
  follow H. clear H.
  epose proof (BigStep_1 (F2_n n0)) as H.
  cbn[F2] in H.
  follow H. clear H.
  epose proof (BigStep_3 ((F n0)*16+15) ((F n0)*32+30) (F0_n n0)) as H.
  follow H. clear H.
  epose proof (BigStep_1 (F1_n (S n0))) as H.
  cbn[F1] in H.
  follow H. clear H.

  cbn[F].
  finish.
Qed.

From BusyCoq Require TC25.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config O).
  - remember (29898%N) as T.
    epose proof (TC25.TC25.TC_state_decide_spec tm [([T],O)]) as H.
    remember (TC25.TC25.TC_state.decide tm [([T], O)]) as v1.
    subst T.
    vm_compute in Heqv1.
    subst v1.
    destruct H as [n' [H _]].
    inverts H.
    eapply without_counter.
    rewrite <-TC25.TC25.TM.multistep_c_spec in H5.
    rewrite multistep_c_spec in H5.
    applys_eq H5.
    cbv.
    repeat rewrite <-const_unfold.
    reflexivity.
  - eapply progress_nonhalt_simple with (C:=config).
    intros i.
    exists (S i).
    apply BigStep.
Qed.

End TM1.

