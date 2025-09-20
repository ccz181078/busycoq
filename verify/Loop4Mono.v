From BusyCoq Require Import Individual62 Longitudinal.
Require Import Zify Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.


Notation "a ^^^ b" := (flat_map a b) (at level 20).

Lemma Llist{T}(ls:list T)(f g:T->list Sym) tm QL qL:
  (forall l r x,
  l <* (f x) <{{QL}} qL *> r -[ tm ]->*
  l <{{QL}} qL *> (g x) *> r) ->
  forall l r,
  l <* f^^^ls <{{QL}} qL *> r -[ tm ]->*
  l <{{QL}} qL *> g^^^(rev ls) *> r.
Proof.
  intros H.
  induction ls; intros; cbn.
  - finish.
  - rewrite flat_map_app.
    cbn.
    repeat rewrite Str_app_assoc.
    follow H.
    follow IHls.
    finish.
Qed.

Lemma Rlist{T}(ls:list T)(f g:T->list Sym) tm QR qR:
  (forall l r x,
  l <* qR {{QR}}> (f x) *> r -[ tm ]->*
  l <* (g x) <* qR {{QR}}> r) ->
  forall l r,
  l <* qR {{QR}}> f^^^ls *> r -[ tm ]->*
  l <* g^^^(rev ls) <* qR {{QR}}> r.
Proof.
  intros H.
  induction ls; intros; cbn.
  - finish.
  - rewrite flat_map_app.
    cbn.
    repeat rewrite Str_app_assoc.
    follow H.
    follow IHls.
    finish.
Qed.

Fixpoint sum (ls:list nat) :=
match ls with
| [] => O
| h::t => h+sum t
end.

Fixpoint sum' ls :=
match ls with
| [] => []
| h::t => (sum ls)::(sum' t)
end.

Lemma length_sum' ls:
  length (sum' ls) = length ls.
Proof.
  induction ls; cbn; congruence.
Qed.

Lemma sum_app ls1 ls2:
  sum (ls1++ls2) = sum ls1 + sum ls2.
Proof.
  induction ls1; cbn; lia.
Qed.

Lemma sum_all0 n:
  sum ([O]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma sum'_all0 n:
  sum' ([O]^^n) = [O]^^n.
Proof.
  induction n; cbn; trivial.
  rewrite sum_all0,IHn; trivial.
Qed.

Lemma sum'_app ls1 ls2:
  sum' (ls1++ls2) =
  (map (Nat.add (sum ls2)) (sum' ls1)) ++ sum' ls2.
Proof.
  induction ls1; cbn.
  - trivial.
  - rewrite IHls1.
    cbn.
    f_equal.
    rewrite sum_app.
    lia.
Qed.

Lemma map_lpow{A B} (f:A->B) (a:list A) n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn; try rewrite map_app; congruence.
Qed.

Lemma sum_lpow a n:
  sum (a^^n) = (sum a)*n.
Proof.
  induction n; cbn.
  - lia.
  - rewrite sum_app; lia.
Qed.

Ltac rw_ls :=
  repeat (
  cbn in * ||
  rewrite sum_app in * ||
  rewrite sum'_app in * ||
  rewrite sum_all0 in * ||
  rewrite sum'_all0 in * ||
  rewrite <-app_assoc in * ||
  rewrite length_sum' in * ||
  rewrite length_app in * ||
  rewrite lpow_length in * ||
  rewrite sum_lpow in * ||
  rewrite map_app in * ||
  rewrite map_id in * ||
  rewrite map_map in * ||
  rewrite map_lpow in * ||
  rewrite length_map in *
  ).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0RA_1LD0LF_0RE0LA_0RB1RE_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([O],2)).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto; congruence.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0RA_1LD1LE_1RC0LA_---0RF_0RB1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{F}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([O],2)).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto; congruence.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA1LE_1LD1RB_1LB0RC_---0RF_0RD1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{F}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0],1)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 10; congruence.
Qed.

End TM3.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC0LE_0RD1RC_1LA0RE_1LD1RA_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{C}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 10; congruence.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1LC0LF_0RD0LE_0RA1RD_1LA1RB_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{D}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;0],3)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 10; congruence.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB1LF_0RC0LE_0RD1RC_1LA0RE_1LD1RA_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{C}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 10; congruence.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB1LC_1RA0LF_---0RD_0RE1RD_1LA0RF_1LE1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{D}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 10; congruence.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1LB0RE_1LC1LF_0RD0LE_0RA1RD_1LA1RB_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{D}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;0],3)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 10; congruence.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC1LD_1RB0LF_---0RE_0RA1RE_1LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;0],3)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 10; congruence.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_0LE0LD_1LC1LA_0RA0LF_0RB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{F}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O] in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^b,(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) b _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;2;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_0LE0LD_1LC1LA_0RA0LF_0RB0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{F}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O] in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^b,(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) b _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;2;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LF_0RD0LE_1RA---_0RA0RD_1LB1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{E}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O] in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^b,(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) b _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;2;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC---_1LE1RD_0RC0RB_0LA0LF_1LE1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{D}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[1])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [1])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[1]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[1]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [1]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [1]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[1]%nat in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+5 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[0]^^b,(sum a)+5-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a++[1])) (a1+sum (a++[1])) (sum' (a++[1])) b _)%nat as HB.
  rw_ls.
  repeat rewrite Nat.add_assoc in *.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;2],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC---_1LE1RD_0RC0RB_0LA0LF_1LE0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{D}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[1])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [1])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[1]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[1]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [1]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [1]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[1]%nat in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+5 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[0]^^b,(sum a)+5-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a++[1])) (a1+sum (a++[1])) (sum' (a++[1])) b _)%nat as HB.
  rw_ls.
  repeat rewrite Nat.add_assoc in *.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;2],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LF_1LD0LE_1RA---_0RA0RD_1LB0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{E}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[1])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [1])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[1]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[1]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [1]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [1]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[1]%nat in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+5 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[0]^^b,(sum a)+5-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a++[1])) (a1+sum (a++[1])) (sum' (a++[1])) b _)%nat as HB.
  rw_ls.
  repeat rewrite Nat.add_assoc in *.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;2;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_0LE0LD_1LC1LA_1LA0LF_0RB0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{F}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[1])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [1])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[1]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[1]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [1]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [1]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[1]%nat in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+5 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[0]^^b,(sum a)+5-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a++[1])) (a1+sum (a++[1])) (sum' (a++[1])) b _)%nat as HB.
  rw_ls.
  repeat rewrite Nat.add_assoc in *.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_0LE0LD_1LC0RC_1LA0LF_0RB0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{F}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[1])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [1])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[1]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[1]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [1]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [1]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[1]%nat in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+5 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[0]^^b,(sum a)+5-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a++[1])) (a1+sum (a++[1])) (sum' (a++[1])) b _)%nat as HB.
  rw_ls.
  repeat rewrite Nat.add_assoc in *.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB1LD_0LC0LA_1LD0LF_1RE---_1LB1RF_0RE0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{F}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[1])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [1])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[1]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[1]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[1;1])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [1]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [1]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[1]%nat in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+5 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[0]^^b,(sum a)+5-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a++[1])) (a1+sum (a++[1])) (sum' (a++[1])) b _)%nat as HB.
  rw_ls.
  repeat rewrite Nat.add_assoc in *.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC0RD_1LA1RB_1RC0LE_0LB---_1LA1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{B}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[a1;O]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1'' a2 a1 b0 b1 b:
  S1 [a2] a1 (b0::b1::b) 0 -->+
  S1 (b++[a1+2;a2;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  do 9 step1.
  rewrite flat_map_app.
  cbn[flat_map].
  unfold LS.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[a1;0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1'' a a1 b0 b1 b:
  S1 (a++[O]) a1 (b0::b1::b) ((length a)) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0;0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  - cbn.
    follow10 Ov1''.
    simpl'; finish.
  - cbn in *.
    follow Inc1.
    follow10 IHa.
    simpl'; finish.
Qed. 

Lemma IncsOv1' a a1 b0 b1 b:
  S1 (a++[O]) a1 (b0::b1::b) (1+(length a)) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0;0;0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  - cbn.
    follow Inc1.
    cbn.
    follow10 Ov1'.
    simpl'; finish.
  - cbn in *.
    follow Inc1.
    follow10 IHa.
    simpl'; finish.
Qed. 

Lemma BigStep_O' a0 a1 a2 a:
  S1 (a1::a2::a++[O]) a0 [] ((2+length a)) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0;0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1''.
  finish.
Qed.

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a++[O]) a0 [] ((3+length a)) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0;0;0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 (a++[O]) a1 b (2 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))++[O;O]) c.
Proof.
  gen a1 b c.
  induction a; intros.
  - cbn.
    follow Inc1.
    follow Ov1.
    cbn.
    simpl'; finish.
  - cbn in *.
    follow Inc1.
    follow IHa.
    simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a++[O]) a0 [] (4+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(2+c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  cbn in *.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a++[O]) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c as [|[|c]].
  - rewrite Nat.add_0_r.
    follow10 BigStep_O'.
    finish.
  - cbn.
    rewrite Nat.add_1_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S (S c)) with (4+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Lemma init: c0 -->* S1 [2;O;O] 2 [] 4.
Proof.
  unfold S1; cbn. solve_init.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O;O] in
  S1 (sum' a') (a0+sum a') [] (1+(length a)+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^(b),(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) b _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  rewrite Nat.add_1_r in HB.
  follow10 HB.
  repeat rewrite lpow_add.
  rw_ls.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;2;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0LE_0RA0RD_1RA0LF_1LB1LD_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{C}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[a1;O]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1'' a2 a1 b0 b1 b:
  S1 [a2] a1 (b0::b1::b) 0 -->+
  S1 (b++[a1+2;a2;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  do 9 step1.
  rewrite flat_map_app.
  cbn[flat_map].
  unfold LS.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[a1;0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1'' a a1 b0 b1 b:
  S1 (a++[O]) a1 (b0::b1::b) ((length a)) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0;0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  - cbn.
    follow10 Ov1''.
    simpl'; finish.
  - cbn in *.
    follow Inc1.
    follow10 IHa.
    simpl'; finish.
Qed. 

Lemma IncsOv1' a a1 b0 b1 b:
  S1 (a++[O]) a1 (b0::b1::b) (1+(length a)) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0;0;0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  - cbn.
    follow Inc1.
    cbn.
    follow10 Ov1'.
    simpl'; finish.
  - cbn in *.
    follow Inc1.
    follow10 IHa.
    simpl'; finish.
Qed. 

Lemma BigStep_O' a0 a1 a2 a:
  S1 (a1::a2::a++[O]) a0 [] ((2+length a)) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0;0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1''.
  finish.
Qed.

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a++[O]) a0 [] ((3+length a)) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0;0;0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 (a++[O]) a1 b (2 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))++[O;O]) c.
Proof.
  gen a1 b c.
  induction a; intros.
  - cbn.
    follow Inc1.
    follow Ov1.
    cbn.
    simpl'; finish.
  - cbn in *.
    follow Inc1.
    follow IHa.
    simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a++[O]) a0 [] (4+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(2+c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  cbn in *.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a++[O]) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c as [|[|c]].
  - rewrite Nat.add_0_r.
    follow10 BigStep_O'.
    finish.
  - cbn.
    rewrite Nat.add_1_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S (S c)) with (4+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O;O] in
  S1 (sum' a') (a0+sum a') [] (1+(length a)+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^(b),(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) b _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  rewrite Nat.add_1_r in HB.
  follow10 HB.
  repeat rewrite lpow_add.
  rw_ls.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;2;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1LB1LD_0LC0LA_0RD0LF_1RE---_1LB1RF_0RE0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{F}}> r) (at level 30).

Definition LS n :=
  [1;1;0] ++ [1;0]^^(1+n).

Definition LS' n :=
  [1;1;1;0] ++ [1;0]^^n.

Definition RS n :=
  [0;1]^^(1+n) ++ [1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* [1;1] <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0])%nat b1 [] (2+b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0])%nat (2+a1) [] (4+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0])%nat b1 [] (2+b0).
Proof.
  unfold S1,S2.
  remember (b0::b1::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  unfold LS.
  es; er.
  follow LS_L.
  es; er.
  follow RS_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  er.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(c+2))%nat (2+a1) [] (4+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  a<>[] ->
  S1 (a1::a) a0 [] (1+length a+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^(c+1))%nat (2+a1) [] (4+a0).
Proof.
  intros Ha.
  destruct a as [|a2 a].
  1: congruence.
  destruct c.
  - rewrite Nat.add_0_r.
    follow10 BigStep_O.
    finish.
  - replace (1+length (a2::a)+S c) with (3+length a+c) by (cbn; lia).
    follow10 BigStep_S.
    finish.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O] in
  S1 (sum' a') (a0+sum a') [] ((length a')+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 3 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^b,(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) b _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  follow10 HB.
  rewrite lpow_add.
  finish.
  Unshelve.
  1: destruct a; cbn; congruence.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;2;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0RA_1LD1LF_0RE0LA_0RB1RE_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).

Definition LS n :=
  [1]^^(2+n) ++ [0;0;0;1].

Definition RS n :=
  [0;1;1;1] ++ [1]^^(2+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a b c :=
  0inf <* [1;1] <* LS^^^a <* <[1;0;1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[3+a0]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 3) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Definition S2 b c :=
  0inf <* [1;1] <* LS^^^b <| [0;1;1] *> [1]^^c *> 0inf.

Lemma Ov1 b c:
  S1 [] b (1+c) -->*
  S2 (b++[3]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Ov1' b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[3]) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as v1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst v1.
  simpl'.
  es.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b:
  S2 (b0::b) 0 -->+
  S1 (b++[0]%nat) [] (3+b0).
Proof.
  unfold S1,S2.
  remember (b0::b) as b1.
  follow LS_L.
  es; er.
  follow RS_R.
  subst b1.
  simpl'.
  unfold LS.
  es.
Qed.

Lemma BigStep a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 3) a ++ [3] ++ [0]^^b)%nat [] (a0+6).
Proof.
  destruct b.
  - follow Incs1.
    cbn[map].
    follow10 Ov1'.
    finish.
  - follow Incs1.
    follow Ov1.
    follow Incs2.
    cbn.
    simpl'.
    follow10 Ov2.
    simpl'.
    rewrite lpow_shift.
    finish.
Qed.

Definition S1' '(a,b) := S1 (sum' a) [] ((length a)+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+6 >= (length a) + b->
  Forall (fun x => x<=3) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [3] ++ [0]^^b, (sum a)+6-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([O],2)).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto; congruence.
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1LB0LD_0RC0LE_1RD1RC_1LA1RE_1LF1RB_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{C}}> r) (at level 30).

Definition LS n :=
  [1;1]^^(n) ++ [1;1;1;1;1;0].

Definition LS' n :=
  [1;1]^^(n) ++ [1;1;1;1;0].

Definition RS n :=
  [1;1]^^(n) ++ [1;0;1;1;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  unfold LS'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1'''' a1 a2 a3 a4 b0 b1 b:
  S1 [a2;a3;a4] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;2+a3;2+a4])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1''' a1 a2 a3 b0 b1 b:
  S1 [a2;a3] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;2+a3;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1'' a1 a2 b0 b1 b:
  S1 [a2] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;0;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1'''' a a1 a2 a3 a4 b0 b1 b:
  S1 (a2::a3::a4::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a3::a4::a))++[0]^^0)%nat b1 [] (b0).
Proof.
  gen a1 a2 a3 a4 b0 b1 b.
  induction a; intros.
  1: apply Ov1''''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1''' a a1 a2 a3 b0 b1 b:
  S1 (a2::a3::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a3::a))++[0]^^1)%nat b1 [] (b0).
Proof.
  gen a1 a2 a3 b0 b1 b.
  induction a; intros.
  1: apply Ov1'''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1'' a a1 a2 b0 b1 b:
  S1 (a2::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a))++[0]^^2)%nat b1 [] (b0).
Proof.
  gen a1 a2 b0 b1 b.
  induction a; intros.
  1: apply Ov1''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0]^^3)%nat b1 [] (b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0]^^3)%nat (2+a1) [] (2+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(c+4))%nat (2+a1) [] (2+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  length a >= 5 ->
  S1 (a1::a) a0 [] (length a-2+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^c)%nat (2+a1) [] (2+a0).
Proof.
  intros H.
  destruct a as [|a2[|a3 a]].
  1,2: cbn in H; lia.
  destruct a as [|a4[|a5 a]].
  1,2: cbn in H; lia.
  destruct c as [|[|[|[|c]]]].
  1-4:
    cbn;
    do 2 follow Inc1;
    cbn;
    rewrite Nat.add_comm.
  - apply IncsOv1''''.
  - apply IncsOv1'''.
  - apply IncsOv1''.
  - apply IncsOv1'.
  - epose proof (BigStep_S a0 a1 a2 (a3::a4::a5::a) c) as HB.
    replace (c+4) with (4+c) in HB by lia.
    cbn in *.
    repeat rewrite Nat.add_succ_r.
    apply HB.
Qed.

Lemma init: c0 -->* S1 [2;2;2;0;0;0]%nat 4 [] 6.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O] in
  S1 (sum' a') (a0+sum a') [] ((length a'-2)+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 6 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^(b),(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) (b+1) _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  replace (length a+1-2+(b+1)) with ((length a+1-1+b)) in HB by lia.
  follow10 HB.
  repeat rewrite lpow_add.
  rw_ls.
  finish.
  Unshelve.
  1: rw_ls; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;0;0;2;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1RE_1LD0LB_0RA0LE_1LF1RD_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Definition LS n :=
  [1;1]^^(n) ++ [1;1;1;1;1;0].

Definition LS' n :=
  [1;1]^^(n) ++ [1;1;1;1;0].

Definition RS n :=
  [1;1]^^(n) ++ [1;0;1;1;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  unfold LS'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1'''' a1 a2 a3 a4 b0 b1 b:
  S1 [a2;a3;a4] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;2+a3;2+a4])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1''' a1 a2 a3 b0 b1 b:
  S1 [a2;a3] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;2+a3;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1'' a1 a2 b0 b1 b:
  S1 [a2] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;0;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1'''' a a1 a2 a3 a4 b0 b1 b:
  S1 (a2::a3::a4::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a3::a4::a))++[0]^^0)%nat b1 [] (b0).
Proof.
  gen a1 a2 a3 a4 b0 b1 b.
  induction a; intros.
  1: apply Ov1''''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1''' a a1 a2 a3 b0 b1 b:
  S1 (a2::a3::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a3::a))++[0]^^1)%nat b1 [] (b0).
Proof.
  gen a1 a2 a3 b0 b1 b.
  induction a; intros.
  1: apply Ov1'''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1'' a a1 a2 b0 b1 b:
  S1 (a2::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a))++[0]^^2)%nat b1 [] (b0).
Proof.
  gen a1 a2 b0 b1 b.
  induction a; intros.
  1: apply Ov1''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0]^^3)%nat b1 [] (b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0]^^3)%nat (2+a1) [] (2+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(c+4))%nat (2+a1) [] (2+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  length a >= 5 ->
  S1 (a1::a) a0 [] (length a-2+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^c)%nat (2+a1) [] (2+a0).
Proof.
  intros H.
  destruct a as [|a2[|a3 a]].
  1,2: cbn in H; lia.
  destruct a as [|a4[|a5 a]].
  1,2: cbn in H; lia.
  destruct c as [|[|[|[|c]]]].
  1-4:
    cbn;
    do 2 follow Inc1;
    cbn;
    rewrite Nat.add_comm.
  - apply IncsOv1''''.
  - apply IncsOv1'''.
  - apply IncsOv1''.
  - apply IncsOv1'.
  - epose proof (BigStep_S a0 a1 a2 (a3::a4::a5::a) c) as HB.
    replace (c+4) with (4+c) in HB by lia.
    cbn in *.
    repeat rewrite Nat.add_succ_r.
    apply HB.
Qed.

Lemma init: c0 -->* S1 [4;4;2;0;0;0]%nat 4 [] 6.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O] in
  S1 (sum' a') (a0+sum a') [] ((length a'-2)+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 6 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^(b),(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) (b+1) _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  replace (length a+1-2+(b+1)) with ((length a+1-1+b)) in HB by lia.
  follow10 HB.
  repeat rewrite lpow_add.
  rw_ls.
  finish.
  Unshelve.
  1: rw_ls; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0;0;2;2;0;0],2)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LA_0RD0LE_1RA1RD_1LF1RC_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{D}}> r) (at level 30).

Definition LS n :=
  [1;1]^^(n) ++ [1;1;1;1;1;0].

Definition LS' n :=
  [1;1]^^(n) ++ [1;1;1;1;0].

Definition RS n :=
  [1;1]^^(n) ++ [1;0;1;1;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Definition S2 b c :=
  0inf <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Ov1 a1 b c:
  S1 [] a1 b (1+c) -->*
  S2 (b++[2+a1]) c.
Proof.
  unfold S1,S2.
  simpl'.
  follow LS_L.
  unfold LS'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1'''' a1 a2 a3 a4 b0 b1 b:
  S1 [a2;a3;a4] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;2+a3;2+a4])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1''' a1 a2 a3 b0 b1 b:
  S1 [a2;a3] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;2+a3;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1'' a1 a2 b0 b1 b:
  S1 [a2] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma Ov1' a1 b0 b1 b:
  S1 [] a1 (b0::b1::b) 0 -->+
  S1 (b++[2+a1;0;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  es.
Qed.

Lemma IncsOv1'''' a a1 a2 a3 a4 b0 b1 b:
  S1 (a2::a3::a4::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a3::a4::a))++[0]^^0)%nat b1 [] (b0).
Proof.
  gen a1 a2 a3 a4 b0 b1 b.
  induction a; intros.
  1: apply Ov1''''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1''' a a1 a2 a3 b0 b1 b:
  S1 (a2::a3::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a3::a))++[0]^^1)%nat b1 [] (b0).
Proof.
  gen a1 a2 a3 b0 b1 b.
  induction a; intros.
  1: apply Ov1'''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1'' a a1 a2 b0 b1 b:
  S1 (a2::a) a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a2::a))++[0]^^2)%nat b1 [] (b0).
Proof.
  gen a1 a2 b0 b1 b.
  induction a; intros.
  1: apply Ov1''.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma IncsOv1' a a1 b0 b1 b:
  S1 a a1 (b0::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a))++[0]^^3)%nat b1 [] (b0).
Proof.
  gen a1 b0 b1 b.
  induction a; intros.
  1: apply Ov1'.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed. 

Lemma BigStep_O a0 a1 a2 a:
  S1 (a1::a2::a) a0 [] (2+length a) -->+
  S1 (map (Nat.add 2) (a2::a) ++ [0]^^3)%nat (2+a1) [] (2+a0).
Proof.
  cbn[Nat.add].
  do 2 follow Inc1.
  cbn.
  follow10 IncsOv1'.
  finish.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[0]%nat) c.
Proof.
  unfold S2.
  simpl'.
  follow LS_L.
  es; er.
  follow RS_R.
  es.
Qed.

Lemma IncsOv1 a a1 b c:
  S1 a a1 b (1 + length a + c) -->*
  S2 (b++(map (Nat.add 2) (a1::a))) c.
Proof.
  gen a1 b c.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[0]^^c)%nat 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 (b++[0;0;0;0])%nat b1 [] (b0).
Proof.
  unfold S1,S2.
  do 4 follow_L_R.
  do 4 (er; sr).
  do 2 rewrite <-lpow_shift2.
  repeat step1; sr.
  rewrite flat_map_app.
  repeat (cbn || rewrite Str_app_assoc).
  es.
Qed.

Lemma BigStep_S a0 a1 a2 a c:
  S1 (a1::a2::a) a0 [] (3+length a+c) -->+
  S1 ((map (Nat.add 2) (a2::a)) ++ [0]^^(c+4))%nat (2+a1) [] (2+a0).
Proof.
  epose proof (IncsOv1 (a1::a2::a) a0 [] c) as HI.
  follow HI.
  follow Incs2.
  rw_ls.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep a0 a1 a c:
  length a >= 5 ->
  S1 (a1::a) a0 [] (length a-2+c) -->+
  S1 ((map (Nat.add 2) (a)) ++ [0]^^c)%nat (2+a1) [] (2+a0).
Proof.
  intros H.
  destruct a as [|a2[|a3 a]].
  1,2: cbn in H; lia.
  destruct a as [|a4[|a5 a]].
  1,2: cbn in H; lia.
  destruct c as [|[|[|[|c]]]].
  1-4:
    cbn;
    do 2 follow Inc1;
    cbn;
    rewrite Nat.add_comm.
  - apply IncsOv1''''.
  - apply IncsOv1'''.
  - apply IncsOv1''.
  - apply IncsOv1'.
  - epose proof (BigStep_S a0 a1 a2 (a3::a4::a5::a) c) as HB.
    replace (c+4) with (4+c) in HB by lia.
    cbn in *.
    repeat rewrite Nat.add_succ_r.
    apply HB.
Qed.

Lemma init: c0 -->* S1 [2;2;2;0;0;0]%nat 4 [] 4.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Definition S1' '(a,c) :=
match a with
| a0::a =>
  let a':=a++[O] in
  S1 (sum' a') (a0+sum a') [] ((length a'-2)+c)
| _ => c0
end.

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  length a >= 6 ->
  (sum a)+4 >= (length a) + b ->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x:=(tl a++[2]++[O]^^(b),(sum a)+4-((length a)+b)) in
  S1' (a,b) -->+
  S1' x /\
  P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 [|a1 a]].
  1,2: cbn in H1; lia.
  split.
  2: {
    cbn in *.
    econstructor.
    - rw_ls. lia.
    - rw_ls.
      inverts H3.
      lia.
    - inverts H3.
      inverts H5.
      constructor; auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep (a0+sum (a1::a)) (a1+sum a) (sum' a++[O]) (b+1) _) as HB.
  rw_ls.
  rewrite Nat.add_0_r.
  replace (length a+1-2+(b+1)) with ((length a+1-1+b)) in HB by lia.
  follow10 HB.
  repeat rewrite lpow_add.
  rw_ls.
  finish.
  Unshelve.
  1: rw_ls; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;0;0;2;0;0],0)%nat).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; repeat (lia || constructor).
Qed.

End TM26.


Module TM27.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE0LB_1LA1LF_1LC1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{A}}> r) (at level 30).

Definition LS n :=
  [1;1]^^(n) ++ [1;1;1;1;0].

Definition LS' n :=
  [1;1]^^(n) ++ [1;1;1;1;1;1;1;0].

Definition RS n :=
  [1;1]^^(n) ++ [1;1;1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1 a1 a2 b0 b1 b:
  S1 [a2] a1 ((2+b0)::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;1;0])%nat b1 [] b0.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma IncsOv1 a a1 a2 b0 b1 b:
  S1 (a++[a2]) a1 ((2+b0)::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a++[a2])) ++ [1;0])%nat b1 [] b0.
Proof.
  gen a1 a2 b0 b1 b.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed.

Definition S1' n := (S1 (sum' ([1]^^(2+n)++[0])) (3+n) [7+n;6+n] (2+n))%nat.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' 0).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  exists (1+n).
  unfold S1'.
  epose proof (IncsOv1 (sum' ([1]^^(2+n)))%nat (3+n) 0 (5+n) (6+n) []) as HI.
  replace (2+(1+n)) with (1+(n+2)) by lia.
  rw_ls.
  repeat rewrite Nat.add_0_r in *.
  rewrite Nat.mul_1_r in *.
  follow10 HI.
  follow Inc1.
  follow Inc1.
  rewrite lpow_add.
  rw_ls.
  rewrite (Nat.add_comm n 2).
  cbn.
  finish.
Qed.

End TM27.

Module TM28.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC0RA_1LD1RC_---0LE_1LF0LB_1LA1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{A}}> r) (at level 30).

Definition LS n :=
  [1;1]^^(n) ++ [1;1;1;1;0].

Definition LS' n :=
  [1;1]^^(n) ++ [1;1;1;1;1;1;1;0].

Definition RS n :=
  [1;1]^^(n) ++ [1;1;1;0;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [1] *> [1;1]^^c *> 0inf.

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) a1 b (1+c) -->*
  S1 a a0 (b++[2+a1]) c.
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1 a1 a2 b0 b1 b:
  S1 [a2] a1 ((2+b0)::b1::b) 0 -->+
  S1 (b++[2+a1;2+a2;1;0])%nat b1 [] b0.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma IncsOv1 a a1 a2 b0 b1 b:
  S1 (a++[a2]) a1 ((2+b0)::b1::b) (length a) -->+
  S1 (b++(map (Nat.add 2) (a1::a++[a2])) ++ [1;0])%nat b1 [] b0.
Proof.
  gen a1 a2 b0 b1 b.
  induction a; intros.
  1: apply Ov1.
  cbn in *.
  follow Inc1.
  follow10 IHa.
  simpl'; finish.
Qed.

Definition S1' n := (S1 (sum' ([1]^^(2+n)++[0])) (3+n) [7+n;6+n] (2+n))%nat.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' 0).
  1: unfold S1',S1; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  exists (1+n).
  unfold S1'.
  epose proof (IncsOv1 (sum' ([1]^^(2+n)))%nat (3+n) 0 (5+n) (6+n) []) as HI.
  replace (2+(1+n)) with (1+(n+2)) by lia.
  rw_ls.
  repeat rewrite Nat.add_0_r in *.
  rewrite Nat.mul_1_r in *.
  follow10 HI.
  follow Inc1.
  follow Inc1.
  rewrite lpow_add.
  rw_ls.
  rewrite (Nat.add_comm n 2).
  cbn.
  finish.
Qed.

End TM28.


Lemma map_feq{A B}(f g:A->B)(a b:list A):
  (forall x, f x = g x) ->
  a=b ->
  map f a = map g b.
Proof.
  intros.
  subst.
  induction b; cbn; try rewrite H,IHb; trivial.
Qed.

Ltac flia := repeat (lia || (apply map_feq; [intros|]) || f_equal).

Lemma map_sum'_rot x y n b:
  map (Nat.add (x+y)) (sum' ([x]^^n)) ++ (x+y)::y::b =
  map (Nat.add y) (sum' ([x]^^(S n))) ++ y::b.
Proof.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  rw_ls.
  flia.
Qed.

Ltac follow11 H :=
  eapply progress_trans;
  [ applys_eq H; try flia | ].

Ltac follow10 H :=
  eapply progress_evstep_trans;
  [ applys_eq H; try flia | ].


Module TM29.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_---0LD_1LE1LF_0RA1LC_0LE0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1;1;0;1] {{A}}> r) (at level 30).

Definition LS n :=
  [1;1;1;0]^^n ++ [1;1;0].

Definition LS' n :=
  [1;1;1;0]^^n ++ [1;1;1;1;0].

Definition RS n :=
  [0;1;0;1]^^(n) ++ [0;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1;0;1]^^c *> 0inf.

Close Scope sym.

Lemma Inc1 a0 a1 a b c:
  S1 a a0 (b++[1+a1]) c -->*
  S1 (a0::a) a1 b (1+c).
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1 a a0 a1 a2 c:
  S1 (a++[1+a1;1+a2;0]) a0 [] c -->+
  S1 [a2] (a1) (c::a0::a) 3.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma Ov1' a a0 a1 a2 c:
  S1 (a++[1+a1;1+a2;1]) a0 [] c -->+
  S1 [a2;O] (a1) (c::a0::a) 3.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma IncsOv1 a a0 a1 a2 b c:
  S1 (a++[1+a1;1+a2;0]) a0 (map S b) c -->+
  S1 [a2] a1 (((length b)+c)::b++a0::a) 3.
Proof.
  gen a a0 a1 a2 c.
  induction b using rev_ind; intros.
  1: apply Ov1.
  rewrite map_app.
  follow Inc1.
  follow10 (IHb (a0::a) x a1 a2 (1+c)).
  rw_ls.
  finish.
Qed.

Lemma IncsOv1' a a0 a1 a2 b c:
  S1 (a++[1+a1;1+a2;1]) a0 (map S b) c -->+
  S1 [a2;0] a1 (((length b)+c)::b++a0::a) 3.
Proof.
  gen a a0 a1 a2 c.
  induction b using rev_ind; intros.
  1: apply Ov1'.
  rewrite map_app.
  follow Inc1.
  follow10 (IHb (a0::a) x a1 a2 (1+c)).
  rw_ls.
  finish.
Qed.

Definition S1' a a0 b c :=
  S1 a a0 (map S b) c.

Lemma BigStep a0 a1 a2 b b0 c:
  S1' [1+a1;1+a2;0] (1+a0) ((map S b)++[1+b0]) c -->+
  S1' [a0;a1;a2] b0 (((length (b))+c)::b) 5.
Proof.
  unfold S1'.
  follow10 (IncsOv1 []).
  rewrite app_comm_cons.
  follow Inc1.
  rewrite app_comm_cons.
  follow Inc1.
  rw_ls.
  finish.
Qed.

Lemma BigStep' a0 a1 a2 b c:
  S1' [1+a1;1+a2;1] (1+a0) (map S b) (1+c) -->+
  S1' [a1;a2;0] a0 (((length (b))+c)::b) 4.
Proof.
  unfold S1'.
  follow10 (IncsOv1' []).
  rewrite app_comm_cons.
  follow Inc1.
  rw_ls.
  finish.
Qed.

Definition S1'' a b := S1' [2;1;0] 3 (sum' ([1]^^a++[2]++[1]^^b++[4])) 5.

Lemma BigStep_S a b:
  S1'' a (1+b) -->*
  S1'' (1+a) b.
Proof.
  unfold S1''.
  rewrite (Nat.add_comm 1 b).
  rewrite lpow_add,<-app_assoc.
  epose proof (BigStep 2 1 0 (sum' ([1]^^a++[2]++[1]^^b++[4])) 3 5) as HB.
  rw_ls.
  apply progress_evstep.
  applys_eq HB; flia.
Qed.

Lemma BigStep_Ss a b:
  S1'' a b -->*
  S1'' (b+a) 0.
Proof.
  gen a.
  ind b BigStep_S.
Qed.

Definition S1''' a := S1'' 0 (5+a).

Lemma BigStep'' a:
  S1'' 0 (5+a) -->+
  S1'' 0 (6+a).
Proof.
  follow BigStep_Ss.
  replace (5+a+0) with (a+5) by lia.
  unfold S1''.
  rewrite lpow_add.
  epose proof (BigStep 2 1 0 (sum' ([1]^^a++[1]^^5++[5])) 3 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(1+a)++[1]^^4++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 1 0 (sum' ([1]^^(2+a)++[1]^^3++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 2 0 (sum' ([1]^^(3+a)++[1]^^2++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 2 1 (sum' ([1]^^(4+a)++[1]^^1++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep' 3 2 1 (sum' ([1]^^(5+a)++[1]^^1++[4])) 4) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(6+a)++[4])) 3 4) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(6+a)++[4])) 3 5) as HB.
  rw_ls.
  rewrite (map_sum'_rot 1 4) in HB.
  rw_ls.
  applys_eq HB; flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1''' 0).
  1: unfold S1''',S1'',S1',S1; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i; exists (S i); apply BigStep''.
Qed.

End TM29.


Module TM30.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_---0LD_1LE1LF_0RA1LC_1RD0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1;1;0;1] {{A}}> r) (at level 30).

Definition LS n :=
  [1;1;1;0]^^n ++ [1;1;0].

Definition LS' n :=
  [1;1;1;0]^^n ++ [1;1;1;1;0].

Definition RS n :=
  [0;1;0;1]^^(n) ++ [0;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1;0;1]^^c *> 0inf.

Close Scope sym.

Lemma Inc1 a0 a1 a b c:
  S1 a a0 (b++[1+a1]) c -->*
  S1 (a0::a) a1 b (1+c).
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1 a a0 a1 a2 c:
  S1 (a++[1+a1;1+a2;0]) a0 [] c -->+
  S1 [a2] (a1) (c::a0::a) 3.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma Ov1' a a0 a1 a2 c:
  S1 (a++[1+a1;1+a2;1]) a0 [] c -->+
  S1 [a2;O] (a1) (c::a0::a) 3.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma IncsOv1 a a0 a1 a2 b c:
  S1 (a++[1+a1;1+a2;0]) a0 (map S b) c -->+
  S1 [a2] a1 (((length b)+c)::b++a0::a) 3.
Proof.
  gen a a0 a1 a2 c.
  induction b using rev_ind; intros.
  1: apply Ov1.
  rewrite map_app.
  follow Inc1.
  follow10 (IHb (a0::a) x a1 a2 (1+c)).
  rw_ls.
  finish.
Qed.

Lemma IncsOv1' a a0 a1 a2 b c:
  S1 (a++[1+a1;1+a2;1]) a0 (map S b) c -->+
  S1 [a2;0] a1 (((length b)+c)::b++a0::a) 3.
Proof.
  gen a a0 a1 a2 c.
  induction b using rev_ind; intros.
  1: apply Ov1'.
  rewrite map_app.
  follow Inc1.
  follow10 (IHb (a0::a) x a1 a2 (1+c)).
  rw_ls.
  finish.
Qed.

Definition S1' a a0 b c :=
  S1 a a0 (map S b) c.

Lemma BigStep a0 a1 a2 b b0 c:
  S1' [1+a1;1+a2;0] (1+a0) ((map S b)++[1+b0]) c -->+
  S1' [a0;a1;a2] b0 (((length (b))+c)::b) 5.
Proof.
  unfold S1'.
  follow10 (IncsOv1 []).
  rewrite app_comm_cons.
  follow Inc1.
  rewrite app_comm_cons.
  follow Inc1.
  rw_ls.
  finish.
Qed.

Lemma BigStep' a0 a1 a2 b c:
  S1' [1+a1;1+a2;1] (1+a0) (map S b) (1+c) -->+
  S1' [a1;a2;0] a0 (((length (b))+c)::b) 4.
Proof.
  unfold S1'.
  follow10 (IncsOv1' []).
  rewrite app_comm_cons.
  follow Inc1.
  rw_ls.
  finish.
Qed.

Definition S1'' a b := S1' [2;1;0] 3 (sum' ([1]^^a++[2]++[1]^^b++[4])) 5.

Lemma BigStep_S a b:
  S1'' a (1+b) -->*
  S1'' (1+a) b.
Proof.
  unfold S1''.
  rewrite (Nat.add_comm 1 b).
  rewrite lpow_add,<-app_assoc.
  epose proof (BigStep 2 1 0 (sum' ([1]^^a++[2]++[1]^^b++[4])) 3 5) as HB.
  rw_ls.
  apply progress_evstep.
  applys_eq HB; flia.
Qed.

Lemma BigStep_Ss a b:
  S1'' a b -->*
  S1'' (b+a) 0.
Proof.
  gen a.
  ind b BigStep_S.
Qed.

Definition S1''' a := S1'' 0 (5+a).

Lemma BigStep'' a:
  S1'' 0 (5+a) -->+
  S1'' 0 (6+a).
Proof.
  follow BigStep_Ss.
  replace (5+a+0) with (a+5) by lia.
  unfold S1''.
  rewrite lpow_add.
  epose proof (BigStep 2 1 0 (sum' ([1]^^a++[1]^^5++[5])) 3 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(1+a)++[1]^^4++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 1 0 (sum' ([1]^^(2+a)++[1]^^3++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 2 0 (sum' ([1]^^(3+a)++[1]^^2++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 2 1 (sum' ([1]^^(4+a)++[1]^^1++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep' 3 2 1 (sum' ([1]^^(5+a)++[1]^^1++[4])) 4) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(6+a)++[4])) 3 4) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(6+a)++[4])) 3 5) as HB.
  rw_ls.
  rewrite (map_sum'_rot 1 4) in HB.
  rw_ls.
  applys_eq HB; flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1''' 0).
  1: unfold S1''',S1'',S1',S1; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i; exists (S i); apply BigStep''.
Qed.

End TM30.


Module TM31.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_---0LD_1LE1LF_0RA1LC_0LE0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1;1;0;1] {{A}}> r) (at level 30).

Definition LS n :=
  [1;1;1;0]^^n ++ [1;1;0].

Definition LS' n :=
  [1;1;1;0]^^n ++ [1;1;1;1;0].

Definition RS n :=
  [0;1;0;1]^^(n) ++ [0;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Ltac simpl' :=
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Definition S1 a a1 b c :=
  0inf <* LS^^^a <* LS' a1 <* LS^^^b <| [0;1;0;1]^^c *> 0inf.

Close Scope sym.

Lemma Inc1 a0 a1 a b c:
  S1 a a0 (b++[1+a1]) c -->*
  S1 (a0::a) a1 b (1+c).
Proof.
  unfold S1.
  follow LS_L.
  unfold LS,LS'.
  simpl'.
  es; er.
  follow RS_R.
  es.
Qed.

Ltac follow_L_R :=
  unfold LS,LS';
  es; er; follow LS_L;
  es; er; follow RS_R.

Lemma Ov1 a a0 a1 a2 c:
  S1 (a++[1+a1;1+a2;0]) a0 [] c -->+
  S1 [a2] (a1) (c::a0::a) 3.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma Ov1' a a0 a1 a2 c:
  S1 (a++[1+a1;1+a2;1]) a0 [] c -->+
  S1 [a2;O] (a1) (c::a0::a) 3.
Proof.
  unfold S1.
  simpl'.
  do 3 follow_L_R.
  es.
Qed.

Lemma IncsOv1 a a0 a1 a2 b c:
  S1 (a++[1+a1;1+a2;0]) a0 (map S b) c -->+
  S1 [a2] a1 (((length b)+c)::b++a0::a) 3.
Proof.
  gen a a0 a1 a2 c.
  induction b using rev_ind; intros.
  1: apply Ov1.
  rewrite map_app.
  follow Inc1.
  follow10 (IHb (a0::a) x a1 a2 (1+c)).
  rw_ls.
  finish.
Qed.

Lemma IncsOv1' a a0 a1 a2 b c:
  S1 (a++[1+a1;1+a2;1]) a0 (map S b) c -->+
  S1 [a2;0] a1 (((length b)+c)::b++a0::a) 3.
Proof.
  gen a a0 a1 a2 c.
  induction b using rev_ind; intros.
  1: apply Ov1'.
  rewrite map_app.
  follow Inc1.
  follow10 (IHb (a0::a) x a1 a2 (1+c)).
  rw_ls.
  finish.
Qed.

Definition S1' a a0 b c :=
  S1 a a0 (map S b) c.

Lemma BigStep a0 a1 a2 b b0 c:
  S1' [1+a1;1+a2;0] (1+a0) ((map S b)++[1+b0]) c -->+
  S1' [a0;a1;a2] b0 (((length (b))+c)::b) 5.
Proof.
  unfold S1'.
  follow10 (IncsOv1 []).
  rewrite app_comm_cons.
  follow Inc1.
  rewrite app_comm_cons.
  follow Inc1.
  rw_ls.
  finish.
Qed.

Lemma BigStep' a0 a1 a2 b c:
  S1' [1+a1;1+a2;1] (1+a0) (map S b) (1+c) -->+
  S1' [a1;a2;0] a0 (((length (b))+c)::b) 4.
Proof.
  unfold S1'.
  follow10 (IncsOv1' []).
  rewrite app_comm_cons.
  follow Inc1.
  rw_ls.
  finish.
Qed.

Definition S1'' a b := S1' [2;1;0] 3 (sum' ([1]^^a++[2]++[1]^^b++[4])) 5.

Lemma BigStep_S a b:
  S1'' a (1+b) -->*
  S1'' (1+a) b.
Proof.
  unfold S1''.
  rewrite (Nat.add_comm 1 b).
  rewrite lpow_add,<-app_assoc.
  epose proof (BigStep 2 1 0 (sum' ([1]^^a++[2]++[1]^^b++[4])) 3 5) as HB.
  rw_ls.
  apply progress_evstep.
  applys_eq HB; flia.
Qed.

Lemma BigStep_Ss a b:
  S1'' a b -->*
  S1'' (b+a) 0.
Proof.
  gen a.
  ind b BigStep_S.
Qed.

Definition S1''' a := S1'' 0 (5+a).

Lemma BigStep'' a:
  S1'' 0 (5+a) -->+
  S1'' 0 (6+a).
Proof.
  follow BigStep_Ss.
  replace (5+a+0) with (a+5) by lia.
  unfold S1''.
  rewrite lpow_add.
  epose proof (BigStep 2 1 0 (sum' ([1]^^a++[1]^^5++[5])) 3 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(1+a)++[1]^^4++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 1 0 (sum' ([1]^^(2+a)++[1]^^3++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 2 0 (sum' ([1]^^(3+a)++[1]^^2++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 3 2 1 (sum' ([1]^^(4+a)++[1]^^1++[5])) 4 5) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep' 3 2 1 (sum' ([1]^^(5+a)++[1]^^1++[4])) 4) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(6+a)++[4])) 3 4) as HB.
  rw_ls.
  follow11 HB; clear HB.
  epose proof (BigStep 2 1 0 (sum' ([1]^^(6+a)++[4])) 3 5) as HB.
  rw_ls.
  rewrite (map_sum'_rot 1 4) in HB.
  rw_ls.
  applys_eq HB; flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1''' 0).
  1: unfold S1''',S1'',S1',S1; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros i; exists (S i); apply BigStep''.
Qed.

End TM31.


Module TM32.

Definition tm := Eval compute in (TM_from_str "1RB---_0LB0RC_1RD0LE_1RE0RA_1LC1LF_0LC1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1;0;1] {{D}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;1;0;1] {{B}}> r) (at level 30).

Definition LS n :=
  <[0;1;1] <+ <[0;1;0;1]^^n.

Definition RS n :=
  [0;1;0;1]^^n ++ [0;1;0].

Definition LS' n :=
  <[0;1;0] <+ <[0;1;0;1]^^n.

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 a0 a b c :=
  0inf <* <[0;1;0;1]^^a0 <* LS'^^^a <* LS^^^b <| [0;1;0;1]^^(1+c) *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Lemma Inc1 a0 a1 a b c:
  S1 a0 (1+a1::a) b c -->*
  S1 a0 a (b++[a1]) (2+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_1 a0 b c:
  S1 (1+a0) [] b c -->+
  S1 a0 (3+c::b) [] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_0 a0 b c:
  S1 0 [] (b++[a0]) c -->+
  S1 a0 (3+c::b) [] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a0 a b c:
  S1 a0 (map (Nat.add 1) a) b c -->*
  S1 a0 [] (b++a) ((length a)*2+c).
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; cbn; es.
Qed.

Lemma BigStep_1 a0 a:
  S1 (1+a0) (map (Nat.add 1) a) [] 0 -->+
  S1 a0 (3+(length a)*2::a) [] 0.
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Lemma BigStep_0 a0 a:
  S1 0 (map (Nat.add 1) (a++[a0])) [] 0 -->+
  S1 a0 (3+(length (a++[a0]))*2::a) [] 0.
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Definition S1' '(a0,a1,a) := S1 a0 (sum' (a++[a0+a1])) [] 0.

Inductive P: nat*nat*(list nat) -> Prop :=
| P_intro a0 a1 a:
  1<=a1 ->
  Forall (fun x => 1<=x) a ->
  sum (a++[a0+a1]) <= (length a)*2+5 ->
  a<>[] ->
  P (a0,a1,a)
.

Lemma BigStep_1' a0 a1 a:
  P (1+a0,a1,a) ->
  S1' (1+a0,a1,a) -->+
  S1' (a0,a1,(length a)*2+5-(sum a+a0+a1)::a).
Proof.
  intros HP.
  inverts HP.
  unfold S1'.
  epose proof (BigStep_1 a0 (sum' (a++[a0+a1]))) as I1.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Lemma BigStep_0' a0 a1 a:
  P (O,1+a0,a++[a1]) ->
  S1' (O,1+a0,(a++[a1])) -->+
  S1' (a0,a1,(length (a++[a1]))*2+5-(sum a+a0+a1)::a).
Proof.
  intros HP.
  inverts HP.
  unfold S1'.
  epose proof (BigStep_0 (a0) (sum' (a++[a0+a1]))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' (1,1,[3])%nat).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve [auto | lia | congruence].
  intros [[a0 a1] a] HP.
  epose proof HP as HP0.
  inverts HP0.
  destruct a0.
  - epose proof H5 as I1.
    eapply exists_last in I1.
    destruct I1 as [a' [a2 Ha]]; subst.
    destruct a1. 1: lia.
    eexists; split.
    1: apply BigStep_0',HP.
    rewrite Forall_app in H3.
    rewrite Forall_cons_iff in H3.
    econstructor.
    + lia.
    + eapply Forall_cons.
      2: tauto.
      rw_ls.
      lia.
    + rw_ls.
      lia.
    + congruence.
  - eexists; split.
    1: apply BigStep_1',HP.
    econstructor.
    + lia.
    + eapply Forall_cons.
      2: tauto.
      rw_ls.
      lia.
    + rw_ls.
      lia.
    + congruence.
Qed.

End TM32.


Module TM33.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1LF_1RA0LB_1RE---_0LE0RC_0LC1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1;0;1] {{A}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;1;0;1] {{E}}> r) (at level 30).

Definition LS n :=
  <[0;1;1] <+ <[0;1;0;1]^^n.

Definition RS n :=
  [0;1;0;1]^^n ++ [0;1;0].

Definition LS' n :=
  <[0;1;0] <+ <[0;1;0;1]^^n.

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 a0 a b c :=
  0inf <* <[0;1;0;1]^^a0 <* LS'^^^a <* LS^^^b <| [0;1;0;1]^^(1+c) *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Lemma Inc1 a0 a1 a b c:
  S1 a0 (1+a1::a) b c -->*
  S1 a0 a (b++[a1]) (2+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_1 a0 b c:
  S1 (1+a0) [] b c -->+
  S1 a0 (3+c::b) [] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_0 a0 b c:
  S1 0 [] (b++[a0]) c -->+
  S1 a0 (3+c::b) [] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a0 a b c:
  S1 a0 (map (Nat.add 1) a) b c -->*
  S1 a0 [] (b++a) ((length a)*2+c).
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; cbn; es.
Qed.

Lemma BigStep_1 a0 a:
  S1 (1+a0) (map (Nat.add 1) a) [] 0 -->+
  S1 a0 (3+(length a)*2::a) [] 0.
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Lemma BigStep_0 a0 a:
  S1 0 (map (Nat.add 1) (a++[a0])) [] 0 -->+
  S1 a0 (3+(length (a++[a0]))*2::a) [] 0.
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Definition S1' '(a0,a1,a) := S1 a0 (sum' (a++[a0+a1])) [] 0.

Inductive P: nat*nat*(list nat) -> Prop :=
| P_intro a0 a1 a:
  1<=a1 ->
  Forall (fun x => 1<=x) a ->
  sum (a++[a0+a1]) <= (length a)*2+5 ->
  a<>[] ->
  P (a0,a1,a)
.

Lemma BigStep_1' a0 a1 a:
  P (1+a0,a1,a) ->
  S1' (1+a0,a1,a) -->+
  S1' (a0,a1,(length a)*2+5-(sum a+a0+a1)::a).
Proof.
  intros HP.
  inverts HP.
  unfold S1'.
  epose proof (BigStep_1 a0 (sum' (a++[a0+a1]))) as I1.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Lemma BigStep_0' a0 a1 a:
  P (O,1+a0,a++[a1]) ->
  S1' (O,1+a0,(a++[a1])) -->+
  S1' (a0,a1,(length (a++[a1]))*2+5-(sum a+a0+a1)::a).
Proof.
  intros HP.
  inverts HP.
  unfold S1'.
  epose proof (BigStep_0 (a0) (sum' (a++[a0+a1]))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' (0,3,[3;1])%nat).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve [auto | lia | congruence].
  intros [[a0 a1] a] HP.
  epose proof HP as HP0.
  inverts HP0.
  destruct a0.
  - epose proof H5 as I1.
    eapply exists_last in I1.
    destruct I1 as [a' [a2 Ha]]; subst.
    destruct a1. 1: lia.
    eexists; split.
    1: apply BigStep_0',HP.
    rewrite Forall_app in H3.
    rewrite Forall_cons_iff in H3.
    econstructor.
    + lia.
    + eapply Forall_cons.
      2: tauto.
      rw_ls.
      lia.
    + rw_ls.
      lia.
    + congruence.
  - eexists; split.
    1: apply BigStep_1',HP.
    econstructor.
    + lia.
    + eapply Forall_cons.
      2: tauto.
      rw_ls.
      lia.
    + rw_ls.
      lia.
    + congruence.
Qed.

End TM33.


Module TM34.

Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC0LA_1RA0RD_1RE---_0LE0RB_0LB1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1;0;1] {{C}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;1;0;1] {{E}}> r) (at level 30).

Definition LS n :=
  <[0;1;1] <+ <[0;1;0;1]^^n.

Definition RS n :=
  [0;1;0;1]^^n ++ [0;1;0].

Definition LS' n :=
  <[0;1;0] <+ <[0;1;0;1]^^n.

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 a0 a b c :=
  0inf <* <[0;1;0;1]^^a0 <* LS'^^^a <* LS^^^b <| [0;1;0;1]^^(1+c) *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Lemma Inc1 a0 a1 a b c:
  S1 a0 (1+a1::a) b c -->*
  S1 a0 a (b++[a1]) (2+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_1 a0 b c:
  S1 (1+a0) [] b c -->+
  S1 a0 (3+c::b) [] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_0 a0 b c:
  S1 0 [] (b++[a0]) c -->+
  S1 a0 (3+c::b) [] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a0 a b c:
  S1 a0 (map (Nat.add 1) a) b c -->*
  S1 a0 [] (b++a) ((length a)*2+c).
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; cbn; es.
Qed.

Lemma BigStep_1 a0 a:
  S1 (1+a0) (map (Nat.add 1) a) [] 0 -->+
  S1 a0 (3+(length a)*2::a) [] 0.
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Lemma BigStep_0 a0 a:
  S1 0 (map (Nat.add 1) (a++[a0])) [] 0 -->+
  S1 a0 (3+(length (a++[a0]))*2::a) [] 0.
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Definition S1' '(a0,a1,a) := S1 a0 (sum' (a++[a0+a1])) [] 0.

Inductive P: nat*nat*(list nat) -> Prop :=
| P_intro a0 a1 a:
  1<=a1 ->
  Forall (fun x => 1<=x) a ->
  sum (a++[a0+a1]) <= (length a)*2+5 ->
  a<>[] ->
  P (a0,a1,a)
.

Lemma BigStep_1' a0 a1 a:
  P (1+a0,a1,a) ->
  S1' (1+a0,a1,a) -->+
  S1' (a0,a1,(length a)*2+5-(sum a+a0+a1)::a).
Proof.
  intros HP.
  inverts HP.
  unfold S1'.
  epose proof (BigStep_1 a0 (sum' (a++[a0+a1]))) as I1.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Lemma BigStep_0' a0 a1 a:
  P (O,1+a0,a++[a1]) ->
  S1' (O,1+a0,(a++[a1])) -->+
  S1' (a0,a1,(length (a++[a1]))*2+5-(sum a+a0+a1)::a).
Proof.
  intros HP.
  inverts HP.
  unfold S1'.
  epose proof (BigStep_0 (a0) (sum' (a++[a0+a1]))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' (0,2,[3])%nat).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve [auto | lia | congruence].
  intros [[a0 a1] a] HP.
  epose proof HP as HP0.
  inverts HP0.
  destruct a0.
  - epose proof H5 as I1.
    eapply exists_last in I1.
    destruct I1 as [a' [a2 Ha]]; subst.
    destruct a1. 1: lia.
    eexists; split.
    1: apply BigStep_0',HP.
    rewrite Forall_app in H3.
    rewrite Forall_cons_iff in H3.
    econstructor.
    + lia.
    + eapply Forall_cons.
      2: tauto.
      rw_ls.
      lia.
    + rw_ls.
      lia.
    + congruence.
  - eexists; split.
    1: apply BigStep_1',HP.
    econstructor.
    + lia.
    + eapply Forall_cons.
      2: tauto.
      rw_ls.
      lia.
    + rw_ls.
      lia.
    + congruence.
Qed.

End TM34.


Module TM35.

Definition tm := Eval compute in (TM_from_str "1RB1LA_1LA0RC_0LF1LD_0RE0RD_1LC0LE_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;1;0;0;0;0] {{E}}> r) (at level 30).
Notation "l |2> r" := (l <* <[1;1;1;1] {{B}}> r) (at level 30).

Definition LS n :=
  <[1;1;0]^^(n) <+ <[1;0].

Definition RS n :=
  [1;1;1]^^n ++ [1;0].

Definition LS' n :=
  <[1;1;0]^^(n) <+ <[1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 a b c :=
  0inf <* LS'^^^a <* LS^^^b <| [1;1;1]^^c *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Lemma Inc1 a1 a2 a b c:
  S1 (a1::a) (b++[1+a2]) c -->*
  S1 a (b++[a2;a1]) (2+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1 b c:
  S1 [] b (1+c) -->+
  S1 (b++[O]) [c] 2.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Inc1_0 b c:
  S1 [O] (b++[O]) c -->*
  S1 [] b (2+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a' a b b0 c:
  S1 ((map S a)++O::a') (b++[1+b0]) c -->*
  S1 a' (b++b0::a++[O]) ((length a)*2+2+c).
Proof.
  gen b c b0.
  induction a; intros.
  - follow Inc1.
    finish.
  - cbn.
    follow Inc1.
    specialize (IHa (b++[b0]) (2+c) a).
    rw_ls.
    follow IHa.
    finish.
Qed.

Definition S1' '(a,b0) := S1 a [1+b0] 2.

Lemma BigStep1 a b0:
  S1' ((map S a)++[O],b0) -->+
  S1' (b0::a++[O;O],(length a)*2+2).
Proof.
  unfold S1'.
  follow (Incs1 [] a [] b0 2).
  epose proof (Ov1 (b0::a++[O]) (1+((length a)*2+2))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Lemma BigStep2 a b0:
  S1' ((map S a)++[O;O],b0) -->+
  S1' (b0::a++[O],(length a)*2+4).
Proof.
  unfold S1'.
  follow (Incs1 [O] a [] b0 2).
  epose proof (Inc1_0 (b0::a) _) as I1.
  rw_ls.
  follow I1. clear I1.
  applys_eq Ov1; rw_ls; flia.
Qed.

Definition S' '(a,b0) := S1' (sum' a,b0).

Lemma BigStep1' a a0 b0:
  sum a + a0 <= b0 ->
  S' (a++[1+a0;O],b0) -->+
  S' (b0-(sum a + a0)::a++[a0;O;O],(length a)*2+4).
Proof.
  intros.
  unfold S'.
  epose proof (BigStep1 (sum' (a++[a0])) b0) as I1.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Lemma BigStep2' a a0 b0:
  sum a + a0 <= b0 ->
  S' (a++[1+a0;O;O],b0) -->+
  S' (b0-(sum a + a0)::a++[a0;O],(length a)*2+6).
Proof.
  intros.
  unfold S'.
  epose proof (BigStep2 (sum' (a++[a0])) b0) as I1.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Close Scope sym.

Inductive P: (list nat)*nat -> Prop :=
| P_1 a a0 b0:
    Forall (fun x => x=1\/x=5) a ->
    a0=0\/a0=2 ->
    sum a + a0 + 2 = b0 \/ sum a + a0 + 6 = b0 ->
    b0 = (length a)*2+4 \/ False ->
    P (a++[2+a0;O],b0)
| P_2 a a0 b0:
    Forall (fun x => x=1\/x=5) a ->
    a0=0\/a0=2\/a0=4 ->
    sum a + a0 + 1 = b0 \/ sum a + a0 + 5 = b0 ->
    b0 = (length a)*2+2 \/ b0 = (length a)*2+6 ->
    a<>[] ->
    P (a++[1+a0;O;O],b0)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ([1;3;0;0],8)%nat).
  1: unfold S',S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P_2 [_]); cbn; solve[ lia | congruence | auto].
  intros [a b0] HP.
  inverts HP.
  - eexists (_,_); split.
    1: apply BigStep1'; lia.
    apply (P_2 (b0-(sum a0+S a1)::a0) a1 ((length a0)*2+4)).
    + constructor.
      2: auto.
      lia.
    + lia.
    + cbn. lia.
    + cbn. lia.
    + congruence.
  - destruct a1.
    + eexists (_,_); split.
      1: apply BigStep2'; lia.
      assert ((b0-(sum a0+0)::a0)<>[]) as I1 by congruence.
      eapply exists_last in I1.
      destruct I1 as [a [a1 I1]].
      rewrite app_comm_cons.
      rewrite I1.
      destruct a1.
      1: {
        destruct a.
        - inverts I1. lia.
        - inverts I1.
          rewrite Forall_app,Forall_cons_iff in H1.
          lia.
      }
      rewrite <-app_assoc.
      apply P_2.
      * destruct a.
        1: auto.
        inverts I1.
        constructor.
        1: lia.
        rewrite Forall_app,Forall_cons_iff in H1.
        tauto.
      * destruct a.
        1: inverts I1; lia.
        inverts I1.
        rewrite Forall_app,Forall_cons_iff in H1.
        lia.
      * destruct a.
        1: inverts I1; lia.
        inverts I1.
        rw_ls.
        rewrite Forall_app,Forall_cons_iff in H1.
        lia.
      * eapply (f_equal (@length _)) in I1.
        rw_ls.
        lia.
      * intro.
        subst.
        inverts I1.
        congruence.
    + eexists (_,_); split.
      1: apply BigStep2'; lia.
      destruct a1.
      1: lia.
      apply (P_1 (b0-(sum a0+S (S a1))::a0) a1 _).
      * constructor.
        1: lia.
        auto.
      * lia.
      * cbn. lia.
      * cbn. lia.
Qed.

End TM35.


Module TM36.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LE_1RA0RB_0RC0RD_1LF---_0RF0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;0;0;0] {{B}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;0] {{D}}> r) (at level 30).

Definition LS n :=
  <[0;0;0;1;0;1]^^(1+n) <+ <[1].

Definition RS n :=
  [0;1;1;0;1;1]^^(1+n) ++ [1].

Definition LS' n :=
  <[1;0;0;0;1;0]^^(1+n) <+ <[0].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 (t:bool) a0 a b c :=
  0inf <* (if t then [1;1] else [1]) <* LS'^^^a <* <[1] <* <[0;0;0;1;0;1]^^a0 <* <[0;0;1;1] <* LS^^^b <| [0;1;1;0;1;1]^^(1+c) *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Lemma Inc1 t a0 a1 a b c:
  S1 t (a0) (1+a1::a) b c -->*
  S1 t a1 a (b++[a0]) (3+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1 t a0 b c:
  S1 t a0 [] b c -->+
  S1 (negb t) c (b++[a0]) [] 1.
Proof.
  destruct t;
  simpl';
  repeat follow'.
Qed.

Lemma Ov1x t a0 b c:
  S1 t a0 [O] b c -->+
  S1 t (1+c) (b++[1+a0]) [] 1.
Proof.
  destruct t;
  simpl';
  repeat follow'.
Qed.

Lemma Incs1 t a0 a1 a a' b c:
  S1 t a0 ((map S (a++[a1]))++a') b c -->*
  S1 t a1 a' (b++a0::a) ((length a)*3+3+c).
Proof.
  gen a0 b c.
  induction a; intros.
  - cbn.
    follow Inc1.
    finish.
  - cbn.
    follow Inc1.
    follow IHa.
    rw_ls.
    finish.
Qed.

Definition S1' '(t,a0,a) := S1 t a0 a [] 1.

Lemma BigStep1 t a0 a1 a:
  S1' (t,a0,map S (a++[a1])) -->+
  S1' (negb t,(length a)*3+4,a0::a++[a1]).
Proof.
  unfold S1'.
  epose proof (Incs1 t a0 a1 a [] [] 1) as I1.
  rw_ls.
  follow I1. clear I1.
  follow10 Ov1.
  finish.
Qed.

Lemma BigStep0 t a0 a1 a:
  S1' (t,a0,(map S (a++[a1]))++[O]) -->+
  S1' (t,(length a)*3+5,a0::a++[1+a1]).
Proof.
  unfold S1'.
  epose proof (Incs1 t a0 a1 a [O] [] 1) as I1.
  rw_ls.
  follow I1. clear I1.
  follow10 Ov1x.
  finish.
Qed.

Definition S' '(t,a0,a) := S1' (t,a0,sum' a).

Lemma BigStep1' t a0 a1 a:
  (sum a)+a1<=a0 ->
  S' (t,a0,a++[1+a1]) -->+
  S' (negb t,(length a)*3+4,a0-((sum a)+a1)::a++[a1]).
Proof.
  intros.
  unfold S'.
  epose proof (BigStep1 t a0 a1 (map (Nat.add (a1+0)) (sum' a))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Lemma BigStep0' t a0 a1 a2 a:
  (sum a)+a2+a1+1<=a0 ->
  S' (t,a0,a++[1+a2;1+a1;O]) -->+
  S' (t,(length a)*3+8,a0-((sum a)+a2+a1+1)::a++[a2;1+a1]).
Proof.
  intros.
  unfold S'.
  epose proof (BigStep0 t a0 a1 (map (Nat.add (a1)) (sum' (a++[1+a2])))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Inductive P: (bool*nat*(list nat))->Prop :=
| P_intro t a0 a1 a2 a:
  Forall (fun i => 2<=i) a ->
  a<>[] ->
  sum a + a2+a1+2<=a0 ->
  a0<=(length a)*3+5 ->
  (a1=O->a0<=(length a)*3+4) ->
  P (t,a0,a++[1+a2;a1])
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (true,7,[3;1;0])%nat).
  1: unfold S',S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: eapply P_intro with (a:=[_]); cbn; solve [lia | congruence | auto].
  intros [[t a0] a] HP.
  inverts HP.
  destruct a2.
  - apply exists_last in H3.
    destruct H3 as [a [a5 I1]]; subst.
    rewrite Forall_app,Forall_cons_iff in H2.
    destruct a5 as [|[|a5]]. 1,2: lia.
    rewrite <-app_assoc.
    eexists (_,_,_); split.
    1: apply (BigStep0').
    1: rw_ls; lia.
    rewrite app_comm_cons.
    econstructor.
    + constructor.
      2: tauto.
      rw_ls; lia.
    + congruence.
    + rw_ls; lia.
    + rw_ls; lia.
    + lia.
  - rewrite app_cons_r.
    eexists (_,_,_); split.
    1: apply BigStep1'.
    1: rw_ls; lia.
    rewrite <-app_assoc.
    rewrite app_comm_cons.
    econstructor.
    + constructor.
      2: tauto.
      rw_ls; lia.
    + congruence.
    + rw_ls; lia.
    + rw_ls; lia.
    + intro; subst.
      rw_ls; lia.
Qed.

End TM36.


Module TM37.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LE_1RA1LF_0RC0RD_0LA---_0RF0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;0;0;0] {{B}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;0] {{D}}> r) (at level 30).

Definition LS n :=
  <[0;0;0;1;0;1]^^(1+n) <+ <[1].

Definition RS n :=
  [0;1;1;0;1;1]^^(1+n) ++ [1].

Definition LS' n :=
  <[1;0;0;0;1;0]^^(1+n) <+ <[0].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 (t:bool) a0 a b c :=
  0inf <* (if t then [1;1] else [1]) <* LS'^^^a <* <[1] <* <[0;0;0;1;0;1]^^a0 <* <[0;0;1;1] <* LS^^^b <| [0;1;1;0;1;1]^^(1+c) *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Lemma Inc1 t a0 a1 a b c:
  S1 t (a0) (1+a1::a) b c -->*
  S1 t a1 a (b++[a0]) (3+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1 t a0 b c:
  S1 t a0 [] b c -->+
  S1 (negb t) c (b++[a0]) [] 1.
Proof.
  destruct t;
  simpl';
  repeat follow'.
Qed.

Lemma Ov1x t a0 b c:
  S1 t a0 [O] b c -->+
  S1 t (1+c) (b++[1+a0]) [] 1.
Proof.
  destruct t;
  simpl';
  repeat follow'.
Qed.

Lemma Incs1 t a0 a1 a a' b c:
  S1 t a0 ((map S (a++[a1]))++a') b c -->*
  S1 t a1 a' (b++a0::a) ((length a)*3+3+c).
Proof.
  gen a0 b c.
  induction a; intros.
  - cbn.
    follow Inc1.
    finish.
  - cbn.
    follow Inc1.
    follow IHa.
    rw_ls.
    finish.
Qed.

Definition S1' '(t,a0,a) := S1 t a0 a [] 1.

Lemma BigStep1 t a0 a1 a:
  S1' (t,a0,map S (a++[a1])) -->+
  S1' (negb t,(length a)*3+4,a0::a++[a1]).
Proof.
  unfold S1'.
  epose proof (Incs1 t a0 a1 a [] [] 1) as I1.
  rw_ls.
  follow I1. clear I1.
  follow10 Ov1.
  finish.
Qed.

Lemma BigStep0 t a0 a1 a:
  S1' (t,a0,(map S (a++[a1]))++[O]) -->+
  S1' (t,(length a)*3+5,a0::a++[1+a1]).
Proof.
  unfold S1'.
  epose proof (Incs1 t a0 a1 a [O] [] 1) as I1.
  rw_ls.
  follow I1. clear I1.
  follow10 Ov1x.
  finish.
Qed.

Definition S' '(t,a0,a) := S1' (t,a0,sum' a).

Lemma BigStep1' t a0 a1 a:
  (sum a)+a1<=a0 ->
  S' (t,a0,a++[1+a1]) -->+
  S' (negb t,(length a)*3+4,a0-((sum a)+a1)::a++[a1]).
Proof.
  intros.
  unfold S'.
  epose proof (BigStep1 t a0 a1 (map (Nat.add (a1+0)) (sum' a))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Lemma BigStep0' t a0 a1 a2 a:
  (sum a)+a2+a1+1<=a0 ->
  S' (t,a0,a++[1+a2;1+a1;O]) -->+
  S' (t,(length a)*3+8,a0-((sum a)+a2+a1+1)::a++[a2;1+a1]).
Proof.
  intros.
  unfold S'.
  epose proof (BigStep0 t a0 a1 (map (Nat.add (a1)) (sum' (a++[1+a2])))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Inductive P: (bool*nat*(list nat))->Prop :=
| P_intro t a0 a1 a2 a:
  Forall (fun i => 2<=i) a ->
  a<>[] ->
  sum a + a2+a1+2<=a0 ->
  a0<=(length a)*3+5 ->
  (a1=O->a0<=(length a)*3+4) ->
  P (t,a0,a++[1+a2;a1])
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (true,7,[3;1;0])%nat).
  1: unfold S',S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: eapply P_intro with (a:=[_]); cbn; solve [lia | congruence | auto].
  intros [[t a0] a] HP.
  inverts HP.
  destruct a2.
  - apply exists_last in H3.
    destruct H3 as [a [a5 I1]]; subst.
    rewrite Forall_app,Forall_cons_iff in H2.
    destruct a5 as [|[|a5]]. 1,2: lia.
    rewrite <-app_assoc.
    eexists (_,_,_); split.
    1: apply (BigStep0').
    1: rw_ls; lia.
    rewrite app_comm_cons.
    econstructor.
    + constructor.
      2: tauto.
      rw_ls; lia.
    + congruence.
    + rw_ls; lia.
    + rw_ls; lia.
    + lia.
  - rewrite app_cons_r.
    eexists (_,_,_); split.
    1: apply BigStep1'.
    1: rw_ls; lia.
    rewrite <-app_assoc.
    rewrite app_comm_cons.
    econstructor.
    + constructor.
      2: tauto.
      rw_ls; lia.
    + congruence.
    + rw_ls; lia.
    + rw_ls; lia.
    + intro; subst.
      rw_ls; lia.
Qed.

End TM37.


Module TM38.

Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC0LD_1LA0RE_---1LE_0LF0RE_1RA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;0;1;1] {{B}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;0;0;0;0;0] {{E}}> r) (at level 30).

Definition LS n :=
  <[0;0;0;1;1;1]^^(1+n) <+ <[0;1;1;1].

Definition RS n :=
  [1;0;1;1;1;0]^^(1+n) ++ [1;0;0;0].

Definition LS' n :=
  <[0;0;0;0;0;0] <+ <[0;0;0;1;1;1]^^n <+ <[0;1;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 (t:bool) a b c :=
  0inf <* (if t then <[1;0;0;0;0;1;1;1;0;1;1;1] else <[1;1;0;0;1;1;1]) <* LS'^^^a <* LS^^^b <| [1;0;1;1;1;0]^^(c) *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Lemma Inc1 t a1 a b c:
  S1 t (1+a1::a) b c -->*
  S1 t a (b++[a1]) (2+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_0 b c:
  S1 false [] (b++[O]) (1+c) -->+
  S1 true (c::b) [] 1.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_1 b c:
  S1 true [] b c -->+
  S1 false (c::b) [] 1.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 t a b c:
  S1 t (map S a) b c -->*
  S1 t [] (b++a) ((length a)*2+c).
Proof.
  gen b c.
  induction a; intros.
  1: rewrite app_nil_r; finish.
  cbn.
  follow Inc1.
  follow IHa.
  rw_ls.
  finish.
Qed.

Lemma BigStep0 a:
  S1 false (map S (a++[O])) [] 1 -->+
  S1 true ((length a)*2+2::a) [] 1.
Proof.
  follow Incs1.
  cbn.
  epose proof (Ov1_0 a (length (a++[O])*2)) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Lemma BigStep1 a:
  S1 true (map S a) [] 1 -->+
  S1 false ((length a)*2+1::a) [] 1.
Proof.
  follow Incs1.
  cbn.
  epose proof (Ov1_1 _ _) as I1.
  applys_eq I1; flia.
Qed.

Definition S' n := S1 true (sum' ([2]^^(n+1))) [] 1.

Lemma BigStep n:
  S' n -->+
  S' (S n).
Proof.
  unfold S'.
  rewrite lpow_add.
  epose proof (BigStep1 (sum' ([2]^^n++[1]%nat))) as I1.
  rw_ls.
  follow10 I1. clear I1.
  epose proof (BigStep0 (n*2+2::sum' ([2]^^n))) as I1.
  rw_ls.
  apply progress_evstep.
  applys_eq I1.
  1: flia.
  rewrite (Nat.add_comm n 1).
  cbn.
  rewrite sum_lpow.
  cbn.
  flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: unfold S',S1; esx.
  eapply progress_nonhalt_simple.
  intro n; eexists; apply BigStep.
Qed.

End TM38.


Module TM39.

Definition tm := Eval compute in (TM_from_str "1LB1RF_0RC0LC_0LD1RB_1LE---_1LA0RA_0RE0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [0] {{E}}> r) (at level 30).

Definition LS n :=
  <[0;0] <+ <[0;1]^^(1+n) <+ <[0;0;1].

Definition RS n :=
  [1;1]^^(2+n) ++ [1;0;0].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Definition S1 a b c :=
  0inf <* LS^^^a <* <[0;1;0;0;1] <* LS^^^b <| [1;1]^^(1+c) *> 0inf.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[2+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a' a b c:
  S1 (a++a') b (length a + c) -->*
  S1 a' (b++(map (Nat.add 2) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Lemma Inc2 b c:
  S1 [] b (1+c) -->*
  S1 [] (b++[O]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov2 b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[O;O]) [] (1+b0).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov2' a1 b0 b:
  S1 [a1] (b0::b) 0 -->+
  S1 (b++[2+a1;O]) [] (1+b0).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 b c:
  S1 [] b c -->*
  S1 [] (b++[O]^^c) 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma BigStep1 a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 2) a ++ [O]^^(b+2)) [] (a0+3).
Proof.
  epose proof (Incs1 [] (a0::a) _ _) as I1.
  rewrite app_nil_r in I1.
  follow I1. clear I1.
  follow Incs2.
  cbn.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep0 a0 a1 a:
  S1 ((a0::a)++[a1]) [] (length (a0::a)) -->+
  S1 (map (Nat.add 2) a ++ [2+a1;O]) [] (a0+3).
Proof. 
  epose proof (Incs1 [a1] (a0::a) [] 0) as I1.
  follow I1.
  cbn.
  follow10 Ov2'.
  finish.
Qed.

Lemma BigStep a0 a b:
  S1 ((a0::a)++[O]) [] (length (a0::a)+b) -->+
  S1 (map (Nat.add 2) (a++[O]) ++ [O]^^b++[O]) [] (a0+3).
Proof. 
  destruct b.
  - epose proof (BigStep0 a0 0 a) as I1.
    rw_ls.
    applys_eq I1; flia.
  - epose proof (BigStep1 a0 (a++[O]) b) as I1.
    replace (b+2) with (1+b+1) in I1 by lia.
    rewrite lpow_add in I1.
    rw_ls.
    applys_eq I1; flia.
Qed.

Definition S1' '(a,b) := S1 (sum' a++[O]) [] (length a+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+3 >= (length a) + b->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [2] ++ [0]^^b, (sum a)+3-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2],2)).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto; congruence.
Qed.

End TM39.


Module TM40.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0RC_1LD1RF_0RE0LE_0LA1RD_0RB0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [0] {{B}}> r) (at level 30).

Definition LS n :=
  <[0;0] <+ <[0;1]^^(1+n) <+ <[0;0;1].

Definition RS n :=
  [1;1]^^(2+n) ++ [1;0;0].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Definition S1 a b c :=
  0inf <* LS^^^a <* <[0;1;0;0;1] <* LS^^^b <| [1;1]^^(1+c) *> 0inf.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[2+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a' a b c:
  S1 (a++a') b (length a + c) -->*
  S1 a' (b++(map (Nat.add 2) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Lemma Inc2 b c:
  S1 [] b (1+c) -->*
  S1 [] (b++[O]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov2 b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[O;O]) [] (1+b0).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov2' a1 b0 b:
  S1 [a1] (b0::b) 0 -->+
  S1 (b++[2+a1;O]) [] (1+b0).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 b c:
  S1 [] b c -->*
  S1 [] (b++[O]^^c) 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma BigStep1 a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map (Nat.add 2) a ++ [O]^^(b+2)) [] (a0+3).
Proof.
  epose proof (Incs1 [] (a0::a) _ _) as I1.
  rewrite app_nil_r in I1.
  follow I1. clear I1.
  follow Incs2.
  cbn.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep0 a0 a1 a:
  S1 ((a0::a)++[a1]) [] (length (a0::a)) -->+
  S1 (map (Nat.add 2) a ++ [2+a1;O]) [] (a0+3).
Proof. 
  epose proof (Incs1 [a1] (a0::a) [] 0) as I1.
  follow I1.
  cbn.
  follow10 Ov2'.
  finish.
Qed.

Lemma BigStep a0 a b:
  S1 ((a0::a)++[O]) [] (length (a0::a)+b) -->+
  S1 (map (Nat.add 2) (a++[O]) ++ [O]^^b++[O]) [] (a0+3).
Proof. 
  destruct b.
  - epose proof (BigStep0 a0 0 a) as I1.
    rw_ls.
    applys_eq I1; flia.
  - epose proof (BigStep1 a0 (a++[O]) b) as I1.
    replace (b+2) with (1+b+1) in I1 by lia.
    rewrite lpow_add in I1.
    rw_ls.
    applys_eq I1; flia.
Qed.

Definition S1' '(a,b) := S1 (sum' a++[O]) [] (length a+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+3 >= (length a) + b->
  Forall (fun x => x<=2) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [2] ++ [0]^^b, (sum a)+3-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (sum' a) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([2;0;0],0)%nat).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 6; congruence.
Qed.

End TM40.


Module TM41.

Definition tm := Eval compute in (TM_from_str "1RB1LE_0LC0RA_0LE0RD_0RB---_0LF1LC_1LA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;0] {{A}}> r) (at level 30).
Notation "l <2| r" := (l <{{F}} [0;0] *> r) (at level 30).
Notation "l |2> r" := (l <* <[0;0;0] {{B}}> r) (at level 30).

Definition LS n :=
  <[0] <+ <[0;1]^^(1+n).

Definition RS n :=
  [0;1]^^n++[0;1;1].

Definition RS' n :=
  [1;0]^^n++[1;0;0].

Definition LS' n :=
  <[0;0;0] <+ <[0;1]^^(n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma LS_L' l r s:
  l <* LS^^^s <2| r -->*
  l <2| RS'^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS'.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS'^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS'.
  es.
Qed.

Definition S1 a b c :=
  0inf <* LS'^^^a <* <[0;0] <* LS^^^b <| [0;1]^^c *> 0inf.

Ltac follow' :=
  unfold LS,RS,LS',RS';
  es; er; (follow LS_L || follow RS_R || follow LS_L' || follow RS_R').

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Close Scope sym.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[1+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a' a b c:
  S1 (a++a') b (length a + c) -->*
  S1 a' (b++(map S a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.


Lemma Inc2 b c:
  S1 [] b (1+c) -->*
  S1 [] (b++[1]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov2 b0 b:
  S1 [] (b0::b) 0 -->+
  S1 (b++[1;1]) [] b0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov2' a1 b0 b:
  S1 [a1] (b0::b) 0 -->+
  S1 (b++[1+a1;1]) [] b0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 b c:
  S1 [] b c -->*
  S1 [] (b++[1]^^c) 0.
Proof.
  gen b.
  induction c; intros.
  1: simpl'; finish.
  follow Inc2.
  follow IHc.
  simpl'; finish.
Qed.

Lemma BigStep1 a0 a b:
  S1 (a0::a) [] (length (a0::a) + b) -->+
  S1 (map S a ++ [1]^^(b+2)) [] (a0+1).
Proof.
  epose proof (Incs1 [] (a0::a) _ _) as I1.
  rewrite app_nil_r in I1.
  follow I1. clear I1.
  follow Incs2.
  cbn.
  follow10 Ov2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep0 a0 a1 a:
  S1 ((a0::a)++[a1]) [] (length (a0::a)) -->+
  S1 (map S a ++ [1+a1;1]) [] (a0+1).
Proof. 
  epose proof (Incs1 [a1] (a0::a) [] 0) as I1.
  follow I1.
  cbn.
  follow10 Ov2'.
  finish.
Qed.

Lemma BigStep a0 a b:
  S1 ((a0::a)++[1]) [] (length (a0::a)+b) -->+
  S1 (map S (a++[1]) ++ [1]^^b++[1]) [] (a0+1).
Proof. 
  destruct b.
  - epose proof (BigStep0 a0 1 a) as I1.
    rw_ls.
    applys_eq I1; flia.
  - epose proof (BigStep1 a0 (a++[1]) b) as I1.
    replace (b+2) with (1+b+1) in I1 by lia.
    rewrite lpow_add in I1.
    rw_ls.
    applys_eq I1; flia.
Qed.

Definition S1' '(a,b) := S1 (sum' (a++[1])) [] (length a+b).

Inductive P: (list nat)*nat -> Prop :=
| P_intro a b:
  a<>[] ->
  (sum a)+2 >= (length a) + b->
  Forall (fun x => x<=1) a ->
  P (a,b)
.

Lemma BigStep' a b:
  P (a,b) ->
  let x := (tl a ++ [1] ++ [0]^^b, (sum a)+2-((length a)+b))%nat in
  S1' (a,b) -->+
  S1' x /\ P x.
Proof.
  intros HP.
  inverts HP.
  destruct a as [|a0 a].
  1: congruence.
  split.
  2:{
    cbn in *.
    econstructor.
    - destruct a; cbn; congruence.
    - rw_ls.
      inverts H3.
      lia.
    - rewrite Forall_app.
      split.
      + inverts H3; auto.
      + constructor.
        1: lia.
        apply Forall_lpow; auto.
  }
  unfold S1'.
  cbn.
  epose proof (BigStep _ (map S (sum' a)) b).
  rw_ls.
  follow10 H.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' ([0],1)).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  - intros [a b] HP.
    eexists.
    apply BigStep',HP.
  - constructor; cbn; auto 6; congruence.
Qed.

End TM41.


Module TM42.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC0LA_0RD1RB_0LE0RB_1LB---_1LC1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{C}}> r) (at level 30).

Definition LS n :=
  <[0;0;1] <+ <[1;1]^^(2+n).

Definition RS n :=
  [0;1] ++ [0;1]^^(2+n) ++ [0].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Definition S1 a b c :=
  0inf <* [1] <* LS^^^a <* <[0;1;1;1;1;1;1] <* LS^^^b <| [0;1]^^(1+c) *> 0inf.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Close Scope sym.

Lemma Inc1 a0 a b c:
  S1 (a0::a) b (1+c) -->*
  S1 a (b++[2+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov2 b0 b:
  S1 [] (b0::b) 1 -->+
  S1 (b++[1;0]) [] (1+b0).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a b c:
  S1 a b (length a + c) -->*
  S1 [] (b++(map (Nat.add 2) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Definition S' n := S1 (sum' ([1]^^(n+1)++[0])) [] (n+3).

Lemma BigStep n:
  S' n -->+ S' (n+1).
Proof.
  unfold S'.
  epose proof (Incs1 (sum' ([1]^^(n+1)++[0])) [] 1) as I1.
  rw_ls.
  follow I1.
  replace (n+1+1) with (n+2) by lia.
  replace (n+1) with (S(n)) by lia.
  cbn.
  follow10 Ov2.
  repeat rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: unfold S',S1; esx.
  eapply progress_nonhalt_simple.
  intro n; eexists; apply BigStep.
Qed.

End TM42.


Module TM43.

Definition tm := Eval compute in (TM_from_str "1LB1RB_1RA1RC_1RE1LD_0LE0LC_0LA0RF_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[] {{F}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0] {{F}}> r) (at level 30).

Definition LS n :=
  <[0;1] <+ <[1;1]^^(3+n*2) <+ <[0].

Definition RS n :=
  [0;1]^^(2+n*2) ++ [0;1;1;0;1].

Definition LS' n :=
  <[0;0;1] <+ <[1;1]^^(3+n*2).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.


Definition S1 a b c :=
  0inf <* LS'^^^a <* LS^^^b <| [0;1]^^c *> 0inf.

Ltac follow' :=
  unfold LS,RS,LS';
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) (b++[a1]) (2+c) -->*
  S1 a (b++[1+a1;1+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a' a a0 a1 b c:
  S1 ((a++[a0])++a') (b++[a1]) ((length a)*2+2+c) -->*
  S1 a' (b++(1+a1)::(map (Nat.add 2) a)++[1+a0]) c.
Proof.
  gen a1 b c.
  induction a; intros.
  - cbn.
    follow Inc1.
    finish.
  - cbn.
    follow Inc1.
    rewrite (app_cons_r b).
    follow IHa.
    simpl'; finish.
Qed.

Lemma Inc2 b c:
  S1 [] b (1+c) -->*
  S1 [] (b++[O]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 b c:
  S1 [] b c -->*
  S1 [] (b++[O]^^c) 0.
Proof.
  gen b.
  induction c; intros.
  1: rewrite app_nil_r; finish.
  follow Inc2.
  follow IHc.
  rw_ls.
  finish.
Qed.

Lemma Ov2 b0 b1 b:
  S1 [] (b0::b1::b) 0 -->+
  S1 (b++[O]) [1+b1] (b0*2+7).
Proof.
  simpl'.
  follow'.
  es; er.
  follow RS_R'.
  es.
Qed.

Lemma Ov2' a1 a2 b0 b1 b:
  S1 [a1] (b0::b1::b++[a2]) 1 -->+
  S1 (b++[1+a2;1+a1]) [1+b1] (b0*2+7).
Proof.
  simpl'.
  do 3 follow'.
  es; er.
  follow RS_R'.
  es.
Qed.

Close Scope sym.

Lemma BigStep0 b0 b1 b k:
  b0*2+7=(length b)*2+5+k ->
  S1 [0] (b0::b1::b++[1]) 1 -->+
  S1 [] ((map (Nat.add 2) (b1::b++[2;0]))++[0]^^k++[0]) 0.
Proof.
  intros.
  follow10 Ov2'.
  epose proof (Incs1 [] (b++[2]) (1) (1+b1) [] (k+1)) as I1.
  rw_ls.
  follow I1. clear I1.
  follow Incs2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep1 b0 b1 b:
  b0*2+7=(length b)*2+3 ->
  S1 [] (b0::b1::(b++[0])) 0 -->+
  S1 [0] ((map (Nat.add 2) (b1::b))++[1]) 1.
Proof.
  intros.
  follow10 Ov2.
  epose proof (Incs1 [O] b 0 (1+b1) [] 1) as I1.
  rw_ls.
  follow I1. clear I1.
  finish.
Qed.

Definition S1' b := S1 [] (b++[0]) 0.

Lemma BigStep b0 b1 b k:
  b0+2=(length b) ->
  b1+4=(length b)+k ->
  S1' (b0::b1::b) -->+
  S1' ((map (Nat.add 4) (b))++[4;2]++[0]^^(k*2)).
Proof.
  intros.
  destruct b as [|b2 b].
  1: rw_ls; lia.
  unfold S1'.
  unshelve epose proof (BigStep1 b0 b1 (b2::b) _) as I1.
  1: lia.
  follow10 I1. clear I1.
  cbn.
  unshelve epose proof (BigStep0 (2+b1) (2+b2) (map (Nat.add 2) b) (k*2) _) as I1.
  1: rw_ls; lia.
  follow100 I1.
  rw_ls.
  finish.
Qed.

Definition S' b := S1' (sum' b).

Lemma BigStep' b0 b k:
  b0*2+sum b+2 = length b ->
  b0+sum b+4 = length b+k ->
  S' (b0::b0::b) -->+
  S' (b++[2;2]++[0]^^(k*2)).
Proof.
  intros.
  unfold S'.
  unshelve epose proof (BigStep (b0+(b0+sum b)) (b0+sum b) (sum' b) k _ _) as I1.
  1,2: rw_ls; lia.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Definition lmul2(x:list nat):= flat_map (fun a => [a;a]) x.

Lemma sum_lmul2 x:
  sum (lmul2 x) = sum x*2.
Proof.
  unfold lmul2.
  induction x; cbn; lia.
Qed.

Lemma length_lmul2 x:
  length (lmul2 x) = length x*2.
Proof.
  unfold lmul2.
  induction x; cbn; lia.
Qed.

Lemma lmul2_all0 n:
  lmul2 ([0]^^n) = [0]^^(n*2).
Proof.
  unfold lmul2.
  induction n; cbn; congruence.
Qed.

Definition S0' b := S' (lmul2 b).

Lemma BigStep'' b0 b k:
  b0+sum b+1 = length b ->
  sum b+3 = length b+k ->
  S0' (b0::b) -->+
  S0' (b++[2]++[0]^^k).
Proof.
  intros.
  unfold S0',lmul2.
  repeat rewrite flat_map_app.
  rewrite lmul2_all0.
  rw_ls.
  apply BigStep'.
  - rewrite sum_lmul2,length_lmul2; lia.
  - rewrite sum_lmul2,length_lmul2; lia.
Qed.

Inductive P: (list nat)->Prop :=
| P_intro b0 b:
  b0+sum b+1 = length b ->
  sum b+3 >= length b ->
  Forall (fun x => x<=2) b ->
  P (b0::b).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0' [1;0;0]).
  1: unfold S0',S',S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve[lia|auto].
  intros b' HP.
  inverts HP.
  eexists; split.
  1: apply BigStep'' with (k:=sum b+3-length b); lia.
  destruct b as [|b1 b].
  1: rw_ls; lia.
  cbn.
  econstructor; rw_ls.
  - lia.
  - inverts H1.
    lia.
  - inverts H1.
    rewrite Forall_app,Forall_cons_iff; repeat split.
    + tauto.
    + lia.
    + induction (b1+sum b+3-S(length b)); cbn; auto.
Qed.

End TM43.


Module TM44.

Definition tm := Eval compute in (TM_from_str "1RB0RC_0RC1RA_1LC1LD_0RE0LF_---0RD_1LA1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;0;1;1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{D}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;0] {{D}}> r) (at level 30).

Definition LS n :=
  <[0;1] <+ <[1;1;1]^^(2+n*2) <+ <[0].

Definition RS n :=
  [0;1;1]^^(2+n*2) ++ [1;1;1].

Definition LS' n :=
  <[0;0;1] <+ <[1;1;1]^^(2+n*2).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.


Definition S1 a b c :=
  0inf <* LS'^^^a <* LS^^^b <| [0;1;1]^^c *> [1] *> 0inf.

Ltac follow' :=
  unfold LS,RS,LS';
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) (b++[a1]) (2+c) -->*
  S1 a (b++[1+a1;1+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a' a a0 a1 b c:
  S1 ((a++[a0])++a') (b++[a1]) ((length a)*2+2+c) -->*
  S1 a' (b++(1+a1)::(map (Nat.add 2) a)++[1+a0]) c.
Proof.
  gen a1 b c.
  induction a; intros.
  - cbn.
    follow Inc1.
    finish.
  - cbn.
    follow Inc1.
    rewrite (app_cons_r b).
    follow IHa.
    simpl'; finish.
Qed.

Lemma Inc2 b c:
  S1 [] b (1+c) -->*
  S1 [] (b++[O]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 b c:
  S1 [] b c -->*
  S1 [] (b++[O]^^c) 0.
Proof.
  gen b.
  induction c; intros.
  1: rewrite app_nil_r; finish.
  follow Inc2.
  follow IHc.
  rw_ls.
  finish.
Qed.

Lemma Ov2 b0 b1 b:
  S1 [] (b0::b1::b) 0 -->+
  S1 (b++[O]) [1+b1] (b0*2+3).
Proof.
  simpl'.
  follow'.
  es; er.
  follow RS_R'.
  es.
Qed.

Lemma Ov2' a1 a2 b0 b1 b:
  S1 [a1] (b0::b1::b++[a2]) 1 -->+
  S1 (b++[1+a2;1+a1]) [1+b1] (b0*2+3).
Proof.
  simpl'.
  do 3 follow'.
  es; er.
  follow RS_R'.
  es.
Qed.

Close Scope sym.

Lemma BigStep0 b0 b1 b k:
  b0*2+3=(length b)*2+5+k ->
  S1 [0] (b0::b1::b++[1]) 1 -->+
  S1 [] ((map (Nat.add 2) (b1::b++[2;0]))++[0]^^k++[0]) 0.
Proof.
  intros.
  follow10 Ov2'.
  epose proof (Incs1 [] (b++[2]) (1) (1+b1) [] (k+1)) as I1.
  rw_ls.
  follow I1. clear I1.
  follow Incs2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep1 b0 b1 b:
  b0*2+3=(length b)*2+3 ->
  S1 [] (b0::b1::(b++[0])) 0 -->+
  S1 [0] ((map (Nat.add 2) (b1::b))++[1]) 1.
Proof.
  intros.
  follow10 Ov2.
  epose proof (Incs1 [O] b 0 (1+b1) [] 1) as I1.
  rw_ls.
  follow I1. clear I1.
  finish.
Qed.

Definition S1' b := S1 [] (b++[0]) 0.

Lemma BigStep b0 b1 b k:
  length b>=1 ->
  b0+0=(length b) ->
  b1+2=(length b)+k ->
  S1' (b0::b1::b) -->+
  S1' ((map (Nat.add 4) (b))++[4;2]++[0]^^(k*2)).
Proof.
  intros.
  destruct b as [|b2 b].
  1: rw_ls; lia.
  unfold S1'.
  unshelve epose proof (BigStep1 b0 b1 (b2::b) _) as I1.
  1: lia.
  follow10 I1. clear I1.
  cbn.
  unshelve epose proof (BigStep0 (2+b1) (2+b2) (map (Nat.add 2) b) (k*2) _) as I1.
  1: rw_ls; lia.
  follow100 I1.
  rw_ls.
  finish.
Qed.

Definition S' b := S1' (sum' b).

Lemma BigStep' b0 b k:
  length b >= 1 ->
  b0*2+sum b = length b ->
  b0+sum b+2 = length b+k ->
  S' (b0::b0::b) -->+
  S' (b++[2;2]++[0]^^(k*2)).
Proof.
  intros.
  unfold S'.
  unshelve epose proof (BigStep (b0+(b0+sum b)) (b0+sum b) (sum' b) k _ _ _) as I1.
  1,2,3: rw_ls; lia.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Definition lmul2(x:list nat):= flat_map (fun a => [a;a]) x.

Lemma sum_lmul2 x:
  sum (lmul2 x) = sum x*2.
Proof.
  unfold lmul2.
  induction x; cbn; lia.
Qed.

Lemma length_lmul2 x:
  length (lmul2 x) = length x*2.
Proof.
  unfold lmul2.
  induction x; cbn; lia.
Qed.

Lemma lmul2_all0 n:
  lmul2 ([0]^^n) = [0]^^(n*2).
Proof.
  unfold lmul2.
  induction n; cbn; congruence.
Qed.

Definition S0' b := S' (lmul2 b).

Lemma BigStep'' b0 b k:
  length b >= 1 ->
  b0+sum b = length b ->
  sum b+2 = length b+k ->
  S0' (b0::b) -->+
  S0' (b++[2]++[0]^^k).
Proof.
  intros.
  unfold S0',lmul2.
  repeat rewrite flat_map_app.
  rewrite lmul2_all0.
  rw_ls.
  apply BigStep'.
  - rewrite length_lmul2; lia.
  - rewrite sum_lmul2,length_lmul2; lia.
  - rewrite sum_lmul2,length_lmul2; lia.
Qed.

Inductive P: (list nat)->Prop :=
| P_intro b0 b:
  length b >= 1 ->
  b0+sum b = length b ->
  sum b+2 >= length b ->
  Forall (fun x => x<=2) b ->
  P (b0::b).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0' [2;0;0]).
  1: unfold S0',S',S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve[lia|auto].
  intros b' HP.
  inverts HP.
  eexists; split.
  1: apply BigStep'' with (k:=sum b+2-length b); lia.
  destruct b as [|b1 b].
  1: rw_ls; lia.
  cbn.
  econstructor; rw_ls.
  - lia.
  - lia.
  - inverts H2.
    lia.
  - inverts H2.
    rewrite Forall_app,Forall_cons_iff; repeat split.
    + tauto.
    + lia.
    + induction (b1+sum b+2-S(length b)); cbn; auto.
Qed.

End TM44.


Module TM45.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1LB1RA_1LC1LD_0RE0LF_---0RD_1LA1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;0;1;1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0] {{D}}> r) (at level 30).
Notation "l |2> r" := (l <* <[0;0] {{D}}> r) (at level 30).

Definition LS n :=
  <[0;1] <+ <[1;1;1]^^(2+n*2) <+ <[0].

Definition RS n :=
  [0;1;1]^^(2+n*2) ++ [1;1;1].

Definition LS' n :=
  <[0;0;1] <+ <[1;1;1]^^(2+n*2).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.


Definition S1 a b c :=
  0inf <* LS'^^^a <* LS^^^b <| [0;1;1]^^c *> [1] *> 0inf.

Ltac follow' :=
  unfold LS,RS,LS';
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 a0 a1 a b c:
  S1 (a0::a) (b++[a1]) (2+c) -->*
  S1 a (b++[1+a1;1+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a' a a0 a1 b c:
  S1 ((a++[a0])++a') (b++[a1]) ((length a)*2+2+c) -->*
  S1 a' (b++(1+a1)::(map (Nat.add 2) a)++[1+a0]) c.
Proof.
  gen a1 b c.
  induction a; intros.
  - cbn.
    follow Inc1.
    finish.
  - cbn.
    follow Inc1.
    rewrite (app_cons_r b).
    follow IHa.
    simpl'; finish.
Qed.

Lemma Inc2 b c:
  S1 [] b (1+c) -->*
  S1 [] (b++[O]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 b c:
  S1 [] b c -->*
  S1 [] (b++[O]^^c) 0.
Proof.
  gen b.
  induction c; intros.
  1: rewrite app_nil_r; finish.
  follow Inc2.
  follow IHc.
  rw_ls.
  finish.
Qed.

Lemma Ov2 b0 b1 b:
  S1 [] (b0::b1::b) 0 -->+
  S1 (b++[O]) [1+b1] (b0*2+3).
Proof.
  simpl'.
  follow'.
  es; er.
  follow RS_R'.
  es.
Qed.

Lemma Ov2' a1 a2 b0 b1 b:
  S1 [a1] (b0::b1::b++[a2]) 1 -->+
  S1 (b++[1+a2;1+a1]) [1+b1] (b0*2+3).
Proof.
  simpl'.
  do 3 follow'.
  es; er.
  follow RS_R'.
  es.
Qed.

Close Scope sym.

Lemma BigStep0 b0 b1 b k:
  b0*2+3=(length b)*2+5+k ->
  S1 [0] (b0::b1::b++[1]) 1 -->+
  S1 [] ((map (Nat.add 2) (b1::b++[2;0]))++[0]^^k++[0]) 0.
Proof.
  intros.
  follow10 Ov2'.
  epose proof (Incs1 [] (b++[2]) (1) (1+b1) [] (k+1)) as I1.
  rw_ls.
  follow I1. clear I1.
  follow Incs2.
  rewrite lpow_add.
  rw_ls.
  finish.
Qed.

Lemma BigStep1 b0 b1 b:
  b0*2+3=(length b)*2+3 ->
  S1 [] (b0::b1::(b++[0])) 0 -->+
  S1 [0] ((map (Nat.add 2) (b1::b))++[1]) 1.
Proof.
  intros.
  follow10 Ov2.
  epose proof (Incs1 [O] b 0 (1+b1) [] 1) as I1.
  rw_ls.
  follow I1. clear I1.
  finish.
Qed.

Definition S1' b := S1 [] (b++[0]) 0.

Lemma BigStep b0 b1 b k:
  length b>=1 ->
  b0+0=(length b) ->
  b1+2=(length b)+k ->
  S1' (b0::b1::b) -->+
  S1' ((map (Nat.add 4) (b))++[4;2]++[0]^^(k*2)).
Proof.
  intros.
  destruct b as [|b2 b].
  1: rw_ls; lia.
  unfold S1'.
  unshelve epose proof (BigStep1 b0 b1 (b2::b) _) as I1.
  1: lia.
  follow10 I1. clear I1.
  cbn.
  unshelve epose proof (BigStep0 (2+b1) (2+b2) (map (Nat.add 2) b) (k*2) _) as I1.
  1: rw_ls; lia.
  follow100 I1.
  rw_ls.
  finish.
Qed.

Definition S' b := S1' (sum' b).

Lemma BigStep' b0 b k:
  length b >= 1 ->
  b0*2+sum b = length b ->
  b0+sum b+2 = length b+k ->
  S' (b0::b0::b) -->+
  S' (b++[2;2]++[0]^^(k*2)).
Proof.
  intros.
  unfold S'.
  unshelve epose proof (BigStep (b0+(b0+sum b)) (b0+sum b) (sum' b) k _ _ _) as I1.
  1,2,3: rw_ls; lia.
  rw_ls.
  follow10 I1.
  finish.
Qed.

Definition lmul2(x:list nat):= flat_map (fun a => [a;a]) x.

Lemma sum_lmul2 x:
  sum (lmul2 x) = sum x*2.
Proof.
  unfold lmul2.
  induction x; cbn; lia.
Qed.

Lemma length_lmul2 x:
  length (lmul2 x) = length x*2.
Proof.
  unfold lmul2.
  induction x; cbn; lia.
Qed.

Lemma lmul2_all0 n:
  lmul2 ([0]^^n) = [0]^^(n*2).
Proof.
  unfold lmul2.
  induction n; cbn; congruence.
Qed.

Definition S0' b := S' (lmul2 b).

Lemma BigStep'' b0 b k:
  length b >= 1 ->
  b0+sum b = length b ->
  sum b+2 = length b+k ->
  S0' (b0::b) -->+
  S0' (b++[2]++[0]^^k).
Proof.
  intros.
  unfold S0',lmul2.
  repeat rewrite flat_map_app.
  rewrite lmul2_all0.
  rw_ls.
  apply BigStep'.
  - rewrite length_lmul2; lia.
  - rewrite sum_lmul2,length_lmul2; lia.
  - rewrite sum_lmul2,length_lmul2; lia.
Qed.

Inductive P: (list nat)->Prop :=
| P_intro b0 b:
  length b >= 1 ->
  b0+sum b = length b ->
  sum b+2 >= length b ->
  Forall (fun x => x<=2) b ->
  P (b0::b).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0' [2;0;0]).
  1: unfold S0',S',S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve[lia|auto].
  intros b' HP.
  inverts HP.
  eexists; split.
  1: apply BigStep'' with (k:=sum b+2-length b); lia.
  destruct b as [|b1 b].
  1: rw_ls; lia.
  cbn.
  econstructor; rw_ls.
  - lia.
  - lia.
  - inverts H2.
    lia.
  - inverts H2.
    rewrite Forall_app,Forall_cons_iff; repeat split.
    + tauto.
    + lia.
    + induction (b1+sum b+2-S(length b)); cbn; auto.
Qed.

End TM45.


Module TM46.

Definition tm := Eval compute in (TM_from_str "1LB0LD_0RC0LE_1LE1RD_1RC1RE_1LF1RB_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (A,[0;1;1;1]).
Notation hR := (B,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition LS n :=
  <[0;1] <+ <[1;1]^^(2+n*2).

Definition RS n :=
  [0;1]^^(2+n*2) ++ [1;1].

Lemma LS_L l r s:
  r {{{ (hL,R) }}} l <* LS^^^s -[ tm' ]->*
  RS^^^(rev s) *> r {{{ (hL,R) }}} l.
Proof.
  eapply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  RS^^^(rev s) *> r {{{ (hR,L) }}} l -[ tm' ]->*
  r {{{ (hR,L) }}} l <* LS^^^s.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Llist.
  unfold LS,RS.
  es.
Qed.

Definition LC1 a0 a b :=
  0inf <* LS^^^a <* <[0] <* <[1;1]^^(2+a0*2) <* LS^^^b.

Definition LC2 b :=
  0inf <* LS^^^b.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold LC1,LC2;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma LInc1 a0 a1 a b:
  sideRLs tm' hLR (LC1 a0 (a1::a) (b)) (LC1 a1 a (b++[1+a0])).
Proof.
  simpl'.
  esx.
  repeat follow'.
Qed.

Lemma LIncs1 a0 a1 a b:
  sideRLs tm' (hLR^^((length a)+1)) (LC1 a0 (a++[a1]) b) (LC1 a1 [] (b++map S (a0::a))).
Proof.
  gen a0 a1 b.
  induction a; intros.
  - rw_ls.
    apply LInc1.
  - replace (length (a::a0)+1) with (1+(length a0+1)) by (cbn; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: cbn; apply LInc1.
    applys_eq IHa; rw_ls; flia.
Qed.

Lemma LOv1 a0 b:
  sideRLs tm' hLR (LC1 a0 [] b) (LC2 (b++[1+a0])).
Proof.
  simpl'.
  esx.
  repeat follow'.
Qed.

Lemma LIncs2 b n:
  sideRLs tm' (hLR^^n) (LC2 b) (LC2 (b++[O]^^n)).
Proof.
  induction n.
  - rw_ls.
    rewrite app_nil_r.
    esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl'.
    esx.
    repeat follow'.
Qed.

Lemma LIncs a0 a1 a b n:
  sideRLs tm' (hLR^^((length a)+1+1+n)) (LC1 a0 (a++[a1]) b) (LC2 (b++(map S (a0::a++[a1]))++[O]^^n)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  1: eapply sideRLs_trans.
  1: apply LIncs1.
  1: apply LOv1.
  applys_eq LIncs2; rw_ls; flia.
Qed.

Definition RC n := [0;1]^^(1+n*2) *> 0inf.
Definition RC0 := [1] *> 0inf.

Lemma RIncs n:
  sideRLs tm (hRL^^(n*2+1)) (RC n) RC0.
Proof.
  unfold RC,RC0.
  induction n.
  - esx.
  - replace (S n*2+1) with (2+(n*2+1)) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: apply IHn.
    esx.
Qed.


Lemma Ov2 b0 b1 b:
  LC2 (b0::b1::b) {{{ (hR,R) }}} RC0 -->+
  LC1 b1 (b) [] {{{ (hL,L) }}} RC (1+b0).
Proof.
  unfold LC1,LC2,RC0,RC.
  eapply (unflip_progress _ (_,(_,_,_)) (_,(_,_,_))).
  simpl'.
  follow'.
Qed.

Close Scope sym.

Definition S1 b := LC2 (b++[0]) {{{ (hR,R) }}} RC0.

Lemma BigStep b0 b:
  1<=(length b)<=b0*2+2 ->
  S1 (b0::b) -->+
  S1 ((map S (b++[0]))++[0]^^(b0*2+2-length b)).
Proof.
  unfold S1.
  intros.
  destruct b as [|b1 b].
  1: rw_ls; lia.
  follow11 Ov2.
  unfold to_DH_config.
  epose proof (RIncs (1+b0)) as I2.
  epose proof (LIncs b1 0 b [] (b0*2+2-(length b))) as I1.
  rewrite <-lrcons_lpow1 in I1 by lia.
  replace (length b+1+1+(b0*2+2-length b)-1) with ((1+b0)*2+1) in I1 by (rw_ls; lia).
  epose proof (sideRLs_concat_L I1 I2) as I.
  follow10 I.
  rw_ls.
  replace (b0*2+2-length b) with (b0*2+2-S(length b)+1) by lia.
  rewrite lpow_add.
  finish.
Qed.

Definition S1' b := S1 (sum' b).

Lemma BigStep' b0 b:
  1<=length b<=(sum b)*2+b0*2+2 ->
  S1' (b0::b) -->+
  S1' (b++[1]++[0]^^((sum b)*2+b0*2+2-length b)).
Proof.
  intros.
  unfold S1'.
  unshelve epose proof (BigStep (b0+sum b) (sum' b) _) as I1.
  1: rw_ls; lia.
  rw_ls.
  applys_eq I1; flia.
Qed.

Inductive P: (list nat) -> Prop :=
| P_intro b0 b:
  1<=length b ->
  length b<=(sum b)*2+b0*2+2 ->
  b0<=1 ->
  Forall (fun x => x<=1) b ->
  P (b0::b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' [0;0;0]).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve[lia|congruence|auto].
  intros b' HP.
  inverts HP.
  destruct b as [|b1 b].
  1: rw_ls; lia.
  eexists; split.
  1: apply BigStep'; lia.
  cbn.
  inverts H2.
  econstructor; rw_ls.
  - lia.
  - lia.
  - lia.
  - apply Forall_app; split.
    1: tauto.
    apply Forall_cons.
    1: lia.
    induction ((b1+sum b)*2+b0*2+2-S(length b)); cbn; auto.
Qed.

End TM46.


Module TM47.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1RA_1LE1RD_0RB0LC_---0LF_1LD0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (F,[0;1;1;1]).
Notation hR := (D,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition LS n :=
  <[0;1] <+ <[1;1]^^(2+n*2).

Definition RS n :=
  [0;1]^^(2+n*2) ++ [1;1].

Lemma LS_L l r s:
  r {{{ (hL,R) }}} l <* LS^^^s -[ tm' ]->*
  RS^^^(rev s) *> r {{{ (hL,R) }}} l.
Proof.
  eapply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  RS^^^(rev s) *> r {{{ (hR,L) }}} l -[ tm' ]->*
  r {{{ (hR,L) }}} l <* LS^^^s.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Llist.
  unfold LS,RS.
  es.
Qed.

Definition LC1 a0 a b :=
  0inf <* LS^^^a <* <[0] <* <[1;1]^^(2+a0*2) <* LS^^^b.

Definition LC2 b :=
  0inf <* LS^^^b.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold LC1,LC2;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma LInc1 a0 a1 a b:
  sideRLs tm' hLR (LC1 a0 (a1::a) (b)) (LC1 a1 a (b++[1+a0])).
Proof.
  simpl'.
  esx.
  repeat follow'.
Qed.

Lemma LIncs1 a0 a1 a b:
  sideRLs tm' (hLR^^((length a)+1)) (LC1 a0 (a++[a1]) b) (LC1 a1 [] (b++map S (a0::a))).
Proof.
  gen a0 a1 b.
  induction a; intros.
  - rw_ls.
    apply LInc1.
  - replace (length (a::a0)+1) with (1+(length a0+1)) by (cbn; lia).
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: cbn; apply LInc1.
    applys_eq IHa; rw_ls; flia.
Qed.

Lemma LOv1 a0 b:
  sideRLs tm' hLR (LC1 a0 [] b) (LC2 (b++[1+a0])).
Proof.
  simpl'.
  esx.
  repeat follow'.
Qed.

Lemma LIncs2 b n:
  sideRLs tm' (hLR^^n) (LC2 b) (LC2 (b++[O]^^n)).
Proof.
  induction n.
  - rw_ls.
    rewrite app_nil_r.
    esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl'.
    esx.
    repeat follow'.
Qed.

Lemma LIncs a0 a1 a b n:
  sideRLs tm' (hLR^^((length a)+1+1+n)) (LC1 a0 (a++[a1]) b) (LC2 (b++(map S (a0::a++[a1]))++[O]^^n)).
Proof.
  do 2 rewrite lpow_add.
  eapply sideRLs_trans.
  1: eapply sideRLs_trans.
  1: apply LIncs1.
  1: apply LOv1.
  applys_eq LIncs2; rw_ls; flia.
Qed.

Definition RC n := [0;1]^^(1+n*2) *> 0inf.
Definition RC0 := [1] *> 0inf.

Lemma RIncs n:
  sideRLs tm (hRL^^(n*2+1)) (RC n) RC0.
Proof.
  unfold RC,RC0.
  induction n.
  - esx.
  - replace (S n*2+1) with (2+(n*2+1)) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: apply IHn.
    esx.
Qed.


Lemma Ov2 b0 b1 b:
  LC2 (b0::b1::b) {{{ (hR,R) }}} RC0 -->+
  LC1 b1 (b) [] {{{ (hL,L) }}} RC (1+b0).
Proof.
  unfold LC1,LC2,RC0,RC.
  eapply (unflip_progress _ (_,(_,_,_)) (_,(_,_,_))).
  simpl'.
  follow'.
Qed.

Close Scope sym.

Definition S1 b := LC2 (b++[0]) {{{ (hR,R) }}} RC0.

Lemma BigStep b0 b:
  1<=(length b)<=b0*2+2 ->
  S1 (b0::b) -->+
  S1 ((map S (b++[0]))++[0]^^(b0*2+2-length b)).
Proof.
  unfold S1.
  intros.
  destruct b as [|b1 b].
  1: rw_ls; lia.
  follow11 Ov2.
  unfold to_DH_config.
  epose proof (RIncs (1+b0)) as I2.
  epose proof (LIncs b1 0 b [] (b0*2+2-(length b))) as I1.
  rewrite <-lrcons_lpow1 in I1 by lia.
  replace (length b+1+1+(b0*2+2-length b)-1) with ((1+b0)*2+1) in I1 by (rw_ls; lia).
  epose proof (sideRLs_concat_L I1 I2) as I.
  follow10 I.
  rw_ls.
  replace (b0*2+2-length b) with (b0*2+2-S(length b)+1) by lia.
  rewrite lpow_add.
  finish.
Qed.

Definition S1' b := S1 (sum' b).

Lemma BigStep' b0 b:
  1<=length b<=(sum b)*2+b0*2+2 ->
  S1' (b0::b) -->+
  S1' (b++[1]++[0]^^((sum b)*2+b0*2+2-length b)).
Proof.
  intros.
  unfold S1'.
  unshelve epose proof (BigStep (b0+sum b) (sum' b) _) as I1.
  1: rw_ls; lia.
  rw_ls.
  applys_eq I1; flia.
Qed.

Inductive P: (list nat) -> Prop :=
| P_intro b0 b:
  1<=length b ->
  length b<=(sum b)*2+b0*2+2 ->
  b0<=1 ->
  Forall (fun x => x<=1) b ->
  P (b0::b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S1' [1;0;0]).
  1: unfold S1',S1; esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: econstructor; cbn; solve[lia|congruence|auto].
  intros b' HP.
  inverts HP.
  destruct b as [|b1 b].
  1: rw_ls; lia.
  eexists; split.
  1: apply BigStep'; lia.
  cbn.
  inverts H2.
  econstructor; rw_ls.
  - lia.
  - lia.
  - lia.
  - apply Forall_app; split.
    1: tauto.
    apply Forall_cons.
    1: lia.
    induction ((b1+sum b)*2+b0*2+2-S(length b)); cbn; auto.
Qed.

End TM47.


Module TM48.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC1RE_1RD0LE_1RB1RD_0LF0LA_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{D}}> r) (at level 30).

Definition LS n :=
  <[0;1;1;0] <+ <[1;1;1]^^(1+n).

Definition RS n :=
  [1;1;0;0] ++ [1;1;1]^^(1+n).

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Definition S1 k a b c :=
  0inf <* [1] <* <[0;1;1;0;1]^^k <* LS^^^a <* <[0;1;1;1] <* LS^^^b <| [1;1;0;0] *> [1]^^(1+c) *> 0inf.

Definition S2 k b c :=
  0inf <* [1] <* <[0;1;1;0;1]^^k <* LS^^^b <| [1;1;0;0] *> [1]^^(1+c) *> 0inf.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold S1,S2;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 k a0 a b c:
  S1 k (a0::a) b (1+c) -->*
  S1 k a (b++[1+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 k a b c:
  S1 k a b (length a + c) -->*
  S1 k [] (b++(map S a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  simpl'; finish.
Qed.

Lemma Ov1 k b c:
  S1 (1+k) [] b (1+c) -->*
  S2 k (b++[O;O]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Inc2 k b c:
  S2 k b (1+c) -->*
  S2 (1+k) b c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 k b c:
  S2 k b c -->*
  S2 (c+k) b 0.
Proof.
  gen k.
  ind c Inc2.
Qed.

Lemma Ov2 k b0 b:
  S2 k (b0::b) 0 -->+
  S1 (1+k) b [] (4+b0*3).
Proof.
  simpl'.
  repeat follow'.
Qed.

Close Scope sym.

Lemma BigStep k b0 b:
  length b <= b0*3+3 ->
  S2 k (b0::b) 0 -->+
  S2 ((b0*3+3-length b)+k) ((map S b)++[0;0]) 0.
Proof.
  intros.
  follow10 Ov2.
  follow (Incs1 (1+k) b [] (1+(3+b0*3-length b))).
  follow Ov1.
  follow Incs2.
  finish.
Qed.

Definition S1' '(k,b) := S2 k (sum' (b++[0])) 0.

Lemma BigStep' k b0 b:
  length b<=(b0+sum b)*3+2 ->
  S1' (k,b0::b) -->+
  S1' (k+((b0+sum b)*3+2-length b),b++[1;0]).
Proof.
  intros.
  unfold S1'.
  unshelve epose proof (BigStep k (b0+(sum b+0)) (sum' (b++[0])) _) as I1.
  1: rw_ls; lia.
  rw_ls.
  applys_eq I1; flia.
Qed.

Definition S' n := S1' ((n+1)*(n+4),[0]++[1;0]^^n).


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: unfold S',S1',S2; esx.
  eapply progress_nonhalt_simple.
  intros n.
  exists (S n).
  unfold S'.
  Local Opaque S1' Nat.mul.
  cbn.
  epose proof (BigStep' _ 0 ([1;0]^^n) _) as I1.
  follow10 I1. clear I1.
  repeat (cbn; rewrite lpow_rotate_list).
  rw_ls.
  rewrite app_nil_r.
  epose proof (BigStep' _ 1 (0::[1;0]^^n) _) as I1.
  follow100 I1. clear I1.
  repeat (cbn; rewrite lpow_rotate_list).
  rw_ls.
  rewrite app_nil_r.
  finish.
  Unshelve.
  all: rw_ls; lia.
Qed.

End TM48.


Module TM49.

Definition tm := Eval compute in (TM_from_str "1LB1RA_0LC0RD_0LD1LF_1LE1RE_0RA1LB_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;0;1] {{A}}> r) (at level 30).
Notation "l |2> r" := (l <* <[1] {{E}}> r) (at level 30).

Definition LS n :=
  <[1;0;0;0]^^(1+n) <+ [0].

Definition RS n :=
  [0;1;0;1]^^n ++ [0;1;1;0;1].

Definition LS' n :=
  <[1;0;0;0]^^(n) <+ <[1;0;1;0;0].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R' l r s:
  l |2> RS^^^(rev s) *> r -->*
  l <* LS'^^^s |2> r.
Proof.
  replace (LS'^^^s) with (LS'^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS',RS.
  es.
Qed.

Definition S1 l a b c :=
  l <* LS'^^^a <* LS^^^b <| [0;1] *> [0;1;0;1]^^(1+c) *> 0inf.

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite rev_app_distr ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Ltac follow' :=
  unfold LS,LS',RS;
  es; er; (follow LS_L || follow RS_R || follow RS_R').

Notation lh0 := (0inf <* <[1;0]^^6).
Notation lh1 := (0inf <* <[1;0]^^4).
Notation lh2 := (0inf <* <[1;0]^^2).

Lemma Inc1 l a1 a b c:
  S1 l (1+a1::a) b c -->*
  S1 l a (b++[a1]) (2+c).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov0 b0 b c:
  S1 lh0 [] (b++[b0]) c -->*
  S1 lh1 (b++[1+b0]) [c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1 b0 b c:
  S1 lh1 [] (b++[b0]) c -->*
  S1 lh2 (b++[1+b0]) [c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Notation lh3 := (0inf <* <[1;0;1;0;1;0;0;0;0;0]).

Lemma Ov2 b0 b c:
  S1 lh2 [0;1]%nat (b++[b0]) c -->*
  S1 lh3 (b++[1+b0]) [2+c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Notation lh4 := (0inf <* <[1;0;1;0]).

Lemma Ov3 b0 b c:
  S1 lh3 [] (b++[b0]) c -->*
  S1 lh4 (b++[1+b0]) [c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov4 b0 b c:
  S1 lh4 [] (b++[b0]) c -->*
  S1 0inf (b++[1+b0]) [c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov5 b0 b c:
  S1 0inf [] (b++[b0]) c -->*
  S1 0inf (b++[1+b0]) [c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Notation lh7 := (0inf <* <[1;0;0;0;1;0;0;0;1;0;0;0;0;0]).

Lemma Ov6 b0 b c:
  S1 0inf [0;3]%nat (b++[b0]) c -->*
  S1 lh7 (b++[1+b0]) [2+c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov7' b0 b c:
  S1 lh7 [] (b++[b0]) c -->+
  S1 lh0 (b++[1+b0]) [c] 0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 l a' a b c:
  S1 l ((map S a)++a') b c -->*
  S1 l a' (b++a) ((length a)*2+c).
Proof.
  gen b c.
  induction a; intros.
  1: rw_ls; rewrite app_nil_r; finish.
  cbn.
  follow Inc1.
  follow IHa.
  rw_ls.
  finish.
Qed.

Close Scope sym.

Lemma BigStep b0 b:
  S1 lh0 ((map (Nat.add 8) b)++[7;6;5;2;1]) [b0+7] 0 -->+
  let len:=length b+1 in
  S1 lh0 (len*2+14::len*2+13::len*2+10::len*2+7::len*2+6::len*2+5::len*2+2::b0::b++[1]) [len*2+14] 0.
Proof.
  remember (length b+1) as len.

  epose proof (Incs1 _ [] ((map (Nat.add 7) b)++[6;5;4;1;0]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov0 0 (b0+7::(map (Nat.add 7) b)++[6;5;4;1]) _) as I1.
  rw_ls.
  follow I1. clear I1.

  epose proof (Incs1 _ [] (b0+6::(map (Nat.add 6) b)++[5;4;3;0;0]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov1 0 (len*2+8::b0+6::(map (Nat.add 6) b)++[5;4;3;0]) _) as I1.
  rw_ls.
  follow I1. clear I1.

  epose proof (Incs1 _ [0;1] (len*2+7::b0+5::(map (Nat.add 5) b)++[4;3;2]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov2 2 (len*2+10::len*2+7::b0+5::(map (Nat.add 5) b)++[4;3]) _) as I1.
  rw_ls.
  follow I1. clear I1.

  epose proof (Incs1 _ [] (len*2+9::len*2+6::b0+4::(map (Nat.add 4) b)++[3;2;2]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov3 2 (len*2+10::len*2+9::len*2+6::b0+4::(map (Nat.add 4) b)++[3;2]) _) as I1.
  rw_ls.
  follow I1. clear I1.

  epose proof (Incs1 _ [] (len*2+9::len*2+8::len*2+5::b0+3::(map (Nat.add 3) b)++[2;1;2]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov4 2 (len*2+10::len*2+9::len*2+8::len*2+5::b0+3::(map (Nat.add 3) b)++[2;1]) _) as I1.
  rw_ls.
  follow I1. clear I1.

  epose proof (Incs1 _ [] (len*2+9::len*2+8::len*2+7::len*2+4::b0+2::(map (Nat.add 2) b)++[1;0;2]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov5 2 (len*2+12::len*2+9::len*2+8::len*2+7::len*2+4::b0+2::(map (Nat.add 2) b)++[1;0]) _) as I1.
  rw_ls.
  follow I1. clear I1.

  epose proof (Incs1 _ [0;3] (len*2+11::len*2+8::len*2+7::len*2+6::len*2+3::b0+1::(map S b)++[0]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov6 0 (len*2+14::len*2+11::len*2+8::len*2+7::len*2+6::len*2+3::b0+1::(map S b)) _) as I1.
  rw_ls.
  follow I1. clear I1.

  epose proof (Incs1 _ [] (len*2+13::len*2+10::len*2+7::len*2+6::len*2+5::len*2+2::b0::(b)++[0]) _ 0) as I1.
  rw_ls.
  follow I1. clear I1.
  epose proof (Ov7' 0 (len*2+14::len*2+13::len*2+10::len*2+7::len*2+6::len*2+5::len*2+2::b0::(b)) _) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Definition S' n :=
  S1 lh0 (sum' ([1;3;3;1]^^(S n)++[1;3;1;1])) [n*8+14] 0.

Lemma BigStep' n:
  S' n -->+
  S' (S n).
Proof.
  unfold S'.
  epose proof (BigStep (n*8+7) (sum' ([1;3;3;1]^^n++[1;3;2]))) as I1.
  rw_ls.
  applys_eq I1; flia.
  destruct n.
  1: rw_ls; flia.
  replace (map (fun m : nat => S (S (S (S (S (S m)))))) (sum' ([1; 3; 3; 1] ^^ S n)) ++ [6; 5; 2; 1]) with (map (fun m : nat => S (S (S (S (S (S m)))))) (sum' ([1; 3; 3; 1] ^^ (n + 1))) ++ [6; 5; 2; 1]) by flia.
  rewrite lpow_add.
  rw_ls.
  flia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: unfold S',S1; esx.
  eapply progress_nonhalt_simple.
  intro n.
  eexists.
  apply BigStep'.
Qed.

End TM49.


Module TM50.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RF_---0LD_0LE1LE_1LF1LD_0RA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{A}}> r) (at level 30).

Definition LS n :=
  <[1;1]^^(1+n) <+ <[1;0].

Definition RS n :=
  [1;1]^^(n) ++ [1;0;1;1].

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Definition S1 a0 a b c :=
  0inf <* LS^^^a <* <[1;1]^^(1+a0) <* <[0] <* LS^^^b <| [1;1]^^(c) *> 0inf.

Definition S2 b c :=
  0inf <* LS^^^b <| [1;1]^^(c) *> 0inf.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold S1,S2;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 a0 a1 a b c:
  S1 a0 (a1::a) b (1+c) -->*
  S1 a1 a (b++[1+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 a0 a1 a b c:
  S1 a0 (a++[a1]) b (length a+1+c) -->*
  S1 a1 [] (b++(map S (a0::a))) c.
Proof.
  gen a0 a1 b c.
  induction a; intros.
  - follow Inc1.
    finish.
  - cbn.
    follow Inc1.
    follow IHa.
    rw_ls.
    finish.
Qed.

Lemma Ov1 a0 b c:
  S1 a0 [] b (1+c) -->*
  S2 (b++[1+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1' a0 b0 b1 b:
  S1 a0 [] (b0::b1::b) 0 -->+
  S1 b1 (b++[1+a0;O]) [] b0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Inc2 b c:
  S2 b (1+c) -->*
  S2 (b++[O]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs2 b c:
  S2 b c -->*
  S2 (b++[O]^^c) 0.
Proof.
  gen b.
  induction c; intros.
  1: rewrite app_nil_r; finish.
  follow Inc2.
  follow IHc.
  rw_ls.
  finish.
Qed.

Lemma Ov2 b0 b1 b:
  S2 (b0::b1::b) 0 -->+
  S1 b1 (b++[O;O]) [] (b0).
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma BigStep a0 a1 a c:
  S1 a0 ((a1::a)++[O]) [] (length (a1::a)+1+c) -->+
  S1 (1+a1) ((map S (a++[O]))++[O]^^c++[O]) [] (1+a0).
Proof.
  follow (Incs1).
  destruct c.
  - cbn.
    follow10 Ov1'.
    rw_ls.
    finish.
  - cbn.
    follow Ov1.
    follow Incs2.
    cbn.
    follow10 Ov2.
    rw_ls.
    repeat (cbn; rewrite lpow_rotate_list).
    finish.
Qed.

Close Scope sym.

Definition S1' a0 a c :=
  S1 a0 (sum' a++[O]) [] (length a+1+c).

Lemma BigStep' a0 a1 a c:
  length a+c+1<=a0 ->
  S1' a0 (a1::a) c -->+
  S1' (a1+sum a+1) (a++[1]++[0]^^c) (a0-(length a+c+1)).
Proof.
  intros.
  unfold S1'.
  epose proof (BigStep a0 (a1+sum a) (sum' a) c) as I1.
  rw_ls.
  follow10 I1.
  rw_ls.
  finish.
Qed.

Definition S3 a b :=
  S1' (1+a+b) ([1]^^a++[0]++[1]^^b) 0.

Lemma Inc3 a b:
  S3 (1+a) b -->*
  S3 a (1+b).
Proof.
  unfold S3.
  cbn.
  epose proof (BigStep' (a+b+2) 1 ([1]^^a++[0]++[1]^^b) 0 _) as I1.
  rw_ls.
  rewrite lpow_rotate_list,app_nil_r in I1.
  rw_ls.
  apply progress_evstep.
  applys_eq I1; flia.
  Unshelve.
  1: rw_ls; lia.
Qed.

Lemma Incs3 a b:
  S3 a b -->*
  S3 0 (a+b).
Proof.
  gen b.
  ind a Inc3.
Qed.

Definition S4 n := S3 n 0.

Ltac rw_ls' :=
  repeat (rw_ls ||
  rewrite lpow_rotate_list in * ||
  rewrite lpow_add in * ||
  rewrite app_nil_r in * ||
  cbn in *).

Lemma BigStep'' n:
  S4 n -->+
  S4 (n+1).
Proof.
  unfold S4.
  follow Incs3.
  unfold S3.
  mid10 (S1' (1+n) ([1]^^(1+n)) 0).
  {
    cbn.
    epose proof (BigStep' (n+1) 0 ([1]^^n) 0 _) as I1.
    rw_ls'.
    applys_eq I1; flia.
  }
  mid (S1' (2+n) ([1]^^(1+n)) 0).
  {
    apply progress_evstep.
    epose proof (BigStep' (n+1) 1 ([1]^^n) 0 _) as I1.
    rw_ls'.
    applys_eq I1; flia.
  }
  mid (S1' (2+n) ([1]^^(1+n)) 1).
  {
    apply progress_evstep.
    epose proof (BigStep' (n+2) 1 ([1]^^n) 0 _) as I1.
    rw_ls'.
    applys_eq I1; flia.
  }
  {
    apply progress_evstep.
    epose proof (BigStep' (n+2) 1 ([1]^^n) 1 _) as I1.
    rw_ls'.
    applys_eq I1; flia.
  }
  Unshelve.
  all: rw_ls; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S4 0).
  1: unfold S4,S3,S1',S1; esx.
  eapply progress_nonhalt_simple.
  intro; eexists; apply BigStep''.
Qed.

End TM50.


Module TM51.

Definition tm := Eval compute in (TM_from_str "1RB1LF_1RC1LB_1RD0LA_1LE0RC_---1LA_0LD1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [] {{D}}> r) (at level 30).

Definition LS n :=
  <[0;1;0;1] <+ <[1;1;1]^^n.

Definition RS n :=
  [1;0;1;0] ++ [1;1;0]^^n.

Lemma LS_L l r s:
  l <* LS^^^s <| r -->*
  l <| RS^^^(rev s) *> r.
Proof.
  eapply Llist.
  unfold LS,RS.
  es.
Qed.

Lemma RS_R l r s:
  l |> RS^^^(rev s) *> r -->*
  l <* LS^^^s |> r.
Proof.
  replace (LS^^^s) with (LS^^^(rev (rev s))) by (f_equal; apply rev_involutive).
  apply Rlist.
  unfold LS,RS.
  es.
Qed.

Definition S1 k a b c :=
  0inf <* <[0;1;1;1;1]^^k <* <[1;1;1] <* LS^^^a <* <[1;1;1;1] <* LS^^^b <| [1;1;1]^^(c) *> 0inf.

Ltac follow' :=
  unfold LS,RS;
  es; er; (follow LS_L || follow RS_R).

Ltac simpl' :=
  unfold S1;
  repeat (
  cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite app_nil_r ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite Str_app_assoc).

Lemma Inc1 k a0 a b c:
  S1 k (a0::a) b (2+c) -->*
  S1 k a (b++[2+a0]) c.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Incs1 k a b c:
  S1 k a b (length a*2+c) -->*
  S1 k [] (b++(map (Nat.add 2) a)) c.
Proof.
  gen b c.
  induction a; intros.
  1: simpl'; finish.
  cbn.
  follow Inc1.
  follow IHa.
  rw_ls.
  finish.
Qed.

Lemma Ov1 b0 b:
  S1 2 [] (2+b0::b) 0 -->*
  S1 2 (b++[4]) [] b0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_2 b0 b:
  S1 2 [] (2+b0::b) 2 -->*
  S1 4 (b++[4]) [] b0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma Ov1_2' b0 b:
  S1 4 [] (2+b0::b) 2 -->+
  S1 2 (b++[4;4]) [] b0.
Proof.
  simpl'.
  repeat follow'.
Qed.

Lemma BigStep0 b0 b:
  S1 2 (b0::b) [] (length (b0::b)*2+0) -->*
  S1 2 (map (Nat.add 2) b ++ [4]) [] b0.
Proof.
  follow Incs1.
  cbn.
  follow Ov1.
  finish.
Qed.

Lemma BigStep1 b0 b:
  S1 2 (b0::b) [] (length (b0::b)*2+2) -->*
  S1 4 (map (Nat.add 2) b ++ [4]) [] b0.
Proof.
  follow Incs1.
  cbn.
  follow Ov1_2.
  finish.
Qed.

Lemma BigStep2 b0 b:
  S1 4 (b0::b) [] (length (b0::b)*2+2) -->+
  S1 2 (map (Nat.add 2) b ++ [4;4]) [] b0.
Proof.
  follow Incs1.
  cbn.
  follow10 Ov1_2'.
  finish.
Qed.

Definition S1' k b c :=
  S1 k (sum' (b++[4])) [] (length b*2+2+c).

Lemma BigStep0' b0 b d:
  sum b+d = length b*2 ->
  S1' 2 (b0+d::b) 0 -->*
  S1' 2 (b++[2]) b0.
Proof.
  intros.
  unfold S1'.
  epose proof (BigStep0 (b0+d+sum b+4) (sum' (b++[4]))) as I1.
  rw_ls.
  follow I1.
  finish.
Qed.

Lemma BigStep1' b0 b:
  sum b = length b*2 ->
  S1' 2 (b0::b) 2 -->*
  S1' 4 (b++[2]) b0.
Proof.
  intros.
  unfold S1'.
  epose proof (BigStep1 (b0+sum b+4) (sum' (b++[4]))) as I1.
  rw_ls.
  follow I1.
  finish.
Qed.

Lemma BigStep2' b0 b:
  sum b = length b*2 ->
  S1' 4 (b0+2::b) 2 -->+
  S1' 2 (b++[2;O]) b0.
Proof.
  intros.
  unfold S1'.
  epose proof (BigStep2 (b0+2+sum b+4) (sum' (b++[4]))) as I1.
  rw_ls.
  applys_eq I1; flia.
Qed.

Close Scope sym.

Ltac rw_ls' :=
  repeat (rw_ls ||
  rewrite lpow_rotate_list in * ||
  rewrite lpow_add in * ||
  rewrite app_nil_r in * ||
  cbn in *).

Definition S3 a b := S1' 2 ([2]^^a++[0]++[2]^^b) 0.

Lemma Inc3 a b:
  S3 (1+a) b -->*
  S3 a (1+b).
Proof.
  unfold S3.
  unshelve epose proof (BigStep0' 0 ([2]^^a++[0]++[2]^^b) 2 _) as I1.
  1: rw_ls; lia.
  follow I1.
  rw_ls'.
  finish.
Qed.

Lemma Incs3 a b:
  S3 a b -->*
  S3 0 (a+b).
Proof.
  gen b.
  ind a Inc3.
Qed.

Definition S4 n := S3 n 0.

Lemma BigStep'' n:
  S4 n -->+
  S4 (n+1).
Proof.
  unfold S4.
  follow Incs3.
  unfold S3.
  mid01 (S1' 2 ([2]^^(1+n)) 0).
  {
    epose proof (BigStep0' 0 ([2]^^n) 0 _) as I1. 
    rw_ls'.
    applys_eq I1; flia.
  }
  mid01 (S1' 2 ([2]^^(1+n)) 2).
  {
    epose proof (BigStep0' 2 ([2]^^n) 0 _) as I1. 
    rw_ls'.
    applys_eq I1; flia.
  }
  mid01 (S1' 4 ([2]^^(1+n)) 2).
  {
    epose proof (BigStep1' 2 ([2]^^n) _) as I1. 
    rw_ls'.
    applys_eq I1; flia.
  }
  {
    epose proof (BigStep2' 0 ([2]^^n) _) as I1.
    rw_ls'.
    applys_eq I1; flia.
  }
  Unshelve.
  all: rw_ls; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S4 0).
  1: unfold S4,S3,S1',S1; esx.
  eapply progress_nonhalt_simple.
  intro; eexists; apply BigStep''.
Qed.

End TM51.


