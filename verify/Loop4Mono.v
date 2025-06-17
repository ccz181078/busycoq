From BusyCoq Require Import Individual62.
Require Import Lia.
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


