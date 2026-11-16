From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import SimplTape.

Ltac unfold_config' :=
match goal with
| |- ?a -[_]->* ?b -> _ =>
  unfold_config_expr a;
  unfold_config_expr b
end.

Ltac follow' x :=
  pose proof x as Hx;
  gen Hx;
  unfold_config';
  simpl_rotate;
  intro Hx;
  try (
  follow Hx;
  clear Hx).

Inductive wf_side :=
| wf_side_intro r sr (Hr:sigma_score_side r sr).

Definition to_side(x:wf_side) :=
match x with
| wf_side_intro r _ _ => r
end.

Ltac solve_sigma_score_side :=
 repeat
  apply sigma_score_side_O ||
  apply sigma_score_lpow ||
  apply sigma_score_Str_app ||
  eassumption || (cbn; reflexivity).

Ltac exside x :=
  unshelve eexists (wf_side_intro x _ _); [| solve_sigma_score_side |].

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LE_0LC0RD_1LC1LA_1RE0RF_0LA0LF_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1;1;1]^^(1+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (1+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b*3) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 0 (4+b*3) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b*3) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c+n2)*3 ->
  4+n2*3>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) n' (4+n2*3-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (4+n2*3) with (n'+(4+n2*3-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c+n2)*3+1 ->
  3+n2*3>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) n' (3+n2*3-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2*3) with (n'+(3+n2*3-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c)*3 ->
  8+n2*6>=c*5 ->
  n2>=c*5+5 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c)*3+1 ->
  4+n2*6>=c*5 ->
  n2>=c*5+5 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (8+n2*6-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n',4+n2*3-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*6-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n',3+n2*3-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (46,14,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 13 4 0 14); try lia.
    unfold P1.
    intros.
    destruct r.
    exside ([0]*>r).
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM1.
  

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0LF_1RD1LB_0LE0RA_1LE1LC_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1;1;1]^^(1+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (1+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b*3) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 0 (4+b*3) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b*3) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c+n2)*3 ->
  4+n2*3>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) n' (4+n2*3-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (4+n2*3) with (n'+(4+n2*3-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c+n2)*3+1 ->
  3+n2*3>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) n' (3+n2*3-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2*3) with (n'+(3+n2*3-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c)*3 ->
  8+n2*6>=c*5 ->
  n2>=c*5+5 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c)*3+1 ->
  4+n2*6>=c*5 ->
  n2>=c*5+5 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (8+n2*6-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n',4+n2*3-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*6-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n',3+n2*3-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (46,14,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 13 4 0 14); try lia.
    unfold P1.
    intros.
    destruct r.
    exside ([0]*>r).
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro (0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LF_0LD1LB_1RE1LC_0RA1LF_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 1 (2+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  2+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3+1) (2+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (2+n2) with (n'+(2+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3+1,2+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (90,78,4)%nat.
    eapply P_0; try lia.
    apply (P1_S0 31 27 1 26); try lia.
    apply (P1_S0 8 7 0 9); try lia.
    apply (P1_S1 0 0 0 2); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro (0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC1LF_1RD0RC_0LE0LF_0LA1LD_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 1 (2+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  2+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3+1) (2+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (2+n2) with (n'+(2+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3+1,2+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (90,78,4)%nat.
    eapply P_0; try lia.
    apply (P1_S0 31 27 1 26); try lia.
    apply (P1_S0 8 7 0 9); try lia.
    apply (P1_S1 0 0 0 2); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1LD1LB_1RA0LC_---1LF_1LF1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (37,33,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 10 9 0 11); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro (0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1LD1LB_1RA0RC_---1LF_1LF1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (37,33,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 10 9 0 11); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro (0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0RA_1RD0RC_0LA0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (37,33,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 10 9 0 11); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0LA_1RD0RC_0LA0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (37,33,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 10 9 0 11); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB0RD_0LC0LD_1RA1LB_---0RE_0LF0RA_1LF1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1;1] *> [1;1;1]^^(b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (1+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b*3) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b*3) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;1] <| R b c r -->*
  l <| R 0 (2+b*3) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c+n2)*3 ->
  3+n2*3>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) n' (3+n2*3-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2*3) with (n'+(3+n2*3-n')) by lia.
  follow Incs.
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c+n2)*3+1 ->
  2+n2*3>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) n' (2+n2*3-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (2+n2*3) with (n'+(2+n2*3-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c)*3 ->
  6+n2*6>=c*5 ->
  n2>=c*5+5 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c)*3+1 ->
  2+n2*6>=c*5 ->
  n2>=c*5+5 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*6-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n',3+n2*3-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (2+n2*6-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n',2+n2*3-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (34,10,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 10 3 0 10); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1LD1LB_1RA1RF_---1LF_1LF1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 0 (4+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  4+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (4+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (4+n2) with (n'+(4+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  8+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (8+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,4+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (46,42,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 13 12 0 14); try lia.
    apply (P1_S1 0 0 0 4); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro (0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC1LD_1RD0RC_0LA0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 0 (4+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  4+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (4+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (4+n2) with (n'+(4+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  8+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (8+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,4+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (46,42,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 13 12 0 14); try lia.
    apply (P1_S1 0 0 0 4); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC1RF_1RD0RC_0LA0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 0 (4+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  4+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (4+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (4+n2) with (n'+(4+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  8+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (8+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,4+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (46,42,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 13 12 0 14); try lia.
    apply (P1_S1 0 0 0 4); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1LD1LB_1RA1LB_---1LF_1LF1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 0 (4+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  4+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (4+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (4+n2) with (n'+(4+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  8+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (8+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,4+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (46,42,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 13 12 0 14); try lia.
    apply (P1_S1 0 0 0 4); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM13.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1LF_1LC0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{F}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;1] <| R b c r -->*
  l <| R 0 (1+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  1+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+1+n'*2) (n'*3) (1+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (1+n2) with (n'+(1+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  0+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (0+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+1+n'*2,n'*3,1+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (226,195,10)%nat.
    eapply P_1; try lia.
    apply (P1_S1 84 72 4 65); try lia.
    apply (P1_S0 31 27 1 24); try lia.
    apply (P1_S0 10 9 0 9); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1LF_1LC0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{F}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;1] <| R b c r -->*
  l <| R 0 (1+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  1+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+1+n'*2) (n'*3) (1+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (1+n2) with (n'+(1+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  0+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (0+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+1+n'*2,n'*3,1+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (226,195,10)%nat.
    eapply P_1; try lia.
    apply (P1_S1 84 72 4 65); try lia.
    apply (P1_S0 31 27 1 24); try lia.
    apply (P1_S0 10 9 0 9); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1LF_1LC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{F}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;1] <| R b c r -->*
  l <| R 1 (1+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  1+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3+1) (1+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (1+n2) with (n'+(1+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  0+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (0+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3+1,1+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (88,76,4)%nat.
    eapply P_0; try lia.
    apply (P1_S0 32 28 1 25); try lia.
    apply (P1_S0 10 9 0 9); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1LB0RB_1RC1LD_1RD0RC_0LB0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;1] <| R b c r -->*
  l <| R 0 (1+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  1+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+1+n'*2) (n'*3) (1+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (1+n2) with (n'+(1+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  0+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (0+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+1+n'*2,n'*3,1+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (226,195,10)%nat.
    eapply P_1; try lia.
    apply (P1_S1 84 72 4 65); try lia.
    apply (P1_S0 31 27 1 24); try lia.
    apply (P1_S0 10 9 0 9); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM17.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC1LD_1RD0RC_0LB0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;1] <| R b c r -->*
  l <| R 0 (1+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  1+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+1+n'*2) (n'*3) (1+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (1+n2) with (n'+(1+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  0+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (0+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+1+n'*2,n'*3,1+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (226,195,10)%nat.
    eapply P_1; try lia.
    apply (P1_S1 84 72 4 65); try lia.
    apply (P1_S0 31 27 1 24); try lia.
    apply (P1_S0 10 9 0 9); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM18.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LD_1RD0RC_0LB0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;1] <| R b c r -->*
  l <| R 1 (1+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  1+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3+1) (1+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (1+n2) with (n'+(1+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  0+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (0+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3+1,1+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (88,76,4)%nat.
    eapply P_0; try lia.
    apply (P1_S0 32 28 1 25); try lia.
    apply (P1_S0 10 9 0 9); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM19.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1LF_1LC1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{F}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;1] <| R b c r -->*
  l <| R 0 (2+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  2+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (2+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (2+n2) with (n'+(2+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  2+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (2+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,2+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (34,30,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 10 9 0 10); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM20.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1LD1LB_1RA0LD_---1LF_1LF1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 2 (2+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  2+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3+2) (2+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (2+n2) with (n'+(2+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3+2,2+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (34,30,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 9 8 0 10); try lia.
    apply (P1_S1 0 0 0 2); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM21.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC1LD_1RD0RC_0LB0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(2+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;1;0] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;1] <| R b c r -->*
  l <| R 0 (2+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  2+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+2+n'*2) (n'*3) (2+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (2+n2) with (n'+(2+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  6+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  2+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (6+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (2+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+2+n'*2,n'*3,2+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (34,30,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 10 9 0 10); try lia.
    apply (P1_S1 0 0 0 3); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM22.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC0LB_1RD0RC_0LA0LE_---1LF_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(3+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1;0] <* [0]^^(b) <| R 0 0 r.
Proof.
  unfold R.
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* <[0;0;0;1;0] <| R b c r -->*
  l <| R 2 (2+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* <[0;0;0;1] <| R b c r -->*
  l <| R 0 (3+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n1 n2 c :=
  forall l r,
  exists r',
  l <* [0]^^n1 <| R 0 0 r -->*
  l <| R n2 c r'.


Lemma P1_S1 n1 n2 c n':
  n1=(c*3+n2) ->
  2+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3+2) (2+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv1 _ _ _ _) as [r3 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  follow HP1b.
  follow LOv1a.
  replace (2+n2) with (n'+(2+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Lemma P1_S0 n1 n2 c n':
  n1=(c*3+n2)+1 ->
  3+n2>=n' ->
  P1 n1 n2 c ->
  P1 (n1+c*2+2+3+n'*2) (n'*3) (3+n2-n').
Proof.
  unfold P1.
  intros Hn1 Hn' HP1 l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (HP1 _ _) as [r2 HP1b].
  epose proof (LOv0 _ _ _ _) as [r3 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROv.
  rewrite Hn1 in HP1b.
  rewrite <-lpow_add' in HP1b.
  cbn[Str_app].
  follow HP1b.
  follow LOv0a.
  replace (3+n2) with (n'+(3+n2-n')) by lia.
  follow Incs.
  cbn[Str_app].
  finish.
Qed.

Inductive P: nat*nat*nat->nat->Prop :=
| P_0 n1 n2 c m:
  n1=(n2+c*3) ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
| P_1 n1 n2 c m:
  n1=(n2+c*3)+1 ->
  4+n2*2>=c*5 ->
  n2>=c*15+15 ->
  n2>=m ->
  P1 n1 n2 c ->
  P (n1,n2,c) m
.

Lemma P_spec x m:
  P x m ->
  let '(n1,n2,c):=x in
  P1 n1 n2 c /\
  n2>=m.
Proof.
  intros HP.
  inverts HP; tauto.
Qed.

Lemma P_S x m:
  P x m ->
  exists x', P x' (S m).
Proof.
  intros HP.
  inversion HP.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3+2,2+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S1; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S1; try assumption; try lia.
  - remember (4+n2*2-c*5) as n''.
    remember (n''/2) as n'.
    exists (n1+c*2+2+3+n'*2,n'*3,3+n2-n').
    pose proof (Nat.Div0.div_mod n'' 2).
    pose proof (Nat.mod_upper_bound n'' 2).
    remember (n'' mod 2) as v1.
    destruct v1 as [|[|]].
    3: lia.
    + eapply P_1; try lia.
      eapply P1_S0; try assumption; try lia.
    + eapply P_0; try lia.
      eapply P1_S0; try assumption; try lia.
Qed.

Lemma P_n m:
  exists x, P x m.
Proof.
  induction m.
  - exists (34,30,1)%nat.
    eapply P_1; try lia.
    apply (P1_S0 9 8 0 10); try lia.
    apply (P1_S1 0 0 0 2); try lia.
    unfold P1.
    intros.
    exists r.
    es.
  - destruct IHm as [x HP].
    eapply P_S; eauto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [[[n1 n2] c] HP].
  pose proof (P_spec _ _ HP) as [HP1 Hn].
  unfold P1 in HP1.
  epose proof (HP1 0inf (wf_side_intro ([1]*>0inf) _ _)) as HP1.
  destruct HP1 as [r' HP1].
  destruct r'.
  eexists _,_.
  split.
  - eapply evstep_trans.
    2: apply HP1.
    rewrite lpow_all0.
    2: solve_const0_eq.
    cbn.
    solve_init.
  - split.
    1: solve_sigma_score; eassumption.
    lia.
  Unshelve.
  2: solve_sigma_score_side.
Qed.

End TM23.


Module TM24. (* TC *)
Definition tm := Eval compute in (TM_from_str "1RB1RF_0RC0RB_0LD0LF_0LE---_1LA1LD_1LF1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [] *> r) (at level 30).

Definition R b c r := [1]^^(6+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  exists r',
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1] <* [0]^^(b) <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([0]*>r).
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0] <| R b c r -->*
  l <| R 0 (6+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* [0]^^5 <* <[1] <| R b c r -->*
  l <| R 0 (5+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv' l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0;0;1] <| R b c r -->+
  l <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^(7+b)*>[0]*>[1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n c :=
  forall l r,
  exists r',
  l <* [0]^^n <| R 0 0 r -->*
  l <| R 0 c r'.

Lemma P1_S0 n c n' c' v1:
  c*3=n'+v1*2 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+5).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv0 _ _ _ _) as [r4 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2)) by lia.
  rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv0a.
  finish.
Qed.


Lemma P1_S1 n c n' c' v1:
  c*3=n'+v1*2+1 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+6).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv1 _ _ _ _) as [r4 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2+1)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv1a.
  finish.
Qed.

Lemma P1_S' n c n' c':
  c=690 ->
  n'=910 ->
  c'=578 ->
  P1 n c ->
  P1 n' c' ->
  forall r,
  exists r',
  0inf <| R 0 0 r -->+
  0inf <| R 0 0 r'.
Proof.
  unfold P1.
  intros Hc Hn' Hc' HP1 HP1' r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (ROv _ _ _) as [r5 ROvb].
  epose proof (HP1' _ _) as [r6 HP1c].
  epose proof (LOv' _ _ _ _) as [r7 LOv'a].
  eexists.
  rewrite <-(lpow_all0 [0] (n+c*2+2+5)).
  2: solve_const0_eq.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(c'*2)+2+2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  follow Incs'.
  follow ROvb.
  replace (c'*3+0) with (n'+(412*2)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1c.
  replace c' with (412+166) by lia.
  follow Incs.
  follow10 LOv'a.
  simpl_lpow_all0.
  finish.
Qed.

Definition list_WF ls := Forall (fun '(n,c) => P1 (N.to_nat n) (N.to_nat c)) ls.

Definition list_upd ls :=
(match ls with
| (n,c)::_ =>
  match find (fun '(n',c') => (n' <=? c*3) && ((c*3-n')/2 <=? c'))%bool ls with
  | Some (n',c') =>
    let v1:=(c*3-n')/2 in
    let v2:=(c*3-n') mod 2 in
    (n+c*2+2+5,v1*3+5+v2)::ls
  | None => ls
  end
| _ => ls
end)%N.

Lemma list_upd_spec ls:
  list_WF ls ->
  list_WF (list_upd ls).
Proof.
  unfold list_WF.
  intros Hls.
  destruct ls as [|[n c] ls].
  1: apply Hls.
  unfold list_upd.
  match goal with
  | |- _ _ (match ?x with _ => _ end) =>
    destruct x as [[n' c']|] eqn:E
  end.
  2: apply Hls.
  epose proof (find_some _ _ E) as [HIn Hc].
  apply Forall_cons.
  2: apply Hls.
  rewrite Bool.andb_true_iff in Hc.
  destruct Hc as [Hc0 Hc1].
  rewrite N.leb_le in *.
  remember (c*3-n')%N as v.
  assert (v mod 2 = 0 \/ v mod 2 = 1)%N as Hv by lia.
  rewrite Forall_forall in Hls.
  unshelve epose proof (Hls (n,c) _) as Hnc.
  1: left; reflexivity.
  epose proof (Hls (n',c') HIn) as Hnc'.
  cbn in Hnc,Hnc'.
  destruct Hv as [Hv|Hv]; rewrite Hv in *.
  - applys_eq (P1_S0 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
  - applys_eq (P1_S1 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
Qed.

Definition get_rules T :=
  (Nat.iter T list_upd [(N0,N0)]).

Definition get_rule T :=
  hd (N0,N0) (get_rules T).

Lemma get_rules_spec T:
  list_WF (get_rules T).
Proof.
  induction T.
  1: unfold list_WF; cbn; apply Forall_cons.
  2: apply Forall_nil.
  1: unfold P1; intros; eexists; es.
  cbn.
  apply list_upd_spec,IHT.
Qed.

Lemma get_rule_spec T:
  let '(n,c):=get_rule T in
  P1 (N.to_nat n) (N.to_nat c).
Proof.
  unfold get_rule,hd.
  destruct (get_rules T) as [|[n c] ls] eqn:E.
  1: unfold P1; intros; eexists; es.
  pose proof (get_rules_spec T) as HT.
  unfold list_WF in HT.
  rewrite Forall_forall in HT.
  apply (HT (n,c)).
  rewrite E.
  left; reflexivity.
Qed.

Lemma init:
  exists r,
  c0 -->* 0inf <| R 0 0 r.
Proof.
  unfold R,to_side.
  exside ([1;1]*>0inf).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  eapply progress_nonhalt_simple with (C:=fun r => 0inf <| R 0 0 r).
  eapply P1_S'.
  1,2,3: reflexivity.
  - pose proof (get_rule_spec 100) as H.
    replace (get_rule 100) with (1176451%N, 690%N) in H by (vm_compute; reflexivity).
    apply H.
  - apply (get_rule_spec 6).
Qed.

End TM24.


Module TM25. (* TC *)
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0RB_0LD0LF_0LE---_1LA1LD_1LF1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{E}} [] *> r) (at level 30).

Definition R b c r := [1]^^(6+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  exists r',
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1] <* [0]^^(b) <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([0]*>r).
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0] <| R b c r -->*
  l <| R 0 (6+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* [0]^^5 <* <[1] <| R b c r -->*
  l <| R 0 (5+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv' l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0;0;1] <| R b c r -->+
  l <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^(7+b)*>[0]*>[1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n c :=
  forall l r,
  exists r',
  l <* [0]^^n <| R 0 0 r -->*
  l <| R 0 c r'.

Lemma P1_S0 n c n' c' v1:
  c*3=n'+v1*2 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+5).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv0 _ _ _ _) as [r4 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2)) by lia.
  rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv0a.
  finish.
Qed.


Lemma P1_S1 n c n' c' v1:
  c*3=n'+v1*2+1 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+6).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv1 _ _ _ _) as [r4 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2+1)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv1a.
  finish.
Qed.

Lemma P1_S' n c n' c':
  c=690 ->
  n'=910 ->
  c'=578 ->
  P1 n c ->
  P1 n' c' ->
  forall r,
  exists r',
  0inf <| R 0 0 r -->+
  0inf <| R 0 0 r'.
Proof.
  unfold P1.
  intros Hc Hn' Hc' HP1 HP1' r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (ROv _ _ _) as [r5 ROvb].
  epose proof (HP1' _ _) as [r6 HP1c].
  epose proof (LOv' _ _ _ _) as [r7 LOv'a].
  eexists.
  rewrite <-(lpow_all0 [0] (n+c*2+2+5)).
  2: solve_const0_eq.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(c'*2)+2+2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  follow Incs'.
  follow ROvb.
  replace (c'*3+0) with (n'+(412*2)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1c.
  replace c' with (412+166) by lia.
  follow Incs.
  follow10 LOv'a.
  simpl_lpow_all0.
  finish.
Qed.

Definition list_WF ls := Forall (fun '(n,c) => P1 (N.to_nat n) (N.to_nat c)) ls.

Definition list_upd ls :=
(match ls with
| (n,c)::_ =>
  match find (fun '(n',c') => (n' <=? c*3) && ((c*3-n')/2 <=? c'))%bool ls with
  | Some (n',c') =>
    let v1:=(c*3-n')/2 in
    let v2:=(c*3-n') mod 2 in
    (n+c*2+2+5,v1*3+5+v2)::ls
  | None => ls
  end
| _ => ls
end)%N.

Lemma list_upd_spec ls:
  list_WF ls ->
  list_WF (list_upd ls).
Proof.
  unfold list_WF.
  intros Hls.
  destruct ls as [|[n c] ls].
  1: apply Hls.
  unfold list_upd.
  match goal with
  | |- _ _ (match ?x with _ => _ end) =>
    destruct x as [[n' c']|] eqn:E
  end.
  2: apply Hls.
  epose proof (find_some _ _ E) as [HIn Hc].
  apply Forall_cons.
  2: apply Hls.
  rewrite Bool.andb_true_iff in Hc.
  destruct Hc as [Hc0 Hc1].
  rewrite N.leb_le in *.
  remember (c*3-n')%N as v.
  assert (v mod 2 = 0 \/ v mod 2 = 1)%N as Hv by lia.
  rewrite Forall_forall in Hls.
  unshelve epose proof (Hls (n,c) _) as Hnc.
  1: left; reflexivity.
  epose proof (Hls (n',c') HIn) as Hnc'.
  cbn in Hnc,Hnc'.
  destruct Hv as [Hv|Hv]; rewrite Hv in *.
  - applys_eq (P1_S0 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
  - applys_eq (P1_S1 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
Qed.

Definition get_rules T :=
  (Nat.iter T list_upd [(N0,N0)]).

Definition get_rule T :=
  hd (N0,N0) (get_rules T).

Lemma get_rules_spec T:
  list_WF (get_rules T).
Proof.
  induction T.
  1: unfold list_WF; cbn; apply Forall_cons.
  2: apply Forall_nil.
  1: unfold P1; intros; eexists; es.
  cbn.
  apply list_upd_spec,IHT.
Qed.

Lemma get_rule_spec T:
  let '(n,c):=get_rule T in
  P1 (N.to_nat n) (N.to_nat c).
Proof.
  unfold get_rule,hd.
  destruct (get_rules T) as [|[n c] ls] eqn:E.
  1: unfold P1; intros; eexists; es.
  pose proof (get_rules_spec T) as HT.
  unfold list_WF in HT.
  rewrite Forall_forall in HT.
  apply (HT (n,c)).
  rewrite E.
  left; reflexivity.
Qed.

Lemma init:
  exists r,
  c0 -->* 0inf <| R 0 0 r.
Proof.
  unfold R,to_side.
  exside ([1;1]*>0inf).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  eapply progress_nonhalt_simple with (C:=fun r => 0inf <| R 0 0 r).
  eapply P1_S'.
  1,2,3: reflexivity.
  - pose proof (get_rule_spec 100) as H.
    replace (get_rule 100) with (1176451%N, 690%N) in H by (vm_compute; reflexivity).
    apply H.
  - apply (get_rule_spec 6).
Qed.

End TM25.


Module TM26. (* TC *)
Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC1RF_0RD0RC_0LE0LF_0LA---_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(6+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  exists r',
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1] <* [0]^^(b) <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([0]*>r).
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0] <| R b c r -->*
  l <| R 0 (6+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* [0]^^5 <* <[1] <| R b c r -->*
  l <| R 0 (5+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv' l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0;0;1] <| R b c r -->+
  l <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^(7+b)*>[0]*>[1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n c :=
  forall l r,
  exists r',
  l <* [0]^^n <| R 0 0 r -->*
  l <| R 0 c r'.

Lemma P1_S0 n c n' c' v1:
  c*3=n'+v1*2 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+5).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv0 _ _ _ _) as [r4 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2)) by lia.
  rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv0a.
  finish.
Qed.


Lemma P1_S1 n c n' c' v1:
  c*3=n'+v1*2+1 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+6).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv1 _ _ _ _) as [r4 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2+1)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv1a.
  finish.
Qed.

Lemma P1_S' n c n' c':
  c=690 ->
  n'=910 ->
  c'=578 ->
  P1 n c ->
  P1 n' c' ->
  forall r,
  exists r',
  0inf <| R 0 0 r -->+
  0inf <| R 0 0 r'.
Proof.
  unfold P1.
  intros Hc Hn' Hc' HP1 HP1' r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (ROv _ _ _) as [r5 ROvb].
  epose proof (HP1' _ _) as [r6 HP1c].
  epose proof (LOv' _ _ _ _) as [r7 LOv'a].
  eexists.
  rewrite <-(lpow_all0 [0] (n+c*2+2+5)).
  2: solve_const0_eq.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(c'*2)+2+2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  follow Incs'.
  follow ROvb.
  replace (c'*3+0) with (n'+(412*2)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1c.
  replace c' with (412+166) by lia.
  follow Incs.
  follow10 LOv'a.
  simpl_lpow_all0.
  finish.
Qed.

Definition list_WF ls := Forall (fun '(n,c) => P1 (N.to_nat n) (N.to_nat c)) ls.

Definition list_upd ls :=
(match ls with
| (n,c)::_ =>
  match find (fun '(n',c') => (n' <=? c*3) && ((c*3-n')/2 <=? c'))%bool ls with
  | Some (n',c') =>
    let v1:=(c*3-n')/2 in
    let v2:=(c*3-n') mod 2 in
    (n+c*2+2+5,v1*3+5+v2)::ls
  | None => ls
  end
| _ => ls
end)%N.

Lemma list_upd_spec ls:
  list_WF ls ->
  list_WF (list_upd ls).
Proof.
  unfold list_WF.
  intros Hls.
  destruct ls as [|[n c] ls].
  1: apply Hls.
  unfold list_upd.
  match goal with
  | |- _ _ (match ?x with _ => _ end) =>
    destruct x as [[n' c']|] eqn:E
  end.
  2: apply Hls.
  epose proof (find_some _ _ E) as [HIn Hc].
  apply Forall_cons.
  2: apply Hls.
  rewrite Bool.andb_true_iff in Hc.
  destruct Hc as [Hc0 Hc1].
  rewrite N.leb_le in *.
  remember (c*3-n')%N as v.
  assert (v mod 2 = 0 \/ v mod 2 = 1)%N as Hv by lia.
  rewrite Forall_forall in Hls.
  unshelve epose proof (Hls (n,c) _) as Hnc.
  1: left; reflexivity.
  epose proof (Hls (n',c') HIn) as Hnc'.
  cbn in Hnc,Hnc'.
  destruct Hv as [Hv|Hv]; rewrite Hv in *.
  - applys_eq (P1_S0 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
  - applys_eq (P1_S1 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
Qed.

Definition get_rules T :=
  (Nat.iter T list_upd [(N0,N0)]).

Definition get_rule T :=
  hd (N0,N0) (get_rules T).

Lemma get_rules_spec T:
  list_WF (get_rules T).
Proof.
  induction T.
  1: unfold list_WF; cbn; apply Forall_cons.
  2: apply Forall_nil.
  1: unfold P1; intros; eexists; es.
  cbn.
  apply list_upd_spec,IHT.
Qed.

Lemma get_rule_spec T:
  let '(n,c):=get_rule T in
  P1 (N.to_nat n) (N.to_nat c).
Proof.
  unfold get_rule,hd.
  destruct (get_rules T) as [|[n c] ls] eqn:E.
  1: unfold P1; intros; eexists; es.
  pose proof (get_rules_spec T) as HT.
  unfold list_WF in HT.
  rewrite Forall_forall in HT.
  apply (HT (n,c)).
  rewrite E.
  left; reflexivity.
Qed.

Lemma init:
  exists r,
  c0 -->* 0inf <| R 0 0 r.
Proof.
  unfold R,to_side.
  exside ([]*>0inf).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  eapply progress_nonhalt_simple with (C:=fun r => 0inf <| R 0 0 r).
  eapply P1_S'.
  1,2,3: reflexivity.
  - pose proof (get_rule_spec 100) as H.
    replace (get_rule 100) with (1176451%N, 690%N) in H by (vm_compute; reflexivity).
    apply H.
  - apply (get_rule_spec 6).
Qed.

End TM26.


Module TM27. (* TC *)
Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC1LE_0RD0RC_0LE0LF_0LA---_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Definition R b c r := [1]^^(6+b) *> [0] *> [1]^^c *> [0] *> to_side r.

Lemma Inc l r a b c:
  l <* [0]^^(2+a) <| R b (1+c) r -->*
  l <* [0]^^(a) <| R (3+b) c r.
Proof.
  unfold R.
  es.
Qed.

Lemma Incs' l r n b:
  l <* [0]^^(n*2) <| R b n r -->*
  l <| R (n*3+b) 0 r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma Incs l r n b c:
  l <* [0]^^(n*2) <| R b (n+c) r -->*
  l <| R (n*3+b) c r.
Proof.
  gen b.
  ind n Inc.
Qed.

Lemma ROv l r b:
  exists r',
  l <* <[0;0] <| R (b) 0 r -->*
  l <* <[1] <* [0]^^(b) <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([0]*>r).
  es.
Qed.

Lemma LOv1 l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0] <| R b c r -->*
  l <| R 0 (6+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv0 l r b c:
  exists r',
  l <* [0]^^5 <* <[1] <| R b c r -->*
  l <| R 0 (5+b) r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^c*>[0]*>r).
  es.
Qed.

Lemma LOv' l r b c:
  exists r',
  l <* [0]^^5 <* <[1;0;0;1] <| R b c r -->+
  l <| R 0 0 r'.
Proof.
  unfold R.
  destruct r.
  exside ([1]^^(7+b)*>[0]*>[1]^^c*>[0]*>r).
  es.
Qed.

Definition P1 n c :=
  forall l r,
  exists r',
  l <* [0]^^n <| R 0 0 r -->*
  l <| R 0 c r'.

Lemma P1_S0 n c n' c' v1:
  c*3=n'+v1*2 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+5).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv0 _ _ _ _) as [r4 LOv0a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2)) by lia.
  rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv0a.
  finish.
Qed.


Lemma P1_S1 n c n' c' v1:
  c*3=n'+v1*2+1 ->
  v1<=c' ->
  P1 n c ->
  P1 n' c' ->
  P1 (n+c*2+2+5) (v1*3+6).
Proof.
  unfold P1.
  intros Hn Hc HP1 HP1' l r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (LOv1 _ _ _ _) as [r4 LOv1a].
  eexists.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(v1*2+1)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  replace c' with (v1+(c'-v1)) by lia.
  follow Incs.
  follow LOv1a.
  finish.
Qed.

Lemma P1_S' n c n' c':
  c=690 ->
  n'=910 ->
  c'=578 ->
  P1 n c ->
  P1 n' c' ->
  forall r,
  exists r',
  0inf <| R 0 0 r -->+
  0inf <| R 0 0 r'.
Proof.
  unfold P1.
  intros Hc Hn' Hc' HP1 HP1' r.
  epose proof (HP1 _ _) as [r1 HP1a].
  epose proof (ROv _ _ _) as [r2 ROva].
  epose proof (HP1' _ _) as [r3 HP1b].
  epose proof (ROv _ _ _) as [r5 ROvb].
  epose proof (HP1' _ _) as [r6 HP1c].
  epose proof (LOv' _ _ _ _) as [r7 LOv'a].
  eexists.
  rewrite <-(lpow_all0 [0] (n+c*2+2+5)).
  2: solve_const0_eq.
  repeat rewrite <-lpow_add'.
  follow HP1a.
  follow Incs'.
  follow ROva.
  replace (c*3+0) with (n'+(c'*2)+2+2) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1b.
  follow Incs'.
  follow ROvb.
  replace (c'*3+0) with (n'+(412*2)) by lia.
  repeat rewrite <-lpow_add'.
  follow HP1c.
  replace c' with (412+166) by lia.
  follow Incs.
  follow10 LOv'a.
  simpl_lpow_all0.
  finish.
Qed.

Definition list_WF ls := Forall (fun '(n,c) => P1 (N.to_nat n) (N.to_nat c)) ls.

Definition list_upd ls :=
(match ls with
| (n,c)::_ =>
  match find (fun '(n',c') => (n' <=? c*3) && ((c*3-n')/2 <=? c'))%bool ls with
  | Some (n',c') =>
    let v1:=(c*3-n')/2 in
    let v2:=(c*3-n') mod 2 in
    (n+c*2+2+5,v1*3+5+v2)::ls
  | None => ls
  end
| _ => ls
end)%N.

Lemma list_upd_spec ls:
  list_WF ls ->
  list_WF (list_upd ls).
Proof.
  unfold list_WF.
  intros Hls.
  destruct ls as [|[n c] ls].
  1: apply Hls.
  unfold list_upd.
  match goal with
  | |- _ _ (match ?x with _ => _ end) =>
    destruct x as [[n' c']|] eqn:E
  end.
  2: apply Hls.
  epose proof (find_some _ _ E) as [HIn Hc].
  apply Forall_cons.
  2: apply Hls.
  rewrite Bool.andb_true_iff in Hc.
  destruct Hc as [Hc0 Hc1].
  rewrite N.leb_le in *.
  remember (c*3-n')%N as v.
  assert (v mod 2 = 0 \/ v mod 2 = 1)%N as Hv by lia.
  rewrite Forall_forall in Hls.
  unshelve epose proof (Hls (n,c) _) as Hnc.
  1: left; reflexivity.
  epose proof (Hls (n',c') HIn) as Hnc'.
  cbn in Hnc,Hnc'.
  destruct Hv as [Hv|Hv]; rewrite Hv in *.
  - applys_eq (P1_S0 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
  - applys_eq (P1_S1 (N.to_nat n) (N.to_nat c) (N.to_nat n') (N.to_nat c') (N.to_nat (v/2))).
    all: try assumption.
    all: try lia.
Qed.

Definition get_rules T :=
  (Nat.iter T list_upd [(N0,N0)]).

Definition get_rule T :=
  hd (N0,N0) (get_rules T).

Lemma get_rules_spec T:
  list_WF (get_rules T).
Proof.
  induction T.
  1: unfold list_WF; cbn; apply Forall_cons.
  2: apply Forall_nil.
  1: unfold P1; intros; eexists; es.
  cbn.
  apply list_upd_spec,IHT.
Qed.

Lemma get_rule_spec T:
  let '(n,c):=get_rule T in
  P1 (N.to_nat n) (N.to_nat c).
Proof.
  unfold get_rule,hd.
  destruct (get_rules T) as [|[n c] ls] eqn:E.
  1: unfold P1; intros; eexists; es.
  pose proof (get_rules_spec T) as HT.
  unfold list_WF in HT.
  rewrite Forall_forall in HT.
  apply (HT (n,c)).
  rewrite E.
  left; reflexivity.
Qed.

Lemma init:
  exists r,
  c0 -->* 0inf <| R 0 0 r.
Proof.
  unfold R,to_side.
  exside ([]*>0inf).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  eapply progress_nonhalt_simple with (C:=fun r => 0inf <| R 0 0 r).
  eapply P1_S'.
  1,2,3: reflexivity.
  - pose proof (get_rule_spec 100) as H.
    replace (get_rule 100) with (1176451%N, 690%N) in H by (vm_compute; reflexivity).
    apply H.
  - apply (get_rule_spec 6).
Qed.

End TM27.

