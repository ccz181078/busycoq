From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import SimplTape.

Open Scope list.

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


Ltac solve_sigma_score' f :=
  eapply sigma_score_unbounded_nonhalt;
  intros n;
  eexists _,_;
  split;
  [ apply (f n) |];
  split;
  [ solve_sigma_score |];
  lia.

Ltac simpl_nat :=
  repeat rewrite Nat.add_succ_r;
  repeat rewrite <-Nat.mul_add_distr_l;
  repeat rewrite <-Nat.mul_succ_r.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LA_0RC0LA_1RD1RB_1RE1RD_1LF1LE_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* <[1;0]^^n {{C}}> [0]^^(3+m*2) *> r -->*
  const 0 <* <[1;0]^^(k1+n) <* [1]^^k2 {{D}}> r.

Lemma P0_S m k1:
  P0 m k1 (3+m*2) ->
  P0 (S m) (1+k1+k1) (2+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (3+m*2) ->
  P0 (2+m) (1+3*k1') (3+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (1+n*2) k1 (3+(1+n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 1%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* <[1;0]^^n <* [1]^^(3+(1+m*2)*2) {{D}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (2,O)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LB_---0LD_0RE0LF_1RA1RD_1LD0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* <[1;0]^^n {{E}}> [0]^^(3+m*2) *> r -->*
  const 0 <* <[1;0]^^(k1+n) <* [1]^^k2 {{A}}> r.

Lemma P0_S m k1:
  P0 m k1 (3+m*2) ->
  P0 (S m) (1+k1+k1) (2+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (3+m*2) ->
  P0 (2+m) (1+3*k1') (3+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (1+n*2) k1 (3+(1+n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 1%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* <[1;0]^^n <* [1]^^(3+(1+m*2)*2) {{A}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1RB_1LD1LC_---0LE_0RA0LF_1LE0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* <[1;0]^^n {{A}}> [0]^^(3+m*2) *> r -->*
  const 0 <* <[1;0]^^(k1+n) <* [1]^^k2 {{B}}> r.

Lemma P0_S m k1:
  P0 m k1 (3+m*2) ->
  P0 (S m) (1+k1+k1) (2+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (3+m*2) ->
  P0 (2+m) (1+3*k1') (3+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (1+n*2) k1 (3+(1+n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 1%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* <[1;0]^^n <* [1]^^(3+(1+m*2)*2) {{B}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1,0)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LB_0LD0LC_0RE0RA_1RE1LF_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* [1]^^(1+n) {{A}}> [0]^^(2+m*2) *> r -->*
  const 0 <* [1]^^(1+k1+n) <* [0] <* [1]^^k2 {{A}}> r.

Lemma P0_S m k1:
  P0 m k1 (2+m*2) ->
  P0 (S m) (1+k1+k1) (1+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (2+m*2) ->
  P0 (2+m) (1+3*k1') (2+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (n*2) k1 (2+(n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 0%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* [1]^^(1+n) <* [0] <* [1]^^(2+(m*2)*2) {{A}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1,0)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RE_0RD0RC_1LD1LA_1RF0LA_---1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[1;1;0;1]^^a <* [0] <* [1;1]^^b {{E}}> [1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a (1+b) (2+c) r -->*
  S1 l (1+a) b c r.
Proof.
  es.
Qed.

Lemma Incs1 l a b c r:
  S1 l a b (b*2+c) r -->*
  S1 l (b+a) 0 c r.
Proof.
  gen l a c r.
  ind b Inc1.
Qed.

Lemma LInc l a r:
  l <* [0] <* [1;1]^^(2+a) <{{A}} [1]^^(a*2+1) *> r -->*
  l <* <[1;1;0;1]^^(1+a) <* [1;1] {{C}}> r.
Proof.
  mid (S1 (l<*<[1;1;0;1]) 0 a (a*2+1) r).
  1: es.
  follow Incs1.
  unfold S1.
  es.
Qed.

Definition P a b' :=
  forall l n,
  l <* <[1;1;0;1]^^a <* [1;1] {{C}}> [1]^^n *> 0inf -->*
  l <* [1]^^(a*2+1) <{{A}} [1]^^(b'+n) *> 0inf.

Lemma P_S a b':
  a*2+1<=b' ->
  P (a+1) b' ->
  P (a+1+1) (b'*2-(a*2+1)).
Proof.
  unfold P.
  intros Hb HP l n.
  rewrite (lpow_add _ (a+1) 1),Str_app_assoc.
  follow HP.
  replace b' with (a*2+1+(b'-(a*2+1))) by lia.
  mid (l<*[1;1]<*[0]<*[1;1]^^(2+a)<{{A}} [1]^^(a*2+1)*>[1]^^(b'-(a*2+1)+n)*>0inf).
  1: es.
  follow LInc.
  rewrite (Nat.add_comm 1 a).
  follow HP.
  replace (a*2+1+(b'-(a*2+1))) with b' by lia.
  replace (b'+(b'-(a*2+1)+n)) with (b'*2-(a*2+1)+n) by lia.
  es.
Qed.

Definition S0 a b :=
  0inf <* <[1;1;0;1]^^a <* [1;1] {{C}}> [1]^^b *> 0inf.

Lemma BigStep a b' n:
  (2+a)*2+1<=b' ->
  P (a+1) b' ->
  S0 (a+1) n -->+
  S0 (a+1+1) (b'-((2+a)*2+1)+n).
Proof.
  unfold P,S0.
  intros Hb HP.
  follow HP.
  remember ((2+a)*2+1) as v1.
  replace b' with (v1+(b'-(v1))) by lia.
  es; er.
  mid (S1 0inf 0 (2+a) v1 ([1]^^(b'-v1+n)*>0inf)).
  1: es.
  subst v1.
  follow Incs1.
  remember ((2+a)*2+1) as v1.
  replace (v1+(b'-(v1))) with b' by lia.
  unfold S1.
  es.
Qed.

Definition S '(a,n) := S0 (a+1) n.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (1,2)%nat).
  1: unfold S,S0; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(a,n) => exists b', a*2+5<=b' /\ P (a+1) b').
  2: exists 13; split; try lia.
  2: unfold P; es.
  intros [a n] [b' [Hb HP]].
  eexists (a+1,_).
  split.
  - unfold S.
    apply BigStep.
    2: apply HP.
    lia.
  - unshelve epose proof (P_S _ _ _ HP) as HP'.
    1: lia.
    eexists; split.
    2: apply HP'.
    lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC0RB_1LC1LD_1RA1LE_1RF0LD_---1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c r :=
  l <* <[1;1;0;1]^^a <* [0] <* [1;1]^^b {{E}}> [1]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a (1+b) (2+c) r -->*
  S1 l (1+a) b c r.
Proof.
  es.
Qed.

Lemma Incs1 l a b c r:
  S1 l a b (b*2+c) r -->*
  S1 l (b+a) 0 c r.
Proof.
  gen l a c r.
  ind b Inc1.
Qed.

Lemma LInc l a r:
  l <* [0] <* [1;1]^^(2+a) <{{D}} [1]^^(a*2+1) *> r -->*
  l <* <[1;1;0;1]^^(1+a) <* [1;1] {{B}}> r.
Proof.
  mid (S1 (l<*<[1;1;0;1]) 0 a (a*2+1) r).
  1: es.
  follow Incs1.
  unfold S1.
  es.
Qed.

Definition P a b' :=
  forall l n,
  l <* <[1;1;0;1]^^a <* [1;1] {{B}}> [1]^^n *> 0inf -->*
  l <* [1]^^(a*2+1) <{{D}} [1]^^(b'+n) *> 0inf.

Lemma P_S a b':
  a*2+1<=b' ->
  P (a+1) b' ->
  P (a+1+1) (b'*2-(a*2+1)).
Proof.
  unfold P.
  intros Hb HP l n.
  rewrite (lpow_add _ (a+1) 1),Str_app_assoc.
  follow HP.
  replace b' with (a*2+1+(b'-(a*2+1))) by lia.
  mid (l<*[1;1]<*[0]<*[1;1]^^(2+a)<{{D}} [1]^^(a*2+1)*>[1]^^(b'-(a*2+1)+n)*>0inf).
  1: es.
  follow LInc.
  rewrite (Nat.add_comm 1 a).
  follow HP.
  replace (a*2+1+(b'-(a*2+1))) with b' by lia.
  replace (b'+(b'-(a*2+1)+n)) with (b'*2-(a*2+1)+n) by lia.
  es.
Qed.

Definition S0 a b :=
  0inf <* <[1;1;0;1]^^a <* [1;1] {{B}}> [1]^^b *> 0inf.

Lemma BigStep a b' n:
  (2+a)*2+1<=b' ->
  P (a+1) b' ->
  S0 (a+1) n -->+
  S0 (a+1+1) (b'-((2+a)*2+1)+n).
Proof.
  unfold P,S0.
  intros Hb HP.
  follow HP.
  remember ((2+a)*2+1) as v1.
  replace b' with (v1+(b'-(v1))) by lia.
  es; er.
  mid (S1 0inf 0 (2+a) v1 ([1]^^(b'-v1+n)*>0inf)).
  1: es.
  subst v1.
  follow Incs1.
  remember ((2+a)*2+1) as v1.
  replace (v1+(b'-(v1))) with b' by lia.
  unfold S1.
  es.
Qed.

Definition S '(a,n) := S0 (a+1) n.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (1,7)%nat).
  1: unfold S,S0; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(a,n) => exists b', a*2+5<=b' /\ P (a+1) b').
  2: exists 13; split; try lia.
  2: unfold P; es.
  intros [a n] [b' [Hb HP]].
  eexists (a+1,_).
  split.
  - unfold S.
    apply BigStep.
    2: apply HP.
    lia.
  - unshelve epose proof (P_S _ _ _ HP) as HP'.
    1: lia.
    eexists; split.
    2: apply HP'.
    lia.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RF_0RD0RE_1LE0RB_0LA1RE_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c :=
  l <* <[1;1;1;1;0;0;1]^^a <* <[0;0] <* [1]^^b {{E}}> [0;0;1]^^c *> 0inf.

Lemma Inc1 l a b c:
  S1 l a (4+b) (1+c) -->*
  S1 l (1+a) b c.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c:
  S1 l a (n*4+b) (n+c) -->*
  S1 l (n+a) b c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 l a b c :=
  l <* <[1;1;1;1;0;0;1]^^a <* [1]^^b {{E}}> [0;0;1]^^c *> 0inf.

Lemma Inc l n c:
  S1 l 0 ((1+n)*4+0) ((1+n)+c) -->*
  S2 l n 3 (5+c).
Proof.
  follow Incs1.
  es.
Qed.

Lemma Ov n c:
  S1 0inf 0 ((2+n)*4+3) ((2+n)+(2+c)) -->+
  S2 0inf (2+n) 11 (6+c).
Proof.
  follow Incs1.
  es.
Qed.

Definition P' n c2 :=
  forall l k c,
  S2 l (n+k) 11 (6+c) -->*
  S2 l k ((2+n)*4+3) (c2+c).

Lemma P'_S n c2:
  P' n (4+n+c2) ->
  P' (1+n) (15+n+c2+c2).
Proof.
  unfold P'; intros.
  epose proof (H _ (1+k) _) as I1.
  follow I1. clear I1.
  mid (S1 (l <* <[1;1;1;1;0;0;1]^^k <* [1]^^4) 0 ((1+(2+n))*4+0) ((1+(2+n))+(1+c2+c))).
  1: es.
  follow Inc.
  mid (S2 ([1] ^^ 4 *> [1; 0; 0; 1; 1; 1; 1] ^^ k *> l) (n) 11 (17 + (c2 + c))).
  1: es.
  epose proof (H _ O (11+c2+c)) as I1.
  follow I1. clear I1.
  es.
Qed.

Definition S' '(n,c) := S2 0inf n 11 (6+c).

Lemma BigStep n c c2:
  P' n (4+n+c2) ->
  S' (n,c) -->+
  S' (2+n,c2+c).
Proof.
  unfold P',S'.
  intros HP.
  epose proof (HP _ O _) as I1.
  follow I1. clear I1.
  mid01 (S1 0inf 0 ((2+n)*4+3) ((2+n)+(2+(c2+c)))).
  1: es.
  follow10 Ov.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S'(O,2)).
  1: unfold S',S2; esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,c) => exists c2, P' n (4+n+c2)).
  2: exists 2; unfold P'; es.
  intros [n c] [c2 HP].
  epose proof (P'_S _ _ HP) as HP1.
  replace (15+n+c2+c2) with (4+(1+n)+(10+c2*2)) in HP1 by lia.
  epose proof (P'_S _ _ HP1) as HP2.
  eexists (_,_); split.
  1: apply BigStep,HP.
  exists (30+c2*4).
  applys_eq HP2; lia.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC1RB_1RD0LA_1RE1RF_0RA0RB_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c :=
  l <* <[1;1;1;1;0;0;1]^^a <* <[0;0] <* [1]^^b {{B}}> [0;0;1]^^c *> 0inf.

Lemma Inc1 l a b c:
  S1 l a (4+b) (1+c) -->*
  S1 l (1+a) b c.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c:
  S1 l a (n*4+b) (n+c) -->*
  S1 l (n+a) b c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 l a b c :=
  l <* <[1;1;1;1;0;0;1]^^a <* [1]^^b {{B}}> [0;0;1]^^c *> 0inf.

Lemma Inc l n c:
  S1 l 0 ((1+n)*4+0) ((1+n)+c) -->*
  S2 l n 3 (5+c).
Proof.
  follow Incs1.
  es.
Qed.

Lemma Ov n c:
  S1 0inf 0 ((2+n)*4+3) ((2+n)+(2+c)) -->+
  S2 0inf (2+n) 11 (6+c).
Proof.
  follow Incs1.
  es.
Qed.

Definition P' n c2 :=
  forall l k c,
  S2 l (n+k) 11 (6+c) -->*
  S2 l k ((2+n)*4+3) (c2+c).

Lemma P'_S n c2:
  P' n (4+n+c2) ->
  P' (1+n) (15+n+c2+c2).
Proof.
  unfold P'; intros.
  epose proof (H _ (1+k) _) as I1.
  follow I1. clear I1.
  mid (S1 (l <* <[1;1;1;1;0;0;1]^^k <* [1]^^4) 0 ((1+(2+n))*4+0) ((1+(2+n))+(1+c2+c))).
  1: es.
  follow Inc.
  mid (S2 ([1] ^^ 4 *> [1; 0; 0; 1; 1; 1; 1] ^^ k *> l) (n) 11 (17 + (c2 + c))).
  1: es.
  epose proof (H _ O (11+c2+c)) as I1.
  follow I1. clear I1.
  es.
Qed.

Definition S' '(n,c) := S2 0inf n 11 (6+c).

Lemma BigStep n c c2:
  P' n (4+n+c2) ->
  S' (n,c) -->+
  S' (2+n,c2+c).
Proof.
  unfold P',S'.
  intros HP.
  epose proof (HP _ O _) as I1.
  follow I1. clear I1.
  mid01 (S1 0inf 0 ((2+n)*4+3) ((2+n)+(2+(c2+c)))).
  1: es.
  follow10 Ov.
  finish.
Qed.

Lemma P'_O: P' 0 6.
Proof.
  unfold P'. es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S'(2,2)).
  1: unfold S',S2; esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,c) => exists c2, P' n (4+n+c2)).
  2: eexists; eapply (P'_S _ _ (P'_S _ _ P'_O)).
  intros [n c] [c2 HP].
  epose proof (P'_S _ _ HP) as HP1.
  replace (15+n+c2+c2) with (4+(1+n)+(10+c2*2)) in HP1 by lia.
  epose proof (P'_S _ _ HP1) as HP2.
  eexists (_,_); split.
  1: apply BigStep,HP.
  exists (30+c2*4).
  applys_eq HP2; lia.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0RC0RD_1LD0RA_0LE1RD_1RA0LC_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c :=
  l <* <[1;1;1;1;0;0;1]^^a <* <[0;0] <* [1]^^b {{D}}> [0;0;1]^^c *> 0inf.

Lemma Inc1 l a b c:
  S1 l a (4+b) (1+c) -->*
  S1 l (1+a) b c.
Proof.
  es.
Qed.

Lemma Incs1 n l a b c:
  S1 l a (n*4+b) (n+c) -->*
  S1 l (n+a) b c.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Definition S2 l a b c :=
  l <* <[1;1;1;1;0;0;1]^^a <* [1]^^b {{D}}> [0;0;1]^^c *> 0inf.

Lemma Inc l n c:
  S1 l 0 ((1+n)*4+0) ((1+n)+c) -->*
  S2 l n 3 (5+c).
Proof.
  follow Incs1.
  es.
Qed.

Lemma Ov n c:
  S1 0inf 0 ((2+n)*4+3) ((2+n)+(2+c)) -->+
  S2 0inf (2+n) 11 (6+c).
Proof.
  follow Incs1.
  es.
Qed.

Definition P' n c2 :=
  forall l k c,
  S2 l (n+k) 11 (6+c) -->*
  S2 l k ((2+n)*4+3) (c2+c).

Lemma P'_S n c2:
  P' n (4+n+c2) ->
  P' (1+n) (15+n+c2+c2).
Proof.
  unfold P'; intros.
  epose proof (H _ (1+k) _) as I1.
  follow I1. clear I1.
  mid (S1 (l <* <[1;1;1;1;0;0;1]^^k <* [1]^^4) 0 ((1+(2+n))*4+0) ((1+(2+n))+(1+c2+c))).
  1: es.
  follow Inc.
  mid (S2 ([1] ^^ 4 *> [1; 0; 0; 1; 1; 1; 1] ^^ k *> l) (n) 11 (17 + (c2 + c))).
  1: es.
  epose proof (H _ O (11+c2+c)) as I1.
  follow I1. clear I1.
  es.
Qed.

Definition S' '(n,c) := S2 0inf n 11 (6+c).

Lemma BigStep n c c2:
  P' n (4+n+c2) ->
  S' (n,c) -->+
  S' (2+n,c2+c).
Proof.
  unfold P',S'.
  intros HP.
  epose proof (HP _ O _) as I1.
  follow I1. clear I1.
  mid01 (S1 0inf 0 ((2+n)*4+3) ((2+n)+(2+(c2+c)))).
  1: es.
  follow10 Ov.
  finish.
Qed.

Lemma P'_O: P' 0 6.
Proof.
  unfold P'. es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S'(0,1)%nat).
  1: unfold S',S2; esx.
  eapply progress_nonhalt_cond with (P:=fun '(n,c) => exists c2, P' n (4+n+c2)).
  2: eexists; eapply P'_O.
  intros [n c] [c2 HP].
  epose proof (P'_S _ _ HP) as HP1.
  replace (15+n+c2+c2) with (4+(1+n)+(10+c2*2)) in HP1 by lia.
  epose proof (P'_S _ _ HP1) as HP2.
  eexists (_,_); split.
  1: apply BigStep,HP.
  exists (30+c2*4).
  applys_eq HP2; lia.
Qed.

End TM9.


