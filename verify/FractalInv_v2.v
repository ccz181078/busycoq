From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Lemma pow2_ge n:
  2^n>=n+1.
Proof.
  induction n; cbn; lia.
Qed.

Ltac follow' H :=
  follow H || (step1; follow' H).



Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RA_0LC1RD_1RA1LD_0RB0LE_0LF0LA_---0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} r) (at level 30).

Definition P1 a b c :=
  forall l r,
  l <* [0]^^a <* [1;1;1] |> [0]^^b *> r -->*
  l <* [0] <* [1]^^c <* [0] |> r.

Definition P2 a b c d e :=
  forall l r,
  l <* [1]^^a |> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [0] <* [1]^^e |> r.

Definition P3 a b c d :=
  forall l r,
  l <* [1]^^a |> [0]^^b *> r -->*
  l <| [0]^^c *> [0;1;0]^^d *> r.

Definition P4 a b c d e :=
  forall l r,
  l <* [1]^^a <* [0] |> [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [1] *> [0]^^d *> [0;1;0]^^e *> r.

Definition P5 a b c d :=
  forall l r,
  l <* [1]^^a <* [0] |> [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [0] |> r.

Lemma P2_S [a b c d a0 c0 d0]:
  P3 a b c (1+d) ->
  P5 a0 (2+c) c0 d0 ->
  P2 (a+3+a0) (b+1) c0 d0 (3+d*3).
Proof.
  unfold P2,P3,P5.
  intros HP3 HP5 l r.
  st.
  follow HP3.
  st.
  simpl_rotate.
  follow' HP5.
  es.
Qed.

Lemma P3_S [a b c d c0 d0]:
  P2 a b c d (3+d) ->
  P3 (1+d) (2+c0) c0 d0 ->
  P3 a (b+2+c0) (c*2+c0) (d0+d0).
Proof.
  unfold P2,P3.
  intros HP2 HP3 l r.
  st.
  follow HP2.
  st.
  do 2 rewrite <-lpow_shift1.
  follow HP3.
  follow' HP3.
  es.
Qed.

Lemma P4_S [a b c d b0 c0 d0]:
  P5 a b (2+c) d ->
  P3 (1+d) b0 c0 d0 ->
  P4 a (b+1+b0) (2+c*2) (2+c0) d0.
Proof.
  unfold P3,P4,P5.
  intros HP5 HP3 l r.
  st.
  follow HP5.
  do 3 step1.
  rewrite <-lpow_shift1.
  follow HP3.
  es.
Qed.

Lemma P5_S [a b c e a0 c0]:
  P4 a b c (1+c) e ->
  P5 a0 (1+c) c0 a0 ->
  P5 (a+3+a0) b (c0+c0) (e*3+a0).
Proof.
  unfold P4,P5.
  intros HP4 HP5 l r.
  st.
  follow HP4.
  follow' HP5.
  follow HP5.
  es.
Qed.

Lemma P1_S [b c b0 d0 a1]:
  P1 (1+a1) b c ->
  P3 c b0 b d0 ->
  P1 (1+a1+1+a1) (b+1+b0) (d0*3+c).
Proof.
  unfold P1,P3.
  intros HP1 HP3 l r.
  st.
  follow HP1.
  er.
  do 2 rewrite <-lpow_shift1.
  follow HP3.
  er.
  follow HP1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (HP1:P1 (2+((2^n-1)*2)) (1+((2^n-1)*4)) (4+(2^n-1)*6))
  (HP2:P2 (4+(2^n-1)*6) (2+(2^n-1)*2) (1+(2^n-1)) ((2^n-1)*3) (3+(2^n-1)*3))
  (HP3:P3 (4+(2^n-1)*6) (3+(2^n-1)*4) (1+(2^n-1)*4) (2+(2^n-1)*2))
  (HP4:P4 (3+(2^n-1)*6) (7+(2^n-1)*8) (2+(2^n-1)*4) (3+(2^n-1)*4) (2+(2^n-1)*2))
  (HP5:P5 (3+(2^n-1)*6) (3+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6)):
  P n.

Lemma P_n n:
  P n.
Proof.
  induction n.
  1: econstructor; unfold P1,P2,P3,P4,P5; es.
  inverts IHn.
  assert (HP2':P2 (10+(2^n-1)*12) (4+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6) (6+(2^n-1)*6)).
  1: applys_eq (P2_S HP3 HP5); lia.
  assert (HP3':P3 (10+(2^n-1)*12) (7+(2^n-1)*8) (5+(2^n-1)*8) (4+(2^n-1)*4)).
  1: applys_eq (P3_S HP2' HP3); lia.
  assert (HP5':P5 (9+(2^n-1)*12) (7+(2^n-1)*8) (4+(2^n-1)*4) (9+(2^n-1)*12)).
  1: applys_eq (P5_S HP4 HP5); lia.
  econstructor; cbn[Nat.pow].
  - applys_eq (P1_S HP1 HP3); lia.
  - applys_eq HP2'; lia.
  - applys_eq HP3'; lia.
  - applys_eq (P4_S HP5' HP3'); lia.
  - applys_eq HP5'; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP1 0inf 0inf) as HP1.
  do 2 rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0RC0LF_1LA1RD_1RE---_1RC0LA_0LB0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{B}} r) (at level 30).

Definition P1 a b c :=
  forall l r,
  l <* [0]^^a <* [1;1;1] |> [0]^^b *> r -->*
  l <* [0] <* [1]^^c <* [1] {{E}}> r.

Definition P2 a b c d e :=
  forall l r,
  l <* [1]^^a <| [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [0] <* [1]^^e |> r.

Definition P3 a b c d :=
  forall l r,
  l <* [1]^^a <| [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [0;1;0]^^d *> r.

Definition P4 a b c d e :=
  forall l r,
  l <* [1]^^a <* [0] |> [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [1] *> [0]^^d *> [0;1;0]^^e *> r.

Definition P5 a b c d :=
  forall l r,
  l <* [1]^^a <* [0] |> [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [1] {{E}}> r.

Lemma P2_S [a b c d a0 c0 d0]:
  P3 a (1+b) c (1+d) ->
  P5 a0 (2+c) c0 d0 ->
  P2 (a+3+a0) (1+b+1) c0 d0 (3+d*3).
Proof.
  unfold P2,P3,P5.
  intros HP3 HP5 l r.
  st.
  follow HP3.
  st.
  simpl_rotate.
  follow' HP5.
  es.
Qed.

Lemma P3_S [a b c d c0 d0]:
  P2 a b c d (3+d) ->
  P3 d (2+c0) c0 d0 ->
  P3 a (b+2+c0) (c*2+c0) (d0+d0).
Proof.
  unfold P2,P3.
  intros HP2 HP3 l r.
  st.
  follow HP2.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  follow' HP3.
  es.
Qed.

Lemma P4_S [a b c d b0 c0 d0]:
  P5 a b (2+c) (1+d) ->
  P3 (1+d) (1+b0) c0 d0 ->
  P4 a (b+2+b0) (2+c*2) (2+c0) d0.
Proof.
  unfold P3,P4,P5.
  intros HP5 HP3 l r.
  st.
  follow HP5.
  st.
  rewrite <-lpow_shift1.
  follow' HP3.
  es.
Qed.

Lemma P5_S [a b c e a0 c0]:
  P4 a b c (1+c) e ->
  P5 a0 (1+c) c0 a0 ->
  P5 (a+3+a0) b (c0+c0) (e*3+a0).
Proof.
  unfold P4,P5.
  intros HP4 HP5 l r.
  st.
  follow HP4.
  follow' HP5.
  follow' HP5.
  es.
Qed.

Lemma P1_S [b c b0 d0 a1]:
  P1 (2+a1) b (1+c) ->
  P3 c (1+b0) b d0 ->
  P1 (2+a1+2+a1) (b+2+b0) (1+d0*3+c).
Proof.
  unfold P1,P3.
  intros HP1 HP3 l r.
  st.
  follow HP1.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  follow' HP1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (HP1:P1 (2+((2^n-1)*2)) (1+((2^n-1)*4)) (4+(2^n-1)*6))
  (HP2:P2 (3+(2^n-1)*6) (2+(2^n-1)*2) (1+(2^n-1)) ((2^n-1)*3) (3+(2^n-1)*3))
  (HP3:P3 (3+(2^n-1)*6) (3+(2^n-1)*4) (1+(2^n-1)*4) (2+(2^n-1)*2))
  (HP4:P4 (3+(2^n-1)*6) (7+(2^n-1)*8) (2+(2^n-1)*4) (3+(2^n-1)*4) (2+(2^n-1)*2))
  (HP5:P5 (3+(2^n-1)*6) (3+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6)):
  P n.

Lemma P_n n:
  P n.
Proof.
  induction n.
  1: econstructor; unfold P1,P2,P3,P4,P5; es.
  inverts IHn.
  assert (HP2':P2 (9+(2^n-1)*12) (4+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6) (6+(2^n-1)*6)).
  1: applys_eq (P2_S HP3 HP5); lia.
  assert (HP3':P3 (9+(2^n-1)*12) (7+(2^n-1)*8) (5+(2^n-1)*8) (4+(2^n-1)*4)).
  1: applys_eq (P3_S HP2' HP3); lia.
  assert (HP5':P5 (9+(2^n-1)*12) (7+(2^n-1)*8) (4+(2^n-1)*4) (9+(2^n-1)*12)).
  1: applys_eq (P5_S HP4 HP5); lia.
  econstructor; cbn[Nat.pow].
  - applys_eq (P1_S HP1 HP3); lia.
  - applys_eq HP2'; lia.
  - applys_eq HP3'; lia.
  - applys_eq (P4_S HP5' HP3'); lia.
  - applys_eq HP5'; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP1 0inf 0inf) as HP1.
  do 2 rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LD_1LD1RA_0LF0LE_0RC0RA_0RB0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} [0] *> r) (at level 30).

Definition P1 a b c :=
  forall l r,
  l <* [0]^^a <* [1;1;1] |> [0]^^b *> r -->*
  l <* [0] <* [1]^^c <* [1;1] {{B}}> r.

Definition P2 a b c d e :=
  forall l r,
  l <* [1]^^a <| [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [0] <* [1]^^e |> r.

Definition P3 a b c d :=
  forall l r,
  l <* [1]^^a <| [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [0;1;0]^^d *> r.

Definition P4 a b c d e :=
  forall l r,
  l <* [1]^^a <* [0] |> [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [1] *> [0]^^d *> [0;1;0]^^e *> r.

Definition P5 a b c d :=
  forall l r,
  l <* [1]^^a <* [0] |> [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [1;1] {{B}}> r.

Lemma P2_S [a b c d a0 c0 d0]:
  P3 a (1+b) c (1+d) ->
  P5 a0 (2+c) c0 d0 ->
  P2 (a+3+a0) (1+b+1) c0 d0 (3+d*3).
Proof.
  unfold P2,P3,P5.
  intros HP3 HP5 l r.
  st.
  follow HP3.
  st.
  simpl_rotate.
  follow' HP5.
  es.
Qed.

Lemma P3_S [a b c d c0 d0]:
  P2 a b c d (3+d) ->
  P3 d (2+c0) c0 d0 ->
  P3 a (b+2+c0) (c*2+c0) (d0+d0).
Proof.
  unfold P2,P3.
  intros HP2 HP3 l r.
  st.
  follow HP2.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  follow' HP3.
  es.
Qed.

Lemma P4_S [a b c d b0 c0 d0]:
  P5 a b (2+c) (1+d) ->
  P3 (1+d) (1+b0) c0 d0 ->
  P4 a (b+2+b0) (2+c*2) (2+c0) d0.
Proof.
  unfold P3,P4,P5.
  intros HP5 HP3 l r.
  st.
  follow HP5.
  st.
  rewrite <-lpow_shift1.
  follow' HP3.
  es.
Qed.

Lemma P5_S [a b c e a0 c0]:
  P4 a b c (1+c) e ->
  P5 a0 (1+c) c0 a0 ->
  P5 (a+3+a0) b (c0+c0) (e*3+a0).
Proof.
  unfold P4,P5.
  intros HP4 HP5 l r.
  st.
  follow HP4.
  follow' HP5.
  follow' HP5.
  es.
Qed.

Lemma P1_S [b c b0 d0 a1]:
  P1 (2+a1) b (1+c) ->
  P3 c (1+b0) b d0 ->
  P1 (2+a1+2+a1) (b+2+b0) (1+d0*3+c).
Proof.
  unfold P1,P3.
  intros HP1 HP3 l r.
  st.
  follow HP1.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  follow' HP1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (HP1:P1 (2+((2^n-1)*2)) (1+((2^n-1)*4)) (4+(2^n-1)*6))
  (HP2:P2 (3+(2^n-1)*6) (2+(2^n-1)*2) (1+(2^n-1)) ((2^n-1)*3) (3+(2^n-1)*3))
  (HP3:P3 (3+(2^n-1)*6) (3+(2^n-1)*4) (1+(2^n-1)*4) (2+(2^n-1)*2))
  (HP4:P4 (3+(2^n-1)*6) (7+(2^n-1)*8) (2+(2^n-1)*4) (3+(2^n-1)*4) (2+(2^n-1)*2))
  (HP5:P5 (3+(2^n-1)*6) (3+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6)):
  P n.

Lemma P_n n:
  P n.
Proof.
  induction n.
  1: econstructor; unfold P1,P2,P3,P4,P5; es.
  inverts IHn.
  assert (HP2':P2 (9+(2^n-1)*12) (4+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6) (6+(2^n-1)*6)).
  1: applys_eq (P2_S HP3 HP5); lia.
  assert (HP3':P3 (9+(2^n-1)*12) (7+(2^n-1)*8) (5+(2^n-1)*8) (4+(2^n-1)*4)).
  1: applys_eq (P3_S HP2' HP3); lia.
  assert (HP5':P5 (9+(2^n-1)*12) (7+(2^n-1)*8) (4+(2^n-1)*4) (9+(2^n-1)*12)).
  1: applys_eq (P5_S HP4 HP5); lia.
  econstructor; cbn[Nat.pow].
  - applys_eq (P1_S HP1 HP3); lia.
  - applys_eq HP2'; lia.
  - applys_eq HP3'; lia.
  - applys_eq (P4_S HP5' HP3'); lia.
  - applys_eq HP5'; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP1 0inf 0inf) as HP1.
  do 2 rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC1LC_0LF0LA_1LE1RE_1RA0RD_---0LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} r) (at level 30).

Definition P1 a b c :=
  forall l r,
  l <* [0]^^a <* [1] |> [0]^^b *> r -->*
  l <* [0] <* [1]^^c |> r.

Definition P2 a b c d e :=
  forall l r,
  l <* [1]^^a <{{B}} [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [0] <* [1]^^e |> r.

Definition P3 a b c d :=
  forall l r,
  l <* [1]^^a <{{B}} [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [0;1;1]^^d *> r.

Definition P4 a b c d e :=
  forall l r,
  l <* [1]^^a <* [0] {{D}}> [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [1;1] *> [0]^^d *> [0;1;1]^^e *> r.

Definition P5 a b c d :=
  forall l r,
  l <* [1]^^a <* [0] {{D}}> [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d {{E}}> r.

Lemma P2_S [a b c d a0 c0 d0]:
  P3 a b c (1+d) ->
  P5 a0 (2+c) c0 d0 ->
  P2 (a+3+a0) (b+1) c0 d0 (1+d*3).
Proof.
  unfold P2,P3,P5.
  intros HP3 HP5 l r.
  st.
  follow HP3.
  st.
  simpl_rotate.
  follow' HP5.
  es.
Qed.

Lemma P3_S [a b c d c0 d0]:
  P2 a b c d (1+d) ->
  P3 d (2+c0) c0 d0 ->
  P3 a (b+3+c0) (c*2+c0) (d0+d0).
Proof.
  unfold P2,P3.
  intros HP2 HP3 l r.
  st.
  follow HP2.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  follow' HP3.
  es.
Qed.

Lemma P4_S [a b c d b0 c0 d0]:
  P5 a b (2+c) (1+d) ->
  P3 (1+d) b0 c0 d0 ->
  P4 a (b+2+b0) (1+c*2) (2+c0) d0.
Proof.
  unfold P3,P4,P5.
  intros HP5 HP3 l r.
  st.
  follow HP5.
  st.
  rewrite <-lpow_shift1.
  follow' HP3.
  es.
Qed.

Lemma P5_S [a b c e a0 c0]:
  P4 a b c (1+c) e ->
  P5 a0 (1+c) c0 a0 ->
  P5 (a+3+a0) b (c0+c0) (e*3+a0).
Proof.
  unfold P4,P5.
  intros HP4 HP5 l r.
  st.
  follow HP4.
  follow' HP5.
  follow' HP5.
  es.
Qed.

Lemma P1_S [b c b0 d0 a1]:
  P1 (1+a1) (2+b) (1+c) ->
  P3 c b0 b d0 ->
  P1 (1+a1+1+a1) (2+b+2+b0) (1+d0*3+c).
Proof.
  unfold P1,P3.
  intros HP1 HP3 l r.
  st.
  follow HP1.
  st.
  do 5 rewrite <-lpow_shift1.
  follow' HP3.
  st.
  simpl_rotate.
  follow' HP1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (HP1:P1 (2+((2^n-1)*2)) (2+((2^n-1)*4)) (4+(2^n-1)*6))
  (HP2:P2 (3+(2^n-1)*6) (1+(2^n-1)*2) (1+(2^n-1)) ((2^n-1)*3) (1+(2^n-1)*3))
  (HP3:P3 (3+(2^n-1)*6) (2+(2^n-1)*4) ((2^n-1)*4) (2+(2^n-1)*2))
  (HP4:P4 (3+(2^n-1)*6) (6+(2^n-1)*8) (1+(2^n-1)*4) (2+(2^n-1)*4) (2+(2^n-1)*2))
  (HP5:P5 (3+(2^n-1)*6) (2+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6)):
  P n.

Lemma P_n n:
  P n.
Proof.
  induction n.
  1: econstructor; unfold P1,P2,P3,P4,P5; es.
  inverts IHn.
  assert (HP2':P2 (9+(2^n-1)*12) (3+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6) (4+(2^n-1)*6)).
  1: applys_eq (P2_S HP3 HP5); lia.
  assert (HP3':P3 (9+(2^n-1)*12) (6+(2^n-1)*8) (4+(2^n-1)*8) (4+(2^n-1)*4)).
  1: applys_eq (P3_S HP2' HP3); lia.
  assert (HP5':P5 (9+(2^n-1)*12) (6+(2^n-1)*8) (4+(2^n-1)*4) (9+(2^n-1)*12)).
  1: applys_eq (P5_S HP4 HP5); lia.
  econstructor; cbn[Nat.pow].
  - applys_eq (P1_S HP1 HP3); lia.
  - applys_eq HP2'; lia.
  - applys_eq HP3'; lia.
  - applys_eq (P4_S HP5' HP3'); lia.
  - applys_eq HP5'; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP1 0inf 0inf) as HP1.
  do 2 rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1RB_1RC0RA_1LD1RA_---1LE_0LF0LC_1RA0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} r) (at level 30).

Definition P1 b c :=
  forall r,
  0inf <* <[1;0;1] |> [0]^^b *> r -->*
  0inf <* <[1;0] <* [1]^^c |> r.

Definition P2 a b c d e :=
  forall l r,
  l <* [1]^^a <{{D}} [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [0] <* [1]^^e |> r.

Definition P3 a b c d :=
  forall l r,
  l <* [1]^^a <{{D}} [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [0;1;1]^^d *> r.

Definition P4 a b c d e :=
  forall l r,
  l <* [1]^^a <* [0] {{A}}> [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [1;1] *> [0]^^d *> [0;1;1]^^e *> r.

Definition P5 a b c d :=
  forall l r,
  l <* [1]^^a <* [0] {{A}}> [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d {{B}}> r.

Lemma P2_S [a b c d a0 c0 d0]:
  P3 a b c (1+d) ->
  P5 a0 (2+c) c0 d0 ->
  P2 (a+3+a0) (b+1) c0 d0 (1+d*3).
Proof.
  unfold P2,P3,P5.
  intros HP3 HP5 l r.
  st.
  follow HP3.
  st.
  simpl_rotate.
  follow' HP5.
  es.
Qed.

Lemma P3_S [a b c d c0 d0]:
  P2 a b c d (1+d) ->
  P3 d (2+c0) c0 d0 ->
  P3 a (b+3+c0) (c*2+c0) (d0+d0).
Proof.
  unfold P2,P3.
  intros HP2 HP3 l r.
  st.
  follow HP2.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  follow' HP3.
  es.
Qed.

Lemma P4_S [a b c d b0 c0 d0]:
  P5 a b (2+c) (1+d) ->
  P3 (1+d) b0 c0 d0 ->
  P4 a (b+2+b0) (1+c*2) (2+c0) d0.
Proof.
  unfold P3,P4,P5.
  intros HP5 HP3 l r.
  st.
  follow HP5.
  st.
  rewrite <-lpow_shift1.
  follow' HP3.
  es.
Qed.

Lemma P5_S [a b c e a0 c0]:
  P4 a b c (1+c) e ->
  P5 a0 (1+c) c0 a0 ->
  P5 (a+3+a0) b (c0+c0) (e*3+a0).
Proof.
  unfold P4,P5.
  intros HP4 HP5 l r.
  st.
  follow HP4.
  follow' HP5.
  follow' HP5.
  es.
Qed.

Lemma P1_S [b c b0 d0]:
  P1 (2+b) (1+c) ->
  P3 c b0 b d0 ->
  P1 (2+b+2+b0) (1+d0*3+c).
Proof.
  unfold P1,P3.
  intros HP1 HP3 r.
  st.
  follow HP1.
  st.
  do 3 rewrite <-lpow_shift1.
  follow' HP3.
  st.
  simpl_rotate.
  follow' HP1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (HP1:P1 (2+((2^n-1)*4)) (4+(2^n-1)*6))
  (HP2:P2 (3+(2^n-1)*6) (1+(2^n-1)*2) (1+(2^n-1)) ((2^n-1)*3) (1+(2^n-1)*3))
  (HP3:P3 (3+(2^n-1)*6) (2+(2^n-1)*4) ((2^n-1)*4) (2+(2^n-1)*2))
  (HP4:P4 (3+(2^n-1)*6) (6+(2^n-1)*8) (1+(2^n-1)*4) (2+(2^n-1)*4) (2+(2^n-1)*2))
  (HP5:P5 (3+(2^n-1)*6) (2+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6)):
  P n.

Lemma P_n n:
  P n.
Proof.
  induction n.
  1: econstructor; unfold P1,P2,P3,P4,P5; es.
  inverts IHn.
  assert (HP2':P2 (9+(2^n-1)*12) (3+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6) (4+(2^n-1)*6)).
  1: applys_eq (P2_S HP3 HP5); lia.
  assert (HP3':P3 (9+(2^n-1)*12) (6+(2^n-1)*8) (4+(2^n-1)*8) (4+(2^n-1)*4)).
  1: applys_eq (P3_S HP2' HP3); lia.
  assert (HP5':P5 (9+(2^n-1)*12) (6+(2^n-1)*8) (4+(2^n-1)*4) (9+(2^n-1)*12)).
  1: applys_eq (P5_S HP4 HP5); lia.
  econstructor; cbn[Nat.pow].
  - applys_eq (P1_S HP1 HP3); lia.
  - applys_eq HP2'; lia.
  - applys_eq HP3'; lia.
  - applys_eq (P4_S HP5' HP3'); lia.
  - applys_eq HP5'; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP1 0inf) as HP1.
  rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RF_---1LD_0LE0LB_0RA0LD_1LA1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{E}} r) (at level 30).

Definition P1 b c :=
  forall r,
  0inf |> [0]^^b *> r -->*
  0inf <* [1]^^c |> r.

Definition P2 a b c d e :=
  forall l r,
  l <* [1]^^a <{{C}} [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d <* [0] <* [1]^^e |> r.

Definition P3 a b c d :=
  forall l r,
  l <* [1]^^a <{{C}} [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [0;1;1]^^d *> r.

Definition P4 a b c d e :=
  forall l r,
  l <* [1]^^a <* [0] {{F}}> [1] *> [0]^^b *> r -->*
  l <| [0]^^c *> [1;1] *> [0]^^d *> [0;1;1]^^e *> r.

Definition P5 a b c d :=
  forall l r,
  l <* [1]^^a <* [0] {{F}}> [1] *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [1]^^d {{A}}> r.

Lemma P2_S [a b c d a0 c0 d0]:
  P3 a b c (1+d) ->
  P5 a0 (2+c) c0 d0 ->
  P2 (a+3+a0) (b+1) c0 d0 (1+d*3).
Proof.
  unfold P2,P3,P5.
  intros HP3 HP5 l r.
  st.
  follow HP3.
  st.
  simpl_rotate.
  follow' HP5.
  es.
Qed.

Lemma P3_S [a b c d c0 d0]:
  P2 a b c d (1+d) ->
  P3 d (2+c0) c0 d0 ->
  P3 a (b+3+c0) (c*2+c0) (d0+d0).
Proof.
  unfold P2,P3.
  intros HP2 HP3 l r.
  st.
  follow HP2.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  follow' HP3.
  es.
Qed.

Lemma P4_S [a b c d b0 c0 d0]:
  P5 a b (2+c) (1+d) ->
  P3 (1+d) b0 c0 d0 ->
  P4 a (b+2+b0) (1+c*2) (2+c0) d0.
Proof.
  unfold P3,P4,P5.
  intros HP5 HP3 l r.
  st.
  follow HP5.
  st.
  rewrite <-lpow_shift1.
  follow' HP3.
  es.
Qed.

Lemma P5_S [a b c e a0 c0]:
  P4 a b c (1+c) e ->
  P5 a0 (1+c) c0 a0 ->
  P5 (a+3+a0) b (c0+c0) (e*3+a0).
Proof.
  unfold P4,P5.
  intros HP4 HP5 l r.
  st.
  follow HP4.
  follow' HP5.
  follow' HP5.
  es.
Qed.

Lemma P1_S [b c b0 d0]:
  P1 (2+b) c ->
  P3 c b0 b d0 ->
  P1 (2+b+2+b0) (d0*3+c).
Proof.
  unfold P1,P3.
  intros HP1 HP3 r.
  st.
  follow HP1.
  st.
  do 2 rewrite <-lpow_shift1.
  follow' HP3.
  st.
  simpl_rotate.
  follow' HP1.
  es.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (HP1:P1 (2+((2^n-1)*4)) (3+(2^n-1)*6))
  (HP2:P2 (3+(2^n-1)*6) (1+(2^n-1)*2) (1+(2^n-1)) ((2^n-1)*3) (1+(2^n-1)*3))
  (HP3:P3 (3+(2^n-1)*6) (2+(2^n-1)*4) ((2^n-1)*4) (2+(2^n-1)*2))
  (HP4:P4 (3+(2^n-1)*6) (6+(2^n-1)*8) (1+(2^n-1)*4) (2+(2^n-1)*4) (2+(2^n-1)*2))
  (HP5:P5 (3+(2^n-1)*6) (2+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6)):
  P n.

Lemma P_n n:
  P n.
Proof.
  induction n.
  1: econstructor; unfold P1,P2,P3,P4,P5; es.
  inverts IHn.
  assert (HP2':P2 (9+(2^n-1)*12) (3+(2^n-1)*4) (2+(2^n-1)*2) (3+(2^n-1)*6) (4+(2^n-1)*6)).
  1: applys_eq (P2_S HP3 HP5); lia.
  assert (HP3':P3 (9+(2^n-1)*12) (6+(2^n-1)*8) (4+(2^n-1)*8) (4+(2^n-1)*4)).
  1: applys_eq (P3_S HP2' HP3); lia.
  assert (HP5':P5 (9+(2^n-1)*12) (6+(2^n-1)*8) (4+(2^n-1)*4) (9+(2^n-1)*12)).
  1: applys_eq (P5_S HP4 HP5); lia.
  econstructor; cbn[Nat.pow].
  - applys_eq (P1_S HP1 HP3); lia.
  - applys_eq HP2'; lia.
  - applys_eq HP3'; lia.
  - applys_eq (P4_S HP5' HP3'); lia.
  - applys_eq HP5'; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_n n) as HP.
  inverts HP.
  epose proof (HP1 0inf) as HP1.
  rewrite lpow_all0 in HP1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: follow HP1; finish.
    es.
  - split.
    + solve_sigma_score.
    + pose proof (pow2_ge n).
      lia.
Qed.

End TM6.


