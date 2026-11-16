From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

Definition Pos_mul2add(a:positive)(b:N):=
  Pos.of_nat (N.to_nat ((Npos a)*2+b)).

Lemma Pos_mul2add0 k:
  (Pos_mul2add k 0 = k~0)%positive.
Proof.
  cbn. lia.
Qed.

Lemma Pos_mul2add1 k:
  (Pos_mul2add k 1 = k~1)%positive.
Proof.
  cbn. lia.
Qed.


Section SBCv2.

Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR d0 d1 d1a:list Sym.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Definition L n := BinaryCounter d0 d1 (d1a *> const 0) n.

Hypothesis R0:nat->side.
Hypothesis R1:nat->nat->side.
Hypothesis c1 c2:nat.
Hypothesis a0 a1:N.
Hypothesis k_init n_init:nat.


Hypothesis LInc:
  forall r n (Hnf:not_full n),
    L n <| r -->+
    L (Pos.succ n) |> r.

Hypothesis RInc0:
  forall l n,
    l |> R0 n -->+
    l <| R0 (c1+n).

Hypothesis RInc1:
  forall l n m,
    l |> R1 (1+n) m -->+
    l <| R1 n (1+m).

Hypothesis ROv1:
  forall l m,
    l |> R1 0 m -->+
    l <| R0 (c2+m).


Hypothesis LOv:
  forall n m,
    L ((pow2' n)~1) <| R0 (1+m) -->+
    L (Pos_mul2add (Pos_mul2add (pow2 n) a0) a1) |> R1 (m) 0.


Hypothesis Ha0: (a0=0\/a0=1)%N.
Hypothesis Ha1: (a1=0\/a1=1)%N.
Hypothesis Hc1:(c1=1 \/ c1=2)%nat.
Hypothesis Hc2:(c2=1 \/ c2=2)%nat.

Lemma Incs1 k n m:
  n <= N.to_nat (rest k) ->
  L k |> R1 n m -->*
  L (Pos.of_nat (n+(Pos.to_nat k))) <| R0 (c2+n+m).
Proof.
  gen k m.
  induction n; intros.
  - follow100 ROv1.
    finish.
  - assert (rest k <> 0)%N as E by lia.
    pose proof (rest_S _ E) as H1.
    rewrite <-not_full_iff_rest in E.
    epose proof (LInc _ _ E) as H0.
    follow100 RInc1.
    follow100 H0.
    follow IHn. 1: lia.
    finish.
Qed.

Lemma Incs0 k n:
  L k <| R0 n -->*
  L (pow2' (log2 k)) <| R0 ((N.to_nat (rest k))*c1 + n).
Proof.
  remember (N.to_nat (rest k)) as i.
  gen k n.
  induction i; intros.
  - assert (rest k = 0)%N as E by lia.
    rewrite <-full_iff_rest in E.
    rewrite full_iff_pow2' in E.
    finish.
  - assert (rest k <> 0)%N as E by lia.
    pose proof (rest_S _ E) as H1.
    rewrite <-not_full_iff_rest in E.
    epose proof (LInc _ _ E) as H0.
    follow100 H0.
    follow100 RInc0.
    follow IHi. 1: lia.
    rewrite not_full_log2_S; auto.
    finish.
Qed.


Lemma not_full_log2_add n k:
  n <= N.to_nat (rest k) ->
  log2 (Pos.of_nat (n+(Pos.to_nat k))) = log2 k.
Proof.
  gen k.
  induction n; intros.
  - f_equal; lia.
  - specialize (IHn (Pos.succ k)).
    assert (rest k <> 0)%N as E by lia.
    epose proof (rest_S _ E).
    rewrite <-not_full_iff_rest in E.
    rewrite (not_full_log2_S E) in IHn.
    rewrite <-IHn. 2: lia.
    f_equal. lia.
Qed.

Lemma log2_Pos_mul2add k i:
  (i=0\/i=1)%N ->
  log2 (Pos_mul2add k i) = S (log2 k).
Proof.
  intro H.
  destruct H; subst.
  - rewrite Pos_mul2add0.
    reflexivity.
  - rewrite Pos_mul2add1.
    reflexivity.
Qed.


Definition config(x:nat*nat) :=
  let (k,n):=x in
  L (pow2' (S k)) <| R0 (1+n).

Definition P(x:nat*nat):Prop :=
  let (k,n):=x in
  ((N.of_nat n)+(a0*2+a1+1)<=Npos (pow2 (2+k)))%N.

Lemma BigStep k n:
  P (k,n) ->
  config (k,n) -->+
  config (S k,
    (N.to_nat
    (N.pos (pow2' (S (S k))) -
     (N.of_nat n) - N.pos (Pos_mul2add (Pos_mul2add (pow2 k) a0) a1)) * c1 +
    (c2 - 1 + n))
  ).
Proof.
  unfold config,P.
  intro H.
  assert (n <= N.to_nat (rest (Pos_mul2add (Pos_mul2add (pow2 k) a0) a1))) as H'. {
    destruct Ha0,Ha1;
    subst;
    repeat (rewrite Pos_mul2add0 || rewrite Pos_mul2add1);
    repeat (rewrite rest_mul2 || rewrite rest_mul2add1);
    cbn in H;
    pose proof (rest_pow2 k); lia.
  }
  cbn[pow2'].
  follow10 LOv.
  follow Incs1.
  follow Incs0.
  unfold rest.
  rewrite not_full_log2_add; auto.
  do 2 (rewrite log2_Pos_mul2add; auto).
  rewrite log2_pow2.
  cbn[pow2'].
  finish.
Qed.

Hypothesis init:
  c0 -->* config (k_init,n_init).

Hypothesis Pinit:
  P (k_init,n_init).


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config _).
  1: apply init.
  eapply progress_nonhalt_cond.
  2: apply Pinit.
  intro i.
  destruct i as [k n].
  intro H.
  eexists (_,_).
  split.
  1: apply BigStep.
  1: apply H.
  unfold P in H.
  unfold P.
  cbn in H.
  cbn[Nat.add].
  cbn[pow2].
  cbn[pow2'].
  clear Pinit.
  pose proof (pow2'_spec k) as H0.
  cbn[pow2] in H0.
  destruct Hc1,Ha0,Ha1; subst;
  repeat (rewrite Pos_mul2add0 || rewrite Pos_mul2add1);
  lia.
Qed.

End SBCv2.


Inductive Cert :=
| cert1
  (QL QR : Q)
  (qL qR d0 d1 d1a : list Sym)
  (R0: nat->side)
  (R1: nat->nat->side)
  (c1 c2: nat)
  (a0 a1: N)
  (k_init n_init: nat)
.

Ltac solve_LOverflow :=
  intros;
  simpl_tape; cbn; step1s;
  use_shift_rule; cbn;
  step1s;
  use_shift_rule; cbn;
  simpl_rotate;
  step1s.

Ltac solve_cert cert :=
time
match cert with
| (cert1
  ?QL ?QR
  ?qL ?qR ?d0 ?d1 ?d1a
  ?R0 ?R1
  ?c1 ?c2
  ?a0 ?a1
  ?k_init ?n_init) =>
  eapply (nonhalt _
    QL QR
    qL qR d0 d1 d1a
    R0 R1
    c1 c2
    a0 a1
    k_init n_init);
  [ intros;
    apply LInc; [|assumption];
    try (execute_with_shift_rule; fail)
  | intros l n;
    try (casen_execute_with_shift_rule n; fail)
  | intros l n m;
    try (casen_execute_with_shift_rule m; fail)
  | intros l n;
    try (casen_execute_with_shift_rule n; fail)
  | intros;
    unfold L;
    repeat (rewrite Pos_mul2add0 || rewrite Pos_mul2add1);
    cbn[BinaryCounter];
    rewrite Counter_pow2',Counter_pow2;
    try ((execute_with_shift_rule; fail) || (solve_LOverflow; fail))
  | lia
  | lia
  | lia
  | lia
  | unfold config; cbn; try (solve_init; fail)
  | unfold P; cbn; lia
  ]
end.

Definition tm0 := Eval compute in (TM_from_str "1LB0RD_0RC0LC_1LB1RD_0RE1RE_1RA1LF_0LB---").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 B D [1;0;1] [0;1;0] [0;1;1;1] [0;1;0;1] [0;1;0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm1 := Eval compute in (TM_from_str "1RB1LF_1LC0RE_0RD0LB_1LC1RE_0RA1RF_0LC---").

Theorem nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 C F [1;0;1] [1;1;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1LB1RC_0RA0LE_0RD1RF_1RE1LF_1LB0RC_0LB---").

Theorem nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 B F [1;0;1] [1;1;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1RB1LF_1LC0RE_0RD0LB_1RC1RE_0RA1RF_0LC---").

Theorem nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 C A [1;0;1] [0;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1RB1RB_0RC1RF_1RD1LF_1LE0RB_0RA0LD_0LE---").

Theorem nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 E F [1;0;1] [1;1;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB1LF_1LC0RE_0RD0LB_1RE1RE_0RA1RF_0LC---").

Theorem nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 C F [1;0;1] [1;1;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1LB0RD_0RC0LA_1RB1RD_0RE1RF_1RA1LF_0LB---").

Theorem nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 B E [1;0;1] [0;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1LB0RC_0RC0LC_0LF1RD_0RE---_1RF0RE_1LB1RA").

Theorem nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 B A [1;0;0;1] [1;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1LB0RE_0LC1LD_1RA0LA_0LE---_1LF0RA_0RF1RE").

Theorem nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 A E [0] [1] [0;0;1;0;0;0;0;0;0] [0;0;1;0;0;0;0;1;0] [0;0;1;0;0;0;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [1;0] *> [0;1;0]^^n *> [] *> const 0)
    1 1 0 0 1 3).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1LB0RE_0RC0LA_1RA1LD_0LB---_1RF1RD_0RA0RF").

Theorem nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 B F [1] [0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1RB1LD_1LC0RE_0RA0LB_0LC---_1RF1RD_0RB0RF").

Theorem nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 C F [1] [0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1LB0RE_0LC1RF_0RD1LA_1RA---_1RC1RF_0RA0LC").

Theorem nonhalt11: ~halts tm11 c0.
Proof.
  solve_cert (cert1 B A [1;1;0;1;0] [0;1;0;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0]^^n *> [1] *> const 0)
    (fun n m => [1;1;0]^^m *> [1] *> [1;1;0]^^n *> [1] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1RB1RF_0RC1LD_1RD---_1LE0RA_0LB1LA_0RD0LB").

Theorem nonhalt12: ~halts tm12 c0.
Proof.
  solve_cert (cert1 E D [1;1;0;1;0] [0;1;0;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0]^^n *> [1] *> const 0)
    (fun n m => [1;1;0]^^m *> [1] *> [1;1;0]^^n *> [1] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm13 := Eval compute in (TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0RB1RF_0LF0RA").

Theorem nonhalt13: ~halts tm13 c0.
Proof.
  solve_cert (cert1 D E [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1RB---_1LC0RD_1LD0LB_0RE1RB_0RB1RF_1LB0RA").

Theorem nonhalt14: ~halts tm14 c0.
Proof.
  solve_cert (cert1 D E [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1RB---_0RC0RC_0RD0LE_1RE1RA_1LF1RA_0LC1LB").

Theorem nonhalt15: ~halts tm15 c0.
Proof.
  solve_cert (cert1 F D [1;0;1;0;1;0] [0;0;1;1;0;0] [1;1;0;0] [1;1;1;0] [1;1;1]
    (fun n => [0;1;0;1;0;0;1;0;1;0]^^n *> [0;1] *> const 0)
    (fun n m => [0;1;0;1;0;0;1;0;1;0]^^m *> [0;1;0;1;0;0;1;0] *> [0;1;0;1;0;0;1;0;1;0]^^n *> [0;1] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RF_0RA1RE_1LF1RE_1LB0RC").

Theorem nonhalt16: ~halts tm16 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1LB---_1LC0LF_0RD1RF_0RA1RE_1LF0RA_1LB0RC").

Theorem nonhalt17: ~halts tm17 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm18 := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0RA1RE_1LA0RF_1LB---").

Theorem nonhalt18: ~halts tm18 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm19 := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0RA1RE_1LA1RF_1LA---").

Theorem nonhalt19: ~halts tm19 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm20 := Eval compute in (TM_from_str "1LB0RC_1LC0LA_0RD1RA_0RA1RE_0LE1RF_1LA---").

Theorem nonhalt20: ~halts tm20 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm21 := Eval compute in (TM_from_str "1LB---_1LC0LA_0RD1RF_0RF1RE_1LF1RE_1LB0RC").

Theorem nonhalt21: ~halts tm21 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm22 := Eval compute in (TM_from_str "1LB0RC_1LC0LF_0RD1RA_0RF1RE_1LA0RF_1LB---").

Theorem nonhalt22: ~halts tm22 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1LB0RC_1LC0LF_0RD1RA_0RA1RE_1LA0RF_1LB---").

Theorem nonhalt23: ~halts tm23 c0.
Proof.
  solve_cert (cert1 C D [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1LB0LE_0RC1RE_0RE1RD_1LE1RF_1LA0RB_0LC---").

Theorem nonhalt24: ~halts tm24 c0.
Proof.
  solve_cert (cert1 B C [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1LB0LE_0RC1RE_0RE1RD_1LE0RF_1LA0RB_0LC---").

Theorem nonhalt25: ~halts tm25 c0.
Proof.
  solve_cert (cert1 B C [1;1;0;1;0;1;0] [0;0;1;0;1;0;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm26 := Eval compute in (TM_from_str "1RB0RF_1LC1RF_0LE1LD_0RE0RE_0RA0LB_1RD---").

Theorem nonhalt26: ~halts tm26 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0;1;0;0;1] [1;1;0;0;1;0;0;0] [1;0;0;0] [1;1;1;0] [1;1;1]
    (fun n => [0;1;0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;1;0;0;1]^^m *> [0;1;0] *> [0;1;0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm27 := Eval compute in (TM_from_str "1LB0RF_1LC---_1RD1RE_0RE0RC_0RA0LE_0RC1RB").

Theorem nonhalt27: ~halts tm27 c0.
Proof.
  solve_cert (cert1 E F [0] [0] [0;1;0;0] [0;1;0;1] [0;1;0;1]
    (fun n => [0;1;0;1;1;0;1]^^n *> [] *> const 0)
    (fun n m => [0;1;0;1;1;0;1]^^m *> [0;1;0;1;1] *> [0;1;0;1;1;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm28 := Eval compute in (TM_from_str "1RB0LE_0RC1RF_1RD1LF_1LE0RB_0RA0LD_0LE---").

Theorem nonhalt28: ~halts tm28 c0.
Proof.
  solve_cert (cert1 E F [1;0;1] [1;1;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm29 := Eval compute in (TM_from_str "1RB1LF_1LC0RE_0RD0LB_1RE0LC_0RA1RF_0LC---").

Theorem nonhalt29: ~halts tm29 c0.
Proof.
  solve_cert (cert1 C F [1;0;1] [1;1;0] [1;0;0;0] [1;0;1;0] [1;0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm30 := Eval compute in (TM_from_str "1RB0LC_1LA1LE_1LD---_1LB1RF_0RA0RD_1RF0RE").

Theorem nonhalt30: ~halts tm30 c0.
Proof.
  solve_cert (cert1 D E [1;0;1] [0;1;1] [0;0;1;0;1;1] [0;0;1;0;1;0] [0;0;1;0;1]
    (fun n => [1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;0;1;0]^^m *> [0] *> [1;0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.





