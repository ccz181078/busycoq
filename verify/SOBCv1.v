From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

Section SOBCv1.

Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis n_init m_init:nat.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).


Definition d0 := [0;0;1].
Definition d1 := [1;1;1].
Definition d1a := [1;1] *> const 0.

Definition L n := BinaryCounter d0 d1 d1a n.
Definition R n := [1]^^n *> const 0.

Hypothesis HLInc:
  forall (l r0 : side) (n0 : nat), d1 ^^ n0 *> d0 *> l <| r0 -->+ d0 ^^ n0 *> d1 *> l |> r0.

Lemma LInc:
  forall r n (Hnf:not_full n),
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  intros.
  apply LInc.
  - apply HLInc.
  - apply Hnf.
Qed.

Hypothesis RInc:
  forall l n,
    l |> R (n*2) -->+
    l <| R (2+n*2).

Hypothesis HLOv2:
  forall n m,
  d1 ^^ n *> d1a <| [1] ^^ (2 + m * 3) *> const 0 -->+
  d0 ^^ (1 + m) *> d1 *> d0 ^^ n *> d1a <| [1] ^^ 0 *> const 0.

Lemma LOv2 n m:
  L (pow2' n) <| R (2+m*3) -->+
  L (((pow2 n)~1)*(pow2 (1+m))) <| R 0.
Proof.
  unfold L,R.
  rewrite Counter_pow2'.
  rewrite Counter_mulpow2.
  cbn[BinaryCounter].
  rewrite Counter_pow2.
  apply HLOv2.
Qed.

Lemma LIncs n m:
  L n <| R (m*2) -->*
  L (pow2' (log2 n)) <| R ((N.to_nat (rest n))*2+m*2).
Proof.
  remember (N.to_nat (rest n)) as r.
  gen n m.
  induction r; intros.
  - assert (rest n = 0)%N as E by lia.
    rewrite <-full_iff_rest in E.
    rewrite full_iff_pow2' in E.
    rewrite <-E.
    finish.
  - assert (rest n <> 0)%N as E by lia.
    pose proof (rest_S _ E) as H.
    rewrite <-not_full_iff_rest in E.
    follow100 (LInc (R (m*2)) _ E).
    follow100 RInc.
    epose proof (IHr (Pos.succ n) _ (1+m)) as H1.
    follow H1.
    rewrite not_full_log2_S. 2: apply E.
    finish.
Unshelve.
  lia.
Qed.

Lemma BigStep2 n m:
  L (pow2' n) <| R (2+m*6) -->+
  L (pow2' (2+m*2+n)) <| R (N.to_nat ((((N.pos (pow2 n))*2-1)*(N.pos (pow2 (1+m*2)))-1)*2)).
Proof.
  replace (m*6) with ((m*2)*3) by lia.
  follow10 LOv2.
  epose proof (LIncs _ 0) as H'.
  follow H'.
  clear H'.
  rewrite log2_mulpow2.
  cbn[log2].
  rewrite log2_pow2.
  pose proof (rest_mul_pow2 ((pow2 n)~1) (1+m*2)) as H.
  rewrite rest_mul2add1 in H.
  pose proof (rest_pow2 n) as H0.
  finish.
Qed.

Lemma pow2_mul2_mod3 n:
  (N.pos (pow2 (n*2)) mod 3 = 1)%N.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    replace (N.pos (pow2 (n * 2))~0~0) with ((N.pos (pow2 (n*2)))*4)%N by lia.
    rewrite N.Div0.mul_mod.
    rewrite IHn.
    reflexivity.
Qed.

Lemma sub_mod a b c:
  (a>=b ->
  c<>0 ->
  ((a-b) mod c) =
  ((a mod c)+(c-(b mod c))) mod c)%N.
Proof.
  intros H H0.
  remember (a-b)%N as d.
  replace a with (d+b)%N by lia.
  rewrite N.Div0.add_mod_idemp_l.
  pose proof (N.mod_upper_bound b c H0).
  pose proof (N.Div0.mod_le b c).
  replace (d+b+(c-b mod c))%N with (b+(d+c-(b mod c)))%N by lia.
  rewrite <-N.Div0.add_mod_idemp_l.
  replace (b mod c+(d+c-(b mod c)))%N with (d+c)%N by lia.
  rewrite <-N.Div0.add_mod_idemp_r.
  rewrite N.Div0.mod_same.
  rewrite N.add_0_r.
  reflexivity.
Qed.

Lemma Npos_mul a b:
  Npos (a*b)%positive = ((N.pos a)*(N.pos b))%N.
Proof.
  lia.
Qed.

Lemma BigStep n m:
  L (pow2' (n*2)) <| R (2+m*6) -->+
  L (pow2' ((1+m+n)*2)) <| R (N.to_nat (2+((((N.pos (pow2 (n*2)))*2-1)*(N.pos (pow2 (1+m*2)))-2)/3) * 6)).
Proof.
  follow10 BigStep2.
  remember (N.pos (pow2 (n * 2)) * 2 - 1)%N as v1.
  change (pow2 (1+m*2))%positive with (2*(pow2 (m*2)))%positive.
  remember (N.pos (2 * pow2 (m * 2))) as v2.
  assert (v1>=1)%N as E1 by lia.
  assert (v2>=2)%N as E2 by lia.
  replace (v1*v2-1)%N with (v1*v2-2+1)%N by lia.
  rewrite N.mul_add_distr_r.
  assert ((v1*v2-2) mod 3 = 0)%N. {
    rewrite sub_mod. 2,3: lia. cbn.
    rewrite N.Div0.mul_mod.
    rewrite Heqv2,Heqv1.
    repeat rewrite Npos_mul.
    rewrite sub_mod. 2,3: lia.
    rewrite (N.Div0.mul_mod (N.pos (pow2 (n * 2)))).
    rewrite (N.Div0.mul_mod _ (N.pos (pow2 (m * 2)))).
    repeat rewrite pow2_mul2_mod3.
    reflexivity.
  }
  finish.
Qed.

Definition config (x:nat*nat) :=
  let (n,m):=x in
  L (pow2' (n*2)) <| R (2+m*6).


Hypothesis init:
  c0 -->*
  config (n_init,m_init)%nat.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config _).
  1: apply init.
  apply progress_nonhalt_simple.
  intro i.
  destruct i as [n m].
  eexists (_,_).
  cbn[config].
  follow10 BigStep.
  rewrite Nnat.N2Nat.inj_add.
  rewrite Nnat.N2Nat.inj_mul.
  finish.
Qed.

End SOBCv1.

Inductive Cert :=
| cert1
  (QL QR : Q)
  (qL qR : list Sym)
  (n_init m_init : nat).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL ?QR
  ?qL ?qR
  ?n_init ?m_init) =>
  eapply (nonhalt _
    QL QR
    qL qR
    n_init m_init);
  [ unfold d0,d1,d1a;
    try (execute_with_shift_rule || fail)
  | intros;
    unfold R;
    simpl_tape;
    repeat rewrite lpow_mul;
    try (execute_with_shift_rule || fail)
  | intros;
    simpl_tape;
    rewrite lpow_mul;
    unfold d0,d1,d1a;
    try (execute_with_shift_rule || fail)
  | unfold config; cbn;
    try (solve_init || fail)
  ]
end.

Definition tm0 := Eval compute in (TM_from_str "1RB0RB_0RC0LE_1LD0RD_1LA0RF_1LD1RA_---0LA").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1LB0LB_1RC1LE_0RA0RD_1LE0RE_0LB0RF_---0LC").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 E A [1;0;1;0] [0;1;0;1] 0 0).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1RB1RB_1LC0LE_1LF1RD_---0RE_1LC0RC_1RA0RB").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB0RC_0LB1RC_1LD0LF_1LA1RE_---0RF_1LD0RD").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 D C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1RB0RC_0RC1RC_1LD0LE_1LA1RF_1LD0RD_---0RE").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 D C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB0RC_1LC1RC_1LE0LD_1LE0RE_1LA1RF_---0RD").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 E C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1RB0RD_1RC1RD_1LA1RF_1LC0LE_1LC0RC_---0RE").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 C D [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RF_0LA0LC_---0LA").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA1RF_0LA0LC_---0RC").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm9 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA1RF_1LD0LC_---0RC").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm10 := Eval compute in (TM_from_str "1RB1RE_0RC1RB_1LD0RD_1LA0RE_0LF0LA_---1LD").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm11 := Eval compute in (TM_from_str "1RB0RF_1LC0LF_0LE0RD_---1LE_1RA1LC_1LC0RC").
Lemma nonhalt11: ~halts tm11 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm12 := Eval compute in (TM_from_str "1RB0RF_1LC1RF_1LA1RD_---0RE_1LC0RC_0LA0LE").
Lemma nonhalt12: ~halts tm12 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm13 := Eval compute in (TM_from_str "1RB0RF_1LC1RF_1LA1RD_---0RE_1LC0RC_1LC0LE").
Lemma nonhalt13: ~halts tm13 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm14 := Eval compute in (TM_from_str "1RB1RF_1LC0RC_1LE1RD_---0RB_1RA0RF_1LC0LB").
Lemma nonhalt14: ~halts tm14 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm15 := Eval compute in (TM_from_str "1RB---_0RC0LC_1LD0RD_0LE0RF_1RA1LD_---0LA").
Lemma nonhalt15: ~halts tm15 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm16 := Eval compute in (TM_from_str "1RB1RB_0RC0LC_1LD0RD_0LE1RF_1RA1LD_---0LA").
Lemma nonhalt16: ~halts tm16 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm17 := Eval compute in (TM_from_str "1RB1RB_0RC0LC_1LD0RD_1LE1RF_1RA0RB_---0RC").
Lemma nonhalt17: ~halts tm17 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm18 := Eval compute in (TM_from_str "1RB0RC_0LB1RC_0RD0LD_1LE0RE_1LA1RF_---0RD").
Lemma nonhalt18: ~halts tm18 c0.
Proof.
  solve_cert (cert1 E C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm19 := Eval compute in (TM_from_str "1RB0RC_0RC0LC_1LD0RD_0LE0RF_1RA1LD_---1LE").
Lemma nonhalt19: ~halts tm19 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm20 := Eval compute in (TM_from_str "1RB0RC_1LC1RC_0RD0LD_1LE0RE_1LA1RF_---0RD").
Lemma nonhalt20: ~halts tm20 c0.
Proof.
  solve_cert (cert1 E C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm21 := Eval compute in (TM_from_str "1RB0RD_0RC0LA_1LD0RD_0LE0RF_1RA1LD_---0LA").
Lemma nonhalt21: ~halts tm21 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm22 := Eval compute in (TM_from_str "1RB0RD_1RC1RD_1LA1RF_0RE0LE_1LC0RC_---0RE").
Lemma nonhalt22: ~halts tm22 c0.
Proof.
  solve_cert (cert1 C D [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm23 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA1RF_0RC0LC_---0RC").
Lemma nonhalt23: ~halts tm23 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm24 := Eval compute in (TM_from_str "1RB1RE_0RC0LF_1LD0RD_0LE0RF_1RA1LD_---0LA").
Lemma nonhalt24: ~halts tm24 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm25 := Eval compute in (TM_from_str "1RB0RF_1LC1RF_1LA1RD_---0RE_1LC0RC_0RE0LE").
Lemma nonhalt25: ~halts tm25 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm26 := Eval compute in (TM_from_str "1RB1RF_1LC0RC_1LE1RD_---0RB_1RA0RF_0RB0LB").
Lemma nonhalt26: ~halts tm26 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm27 := Eval compute in (TM_from_str "1RB0RE_1LC0LF_1LA1RD_---0RB_0RC0LB_0RE1RA").
Lemma nonhalt27: ~halts tm27 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm28 := Eval compute in (TM_from_str "1RB0RE_1LC0LF_1LA1RD_---0RB_0RC0LB_1LF1RA").
Lemma nonhalt28: ~halts tm28 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm29 := Eval compute in (TM_from_str "1RB1RE_0RC1RB_1LD0RD_1LA0RE_0LF0LA_---0LB").
Lemma nonhalt29: ~halts tm29 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm30 := Eval compute in (TM_from_str "1RB1RE_0RC1RB_1LD0RD_1LA1RF_0LF0LA_---0LB").
Lemma nonhalt30: ~halts tm30 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm31 := Eval compute in (TM_from_str "1RB---_0RC0LC_1LD0RD_0LE1RF_1RA1LD_---0RC").
Lemma nonhalt31: ~halts tm31 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm33 := Eval compute in (TM_from_str "1RB---_1LC0LE_0LF1RD_---0RE_1LC0RC_1RA1LC").
Lemma nonhalt33: ~halts tm33 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm34 := Eval compute in (TM_from_str "1RB1RA_0RC0LA_1LD0RD_0LE0RF_1RA1LD_---0LA").
Lemma nonhalt34: ~halts tm34 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm35 := Eval compute in (TM_from_str "1RB0LB_0RC1RB_1LD0RD_0LE0RF_1RA1LD_---1LE").
Lemma nonhalt35: ~halts tm35 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm36 := Eval compute in (TM_from_str "1RB0LB_1LC0RC_1LE0RD_---0LE_1RF0RA_0RB1RF").
Lemma nonhalt36: ~halts tm36 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm37 := Eval compute in (TM_from_str "1RB0LB_1LC0RC_1LF1RD_---0LE_0RB1RE_1RE0RA").
Lemma nonhalt37: ~halts tm37 c0.
Proof.
  solve_cert (cert1 C E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm38 := Eval compute in (TM_from_str "1RB0RB_0RC0LE_1LD0RD_1LA1RF_1LD1RA_---0RC").
Lemma nonhalt38: ~halts tm38 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm39 := Eval compute in (TM_from_str "1LB0LB_1RC1LE_0RA0RD_1LE0RE_0LB0RF_---1LB").
Lemma nonhalt39: ~halts tm39 c0.
Proof.
  solve_cert (cert1 E A [1;0;1;0] [0;1;0;1] 0 0).
Qed.

Definition tm40 := Eval compute in (TM_from_str "1RB0RB_1LC0LF_1LA1RD_---0RE_1LC0RC_1LC1RA").
Lemma nonhalt40: ~halts tm40 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm41 := Eval compute in (TM_from_str "1RB0LC_0RC1RB_1LD0RD_1LE0RF_1RB0RA_---0LA").
Lemma nonhalt41: ~halts tm41 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm42 := Eval compute in (TM_from_str "1RB0LC_0RC1RB_1LD0RD_1LE0RF_1RB0RA_---0LE").
Lemma nonhalt42: ~halts tm42 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm43 := Eval compute in (TM_from_str "1RB0LC_0RC1RB_1LD0RD_1LE1RF_1RB0RA_---0LB").
Lemma nonhalt43: ~halts tm43 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm44 := Eval compute in (TM_from_str "1RB0RC_1LC0LA_0LF1RD_---0RE_1LC0RC_1RA1LC").
Lemma nonhalt44: ~halts tm44 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm45 := Eval compute in (TM_from_str "1RB1RC_0LA0LC_1LD0RD_0LF1RE_---0RC_1RA1LD").
Lemma nonhalt45: ~halts tm45 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm46 := Eval compute in (TM_from_str "1RB1RC_1LA0LD_---0RD_1LE0RE_0LF1RC_1RA1LE").
Lemma nonhalt46: ~halts tm46 c0.
Proof.
  solve_cert (cert1 E B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm47 := Eval compute in (TM_from_str "1RB1RC_1LA0LF_1RA1LD_0LC1RE_---0RF_1LD0RD").
Lemma nonhalt47: ~halts tm47 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm48 := Eval compute in (TM_from_str "1RB0RD_0RC0LA_1LD0RD_0LE1RF_1RA1LD_---0RC").
Lemma nonhalt48: ~halts tm48 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm49 := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA1RD_---0LB_0RF1RB_1LC0RC").
Lemma nonhalt49: ~halts tm49 c0.
Proof.
  solve_cert (cert1 C E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm50 := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA1RD_---0LB_0RF1RE_1LC0RC").
Lemma nonhalt50: ~halts tm50 c0.
Proof.
  solve_cert (cert1 C E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm51 := Eval compute in (TM_from_str "1RB1LD_0RC1RB_1LD0RD_1LE0RF_1RB1RF_---0LA").
Lemma nonhalt51: ~halts tm51 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm52 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RE_---0LF_1LD1RB").
Lemma nonhalt52: ~halts tm52 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm53 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA0RF_---0LC_---0LA").
Lemma nonhalt53: ~halts tm53 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm54 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA0RF_1LD0LE_---0LA").
Lemma nonhalt54: ~halts tm54 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm55 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RF_---0LC_---0LB").
Lemma nonhalt55: ~halts tm55 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm56 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RF_1LD0LE_---0LB").
Lemma nonhalt56: ~halts tm56 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm57 := Eval compute in (TM_from_str "1RB0RE_0RC1RF_1LD0RD_1LA1RE_---0LF_1LD1RB").
Lemma nonhalt57: ~halts tm57 c0.
Proof.
  solve_cert (cert1 D F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm58 := Eval compute in (TM_from_str "1RB0RF_1LC1RB_1LA1RD_---0RE_0LF0RC_0RB0LB").
Lemma nonhalt58: ~halts tm58 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm59 := Eval compute in (TM_from_str "1RB1LF_1LC0LF_0LE1RD_---0RB_1RA1LC_0RE0RC").
Lemma nonhalt59: ~halts tm59 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm60 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RE_---0LF_0LB1RF").
Lemma nonhalt60: ~halts tm60 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm61 := Eval compute in (TM_from_str "1RB0RF_0LC1RB_0RD1RC_1LE0RE_1LA1RF_---0LB").
Lemma nonhalt61: ~halts tm61 c0.
Proof.
  solve_cert (cert1 C B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm62 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE0RF_1RA1LD_---0LA").
Lemma nonhalt62: ~halts tm62 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm63 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_1RA1LD_---0LB").
Lemma nonhalt63: ~halts tm63 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm64 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_0RF1LD_1LA0LB").
Lemma nonhalt64: ~halts tm64 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm65 := Eval compute in (TM_from_str "1RB1RA_0RC0LA_1LD0RD_0LE1RF_1RA1LD_---0RC").
Lemma nonhalt65: ~halts tm65 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm66 := Eval compute in (TM_from_str "1RB1RA_1LC0LA_0LF1RD_---0RE_1LC0RC_1RA1LC").
Lemma nonhalt66: ~halts tm66 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm67 := Eval compute in (TM_from_str "1RB0LB_0RC1RB_1LD0RD_1LE0RF_1RB1RF_---0LA").
Lemma nonhalt67: ~halts tm67 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm68 := Eval compute in (TM_from_str "1RB0LB_1LC1RB_1LF1RD_---0RE_1LC0RC_1RB0RA").
Lemma nonhalt68: ~halts tm68 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm69 := Eval compute in (TM_from_str "1RB0LB_1LC0RC_1LE1RD_---0RB_1RF0RA_0RB1RF").
Lemma nonhalt69: ~halts tm69 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm70 := Eval compute in (TM_from_str "1RB0LB_1LC0RC_1LE1RD_---0RB_1RF0RA_1LC1RF").
Lemma nonhalt70: ~halts tm70 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm71 := Eval compute in (TM_from_str "1LB0LB_1RC1LD_0RA1LD_0LB1RE_---0RF_1LD0RD").
Lemma nonhalt71: ~halts tm71 c0.
Proof.
  solve_cert (cert1 D A [1;0;1;0] [0;1;0;1] 0 0).
Qed.

Definition tm72 := Eval compute in (TM_from_str "1LB0LB_1RC1LE_0RA0RD_1LE0RE_0LB1RF_---0RD").
Lemma nonhalt72: ~halts tm72 c0.
Proof.
  solve_cert (cert1 E A [1;0;1;0] [0;1;0;1] 0 0).
Qed.

Definition tm73 := Eval compute in (TM_from_str "1RB1RB_0RC1RB_1LD0RD_0LE1RF_1RA1LD_---0LA").
Lemma nonhalt73: ~halts tm73 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm74 := Eval compute in (TM_from_str "1RB0LC_0RC1RB_1LD0RD_1LE1RF_1RB0RA_---0RC").
Lemma nonhalt74: ~halts tm74 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm75 := Eval compute in (TM_from_str "1RB0RC_0RC1RB_1LD0RD_0LE0RF_1RA1LD_---1LE").
Lemma nonhalt75: ~halts tm75 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm76 := Eval compute in (TM_from_str "1RB0LD_1LC0RC_1LF1RD_---0LE_0RB1RE_1RE1RA").
Lemma nonhalt76: ~halts tm76 c0.
Proof.
  solve_cert (cert1 E E [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm77 := Eval compute in (TM_from_str "1RB1RD_0RC1RB_1LD0RF_1LA0LE_---0LB_1LA1RE").
Lemma nonhalt77: ~halts tm77 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm78 := Eval compute in (TM_from_str "1RB1RD_0RC1RB_1LD0RF_0LE0LA_---1LF_1LA0RD").
Lemma nonhalt78: ~halts tm78 c0.
Proof.
  solve_cert (cert1 F B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm79 := Eval compute in (TM_from_str "1RB0LE_1LC1RB_1LF1RD_---0RE_1LC0RC_1RB0RA").
Lemma nonhalt79: ~halts tm79 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm80 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RE_---0LF_0LB1RB").
Lemma nonhalt80: ~halts tm80 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm81 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA0RF_0LB0LE_---0LA").
Lemma nonhalt81: ~halts tm81 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm82 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RF_---0LC_---0RC").
Lemma nonhalt82: ~halts tm82 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm83 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RF_0LB0LE_---0LB").
Lemma nonhalt83: ~halts tm83 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm84 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RF_0LB0LE_---0RC").
Lemma nonhalt84: ~halts tm84 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm85 := Eval compute in (TM_from_str "1RB0RE_0RC1RB_1LD0RD_1LA1RF_1LD0LE_---0RC").
Lemma nonhalt85: ~halts tm85 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm86 := Eval compute in (TM_from_str "1RB1RE_0RC1RB_1LD0RD_1LA1RF_---0LF_---0LB").
Lemma nonhalt86: ~halts tm86 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm87 := Eval compute in (TM_from_str "1RB0LF_0RC1RB_1LD0RD_1LE1RF_1RB1RA_---0LB").
Lemma nonhalt87: ~halts tm87 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm88 := Eval compute in (TM_from_str "1RB0LF_1LC0RC_1LE1RD_---0RB_1RF0RA_1LC1RF").
Lemma nonhalt88: ~halts tm88 c0.
Proof.
  solve_cert (cert1 C F [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm89 := Eval compute in (TM_from_str "1RB0RF_0LC1RC_0RD1RC_1LE0RE_1LA1RF_---0LB").
Lemma nonhalt89: ~halts tm89 c0.
Proof.
  solve_cert (cert1 C C [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm90 := Eval compute in (TM_from_str "1RB0RF_1LC1RB_1LA1RD_---0RE_1LC0RC_---0LB").
Lemma nonhalt90: ~halts tm90 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm91 := Eval compute in (TM_from_str "1RB0RF_1LC1RB_1LA1RD_---0RE_1LC0RC_---0LE").
Lemma nonhalt91: ~halts tm91 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm92 := Eval compute in (TM_from_str "1RB0RF_1LC1RB_1LA1RD_---0RE_1LC0RC_1LC0LF").
Lemma nonhalt92: ~halts tm92 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm93 := Eval compute in (TM_from_str "1RB0RF_1LC1RB_1LA1RD_---0RE_1LF0RC_1LA0LB").
Lemma nonhalt93: ~halts tm93 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm94 := Eval compute in (TM_from_str "1RB0RF_1LC1RB_0LE0RD_---1LE_1RA1LC_1LC0RC").
Lemma nonhalt94: ~halts tm94 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm95 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE0RF_1RA0LB_---0LA").
Lemma nonhalt95: ~halts tm95 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm96 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_1RA0LB_---0LB").
Lemma nonhalt96: ~halts tm96 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm97 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_1RA0LB_---0RC").
Lemma nonhalt97: ~halts tm97 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm98 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_0RF0LB_1LA0LB").
Lemma nonhalt98: ~halts tm98 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm99 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_0RF0LB_1LA0RC").
Lemma nonhalt99: ~halts tm99 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm100 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_0RF1LD_1LA0RC").
Lemma nonhalt100: ~halts tm100 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm101 := Eval compute in (TM_from_str "1RB---_1LC1RB_0LF1RD_---0RE_1LC0RC_1RA1LC").
Lemma nonhalt101: ~halts tm101 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm102 := Eval compute in (TM_from_str "1RB---_1LC1RB_0LF1RD_1LA0RE_1LC0RC_0RD1LC").
Lemma nonhalt102: ~halts tm102 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm103 := Eval compute in (TM_from_str "1RB0LB_0RC1RB_1LD0RD_0LE0RF_1RA0LB_---1LE").
Lemma nonhalt103: ~halts tm103 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm104 := Eval compute in (TM_from_str "1RB1RB_0RC1RB_1LD0RD_0LE1RF_1RA0LB_---0LA").
Lemma nonhalt104: ~halts tm104 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm105 := Eval compute in (TM_from_str "1RB0RC_0RC1RB_1LD0RD_0LE0RF_1RA0LB_---1LE").
Lemma nonhalt105: ~halts tm105 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm106 := Eval compute in (TM_from_str "1RB1RC_0LA1RB_1LD0RD_0LF1RE_---0RC_1RA1LD").
Lemma nonhalt106: ~halts tm106 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm107 := Eval compute in (TM_from_str "1RB1RC_1LA1RB_---0RD_1LE0RE_0LF1RC_1RA1LE").
Lemma nonhalt107: ~halts tm107 c0.
Proof.
  solve_cert (cert1 E B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm108 := Eval compute in (TM_from_str "1RB1RC_1LA1RB_---0RD_1LE0RE_0LF1RC_0RB1LE").
Lemma nonhalt108: ~halts tm108 c0.
Proof.
  solve_cert (cert1 E B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm109 := Eval compute in (TM_from_str "1RB1RC_1LA1RB_1RA1LD_0LC1RE_---0RF_1LD0RD").
Lemma nonhalt109: ~halts tm109 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm110 := Eval compute in (TM_from_str "1RB1RC_1LA1RB_0RB1LD_0LC1RE_---0RF_1LD0RD").
Lemma nonhalt110: ~halts tm110 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm111 := Eval compute in (TM_from_str "1RB0RE_1RC1RB_1LD0LA_---0LE_0RF0LB_1LA0RC").
Lemma nonhalt111: ~halts tm111 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm112 := Eval compute in (TM_from_str "1RB1RE_0RC1RB_1LD0RD_0LE1RF_1RA0LB_---1LA").
Lemma nonhalt112: ~halts tm112 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm113 := Eval compute in (TM_from_str "1RB0RF_0RC1RB_1LD1RA_0LE0RB_1RA0LB_---0LC").
Lemma nonhalt113: ~halts tm113 c0.
Proof.
  solve_cert (cert1 B B [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm114 := Eval compute in (TM_from_str "1RB---_0RC1RB_1LD0RD_0LE1RF_1RA1LD_---0RC").
Lemma nonhalt114: ~halts tm114 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm115 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA1RF_0LA0LC_---0LB").
Lemma nonhalt115: ~halts tm115 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm116 := Eval compute in (TM_from_str "1RB1RA_0RC0LC_1LD0RD_1LE0RF_1RF0RB_---0LA").
Lemma nonhalt116: ~halts tm116 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm117 := Eval compute in (TM_from_str "1RB1LB_0RC0LC_1LD0RD_0LE0RF_1RA0RE_---0LA").
Lemma nonhalt117: ~halts tm117 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm118 := Eval compute in (TM_from_str "1RB0RC_0LB1RC_0RD0LD_1LE0RE_1LA0RF_---0LA").
Lemma nonhalt118: ~halts tm118 c0.
Proof.
  solve_cert (cert1 E C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm119 := Eval compute in (TM_from_str "1RB0RC_0RC1RC_1LD0LE_1LA1RF_0LB0RD_---0RE").
Lemma nonhalt119: ~halts tm119 c0.
Proof.
  solve_cert (cert1 B C [0;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm120 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA1RF_0LA0LC_---0LA").
Lemma nonhalt120: ~halts tm120 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm121 := Eval compute in (TM_from_str "1RB1LB_0RC0LC_1LD0RD_0LE1RF_1RA0RE_---0RC").
Lemma nonhalt121: ~halts tm121 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm122 := Eval compute in (TM_from_str "1RB1LB_1LC0LE_0LF1RD_---0RE_1LC0RC_1RA0RF").
Lemma nonhalt122: ~halts tm122 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm123 := Eval compute in (TM_from_str "1RB1RB_0RC0LC_1LD0RD_1LE0RF_1RA0RB_---0LA").
Lemma nonhalt123: ~halts tm123 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm124 := Eval compute in (TM_from_str "1RB1RB_0RC0LC_1LD0RD_1LE1RF_1RA0RB_---0LA").
Lemma nonhalt124: ~halts tm124 c0.
Proof.
  solve_cert (cert1 D B [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm125 := Eval compute in (TM_from_str "1RB0RC_0LB1RC_0RD0LD_1LE0RE_1LA1RF_---0LB").
Lemma nonhalt125: ~halts tm125 c0.
Proof.
  solve_cert (cert1 E C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm126 := Eval compute in (TM_from_str "1RB0RC_1LC1RC_0RD0LD_1LE0RE_1LA1RF_---0LB").
Lemma nonhalt126: ~halts tm126 c0.
Proof.
  solve_cert (cert1 E C [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm127 := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA1RD_---0LB_0RF0LF_1LC0RC").
Lemma nonhalt127: ~halts tm127 c0.
Proof.
  solve_cert (cert1 C E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm128 := Eval compute in (TM_from_str "1RB0RD_1RC1RD_1LA1RF_0RE0LE_1LC0RC_---0LB").
Lemma nonhalt128: ~halts tm128 c0.
Proof.
  solve_cert (cert1 C D [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm129 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA0RF_0LA0LC_---0LA").
Lemma nonhalt129: ~halts tm129 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm130 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA0RF_0RC0LC_---0LA").
Lemma nonhalt130: ~halts tm130 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm131 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA0RF_1LD0LC_---0LA").
Lemma nonhalt131: ~halts tm131 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm132 := Eval compute in (TM_from_str "1RB0RE_0RC1RE_1LD0RD_1LA1RF_0RC0LC_---0LB").
Lemma nonhalt132: ~halts tm132 c0.
Proof.
  solve_cert (cert1 D E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm133 := Eval compute in (TM_from_str "1RB0RE_1LC1RE_1LA1RD_---0LB_0RF0LF_1LC0RC").
Lemma nonhalt133: ~halts tm133 c0.
Proof.
  solve_cert (cert1 C E [1;0;1;0] [1;1;0;1] 0 0).
Qed.

Definition tm134 := Eval compute in (TM_from_str "1RB1RE_1LC0RC_1LF1RD_---0LA_0RB0LB_1RA0RE").
Lemma nonhalt134: ~halts tm134 c0.
Proof.
  solve_cert (cert1 C E [1;0;1;0] [1;1;0;1] 0 0).
Qed.






