From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Ltac flia := repeat (lia || f_equal).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LA1RB2RB2LA_2LB3RB4RB---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive Digit := d0 | d1 | d2.

Fixpoint L(ls:list Digit) :=
match ls with
| [] => 0inf <* [1]
| d0::ls0 => L ls0 <* [3]
| d1::ls0 => L ls0 <* [2]
| d2::ls0 => L ls0 <* [1]
end.

Fixpoint LS(ls:list Digit) :=
match ls with
| [] => d0::nil
| d0::ls0 => d1::ls0 
| d1::ls0 => d2::ls0 
| d2::ls0 => d0::LS ls0
end.

Fixpoint Ln n :=
match n with
| O => []
| S n0 => LS (Ln n0)
end.

Lemma Ln_spec n:
  d0::Ln n = Ln (n*3+1) /\
  d1::Ln n = Ln (n*3+2) /\
  d2::Ln n = Ln (n*3+3).
Proof.
  induction n; cbn.
  1: tauto.
  destruct IHn as [I0 [I1 I2]].
  repeat split.
  - rewrite <-I0; reflexivity.
  - rewrite <-I1; reflexivity.
  - rewrite <-I2; reflexivity.
Qed.

Lemma LInc n r:
  L (Ln n) <{{A}} r -->*
  L (Ln (1+n)) {{B}}> r.
Proof.
  cbn.
  gen r.
  induction (Ln n) as [|[ | | ] ls]; intros; cbn.
  all: er.
  follow IHls.
  er.
Qed.

Definition S0 a b c :=
  L (Ln a) {{B}}> [2]^^b *> [0] *> [2]^^c *> 0inf.

Lemma Inc0 a b c:
  S0 a (1+b) c -->*
  S0 (1+a) b (1+c).
Proof.
  unfold S0.
  es; er.
  follow LInc.
  finish.
Qed.

Lemma Incs0 a b c:
  S0 a b c -->*
  S0 (b+a) 0 (b+c).
Proof.
  gen a c.
  ind b Inc0.
Qed.

Lemma BigStep a c:
  S0 (a*3+2) 0 c -->+
  S0 (2+c+a) 0 (2+c).
Proof.
  unfold S0.
  pose proof (Ln_spec a) as [_ [H _]].
  rewrite <-H.
  mid10 (S0 a (2+c) 0).
  1: es.
  follow Incs0.
  es.
Qed.

Definition config n := S0 (n*3+2) 0 (n*2+3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold config.
  follow10 BigStep.
  finish.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB3RB1LA3LA2RA_2LB2RB0LA4RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive Digits :=
| h0 | h1
| d0(n:nat)(x:Digits)
| d1(n:nat)(x:Digits)
.

Fixpoint L(ls:Digits) :=
match ls with
| h0 => 0inf <* [1]
| h1 => 0inf <* [3]
| d0 n ls0 => L ls0 <* [2]^^n <* [4]
| d1 n ls0 => L ls0 <* [2]^^(1+n) <* [3]
end.

Definition Lx(ls:Digits):nat :=
match ls with
| d0 _ _ => 1
| _ => 0
end.

Fixpoint LS(ls:Digits) :=
match ls with
| h0 => h1
| h1 => d0 0 h0
| d0 n ls0 => d1 n ls0
| d1 n ls0 => d0 (1-(Lx ls0)+n) (LS ls0)
end.

Fixpoint Ln n :=
match n with
| O => h0
| S n0 => LS (Ln n0)
end.

Fixpoint F(n:nat):nat :=
(match n with
| 0 => 0
| S n => (1-Lx (Ln n)+F n)
end)%nat.

Lemma Ln_spec n:
  (d0 (F n) (Ln n) = Ln (n*2+2) /\
   d1 (F n) (Ln n) = Ln (n*2+3)).
Proof.
  induction n; cbn.
  - split; reflexivity.
  - destruct IHn as [I0 I1].
    split.
    + rewrite <-I0.
      reflexivity.
    + rewrite <-I1.
      reflexivity.
Qed.

Lemma F_spec n:
  F (n*2+2) = 2+n /\
  F (n*2+3) = 2+n.
Proof.
  induction n; cbn.
  - split; reflexivity.
  - pose proof (Ln_spec n) as [H0 H1].
    rewrite <-H0,<-H1.
    cbn.
    destruct IHn as [I0 I1].
    lia.
Qed.

Definition S0 a b c :=
  L (Ln a) <{{A}} [1]^^b *> [0] *> [2]^^c *> 0inf.

Lemma LInc n r:
  L (Ln n) <{{A}} [1]^^(Lx (Ln n)) *> r -->*
  L (Ln (1+n)) {{B}}> r.
Proof.
  cbn.
  gen r.
  induction (Ln n); intros; cbn.
  all: er.
  sr.
  destruct d; cbn in *;
  follow IHd; es.
Qed.

Lemma Inc0_2 a b c:
  S0 (a*2+2) (2+b) c -->*
  S0 (a*2+3) b (1+c).
Proof.
  unfold S0.
  epose proof (LInc (a*2+2) _) as HLInc.
  pose proof (Ln_spec a) as [H0 H1].
  rewrite <-H0 in *.
  cbn[Lx] in *.
  rewrite <-lpow_add'.
  cbn.
  follow HLInc. clear HLInc.
  replace (1+(a*2+2)) with (a*2+3) by lia.
  es.
Qed.

Lemma Inc0_3 a b c:
  S0 (a*2+3) (1+b) c -->*
  S0 ((a+1)*2+2) b (1+c).
Proof.
  unfold S0.
  epose proof (LInc (a*2+3) _) as HLInc.
  pose proof (Ln_spec a) as [H0 H1].
  rewrite <-H1 in *.
  cbn[Lx] in *.
  rewrite <-lpow_add'.
  cbn.
  follow HLInc. clear HLInc.
  replace (1+(a*2+3)) with ((a+1)*2+2) by lia.
  es.
Qed.

Lemma Inc0 a b c:
  S0 (a*2+2) (3+b) c -->*
  S0 ((a+1)*2+2) b (2+c).
Proof.
  follow Inc0_2.
  follow Inc0_3.
  finish.
Qed.


Lemma Incs0 n a b c:
  S0 (a*2+2) (n*3+b) c -->*
  S0 ((n+a)*2+2) b (n*2+c).
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma BigStep_0 a c n:
  4+a+c=n*3+0 ->
  S0 ((a*2+2)*2+2) 0 c -->+
  S0 ((n+a)*2+2) 0 (n*2).
Proof.
  intros Hn.
  unfold S0.
  pose proof (Ln_spec (a*2+2)) as [H0 H1].
  rewrite <-H0.
  cbn[L].
  pose proof (F_spec a) as [F0 F1].
  rewrite F0.
  mid10 (S0 (a*2+2) (4+a+c) 0).
  1: es.
  rewrite Hn.
  follow Incs0.
  es.
Qed.

Lemma BigStep_1 a c n:
  3+a+c=n*3+0 ->
  S0 ((a*2+3)*2+2) 0 c -->+
  S0 ((n+(a+1))*2+2) 0 (n*2+1).
Proof.
  intros Hn.
  unfold S0.
  pose proof (Ln_spec (a*2+3)) as [H0 H1].
  rewrite <-H0.
  cbn[L].
  pose proof (F_spec a) as [F0 F1].
  rewrite F1.
  mid10 (S0 (a*2+3) (1+(3+a+c)) 0).
  1: es.
  follow Inc0_3.
  rewrite Hn.
  follow Incs0.
  es.
Qed.

Definition config n :=
  S0 ((n*2+2)*2+2) 0 (n*2+5).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0).
  1: es.
  eapply progress_nonhalt_simple.
  intros n.
  exists (n+1).
  unfold config.
  epose proof (BigStep_0 n (n*2+5) (n+3) _) as H0.
  follow11 H0.
  epose proof (BigStep_1 n (n*2+6) (n+3) _) as H1.
  applys_eq H1; flia.
  Unshelve.
  all: lia.
Qed.

End TM2.


