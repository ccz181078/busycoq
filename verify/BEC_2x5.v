From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

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

