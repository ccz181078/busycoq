From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB3LA2LB0RA---_2LA4LA3RB0LB0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P1 a b :=
  forall r,
  0inf <* [1]^^a <{{A}} r -->*
  0inf <* [1]^^(1+a) <* [3]^^b {{B}}> r.

Definition S1 a b c l r :=
  l <* [3]^^a <* [0] <{{A}} [2]^^(1+b) *> [0]^^c *> r.

Lemma Inc1 a b c l r:
  S1 (1+a) b (1+c) l r -->*
  S1 a (2+b) c l r.
Proof. es. Qed.

Lemma Incs1 n a b c l r:
  S1 (n+a) b (n+c) l r -->*
  S1 a (n*2+b) c l r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma P1_S a b:
  P1 a b ->
  P1 (1+a) (1+b*2).
Proof.
  unfold P1.
  intros HP1 r.
  rewrite <-lpow_add'.
  step1.
  follow HP1.
  er; sr.
  step1.
  follow HP1.
  mid (S1 (b+0) 0 (b+0) ([1]^^(1+a)*>0inf) r).
  1: es.
  follow Incs1.
  es.
Qed.

Definition config(x:nat*nat*nat) :=
  let '(a,b,c):=x in
  0inf <* [1]^^a <{{A}} [2]^^(1+c) *> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,1,0)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,b,c) => P1 a b).
  2: unfold P1; es.
  intros [[a b] c] HP1.
  eexists (_,_,1+b+c).
  split.
  2: eapply P1_S,HP1.
  unfold config.
  follow HP1.
  es.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB3RA4LB0LA0RA_2RA1LA3LB0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P1 a b :=
  forall r,
  0inf <* [2]^^a <{{B}} r -->*
  0inf <* [2]^^(1+a) <* [3]^^b {{A}}> r.

Definition S1 a b c l r :=
  l <* [3]^^a <* [0] <{{B}} [1]^^(1+b) *> [0]^^c *> r.

Lemma Inc1 a b c l r:
  S1 (1+a) b (1+c) l r -->*
  S1 a (2+b) c l r.
Proof. es. Qed.

Lemma Incs1 n a b c l r:
  S1 (n+a) b (n+c) l r -->*
  S1 a (n*2+b) c l r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma P1_S a b:
  P1 a b ->
  P1 (1+a) (1+b*2).
Proof.
  unfold P1.
  intros HP1 r.
  rewrite <-lpow_add'.
  step1.
  follow HP1.
  er; sr.
  step1.
  follow HP1.
  mid (S1 (b+0) 0 (b+0) ([2]^^(1+a)*>0inf) r).
  1: es.
  follow Incs1.
  es.
Qed.

Definition config(x:nat*nat*nat) :=
  let '(a,b,c):=x in
  0inf <* [2]^^a <{{B}} [1]^^(1+c) *> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (1,1,1)%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=fun '(a,b,c) => P1 a b).
  2: unfold P1; es.
  intros [[a b] c] HP1.
  eexists (_,_,1+b+c).
  split.
  2: eapply P1_S,HP1.
  unfold config.
  follow HP1.
  es.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB2LA3LA1RA0LA_0LA2RB1LB4RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint L n :=
match n with
| O => 0inf
| S n0 => L n0 <* [1]^^(2^n0) <* [4]
end.

Definition S1 a b c l r :=
  l <* [1]^^a <* [2]^^b {{B}}> [2]^^c *> r.

Lemma Inc1 a b c l r:
  S1 (1+a) b (1+c) l r -->*
  S1 a (2+b) c l r.
Proof.
  es.
Qed.

Lemma Incs1 n b l r:
  S1 n b n l r -->*
  S1 0 (n*2+b) 0 l r.
Proof.
  gen b.
  ind n Inc1.
Qed.

Definition P1 n :=
  forall r,
  L n <{{A}} r -->*
  L n <* [1]^^(2^n) {{B}}> r.

Lemma P1_n n:
  P1 n.
Proof.
  unfold P1.
  induction n.
  1: es.
  intros.
  cbn[L].
  er; sr.
  follow IHn.
  follow (Incs1 (2^n) 0).
  er; sr.
  follow IHn.
  rewrite Nat.mul_comm.
  pose proof (Nat.pow_nonzero 2 n).
  replace (2^n) with (1+(2^n-1)) by lia.
  es.
Qed.

Definition config n :=
  L n <{{A}} [2]^^(2^n) *> 0inf.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 0%nat).
  1: es.
  eapply progress_nonhalt_cond with (P:=P1).
  2: unfold P1; es.
  intros n HP1.
  eexists (S n).
  split.
  2: eapply P1_n.
  unfold config.
  follow HP1.
  follow (Incs1 (2^n) 0).
  er; sr.
  follow HP1.
  rewrite Nat.mul_comm.
  pose proof (Nat.pow_nonzero 2 n).
  replace (2^n) with (1+(2^n-1)) by lia.
  es.
Qed.

End TM3.


