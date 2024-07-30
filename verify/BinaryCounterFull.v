Require Import Lia.
Require Import ZArith.
Set Default Goal Selector "!".




Inductive not_full: positive -> Prop :=
| not_full_O x: not_full (xO x)
| not_full_S x: not_full x -> not_full (xI x)
.

Inductive full: positive -> Prop :=
| full_O: full xH
| full_S x: full x -> full (xI x)
.


Open Scope positive.

Lemma full_iff n:
  full n <->
  exists i, n+1 = 2^(Pos.of_succ_nat i).
Proof.
  split; intro H.
  - induction H.
    + exists O. reflexivity.
    + destruct IHfull as [i Hf].
      exists (S i).
      cbn.
      rewrite Pos.pow_succ_r.
      lia.
  - induction n.
    + constructor.
      apply IHn.
      destruct H as [i H].
      destruct i as [|i].
      1: lia.
      cbn in H.
      exists i.
      rewrite Pos.pow_succ_r in H.
      lia.
    + destruct H as [i H].
      destruct i as [|i].
      * lia.
      * cbn in H.
        rewrite Pos.pow_succ_r in H.
        lia.
    + constructor.
Qed.

Fixpoint is_full n :=
match n with
| xH => true
| xI x => is_full x
| xO x => false
end.

Lemma is_full_spec n:
  full n <-> is_full n = true.
Proof.
  split; intro H.
  - induction H; auto 1.
  - induction n; cbn in H.
    + constructor; tauto.
    + congruence.
    + constructor.
Qed.

Lemma is_full_spec' n:
  not_full n <-> is_full n = false.
Proof.
  split; intro H.
  - induction H; auto 1.
  - induction n; cbn in H.
    + constructor; tauto.
    + constructor.
    + congruence.
Qed.

Definition full_discriminate {n}:
  full n -> not_full n -> False.
Proof.
  rewrite is_full_spec.
  rewrite is_full_spec'.
  congruence.
Qed.

Lemma full_2n_not_full {n} (Hf:full n) {m}:
  (n < m ->
  m <= 2*n ->
  not_full m)%positive.
Proof.
  intros H0 H1.
  destruct (is_full m) eqn:E.
  2: rewrite is_full_spec'; apply E.
  rewrite <-is_full_spec in E.
  rewrite full_iff in E,Hf.
  destruct E as [i E].
  destruct Hf as [i' E'].
  assert (i<i'\/i=i'\/S i'=i\/S i'<i)%nat as H by lia.
  pose proof (f_equal Pos.to_nat E') as F'.
  pose proof (f_equal Pos.to_nat E) as F.
  rewrite Pos2Nat.inj_pow,SuccNat2Pos.id_succ in F',F.
  change (Pos.to_nat 2) with (2%nat) in F',F.
  cbn in F,F'.
  destruct H as [H|[H|[H|H]]].
  - rewrite (Nat.pow_lt_mono_r_iff 2) in H; lia.
  - subst. lia.
  - subst. cbn in F. lia.
  - rewrite (Nat.pow_lt_mono_r_iff 2) in H. 2: lia.
    cbn in H.
    lia.
Qed.

Lemma full_S__not_full n:
  full n -> not_full (n+1).
Proof.
  intro Hf.
  induction Hf; cbn; constructor.
Qed.

Close Scope positive.