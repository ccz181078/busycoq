From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RB_1RA1LD_1LE0LD_0LF0LE_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) (f0 (S n))
    ((f0 n)+2) (f0 (S n))).
Definition AD n :=
  (RL A D
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) (f1 n)
    ((f1 n)+2) (f0 n)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) (f1 (S n))
    ((f1 n)+2) (f1 (S n))).
Definition BD n :=
  (RL B D
    ((f1 n)+2) (f0 (S n))
    ((f0 (S n))+2) (f1 n)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DA n :=
  (LR D A
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DB n :=
  (LR D B
    ((f1 n)+2) (f0 n)
    ((f0 n)+2) (f1 n)).
Definition DE n :=
  (LL D E
    ((f1 n)+2) (f0 (S n))
    ((f1 n)+2) (f0 (S n))).
Definition EA n :=
  (LR E A
    ((f0 (S n))+2) (f1 n)
    ((f1 n)+2) (f0 (S n))).
Definition EB n :=
  (LR E B
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition ED n :=
  (LL E D
    ((f0 n)+2) (f1 n)
    ((f0 n)+2) (f1 n)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB HBD); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA HAB); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD' HDB'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED' HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold AB,RR in HAB.
  specialize (HAB 0inf 0inf).
  rewrite lpow_all0 in HAB.
  2: solve_const0_eq.
  rewrite lpow_all0 in HAB.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HAB.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0RA_1RC1LD_1RA0RC_1LE0LD_0LF0LE_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.C.
Notation "'B'" := BB62.A.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) (f0 (S n))
    ((f0 n)+2) (f0 (S n))).
Definition AD n :=
  (RL A D
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) (f1 n)
    ((f1 n)+2) (f0 n)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) (f1 (S n))
    ((f1 n)+2) (f1 (S n))).
Definition BD n :=
  (RL B D
    ((f1 n)+2) (f0 (S n))
    ((f0 (S n))+2) (f1 n)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DA n :=
  (LR D A
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DB n :=
  (LR D B
    ((f1 n)+2) (f0 n)
    ((f0 n)+2) (f1 n)).
Definition DE n :=
  (LL D E
    ((f1 n)+2) (f0 (S n))
    ((f1 n)+2) (f0 (S n))).
Definition EA n :=
  (LR E A
    ((f0 (S n))+2) (f1 n)
    ((f1 n)+2) (f0 (S n))).
Definition EB n :=
  (LR E B
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition ED n :=
  (LL E D
    ((f0 n)+2) (f1 n)
    ((f0 n)+2) (f1 n)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB HBD); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA HAB); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD' HDB'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED' HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold BD,RL in HBD.
  specialize (HBD 0inf 0inf).
  rewrite lpow_all0 in HBD.
  2: solve_const0_eq.
  rewrite lpow_all0 in HBD.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HBD.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge (S n)).
    lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC0LB_1RD---_1RE0RD_1LF0RE_1RD1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.D.
Notation "'B'" := BB62.E.
Notation "'D'" := BB62.A.
Notation "'E'" := BB62.B.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) (f0 (S n))
    ((f0 n)+2) (f0 (S n))).
Definition AD n :=
  (RL A D
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) (f1 n)
    ((f1 n)+2) (f0 n)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) (f1 (S n))
    ((f1 n)+2) (f1 (S n))).
Definition BD n :=
  (RL B D
    ((f1 n)+2) (f0 (S n))
    ((f0 (S n))+2) (f1 n)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DA n :=
  (LR D A
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DB n :=
  (LR D B
    ((f1 n)+2) (f0 n)
    ((f0 n)+2) (f1 n)).
Definition DE n :=
  (LL D E
    ((f1 n)+2) (f0 (S n))
    ((f1 n)+2) (f0 (S n))).
Definition EA n :=
  (LR E A
    ((f0 (S n))+2) (f1 n)
    ((f1 n)+2) (f0 (S n))).
Definition EB n :=
  (LR E B
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition ED n :=
  (LL E D
    ((f0 n)+2) (f1 n)
    ((f0 n)+2) (f1 n)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB HBD); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA HAB); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD' HDB'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED' HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold DB,RL in HDB.
  specialize (HDB 0inf 0inf).
  rewrite lpow_all0 in HDB.
  2: solve_const0_eq.
  rewrite lpow_all0 in HDB.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HDB.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RB_1LD0RC_1RB1LE_1LF0LE_0LA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.B.
Notation "'B'" := BB62.C.
Notation "'D'" := BB62.E.
Notation "'E'" := BB62.F.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) (f0 (S n))
    ((f0 n)+2) (f0 (S n))).
Definition AD n :=
  (RL A D
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) (f1 n)
    ((f1 n)+2) (f0 n)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) (f1 (S n))
    ((f1 n)+2) (f1 (S n))).
Definition BD n :=
  (RL B D
    ((f1 n)+2) (f0 (S n))
    ((f0 (S n))+2) (f1 n)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DA n :=
  (LR D A
    ((f1 n)+2) (f1 n)
    ((f1 n)+2) (f1 n)).
Definition DB n :=
  (LR D B
    ((f1 n)+2) (f0 n)
    ((f0 n)+2) (f1 n)).
Definition DE n :=
  (LL D E
    ((f1 n)+2) (f0 (S n))
    ((f1 n)+2) (f0 (S n))).
Definition EA n :=
  (LR E A
    ((f0 (S n))+2) (f1 n)
    ((f1 n)+2) (f0 (S n))).
Definition EB n :=
  (LR E B
    ((f0 n)+2) (f0 n)
    ((f0 n)+2) (f0 n)).
Definition ED n :=
  (LL E D
    ((f0 n)+2) (f1 n)
    ((f0 n)+2) (f1 n)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB HBD); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA HAB); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD' HDB'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED' HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold EB,RL in HEB.
  specialize (HEB 0inf 0inf).
  rewrite lpow_all0 in HEB.
  2: solve_const0_eq.
  rewrite lpow_all0 in HEB.
  2: solve_const0_eq.
  inverts HEB.
  inverts H; inverts H6.
  cbn in H0.
  rewrite <-const_unfold in H0.
  eexists _,_.
  split.
  1: apply H0.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0RA_1LC0LE_1RD0LC_1RA0RD_1LF0LE_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.A.
Notation "'B'" := BB62.D.
Notation "'D'" := BB62.C.
Notation "'E'" := BB62.E.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)).
Definition AD n :=
  (RL A D
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)).
Definition BA n :=
  (RR B A
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition BD n :=
  (RL B D
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)).
Definition BE n :=
  (RL B E
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)).
Definition DA n :=
  (LR D A
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)).
Definition DB n :=
  (LR D B
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition DE n :=
  (LL D E
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)).
Definition EA n :=
  (LR E A
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition EB n :=
  (LR E B
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition ED n :=
  (LL E D
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE HED); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA' HAE'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold AD,RL in HAD.
  specialize (HAD 0inf 0inf).
  rewrite lpow_all0 in HAD.
  2: solve_const0_eq.
  rewrite lpow_all0 in HAD.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HAD.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RB_1LF0LD_1LE0LD_1RB---_1RA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.B.
Notation "'B'" := BB62.A.
Notation "'D'" := BB62.F.
Notation "'E'" := BB62.D.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)).
Definition AD n :=
  (RL A D
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)).
Definition BA n :=
  (RR B A
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition BD n :=
  (RL B D
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)).
Definition BE n :=
  (RL B E
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)).
Definition DA n :=
  (LR D A
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)).
Definition DB n :=
  (LR D B
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition DE n :=
  (LL D E
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)).
Definition EA n :=
  (LR E A
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition EB n :=
  (LR E B
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition ED n :=
  (LL E D
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE HED); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA' HAE'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold BD,RL in HBD.
  specialize (HBD 0inf 0inf).
  rewrite lpow_all0 in HBD.
  2: solve_const0_eq.
  rewrite lpow_all0 in HBD.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HBD.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC0RB_1LD0RC_1LA0LE_1LF0LE_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.C.
Notation "'B'" := BB62.B.
Notation "'D'" := BB62.A.
Notation "'E'" := BB62.E.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)).
Definition AD n :=
  (RL A D
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)).
Definition BA n :=
  (RR B A
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition BD n :=
  (RL B D
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)).
Definition BE n :=
  (RL B E
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)).
Definition DA n :=
  (LR D A
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)).
Definition DB n :=
  (LR D B
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition DE n :=
  (LL D E
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)).
Definition EA n :=
  (LR E A
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition EB n :=
  (LR E B
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition ED n :=
  (LL E D
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE HED); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA' HAE'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold DA,LR in HDA.
  specialize (HDA 0inf 0inf).
  rewrite lpow_all0 in HDA.
  2: solve_const0_eq.
  rewrite lpow_all0 in HDA.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HDA.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge (S (S n))).
    lia.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC---_1LD0RC_1LE0LA_1RF0LE_1RC0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.C.
Notation "'B'" := BB62.F.
Notation "'D'" := BB62.E.
Notation "'E'" := BB62.A.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)
    ((f1 n)+2) ((f0 n)+(f0 (S n))+3)).
Definition AD n :=
  (RL A D
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)).
Definition BA n :=
  (RR B A
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)
    ((f0 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition BD n :=
  (RL B D
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)).
Definition BE n :=
  (RL B E
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)).
Definition DA n :=
  (LR D A
    ((f1 n)+(f1 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 (S (S n)))+2) ((f1 n)+(f1 (S n))+3)).
Definition DB n :=
  (LR D B
    ((f1 n)+(f1 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f1 n)+(f1 (S n))+3)).
Definition DE n :=
  (LL D E
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)
    ((f1 n)+(f1 (S n))+4) ((f1 (S (S n)))+1)).
Definition EA n :=
  (LR E A
    ((f0 n)+(f0 (S n))+4) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition EB n :=
  (LR E B
    ((f0 n)+(f0 (S n))+4) ((f1 (S n))+1)
    ((f1 (S n))+2) ((f0 n)+(f0 (S n))+3)).
Definition ED n :=
  (LL E D
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)
    ((f0 n)+(f0 (S n))+4) ((f0 (S (S n)))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.

Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE HED); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD' HDE); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA' HAE'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold EA,LR in HEA.
  specialize (HEA 0inf 0inf).
  rewrite lpow_all0 in HEA.
  2: solve_const0_eq.
  rewrite lpow_all0 in HEA.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HEA.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge (S n)).
    lia.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1LB0RA_1RC0LB_1RE0RD_1LA---_1LF0RE_1RA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.A.
Notation "'B'" := BB62.E.
Notation "'D'" := BB62.F.
Notation "'E'" := BB62.B.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) ((f1 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition AD n :=
  (RL A D
    ((f0 (S n))+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) ((f0 (S n))+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition BD n :=
  (RL B D
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition DA n :=
  (LR D A
    ((f0 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 n)+1)).
Definition DB n :=
  (LR D B
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition DE n :=
  (LL D E
    ((f0 n)+2) ((f0 (S n))+1)
    ((f0 n)+2) ((f0 (S n))+1)).
Definition EA n :=
  (LR E A
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition EB n :=
  (LR E B
    ((f1 n)+2) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f1 n)+1)).
Definition ED n :=
  (LL E D
    ((f1 n)+2) ((f1 (S n))+1)
    ((f1 n)+2) ((f1 (S n))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.


Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD HDE); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold AB,RR in HAB.
  specialize (HAB 0inf 0inf).
  rewrite lpow_all0 in HAB.
  2: solve_const0_eq.
  rewrite lpow_all0 in HAB.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HAB.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RA_1RC0LB_1LD0RC_1RE0LD_1RA0RF_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.C.
Notation "'B'" := BB62.A.
Notation "'D'" := BB62.B.
Notation "'E'" := BB62.D.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) ((f1 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition AD n :=
  (RL A D
    ((f0 (S n))+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) ((f0 (S n))+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition BD n :=
  (RL B D
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition DA n :=
  (LR D A
    ((f0 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 n)+1)).
Definition DB n :=
  (LR D B
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition DE n :=
  (LL D E
    ((f0 n)+2) ((f0 (S n))+1)
    ((f0 n)+2) ((f0 (S n))+1)).
Definition EA n :=
  (LR E A
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition EB n :=
  (LR E B
    ((f1 n)+2) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f1 n)+1)).
Definition ED n :=
  (LL E D
    ((f1 n)+2) ((f1 (S n))+1)
    ((f1 n)+2) ((f1 (S n))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.


Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD HDE); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold BE,RL in HBE.
  specialize (HBE 0inf 0inf).
  rewrite lpow_all0 in HBE.
  2: solve_const0_eq.
  rewrite lpow_all0 in HBE.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HBE.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC0RB_1RD0LC_1RE0RF_1LA0RE_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.B.
Notation "'B'" := BB62.E.
Notation "'D'" := BB62.A.
Notation "'E'" := BB62.C.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) ((f1 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition AD n :=
  (RL A D
    ((f0 (S n))+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) ((f0 (S n))+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition BD n :=
  (RL B D
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition DA n :=
  (LR D A
    ((f0 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 n)+1)).
Definition DB n :=
  (LR D B
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition DE n :=
  (LL D E
    ((f0 n)+2) ((f0 (S n))+1)
    ((f0 n)+2) ((f0 (S n))+1)).
Definition EA n :=
  (LR E A
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition EB n :=
  (LR E B
    ((f1 n)+2) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f1 n)+1)).
Definition ED n :=
  (LL E D
    ((f1 n)+2) ((f1 (S n))+1)
    ((f1 n)+2) ((f1 (S n))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.


Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD HDE); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold DE,LL in HDE.
  specialize (HDE 0inf 0inf).
  rewrite lpow_all0 in HDE.
  2: solve_const0_eq.
  rewrite lpow_all0 in HDE.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HDE.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge n).
    lia.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC0RF_1LD0RC_1RE0LD_1LA0RE_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "'A'" := BB62.E.
Notation "'B'" := BB62.C.
Notation "'D'" := BB62.D.
Notation "'E'" := BB62.A.

Definition RR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition LR q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <* [1]^^n1 <* [0]^^n2 {{q2}}> r.

Definition RL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m2 {{q1}}> [0]^^m1 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

Definition LL q1 q2 m1 m2 n1 n2 :=
  forall l r,
  l <* [0]^^m1 <{{q1}} [0]^^m2 *> r -->*
  l <{{q2}} [0]^^n2 *> [1]^^n1 *> r.

(*
A>B>
<D<E
*)
Fixpoint f0(n:nat):nat :=
match n with
| O => O
| S n0 => f0 n0 + f1 n0 + 2
end
with f1(n:nat):nat :=
match n with
| O => 1
| S n0 => f0 n0 + (f1 n0)*2 + 4
end.

Ltac simpl' :=
  unfold RR,RL,LR,LL;
  intros;
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc.

Lemma ADB {a b c d e f g}:
  RL A D a b c d ->
  LR D B g d e f ->
  RR A B a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ABD {a b c d e f g}:
  RR A B a b c d ->
  RL B D g d e f ->
  RL A D (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma ADE {a b c d e f g}:
  RL A D a b c d ->
  LL D E g d e f ->
  RL A E a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BEA {a b c d e f g}:
  RL B E a b c d ->
  LR E A g d e f ->
  RR B A a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BED {a b c d e f g}:
  RL B E a b c d ->
  LL E D g d e f ->
  RL B D a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma BAE {a b c d e f g}:
  RR B A a b c d ->
  RL A E g d e f ->
  RL B E (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBA {a b c d e f g}:
  LR D B a b c d ->
  RR B A g d e f ->
  LR D A a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DEB {a b c d e f g}:
  LL D E a b c d ->
  LR E B g d e f ->
  LR D B (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma DBE {a b c d e f g}:
  LR D B a b c d ->
  RL B E g d e f ->
  LL D E a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EDA {a b c d e f g}:
  LL E D a b c d ->
  LR D A g d e f ->
  LR E A (a+g) b e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EAB {a b c d e f g}:
  LR E A a b c d ->
  RR A B g d e f ->
  LR E B a (b+g) (e+c) f.
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Lemma EBD {a b c d e f g}:
  LR E B a b c d ->
  RL B D g d e f ->
  LL E D a (b+g) e (c+f).
Proof.
  simpl'.
  follow H.
  follow H0.
  es.
Qed.

Definition AB n :=
  (RR A B
    ((f0 n)+2) ((f1 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition AD n :=
  (RL A D
    ((f0 (S n))+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition AE n :=
  (RL A E
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition BA n :=
  (RR B A
    ((f1 n)+2) ((f0 (S n))+1)
    ((f1 n)+2) ((f0 (S n))+1)).
Definition BD n :=
  (RL B D
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition BE n :=
  (RL B E
    ((f1 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f1 n)+1)).
Definition DA n :=
  (LR D A
    ((f0 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f0 n)+1)).
Definition DB n :=
  (LR D B
    ((f0 n)+2) ((f0 n)+1)
    ((f0 n)+2) ((f0 n)+1)).
Definition DE n :=
  (LL D E
    ((f0 n)+2) ((f0 (S n))+1)
    ((f0 n)+2) ((f0 (S n))+1)).
Definition EA n :=
  (LR E A
    ((f1 n)+2) ((f1 n)+1)
    ((f1 n)+2) ((f1 n)+1)).
Definition EB n :=
  (LR E B
    ((f1 n)+2) ((f0 (S n))+1)
    ((f0 (S n))+2) ((f1 n)+1)).
Definition ED n :=
  (LL E D
    ((f1 n)+2) ((f1 (S n))+1)
    ((f1 n)+2) ((f1 (S n))+1)).

Ltac simpl'' :=
  unfold AB,AD,AE,BA,BD,BE,DA,DB,DE,EA,EB,ED in *;
  intros.

Inductive P(n:nat):Prop :=
| P_intro
  (HAB:AB n)
  (HAD:AD n)
  (HAE:AE n)
  (HBA:BA n)
  (HBD:BD n)
  (HBE:BE n)
  (HDA:DA n)
  (HDB:DB n)
  (HDE:DE n)
  (HEA:EA n)
  (HEB:EB n)
  (HED:ED n)
    : P n.


Lemma P_spec n: P n.
Proof.
  induction n.
  1: constructor; simpl''; simpl'; es.
  inverts IHn.
  assert (HAE':AE (S n)) by (simpl''; applys_eq (ADE HAD HDE); cbn; lia).
  assert (HDB':DB (S n)) by (simpl''; applys_eq (DEB HDE HEB); cbn; lia).
  assert (HDA':DA (S n)) by (simpl''; applys_eq (DBA HDB' HBA); cbn; lia).
  assert (HBE':BE (S n)) by (simpl''; applys_eq (BAE HBA HAE'); cbn; lia).
  assert (HBD':BD (S n)) by (simpl''; applys_eq (BED HBE' HED); cbn; lia).
  assert (HAB':AB (S n)) by (simpl''; applys_eq (ADB HAD HDB'); cbn; lia).
  assert (HEA':EA (S n)) by (simpl''; applys_eq (EDA HED HDA'); cbn; lia).
  assert (HBA':BA (S n)) by (simpl''; applys_eq (BEA HBE' HEA'); cbn; lia).
  assert (HEB':EB (S n)) by (simpl''; applys_eq (EAB HEA' HAB'); cbn; lia).
  assert (HAD':AD (S n)) by (simpl''; applys_eq (ABD HAB' HBD'); cbn; lia).
  assert (HED':ED (S n)) by (simpl''; applys_eq (EBD HEB' HBD'); cbn; lia).
  assert (HDE':DE (S n)) by (simpl''; applys_eq (DBE HDB' HBE'); cbn; lia).
  constructor; assumption.
Qed.

Lemma f0_ge n:
  f0 n >= n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (P_spec n) as HP.
  inverts HP.
  unfold EB,LR in HEB.
  specialize (HEB 0inf 0inf).
  rewrite lpow_all0 in HEB.
  2: solve_const0_eq.
  rewrite lpow_all0 in HEB.
  2: solve_const0_eq.
  eexists _,_.
  split.
  1: apply HEB.
  split.
  - solve_sigma_score.
  - epose proof (f0_ge (S n)).
    lia.
Qed.

End TM12.


