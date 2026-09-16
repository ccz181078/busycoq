From BusyCoq Require Import Individual62 ES_v2 ES_v3.
Require Import ZifyNat Lia NArith String.
From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia NArith String PeanoNat.
From BusyCoq Require Import Individual62 Eqb.
Require Import NArith Lia ZifyNat.
Require Import NArith Lia ZifyNat Bool.
Require Import ZifyNat Lia String.
Require Import ZifyNat Lia PeanoNat.
From BusyCoq Require Import Individual62 ES_v2.
Require Import ZifyNat Lia.
Require Import NArith ZifyNat Lia PeanoNat List.
Require Import NArith Lia ZifyNat List.
Require Import NArith List.
Require Import NArith List Lia.
Require Import NArith String.
From BusyCoq Require Import Individual62 ES_v2 ES_v3 Eqb.
Require Import ZArith ZifyNat Lia String List.

(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

Module TM11.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{B}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.
Lemma Inc l a b c d r:
  S1 l a (1+b) c (3+d) r -->* S1 l (1+a) b (2+c) d r.
Proof. unfold S1; ES_v2.es. Qed.
Lemma Incs n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->* S1 l (n+a) b (n*2+c) d r.
Proof. gen a b c d; ind n Inc. Qed.
Lemma Empty_b l a c d r:
  S1 l a 0 c (3+d) r -->* l <{{A}} [0]^^a *> [1;0]^^(3+c) *> [0]^^d *> r.
Proof. unfold S1; ES_v2.es. Qed.
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Ltac run := intros; unfold_config; ES_v2.es.

Lemma Inc2 l a b c r:
  S1 l a (1+b) c 2 r -->* S1 l (1+a) b (1+c) 0 ([1]*>r).
Proof. run. Qed.

Lemma Enter l a b c r:
  S1 l a (1+b) c 0 ([1]*>r) -->*
  l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <* [0] <{{B}} [1] *> r.
Proof. run. Qed.

Lemma Return l a b c d r:
  l <* [1]^^a <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <{{A}} [0]^^d *> r -->*
  S1 l a b c d r.
Proof. run. Qed.

Definition P u r r' := forall l,
  l <* [0] <{{B}} [1] *> r -->* l <{{A}} [0]^^u *> r'.

Lemma Call l a b c u r r':
  P u r r' -> S1 l a (1+b) c 0 ([1]*>r) -->* S1 l (1+a) b c u r'.
Proof. intros H; follow Enter; follow H; follow Return; finish. Qed.

Lemma Column k b v r r':
  P (b*3+3+v) r r' ->
  P (k+2+b) ([1;0]^^(k+2+b)*>[0]^^(k*3+3)*>r)
    ([1;0]^^((k+2+b)*2)*>[0]^^v*>r').
Proof.
  intros H l.
  mid (S1 l 0 (k+(2+b)) 0 (k*3+2) r). run.
  follow Incs.
  follow Inc2.
  follow Call.
  follow (Incs b l (k+2) 0 (k*2+1) (3+v) r').
  follow Empty_b.
  finish.
Qed.

Lemma Column3 x d u r r':
  P (u*3) r r' -> 1<=d -> d<x*3 -> x*3<=u+d ->
  P (x*3) ([1;0]^^(x*3)*>[0]^^(d*3)*>r)
    ([1;0]^^(x*6)*>[0]^^((u+d-x*3)*3)*>r').
Proof.
  intros HP Hd Hx Hu.
  applys_eq (Column (d-1) (x*3-d-1) ((u+d-x*3)*3) r r'); try flia.
  applys_eq HP; flia.
Qed.

Lemma Tail n:
  P n ([1;0]^^n*>0inf) ([1;0]^^(n*2+3)*>0inf).
Proof.
  intros l.
  mid (S1 l 0 (n+0) 0 (n*3+3) 0inf).
  unfold S1; rewrite (lpow_all0 [0] (n*3+3)) by solve_const0_eq; simpl_tape; finish.
  follow Incs.
  follow Empty_b.
  finish.
Qed.

Definition L0 := [0]^^33.
Definition L1 := [0;0] ++ [1;0]^^4 ++ [0]^^5 ++ [1;0]^^15 ++ [0]^^60.

Lemma LeftEven r r':
  P 66 r r' -> 0inf <{{A}} L0 *> r -->+ 0inf <{{A}} L1 *> r'.
Proof.
  intros H; unfold L0, L1.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (0inf <* <[1;1;0;0;1;1;0] <* [1]^^7 <* <[0;0;1;0;1]
    <* [0;1]^^10 <* [0] <{{B}} [1] *> r).
  es' & r.
  follow H.
  es' & r'.
Qed.

Lemma LeftOdd r r':
  P 132 r r' -> 0inf <{{A}} L1 *> r -->+
  0inf <{{A}} L0 *> [1;0]^^66 *> [0]^^78 *> r'.
Proof.
  intros H; unfold L0, L1.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (0inf <* [1]^^16 <* [0] <* [1;0]^^18 <* [0;1]^^29 <* [0] <{{B}} [1] *> r).
  es' & r.
  follow H.
  es' & r'.
Qed.

Fixpoint Body (k x d t:nat) : side :=
  match k with
  | O => [1;0]^^(x*3) *> [0]^^(d*3) *> [1;0]^^(t*3) *> 0inf
  | S k => [1;0]^^(x*3) *> [0]^^((x+4)*3) *> Body k (x*4) d t
  end.
Definition Top k x := x*Nat.pow 4 k.
Lemma Top_succ k x: Top (S k) x = Top k (x*4).
Proof. unfold Top; cbn [Nat.pow]; nia. Qed.

Lemma Body_spec k x d t:
  3<=x -> 1<=d -> d<Top k x*3 -> Top k x*3<=t+d ->
  P (x*3) (Body k x d t) (Body k (x*2) (t+d-Top k x*3) (t*2+1)).
Proof.
  gen x; induction k; intros x Hx Hd Hdt Htd; cbn [Body].
  - unfold Top in *; cbn [Nat.pow] in *.
    applys_eq (Column3 x d t ([1;0]^^(t*3)*>0inf)
      ([1;0]^^((t*2+1)*3)*>0inf)); try flia.
    applys_eq (Tail (t*3)); flia.
  - rewrite Top_succ in Hdt, Htd |- *.
    applys_eq (Column3 x (x+4) (x*4) (Body k (x*4) d t)
      (Body k (x*8) (t+d-Top k (x*4)*3) (t*2+1))); try flia.
    applys_eq (IHk (x*4)); flia.
Qed.

Definition Valid x d t := 1<=d /\ d<x*3 /\ x*3+1<=t /\ t<x*6.
Lemma Valid_next x d t:
  Valid x d t -> Valid (x*2) (t+d-x*3) (t*2+1).
Proof. unfold Valid; lia. Qed.

Inductive Inv : Q*tape -> Prop :=
| Ieven k d t: Valid (Top k 22) d t -> Inv (0inf <{{A}} L0 *> Body k 22 d t)
| Iodd k d t: Valid (Top k 44) d t -> Inv (0inf <{{A}} L1 *> Body k 44 d t).

Lemma Inv_step c: Inv c -> exists c', Inv c' /\ c -->+ c'.
Proof.
  intros H; inversion H as [k d t HV|k d t HV]; subst.
  - exists (0inf <{{A}} L1 *> Body k 44 (t+d-Top k 22*3) (t*2+1)); split.
    + apply Iodd. applys_eq (Valid_next _ _ _ HV); unfold Top; flia.
    + apply LeftEven; apply Body_spec; unfold Valid in HV; lia.
  - exists (0inf <{{A}} L0 *> Body (S k) 22 (t+d-Top k 44*3) (t*2+1)); split.
    + apply Ieven. applys_eq (Valid_next _ _ _ HV); unfold Top; cbn [Nat.pow]; flia.
    + apply LeftOdd; apply Body_spec; unfold Valid in HV; lia.
Qed.

Lemma init: c0 -->* 0inf <{{A}} L0 *> Body 0 22 37 103.
Proof.
  eapply without_counter with (n:=N.to_nat 291168%N).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt; [apply Inv_step|].
  apply Ieven; unfold Valid, Top; cbn; lia.
Qed.
End TM11.

Module TM12.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{A}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.
Lemma Inc l a b c d r:
  S1 l a (1+b) c (3+d) r -->* S1 l (1+a) b (2+c) d r.
Proof. unfold S1; ES_v2.es. Qed.
Lemma Incs n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->* S1 l (n+a) b (n*2+c) d r.
Proof. gen a b c d; ind n Inc. Qed.
Lemma Empty_b l a c d r:
  S1 l a 0 c (3+d) r -->* l <{{D}} [0]^^a *> [1;0]^^(3+c) *> [0]^^d *> r.
Proof. unfold S1; ES_v2.es. Qed.
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Ltac run := intros; unfold_config; ES_v2.es.

Lemma Inc2 l a b c r:
  S1 l a (1+b) c 2 r -->* S1 l (1+a) b (1+c) 0 ([1]*>r).
Proof. run. Qed.

Lemma Enter l a b c r:
  S1 l a (1+b) c 0 ([1]*>r) -->*
  l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <* [0] <{{A}} [1] *> r.
Proof. run. Qed.

Lemma Return l a b c d r:
  l <* [1]^^a <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <{{D}} [0]^^d *> r -->*
  S1 l a b c d r.
Proof. run. Qed.

Definition P u r r' := forall l,
  l <* [0] <{{A}} [1] *> r -->* l <{{D}} [0]^^u *> r'.

Lemma Call l a b c u r r':
  P u r r' -> S1 l a (1+b) c 0 ([1]*>r) -->* S1 l (1+a) b c u r'.
Proof. intros H; follow Enter; follow H; follow Return; finish. Qed.

Lemma Column k b v r r':
  P (b*3+3+v) r r' ->
  P (k+2+b) ([1;0]^^(k+2+b)*>[0]^^(k*3+3)*>r)
    ([1;0]^^((k+2+b)*2)*>[0]^^v*>r').
Proof.
  intros H l.
  mid (S1 l 0 (k+(2+b)) 0 (k*3+2) r). run.
  follow Incs.
  follow Inc2.
  follow Call.
  follow (Incs b l (k+2) 0 (k*2+1) (3+v) r').
  follow Empty_b.
  finish.
Qed.

Lemma Column3 x d u r r':
  P (u*3) r r' -> 1<=d -> d<x*3 -> x*3<=u+d ->
  P (x*3) ([1;0]^^(x*3)*>[0]^^(d*3)*>r)
    ([1;0]^^(x*6)*>[0]^^((u+d-x*3)*3)*>r').
Proof.
  intros HP Hd Hx Hu.
  applys_eq (Column (d-1) (x*3-d-1) ((u+d-x*3)*3) r r'); try flia.
  applys_eq HP; flia.
Qed.

Lemma Tail n:
  P n ([1;0]^^n*>0inf) ([1;0]^^(n*2+3)*>0inf).
Proof.
  intros l.
  mid (S1 l 0 (n+0) 0 (n*3+3) 0inf).
  unfold S1; rewrite (lpow_all0 [0] (n*3+3)) by solve_const0_eq; simpl_tape; finish.
  follow Incs.
  follow Empty_b.
  finish.
Qed.

Definition L0 := [0]^^33.
Definition L1 := [0;0] ++ [1;0]^^4 ++ [0]^^5 ++ [1;0]^^15 ++ [0]^^60.

Lemma LeftEven r r':
  P 66 r r' -> 0inf <{{D}} L0 *> r -->+ 0inf <{{D}} L1 *> r'.
Proof.
  intros H; unfold L0, L1.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (0inf <* <[1;1;0;0;1;1;0] <* [1]^^7 <* <[0;0;1;0;1]
    <* [0;1]^^10 <* [0] <{{A}} [1] *> r).
  es' & r.
  follow H.
  es' & r'.
Qed.

Lemma LeftOdd r r':
  P 132 r r' -> 0inf <{{D}} L1 *> r -->+
  0inf <{{D}} L0 *> [1;0]^^66 *> [0]^^78 *> r'.
Proof.
  intros H; unfold L0, L1.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (0inf <* [1]^^16 <* [0] <* [1;0]^^18 <* [0;1]^^29 <* [0] <{{A}} [1] *> r).
  es' & r.
  follow H.
  es' & r'.
Qed.

Fixpoint Body (k x d t:nat) : side :=
  match k with
  | O => [1;0]^^(x*3) *> [0]^^(d*3) *> [1;0]^^(t*3) *> 0inf
  | S k => [1;0]^^(x*3) *> [0]^^((x+4)*3) *> Body k (x*4) d t
  end.
Definition Top k x := x*Nat.pow 4 k.
Lemma Top_succ k x: Top (S k) x = Top k (x*4).
Proof. unfold Top; cbn [Nat.pow]; nia. Qed.

Lemma Body_spec k x d t:
  3<=x -> 1<=d -> d<Top k x*3 -> Top k x*3<=t+d ->
  P (x*3) (Body k x d t) (Body k (x*2) (t+d-Top k x*3) (t*2+1)).
Proof.
  gen x; induction k; intros x Hx Hd Hdt Htd; cbn [Body].
  - unfold Top in *; cbn [Nat.pow] in *.
    applys_eq (Column3 x d t ([1;0]^^(t*3)*>0inf)
      ([1;0]^^((t*2+1)*3)*>0inf)); try flia.
    applys_eq (Tail (t*3)); flia.
  - rewrite Top_succ in Hdt, Htd |- *.
    applys_eq (Column3 x (x+4) (x*4) (Body k (x*4) d t)
      (Body k (x*8) (t+d-Top k (x*4)*3) (t*2+1))); try flia.
    applys_eq (IHk (x*4)); flia.
Qed.

Definition Valid x d t := 1<=d /\ d<x*3 /\ x*3+1<=t /\ t<x*6.
Lemma Valid_next x d t:
  Valid x d t -> Valid (x*2) (t+d-x*3) (t*2+1).
Proof. unfold Valid; lia. Qed.

Inductive Inv : Q*tape -> Prop :=
| Ieven k d t: Valid (Top k 22) d t -> Inv (0inf <{{D}} L0 *> Body k 22 d t)
| Iodd k d t: Valid (Top k 44) d t -> Inv (0inf <{{D}} L1 *> Body k 44 d t).

Lemma Inv_step c: Inv c -> exists c', Inv c' /\ c -->+ c'.
Proof.
  intros H; inversion H as [k d t HV|k d t HV]; subst.
  - exists (0inf <{{D}} L1 *> Body k 44 (t+d-Top k 22*3) (t*2+1)); split.
    + apply Iodd. applys_eq (Valid_next _ _ _ HV); unfold Top; flia.
    + apply LeftEven; apply Body_spec; unfold Valid in HV; lia.
  - exists (0inf <{{D}} L0 *> Body (S k) 22 (t+d-Top k 44*3) (t*2+1)); split.
    + apply Ieven. applys_eq (Valid_next _ _ _ HV); unfold Top; cbn [Nat.pow]; flia.
    + apply LeftOdd; apply Body_spec; unfold Valid in HV; lia.
Qed.

Lemma init: c0 -->* 0inf <{{D}} L0 *> Body 0 22 9 71.
Proof.
  eapply without_counter with (n:=N.to_nat 143263%N).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt; [apply Inv_step|].
  apply Ieven; unfold Valid, Top; cbn; lia.
Qed.
End TM12.

(* Shared definitions from FT7CallRules.v. *)
Module FT7CallRules.
(* Additional returning-call rules for the common TM9--12 graph.
   State names here are those of TM11, not blank-tape equivalence. *)
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.

Module CallRules.
Import TM11.

Lemma Enter1 l a b c t r:
  S1 l a (1+b) c 1 ([1;0]^^(1+t)*>[0;0]*>r) -->*
  S1 (l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c)
    1 t 1 0 r.
Proof. run. Qed.

Lemma Call1 l a b c t u r r':
  (forall l', S1 l' 1 t 1 0 r -->* l' <{{A}} [0]^^u *> r') ->
  S1 l a (1+b) c 1 ([1;0]^^(1+t)*>[0;0]*>r) -->*
  S1 l (1+a) b c u r'.
Proof. intros H; follow Enter1; follow H; follow Return; finish. Qed.

Lemma Merge l a b c d y r:
  S1 l a b c 0 ([1;0]^^y*>[0]^^d*>r) = S1 l a b (c+y) d r.
Proof. unfold S1; simpl_tape; reflexivity. Qed.
End CallRules.
End FT7CallRules.

(* Shared definitions from FT7Cycle.v. *)
Module FT7Cycle.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.
Import FT7CallRules.

Module Cycle.
Import TM11 CallRules.

Definition E a b c d r r' := forall l,
  S1 l a b c d r -->* l <{{A}} [0]^^(a+b) *> r'.

Lemma EInc n a b c d r r':
  E (n+a) b (n*2+c) d r r' -> E a (n+b) c (n*3+d) r r'.
Proof. intros H l; follow Incs; follow H; finish. Qed.

Lemma EEnd a c d r:
  E a 0 c (3+d) r ([1;0]^^(3+c)*>[0]^^d*>r).
Proof. intros l; follow Empty_b; finish. Qed.

Lemma ETail a b c d:
  E a b c d 0inf ([1;0]^^(b*2+c+3)*>0inf).
Proof.
  intros l.
  mid (S1 l a (b+0) c (b*3+3) 0inf).
  unfold S1; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; simpl_tape; finish.
  follow Incs; follow Empty_b; finish.
Qed.

Lemma EMerge a b c d y r r':
  E a b (c+y) d r r' -> E a b c 0 ([1;0]^^y*>[0]^^d*>r) r'.
Proof. intros H l; rewrite Merge; apply H. Qed.

Lemma EP x d r r':
  E 0 x 0 d r r' -> P x ([1;0]^^x*>[0]^^(1+d)*>r) r'.
Proof. intros H l; applys_eq (H l); unfold S1; simpl_tape; flia. Qed.

Lemma ECall2 a b c u r r1 r2:
  P u r r1 -> E (a+2) b (c+1) u r1 r2 -> E a (2+b) c 2 r r2.
Proof.
  intros H1 H2 l.
  follow Inc2; follow Call; follow (H2 l); finish.
Qed.

Lemma ECall1 a b c t d r r1 r2:
  E 1 t 1 d r r1 -> E (a+1) b c (t+1) r1 r2 ->
  E a (1+b) c 1 ([1;0]^^(1+t)*>[0]^^(2+d)*>r) r2.
Proof.
  intros H1 H2 l.
  follow Enter1.
  mid (S1 (l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c) 1 t 1 d r).
  unfold S1; simpl_tape; finish.
  follow H1; follow Return; follow (H2 l); finish.
Qed.

Definition C x d r := [1;0]^^x *> [0]^^d *> r.
Fixpoint W (xs:list (nat*nat)) (t:nat) : side :=
  match xs with
  | nil => [1;0]^^t *> 0inf
  | (x,d)::xs => C x d (W xs t)
  end.
Ltac eqs := cbn [W]; unfold C;
  repeat rewrite (lpow_all0 [0]) by solve_const0_eq;
  first [solve [flia] | simpl_tape; solve [flia]].
Ltac e_inc n :=
  match goal with |- E ?a ?b ?c ?d ?r ?r' =>
    applys_eq (EInc n a (b-n) c (d-n*3) r r'); try eqs end.
Ltac e_end :=
  match goal with |- E ?a ?b ?c ?d ?r ?r' =>
    applys_eq (EEnd a c (d-3) r); eqs end.
Ltac e_tail :=
  match goal with |- E ?a ?b ?c ?d ?r ?r' =>
    applys_eq (ETail a b c d); eqs end.
Ltac e_merge y d r :=
  match goal with |- E ?a ?b ?c ?d0 ?r0 ?r' =>
    applys_eq (EMerge a b c d y r r'); try eqs end.
Ltac e_call2 u r1 :=
  match goal with |- E ?a ?b ?c ?d ?r ?r2 =>
    applys_eq (ECall2 a (b-2) c u r r1 r2); try eqs end.
Ltac e_call1 t d r r1 :=
  match goal with |- E ?a ?b ?c ?d0 ?r0 ?r2 =>
    applys_eq (ECall1 a (b-1) c t d r r1 r2); try eqs end.
Ltac p_start x d r :=
  match goal with |- P ?u ?r0 ?r' =>
    applys_eq (EP x d r r'); try eqs end.
Ltac p_tail n := applys_eq (Tail n); eqs.

Fixpoint G n x r :=
  match n with
  | O => r
  | S n => C (x*3) ((x+4)*3) (G n (x*4) r)
  end.

Lemma G_spec n x r r':
  3<=x -> P (Top n x*3) r r' -> P (x*3) (G n x r) (G n (x*2) r').
Proof.
  gen x; induction n; intros x Hx HP; cbn [G].
  - applys_eq HP; unfold Top; cbn [Nat.pow]; flia.
  - rewrite Top_succ in HP; unfold C.
    applys_eq (Column3 x (x+4) (x*4) (G n (x*4) r) (G n (x*8) r')); try flia.
    applys_eq (IHn (x*4)); try flia; assumption.
Qed.

Lemma G_snoc n x r:
  G (S n) x r = G n x (C (Top n x*3) ((Top n x+4)*3) r).
Proof.
  gen x; induction n; intros x; cbn [G].
  - unfold Top; cbn [Nat.pow]; flia.
  - rewrite Top_succ; f_equal; apply IHn.
Qed.

Lemma G_app n m x r:
  G n x (G m (Top n x) r) = G (n+m) x r.
Proof.
  gen x; induction n; intros x; cbn [G].
  - unfold Top; cbn [Nat.pow]; flia.
  - rewrite Top_succ, IHn; reflexivity.
Qed.

Definition Config (p:bool) n r :=
  0inf <{{A}} (if p then L1 else L0) *> G n (if p then 44 else 22) r.

Lemma Step0 n z r r':
  Top n 22=z -> P (z*3) r r' -> Config false n r -->+ Config true n r'.
Proof.
  intros Hz H; apply LeftEven; apply G_spec; try lia.
  applys_eq H; flia.
Qed.

Lemma Step1 n z r r':
  Top n 22=z -> P (z*6) r r' ->
  Config true n r -->+ Config false n (C (z*3) ((z+4)*3) r').
Proof.
  intros Hz H; unfold Config; rewrite <-Hz, <-G_snoc; cbn [G]; unfold C.
  apply LeftOdd; apply G_spec; try lia.
  applys_eq H; unfold Top in *; flia.
Qed.
End Cycle.
End FT7Cycle.

(* Shared definitions from FT7Stages.v. *)
Module FT7Stages.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.
Import FT7Cycle.
Module Stages.
Import TM11 Cycle.
Lemma Local1 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*12) (W [((z*12),(z*12+12))] (t*3))
    (W [((z*24),(t*3+12-(z*24)))] (t*6+3)).
Proof.
  intros.
  p_start (z*12) (z*12+11) (W [] (t*3)).
  e_inc (z*4+3).
  e_call2 (t*3) (W [] (t*6+3)).
  {
    p_tail (t*3).
  }
  e_inc (z*8-(5)).
  e_end.
Qed.

Lemma Local2 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (W [((z*6),(z*6+12));((z*24),(t*3+12-(z*24)))] (t*6+3))
    (W [((z*12),(z*12+12));((z*48+3),(t*3+8-(z*96)))] (t*6+3)).
Proof.
  intros.
  p_start (z*6) (z*6+11) (W [((z*24),(t*3+12-(z*24)))] (t*6+3)).
  e_inc (z*2+3).
  e_call2 (z*24) (W [((z*48+3),(t*3+8-(z*96)))] (t*6+3)).
  {
    p_start (z*24) (t*3+11-(z*24)) (W [] (t*6+3)).
    e_inc (z*24).
    e_end.
  }
  e_inc (z*4-(5)).
  e_end.
Qed.

Lemma Local3 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*12) (W [((z*12),(z*12+12));((z*48+3),(t*3+8-(z*96)))] (t*6+3))
    (W [((z*24),(z*24+15));((z*96+9),(t*3-(z*240+5)))] (t*6+3)).
Proof.
  intros.
  p_start (z*12) (z*12+11) (W [((z*48+3),(t*3+8-(z*96)))] (t*6+3)).
  e_inc (z*4+3).
  e_call2 (z*48+3) (W [((z*96+9),(t*3-(z*240+5)))] (t*6+3)).
  {
    p_start (z*48+3) (t*3+7-(z*96)) (W [] (t*6+3)).
    e_inc (z*48+3).
    e_end.
  }
  e_inc (z*8-(5)).
  e_end.
Qed.

Lemma Local4 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (W [((z*6),(z*6+12));((z*24),(z*24+15));((z*96+9),(t*3-(z*240+5)))] (t*6+3))
    (W [((z*12),(z*12+12));((z*48),(z*48+24))] (z*192+t*6+24)).
Proof.
  intros.
  p_start (z*6) (z*6+11) (W [((z*24),(z*24+15));((z*96+9),(t*3-(z*240+5)))] (t*6+3)).
  e_inc (z*2+3).
  e_call2 (z*24) (W [((z*48),(z*48+24))] (z*192+t*6+24)).
  {
    p_start (z*24) (z*24+14) (W [((z*96+9),(t*3-(z*240+5)))] (t*6+3)).
    e_inc (z*8+4).
    e_call2 (z*96+9) (W [] (z*192+t*6+24)).
    {
      p_start (z*96+9) (t*3-(z*240+6)) (W [] (t*6+3)).
      e_inc (t-(z*80+2)).
      e_merge (t*6+3) 0%nat 0inf.
      e_tail.
    }
    e_inc (z*16-(6)).
    e_end.
  }
  e_inc (z*4-(5)).
  e_end.
Qed.

Lemma Local5 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*12) (W [((z*12),(z*12+12));((z*48),(z*48+24))] (z*192+t*6+24))
    (W [((z*24),(z*24+12));((z*96),(z*96+t*6+48))] (z*(N.to_nat 384%N)+t*12+51)).
Proof.
  intros.
  p_start (z*12) (z*12+11) (W [((z*48),(z*48+24))] (z*192+t*6+24)).
  e_inc (z*4+3).
  e_call2 (z*48) (W [((z*96),(z*96+t*6+48))] (z*(N.to_nat 384%N)+t*12+51)).
  {
    p_start (z*48) (z*48+23) (W [] (z*192+t*6+24)).
    e_inc (z*16+7).
    e_call2 (z*192+t*6+24) (W [] (z*(N.to_nat 384%N)+t*12+51)).
    {
      p_tail (z*192+t*6+24).
    }
    e_inc (z*32-(9)).
    e_end.
  }
  e_inc (z*8-(5)).
  e_end.
Qed.

Lemma Local6 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*24) (W [((z*24),(z*24+12));((z*96),(z*96+t*6+48))] (z*(N.to_nat 384%N)+t*12+51))
    (W [((z*48),(z*48+12));((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51)).
Proof.
  intros.
  p_start (z*24) (z*24+11) (W [((z*96),(z*96+t*6+48))] (z*(N.to_nat 384%N)+t*12+51)).
  e_inc (z*8+3).
  e_call2 (z*96) (W [((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51)).
  {
    p_start (z*96) (z*96+t*6+47) (W [] (z*(N.to_nat 384%N)+t*12+51)).
    e_inc (z*96).
    e_end.
  }
  e_inc (z*16-(5)).
  e_end.
Qed.

Lemma Local7 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*48) (W [((z*48),(z*48+12));((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51))
    (W [((z*96),(z*96+15));((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51)).
Proof.
  intros.
  p_start (z*48) (z*48+11) (W [((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51)).
  e_inc (z*16+3).
  e_call2 (z*192+3) (W [((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51)).
  {
    p_start (z*192+3) (t*6+43-(z*192)) (W [] (z*(N.to_nat 384%N)+t*12+51)).
    e_inc (z*192+3).
    e_end.
  }
  e_inc (z*32-(5)).
  e_end.
Qed.

Lemma Local8 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*24) (W [((z*24),(z*24+12));((z*96),(z*96+15));((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51))
    (W [((z*48),(z*48+12));((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72)).
Proof.
  intros.
  p_start (z*24) (z*24+11) (W [((z*96),(z*96+15));((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51)).
  e_inc (z*8+3).
  e_call2 (z*96) (W [((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72)).
  {
    p_start (z*96) (z*96+14) (W [((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51)).
    e_inc (z*32+4).
    e_call2 (z*(N.to_nat 384%N)+9) (W [] (z*(N.to_nat 1152%N)+t*12+72)).
    {
      p_start (z*(N.to_nat 384%N)+9) (t*6+30-(z*(N.to_nat 768%N))) (W [] (z*(N.to_nat 384%N)+t*12+51)).
      e_inc (t*2+10-(z*(N.to_nat 256%N))).
      e_merge (z*(N.to_nat 384%N)+t*12+51) 0%nat 0inf.
      e_tail.
    }
    e_inc (z*64-(6)).
    e_end.
  }
  e_inc (z*16-(5)).
  e_end.
Qed.

Lemma Local9 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*48) (W [((z*48),(z*48+12));((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72))
    (W [((z*96),(z*96+12));((z*(N.to_nat 384%N)),(z*(N.to_nat 768%N)+t*12+96))] (z*(N.to_nat 2304%N)+t*24+147)).
Proof.
  intros.
  p_start (z*48) (z*48+11) (W [((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72)).
  e_inc (z*16+3).
  e_call2 (z*192) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 768%N)+t*12+96))] (z*(N.to_nat 2304%N)+t*24+147)).
  {
    p_start (z*192) (z*192+23) (W [] (z*(N.to_nat 1152%N)+t*12+72)).
    e_inc (z*64+7).
    e_call2 (z*(N.to_nat 1152%N)+t*12+72) (W [] (z*(N.to_nat 2304%N)+t*24+147)).
    {
      p_tail (z*(N.to_nat 1152%N)+t*12+72).
    }
    e_inc (z*128-(9)).
    e_end.
  }
  e_inc (z*32-(5)).
  e_end.
Qed.

Lemma Local10 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*96) (W [((z*96),(z*96+12));((z*(N.to_nat 384%N)),(z*(N.to_nat 768%N)+t*12+96))] (z*(N.to_nat 2304%N)+t*24+147))
    (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147)).
Proof.
  intros.
  p_start (z*96) (z*96+11) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 768%N)+t*12+96))] (z*(N.to_nat 2304%N)+t*24+147)).
  e_inc (z*32+3).
  e_call2 (z*(N.to_nat 384%N)) (W [((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147)).
  {
    p_start (z*(N.to_nat 384%N)) (z*(N.to_nat 768%N)+t*12+95) (W [] (z*(N.to_nat 2304%N)+t*24+147)).
    e_inc (z*(N.to_nat 384%N)).
    e_end.
  }
  e_inc (z*64-(5)).
  e_end.
Qed.

Lemma Local11 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*192) (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147))
    (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+15));((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
Proof.
  intros.
  p_start (z*192) (z*192+11) (W [((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147)).
  e_inc (z*64+3).
  e_call2 (z*(N.to_nat 768%N)+3) (W [((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
  {
    p_start (z*(N.to_nat 768%N)+3) (t*12+91-(z*(N.to_nat 384%N))) (W [] (z*(N.to_nat 2304%N)+t*24+147)).
    e_inc (t*4+30-(z*128)).
    e_call1 (z*(N.to_nat 2304%N)+t*24+146) (0%nat) 0inf (W [] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
    {
      e_tail.
    }
    e_inc (z*(N.to_nat 896%N)-(t*4+28)).
    e_end.
  }
  e_inc (z*128-(5)).
  e_end.
Qed.

Lemma Local12 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*96) (W [((z*96),(z*96+12));((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+15));((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N)))
    (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
Proof.
  intros.
  p_start (z*96) (z*96+11) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+15));((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
  e_inc (z*32+3).
  e_call2 (z*(N.to_nat 384%N)) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
  {
    p_start (z*(N.to_nat 384%N)) (z*(N.to_nat 384%N)+14) (W [((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
    e_inc (z*128+4).
    e_call2 (z*(N.to_nat 1536%N)+7) (W [((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
    {
      p_start (z*(N.to_nat 1536%N)+7) (t*36+227-(z*(N.to_nat 384%N))) (W [] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
      e_inc (z*(N.to_nat 1536%N)+7).
      e_end.
    }
    e_inc (z*(N.to_nat 256%N)-(6)).
    e_end.
  }
  e_inc (z*64-(5)).
  e_end.
Qed.

Lemma Local13 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*192) (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N)))
    (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 4608%N)+17),(t*84+(N.to_nat 521%N)-(z*(N.to_nat 1920%N))))] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N))).
Proof.
  intros.
  p_start (z*192) (z*192+11) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
  e_inc (z*64+3).
  e_call2 (z*(N.to_nat 768%N)) (W [((z*(N.to_nat 4608%N)+17),(t*84+(N.to_nat 521%N)-(z*(N.to_nat 1920%N))))] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N))).
  {
    p_start (z*(N.to_nat 768%N)) (z*(N.to_nat 768%N)+21) (W [((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
    e_inc (z*(N.to_nat 256%N)+7).
    e_merge (z*(N.to_nat 3072%N)+17) (t*36+203-(z*(N.to_nat 4992%N))) (W [] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
    e_inc (t*12+67-(z*(N.to_nat 1664%N))).
    e_call2 (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N)) (W [] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N))).
    {
      p_tail (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N)).
    }
    e_inc (z*(N.to_nat 2176%N)-(t*12+76)).
    e_end.
  }
  e_inc (z*128-(5)).
  e_end.
Qed.

Lemma Local14 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 384%N)) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 4608%N)+17),(t*84+(N.to_nat 521%N)-(z*(N.to_nat 1920%N))))] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N)))
    (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 3840%N)+29));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 384%N)) (z*(N.to_nat 384%N)+11) (W [((z*(N.to_nat 4608%N)+17),(t*84+(N.to_nat 521%N)-(z*(N.to_nat 1920%N))))] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N))).
  e_inc (z*128+3).
  e_call2 (z*(N.to_nat 4608%N)+17) (W [((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
  {
    p_start (z*(N.to_nat 4608%N)+17) (t*84+(N.to_nat 520%N)-(z*(N.to_nat 1920%N))) (W [] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N))).
    e_inc (t*28+173-(z*(N.to_nat 640%N))).
    e_call1 (z*(N.to_nat 9216%N)+t*96+(N.to_nat 594%N)) (0%nat) 0inf (W [] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
    {
      e_tail.
    }
    e_inc (z*(N.to_nat 5248%N)-(t*28+157)).
    e_end.
  }
  e_inc (z*(N.to_nat 256%N)-(5)).
  e_end.
Qed.

Lemma Local15 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*192) (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 3840%N)+29));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))
    (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)+3),(z*(N.to_nat 1536%N)+25));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
Proof.
  intros.
  p_start (z*192) (z*192+11) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 3840%N)+29));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
  e_inc (z*64+3).
  e_call2 (z*(N.to_nat 768%N)) (W [((z*(N.to_nat 1536%N)+3),(z*(N.to_nat 1536%N)+25));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
  {
    p_start (z*(N.to_nat 768%N)) (z*(N.to_nat 3840%N)+28) (W [((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
    e_inc (z*(N.to_nat 768%N)).
    e_end.
  }
  e_inc (z*128-(5)).
  e_end.
Qed.

Lemma Local16 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 384%N)) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)+3),(z*(N.to_nat 1536%N)+25));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))
    (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+15));((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 384%N)) (z*(N.to_nat 384%N)+11) (W [((z*(N.to_nat 1536%N)+3),(z*(N.to_nat 1536%N)+25));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
  e_inc (z*128+3).
  e_call2 (z*(N.to_nat 1536%N)+3) (W [((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
  {
    p_start (z*(N.to_nat 1536%N)+3) (z*(N.to_nat 1536%N)+24) (W [((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
    e_inc (z*(N.to_nat 512%N)+8).
    e_merge (z*(N.to_nat 9216%N)+35) (t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))) (W [] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
    e_inc (z*(N.to_nat 1024%N)-(5)).
    e_end.
  }
  e_inc (z*(N.to_nat 256%N)-(5)).
  e_end.
Qed.

Lemma Local17 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*192) (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+15));((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))
    (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)),(z*(N.to_nat 10752%N)+59))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
Proof.
  intros.
  p_start (z*192) (z*192+11) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+15));((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
  e_inc (z*64+3).
  e_call2 (z*(N.to_nat 768%N)) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 10752%N)+59))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
  {
    p_start (z*(N.to_nat 768%N)) (z*(N.to_nat 768%N)+14) (W [((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
    e_inc (z*(N.to_nat 256%N)+4).
    e_call2 (z*(N.to_nat 12288%N)+44) (W [] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
    {
      p_start (z*(N.to_nat 12288%N)+44) (t*180+(N.to_nat 1074%N)-(z*(N.to_nat 9600%N))) (W [] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
      e_inc (t*60+(N.to_nat 358%N)-(z*(N.to_nat 3200%N))).
      e_merge (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)) 0%nat 0inf.
      e_tail.
    }
    e_inc (z*(N.to_nat 512%N)-(6)).
    e_end.
  }
  e_inc (z*128-(5)).
  e_end.
Qed.

Lemma Local18 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 384%N)) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)),(z*(N.to_nat 10752%N)+59))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N)))
    (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 384%N)) (z*(N.to_nat 384%N)+11) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 10752%N)+59))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
  e_inc (z*128+3).
  e_call2 (z*(N.to_nat 1536%N)) (W [((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
  {
    p_start (z*(N.to_nat 1536%N)) (z*(N.to_nat 10752%N)+58) (W [] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
    e_inc (z*(N.to_nat 1536%N)).
    e_end.
  }
  e_inc (z*(N.to_nat 256%N)-(5)).
  e_end.
Qed.

Lemma Local19 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 768%N)) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N)))
    (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+15))] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 768%N)) (z*(N.to_nat 768%N)+11) (W [((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
  e_inc (z*(N.to_nat 256%N)+3).
  e_call2 (z*(N.to_nat 3072%N)+3) (W [] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N))).
  {
    p_start (z*(N.to_nat 3072%N)+3) (z*(N.to_nat 6144%N)+54) (W [] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
    e_inc (z*(N.to_nat 2048%N)+18).
    e_merge (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N)) 0%nat 0inf.
    e_tail.
  }
  e_inc (z*(N.to_nat 512%N)-(5)).
  e_end.
Qed.

Lemma Local20 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 384%N)) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+15))] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N)))
    (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 384%N)) (z*(N.to_nat 384%N)+11) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+15))] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N))).
  e_inc (z*128+3).
  e_call2 (z*(N.to_nat 1536%N)) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  {
    p_start (z*(N.to_nat 1536%N)) (z*(N.to_nat 1536%N)+14) (W [] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N))).
    e_inc (z*(N.to_nat 512%N)+4).
    e_call2 (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N)) (W [] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
    {
      p_tail (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N)).
    }
    e_inc (z*(N.to_nat 1024%N)-(6)).
    e_end.
  }
  e_inc (z*(N.to_nat 256%N)-(5)).
  e_end.
Qed.

Lemma Local21 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 768%N)) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))
    (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)+3),(z*(N.to_nat 36864%N)+t*192+(N.to_nat 1303%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 768%N)) (z*(N.to_nat 768%N)+11) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  e_inc (z*(N.to_nat 256%N)+3).
  e_call2 (z*(N.to_nat 3072%N)) (W [((z*(N.to_nat 6144%N)+3),(z*(N.to_nat 36864%N)+t*192+(N.to_nat 1303%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  {
    p_start (z*(N.to_nat 3072%N)) (z*(N.to_nat 46080%N)+t*192+(N.to_nat 1306%N)) (W [] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
    e_inc (z*(N.to_nat 3072%N)).
    e_end.
  }
  e_inc (z*(N.to_nat 512%N)-(5)).
  e_end.
Qed.

Lemma Local22 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 1536%N)) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)+3),(z*(N.to_nat 36864%N)+t*192+(N.to_nat 1303%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))
    (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+15));((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 1536%N)) (z*(N.to_nat 1536%N)+11) (W [((z*(N.to_nat 6144%N)+3),(z*(N.to_nat 36864%N)+t*192+(N.to_nat 1303%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  e_inc (z*(N.to_nat 512%N)+3).
  e_call2 (z*(N.to_nat 6144%N)+3) (W [((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  {
    p_start (z*(N.to_nat 6144%N)+3) (z*(N.to_nat 36864%N)+t*192+(N.to_nat 1302%N)) (W [] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
    e_inc (z*(N.to_nat 6144%N)+3).
    e_end.
  }
  e_inc (z*(N.to_nat 1024%N)-(5)).
  e_end.
Qed.

Lemma Local23 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 768%N)) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+15));((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))
    (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+24));((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 768%N)) (z*(N.to_nat 768%N)+11) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+15));((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  e_inc (z*(N.to_nat 256%N)+3).
  e_call2 (z*(N.to_nat 3072%N)) (W [((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+24));((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  {
    p_start (z*(N.to_nat 3072%N)) (z*(N.to_nat 3072%N)+14) (W [((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
    e_inc (z*(N.to_nat 1024%N)+4).
    e_call2 (z*(N.to_nat 12288%N)+9) (W [((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
    {
      p_start (z*(N.to_nat 12288%N)+9) (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1289%N)) (W [] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
      e_inc (z*(N.to_nat 12288%N)+9).
      e_end.
    }
    e_inc (z*(N.to_nat 2048%N)-(6)).
    e_end.
  }
  e_inc (z*(N.to_nat 512%N)-(5)).
  e_end.
Qed.

Lemma Local24 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 1536%N)) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+24));((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))
    (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+12));((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 1536%N)) (z*(N.to_nat 1536%N)+11) (W [((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+24));((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
  e_inc (z*(N.to_nat 512%N)+3).
  e_call2 (z*(N.to_nat 6144%N)) (W [((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
  {
    p_start (z*(N.to_nat 6144%N)) (z*(N.to_nat 6144%N)+23) (W [((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
    e_inc (z*(N.to_nat 2048%N)+7).
    e_call2 (z*(N.to_nat 24576%N)+21) (W [((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
    {
      p_start (z*(N.to_nat 24576%N)+21) (t*192+(N.to_nat 1258%N)-(z*(N.to_nat 18432%N))) (W [] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
      e_inc (t*64+(N.to_nat 419%N)-(z*(N.to_nat 6144%N))).
      e_call1 (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2586%N)) (0%nat) 0inf (W [] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
      {
        e_tail.
      }
      e_inc (z*(N.to_nat 30720%N)-(t*64+(N.to_nat 399%N))).
      e_end.
    }
    e_inc (z*(N.to_nat 4096%N)-(9)).
    e_end.
  }
  e_inc (z*(N.to_nat 1024%N)-(5)).
  e_end.
Qed.

Lemma Local25 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 3072%N)) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+12));((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N)))
    (W [((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+12));((z*(N.to_nat 24576%N)),(z*(N.to_nat 24576%N)+88))] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 3072%N)) (z*(N.to_nat 3072%N)+11) (W [((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
  e_inc (z*(N.to_nat 1024%N)+3).
  e_call2 (z*(N.to_nat 12288%N)) (W [((z*(N.to_nat 24576%N)),(z*(N.to_nat 24576%N)+88))] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N))).
  {
    p_start (z*(N.to_nat 12288%N)) (z*(N.to_nat 12288%N)+44) (W [((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
    e_inc (z*(N.to_nat 4096%N)+14).
    e_call2 (z*(N.to_nat 49152%N)+43) (W [] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N))).
    {
      p_start (z*(N.to_nat 49152%N)+43) (z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3780%N)) (W [] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
      e_inc (z*(N.to_nat 2048%N)+t*192+(N.to_nat 1260%N)).
      e_merge (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N)) 0%nat 0inf.
      e_tail.
    }
    e_inc (z*(N.to_nat 8192%N)-(16)).
    e_end.
  }
  e_inc (z*(N.to_nat 2048%N)-(5)).
  e_end.
Qed.

Lemma Local26 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*(N.to_nat 6144%N)) (W [((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+12));((z*(N.to_nat 24576%N)),(z*(N.to_nat 24576%N)+88))] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N)))
    (W [((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+12))] (z*(N.to_nat 344064%N)+t*(N.to_nat 768%N)+(N.to_nat 5268%N))).
Proof.
  intros.
  p_start (z*(N.to_nat 6144%N)) (z*(N.to_nat 6144%N)+11) (W [((z*(N.to_nat 24576%N)),(z*(N.to_nat 24576%N)+88))] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N))).
  e_inc (z*(N.to_nat 2048%N)+3).
  e_call2 (z*(N.to_nat 24576%N)) (W [] (z*(N.to_nat 344064%N)+t*(N.to_nat 768%N)+(N.to_nat 5268%N))).
  {
    p_start (z*(N.to_nat 24576%N)) (z*(N.to_nat 24576%N)+87) (W [] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N))).
    e_inc (z*(N.to_nat 8192%N)+29).
    e_merge (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N)) 0%nat 0inf.
    e_tail.
  }
  e_inc (z*(N.to_nat 4096%N)-(5)).
  e_end.
Qed.

Ltac geqs := unfold Top; cbn [G W Nat.pow]; unfold C; solve [flia].

Definition R1 z t := G 2 z (W [] (t*3)).
Definition R2 z t := G 1 (z*2) (W [((z*24),(t*3+12-(z*24)))] (t*6+3)).
Definition R3 z t := G 2 z (W [((z*48+3),(t*3+8-(z*96)))] (t*6+3)).
Definition R4 z t := G 1 (z*2) (W [((z*24),(z*24+15));((z*96+9),(t*3-(z*240+5)))] (t*6+3)).
Definition R5 z t := G 2 z (W [((z*48),(z*48+24))] (z*192+t*6+24)).
Definition R6 z t := G 2 (z*2) (W [((z*96),(z*96+t*6+48))] (z*(N.to_nat 384%N)+t*12+51)).
Definition R7 z t := G 3 z (W [((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51)).
Definition R8 z t := G 2 (z*2) (W [((z*96),(z*96+15));((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51)).
Definition R9 z t := G 3 z (W [((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72)).
Definition R10 z t := G 3 (z*2) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 768%N)+t*12+96))] (z*(N.to_nat 2304%N)+t*24+147)).
Definition R11 z t := G 4 z (W [((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147)).
Definition R12 z t := G 3 (z*2) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+15));((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
Definition R13 z t := G 4 z (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))).
Definition R14 z t := G 4 (z*2) (W [((z*(N.to_nat 4608%N)+17),(t*84+(N.to_nat 521%N)-(z*(N.to_nat 1920%N))))] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N))).
Definition R15 z t := G 4 z (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 3840%N)+29));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
Definition R16 z t := G 4 (z*2) (W [((z*(N.to_nat 1536%N)+3),(z*(N.to_nat 1536%N)+25));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
Definition R17 z t := G 4 z (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+15));((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))).
Definition R18 z t := G 4 (z*2) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 10752%N)+59))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
Definition R19 z t := G 5 z (W [((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))).
Definition R20 z t := G 4 (z*2) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+15))] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N))).
Definition R21 z t := G 5 z (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Definition R22 z t := G 5 (z*2) (W [((z*(N.to_nat 6144%N)+3),(z*(N.to_nat 36864%N)+t*192+(N.to_nat 1303%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Definition R23 z t := G 5 z (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+15));((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Definition R24 z t := G 5 (z*2) (W [((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+24));((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))).
Definition R25 z t := G 6 z (W [((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))).
Definition R26 z t := G 6 (z*2) (W [((z*(N.to_nat 24576%N)),(z*(N.to_nat 24576%N)+88))] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N))).
Definition R27 z t := G 7 z (W [] (z*(N.to_nat 344064%N)+t*(N.to_nat 768%N)+(N.to_nat 5268%N))).

Definition O1 z t := (R2 z t).
Lemma Flow1 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R1 z t) (O1 z t).
Proof.
  intros; unfold R1, O1, R2.
  applys_eq (G_spec 1 z (W [((z*12),(z*12+12))] (t*3)) (W [((z*24),(t*3+12-(z*24)))] (t*6+3))); try geqs.
  applys_eq (Local1 z t); try geqs; assumption.
Qed.
Lemma Trans1 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R1 z t) -->+ Config true n (R2 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R1 z t) (O1 z t) H); apply Flow1; assumption.
Qed.

Definition O2 z t := (G 1 (z*4) (W [((z*48+3),(t*3+8-(z*96)))] (t*6+3))).
Lemma Flow2 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R2 z t) (O2 z t).
Proof.
  intros; unfold R2, O2.
  applys_eq (G_spec 0 (z*2) (W [((z*6),(z*6+12));((z*24),(t*3+12-(z*24)))] (t*6+3)) (W [((z*12),(z*12+12));((z*48+3),(t*3+8-(z*96)))] (t*6+3))); try geqs.
  applys_eq (Local2 z t); try geqs; assumption.
Qed.
Lemma Trans2 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R2 z t) -->+ Config false n (R3 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R2 z t) (O2 z t) H); apply Flow2; assumption.
Qed.

Definition O3 z t := (R4 z t).
Lemma Flow3 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R3 z t) (O3 z t).
Proof.
  intros; unfold R3, O3, R4.
  applys_eq (G_spec 1 z (W [((z*12),(z*12+12));((z*48+3),(t*3+8-(z*96)))] (t*6+3)) (W [((z*24),(z*24+15));((z*96+9),(t*3-(z*240+5)))] (t*6+3))); try geqs.
  applys_eq (Local3 z t); try geqs; assumption.
Qed.
Lemma Trans3 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R3 z t) -->+ Config true n (R4 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R3 z t) (O3 z t) H); apply Flow3; assumption.
Qed.

Definition O4 z t := (G 1 (z*4) (W [((z*48),(z*48+24))] (z*192+t*6+24))).
Lemma Flow4 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R4 z t) (O4 z t).
Proof.
  intros; unfold R4, O4.
  applys_eq (G_spec 0 (z*2) (W [((z*6),(z*6+12));((z*24),(z*24+15));((z*96+9),(t*3-(z*240+5)))] (t*6+3)) (W [((z*12),(z*12+12));((z*48),(z*48+24))] (z*192+t*6+24))); try geqs.
  applys_eq (Local4 z t); try geqs; assumption.
Qed.
Lemma Trans4 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R4 z t) -->+ Config false n (R5 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R4 z t) (O4 z t) H); apply Flow4; assumption.
Qed.

Definition O5 z t := (R6 z t).
Lemma Flow5 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R5 z t) (O5 z t).
Proof.
  intros; unfold R5, O5, R6.
  applys_eq (G_spec 1 z (W [((z*12),(z*12+12));((z*48),(z*48+24))] (z*192+t*6+24)) (W [((z*24),(z*24+12));((z*96),(z*96+t*6+48))] (z*(N.to_nat 384%N)+t*12+51))); try geqs.
  applys_eq (Local5 z t); try geqs; assumption.
Qed.
Lemma Trans5 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R5 z t) -->+ Config true n (R6 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R5 z t) (O5 z t) H); apply Flow5; assumption.
Qed.

Definition O6 z t := (G 2 (z*4) (W [((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51))).
Lemma Flow6 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R6 z t) (O6 z t).
Proof.
  intros; unfold R6, O6.
  applys_eq (G_spec 1 (z*2) (W [((z*24),(z*24+12));((z*96),(z*96+t*6+48))] (z*(N.to_nat 384%N)+t*12+51)) (W [((z*48),(z*48+12));((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51))); try geqs.
  applys_eq (Local6 z t); try geqs; assumption.
Qed.
Lemma Trans6 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R6 z t) -->+ Config false n (R7 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R6 z t) (O6 z t) H); apply Flow6; assumption.
Qed.

Definition O7 z t := (R8 z t).
Lemma Flow7 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R7 z t) (O7 z t).
Proof.
  intros; unfold R7, O7, R8.
  applys_eq (G_spec 2 z (W [((z*48),(z*48+12));((z*192+3),(t*6+44-(z*192)))] (z*(N.to_nat 384%N)+t*12+51)) (W [((z*96),(z*96+15));((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51))); try geqs.
  applys_eq (Local7 z t); try geqs; assumption.
Qed.
Lemma Trans7 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R7 z t) -->+ Config true n (R8 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R7 z t) (O7 z t) H); apply Flow7; assumption.
Qed.

Definition O8 z t := (G 2 (z*4) (W [((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72))).
Lemma Flow8 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R8 z t) (O8 z t).
Proof.
  intros; unfold R8, O8.
  applys_eq (G_spec 1 (z*2) (W [((z*24),(z*24+12));((z*96),(z*96+15));((z*(N.to_nat 384%N)+9),(t*6+31-(z*(N.to_nat 768%N))))] (z*(N.to_nat 384%N)+t*12+51)) (W [((z*48),(z*48+12));((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72))); try geqs.
  applys_eq (Local8 z t); try geqs; assumption.
Qed.
Lemma Trans8 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R8 z t) -->+ Config false n (R9 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R8 z t) (O8 z t) H); apply Flow8; assumption.
Qed.

Definition O9 z t := (R10 z t).
Lemma Flow9 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R9 z t) (O9 z t).
Proof.
  intros; unfold R9, O9, R10.
  applys_eq (G_spec 2 z (W [((z*48),(z*48+12));((z*192),(z*192+24))] (z*(N.to_nat 1152%N)+t*12+72)) (W [((z*96),(z*96+12));((z*(N.to_nat 384%N)),(z*(N.to_nat 768%N)+t*12+96))] (z*(N.to_nat 2304%N)+t*24+147))); try geqs.
  applys_eq (Local9 z t); try geqs; assumption.
Qed.
Lemma Trans9 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R9 z t) -->+ Config true n (R10 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R9 z t) (O9 z t) H); apply Flow9; assumption.
Qed.

Definition O10 z t := (G 3 (z*4) (W [((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147))).
Lemma Flow10 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R10 z t) (O10 z t).
Proof.
  intros; unfold R10, O10.
  applys_eq (G_spec 2 (z*2) (W [((z*96),(z*96+12));((z*(N.to_nat 384%N)),(z*(N.to_nat 768%N)+t*12+96))] (z*(N.to_nat 2304%N)+t*24+147)) (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147))); try geqs.
  applys_eq (Local10 z t); try geqs; assumption.
Qed.
Lemma Trans10 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R10 z t) -->+ Config false n (R11 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R10 z t) (O10 z t) H); apply Flow10; assumption.
Qed.

Definition O11 z t := (R12 z t).
Lemma Flow11 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R11 z t) (O11 z t).
Proof.
  intros; unfold R11, O11, R12.
  applys_eq (G_spec 3 z (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)+3),(t*12+92-(z*(N.to_nat 384%N))))] (z*(N.to_nat 2304%N)+t*24+147)) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+15));((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N)))); try geqs.
  applys_eq (Local11 z t); try geqs; assumption.
Qed.
Lemma Trans11 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R11 z t) -->+ Config true n (R12 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R11 z t) (O11 z t) H); apply Flow11; assumption.
Qed.

Definition O12 z t := (G 3 (z*4) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N)))).
Lemma Flow12 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R12 z t) (O12 z t).
Proof.
  intros; unfold R12, O12.
  applys_eq (G_spec 2 (z*2) (W [((z*96),(z*96+12));((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+15));((z*(N.to_nat 1536%N)+7),(t*36+228-(z*(N.to_nat 384%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))) (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N)))); try geqs.
  applys_eq (Local12 z t); try geqs; assumption.
Qed.
Lemma Trans12 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R12 z t) -->+ Config false n (R13 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R12 z t) (O12 z t) H); apply Flow12; assumption.
Qed.

Definition O13 z t := (R14 z t).
Lemma Flow13 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R13 z t) (O13 z t).
Proof.
  intros; unfold R13, O13, R14.
  applys_eq (G_spec 3 z (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+22));((z*(N.to_nat 3072%N)+17),(t*36+203-(z*(N.to_nat 4992%N))))] (z*(N.to_nat 4608%N)+t*48+(N.to_nat 296%N))) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 4608%N)+17),(t*84+(N.to_nat 521%N)-(z*(N.to_nat 1920%N))))] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N)))); try geqs.
  applys_eq (Local13 z t); try geqs; assumption.
Qed.
Lemma Trans13 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R13 z t) -->+ Config true n (R14 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R13 z t) (O13 z t) H); apply Flow13; assumption.
Qed.

Definition O14 z t := (G 3 (z*4) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 3840%N)+29));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))).
Lemma Flow14 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R14 z t) (O14 z t).
Proof.
  intros; unfold R14, O14.
  applys_eq (G_spec 3 (z*2) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 4608%N)+17),(t*84+(N.to_nat 521%N)-(z*(N.to_nat 1920%N))))] (z*(N.to_nat 9216%N)+t*96+(N.to_nat 595%N))) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 3840%N)+29));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))); try geqs.
  applys_eq (Local14 z t); try geqs; assumption.
Qed.
Lemma Trans14 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R14 z t) -->+ Config false n (R15 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R14 z t) (O14 z t) H); apply Flow14; assumption.
Qed.

Definition O15 z t := (R16 z t).
Lemma Flow15 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R15 z t) (O15 z t).
Proof.
  intros; unfold R15, O15, R16.
  applys_eq (G_spec 3 z (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 3840%N)+29));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)+3),(z*(N.to_nat 1536%N)+25));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))); try geqs.
  applys_eq (Local15 z t); try geqs; assumption.
Qed.
Lemma Trans15 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R15 z t) -->+ Config true n (R16 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R15 z t) (O15 z t) H); apply Flow15; assumption.
Qed.

Definition O16 z t := (G 3 (z*4) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+15));((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))).
Lemma Flow16 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R16 z t) (O16 z t).
Proof.
  intros; unfold R16, O16.
  applys_eq (G_spec 3 (z*2) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)+3),(z*(N.to_nat 1536%N)+25));((z*(N.to_nat 9216%N)+35),(t*180+(N.to_nat 1063%N)-(z*(N.to_nat 6528%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+15));((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N)))); try geqs.
  applys_eq (Local16 z t); try geqs; assumption.
Qed.
Lemma Trans16 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R16 z t) -->+ Config false n (R17 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R16 z t) (O16 z t) H); apply Flow16; assumption.
Qed.

Definition O17 z t := (R18 z t).
Lemma Flow17 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R17 z t) (O17 z t).
Proof.
  intros; unfold R17, O17, R18.
  applys_eq (G_spec 3 z (W [((z*192),(z*192+12));((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+15));((z*(N.to_nat 12288%N)+44),(t*180+(N.to_nat 1075%N)-(z*(N.to_nat 9600%N))))] (z*(N.to_nat 18432%N)+t*192+(N.to_nat 1192%N))) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)),(z*(N.to_nat 10752%N)+59))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N)))); try geqs.
  applys_eq (Local17 z t); try geqs; assumption.
Qed.
Lemma Trans17 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R17 z t) -->+ Config true n (R18 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R17 z t) (O17 z t) H); apply Flow17; assumption.
Qed.

Definition O18 z t := (G 4 (z*4) (W [((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N)))).
Lemma Flow18 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R18 z t) (O18 z t).
Proof.
  intros; unfold R18, O18.
  applys_eq (G_spec 3 (z*2) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)),(z*(N.to_nat 10752%N)+59))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N)))); try geqs.
  applys_eq (Local18 z t); try geqs; assumption.
Qed.
Lemma Trans18 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R18 z t) -->+ Config false n (R19 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R18 z t) (O18 z t) H); apply Flow18; assumption.
Qed.

Definition O19 z t := (R20 z t).
Lemma Flow19 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R19 z t) (O19 z t).
Proof.
  intros; unfold R19, O19, R20.
  applys_eq (G_spec 4 z (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)+3),(z*(N.to_nat 6144%N)+55))] (z*(N.to_nat 43008%N)+t*192+(N.to_nat 1283%N))) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+15))] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N)))); try geqs.
  applys_eq (Local19 z t); try geqs; assumption.
Qed.
Lemma Trans19 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R19 z t) -->+ Config true n (R20 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R19 z t) (O19 z t) H); apply Flow19; assumption.
Qed.

Definition O20 z t := (G 4 (z*4) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))).
Lemma Flow20 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R20 z t) (O20 z t).
Proof.
  intros; unfold R20, O20.
  applys_eq (G_spec 3 (z*2) (W [((z*(N.to_nat 384%N)),(z*(N.to_nat 384%N)+12));((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+15))] (z*(N.to_nat 49152%N)+t*192+(N.to_nat 1292%N))) (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))); try geqs.
  applys_eq (Local20 z t); try geqs; assumption.
Qed.
Lemma Trans20 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R20 z t) -->+ Config false n (R21 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R20 z t) (O20 z t) H); apply Flow20; assumption.
Qed.

Definition O21 z t := (R22 z t).
Lemma Flow21 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R21 z t) (O21 z t).
Proof.
  intros; unfold R21, O21, R22.
  applys_eq (G_spec 4 z (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)),(z*(N.to_nat 46080%N)+t*192+(N.to_nat 1307%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)+3),(z*(N.to_nat 36864%N)+t*192+(N.to_nat 1303%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))); try geqs.
  applys_eq (Local21 z t); try geqs; assumption.
Qed.
Lemma Trans21 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R21 z t) -->+ Config true n (R22 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R21 z t) (O21 z t) H); apply Flow21; assumption.
Qed.

Definition O22 z t := (G 4 (z*4) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+15));((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))).
Lemma Flow22 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R22 z t) (O22 z t).
Proof.
  intros; unfold R22, O22.
  applys_eq (G_spec 4 (z*2) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)+3),(z*(N.to_nat 36864%N)+t*192+(N.to_nat 1303%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+15));((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))); try geqs.
  applys_eq (Local22 z t); try geqs; assumption.
Qed.
Lemma Trans22 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R22 z t) -->+ Config false n (R23 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R22 z t) (O22 z t) H); apply Flow22; assumption.
Qed.

Definition O23 z t := (R24 z t).
Lemma Flow23 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R23 z t) (O23 z t).
Proof.
  intros; unfold R23, O23, R24.
  applys_eq (G_spec 4 z (W [((z*(N.to_nat 768%N)),(z*(N.to_nat 768%N)+12));((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+15));((z*(N.to_nat 12288%N)+9),(z*(N.to_nat 18432%N)+t*192+(N.to_nat 1290%N)))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+24));((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N)))); try geqs.
  applys_eq (Local23 z t); try geqs; assumption.
Qed.
Lemma Trans23 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R23 z t) -->+ Config true n (R24 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R23 z t) (O23 z t) H); apply Flow23; assumption.
Qed.

Definition O24 z t := (G 5 (z*4) (W [((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N)))).
Lemma Flow24 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R24 z t) (O24 z t).
Proof.
  intros; unfold R24, O24.
  applys_eq (G_spec 4 (z*2) (W [((z*(N.to_nat 1536%N)),(z*(N.to_nat 1536%N)+12));((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+24));((z*(N.to_nat 24576%N)+21),(t*192+(N.to_nat 1259%N)-(z*(N.to_nat 18432%N))))] (z*(N.to_nat 98304%N)+t*(N.to_nat 384%N)+(N.to_nat 2587%N))) (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+12));((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N)))); try geqs.
  applys_eq (Local24 z t); try geqs; assumption.
Qed.
Lemma Trans24 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R24 z t) -->+ Config false n (R25 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R24 z t) (O24 z t) H); apply Flow24; assumption.
Qed.

Definition O25 z t := (R26 z t).
Lemma Flow25 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*3) (R25 z t) (O25 z t).
Proof.
  intros; unfold R25, O25, R26.
  applys_eq (G_spec 5 z (W [((z*(N.to_nat 3072%N)),(z*(N.to_nat 3072%N)+12));((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+45));((z*(N.to_nat 49152%N)+43),(z*(N.to_nat 6144%N)+t*(N.to_nat 576%N)+(N.to_nat 3781%N)))] (z*(N.to_nat 196608%N)+t*(N.to_nat 768%N)+(N.to_nat 5176%N))) (W [((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+12));((z*(N.to_nat 24576%N)),(z*(N.to_nat 24576%N)+88))] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N)))); try geqs.
  applys_eq (Local25 z t); try geqs; assumption.
Qed.
Lemma Trans25 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R25 z t) -->+ Config true n (R26 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step0 n z (R25 z t) (O25 z t) H); apply Flow25; assumption.
Qed.

Definition O26 z t := (G 6 (z*4) (W [] (z*(N.to_nat 344064%N)+t*(N.to_nat 768%N)+(N.to_nat 5268%N)))).
Lemma Flow26 z t: 22<=z -> z*144<=t -> t<=z*160 ->
  P (z*6) (R26 z t) (O26 z t).
Proof.
  intros; unfold R26, O26.
  applys_eq (G_spec 5 (z*2) (W [((z*(N.to_nat 6144%N)),(z*(N.to_nat 6144%N)+12));((z*(N.to_nat 24576%N)),(z*(N.to_nat 24576%N)+88))] (z*(N.to_nat 294912%N)+t*(N.to_nat 768%N)+(N.to_nat 5265%N))) (W [((z*(N.to_nat 12288%N)),(z*(N.to_nat 12288%N)+12))] (z*(N.to_nat 344064%N)+t*(N.to_nat 768%N)+(N.to_nat 5268%N)))); try geqs.
  applys_eq (Local26 z t); try geqs; assumption.
Qed.
Lemma Trans26 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config true n (R26 z t) -->+ Config false n (R27 z t).
Proof.
  intros H H0 H1 H2.
  apply (Step1 n z (R26 z t) (O26 z t) H); apply Flow26; assumption.
Qed.

Lemma Cycle26 n z t: Top n 22=z -> 22<=z -> z*144<=t -> t<=z*160 ->
  Config false n (R1 z t) -->+ Config false n (R27 z t).
Proof.
  intros H H0 H1 H2.
  follow11 (Trans1 n z t H H0 H1 H2).
  follow11 (Trans2 n z t H H0 H1 H2).
  follow11 (Trans3 n z t H H0 H1 H2).
  follow11 (Trans4 n z t H H0 H1 H2).
  follow11 (Trans5 n z t H H0 H1 H2).
  follow11 (Trans6 n z t H H0 H1 H2).
  follow11 (Trans7 n z t H H0 H1 H2).
  follow11 (Trans8 n z t H H0 H1 H2).
  follow11 (Trans9 n z t H H0 H1 H2).
  follow11 (Trans10 n z t H H0 H1 H2).
  follow11 (Trans11 n z t H H0 H1 H2).
  follow11 (Trans12 n z t H H0 H1 H2).
  follow11 (Trans13 n z t H H0 H1 H2).
  follow11 (Trans14 n z t H H0 H1 H2).
  follow11 (Trans15 n z t H H0 H1 H2).
  follow11 (Trans16 n z t H H0 H1 H2).
  follow11 (Trans17 n z t H H0 H1 H2).
  follow11 (Trans18 n z t H H0 H1 H2).
  follow11 (Trans19 n z t H H0 H1 H2).
  follow11 (Trans20 n z t H H0 H1 H2).
  follow11 (Trans21 n z t H H0 H1 H2).
  follow11 (Trans22 n z t H H0 H1 H2).
  follow11 (Trans23 n z t H H0 H1 H2).
  follow11 (Trans24 n z t H H0 H1 H2).
  follow11 (Trans25 n z t H H0 H1 H2).
  apply Trans26; assumption.
Qed.
End Stages.
End FT7Stages.

(* Shared definitions from FT7Proof.v. *)
Module FT7Proof.
Import BusyCoq.Individual62.
Import ZifyNat Lia NArith String PeanoNat.
Import FT7Cycle FT7Stages.

Module Proof9_10.
Import TM11 Cycle Stages.

Definition Entry n t := Config false n (R1 (Top n 22) t).

Lemma Top_ge n: 22<=Top n 22.
Proof. unfold Top; lia. Qed.

Lemma Top_next n: Top (n+5) 22=Top n 22*1024.
Proof. unfold Top; rewrite Nat.pow_add_r; cbn [Nat.pow]; nia. Qed.

Lemma repack n z t:
  Top n 22=z -> Config false n (R27 z t) =
  Entry (n+5) (z*(N.to_nat 114688%N)+t*256+1756).
Proof.
  intros H; unfold Entry, Config, R27, R1; rewrite <-H.
  repeat rewrite G_app; eqs.
Qed.

Lemma entry_step n t:
  Top n 22*144<=t -> t<=Top n 22*160 ->
  Entry n t -->+ Entry (n+5) (Top n 22*(N.to_nat 114688%N)+t*256+1756).
Proof.
  intros H H0; rewrite <-(repack n (Top n 22) t eq_refl).
  apply Cycle26; try assumption; [reflexivity|apply Top_ge].
Qed.

Inductive Inv : Q*tape -> Prop :=
| Intro n t: Top n 22*144<=t -> t<=Top n 22*160 -> Inv (Entry n t).

Lemma Inv_step c: Inv c -> exists c', Inv c' /\ c -->+ c'.
Proof.
  intros H; inversion H; subst.
  exists (Entry (n+5) (Top n 22*(N.to_nat 114688%N)+t*256+1756)); split.
  - constructor; rewrite Top_next; pose proof (Top_ge n); lia.
  - apply entry_step; assumption.
Qed.

Theorem entry_nonhalt n t:
  Top n 22*144<=t -> t<=Top n 22*160 -> ~halts tm (Entry n t).
Proof.
  intros; eapply progress_nonhalt; [apply Inv_step|constructor; assumption].
Qed.
End Proof9_10.
End FT7Proof.

(* Shared definitions from FT7Entry.v. *)
Module FT7Entry.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.
Import FT7Cycle FT7Stages FT7Proof.
Module EntrySteps.
Import TM11 Cycle Stages Proof9_10.
Lemma InitLocal1 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*90))] (t*3)) (W [((z*132),(t*3-(z*108)))] (t*6+z*3)).
Proof.
  intros.
  p_start (z*66) (z*89) (W [] (t*3)).
  e_inc (z*29).
  e_call2 (t*3) (W [] (t*6+z*3)).
  {
    p_tail (t*3).
  }
  e_inc (z*35).
  e_end.
Qed.

Lemma InitTrans1 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*90))] (t*3)) -->+ Config true 0 (W [((z*132),(t*3-(z*108)))] (t*6+z*3)).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*90))] (t*3)) (W [((z*132),(t*3-(z*108)))] (t*6+z*3))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal1 z t); try eqs; assumption.
Qed.

Lemma InitLocal2 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(t*3-(z*108)))] (t*6+z*3)) (W [((z*(N.to_nat 267%N)),(t*3-(z*(N.to_nat 508%N))))] (t*6+z*3)).
Proof.
  intros.
  p_start (z*132) (t*3-(z*109)) (W [] (t*6+z*3)).
  e_inc (z*132).
  e_end.
Qed.

Lemma InitTrans2 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(t*3-(z*108)))] (t*6+z*3)) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 267%N)),(t*3-(z*(N.to_nat 508%N))))] (t*6+z*3)).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(t*3-(z*108)))] (t*6+z*3)) (W [((z*(N.to_nat 267%N)),(t*3-(z*(N.to_nat 508%N))))] (t*6+z*3))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal2 z t); try eqs; assumption.
Qed.

Lemma InitLocal3 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 267%N)),(t*3-(z*(N.to_nat 508%N))))] (t*6+z*3)) (W [((z*132),(z*147));((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3)).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 267%N)),(t*3-(z*(N.to_nat 508%N))))] (t*6+z*3)).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 267%N)) (W [((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3)).
  {
    p_start (z*(N.to_nat 267%N)) (t*3-(z*(N.to_nat 509%N))) (W [] (t*6+z*3)).
    e_inc (z*(N.to_nat 267%N)).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans3 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 267%N)),(t*3-(z*(N.to_nat 508%N))))] (t*6+z*3)) -->+ Config true 0 (W [((z*132),(z*147));((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3)).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 267%N)),(t*3-(z*(N.to_nat 508%N))))] (t*6+z*3)) (W [((z*132),(z*147));((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal3 z t); try eqs; assumption.
Qed.

Lemma InitLocal4 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*147));((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3)) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 288%N)))] (t*6+z*(N.to_nat 1080%N))).
Proof.
  intros.
  p_start (z*132) (z*146) (W [((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3)).
  e_inc (z*48).
  e_call2 (z*(N.to_nat 537%N)) (W [] (t*6+z*(N.to_nat 1080%N))).
  {
    p_start (z*(N.to_nat 537%N)) (t*3-(z*(N.to_nat 1314%N))) (W [] (t*6+z*3)).
    e_inc (t-(z*(N.to_nat 438%N))).
    e_merge (t*6+z*3) 0%nat 0inf.
    e_tail.
  }
  e_inc (z*82).
  e_end.
Qed.

Lemma InitTrans4 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*147));((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3)) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 288%N)))] (t*6+z*(N.to_nat 1080%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*147));((z*(N.to_nat 537%N)),(t*3-(z*(N.to_nat 1313%N))))] (t*6+z*3)) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 288%N)))] (t*6+z*(N.to_nat 1080%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal4 z t); try eqs; assumption.
Qed.

Lemma InitLocal5 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 288%N)))] (t*6+z*(N.to_nat 1080%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 288%N)))] (t*6+z*(N.to_nat 1080%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 287%N)) (W [] (t*6+z*(N.to_nat 1080%N))).
    e_inc (z*95).
    e_call2 (t*6+z*(N.to_nat 1080%N)) (W [] (t*12+z*(N.to_nat 2163%N))).
    {
      p_tail (t*6+z*(N.to_nat 1080%N)).
    }
    e_inc (z*167).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans5 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 288%N)))] (t*6+z*(N.to_nat 1080%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 288%N)))] (t*6+z*(N.to_nat 1080%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal5 z t); try eqs; assumption.
Qed.

Lemma InitLocal6 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))).
  {
    p_start (z*(N.to_nat 528%N)) (t*6+z*(N.to_nat 575%N)) (W [] (t*12+z*(N.to_nat 2163%N))).
    e_inc (z*(N.to_nat 528%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans6 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(t*6+z*(N.to_nat 576%N)))] (t*12+z*(N.to_nat 2163%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal6 z t); try eqs; assumption.
Qed.

Lemma InitLocal7 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1059%N)) (W [((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))).
    {
      p_start (z*(N.to_nat 1059%N)) (t*6-(z*(N.to_nat 1013%N))) (W [] (t*12+z*(N.to_nat 2163%N))).
      e_inc (t*2-(z*(N.to_nat 338%N))).
      e_call1 (t*12+z*(N.to_nat 2162%N)) (0%nat) 0inf (W [] (t*24+z*(N.to_nat 4328%N))).
      {
        e_tail.
      }
      e_inc (z*(N.to_nat 1396%N)-(t*2)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans7 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1059%N)),(t*6-(z*(N.to_nat 1012%N))))] (t*12+z*(N.to_nat 2163%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal7 z t); try eqs; assumption.
Qed.

Lemma InitLocal8 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 542%N)) (W [((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))).
    e_inc (z*180).
    e_call2 (z*(N.to_nat 2119%N)) (W [((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))).
    {
      p_start (z*(N.to_nat 2119%N)) (t*18-(z*(N.to_nat 2029%N))) (W [] (t*24+z*(N.to_nat 4328%N))).
      e_inc (z*(N.to_nat 2119%N)).
      e_end.
    }
    e_inc (z*(N.to_nat 346%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans8 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 543%N)));((z*(N.to_nat 2119%N)),(t*18-(z*(N.to_nat 2028%N))))] (t*24+z*(N.to_nat 4328%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal8 z t); try eqs; assumption.
Qed.

Lemma InitLocal9 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1056%N)) (W [((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))).
    {
      p_start (z*(N.to_nat 1056%N)) (z*(N.to_nat 1077%N)) (W [((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))).
      e_inc (z*(N.to_nat 359%N)).
      e_merge (z*(N.to_nat 4241%N)) (t*18-(z*(N.to_nat 8389%N))) (W [] (t*24+z*(N.to_nat 4328%N))).
      e_inc (t*6-(z*(N.to_nat 2797%N))).
      e_call2 (t*24+z*(N.to_nat 4328%N)) (W [] (t*48+z*(N.to_nat 8659%N))).
      {
        p_tail (t*24+z*(N.to_nat 4328%N)).
      }
      e_inc (z*(N.to_nat 3492%N)-(t*6)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans9 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1078%N)));((z*(N.to_nat 4241%N)),(t*18-(z*(N.to_nat 8389%N))))] (t*24+z*(N.to_nat 4328%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal9 z t); try eqs; assumption.
Qed.

Lemma InitLocal10 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 539%N)) (W [((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))).
    e_inc (z*179).
    e_call2 (z*(N.to_nat 6353%N)) (W [((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
    {
      p_start (z*(N.to_nat 6353%N)) (t*42-(z*(N.to_nat 6152%N))) (W [] (t*48+z*(N.to_nat 8659%N))).
      e_inc (t*14-(z*(N.to_nat 2051%N))).
      e_call1 (t*48+z*(N.to_nat 8658%N)) (0%nat) 0inf (W [] (t*96+z*(N.to_nat 17320%N))).
      {
        e_tail.
      }
      e_inc (z*(N.to_nat 8403%N)-(t*14)).
      e_end.
    }
    e_inc (z*(N.to_nat 347%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans10 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 6353%N)),(t*42-(z*(N.to_nat 6151%N))))] (t*48+z*(N.to_nat 8659%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal10 z t); try eqs; assumption.
Qed.

Lemma InitLocal11 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1056%N)) (W [((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
    {
      p_start (z*(N.to_nat 1056%N)) (z*(N.to_nat 5308%N)) (W [((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
      e_inc (z*(N.to_nat 1056%N)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans11 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 5309%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal11 z t); try eqs; assumption.
Qed.

Lemma InitLocal12 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 539%N)) (W [((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
    e_inc (z*179).
    e_call2 (z*(N.to_nat 2115%N)) (W [((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))).
    {
      p_start (z*(N.to_nat 2115%N)) (z*(N.to_nat 2136%N)) (W [((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))).
      e_inc (z*(N.to_nat 712%N)).
      e_merge (z*(N.to_nat 12707%N)) (t*90-(z*(N.to_nat 16553%N))) (W [] (t*96+z*(N.to_nat 17320%N))).
      e_inc (z*(N.to_nat 1403%N)).
      e_end.
    }
    e_inc (z*(N.to_nat 347%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans12 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2115%N)),(z*(N.to_nat 2137%N)));((z*(N.to_nat 12707%N)),(t*90-(z*(N.to_nat 16553%N))))] (t*96+z*(N.to_nat 17320%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal12 z t); try eqs; assumption.
Qed.

Lemma InitLocal13 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1056%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))).
    {
      p_start (z*(N.to_nat 1056%N)) (z*(N.to_nat 1070%N)) (W [((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))).
      e_inc (z*(N.to_nat 356%N)).
      e_call2 (z*(N.to_nat 16940%N)) (W [] (t*96+z*(N.to_nat 51203%N))).
      {
        p_start (z*(N.to_nat 16940%N)) (t*90-(z*(N.to_nat 20766%N))) (W [] (t*96+z*(N.to_nat 17320%N))).
        e_inc (t*30-(z*(N.to_nat 6922%N))).
        e_merge (t*96+z*(N.to_nat 17320%N)) 0%nat 0inf.
        e_tail.
      }
      e_inc (z*(N.to_nat 698%N)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans13 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1071%N)));((z*(N.to_nat 16940%N)),(t*90-(z*(N.to_nat 20765%N))))] (t*96+z*(N.to_nat 17320%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal13 z t); try eqs; assumption.
Qed.

Lemma InitLocal14 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 539%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))).
    e_inc (z*179).
    e_call2 (z*(N.to_nat 2112%N)) (W [((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))).
    {
      p_start (z*(N.to_nat 2112%N)) (z*(N.to_nat 14842%N)) (W [] (t*96+z*(N.to_nat 51203%N))).
      e_inc (z*(N.to_nat 2112%N)).
      e_end.
    }
    e_inc (z*(N.to_nat 347%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans14 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 14843%N)))] (t*96+z*(N.to_nat 51203%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal14 z t); try eqs; assumption.
Qed.

Lemma InitLocal15 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1056%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))).
    {
      p_start (z*(N.to_nat 1056%N)) (z*(N.to_nat 1067%N)) (W [((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))).
      e_inc (z*(N.to_nat 355%N)).
      e_call2 (z*(N.to_nat 4227%N)) (W [] (t*96+z*(N.to_nat 59660%N))).
      {
        p_start (z*(N.to_nat 4227%N)) (z*(N.to_nat 8502%N)) (W [] (t*96+z*(N.to_nat 51203%N))).
        e_inc (z*(N.to_nat 2834%N)).
        e_merge (t*96+z*(N.to_nat 51203%N)) 0%nat 0inf.
        e_tail.
      }
      e_inc (z*(N.to_nat 699%N)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans15 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4227%N)),(z*(N.to_nat 8503%N)))] (t*96+z*(N.to_nat 51203%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal15 z t); try eqs; assumption.
Qed.

Lemma InitLocal16 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 539%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))).
    e_inc (z*179).
    e_call2 (z*(N.to_nat 2112%N)) (W [((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))).
    {
      p_start (z*(N.to_nat 2112%N)) (z*(N.to_nat 2126%N)) (W [] (t*96+z*(N.to_nat 59660%N))).
      e_inc (z*(N.to_nat 708%N)).
      e_call2 (t*96+z*(N.to_nat 59660%N)) (W [] (t*192+z*(N.to_nat 119323%N))).
      {
        p_tail (t*96+z*(N.to_nat 59660%N)).
      }
      e_inc (z*(N.to_nat 1402%N)).
      e_end.
    }
    e_inc (z*(N.to_nat 347%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans16 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2127%N)))] (t*96+z*(N.to_nat 59660%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal16 z t); try eqs; assumption.
Qed.

Lemma InitLocal17 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1056%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
    {
      p_start (z*(N.to_nat 1056%N)) (z*(N.to_nat 1067%N)) (W [((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))).
      e_inc (z*(N.to_nat 355%N)).
      e_call2 (z*(N.to_nat 4224%N)) (W [((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
      {
        p_start (z*(N.to_nat 4224%N)) (t*96+z*(N.to_nat 55450%N)) (W [] (t*192+z*(N.to_nat 119323%N))).
        e_inc (z*(N.to_nat 4224%N)).
        e_end.
      }
      e_inc (z*(N.to_nat 699%N)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans17 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(t*96+z*(N.to_nat 55451%N)))] (t*192+z*(N.to_nat 119323%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal17 z t); try eqs; assumption.
Qed.

Lemma InitLocal18 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 539%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
    e_inc (z*179).
    e_call2 (z*(N.to_nat 2112%N)) (W [((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
    {
      p_start (z*(N.to_nat 2112%N)) (z*(N.to_nat 2123%N)) (W [((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))).
      e_inc (z*(N.to_nat 707%N)).
      e_call2 (z*(N.to_nat 8451%N)) (W [((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
      {
        p_start (z*(N.to_nat 8451%N)) (t*96+z*(N.to_nat 42774%N)) (W [] (t*192+z*(N.to_nat 119323%N))).
        e_inc (z*(N.to_nat 8451%N)).
        e_end.
      }
      e_inc (z*(N.to_nat 1403%N)).
      e_end.
    }
    e_inc (z*(N.to_nat 347%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans18 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8451%N)),(t*96+z*(N.to_nat 42775%N)))] (t*192+z*(N.to_nat 119323%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal18 z t); try eqs; assumption.
Qed.

Lemma InitLocal19 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1056%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
    {
      p_start (z*(N.to_nat 1056%N)) (z*(N.to_nat 1067%N)) (W [((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
      e_inc (z*(N.to_nat 355%N)).
      e_call2 (z*(N.to_nat 4224%N)) (W [((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
      {
        p_start (z*(N.to_nat 4224%N)) (z*(N.to_nat 4238%N)) (W [((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))).
        e_inc (z*(N.to_nat 1412%N)).
        e_call2 (z*(N.to_nat 16905%N)) (W [((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
        {
          p_start (z*(N.to_nat 16905%N)) (t*96+z*(N.to_nat 17417%N)) (W [] (t*192+z*(N.to_nat 119323%N))).
          e_inc (z*(N.to_nat 16905%N)).
          e_end.
        }
        e_inc (z*(N.to_nat 2810%N)).
        e_end.
      }
      e_inc (z*(N.to_nat 699%N)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans19 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4239%N)));((z*(N.to_nat 16905%N)),(t*96+z*(N.to_nat 17418%N)))] (t*192+z*(N.to_nat 119323%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal19 z t); try eqs; assumption.
Qed.

Lemma InitLocal20 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 539%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
    e_inc (z*179).
    e_call2 (z*(N.to_nat 2112%N)) (W [((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
    {
      p_start (z*(N.to_nat 2112%N)) (z*(N.to_nat 2123%N)) (W [((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
      e_inc (z*(N.to_nat 707%N)).
      e_call2 (z*(N.to_nat 8448%N)) (W [((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
      {
        p_start (z*(N.to_nat 8448%N)) (z*(N.to_nat 8471%N)) (W [((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))).
        e_inc (z*(N.to_nat 2823%N)).
        e_call2 (z*(N.to_nat 33813%N)) (W [((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
        {
          p_start (z*(N.to_nat 33813%N)) (t*96-(z*(N.to_nat 33302%N))) (W [] (t*192+z*(N.to_nat 119323%N))).
          e_inc (t*32-(z*(N.to_nat 11101%N))).
          e_call1 (t*192+z*(N.to_nat 119322%N)) (0%nat) 0inf (W [] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
          {
            e_tail.
          }
          e_inc (z*(N.to_nat 44913%N)-(t*32)).
          e_end.
        }
        e_inc (z*(N.to_nat 5623%N)).
        e_end.
      }
      e_inc (z*(N.to_nat 1403%N)).
      e_end.
    }
    e_inc (z*(N.to_nat 347%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans20 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8472%N)));((z*(N.to_nat 33813%N)),(t*96-(z*(N.to_nat 33301%N))))] (t*192+z*(N.to_nat 119323%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal20 z t); try eqs; assumption.
Qed.

Lemma InitLocal21 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*66) (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
Proof.
  intros.
  p_start (z*66) (z*77) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
  e_inc (z*25).
  e_call2 (z*(N.to_nat 264%N)) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
  {
    p_start (z*(N.to_nat 264%N)) (z*(N.to_nat 275%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
    e_inc (z*91).
    e_call2 (z*(N.to_nat 1056%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
    {
      p_start (z*(N.to_nat 1056%N)) (z*(N.to_nat 1067%N)) (W [((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
      e_inc (z*(N.to_nat 355%N)).
      e_call2 (z*(N.to_nat 4224%N)) (W [((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
      {
        p_start (z*(N.to_nat 4224%N)) (z*(N.to_nat 4235%N)) (W [((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
        e_inc (z*(N.to_nat 1411%N)).
        e_call2 (z*(N.to_nat 16896%N)) (W [((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
        {
          p_start (z*(N.to_nat 16896%N)) (z*(N.to_nat 16940%N)) (W [((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
          e_inc (z*(N.to_nat 5646%N)).
          e_call2 (z*(N.to_nat 67627%N)) (W [] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
          {
            p_start (z*(N.to_nat 67627%N)) (t*(N.to_nat 288%N)-(z*(N.to_nat 15420%N))) (W [] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))).
            e_inc (t*96-(z*(N.to_nat 5140%N))).
            e_merge (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N)) 0%nat 0inf.
            e_tail.
          }
          e_inc (z*(N.to_nat 11248%N)).
          e_end.
        }
        e_inc (z*(N.to_nat 2811%N)).
        e_end.
      }
      e_inc (z*(N.to_nat 699%N)).
      e_end.
    }
    e_inc (z*171).
    e_end.
  }
  e_inc (z*39).
  e_end.
Qed.

Lemma InitTrans21 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))) -->+ Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
Proof.
  intros.
  applys_eq (LeftEven (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16941%N)));((z*(N.to_nat 67627%N)),(t*(N.to_nat 288%N)-(z*(N.to_nat 15419%N))))] (t*(N.to_nat 384%N)+z*(N.to_nat 238648%N))) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal21 z t); try eqs; assumption.
Qed.

Lemma InitLocal22 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  P (z*132) (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16908%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 441492%N))).
Proof.
  intros.
  p_start (z*132) (z*143) (W [((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
  e_inc (z*47).
  e_call2 (z*(N.to_nat 528%N)) (W [((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16908%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 441492%N))).
  {
    p_start (z*(N.to_nat 528%N)) (z*(N.to_nat 539%N)) (W [((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
    e_inc (z*179).
    e_call2 (z*(N.to_nat 2112%N)) (W [((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16908%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 441492%N))).
    {
      p_start (z*(N.to_nat 2112%N)) (z*(N.to_nat 2123%N)) (W [((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
      e_inc (z*(N.to_nat 707%N)).
      e_call2 (z*(N.to_nat 8448%N)) (W [((z*(N.to_nat 16896%N)),(z*(N.to_nat 16908%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 441492%N))).
      {
        p_start (z*(N.to_nat 8448%N)) (z*(N.to_nat 8459%N)) (W [((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
        e_inc (z*(N.to_nat 2819%N)).
        e_call2 (z*(N.to_nat 33792%N)) (W [] (t*(N.to_nat 384%N)+z*(N.to_nat 441492%N))).
        {
          p_start (z*(N.to_nat 33792%N)) (z*(N.to_nat 33879%N)) (W [] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))).
          e_inc (z*(N.to_nat 11293%N)).
          e_merge (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N)) 0%nat 0inf.
          e_tail.
        }
        e_inc (z*(N.to_nat 5627%N)).
        e_end.
      }
      e_inc (z*(N.to_nat 1403%N)).
      e_end.
    }
    e_inc (z*(N.to_nat 347%N)).
    e_end.
  }
  e_inc (z*83).
  e_end.
Qed.

Lemma InitTrans22 (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config true 0 (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))) -->+ Config false 0 (W [((z*66),(z*78));((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16908%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 441492%N))).
Proof.
  intros.
  applys_eq (LeftOdd (W [((z*132),(z*144));((z*(N.to_nat 528%N)),(z*(N.to_nat 540%N)));((z*(N.to_nat 2112%N)),(z*(N.to_nat 2124%N)));((z*(N.to_nat 8448%N)),(z*(N.to_nat 8460%N)));((z*(N.to_nat 33792%N)),(z*(N.to_nat 33880%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 373905%N))) (W [((z*(N.to_nat 264%N)),(z*(N.to_nat 276%N)));((z*(N.to_nat 1056%N)),(z*(N.to_nat 1068%N)));((z*(N.to_nat 4224%N)),(z*(N.to_nat 4236%N)));((z*(N.to_nat 16896%N)),(z*(N.to_nat 16908%N)))] (t*(N.to_nat 384%N)+z*(N.to_nat 441492%N)))); try (unfold Config; cbn [G]; eqs).
  applys_eq (InitLocal22 z t); try eqs; assumption.
Qed.

Lemma finite_entry (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  Config false 0 (W [(z*66,z*90)] (t*3)) -->+
  Entry 3 (t*128+z*N.to_nat 147164%N).
Proof.
  intros H H0 H1.
  follow11 (InitTrans1 z t H H0 H1).
  follow11 (InitTrans2 z t H H0 H1).
  follow11 (InitTrans3 z t H H0 H1).
  follow11 (InitTrans4 z t H H0 H1).
  follow11 (InitTrans5 z t H H0 H1).
  follow11 (InitTrans6 z t H H0 H1).
  follow11 (InitTrans7 z t H H0 H1).
  follow11 (InitTrans8 z t H H0 H1).
  follow11 (InitTrans9 z t H H0 H1).
  follow11 (InitTrans10 z t H H0 H1).
  follow11 (InitTrans11 z t H H0 H1).
  follow11 (InitTrans12 z t H H0 H1).
  follow11 (InitTrans13 z t H H0 H1).
  follow11 (InitTrans14 z t H H0 H1).
  follow11 (InitTrans15 z t H H0 H1).
  follow11 (InitTrans16 z t H H0 H1).
  follow11 (InitTrans17 z t H H0 H1).
  follow11 (InitTrans18 z t H H0 H1).
  follow11 (InitTrans19 z t H H0 H1).
  follow11 (InitTrans20 z t H H0 H1).
  follow11 (InitTrans21 z t H H0 H1).
  applys_eq (InitTrans22 z t H H0 H1); unfold Entry, Config, R1;
    cbn [G W]; unfold C, Top; cbn [Nat.pow]; flia.
Qed.

Theorem early_nonhalt (z t:nat): z=1%nat -> 492<=t -> t<=556 ->
  ~halts tm (Config false 0 (W [(z*66,z*90)] (t*3))).
Proof.
  intros H H0 H1.
  eapply multistep_nonhalt; [apply progress_evstep; apply finite_entry; assumption|].
  apply entry_nonhalt; unfold Top; cbn [Nat.pow]; lia.
Qed.
End EntrySteps.
End FT7Entry.

(* Shared definitions from TM13.FT7TM13Rules.v. *)
Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA0RF_1RB0LD_0LC---").

Module FT7TM13Rules.
(* Local TM13 rules only. No blank-tape nonhalting theorem in this file. *)
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.

Module Rules13.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{B}} [1] *> [1;0]^^b *> [0] *> [1;0]^^c *> [0]^^d *> r.
Ltac run := unfold S1; ES_v2.es.
Lemma Inc l a b c d r:
  S1 l a (1+b) c (3+d) r -->* S1 l (1+a) b (2+c) d r.
Proof. run. Qed.
Lemma Incs n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->* S1 l (n+a) b (n*2+c) d r.
Proof. gen a b c d; ind n Inc. Qed.
Lemma Empty_b l a c d r:
  S1 l a 0 c (3+d) r -->* l <{{A}} [0]^^a *> [1;0]^^(3+c) *> [0]^^d *> r.
Proof. run. Qed.
Lemma Inc2 l a b c r:
  S1 l a (1+b) c 2 r -->* S1 l (1+a) b (1+c) 0 ([1]*>r).
Proof. run. Qed.
Lemma Enter l a b c r:
  S1 l a (1+b) c 0 ([1]*>r) -->*
  l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <* [0] <{{B}} [1] *> r.
Proof. run. Qed.
Lemma Return l a b c d r:
  l <* [1]^^a <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <{{A}} [0]^^d *> r -->*
  S1 l a b c d r.
Proof. run. Qed.
Definition P u r r' := forall l,
  l <* [0] <{{B}} [1] *> r -->* l <{{A}} [0]^^u *> r'.
Lemma Call l a b c u r r':
  P u r r' -> S1 l a (1+b) c 0 ([1]*>r) -->* S1 l (1+a) b c u r'.
Proof. intros H; follow Enter; follow H; follow Return; finish. Qed.

Lemma Column k b v r r':
  P (b*3+3+v) r r' ->
  P (k+2+b) ([1;0]^^(k+2+b)*>[0]^^(k*3+3)*>r)
    ([1;0]^^((k+2+b)*2)*>[0]^^v*>r').
Proof.
  intros H l.
  mid (S1 l 0 (k+(2+b)) 0 (k*3+2) r). run.
  follow Incs; follow Inc2; follow Call.
  follow (Incs b l (k+2) 0 (k*2+1) (3+v) r').
  follow Empty_b; finish.
Qed.
Lemma Column3 x d u r r':
  P (u*3) r r' -> 1<=d -> d<x*3 -> x*3<=u+d ->
  P (x*3) ([1;0]^^(x*3)*>[0]^^(d*3)*>r)
    ([1;0]^^(x*6)*>[0]^^((u+d-x*3)*3)*>r').
Proof.
  intros HP Hd Hx Hu.
  applys_eq (Column (d-1) (x*3-d-1) ((u+d-x*3)*3) r r'); try flia.
  applys_eq HP; flia.
Qed.
Lemma Tail n:
  P n ([1;0]^^n*>0inf) ([1;0]^^(n*2+3)*>0inf).
Proof.
  intros l.
  mid (S1 l 0 (n+0) 0 (n*3+3) 0inf).
  unfold S1; rewrite (lpow_all0 [0] (n*3+3)) by solve_const0_eq; simpl_tape; finish.
  follow Incs; follow Empty_b; finish.
Qed.

Lemma One l a b c r:
  S1 l a (1+b) c 1 ([1;0;1;0]*>r) -->*
  S1 l (1+a) b c 1 ([1;0;1;0;0]*>r).
Proof. run. Qed.
Lemma Empty1 l a c r:
  S1 l a 0 c 1 ([1;0;1;0]*>r) -->*
  l <{{A}} [0]^^a *> [1;0]^^(1+c) *> [0;1;0;1;0;0] *> r.
Proof. run. Qed.
Definition LO := [0]^^6 ++ [1;0]^^6 ++ [0] ++ [1;0]^^2 ++ [0] ++ [1;0]^^37 ++ [0]^^120.
Definition LE := [0]^^6 ++ [1;0]^^5 ++ [0]^^3 ++ [1;0]^^11 ++ [0]^^13 ++ [1;0]^^109 ++ [0]^^300.
Definition K0 := 0inf <* [1]^^7 <* [1;0]^^5 <* <[1;1;0;0;1] <* [0;1]^^8
  <* [1]^^9 <* [0] <* [1;0]^^8 <* [0;1]^^92.
Definition K1 := 0inf <* [1]^^3 <* [0] <* [1;0]^^4 <* <[1;0;1;0;1;1;0;0;1;1;0;1;1;0]
  <* [1;0]^^12 <* [0;1]^^3 <* [1]^^75 <* [0] <* [1;0]^^88 <* [0;1]^^147.

Lemma Left0 r r':
  P 324 r r' -> 0inf <{{A}} LO *> r -[tm]->+ 0inf <{{A}} LE *> r'.
Proof.
  intros H; unfold LO, LE.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (K0 <* [0] <{{B}} [1] *> r).
  unfold K0; es' & r.
  follow H.
  unfold K0; es' & r'.
Qed.
Lemma Left1 d r r':
  P (264+d) r r' -> 0inf <{{A}} LE *> r -[tm]->+
  0inf <{{A}} LO *> [1;0]^^324 *> [0]^^d *> r'.
Proof.
  intros H; unfold LO, LE.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (K1 <* [0] <{{B}} [1] *> r).
  unfold K1; es' & r.
  follow H.
  unfold K1; es' d & r'.
Qed.

(* Counts below are divided by 3; no mod/div computations in the invariant. *)
Definition C x d r := [1;0]^^(x*3) *> [0]^^(d*3) *> r.
Definition E t := [1;0]^^(t*3) *> 0inf.
Inductive Good : nat -> side -> Prop :=
| Good_tail x t: x*3<=t -> t<x*6 -> Good x (E t)
| Good_cons x y d r: x*3<=y -> y<=x*6 -> 1<=d -> d<y*3 ->
    Good y r -> Good x (C y d r).

Lemma Good_step x r: Good x r ->
  exists u r', x*3<=u /\ u<=x*6 /\ P (u*3) r r' /\ Good (x*2) r'.
Proof.
  intros HG; induction HG.
  - exists t, (E (t*2+1)); repeat apply conj; try lia.
    + unfold E; applys_eq (Tail (t*3)); flia.
    + apply Good_tail; lia.
  - destruct IHHG as [u [r' [Hu [Hu' [HP Hr]]]]].
    exists y, (C (y*2) (u+d-y*3) r'); repeat apply conj; try lia.
    + unfold C; applys_eq (Column3 y d u r r'); try assumption; flia.
    + apply Good_cons; try lia; exact Hr.
Qed.

Inductive Inv : Q*tape -> Prop :=
| IO d r: 1<=d -> d<324 -> Good 108 r -> Inv (0inf <{{A}} LO *> C 108 d r)
| IE d r: 1<=d -> d<648 -> Good 216 r -> Inv (0inf <{{A}} LE *> C 216 d r).
Lemma Inv_step c: Inv c -> exists c', Inv c' /\ c -[tm]->+ c'.
Proof.
  intros H; destruct H as [d r Hd Hd' HG|d r Hd Hd' HG];
    destruct (Good_step _ _ HG) as [u [r' [Hu [Hu' [HP Hr]]]]].
  - exists (0inf <{{A}} LE *> C 216 (u+d-324) r'); split.
    + apply IE; try lia; exact Hr.
    + apply Left0; unfold C; applys_eq (Column3 108 d u r r'); try assumption; flia.
  - exists (0inf <{{A}} LO *> C 108 128 (C 432 (u+d-648) r')); split.
    + apply IO; try lia. apply Good_cons; try lia; exact Hr.
    + apply (Left1 384); unfold C; applys_eq (Column3 216 d u r r'); try assumption; flia.
Qed.
Theorem region_nonhalt c: Inv c -> ~halts tm c.
Proof. eapply progress_nonhalt; apply Inv_step. Qed.
End Rules13.
End FT7TM13Rules.

(* Shared definitions from FT7Compute.v. *)
Module FT7Compute.
(* Finite returning-call checker. Binary counters are never expanded while
   computing; [denote] is used only in the specification. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat.
Import FT7TM13Rules.

Module Compute13.
Import FT7TM13Rules.Rules13.
Local Open Scope N_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.
Inductive Tape := Blank | Zeros (n:N) (r:Tape) | Pairs (n:N) (r:Tape) | OneBit (r:Tape).
Fixpoint denote r : side :=
  match r with
  | Blank => 0inf
  | Zeros n r => [0%sym]^^(N.to_nat n) *> denote r
  | Pairs n r => [1%sym;0%sym]^^(N.to_nat n) *> denote r
  | OneBit r => [1%sym] *> denote r
  end.
Definition zeros n r :=
  if n =? 0 then r else
  match r with Blank => Blank | Zeros m s => Zeros (n+m) s | _ => Zeros n r end.
Definition pairs n r :=
  if n =? 0 then r else
  match r with Pairs m s => Pairs (n+m) s | _ => Pairs n r end.
Definition push b r :=
  match b with
  | S0 => zeros 1 r
  | BusyCoq.BB62.S1 => match r with
          | Blank => Pairs 1 Blank
          | Zeros n s => if n =? 0 then OneBit r else pairs 1 (zeros (n-1) s)
          | _ => OneBit r
          end
  end.
Fixpoint pop r : Sym*Tape :=
  match r with
  | Blank => (S0,Blank)
  | OneBit s => (1%sym,s)
  | Zeros n s => if n =? 0 then pop s else (S0,zeros (n-1) s)
  | Pairs n s => if n =? 0 then pop s else (1%sym,zeros 1 (pairs (n-1) s))
  end.

Definition send (f:N->N->N->Tape->option Tape) r : option (N*Tape) :=
  match r with
  | Blank => Some (0,Pairs 3 Blank)
  | Pairs x Blank => Some (x,Pairs (x*2+3) Blank)
  | Pairs x (Zeros d s) =>
      if d =? 0 then None else
      match f x 0 (d-1) s with Some s' => Some (x,s') | None => None end
  | _ => None
  end.
Definition resume (f:N->N->N->Tape->option Tape) (b c d:N) r : option Tape :=
        if (b =? 0) && (3 <=? d) then Some (pairs (c+3) (zeros (d-3) r)) else
        if d =? 0 then
          match r with
          | Pairs y (Zeros z s) => f b (c+y) z s
          | Pairs y Blank => Some (Pairs (b*2+c+y+3) Blank)
          | _ => None
          end
        else if d =? 1 then
          match r with
          | Pairs y s => if 2 <=? y then
              Some (pairs (c+1) (zeros 1 (pairs 2 (zeros (b+1) (pairs (y-2) s)))))
              else None
          | _ => None
          end
        else if (d =? 2) && (2 <=? b) then
          match send f r with
          | Some (u,s) => f (b-2) (c+1) u s
          | None => None
          end
        else None.
Fixpoint run fuel (b c d:N) r : option Tape :=
  match fuel with
  | O => None
  | S fuel =>
    match r with
    | Blank => Some (Pairs (b*2+c+3) Blank)
    | _ =>
      let n := N.min b (d/3) in
      if (n <=? b) && (n*3 <=? d) then
        resume (run fuel) (b-n) (c+n*2) (d-n*3) r
      else None
    end
  end.

Definition State := (Q * list Sym * Tape)%type.
Definition config (s:State) := let '(q,l,r) := s in (l *> 0inf) {{q}}> denote r.
Definition raw (s:State) : option State :=
  let '(q,l,r) := s in let '(b,r) := pop r in
  match tm (q,b) with
  | None => None
  | Some (b,R,q') => Some (q',b::l,r)
  | Some (b,L,q') => match l with
                    | nil => Some (q',nil,push S0 (push b r))
                    | a::l => Some (q',l,push a (push b r))
                    end
  end.
Definition call_step fuel (s:State) : option State :=
  let '(q,l,r) := s in
  match q,pop r with
  | B,(S0,r) => match pop r with
    | (BusyCoq.BB62.S1,r) => match send (run fuel) r with
      | Some (u,r) =>
          match l with
          | nil => Some (A,nil,push S0 (zeros u r))
          | a::l => Some (A,l,push a (zeros u r))
          end
      | None => None
      end
    | _ => None
    end
  | _,_ => None
  end.
Definition machine_step fuel s :=
  match call_step fuel s with Some s' => Some s' | None => raw s end.

(* Once the finite left context reaches LO/LE, only complete stages are used. *)
Fixpoint strip (w:list Sym) r : option Tape :=
  match w with
  | nil => Some r
  | b::w => let '(a,s) := pop r in if sym_eqb a b then strip w s else None
  end.
Definition Stage := (bool*Tape)%type.
Definition stage_config (s:Stage) :=
  let '(p,r) := s in 0inf <{{A}} (if p then LE else LO) *> denote r.
Definition stage_step fuel (s:Stage) : option Stage :=
  let '(p,r) := s in
  match send (run fuel) r with
  | None => None
  | Some (u,r) => if p then
      if 264 <=? u then Some (false,pairs 324 (zeros (u-264) r)) else None
    else if u =? 324 then Some (true,r) else None
  end.
Fixpoint goodb (x:N) r : bool :=
  match r with
  | Pairs t Blank => let v:=t/3 in
      (t =? v*3) && (x*3 <=? v) && (v <? x*6)
  | Pairs y (Zeros z s) => let v:=y/3 in let d:=z/3 in
      (y =? v*3) && (z =? d*3) && (x*3 <=? v) && (v <=? x*6) &&
      (1 <=? d) && (d <? v*3) && goodb v s
  | _ => false
  end.
Definition regionb (s:Stage) : bool :=
  let '(p,r) := s in let x := if p then 216 else 108 in
  match r with
  | Pairs y (Zeros z s) => let d:=z/3 in
      (y =? x*3) && (z =? d*3) && (1 <=? d) && (d <? x*3) && goodb x s
  | _ => false
  end.
Fixpoint check_stages count fuel s : bool :=
  if regionb s then true else
  match count with
  | O => false
  | S count => match stage_step fuel s with
               | Some s => check_stages count fuel s
               | None => false
               end
  end.
Definition seed13 : Stage := (false,
  Pairs 324 (Zeros 384 (Pairs 1296 (Zeros 4025 (Pairs 3919 (Zeros 1
  (Pairs 2 (Zeros 3313 (Pairs 20661 Blank))))))))).
Definition seed14 : Stage := (false,
  Pairs 324 (Zeros 384 (Pairs 1296 (Zeros 7108 (Pairs 50548 Blank))))).
Fixpoint tape_eqb r s : bool :=
  match r,s with
  | Blank,Blank => true
  | Zeros n r,Zeros m s | Pairs n r,Pairs m s => (n =? m) && tape_eqb r s
  | OneBit r,OneBit s => tape_eqb r s
  | _,_ => false
  end.
Fixpoint allzero (l:list Sym) : bool :=
  match l with nil => true | S0::l => allzero l | _ => false end.
Definition at_stage (s:State) (target:Stage) : bool :=
  let '(p,t) := target in
  match s with
  | (A,l,r) => if allzero l then
      match pop r with
      | (S0,r) => match strip (if p then LE else LO) r with
                  | Some r => tape_eqb r t
                  | None => false
                  end
      | _ => false
      end
    else false
  | _ => false
  end.
Fixpoint seek count fuel s target : bool :=
  if at_stage s target then true else
  match count with
  | O => false
  | S count => match machine_step fuel s with
               | Some s => seek count fuel s target
               | None => false
               end
  end.
Definition check count stages fuel q target :=
  seek count fuel (q,nil,Blank) target && check_stages stages fuel target.
End Compute13.
End FT7Compute.

(* Shared definitions from FT7ComputeSpec.v. *)
Module FT7ComputeSpec.
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat Bool.
Import FT7TM13Rules FT7Compute.

Module ComputeSpec13.
Import FT7TM13Rules.Rules13 Compute13.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).

Lemma zeros_spec n r: denote (zeros n r) = [0]^^(nn n) *> denote r.
Proof.
  unfold zeros; destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; reflexivity.
  - destruct r; cbn [denote]; try reflexivity.
    + rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
    + rewrite N2Nat.inj_add; simpl_tape; reflexivity.
Qed.
Lemma pairs_spec n r: denote (pairs n r) = [1;0]^^(nn n) *> denote r.
Proof.
  unfold pairs; destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; reflexivity.
  - destruct r; cbn [denote]; try reflexivity.
    rewrite N2Nat.inj_add; simpl_tape; reflexivity.
Qed.
Lemma nn_pred n: (n<>0)%N -> nn n = 1+nn (n-1)%N.
Proof. lia. Qed.
Lemma push_spec b r: denote (push b r) = b >> denote r.
Proof.
  destruct b; cbn [push].
  - rewrite zeros_spec; reflexivity.
  - destruct r; cbn [push denote]; try reflexivity.
    + simpl_tape; reflexivity.
    + destruct (N.eqb n 0) eqn:E; [reflexivity|].
      apply N.eqb_neq in E.
      rewrite pairs_spec, zeros_spec, (nn_pred _ E); reflexivity.
Qed.
Lemma pop_spec r: let '(b,s):=pop r in denote r = b >> denote s.
Proof.
  induction r; cbn [pop denote].
  - rewrite <-const_unfold; reflexivity.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; exact IHr.
    + apply N.eqb_neq in E; rewrite zeros_spec, (nn_pred _ E); reflexivity.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; exact IHr.
    + apply N.eqb_neq in E; rewrite zeros_spec, pairs_spec, (nn_pred _ E); reflexivity.
  - reflexivity.
Qed.

(* Generalising the zero counter keeps each iteration's extra zero inside
   one power; no explicit reassociation of a growing concrete word. *)
Lemma Ones l a b c n r:
  S1 l a b c 1 ([1;0;1;0]*>[0]^^n*>r) -[tm]->*
  l <{{A}} [0]^^(a+b) *> [1;0]^^(1+c) *> [0;1;0;1;0] *> [0]^^(1+b+n) *> r.
Proof.
  gen a n; induction b; intros.
  - follow Empty1; finish; flia.
  - follow One; follow (IHb (1+a) (1+n)); finish; flia.
Qed.

Lemma RunTail l a b c d:
  S1 l a b c d 0inf -[tm]->* l <{{A}} [0]^^(a+b) *> [1;0]^^(b*2+c+3) *> 0inf.
Proof.
  mid (S1 l a (b+0) c (b*3+3) 0inf).
  - unfold S1; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; finish.
  - follow Incs; follow Empty_b; finish; flia.
Qed.
Definition RunSpec f := forall b c d r r' a l,
  f b c d r = Some r' ->
  S1 l a (nn b) (nn c) (nn d) (denote r) -[tm]->*
  l <{{A}} [0]^^(a+nn b) *> denote r'.
Lemma send_spec f: RunSpec f -> forall r u s,
  send f r = Some (u,s) -> P (nn u) (denote r) (denote s).
Proof.
  intros HF r u s; destruct r as [|d r|x r|r]; cbn [send]; try discriminate.
  - intros H; inversion H; subst; apply (Tail 0).
  - destruct r as [|d r|d r|r]; try discriminate.
    + intros H; inversion H; subst; cbn [denote].
      rewrite N2Nat.inj_add, N2Nat.inj_mul; apply Tail.
    + destruct (N.eqb d 0) eqn:Hd; try discriminate.
      destruct (f x 0%N (d-1)%N r) eqn:E; try discriminate.
      intros H l; injection H as Hu Hs; subst u s; apply N.eqb_neq in Hd.
      mid (S1 l 0 (nn x) 0 (nn (d-1)%N) (denote r)).
      * unfold S1; cbn [denote]; rewrite (nn_pred _ Hd); finish.
      * exact (HF x 0%N (d-1)%N r t 0%nat l E).
Qed.
Lemma resume_spec f: RunSpec f -> RunSpec (resume f).
Proof.
  intros HF b c d r r' a l; unfold resume.
  destruct (if (b =? 0)%N then (3 <=? d)%N else false) eqn:Hempty.
  - apply andb_true_iff in Hempty; destruct Hempty as [Hb Hd].
    apply N.eqb_eq in Hb; apply N.leb_le in Hd; subst b.
    intros H; inversion H; subst; rewrite pairs_spec, zeros_spec.
    follow (Empty_b l a (nn c) (nn (d-3)%N) (denote r)); finish; flia.
  - destruct (N.eqb d 0) eqn:Hd.
    + apply N.eqb_eq in Hd; subst d.
      destruct r as [|y r|y r|r]; try discriminate.
      destruct r as [|z s|z s|s]; try discriminate.
      * intros H; inversion H; subst; cbn [denote].
        mid (S1 l a (nn b) (nn c+nn y) 0 0inf).
        { unfold S1; simpl_tape; finish; flia. }
        follow RunTail; finish; flia.
      * intros H; mid (S1 l a (nn b) (nn (c+y)%N) (nn z) (denote s)).
        { unfold S1; cbn [denote]; rewrite N2Nat.inj_add; simpl_tape; finish; flia. }
        exact (HF b (c+y)%N z s r' a l H).
    + destruct (N.eqb d 1) eqn:Hd1.
      * apply N.eqb_eq in Hd1; subst d.
        destruct r as [|y s|y s|s]; try discriminate.
        destruct (N.leb 2 y) eqn:Hy; try discriminate.
        apply N.leb_le in Hy; intros H; inversion H; subst.
        repeat (rewrite pairs_spec || rewrite zeros_spec).
        mid (S1 l a (nn b) (nn c) 1 ([1;0;1;0]*>[0]^^0*>[1;0]^^(nn (y-2)%N)*>denote s)).
        { unfold S1; cbn [denote]; replace (nn y) with (2+nn (y-2)%N) by lia; finish. }
        follow Ones; change (nn 1%N) with 1%nat; change (nn 2%N) with 2%nat.
        replace (nn (c+1)%N) with (1+nn c) by lia.
        replace (nn (b+1)%N) with (1+nn b) by lia.
        simpl_tape; finish; flia.
      * destruct (if (d =? 2)%N then (2 <=? b)%N else false) eqn:Hcall; try discriminate.
        apply andb_true_iff in Hcall; destruct Hcall as [Hd2 Hb].
        apply N.eqb_eq in Hd2; apply N.leb_le in Hb; subst d.
        destruct (send f r) as [[u s]|] eqn:E; try discriminate.
        intros H; specialize (send_spec f HF _ _ _ E) as HP.
        follow (Inc2 l a (1+nn (b-2)%N) (nn c) (denote r)).
        follow (Call l (1+a) (nn (b-2)%N) (1+nn c) (nn u) (denote r) (denote s) HP).
        follow (HF _ _ _ _ _ (1+(1+a)) l H); finish; flia.
Qed.
Lemma run_spec fuel: RunSpec (run fuel).
Proof.
  induction fuel as [|fuel IH]; [intros b c d r r' a l H; discriminate|].
  intros b c d r r' a l; destruct r; cbn [run].
  1: { intros H; inversion H; subst; cbn [denote].
    follow RunTail; finish; flia. }
  all: remember (N.min b (d/3)) as k eqn:En;
    destruct (if (k <=? b)%N then (k*3 <=? d)%N else false) eqn:Hn; try discriminate;
    apply andb_true_iff in Hn; destruct Hn as [Hb Hd];
    apply N.leb_le in Hb; apply N.leb_le in Hd; intros H;
    match goal with |- S1 _ _ _ _ _ ?rr -[tm]->* _ =>
      follow (Incs (nn k) l a (nn (b-k)%N) (nn c) (nn (d-k*3)%N) rr)
    end;
    follow (resume_spec _ IH _ _ _ _ _ (nn k+a) l H); finish; flia.
Qed.
Lemma raw_spec s s': raw s = Some s' -> config s -[tm]->* config s'.
Proof.
  destruct s as [[q l] r]; unfold raw.
  specialize (pop_spec r) as Hr; destruct (pop r) as [b t].
  destruct (tm (q,b)) as [[[w d] q']|] eqn:E; try discriminate.
  destruct d.
  - destruct l as [|a l]; intros H; inversion H; subst; cbn [config];
      repeat (rewrite push_spec || rewrite zeros_spec); rewrite Hr.
    all: eapply evstep_step; [apply step_c_spec; cbn [step_c hd tl]; rewrite E; reflexivity|simpl_tape; finish].
  - intros H; inversion H; subst; cbn [config]; rewrite Hr.
    eapply evstep_step; [apply step_c_spec; cbn [step_c hd tl]; rewrite E; reflexivity|apply evstep_refl].
Qed.
Lemma call_step_spec fuel s s':
  call_step fuel s = Some s' -> config s -[tm]->* config s'.
Proof.
  destruct s as [[q l] r]; unfold call_step.
  specialize (pop_spec r) as Hr; destruct (pop r) as [b t].
  destruct q,b; try discriminate.
  specialize (pop_spec t) as Ht; destruct (pop t) as [b t']; destruct b; try discriminate.
  destruct (send (run fuel) t') as [[u t'']|] eqn:E; try discriminate.
  specialize (send_spec _ (run_spec fuel) _ _ _ E) as HP.
  destruct l as [|a l]; intros H; inversion H; subst; cbn [config];
    repeat (rewrite push_spec || rewrite zeros_spec); rewrite Hr, Ht.
  - applys_eq (HP 0inf); simpl_tape; reflexivity.
  - applys_eq (HP ((a::l) *> 0inf)); simpl_tape; reflexivity.
Qed.
Lemma machine_step_spec fuel s s':
  machine_step fuel s = Some s' -> config s -[tm]->* config s'.
Proof.
  unfold machine_step; destruct (call_step fuel s) eqn:E.
  - intros H; inversion H; subst; eapply call_step_spec; eauto.
  - apply raw_spec.
Qed.
Lemma strip_spec w r s: strip w r = Some s -> denote r = w *> denote s.
Proof.
  gen r; induction w as [|b w IH]; intros r; cbn [strip].
  - intros H; inversion H; reflexivity.
  - specialize (pop_spec r) as Hr; destruct (pop r) as [a t].
    destruct (sym_eqb_spec a b); try discriminate; subst a.
    intros H; rewrite Hr, (IH _ H); reflexivity.
Qed.
Lemma tape_eqb_spec r s: tape_eqb r s = true -> r=s.
Proof.
  gen s; induction r; destruct s; cbn [tape_eqb]; try discriminate;
    try solve [intros H; f_equal; auto].
  all: intros H; apply andb_true_iff in H; destruct H as [Hn Hr];
    apply N.eqb_eq in Hn; subst; f_equal; auto.
Qed.
Lemma allzero_spec l: allzero l = true -> l *> 0inf = 0inf.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  destruct b; cbn [allzero]; try discriminate.
  intros H; cbn; rewrite (IH H), <-const_unfold; reflexivity.
Qed.
Lemma at_stage_spec s t: at_stage s t = true -> config s = stage_config t.
Proof.
  destruct s as [[q l] r], t as [p t]; unfold at_stage.
  destruct q; try discriminate.
  destruct (allzero l) eqn:Hl; try discriminate.
  specialize (pop_spec r) as Hr; destruct (pop r) as [b s]; destruct b; try discriminate.
  destruct (strip (if p then LE else LO) s) eqn:E; try discriminate.
  intros H; apply tape_eqb_spec in H; subst.
  cbn [config stage_config]; rewrite (allzero_spec _ Hl), Hr, (strip_spec _ _ _ E).
  reflexivity.
Qed.
Lemma seek_spec count fuel s t: seek count fuel s t = true ->
  config s -[tm]->* stage_config t.
Proof.
  gen s; induction count; intros s; cbn [seek];
    destruct (at_stage s t) eqn:E;
    try solve [intros _; rewrite (at_stage_spec _ _ E); apply evstep_refl].
  - discriminate.
  - destruct (machine_step fuel s) eqn:H; try discriminate.
    intros Ht; eapply evstep_trans; [eapply machine_step_spec; eauto|eauto].
Qed.
Ltac unbool :=
  repeat match goal with
  | H: (if _ then _ else false) = true |- _ =>
      apply andb_true_iff in H; destruct H
  | H: N.eqb _ _ = true |- _ => apply N.eqb_eq in H
  | H: N.leb _ _ = true |- _ => apply N.leb_le in H
  | H: N.ltb _ _ = true |- _ => apply N.ltb_lt in H
  end.
Lemma goodb_spec: forall r x, goodb x r = true -> Good (nn x) (denote r).
Proof.
  fix IH 1; intros r x; destruct r as [|y r|y r|r]; try discriminate.
  destruct r as [|z r|z r|r]; cbn [goodb]; try discriminate; intros H; unbool.
  - applys_eq (Good_tail (nn x) (nn (y/3)%N)); unfold E; cbn [denote]; flia.
  - applys_eq (Good_cons (nn x) (nn (y/3)%N) (nn (z/3)%N) (denote r));
      try (unfold C; cbn [denote]; flia).
    apply IH; assumption.
Qed.
Lemma regionb_spec s: regionb s = true -> Inv (stage_config s).
Proof.
  destruct s as [p r]; destruct r as [|y r|y r|r]; try discriminate.
  destruct r as [|z r|z r|r]; try discriminate.
  destruct p; cbn [regionb stage_config]; intros H; unbool.
  - applys_eq (IE (nn (z/3)%N) (denote r)); try (unfold C; cbn [denote]; flia).
    apply (goodb_spec r 216%N); assumption.
  - applys_eq (IO (nn (z/3)%N) (denote r)); try (unfold C; cbn [denote]; flia).
    apply (goodb_spec r 108%N); assumption.
Qed.
Lemma stage_step_spec fuel s s': stage_step fuel s = Some s' ->
  stage_config s -[tm]->* stage_config s'.
Proof.
  destruct s as [p r]; unfold stage_step.
  destruct (send (run fuel) r) as [[u t]|] eqn:E; try discriminate.
  specialize (send_spec _ (run_spec fuel) _ _ _ E) as HP.
  destruct p.
  - destruct (N.leb 264 u) eqn:Hu; try discriminate; apply N.leb_le in Hu.
    intros H; inversion H; subst; cbn [stage_config]; rewrite pairs_spec, zeros_spec.
    apply progress_evstep, Left1; applys_eq HP; flia.
  - destruct (N.eqb u 324) eqn:Hu; try discriminate; apply N.eqb_eq in Hu; subst u.
    intros H; inversion H; subst; apply progress_evstep, Left0; exact HP.
Qed.
Lemma check_stages_spec count fuel s: check_stages count fuel s = true ->
  ~halts tm (stage_config s).
Proof.
  gen s; induction count; intros s; cbn [check_stages];
    destruct (regionb s) eqn:E;
    try solve [intros _; apply region_nonhalt, regionb_spec, E].
  - discriminate.
  - destruct (stage_step fuel s) eqn:H; try discriminate.
    intros Ht; eapply multistep_nonhalt; [eapply stage_step_spec; eauto|eauto].
Qed.
Theorem check_spec count stages fuel q target:
  check count stages fuel q target = true -> ~halts tm (config (q,nil,Blank)).
Proof.
  unfold check; intros H; apply andb_true_iff in H; destruct H as [Hs Hc].
  eapply multistep_nonhalt; [eapply seek_spec; exact Hs|apply check_stages_spec in Hc; exact Hc].
Qed.
End ComputeSpec13.
End FT7ComputeSpec.

Import BusyCoq.Individual62.
Import ZifyNat Lia NArith String.
Import FT7Cycle FT7Entry FT7Compute FT7ComputeSpec.

Theorem nonhalt: ~halts tm c0.
Proof.
  change (~halts tm (Compute13.config (A,nil,Compute13.Blank))).
  apply (ComputeSpec13.check_spec 30000 4000 1024 A Compute13.seed13).
  native_compute; reflexivity.
Qed.
End TM13.

(* Shared definitions from FT7Machines.v. *)
Module FT7Machines.
Import BusyCoq.Individual62.
Import ZifyNat Lia NArith String.
Import FT7Cycle FT7Entry TM13.FT7Compute TM13.FT7ComputeSpec.

(* Bouncer_v3.vo is stale relative to the installed ES_v3.vo. Only its small
   chunked-computation definition and specification are copied here. *)
Fixpoint multistep_c' tm n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm n3 c
  | S n1 => match multistep_c tm n2 c with
            | Some c => multistep_c' tm n1 n2 n3 c
            | None => None
            end
  end.
Lemma multistep_c'_spec tm n1 n2 n3 c c':
  multistep_c' tm n1 n2 n3 c = Some c' <-> c -[tm]->> (n1*n2+n3) / c'.
Proof.
  gen c c'; induction n1; cbn [multistep_c']; intros.
  1: apply multistep_c_spec.
  destruct (multistep_c tm n2 c) eqn:E.
  + apply multistep_c_spec in E; rewrite IHn1.
    replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
    split; intro H.
    * eapply multistep_trans; eauto.
    * eapply rewind_split in H; destruct H as [c'0 [I1 I2]].
      multistep_deterministic; eauto.
  + split.
    1: congruence.
    replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
    intro H; eapply rewind_split in H; destruct H as [c'0 [I1 I2]].
    eapply multistep_c_spec in I1; congruence.
Qed.
End FT7Machines.

Module TM9.
Import BusyCoq.Individual62.
Import ZifyNat Lia NArith String.
Import FT7Cycle FT7Entry TM13.FT7Compute TM13.FT7ComputeSpec.
Import FT7Machines.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_1RA---").
Definition rename q := match q with A=>B | B=>C | C=>D | D=>A | E=>E | F=>F end.
Lemma perm: Perm TM11.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.

Lemma init: c0 -[tm]->* 0inf <{{B}} TM11.L0 *> Cycle.W [(66,90)] (492*3).
Proof.
  eapply without_counter.
  apply multistep_c'_spec with (n1:=2107) (n2:=2107) (n3:=922).
  vm_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (@perm_nonhalt' TM11.tm tm rename A _); [apply perm|].
  apply (EntrySteps.early_nonhalt 1%nat 492); lia.
Qed.
End TM9.

Module TM10.
Import BusyCoq.Individual62.
Import ZifyNat Lia NArith String.
Import FT7Cycle FT7Entry TM13.FT7Compute TM13.FT7ComputeSpec.
Import FT7Machines.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RA_1LD0LC_1RE0RF_0RB0RD_1RD0LB").
Definition rename q := match q with A=>C | B=>D | C=>E | D=>B | E=>F | F=>A end.
Lemma perm: Perm TM11.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.

Lemma init: c0 -[tm]->* 0inf <{{C}} TM11.L0 *> Cycle.W [(66,90)] (556*3).
Proof.
  eapply without_counter.
  apply multistep_c'_spec with (n1:=2355) (n2:=2354) (n3:=2289).
  vm_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (@perm_nonhalt' TM11.tm tm rename A _); [apply perm|].
  apply (EntrySteps.early_nonhalt 1%nat 556); lia.
Qed.
End TM10.

Module TM14.
Import BusyCoq.Individual62.
Import ZifyNat Lia NArith String.
Import FT7Cycle FT7Entry TM13.FT7Compute TM13.FT7ComputeSpec.
Import FT7Machines.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_0LD---").
Definition rename q := match q with A=>B | B=>C | C=>D | D=>A | E=>E | F=>F end.
Lemma perm: Perm TM13.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (@perm_nonhalt' TM13.tm tm rename D _); [apply perm|].
  change (~halts TM13.tm (Compute13.config (D,nil,Compute13.Blank))).
  apply (ComputeSpec13.check_spec 20000 2100 1024 D Compute13.seed14).
  native_compute; reflexivity.
Qed.
End TM14.

(* Shared definitions from FT7TM7Rules.v. *)
Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RF_1RB0LD_1RE---").

Module FT7TM7Rules.
(* Common local rules for ft7 TM3--TM7, in TM7 state names.
   The completed blank-tape nonhalting theorems are in FT7TM3_7.v. *)
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia String.

Module Rules7.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{B}} [1]*>[1;0]^^b*>[0]*>[1;0]^^c*>[0]^^d*>r.
Ltac run := unfold S1; ES_v2.es.
Lemma Inc l a b c d r:
  S1 l a (1+b) c (3+d) r -->* S1 l (1+a) b (2+c) d r.
Proof. run. Qed.
Lemma Incs n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->* S1 l (n+a) b (n*2+c) d r.
Proof. gen a b c d; ind n Inc. Qed.
Lemma Empty_b l a c d r:
  S1 l a 0 c (3+d) r -->* l <{{A}} [0]^^a*>[1;0]^^(3+c)*>[0]^^d*>r.
Proof. run. Qed.
Lemma Inc2 l a b c r:
  S1 l a (1+b) c 2 r -->* S1 l (1+a) b (1+c) 0 ([1]*>r).
Proof. run. Qed.
Lemma Empty2 l a c r:
  S1 l a 0 c 2 r -->* l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[1]*>r.
Proof. run. Qed.
Definition P u r r' := forall l,
  l <* [0] <{{B}} [1]*>r -->* l <{{A}} [0]^^u*>r'.
Lemma Enter l a b c r:
  S1 l a (1+b) c 0 ([1]*>r) -->*
  l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <* [0] <{{B}} [1]*>r.
Proof. run. Qed.
Lemma Return l a b c d r:
  l <* [1]^^a <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <{{A}} [0]^^d*>r -->*
  S1 l a b c d r.
Proof. run. Qed.
Lemma Call l a b c u r r':
  P u r r' -> S1 l a (1+b) c 0 ([1]*>r) -->* S1 l (1+a) b c u r'.
Proof. intros H; follow Enter; follow H; follow Return; finish. Qed.
Lemma Empty0_call l a c u r r':
  P u r r' -> S1 l a 0 c 0 ([1]*>r) -->*
  l <{{A}} [0]^^a*>[1;0]^^(1+c)*>[0]^^u*>r'.
Proof.
  intros H; unfold S1.
  mid (l <* [1]^^a <* [0;1]^^(1+c) <* [0] <{{B}} [1]*>r).
  ES_v2.es. follow H; ES_v2.es.
Qed.
Lemma D1_inc l a b c y z r:
  S1 l a (1+b) c 1 ([1;0]^^(2+y)*>[0]^^(3+z)*>r) -->*
  S1 l (1+a) b (1+c) 3 ([1;0]^^y*>[0;1;0;1]*>[0]^^z*>r).
Proof. run. Qed.
Lemma D1_empty l a c y z r:
  S1 l a 0 c 1 ([1;0]^^(2+y)*>[0]^^(3+z)*>r) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^3*>[1;0]^^y*>[0;1;0;1]*>[0]^^z*>r.
Proof. run. Qed.
Lemma D1_call l a b c y u r r':
  P u r r' -> S1 l a (1+b) c 1 ([1;0]^^(2+y)*>[0;1]*>r) -->*
  S1 l (1+a) b (1+c) 3 ([1;0]^^y*>[0]^^(1+u)*>r').
Proof.
  intros H; unfold S1.
  mid (l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^(1+c)
    <* [1;1;1;1] <* [1;0]^^y <* [0] <{{B}} [1]*>r).
  ES_v2.es. follow H; ES_v2.es.
Qed.
Lemma D1_empty_call l a c y u r r':
  P u r r' -> S1 l a 0 c 1 ([1;0]^^(2+y)*>[0;1]*>r) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^3*>[1;0]^^y*>[0]^^(1+u)*>r'.
Proof.
  intros H; unfold S1.
  mid (l <* [1]^^a <* [0;1]^^(2+c) <* [1;1;1;1]
    <* [1;0]^^y <* [0] <{{B}} [1]*>r).
  ES_v2.es. follow H; ES_v2.es.
Qed.
Lemma D1_odd l a b c y r:
  S1 l a (1+b) c 1 ([1;0]^^(2+y)*>[1;1]*>r) -->*
  S1 l (1+a) b (1+c) 3 ([1;0]^^y*>[0;1;0]*>r).
Proof. run. Qed.
Lemma D1_empty_odd l a c y r:
  S1 l a 0 c 1 ([1;0]^^(2+y)*>[1;1]*>r) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^3*>[1;0]^^y*>[0;1;0]*>r.
Proof. run. Qed.
Lemma D1_two l a b c z r:
  S1 l a (2+b) c 1 ([1;0]^^2*>[0]^^(4+z)*>r) -->*
  S1 l (2+a) b (3+c) 1 ([1;0]^^2*>[0]^^z*>r).
Proof.
  follow (D1_inc l a (1+b) c 0 (1+z) r).
  follow Inc; unfold S1; finish.
Qed.
Lemma D1_twos n l a b c z r:
  S1 l a (n*2+b) c 1 ([1;0]^^2*>[0]^^(n*4+z)*>r) -->*
  S1 l (n*2+a) b (n*3+c) 1 ([1;0]^^2*>[0]^^z*>r).
Proof. gen a b c z; ind n D1_two. Qed.
Lemma D1_gap_tail l a b c y t n:
  S1 l a (1+b) c 1 ([1;0]^^(2+y)*>[0]^^2*>[1;0]^^(2+t)*>[0]*>[1;0]^^n*>0inf) -->*
  S1 l (1+a) b (1+c) 3
    ([1;0]^^y*>[0;1;0]*>[0]^^3*>[1;0]^^t*>[0]*>[1;0]^^(2+n)*>0inf).
Proof. unfold S1; es' a b c y t n & l. Qed.
Lemma D1_empty_gap_tail l a c y t n:
  S1 l a 0 c 1 ([1;0]^^(2+y)*>[0]^^2*>[1;0]^^(2+t)*>[0]*>[1;0]^^n*>0inf) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^3*>
    [1;0]^^y*>[0;1;0]*>[0]^^3*>[1;0]^^t*>[0]*>[1;0]^^(2+n)*>0inf.
Proof. unfold S1; es' a c y t n & l. Qed.
Lemma D1_one l a b c z r:
  S1 l a (1+b) c 1 ([1;0]*>[0]^^(4+z)*>r) -->*
  S1 l (1+a) b (1+c) 3 ([1;0;1]*>[0]^^z*>r).
Proof. run. Qed.
Lemma D1_empty_one l a c z r:
  S1 l a 0 c 1 ([1;0]*>[0]^^(4+z)*>r) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^3*>[1;0;1]*>[0]^^z*>r.
Proof. run. Qed.
Lemma D1_one_tail l a b c t n:
  S1 l a (1+b) c 1 ([1;0]*>[0]^^3*>[1;0]^^(2+t)*>[0]*>[1;0]^^n*>0inf) -->*
  S1 l (1+a) b (1+c) 3 ([1;0]*>[0]^^3*>[1;0]^^t*>[0]*>[1;0]^^(2+n)*>0inf).
Proof. unfold S1; es' a b c t n & l. Qed.
Lemma D1_empty_one_tail l a c t n:
  S1 l a 0 c 1 ([1;0]*>[0]^^3*>[1;0]^^(2+t)*>[0]*>[1;0]^^n*>0inf) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^3*>[1;0]*>[0]^^3*>
    [1;0]^^t*>[0]*>[1;0]^^(2+n)*>0inf.
Proof. unfold S1; es' a c t n & l. Qed.
Lemma D1_one_odd_tail l a b c y:
  S1 l a (1+b) c 1 ([1;0;1]*>[1;0]^^(1+y)*>0inf) -->*
  S1 l (1+a) b (1+c) 4 ([1;0]^^y*>[0]*>[1;0]^^2*>0inf).
Proof. unfold S1; es' a b c y & l. Qed.
Lemma D1_empty_one_odd_tail l a c y:
  S1 l a 0 c 1 ([1;0;1]*>[1;0]^^(1+y)*>0inf) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^4*>[1;0]^^y*>[0]*>[1;0]^^2*>0inf.
Proof. unfold S1; es' a c y & l. Qed.
Lemma Odd_enter l b r:
  l <* [0] <{{B}} [1]*>[1;0]^^(1+b)*>[1;1;0]*>r -->*
  S1 l 1 b 1 1 r.
Proof. run. Qed.
Lemma Odd_zero r: P 0 ([1;1]*>r) ([1;0;1;0]*>r).
Proof. intros l; ES_v2.es. Qed.
Lemma RunTail l a b c d:
  S1 l a b c d 0inf -->* l <{{A}} [0]^^(a+b)*>[1;0]^^(b*2+c+3)*>0inf.
Proof.
  mid (S1 l a (b+0) c (b*3+3) 0inf).
  - unfold S1; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; finish.
  - follow Incs; follow Empty_b; finish.
Qed.

(* A whole repeated prefix can be handled without nested recursive calls. *)
Definition W := [1;0;0;1;0;1].
Definition J r := [1;0]^^3*>[0]^^3*>r.
Lemma W_call l u r r':
  P u r r' -> l <* [0] <{{B}} [1]*>W*>r -->* S1 l 1 0 1 u r'.
Proof.
  intros H; unfold W.
  mid (S1 l 0 1 1 0 ([1]*>r)). unfold S1; finish.
  follow Call; finish.
Qed.
Lemma W_shift r s: P 1 r (J s) -> P 1 (W*>r) (J (W*>s)).
Proof.
  intros H l; follow (W_call l 1 r (J s) H); unfold J, W.
  follow D1_empty; finish.
Qed.
Lemma W_shifts n r s: P 1 r (J s) -> P 1 (W^^n*>r) (J (W^^n*>s)).
Proof.
  intros H; induction n; [exact H|].
  simpl_tape; apply W_shift; exact IHn.
Qed.
End Rules7.
End FT7TM7Rules.

(* Shared definitions from FT7TM7Stages.v. *)
Module FT7TM7Stages.
(* Successive frontier reductions. All P premises are finite complete
   returns; FT7TM3_7.v connects the checked hierarchy to blank-tape nonhalting. *)
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat.
Import FT7TM7Rules.
Import Rules7.

Module Stages7.
Definition A0 q r := [1;0]^^6*>[0]*>[1;0]^^4*>[0]^^q*>r.
Definition B0 r := [1;0]^^2*>[0;1;0;1]*>r.
Definition C0 q r := [1;0;0;1;0;0]*>[1;0]^^5*>[0]^^q*>r.
Definition T n r := [0]^^2*>J (W^^n*>r).
Definition E0 n r := [1;0]^^2*>[0]^^3*>W^^(1+n)*>r.
Definition Out s t := forall l a,
  S1 l a 0 1 1 s -->* l <{{A}} [0]^^a*>J t.
Lemma W_snoc n r: W^^n*>W*>r = W*>W^^n*>r.
Proof. rewrite <-!Str_app_assoc, lpow_shift; reflexivity. Qed.

Lemma Low0 n r: P 0 (T n r) (E0 n r).
Proof.
  intros l; unfold T, J.
  mid (S1 l 0 0 0 1 ([1;0]^^3*>[0]^^3*>W^^n*>r)).
  unfold S1; finish.
  follow D1_empty; unfold E0, W; finish.
Qed.
Lemma Out_J r: Out (J r) (W*>r).
Proof. intros l a; unfold J, W; follow D1_empty; finish. Qed.
Lemma Lift n r s t:
  P 1 (W*>r) s -> Out s t -> P 2 (E0 n r) (J (W^^n*>t)).
Proof.
  intros H O; destruct n as [|n].
  - intros l.
    mid (S1 l 0 2 0 2 (W*>r)). unfold E0, S1; finish.
    follow Inc2; follow (Call l 1 0 1 1 (W*>r) s H); follow O; finish.
  - assert (H2: P 1 (W^^2*>r) (J t)).
    { intros l; follow (W_call l 1 (W*>r) s H); follow O; finish. }
    assert (Hn: P 1 (W^^(2+n)*>r) (J (W^^n*>t))).
    { intros l; rewrite (Nat.add_comm 2 n), lpow_add; simpl_tape.
      apply W_shifts; exact H2. }
    intros l.
    mid (S1 l 0 2 0 2 (W^^(2+n)*>r)). unfold E0, S1; finish.
    follow Inc2; follow (Call l 1 0 1 1 (W^^(2+n)*>r) (J (W^^n*>t)) Hn).
    follow Out_J; unfold W; finish.
Qed.

Lemma A_call q r s: P 6 (A0 q r) s ->
  P 1 (W*>A0 q r) ([1;0]^^4*>[0]^^3*>s).
Proof. intros H l; follow (W_call l 6 (A0 q r) s H); follow Empty_b; finish. Qed.
Lemma A_out r: Out ([1;0]^^4*>[0]^^3*>r) (B0 r).
Proof. intros l a; follow D1_empty; unfold J, B0; finish. Qed.
Lemma B_call q r s: P (13+q) r s ->
  P 2 (B0 r) ([1;0]^^6*>[0]^^(7+q)*>s).
Proof.
  intros H l; unfold B0.
  mid (S1 l 0 2 1 0 ([1]*>r)). unfold S1; finish.
  follow (Call l 0 1 1 (13+q) r s H); follow Inc; follow Empty_b; finish.
Qed.
Lemma B_W q r s: P (13+q) r s ->
  P 1 (W*>B0 r) ([1;0]^^3*>[1]*>[1;0]^^6*>[0]^^(7+q)*>s).
Proof.
  intros H l; follow (W_call l 2 (B0 r) ([1;0]^^6*>[0]^^(7+q)*>s) (B_call q r s H)).
  follow Empty2; finish.
Qed.
Lemma B_out q r:
  Out ([1;0]^^3*>[1]*>[1;0]^^6*>[0]^^(7+q)*>r) (C0 (7+q) r).
Proof. intros l a; follow D1_empty_odd; unfold J, C0; finish. Qed.
Lemma C_call q r:
  P 1 (C0 (7+q) r) ([1;0]^^8*>[0]*>[1;0]^^2*>[0]^^(3+q)*>r).
Proof.
  intros l; unfold C0.
  mid (S1 l 0 1 1 1 ([1;0]^^5*>[0]^^(7+q)*>r)). unfold S1; finish.
  follow D1_inc; follow Empty_b; finish.
Qed.
Lemma C_sub q r: P 0 ([0]*>[1;0]*>[0]^^(3+q)*>r) ([1;0]^^4*>[0]^^q*>r).
Proof.
  intros l; mid (S1 l 0 0 1 (3+q) r). unfold S1; finish.
  follow Empty_b; finish.
Qed.
Lemma C_W q r: P 1 (W*>C0 (7+q) r) (J (A0 q r)).
Proof.
  intros l; follow (W_call l 1 (C0 (7+q) r)
    ([1;0]^^8*>[0]*>[1;0]^^2*>[0]^^(3+q)*>r) (C_call q r)).
  follow (D1_empty_call l 1 1 6 0 ([0]*>[1;0]*>[0]^^(3+q)*>r)
    ([1;0]^^4*>[0]^^q*>r) (C_sub q r)).
  unfold J, A0; finish.
Qed.

Lemma Frontier u r s: P u r s ->
  0inf <{{A}} r -->* 0inf <{{A}} [0]^^u*>s.
Proof. intros H; eapply evstep_trans; [apply evstep_one; prove_step|]. follow H; finish. Qed.
Lemma Tick n r s: P 2 (E0 n r) (J (W^^n*>s)) ->
  0inf <{{A}} T n r -[tm]->+ 0inf <{{A}} T n s.
Proof.
  intros H; eapply progress_intro; [prove_step|].
  follow (Low0 n r); follow (Frontier _ _ _ H); finish.
Qed.
Lemma Cycle n q q' r s t:
  P 6 (A0 q r) s -> P (13+q') s t ->
  0inf <{{A}} T n (A0 q r) -[tm]->+ 0inf <{{A}} T (1+n) (A0 q' t).
Proof.
  intros H G.
  follow10 (Tick _ _ _ (Lift n _ _ _ (A_call _ _ _ H) (A_out s))).
  follow100 (Tick _ _ _ (Lift n _ _ _ (B_W _ _ _ G) (B_out q' t))).
  follow100 (Tick _ _ _ (Lift n _ _ _ (C_W q' t) (Out_J (A0 q' t)))).
  unfold T, J; rewrite W_snoc; finish.
Qed.

(* First-call formulas expose the three grouped column types. *)
Definition Col x z r := [1;0]^^x*>[0]^^z*>r.
Definition Mark h x z r := [1;0]^^x*>[0]^^h*>[1;0]^^2*>[0]^^z*>r.
Lemma Counter x z r:
  P x (Col x (1+(x*3+(3+z))) r) (Col (x*2+3) z r).
Proof.
  intros l; unfold Col.
  mid (S1 l 0 (x+0) 0 (x*3+(3+z)) r). unfold S1; finish.
  follow Incs; follow Empty_b; finish; flia.
Qed.
Lemma BigFirst z r:
  P 6 (A0 (21+z) r) (Col 19 z r).
Proof.
  intros l; unfold A0, Col.
  mid (S1 l 0 (6+0) 4 (6*3+(3+z)) r). unfold S1; finish.
  follow Incs; follow Empty_b; finish.
Qed.
Lemma FirstC x z r:
  P 6 (A0 6 (Col x (15+z) r)) (Col (x+19) z r).
Proof.
  intros l; unfold A0, Col.
  mid (S1 l 0 6 4 6 ([1;0]^^x*>[0]^^(15+z)*>r)). unfold S1; finish.
  follow (Incs 2 l 0 4 4 0 ([1;0]^^x*>[0]^^(15+z)*>r)).
  mid (S1 l 2 (4+0) (8+x) (4*3+(3+z)) r). unfold S1; finish.
  follow Incs; follow Empty_b; finish.
Qed.
Lemma FirstD1 x z r:
  P 6 (A0 6 (Mark 1 x (12+z) r)) (Mark 4 (x+16) z r).
Proof.
  intros l; unfold A0, Mark.
  mid (S1 l 0 6 4 6 ([1;0]^^x*>[0]*>[1;0]^^2*>[0]^^(12+z)*>r)).
  unfold S1; finish.
  follow (Incs 2 l 0 4 4 0 ([1;0]^^x*>[0]*>[1;0]^^2*>[0]^^(12+z)*>r)).
  mid (S1 l 2 (2*2+0) (8+x) 1 ([1;0]^^2*>[0]^^(2*4+(4+z))*>r)).
  unfold S1; finish.
  follow D1_twos; follow D1_empty; finish.
Qed.
Lemma FirstD4 x z r:
  P 6 (A0 6 (Mark 4 x (8+z) r)) (Mark 1 (x+17) z r).
Proof.
  intros l; unfold A0, Mark.
  mid (S1 l 0 6 4 6 ([1;0]^^x*>[0]^^4*>[1;0]^^2*>[0]^^(8+z)*>r)).
  unfold S1; finish.
  follow (Incs 2 l 0 4 4 0 ([1;0]^^x*>[0]^^4*>[1;0]^^2*>[0]^^(8+z)*>r)).
  mid (S1 l 2 4 (8+x) 4 ([1;0]^^2*>[0]^^(8+z)*>r)). unfold S1; finish.
  follow Inc.
  follow (D1_twos 1 l 3 1 (10+x) (4+z) r).
  follow D1_inc; follow Empty_b; finish.
Qed.
Lemma LargeCycle n z r:
  0inf <{{A}} T n (A0 (82+z) r) -[tm]->+
  0inf <{{A}} T (1+n) (A0 6 (Col 41 z r)).
Proof.
  apply (Cycle n (82+z) 6 r (Col 19 (61+z) r) (Col 41 z r)).
  applys_eq (BigFirst (61+z) r); flia.
  applys_eq (Counter 19 z r); flia.
Qed.
Lemma FourCycle n a b c r s t u:
  P 60 (Col 60 (62+b) r) s ->
  P 19 (Col 19 26 s) (Mark 1 (156+a) (12+c) t) ->
  P (172+a) (Mark 4 (172+a) c t) u ->
  0inf <{{A}} T n (A0 6 (Col 41 (77+b) r)) -[tm]->+
  0inf <{{A}} T (4+n) (A0 6 (Col 41 (77+a) u)).
Proof.
  intros H G K.
  assert (F: P 6 (A0 6 (Mark 1 (156+a) (12+c) t)) (Mark 4 (172+a) c t)).
  { intros l; applys_eq (FirstD1 (156+a) c t l); unfold Mark; flia. }
  follow10 (Cycle n 6 47 (Col 41 (77+b) r) (Col 60 (62+b) r) s
    (FirstC 41 (62+b) r) H).
  follow100 (Cycle (1+n) 47 6 s (Col 19 26 s) (Mark 1 (156+a) (12+c) t)
    (BigFirst 26 s) G).
  follow100 (Cycle (2+n) 6 (159+a) (Mark 1 (156+a) (12+c) t)
    (Mark 4 (172+a) c t) u F K).
  follow100 (LargeCycle (3+n) (77+a) u); finish.
Qed.
(* These local combinations never inspect the suffix r. *)
Lemma SecondC x z r:
  P 19 (Col 19 26 (Col (2+x) (24+z) r)) (Mark 1 (35+x) z r).
Proof.
  intros l; unfold Col, Mark.
  mid (S1 l 0 (8+11) 0 (8*3+1) ([1;0]^^(2+x)*>[0]^^(24+z)*>r)).
  unfold S1; finish.
  follow Incs; follow D1_inc; follow Inc.
  mid (S1 l 10 (4*2+1) (19+x) 1 ([1;0]^^2*>[0]^^(4*4+(4+z))*>r)).
  unfold S1; finish; flia.
  follow D1_twos; follow D1_inc; follow Empty_b; finish; flia.
Qed.
Lemma SecondM4 x z r:
  P 19 (Col 19 26 (Mark 4 (2+x) (20+z) r)) (Mark 1 (37+x) z r).
Proof.
  intros l; unfold Col, Mark.
  mid (S1 l 0 (8+11) 0 (8*3+1)
    ([1;0]^^(2+x)*>[0]^^4*>[1;0]^^2*>[0]^^(20+z)*>r)).
  unfold S1; finish.
  follow Incs; follow D1_inc; follow Inc.
  mid (S1 l 10 9 (19+x) 1 ([1;0]^^4*>[0]^^(20+z)*>r)).
  unfold S1; finish; flia.
  follow (D1_inc l 10 8 (19+x) 2 (17+z) r); follow Inc.
  mid (S1 l 12 (3*2+1) ((22+x)+2) 1 ([1;0]^^2*>[0]^^(3*4+(4+z))*>r)).
  unfold S1; rewrite (lpow_add _ (22+x) 2); simpl_tape; finish; flia.
  follow D1_twos; follow D1_inc; follow Empty_b; finish; flia.
Qed.
Lemma MarkedCounter x z r:
  P (1+x) (Mark 4 (1+x) (x*3+(3+z)) r) (Col (x*2+7) z r).
Proof.
  intros l; unfold Mark, Col.
  mid (S1 l 0 (1+x) 0 3 ([1;0]^^2*>[0]^^(x*3+(3+z))*>r)).
  unfold S1; finish.
  follow Inc.
  mid (S1 l 1 (x+0) 4 (x*3+(3+z)) r). unfold S1; finish.
  follow Incs; follow Empty_b; finish; flia.
Qed.
Lemma LargeFour n z r:
  0inf <{{A}} T n (A0 6 (Col 41 (751+z) r)) -[tm]->+
  0inf <{{A}} T (4+n) (A0 6 (Col 41 77 (Col 349 z r))).
Proof.
  apply (FourCycle n 0 (674+z) (516+z) r (Col 123 (552+z) r) r (Col 349 z r)).
  applys_eq (Counter 60 (552+z) r); flia.
  applys_eq (SecondC 121 (528+z) r); flia.
  applys_eq (MarkedCounter 171 z r); flia.
Qed.

Lemma SmallFirst x z r:
  P 60 (Col 60 62 (Col (2+x) (84+z) r)) (Mark 4 (102+x) z r).
Proof.
  intros l; unfold Col, Mark.
  mid (S1 l 0 (20+40) 0 (20*3+1) ([1;0]^^(2+x)*>[0]^^(84+z)*>r)).
  unfold S1; finish.
  follow Incs; follow D1_inc; follow Inc.
  mid (S1 l 22 (19*2+0) (43+x) 1 ([1;0]^^2*>[0]^^(19*4+(4+z))*>r)).
  unfold S1; finish; flia.
  follow D1_twos; follow D1_empty; finish; flia.
Qed.
Lemma SmallLast a r s:
  P (345+a) r s -> P 172 (Mark 4 172 167 r) (Col 346 a s).
Proof.
  intros H l; unfold Mark, Col.
  mid (S1 l 0 172 0 3 ([1;0]^^2*>[0]^^167*>r)). unfold S1; finish.
  follow Inc.
  mid (S1 l 1 (55+116) 4 (55*3+2) r). unfold S1; finish.
  follow Incs; follow Inc2; follow (Call l 57 114 115 (345+a) r s H).
  mid (S1 l 58 (114+0) 115 (114*3+(3+a)) s). unfold S1; finish.
  follow Incs; follow Empty_b; finish.
Qed.

(* A new two-call recurrence after eight Cycle steps. Unlike selecting a
   bounded observed phase, this statement allows every natural d and d'. *)
Definition G n d r := T n (A0 6 (Col 41 77 (Col 346 (116+d) r))).
Lemma EightCycle n d d' r s t:
  P 497 (Mark 4 497 d r) s -> P (461+d') s t ->
  0inf <{{A}} G n d r -[tm]->+ 0inf <{{A}} G (8+n) d' t.
Proof.
  intros H K; unfold G.
  mid10 (0inf <{{A}} T (4+n) (A0 6 (Col 41 402 s))).
  { apply (FourCycle n 325 0 d (Col 346 (116+d) r) (Mark 4 446 (32+d) r) r s).
    applys_eq (SmallFirst 344 (32+d) r); flia.
    applys_eq (SecondM4 444 (12+d) r); flia.
    exact H. }
  apply progress_evstep.
  applys_eq (FourCycle (4+n) 0 325 167 s (Col 123 203 s) s (Col 346 (116+d') t)); try flia.
  applys_eq (Counter 60 203 s); flia.
  applys_eq (SecondC 121 179 s); flia.
  apply SmallLast; applys_eq K; flia.
Qed.
Lemma LargeEight n z r:
  0inf <{{A}} G n (4492+z) r -[tm]->+
  0inf <{{A}} G (8+n) 538 (Col 2001 z r).
Proof.
  apply (EightCycle n (4492+z) 538 r (Col 999 (3001+z) r) (Col 2001 z r)).
  applys_eq (MarkedCounter 496 (3001+z) r); flia.
  applys_eq (Counter 999 z r); flia.
Qed.

Lemma EightFirstC x z r:
  P 497 (Mark 4 497 538 (Col (2+x) (636+z) r)) (Mark 1 (840+x) z r).
Proof.
  intros l; unfold Mark, Col.
  mid (S1 l 0 497 0 3 ([1;0]^^2*>[0]^^538*>
    [1;0]^^(2+x)*>[0]^^(636+z)*>r)). unfold S1; finish.
  follow Inc.
  mid (S1 l 1 (179+317) 4 (179*3+1) ([1;0]^^(2+x)*>[0]^^(636+z)*>r)).
  unfold S1; finish.
  follow Incs; follow D1_inc; follow Inc.
  mid (S1 l 182 (157*2+1) (365+x) 1 ([1;0]^^2*>[0]^^(157*4+(4+z))*>r)).
  unfold S1; finish; flia.
  follow D1_twos; follow D1_inc; follow Empty_b; finish; flia.
Qed.
Lemma EightFirstM4 x z r:
  P 497 (Mark 4 497 538 (Mark 4 (2+x) (632+z) r)) (Mark 1 (842+x) z r).
Proof.
  intros l; unfold Mark.
  mid (S1 l 0 497 0 3 ([1;0]^^2*>[0]^^538*>
    [1;0]^^(2+x)*>[0]^^4*>[1;0]^^2*>[0]^^(632+z)*>r)). unfold S1; finish.
  follow Inc.
  mid (S1 l 1 (179+317) 4 (179*3+1)
    ([1;0]^^(2+x)*>[0]^^4*>[1;0]^^2*>[0]^^(632+z)*>r)). unfold S1; finish.
  follow Incs; follow D1_inc; follow Inc.
  mid (S1 l 182 315 (365+x) 1 ([1;0]^^4*>[0]^^(632+z)*>r)).
  unfold S1; finish; flia.
  follow (D1_inc l 182 314 (365+x) 2 (629+z) r); follow Inc.
  mid (S1 l 184 (156*2+1) ((368+x)+2) 1 ([1;0]^^2*>[0]^^(156*4+(4+z))*>r)).
  unfold S1; rewrite (lpow_add _ (368+x) 2); simpl_tape; finish; flia.
  follow D1_twos; follow D1_inc; follow Empty_b; finish; flia.
Qed.
Definition H n b r := G n 538 (Col 2001 (3216+b) r).
Lemma ThirtyTwoCycle n a b c r s t u:
  P 2839 (Mark 1 2839 (2580+b) r) s ->
  P 999 (Col 999 887 s) (Mark 4 (7329+a) (632+c) t) ->
  P (8169+a) (Mark 1 (8169+a) c t) u ->
  0inf <{{A}} H n b r -[tm]->+ 0inf <{{A}} H (32+n) a u.
Proof.
  intros HP GP KP; unfold H.
  assert (F1: P 497 (Mark 4 497 538 (Col 2001 (3216+b) r))
    (Mark 1 2839 (2580+b) r)).
  { applys_eq (EightFirstC 1999 (2580+b) r); flia. }
  assert (F2: P 497 (Mark 4 497 2378 s) (Col 999 887 s)).
  { applys_eq (MarkedCounter 496 887 s); flia. }
  assert (F3: P 497 (Mark 4 497 538 (Mark 4 (7329+a) (632+c) t))
    (Mark 1 (8169+a) c t)).
  { applys_eq (EightFirstM4 (7327+a) c t); flia. }
  follow10 (EightCycle n 538 2378 (Col 2001 (3216+b) r)
    (Mark 1 2839 (2580+b) r) s F1 HP).
  follow100 (EightCycle (8+n) 2378 538 s (Col 999 887 s)
    (Mark 4 (7329+a) (632+c) t) F2 GP).
  follow100 (EightCycle (16+n) 538 (7708+a) (Mark 4 (7329+a) (632+c) t)
    (Mark 1 (8169+a) c t) u F3 KP).
  follow100 (LargeEight (24+n) (3216+a) u); finish.
Qed.
Lemma Marked1Counter x z r:
  P x (Mark 1 x (x*3+(3+z)) r) (Col (x*2+5) z r).
Proof.
  intros l; unfold Mark, Col.
  mid (S1 l 0 (x+0) 2 (x*3+(3+z)) r). unfold S1; finish.
  follow Incs; follow Empty_b; finish; flia.
Qed.
Lemma Second999 x z r:
  P 999 (Col 999 887 (Col (2+x) (1412+z) r)) (Mark 4 (1648+x) z r).
Proof.
  intros l; unfold Col, Mark.
  mid (S1 l 0 (295+704) 0 (295*3+1) ([1;0]^^(2+x)*>[0]^^(1412+z)*>r)).
  unfold S1; finish.
  follow Incs; follow D1_inc; follow Inc.
  mid (S1 l 297 (351*2+0) (593+x) 1 ([1;0]^^2*>[0]^^(351*4+(4+z))*>r)).
  unfold S1; finish; flia.
  follow D1_twos; follow D1_empty; finish; flia.
Qed.
Lemma LargeThirtyTwo n z r:
  0inf <{{A}} H n (32494+z) r -[tm]->+
  0inf <{{A}} H (32+n) 0 (Col 16343 z r).
Proof.
  apply (ThirtyTwoCycle n 0 (32494+z) (24510+z) r (Col 5683 (26554+z) r) r (Col 16343 z r)).
  applys_eq (Marked1Counter 2839 (26554+z) r); flia.
  applys_eq (Second999 5681 (25142+z) r); flia.
  applys_eq (Marked1Counter 8169 z r); flia.
Qed.
End Stages7.
End FT7TM7Stages.

(* Shared definitions from FT7TM7Columns.v. *)
Module FT7TM7Columns.
(* Local column maps used by the finite hierarchy generator. *)
Import BusyCoq.Individual62 BusyCoq.ES_v2.
Import ZifyNat Lia.
Import FT7TM7Rules FT7TM7Stages.
Import Rules7 Stages7.

Module Columns7.
Definition Run b c d r s := forall l a,
  S1 l a b c d r -->* l <{{A}} [0]^^(a+b)*>s.
Lemma RInc n b c d r s:
  Run b (n*2+c) d r s -> Run (n+b) c (n*3+d) r s.
Proof. intros H l a; follow Incs; follow (H l (n+a)); finish; flia. Qed.
Lemma RMerge b c x d r s:
  Run b (c+x) d r s -> Run b c 0 (Col x d r) s.
Proof.
  intros H l a; applys_eq (H l a); unfold S1, Col;
    rewrite (lpow_add _ c x); simpl_tape; reflexivity.
Qed.
Lemma REnd c d r: Run 0 c (3+d) r (Col (3+c) d r).
Proof. intros l a; follow Empty_b; unfold Col; finish. Qed.
Lemma RTail b c d: Run b c d 0inf (Col (b*2+c+3) 0 0inf).
Proof. intros l a; follow RunTail; unfold Col; finish. Qed.
Lemma Head0 b d r s: Run b 0 d r s -> P b (Col b (1+d) r) s.
Proof. intros H l; applys_eq (H l 0%nat); unfold S1, Col; finish; flia. Qed.
Lemma Head1 b d r s: Run b 2 d r s -> P b (Mark 1 b d r) s.
Proof. intros H l; applys_eq (H l 0%nat); unfold S1, Mark; finish; flia. Qed.
Lemma Head4 b d r s: Run b 4 d r s -> P (1+b) (Mark 4 (1+b) d r) s.
Proof.
  intros H l; unfold Mark.
  mid (S1 l 0 (1+b) 0 3 ([1;0]^^2*>[0]^^d*>r)). unfold S1; finish.
  follow Inc.
  mid (S1 l 1 b 4 d r). unfold S1; finish.
  follow H; finish.
Qed.
Lemma TwosEven n c z r:
  Run (n*2) c 1 (Col 2 (n*4+(4+z)) r) (Mark 4 (c+n*3+2) z r).
Proof.
  intros l a; unfold Col.
  mid (S1 l a (n*2+0) c 1 ([1;0]^^2*>[0]^^(n*4+(4+z))*>r)).
  unfold S1; finish.
  follow D1_twos; follow D1_empty; unfold Mark; finish; flia.
Qed.
Lemma TwosOdd n c z r:
  Run (n*2+1) c 1 (Col 2 (n*4+(4+z)) r) (Mark 1 (c+n*3+4) z r).
Proof.
  intros l a; unfold Col.
  follow D1_twos; follow D1_inc; follow Empty_b; unfold Mark; finish; flia.
Qed.
Lemma Pair0 l a b c x z r:
  S1 l a (2+b) c 1 (Col (2+x) (4+z) r) -->*
  S1 l (2+a) b (3+c+x) 1 (Col 2 z r).
Proof.
  unfold Col; follow D1_inc; follow Inc.
  unfold S1; rewrite (lpow_add _ (3+c) x); simpl_tape; finish; flia.
Qed.
Lemma Pair4 l a b c x z r:
  S1 l a (2+b) c 1 (Mark 4 (2+x) z r) -->*
  S1 l (2+a) b (3+c+x) 1 (Col 4 z r).
Proof.
  unfold Mark.
  follow (Pair0 l a b c x 0 ([1;0]^^2*>[0]^^z*>r)).
  unfold S1, Col; finish.
Qed.
Lemma Pair1 l a b c x z r:
  S1 l a (2+b) c 1 (Mark 1 (2+x) (3+z) r) -->*
  S1 l (2+a) b (3+c+x) 1 (Col 4 z r).
Proof.
  unfold Mark.
  mid (S1 l (1+a) (1+b) (1+c) 3 (Col x 1 (Col 4 z r))).
  applys_eq (D1_call l a (1+b) c x 0 ([0]*>[1;0]*>[0]^^(3+z)*>r)
    (Col 4 z r) (C_sub z r)); unfold S1, Col; finish.
  follow Inc; unfold S1, Col.
  rewrite (lpow_add _ (3+c) x); simpl_tape; finish; flia.
Qed.

Lemma NormalEven n c x z r:
  Run (2+n*2) c 1 (Col (2+x) (8+n*4+z) r) (Mark 4 (c+x+5+n*3) z r).
Proof.
  intros l a; follow (Pair0 l a (n*2) c x (n*4+(4+z)) r).
  follow (TwosEven n (3+c+x) z r); finish; flia.
Qed.
Lemma NormalOdd n c x z r:
  Run (3+n*2) c 1 (Col (2+x) (8+n*4+z) r) (Mark 1 (c+x+7+n*3) z r).
Proof.
  intros l a.
  mid (S1 l a (2+(n*2+1)) c 1 (Col (2+x) (4+(n*4+(4+z))) r)).
  unfold S1; finish; flia.
  follow Pair0; follow (TwosOdd n (3+c+x) z r); finish; flia.
Qed.

Lemma Mark4Even n c x z r:
  Run (4+n*2) c 1 (Mark 4 (2+x) (8+n*4+z) r) (Mark 4 (c+x+10+n*3) z r).
Proof.
  intros l a; follow (Pair4 l a (2+n*2) c x (8+n*4+z) r).
  follow (NormalEven n (3+c+x) 2 z r); finish; flia.
Qed.
Lemma Mark4Odd n c x z r:
  Run (5+n*2) c 1 (Mark 4 (2+x) (8+n*4+z) r) (Mark 1 (c+x+12+n*3) z r).
Proof.
  intros l a; follow (Pair4 l a (3+n*2) c x (8+n*4+z) r).
  follow (NormalOdd n (3+c+x) 2 z r); finish; flia.
Qed.
Lemma Mark1Even n c x z r:
  Run (4+n*2) c 1 (Mark 1 (2+x) (11+n*4+z) r) (Mark 4 (c+x+10+n*3) z r).
Proof.
  intros l a; follow (Pair1 l a (2+n*2) c x (8+n*4+z) r).
  follow (NormalEven n (3+c+x) 2 z r); finish; flia.
Qed.
Lemma Mark1Odd n c x z r:
  Run (5+n*2) c 1 (Mark 1 (2+x) (11+n*4+z) r) (Mark 1 (c+x+12+n*3) z r).
Proof.
  intros l a; follow (Pair1 l a (3+n*2) c x (8+n*4+z) r).
  follow (NormalOdd n (3+c+x) 2 z r); finish; flia.
Qed.

Lemma ZeroCol b c x z r:
  Run b c 0 (Col x (b*3+(3+z)) r) (Col (c+x+b*2+3) z r).
Proof.
  apply RMerge; applys_eq (RInc b 0 (c+x) (3+z) r
    (Col (c+x+b*2+3) z r)); try flia.
  applys_eq (REnd (b*2+(c+x)) z r); flia.
Qed.
Lemma ZeroMark1 b c x z r s:
  Run b (c+x) 1 (Col 2 z r) s -> Run b c 0 (Mark 1 x z r) s.
Proof. intros H; applys_eq (RMerge b c x 1 (Col 2 z r) s H); reflexivity. Qed.
Lemma ZeroMark4 b c x z r s:
  Run b (2+c+x) 1 (Col 2 z r) s -> Run (1+b) c 0 (Mark 4 x z r) s.
Proof.
  intros H; applys_eq (RMerge (1+b) c x 4 (Col 2 z r) s); try reflexivity.
  applys_eq (RInc 1 b (c+x) 1 (Col 2 z r) s); try flia.
  applys_eq H; flia.
Qed.
Lemma ZeroMark4Empty c x z r:
  Run 0 c 0 (Mark 4 x z r) (Mark 1 (3+c+x) z r).
Proof.
  applys_eq (RMerge 0 c x 4 (Col 2 z r) (Mark 1 (3+c+x) z r)); try reflexivity.
  applys_eq (REnd (c+x) 1 (Col 2 z r)); unfold Col, Mark; flia.
Qed.
Lemma Call2 b c z r s: P (b*3+(3+z)) r s ->
  Run (2+b) c 2 r (Col (b*2+c+4) z s).
Proof.
  intros H l a; follow Inc2.
  follow (Call l (1+a) b (1+c) (b*3+(3+z)) r s H).
  mid (S1 l (2+a) (b+0) (1+c) (b*3+(3+z)) s). unfold S1; finish.
  follow Incs; follow Empty_b; unfold Col; finish; flia.
Qed.

End Columns7.
End FT7TM7Columns.

(* Shared definitions from FT7TM7Compute.v. *)
Module FT7TM7Compute.
(* Finite returning-call checker. Only binary counters are evaluated. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat Bool.
Import FT7TM7Rules FT7TM7Stages FT7TM7Columns.
Module Compute7.
Import Rules7 Columns7.
Local Open Scope N_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.
Inductive Tape := Blank | Zeros (n:N) (r:Tape) | Pairs (n:N) (r:Tape) | OneBit (r:Tape).
Fixpoint denote r : side := match r with
  | Blank => 0inf
  | Zeros n r => [0%sym]^^(N.to_nat n) *> denote r
  | Pairs n r => [1%sym;0%sym]^^(N.to_nat n) *> denote r
  | OneBit r => [1%sym] *> denote r end.
Definition zeros n r := if n =? 0 then r else match r with
  | Blank => Blank | Zeros m s => Zeros (n+m) s | _ => Zeros n r end.
Definition pairs n r := if n =? 0 then r else match r with
  | Pairs m s => Pairs (n+m) s | _ => Pairs n r end.
Definition push b r := match b with
  | S0 => zeros 1 r
  | BusyCoq.BB62.S1 => match r with
      | Blank => Pairs 1 Blank
      | Zeros n s => if n =? 0 then OneBit r else pairs 1 (zeros (n-1) s)
      | _ => OneBit r end end.
Fixpoint pop r : Sym*Tape := match r with
  | Blank => (S0,Blank)
  | OneBit s => (1%sym,s)
  | Zeros n s => if n =? 0 then pop s else (S0,zeros (n-1) s)
  | Pairs n s => if n =? 0 then pop s else (1%sym,zeros 1 (pairs (n-1) s)) end.
Fixpoint prefix (w:list Sym) r := match w with
  | nil => r | b::w => push b (prefix w r) end.
Fixpoint tape_eqb r s := match r,s with
  | Blank,Blank => true
  | Zeros n r,Zeros m s | Pairs n r,Pairs m s => (n =? m) && tape_eqb r s
  | OneBit r,OneBit s => tape_eqb r s
  | _,_ => false end.

Definition send (f:N->N->N->Tape->option Tape) r : option (N*Tape) :=
  match r with
  | Blank => Some (0,Pairs 3 Blank)
  | Pairs x Blank => Some (x,Pairs (x*2+3) Blank)
  | Pairs x (Zeros d s) => if d =? 0 then None else
      match f x 0 (d-1) s with Some t => Some (x,t) | None => None end
  | Zeros d s => if d =? 0 then None else
      match f 0 0 (d-1) s with Some t => Some (0,t) | None => None end
  | _ => None end.

(* A finite short-gap tail has at most two normal columns. *)
Definition gap_view r := match r with
  | Pairs x Blank => if 2<=?x then Some (x-2,0) else None
  | Pairs x (Zeros z (Pairs n Blank)) =>
      if (2<=?x) && (z=?1) then Some (x-2,n) else None
  | _ => None end.
Definition gap_out t n := pairs t (zeros 1 (pairs (2+n) Blank)).

(* The suffix effect is shared by empty and nonempty left counters. *)
Definition d1_effect (g:Tape->option(N*Tape)) y r : option(N*Tape) :=
  if y=?1 then match r with
    | Blank => Some (3,prefix [1%sym;0%sym;1%sym] Blank)
    | Zeros z s => if 4<=?z then Some (3,prefix [1%sym;0%sym;1%sym] (zeros (z-4) s))
        else if z=?3 then match gap_view s with
          | Some (t,n) => Some (3,pairs 1 (zeros 3 (gap_out t n))) | None => None end
        else None
    | OneBit (Pairs x Blank) => if 1<=?x then
        Some (4,pairs (x-1) (zeros 1 (pairs 2 Blank))) else None
    | _ => None end
  else if 2<=?y then match r with
    | Blank => Some (3,pairs (y-2) (prefix [0%sym;1%sym;0%sym;1%sym] Blank))
    | Zeros z s => if 3<=?z then
        Some (3,pairs (y-2) (prefix [0%sym;1%sym;0%sym;1%sym] (zeros (z-3) s)))
      else if z=?1 then match pop s with
        | (BusyCoq.BB62.S1,s) => match g s with
          | Some (u,s) => Some (3,pairs (y-2) (zeros (1+u) s)) | None=>None end
        | _ => None end
      else if z=?2 then match gap_view s with
        | Some (t,n) => Some (3,pairs (y-2) (prefix [0%sym;1%sym;0%sym]
            (zeros 3 (gap_out t n)))) | None => None end
      else None
    | _ => None end
  else None.
Definition twos (f:N->N->N->Tape->option Tape) b c z r :=
  let n := N.min (b/2) (z/4) in
  if (0<?n) && (n*2<=?b) && (n*4<=?z) then
    f (b-n*2) (c+n*3) 1 (pairs 2 (zeros (z-n*4) r))
  else None.
Definition finish_d1 (f:N->N->N->Tape->option Tape) b c y r :=
  match d1_effect (send f) y r with
  | Some (d,s) => if b=?0 then Some (pairs (c+2) (zeros d s))
      else f (b-1) (c+1) d s
  | None => None end.
Definition residue1 (f:N->N->N->Tape->option Tape) b c r := match r with
  | Pairs y s =>
      let result := if y=?2 then match s with
        | Blank => twos f b c ((b/2)*4) Blank
        | Zeros z r => twos f b c z r | _ => None end else None in
      match result with Some s => Some s | None => finish_d1 f b c y s end
  | _ => None end.
Definition resume (f:N->N->N->Tape->option Tape) b c d r :=
  if (b=?0) && (3<=?d) then Some (pairs (c+3) (zeros (d-3) r)) else
  if d=?0 then match r with
    | Pairs y s => f b (c+y) 0 s
    | OneBit s => match send f s with
        | Some (u,s) => if b=?0 then Some (pairs (c+1) (zeros u s)) else f (b-1) c u s
        | None => None end
    | _ => None end
  else if d=?2 then if b=?0 then Some (pairs (c+2) (push 1%sym r))
      else f (b-1) (c+1) 0 (push 1%sym r)
  else if d=?1 then residue1 f b c r else None.
Fixpoint run fuel b c d r := match fuel with
  | O => None
  | S fuel => match r with
    | Blank => Some (Pairs (b*2+c+3) Blank)
    | Zeros z s => run fuel b c (d+z) s
    | _ => let n := N.min b (d/3) in
      if (n<=?b) && (n*3<=?d) then resume (run fuel) (b-n) (c+n*2) (d-n*3) r
      else None end end.

Local Close Scope N_scope.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).
Lemma zeros_spec n r: denote (zeros n r) = [0]^^(nn n) *> denote r.
Proof.
  unfold zeros; destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; reflexivity.
  - destruct r; cbn [denote]; try reflexivity.
    + rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
    + rewrite N2Nat.inj_add; simpl_tape; reflexivity.
Qed.
Lemma pairs_spec n r: denote (pairs n r) = [1;0]^^(nn n) *> denote r.
Proof.
  unfold pairs; destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; reflexivity.
  - destruct r; cbn [denote]; try reflexivity.
    rewrite N2Nat.inj_add; simpl_tape; reflexivity.
Qed.
Lemma nn_pred n: (n<>0)%N -> nn n = 1+nn (n-1)%N.
Proof. lia. Qed.
Lemma push_spec b r: denote (push b r) = b >> denote r.
Proof.
  destruct b; cbn [push].
  - rewrite zeros_spec; reflexivity.
  - destruct r; cbn [push denote]; try reflexivity.
    + simpl_tape; reflexivity.
    + destruct (N.eqb n 0) eqn:E; [reflexivity|].
      apply N.eqb_neq in E; rewrite pairs_spec, zeros_spec, (nn_pred _ E); reflexivity.
Qed.
Lemma pop_spec r: let '(b,s):=pop r in denote r = b >> denote s.
Proof.
  induction r; cbn [pop denote].
  - rewrite <-const_unfold; reflexivity.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; exact IHr.
    + apply N.eqb_neq in E; rewrite zeros_spec, (nn_pred _ E); reflexivity.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; exact IHr.
    + apply N.eqb_neq in E; rewrite zeros_spec, pairs_spec, (nn_pred _ E); reflexivity.
  - reflexivity.
Qed.
Lemma prefix_spec w r: denote (prefix w r)=w*>denote r.
Proof. induction w; cbn [prefix]; [reflexivity|rewrite push_spec, IHw; reflexivity]. Qed.
Lemma tape_eqb_spec r s: tape_eqb r s=true -> r=s.
Proof.
  gen s; induction r; destruct s; cbn [tape_eqb]; try discriminate;
    try solve [intros H; f_equal; auto].
  all: intros H; apply andb_true_iff in H; destruct H as [Hn Hr];
    apply N.eqb_eq in Hn; subst; f_equal; auto.
Qed.
Definition RunSpec f := forall b c d r s,
  f b c d r=Some s -> Run (nn b) (nn c) (nn d) (denote r) (denote s).
Definition SendSpec g := forall r u s,
  g r=Some (u,s) -> P (nn u) (denote r) (denote s).
Local Opaque N.add N.sub N.mul zeros pairs push pop prefix.
Ltac unbool := repeat match goal with
  | H:(if _ then _ else false)=true |- _ => apply andb_true_iff in H;
      let HA:=fresh "HcheckA" in let HB:=fresh "HcheckB" in destruct H as [HA HB]
  | H:N.eqb _ _=true |- _ => apply N.eqb_eq in H
  | H:N.eqb _ _=false |- _ => apply N.eqb_neq in H
  | H:N.leb _ _=true |- _ => apply N.leb_le in H
  | H:N.ltb _ _=true |- _ => apply N.ltb_lt in H end.
Ltac natify := repeat (rewrite N2Nat.inj_add || rewrite N2Nat.inj_mul || rewrite N2Nat.inj_sub).
Ltac tape_simpl := repeat (rewrite pairs_spec || rewrite zeros_spec || rewrite push_spec || rewrite prefix_spec); natify.

Lemma send_spec f: RunSpec f -> SendSpec (send f).
Proof.
  intros HF r u s; destruct r as [|d r|x r|r]; cbn [send]; try discriminate.
  - intros H; injection H as Hu Hs; subst u s; intros l; cbn [denote];
      applys_eq (RunTail l 0 0 0 0); unfold S1; simpl_tape; repeat rewrite <-const_unfold; reflexivity.
  - destruct (N.eqb d 0) eqn:Hd; try discriminate.
    destruct (f 0%N 0%N (d-1)%N r) eqn:E; try discriminate.
    intros H; injection H as Hu Hs; subst u s; unbool; intros l.
    applys_eq (HF _ _ _ _ _ E l 0%nat); cbn [denote]; unfold S1; simpl_tape; flia.
    rewrite (nn_pred _ Hd); reflexivity.
  - destruct r as [|d r|d r|r]; try discriminate.
    + intros H; injection H as Hu Hs; subst u s; intros l; cbn [denote].
      applys_eq (RunTail l 0 (nn x) 0 0); unfold S1; natify; simpl_tape; repeat rewrite <-const_unfold; flia.
    + destruct (N.eqb d 0) eqn:Hd; try discriminate.
      destruct (f x 0%N (d-1)%N r) eqn:E; try discriminate.
      intros H; injection H as Hu Hs; subst u s; unbool; applys_eq (Head0 (nn x) (nn (d-1)%N)
        (denote r) (denote t) (HF _ _ _ _ _ E)); cbn [denote]; unfold Stages7.Col; flia.
Qed.

Lemma gap_view_spec r t n: gap_view r=Some (t,n) ->
  denote r=[1;0]^^(2+nn t)*>[0]*>[1;0]^^(nn n)*>0inf.
Proof.
  destruct r as [|z r|x r|r]; cbn [gap_view]; try discriminate.
  destruct r as [|z r|z r|r]; try discriminate.
  - destruct (2<=?x)%N eqn:E; try discriminate.
    intros H; injection H as Ht Hn; subst; unbool; cbn [denote Str_app];
      repeat rewrite <-const_unfold; flia.
  - destruct r as [|y r|y r|r]; try discriminate; destruct r; try discriminate.
    destruct ((2<=?x) && (z=?1))%N eqn:E; try discriminate.
    intros H; injection H as Ht Hn; subst; unbool; subst z; cbn [denote]; flia.
Qed.
Lemma gap_out_spec t n:
  denote (gap_out t n)=[1;0]^^(nn t)*>[0]*>[1;0]^^(2+nn n)*>0inf.
Proof. unfold gap_out; tape_simpl; cbn [denote]; flia. Qed.

Definition Effect r d s :=
  (forall l a c, S1 l a 0 c 1 r -->*
    l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]^^d*>s) /\
  (forall l a b c, S1 l a (1+b) c 1 r -->* S1 l (1+a) b (1+c) d s).
Lemma Effect_normal y z r:
  Effect ([1;0]^^(2+y)*>[0]^^(3+z)*>r) 3 ([1;0]^^y*>[0;1;0;1]*>[0]^^z*>r).
Proof. split; intros; [apply D1_empty|apply D1_inc]. Qed.
Lemma Effect_one z r:
  Effect ([1;0]*>[0]^^(4+z)*>r) 3 ([1;0;1]*>[0]^^z*>r).
Proof. split; intros; [apply D1_empty_one|apply D1_one]. Qed.
Lemma Effect_one_tail t n:
  Effect ([1;0]*>[0]^^3*>[1;0]^^(2+t)*>[0]*>[1;0]^^n*>0inf) 3
    ([1;0]*>[0]^^3*>[1;0]^^t*>[0]*>[1;0]^^(2+n)*>0inf).
Proof. split; intros; [apply D1_empty_one_tail|apply D1_one_tail]. Qed.
Lemma Effect_odd_tail y:
  Effect ([1;0;1]*>[1;0]^^(1+y)*>0inf) 4 ([1;0]^^y*>[0]*>[1;0]^^2*>0inf).
Proof. split; intros; [apply D1_empty_one_odd_tail|apply D1_one_odd_tail]. Qed.
Lemma Effect_gap_tail y t n:
  Effect ([1;0]^^(2+y)*>[0]^^2*>[1;0]^^(2+t)*>[0]*>[1;0]^^n*>0inf) 3
    ([1;0]^^y*>[0;1;0]*>[0]^^3*>[1;0]^^t*>[0]*>[1;0]^^(2+n)*>0inf).
Proof. split; intros; [apply D1_empty_gap_tail|apply D1_gap_tail]. Qed.
Lemma Effect_call y u r s: P u r s ->
  Effect ([1;0]^^(2+y)*>[0;1]*>r) 3 ([1;0]^^y*>[0]^^(1+u)*>s).
Proof. intros H; split; intros; [apply D1_empty_call|apply D1_call]; exact H. Qed.

Lemma d1_effect_spec g: SendSpec g -> forall y r d s,
  d1_effect g y r=Some (d,s) ->
  Effect ([1;0]^^(nn y)*>denote r) (nn d) (denote s).
Proof.
  intros SG y r d s; unfold d1_effect; destruct (y=?1)%N eqn:Hy.
  - unbool; subst y; destruct r as [|z r|z r|r]; try discriminate.
    + intros H; injection H as Hd Hs; subst; tape_simpl; cbn [denote].
      applys_eq (Effect_one 0 0inf); repeat rewrite (lpow_all0 [0]) by solve_const0_eq; flia.
    + destruct (4<=?z)%N eqn:Hz.
      * intros H; injection H as Hd Hs; subst; unbool; tape_simpl; cbn [denote].
        applys_eq (Effect_one (nn (z-4)%N) (denote r)); flia.
      * destruct (z=?3)%N eqn:Hz3; try discriminate.
        destruct (gap_view r) as [[t n]|] eqn:E; try discriminate.
        intros H; injection H as Hd Hs; subst; unbool; subst z.
        tape_simpl; rewrite gap_out_spec; cbn [denote]; rewrite (gap_view_spec _ _ _ E).
        applys_eq (Effect_one_tail (nn t) (nn n)); flia.
    + destruct r as [|z r|x r|r]; try discriminate; destruct r; try discriminate.
      destruct (1<=?x)%N eqn:Hx; try discriminate.
      intros H; injection H as Hd Hs; subst; unbool; tape_simpl; cbn [denote].
      rewrite (nn_pred x ltac:(lia)); applys_eq (Effect_odd_tail (nn (x-1)%N)); simpl_tape; flia.
  - destruct (2<=?y)%N eqn:Hy2; try discriminate; unbool.
    destruct r as [|z r|z r|r]; try discriminate.
    + intros H; injection H as Hd Hs; subst; tape_simpl; cbn [denote].
      applys_eq (Effect_normal (nn (y-2)%N) 0 0inf); repeat rewrite (lpow_all0 [0]) by solve_const0_eq; flia.
    + destruct (3<=?z)%N eqn:Hz.
      * intros H; injection H as Hd Hs; subst; unbool; tape_simpl; cbn [denote].
        applys_eq (Effect_normal (nn (y-2)%N) (nn (z-3)%N) (denote r)); flia.
      * destruct (z=?1)%N eqn:Hz1.
        -- specialize (pop_spec r) as Hr; destruct (pop r) as [bit t]; destruct bit; try discriminate.
           destruct (g t) as [[u v]|] eqn:E; try discriminate.
           intros H; injection H as Hd Hs; subst; unbool; subst z; tape_simpl; cbn [denote]; rewrite Hr.
           applys_eq (Effect_call (nn (y-2)%N) (nn u) (denote t) (denote v) (SG _ _ _ E));
             flia.
        -- destruct (z=?2)%N eqn:Hz2; try discriminate.
           destruct (gap_view r) as [[t n]|] eqn:E; try discriminate.
           intros H; injection H as Hd Hs; subst; unbool; subst z.
           tape_simpl; rewrite gap_out_spec; cbn [denote]; rewrite (gap_view_spec _ _ _ E).
           applys_eq (Effect_gap_tail (nn (y-2)%N) (nn t) (nn n)); flia.
Qed.

Lemma twos_spec f: RunSpec f -> forall b c z r s,
  twos f b c z r=Some s ->
  Run (nn b) (nn c) 1 ([1;0]^^2*>[0]^^(nn z)*>denote r) (denote s).
Proof.
  intros HF b c z r s; unfold twos; remember (N.min (b/2) (z/4)) as n.
  destruct ((0<?n) && (n*2<=?b) && (n*4<=?z))%N eqn:E; try discriminate; unbool.
  intros H l a.
  mid (S1 l (nn n*2+a) (nn (b-n*2)%N) (nn (c+n*3)%N) 1
    (denote (pairs 2 (zeros (z-n*4)%N r)))).
  - tape_simpl; applys_eq (D1_twos (nn n) l a (nn (b-n*2)%N) (nn c) (nn (z-n*4)%N) (denote r)); flia.
  - applys_eq (HF _ _ _ _ _ H l (nn n*2+a)); flia.
Qed.
Lemma finish_d1_spec f: RunSpec f -> forall b c y r s,
  finish_d1 f b c y r=Some s ->
  Run (nn b) (nn c) 1 ([1;0]^^(nn y)*>denote r) (denote s).
Proof.
  intros HF b c y r s; unfold finish_d1.
  destruct (d1_effect (send f) y r) as [[d t]|] eqn:E; try discriminate.
  destruct (d1_effect_spec _ (send_spec _ HF) _ _ _ _ E) as [E0 E1].
  destruct (b=?0)%N eqn:Hb; unbool.
  - subst b; intros H; injection H as Hs; subst s; intros l a; tape_simpl.
    applys_eq (E0 l a (nn c)); flia.
  - intros H l a.
    mid (S1 l (1+a) (nn (b-1)%N) (nn (c+1)%N) (nn d) (denote t)).
    + applys_eq (E1 l a (nn (b-1)%N) (nn c)); flia.
    + applys_eq (HF _ _ _ _ _ H l (1+a)); flia.
Qed.
Lemma residue1_spec f: RunSpec f -> forall b c r s,
  residue1 f b c r=Some s -> Run (nn b) (nn c) 1 (denote r) (denote s).
Proof.
  intros HF b c r s; destruct r as [|z r|y r|r]; cbn [residue1]; try discriminate.
  destruct (y=?2)%N eqn:Hy.
  - unbool; subst y; destruct r as [|z r|z r|r];
      try (apply finish_d1_spec; assumption).
    + destruct (twos f b c ((b/2)*4)%N Blank) eqn:E.
      * intros H; injection H as Hs; subst s; cbn [denote].
        applys_eq (twos_spec _ HF _ _ _ _ _ E); cbn [denote]; simpl_tape;
          repeat rewrite (lpow_all0 [0]) by solve_const0_eq;
          repeat rewrite <-const_unfold; reflexivity.
      * apply finish_d1_spec; assumption.
    + destruct (twos f b c z r) eqn:E.
      * intros H; injection H as Hs; subst s; cbn [denote]; eapply twos_spec; eassumption.
      * apply finish_d1_spec; assumption.
  - apply finish_d1_spec; assumption.
Qed.
Lemma resume_spec f: RunSpec f -> RunSpec (resume f).
Proof.
  intros HF b c d r s; unfold resume.
  destruct ((b=?0) && (3<=?d))%N eqn:HE.
  - unbool; subst b; intros H; injection H as Hs; subst s; tape_simpl.
    applys_eq (REnd (nn c) (nn (d-3)%N) (denote r)); unfold Stages7.Col; flia.
  - destruct (d=?0)%N eqn:Hd.
    + unbool; subst d; destruct r as [|y r|y r|r]; try discriminate.
      * intros H; cbn [denote].
        applys_eq (RMerge (nn b) (nn c) (nn y) 0 (denote r) (denote s));
          unfold Stages7.Col; try flia.
        applys_eq (HF _ _ _ _ _ H); flia.
      * destruct (send f r) as [[u t]|] eqn:E; try discriminate.
        specialize (send_spec _ HF _ _ _ E) as HP.
        destruct (b=?0)%N eqn:Hb; unbool.
        -- subst b; intros H; injection H as Hs; subst s; intros l a; tape_simpl; cbn [denote].
           applys_eq (Empty0_call l a (nn c) (nn u) (denote r) (denote t) HP); flia.
        -- intros H l a; cbn [denote].
           mid (S1 l (1+a) (nn (b-1)%N) (nn c) (nn u) (denote t)).
           ++ applys_eq (Call l a (nn (b-1)%N) (nn c) (nn u) (denote r) (denote t) HP); flia.
           ++ applys_eq (HF _ _ _ _ _ H l (1+a)); flia.
    + destruct (d=?2)%N eqn:Hd2.
      * unbool; subst d; destruct (b=?0)%N eqn:Hb; unbool.
        -- subst b; intros H; injection H as Hs; subst s; intros l a; tape_simpl.
           applys_eq (Empty2 l a (nn c) (denote r)); flia.
        -- intros H l a.
           mid (S1 l (1+a) (nn (b-1)%N) (nn (c+1)%N) 0 (denote (push 1%sym r))).
           ++ rewrite push_spec; applys_eq (Inc2 l a (nn (b-1)%N) (nn c) (denote r)); flia.
           ++ applys_eq (HF _ _ _ _ _ H l (1+a)); flia.
      * destruct (d=?1)%N eqn:Hd1; try discriminate; unbool; subst d.
        apply residue1_spec; assumption.
Qed.
Lemma run_spec fuel: RunSpec (run fuel).
Proof.
  induction fuel as [|fuel IH]; [intros b c d r s H; discriminate|].
  intros b c d r s; destruct r as [|z r|y r|r]; cbn [run].
  - intros H; injection H as Hs; subst s; cbn [denote].
    applys_eq (RTail (nn b) (nn c) (nn d)); unfold Stages7.Col; flia.
  - intros H l a; applys_eq (IH _ _ _ _ _ H l a); cbn [denote]; unfold S1; natify; simpl_tape; flia.
  - remember (N.min b (d/3)) as n.
    destruct ((n<=?b) && (n*3<=?d))%N eqn:E; try discriminate; unbool; intros H.
    applys_eq (RInc (nn n) (nn (b-n)%N) (nn c) (nn (d-n*3)%N)
      (denote (Pairs y r)) (denote s)); try flia.
    applys_eq (resume_spec _ IH _ _ _ _ _ H); flia.
  - remember (N.min b (d/3)) as n.
    destruct ((n<=?b) && (n*3<=?d))%N eqn:E; try discriminate; unbool; intros H.
    applys_eq (RInc (nn n) (nn (b-n)%N) (nn c) (nn (d-n*3)%N)
      (denote (OneBit r)) (denote s)); try flia.
    applys_eq (resume_spec _ IH _ _ _ _ _ H); flia.
Qed.
Definition check_call fuel r u s := match send (run fuel) r with
  | Some (v,t) => (u=?v)%N && tape_eqb s t | None => false end.
Theorem check_call_spec fuel r u s:
  check_call fuel r u s=true -> P (nn u) (denote r) (denote s).
Proof.
  unfold check_call; destruct (send (run fuel) r) as [[v t]|] eqn:E; try discriminate.
  intros H; apply andb_true_iff in H; destruct H as [Hu Hs].
  apply N.eqb_eq in Hu; apply tape_eqb_spec in Hs; subst.
  apply (send_spec _ (run_spec fuel) _ _ _ E).
Qed.

End Compute7.
End FT7TM7Compute.

(* Shared definitions from FT7TM7Invariant.v. *)
Module FT7TM7Invariant.
(* The stable hierarchy for ft7 TM3--TM7. Parameters remain symbolic. *)
Import BusyCoq.Individual62.
Import ZifyNat Lia PeanoNat.
Import FT7TM7Rules FT7TM7Stages.
Import Rules7 Stages7.

Module Invariant7.

Lemma MergeCounter i j x z r:
  P (i+j) (Mark 1 (i+j) (i*3) (Col x (j*3+(3+z)) r))
    (Col (x+(i+j)*2+5) z r).
Proof.
  intros l; unfold Mark, Col.
  mid (S1 l 0 (i+j) 2 (i*3+0) ([1;0]^^x*>[0]^^(j*3+(3+z))*>r)).
  unfold S1; finish.
  follow Incs.
  mid (S1 l i (j+0) (i*2+2+x) (j*3+(3+z)) r).
  unfold S1; rewrite (lpow_add _ (i*2+2) x); simpl_tape; finish; flia.
  follow Incs; follow Empty_b; finish; flia.
Qed.
Lemma MergeTail i j x:
  P (i+j) (Mark 1 (i+j) (i*3) (Col x 0 0inf))
    (Col (x+(i+j)*2+5) 0 0inf).
Proof.
  intros l; unfold Mark, Col.
  mid (S1 l 0 (i+j) 2 (i*3+0) ([1;0]^^x*>0inf)). unfold S1; finish.
  follow Incs.
  mid (S1 l i j (i*2+2+x) 0 0inf).
  unfold S1; rewrite (lpow_add _ (i*2+2) x); simpl_tape; finish; flia.
  follow RunTail; finish; flia.
Qed.
Lemma MarkedTail p d: P p (Mark 1 p d 0inf) (Col (p*2+5) 0 0inf).
Proof.
  intros l; unfold Mark, Col.
  mid (S1 l 0 p 2 d 0inf). unfold S1; finish.
  follow RunTail; finish; flia.
Qed.

(* q=5+6u, v=6w. The normal middle branch of the three-call interface. *)
Inductive Round u w : nat -> side -> nat -> side -> Prop :=
| RoundIntro a b c r s t v:
  P (20+u*18) (Mark 1 (20+u*18) (15+u*18+w*12+b) r) s ->
  P (5+u*6) (Mark 1 (5+u*6) (3+u*6+w*6) s)
    (Col (57+u*48+a) (12+(u-w)*6+c) t) ->
  P (62+u*54+a) (Mark 1 (62+u*54+a) c t) v ->
  Round u w b r a v.

Lemma Round_merge u w x z r s: w<=u ->
  P (65+u*54+x) (Mark 1 (65+u*54+x) z r) s ->
  Round u w 3 (Col x (72+u*54-w*24+z) r) (x+3) s.
Proof.
  intros Hw H.
  eapply RoundIntro with (c:=z) (t:=r)
    (s:=Col (x+45+u*36) (27+u*18-w*12+z) r).
  - applys_eq (MergeCounter (6+u*6+w*4) (14+u*12-w*4) x
      (27+u*18-w*12+z) r); flia.
  - applys_eq (MergeCounter (1+u*2+w*2) (4+u*4-w*2) (x+45+u*36)
      (12+(u-w)*6+z) r); flia.
  - applys_eq H; flia.
Qed.
Lemma Round_call u w c r s: w<=u ->
  P (65+u*54) (Mark 1 (65+u*54) c r) s ->
  Round u w (75+u*54-w*24+c) r 3 s.
Proof.
  intros Hw H.
  eapply RoundIntro with (c:=c) (t:=r)
    (s:=Col (45+u*36) (27+u*18-w*12+c) r).
  - applys_eq (Marked1Counter (20+u*18) (27+u*18-w*12+c) r); flia.
  - applys_eq (MergeCounter (1+u*2+w*2) (4+u*4-w*2) (45+u*36)
      (12+(u-w)*6+c) r); flia.
  - applys_eq H; flia.
Qed.
Lemma Round_large u w z r: w<=u ->
  Round u w (273+u*216-w*24+z) r 3 (Col (135+u*108) z r).
Proof.
  intros Hw; applys_eq (Round_call u w ((65+u*54)*3+(3+z)) r
    (Col (135+u*108) z r)); try flia.
  applys_eq (Marked1Counter (65+u*54) z r); flia.
Qed.
Lemma Round_low u w k y: w<=u -> k+w*4<=15+u*12 ->
  Round u w (k*3) (Col y 0 0inf) (y+3) (Col (y*2+135+u*108) 0 0inf).
Proof.
  intros Hw Hk.
  eapply RoundIntro with (c:=0%nat) (t:=0inf) (s:=Col (y+45+u*36) 0 0inf).
  - applys_eq (MergeTail (5+u*6+w*4+k) (15+u*12-w*4-k) y); flia.
  - applys_eq (MergeTail (1+u*2+w*2) (4+u*4-w*2) (y+45+u*36));
      unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; flia.
  - applys_eq (MarkedTail (65+u*54+y) 0); flia.
Qed.
Lemma Round_middle u w i y: w<=u -> i<=65+u*54 ->
  Round u w (75+u*54-w*24+i*3) (Col y 0 0inf) 3
    (Col (y+135+u*108) 0 0inf).
Proof.
  intros Hw Hi; apply Round_call; [exact Hw|].
  applys_eq (MergeTail i (65+u*54-i) y); flia.
Qed.

(* Nonempty paths in the conditional layer relation. *)
Inductive Walk (R:nat->side->nat->side->Prop) : nat -> nat -> side -> nat -> side -> Prop :=
| ROne b r a s: R b r a s -> Walk R 1 b r a s
| RMore n b r a s c t: R b r a s -> Walk R n a s c t -> Walk R (1+n) b r c t.
Definition RSteps u w := Walk (Round u w).

Lemma Walk_app R n m b r a s c t:
  Walk R n b r a s -> Walk R m a s c t -> Walk R (n+m) b r c t.
Proof. intros H; induction H; intros K; cbn [Nat.add]; eauto using RMore. Qed.

Definition Embed u w b r := Col (135+u*108) (267+u*216+w*24+b) r.
Lemma Grow u w b r a v: w<=u -> Round (10+u*9) (w*4) b r a v ->
  RSteps u w 4 3 (Embed u w b r) 3 (Embed u w a v).
Proof.
  intros Hw H; destruct H as [a b c r s t v H1 H2 H3]; unfold Embed.
  eapply RMore with (a:=138+u*108) (s:=s).
  - applys_eq (Round_merge u w (135+u*108)
      (15+(10+u*9)*18+(w*4)*12+b) r s); try flia.
    applys_eq H1; flia.
  - eapply RMore with (a:=3)
      (s:=Col (57+(10+u*9)*48+a) (12+(10+u*9-w*4)*6+c) t).
    + applys_eq (Round_call u w (3+(10+u*9)*6+(w*4)*6) s
        (Col (57+(10+u*9)*48+a) (12+(10+u*9-w*4)*6+c) t)); try flia.
      applys_eq H2; flia.
    + eapply RMore with (a:=540+u*432+a) (s:=v).
      * applys_eq (Round_merge u w (57+(10+u*9)*48+a) c t v); try flia.
        applys_eq H3; flia.
      * apply ROne; applys_eq (Round_large u w (267+u*216+w*24+a) v); flia.
Qed.

Definition TailA u t := Col (135+u*108+t*12) 0 0inf.
Definition TailB u e := Col (309+u*324-e*12) 0 0inf.
Lemma CycleA u w t: w<=u -> t<=u ->
  RSteps u w 4 (3+t*6) (TailA u t) 3
    (Embed u w (3+(t*4)*6) (TailA (10+u*9) (t*4))).
Proof.
  intros Hw Ht; unfold TailA, Embed.
  eapply RMore with (a:=138+u*108+t*12) (s:=Col (405+u*324+t*24) 0 0inf).
  - applys_eq (Round_low u w (1+t*2) (135+u*108+t*12)); flia.
  - eapply RMore with (a:=3) (s:=Col (540+u*432+t*24) 0 0inf).
    + applys_eq (Round_middle u w (21+u*18+w*8+t*4) (405+u*324+t*24)); flia.
    + eapply RMore with (a:=543+u*432+t*24) (s:=Col (1215+u*972+t*48) 0 0inf).
      * applys_eq (Round_low u w 1 (540+u*432+t*24)); flia.
      * apply ROne; applys_eq (Round_large u w (270+u*216+w*24+t*24)
          (Col (1215+u*972+t*48) 0 0inf)); flia.
Qed.

Lemma CycleB u w e: w<=u -> e<=u ->
  RSteps u w 7 (90+u*108-e*6) (TailB u e) 3
    (Embed u w (90+(10+u*9)*108-(24+e*4)*6) (TailB (10+u*9) (24+e*4))).
Proof.
  intros Hw He; unfold TailB, Embed.
  eapply RMore with (a:=3) (s:=Col (444+u*432-e*12) 0 0inf).
  - applys_eq (Round_middle u w (5+u*18+w*8-e*2) (309+u*324-e*12)); flia.
  - eapply RMore with (a:=447+u*432-e*12) (s:=Col (1023+u*972-e*24) 0 0inf).
    + applys_eq (Round_low u w 1 (444+u*432-e*12)); flia.
    + eapply RMore with (a:=3)
        (s:=Col (135+u*108) (174+u*216+w*24-e*12) (Col (1023+u*972-e*24) 0 0inf)).
      * applys_eq (Round_large u w (174+u*216+w*24-e*12)
          (Col (1023+u*972-e*24) 0 0inf)); flia.
      * eapply RMore with (a:=138+u*108) (s:=Col (1428+u*1296-e*24) 0 0inf).
        -- applys_eq (Round_merge u w (135+u*108) (102+u*162+w*48-e*12)
             (Col (1023+u*972-e*24) 0 0inf) (Col (1428+u*1296-e*24) 0 0inf)); try flia.
           applys_eq (MergeTail (34+u*54+w*16-e*4) (166+u*108-w*16+e*4)
             (1023+u*972-e*24)); flia.
        -- eapply RMore with (a:=3) (s:=Col (1563+u*1404-e*24) 0 0inf).
           ++ applys_eq (Round_middle u w (21+u*18+w*8) (1428+u*1296-e*24)); flia.
           ++ eapply RMore with (a:=1566+u*1404-e*24) (s:=Col (3261+u*2916-e*48) 0 0inf).
              ** applys_eq (Round_low u w 1 (1563+u*1404-e*24)); flia.
              ** apply ROne; applys_eq (Round_large u w (1293+u*1188+w*24-e*24)
                   (Col (3261+u*2916-e*48) 0 0inf)); flia.
Qed.

Lemma Grow_steps u w n b r a s: w<=u ->
  RSteps (10+u*9) (w*4) n b r a s ->
  RSteps u w (n*4) 3 (Embed u w b r) 3 (Embed u w a s).
Proof.
  intros Hw H; induction H; cbn [Nat.mul].
  - apply Grow; assumption.
  - eapply Walk_app; [apply Grow; eassumption|exact IHWalk].
Qed.

Definition Infinite (R:nat->side->nat->side->Prop) b r :=
  forall n, exists k a s, n<=k /\ Walk R k b r a s.
Lemma Infinite_back R n b r a s:
  Walk R n b r a s -> Infinite R a s -> Infinite R b r.
Proof.
  intros H I k; destruct (I k) as [m [c [t [Hm K]]]].
  exists (n+m),c,t; split; [lia|eapply Walk_app; eassumption].
Qed.

Theorem InfiniteA u w t: 4<=u -> w<=u -> t<=u ->
  Infinite (Round u w) (3+t*6) (TailA u t).
Proof.
  intros Hu Hw Ht n; revert u w t Hu Hw Ht; induction n; intros u w t Hu Hw Ht.
  - exists 4,3,(Embed u w (3+(t*4)*6) (TailA (10+u*9) (t*4))).
    split; [lia|apply CycleA; assumption].
  - destruct (IHn (10+u*9) (w*4) (t*4)) as [k [a [s [Hk K]]]]; try lia.
    exists (4+k*4),3,(Embed u w a s); split; [lia|].
    eapply Walk_app; [apply CycleA; assumption|apply Grow_steps; assumption].
Qed.
Theorem InfiniteB u w e: 4<=u -> w<=u -> e<=u ->
  Infinite (Round u w) (90+u*108-e*6) (TailB u e).
Proof.
  intros Hu Hw He n; revert u w e Hu Hw He; induction n; intros u w e Hu Hw He.
  - exists 7,3,(Embed u w (90+(10+u*9)*108-(24+e*4)*6)
      (TailB (10+u*9) (24+e*4))).
    split; [lia|apply CycleB; assumption].
  - destruct (IHn (10+u*9) (w*4) (24+e*4)) as [k [a [s [Hk K]]]]; try lia.
    exists (7+k*4),3,(Embed u w a s); split; [lia|].
    eapply Walk_app; [apply CycleB; assumption|apply Grow_steps; assumption].
Qed.

(* Only the base layer needs a concrete whole-tape interpretation F.
   Its first argument retains the left-prefix growth omitted by the simulator. *)
Definition Realizes (R:nat->side->nat->side->Prop) (F:nat->nat->side->Q*tape) :=
  forall i b r a s, R b r a s -> F i b r -[tm]->+ F (1+i) a s.
Lemma Walk_sound R F n b r a s: Realizes R F -> Walk R n b r a s ->
  forall i, exists k, n<=k /\ F i b r -[tm]->>k / F (n+i) a s.
Proof.
  intros HR H; induction H as [b r a s HX|n b r a s c t HX K0 IHWalk]; intros i.
  - destruct (progress_multistep _ _ _ (HR i b r a s HX)) as [k K].
    exists (S k); split; [lia|exact K].
  - destruct (progress_multistep _ _ _ (HR i b r a s HX)) as [k K].
    destruct (IHWalk (1+i)) as [j [Hj J]].
    exists (S k+j); split; [lia|].
    applys_eq (multistep_trans _ _ _ _ _ _ K J); flia.
Qed.
Theorem Infinite_nonhalt R F i b r: Realizes R F -> Infinite R b r ->
  ~halts tm (F i b r).
Proof.
  intros HR I [n Hn]; destruct (I (S n)) as [k [a [s [Hk K]]]].
  destruct (Walk_sound _ _ _ _ _ _ _ HR K i) as [j [Hj J]].
  eapply exceeds_halt with (n:=j); [exact Hn|lia|exact J].
Qed.

(* A cut can move across a proved complete call without constructing the
   intervening whole-tape configurations. The first R call is NOT omitted. *)
Definition Compose (R S:nat->side->nat->side->Prop) b r a s :=
  exists c t, R b r c t /\ S c t a s.
Lemma Walk_rotate R S n b r a s c t:
  R b r a s -> Walk (Compose S R) n a s c t ->
  exists d v, Walk (Compose R S) n b r d v /\ R d v c t.
Proof.
  intros A H; revert b r A;
    induction H as [b r a s HX|n b r a s c t HX K0 IHWalk]; intros b0 r0 A;
    destruct HX as [d [v [B C]]].
  - exists d,v; split; [apply ROne; unfold Compose; eauto|exact C].
  - destruct (IHWalk d v C) as [x [y [K L]]].
    exists x,y; split; [eapply RMore; [unfold Compose; eauto|exact K]|exact L].
Qed.
Lemma Infinite_rotate R S b r a s:
  R b r a s -> Infinite (Compose S R) a s -> Infinite (Compose R S) b r.
Proof.
  intros A I n; destruct (I n) as [k [c [t [Hk K]]]].
  destruct (Walk_rotate _ _ _ _ _ _ _ _ _ A K) as [d [v [J L]]].
  exists k,d,v; auto.
Qed.

Lemma Walk_embed R S f g m:
  (forall b r a s, R b r a s -> Walk S m (f b r) (g b r) (f a s) (g a s)) ->
  forall n b r a s, Walk R n b r a s ->
    Walk S (n*m) (f b r) (g b r) (f a s) (g a s).
Proof.
  intros H n b r a s K;
    induction K as [b r a s HX|n b r a s c t HX K0 IH]; cbn [Nat.mul].
  - rewrite Nat.add_0_r; apply H; assumption.
  - eapply Walk_app; [apply H; eassumption|exact IH].
Qed.
Lemma Infinite_embed R S f g m b r: 1<=m ->
  (forall b r a s, R b r a s -> Walk S m (f b r) (g b r) (f a s) (g a s)) ->
  Infinite R b r -> Infinite S (f b r) (g b r).
Proof.
  intros Hm H I n; destruct (I n) as [k [a [s [Hk K]]]].
  exists (k*m),(f a s),(g a s); split; [nia|eapply Walk_embed; eassumption].
Qed.

Inductive Two (K:nat->side->side) p k : nat->side->nat->side->Prop :=
| TwoIntro d a r s t: P p (K d r) s -> P (k+a) s t -> Two K p k d r a t.
Definition Eight := Two (Mark 4 497) 497 461.
Lemma Eight_realizes n:
  Realizes Eight (fun i d r => 0inf <{{A}} G (n+i*8) d r).
Proof.
  intros i d r a t H; destruct H as [d a r s t H K].
  applys_eq (EightCycle (n+i*8) d a r s t H K); unfold G; flia.
Qed.
Theorem Eight_nonhalt n d r: Infinite Eight d r -> ~halts tm (0inf <{{A}} G n d r).
Proof.
  intros I; applys_eq (Infinite_nonhalt Eight
    (fun i d r => 0inf <{{A}} G (n+i*8) d r) 0 d r (Eight_realizes n) I); cbn beta; flia.
Qed.

End Invariant7.
End FT7TM7Invariant.

(* Shared definitions from FT7TM7Layers.v. *)
Module FT7TM7Layers.
(* Checked finite hierarchy rules. Arithmetic certificates use N, while
   semantic parameters are interpreted with N.to_nat. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith ZifyNat Lia PeanoNat List.
Import FT7TM7Rules FT7TM7Stages FT7TM7Columns FT7TM7Invariant.
Import Rules7 Stages7 Columns7 Invariant7.

Module Layers7.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).
Inductive Kind := C0 | M1 | M4.
Definition form h x z r := match h with
  | C0 => Col x z r | M1 => Mark 1 x z r | M4 => Mark 4 x z r end.
Definition keqb x y := match x,y with
  | C0,C0 | M1,M1 | M4,M4 => true | _,_ => false end.
Lemma keqb_spec x y: keqb x y=true -> x=y.
Proof. destruct x,y; cbn; congruence. Qed.

Inductive Case := ZC | Z1E | Z1O | Z4Empty | Z4E | Z4O
  | DCE | DCO | D1E | D1O | D4E | D4O.
Record Row := RowMake { ri:Kind; ro:Kind; rb:N; rd:N; rx:N; rz:N }.
Definition row e n := match e with
  | ZC => RowMake C0 C0 n 0 (n*2+3) (n*3+3)
  | Z1E => RowMake M1 M4 (n*2) 0 (n*3+2) (n*4+4)
  | Z1O => RowMake M1 M1 (n*2+1) 0 (n*3+4) (n*4+4)
  | Z4Empty => RowMake M4 M1 0 0 3 0
  | Z4E => RowMake M4 M4 (1+n*2) 0 (n*3+4) (n*4+4)
  | Z4O => RowMake M4 M1 (2+n*2) 0 (n*3+6) (n*4+4)
  | DCE => RowMake C0 M4 (2+n*2) 1 (3+n*3) (8+n*4)
  | DCO => RowMake C0 M1 (3+n*2) 1 (5+n*3) (8+n*4)
  | D1E => RowMake M1 M4 (4+n*2) 1 (8+n*3) (11+n*4)
  | D1O => RowMake M1 M1 (5+n*2) 1 (10+n*3) (11+n*4)
  | D4E => RowMake M4 M4 (4+n*2) 1 (8+n*3) (8+n*4)
  | D4O => RowMake M4 M1 (5+n*2) 1 (10+n*3) (8+n*4)
  end%N.
Local Opaque N.add N.mul N.sub.
Ltac unbool := repeat match goal with
  | H:(if _ then _ else false)=true |- _ => apply and_true_iff in H; destruct H
  | H:N.eqb _ _=true |- _ => apply N.eqb_eq in H
  | H:N.leb _ _=true |- _ => apply N.leb_le in H
  end.

Lemma row_spec e n c x z r:
  let a := row e n in
  Run (nn (rb a)) c (nn (rd a)) (form (ri a) (2+x) (nn (rz a)+z) r)
    (form (ro a) (2+x+c+nn (rx a)) z r).
Proof.
  destruct e; cbn [row ri ro rb rd rx rz form].
  - applys_eq (ZeroCol (nn n) c (2+x) z r); flia.
  - apply ZeroMark1; applys_eq (TwosEven (nn n) (c+(2+x)) z r); flia.
  - apply ZeroMark1; applys_eq (TwosOdd (nn n) (c+(2+x)) z r); flia.
  - applys_eq (ZeroMark4Empty c (2+x) z r); flia.
  - applys_eq (ZeroMark4 (nn n*2) c (2+x) (nn (n*4+4)%N+z) r
      (Mark 4 (2+x+c+nn (n*3+4)%N) z r)); try flia.
    applys_eq (TwosEven (nn n) (2+c+(2+x)) z r); flia.
  - applys_eq (ZeroMark4 (nn n*2+1) c (2+x) (nn (n*4+4)%N+z) r
      (Mark 1 (2+x+c+nn (n*3+6)%N) z r)); try flia.
    applys_eq (TwosOdd (nn n) (2+c+(2+x)) z r); flia.
  - applys_eq (NormalEven (nn n) c x z r); flia.
  - applys_eq (NormalOdd (nn n) c x z r); flia.
  - applys_eq (Mark1Even (nn n) c x z r); flia.
  - applys_eq (Mark1Odd (nn n) c x z r); flia.
  - applys_eq (Mark4Even (nn n) c x z r); flia.
  - applys_eq (Mark4Odd (nn n) c x z r); flia.
Qed.

Record Map := MapMake { mo:Kind; mx:N; mz:N }.
Definition Local h p d t m := forall x z r, 2<=x ->
  P (nn p) (form h (nn p) (nn d) (form t x (nn (mz m)+z) r))
    (form (mo m) (x+nn (mx m)) z r).
Definition local_check h p d t i e n := (
  let a := row e n in
  if keqb t (ri a) then
    match h with
    | C0 => if (p =? i+rb a) && (d =? 1+i*3+rd a)
        then Some (MapMake (ro a) (i*2+rx a) (rz a)) else None
    | M1 => if (p =? i+rb a) && (d =? i*3+rd a)
        then Some (MapMake (ro a) (2+i*2+rx a) (rz a)) else None
    | M4 => if (p =? 1+i+rb a) && (d =? i*3+rd a)
        then Some (MapMake (ro a) (4+i*2+rx a) (rz a)) else None
    end
  else None)%N.

Lemma local_check_spec h p d t i e n m:
  local_check h p d t i e n=Some m -> Local h p d t m.
Proof.
  unfold local_check; destruct (keqb t (ri (row e n))) eqn:Ht; try discriminate.
  apply keqb_spec in Ht; subst t.
  destruct h.
  - destruct ((p =? i+rb (row e n)) && (d =? 1+i*3+rd (row e n)))%N eqn:E; try discriminate.
    intros H; injection H as Hm; subst m; unbool.
    intros x z r Hx; cbn [form mo mx mz].
    applys_eq (Head0 (nn p) (nn (i*3+rd (row e n))%N)
      (form (ri (row e n)) x (nn (rz (row e n))+z) r)
      (form (ro (row e n)) (x+nn (i*2+rx (row e n))%N) z r)); try flia.
    applys_eq (RInc (nn i) (nn (rb (row e n))) 0 (nn (rd (row e n)))
      (form (ri (row e n)) x (nn (rz (row e n))+z) r)
      (form (ro (row e n)) (x+nn (i*2+rx (row e n))%N) z r)); try flia.
    applys_eq (row_spec e n (nn i*2) (x-2) z r); flia.
  - destruct ((p =? i+rb (row e n)) && (d =? i*3+rd (row e n)))%N eqn:E; try discriminate.
    intros H; injection H as Hm; subst m; unbool.
    intros x z r Hx; cbn [form mo mx mz]; apply Head1.
    applys_eq (RInc (nn i) (nn (rb (row e n))) 2 (nn (rd (row e n)))
      (form (ri (row e n)) x (nn (rz (row e n))+z) r)
      (form (ro (row e n)) (x+nn (2+i*2+rx (row e n))%N) z r)); try flia.
    applys_eq (row_spec e n (nn i*2+2) (x-2) z r); flia.
  - destruct ((p =? 1+i+rb (row e n)) && (d =? i*3+rd (row e n)))%N eqn:E; try discriminate.
    intros H; injection H as Hm; subst m; unbool.
    intros x z r Hx; cbn [form mo mx mz].
    applys_eq (Head4 (nn (i+rb (row e n))%N) (nn d)
      (form (ri (row e n)) x (nn (rz (row e n))+z) r)
      (form (ro (row e n)) (x+nn (4+i*2+rx (row e n))%N) z r)); try flia.
    applys_eq (RInc (nn i) (nn (rb (row e n))) 4 (nn (rd (row e n)))
      (form (ri (row e n)) x (nn (rz (row e n))+z) r)
      (form (ro (row e n)) (x+nn (4+i*2+rx (row e n))%N) z r)); try flia.
    applys_eq (row_spec e n (nn i*2+4) (x-2) z r); flia.
Qed.

Definition threshold h p := match h with
  | C0 => p*3+4 | M1 => p*3+3 | M4 => p*3 end%N.
Definition produced h p := match h with C0 => p*2+3 | _ => p*2+5 end%N.
Definition head_ok h p := match h with M4 => (1<=?p)%N | _ => true end.
Lemma produced_ge h p: 2<=nn (produced h p).
Proof. destruct h; cbn [produced]; lia. Qed.
Lemma counter_spec h p z r: head_ok h p=true ->
  P (nn p) (form h (nn p) (nn (threshold h p)+z) r)
    (Col (nn (produced h p)) z r).
Proof.
  destruct h; cbn [head_ok form threshold produced]; intros H.
  - applys_eq (Counter (nn p) z r); flia.
  - applys_eq (Marked1Counter (nn p) z r); flia.
  - apply N.leb_le in H; applys_eq (MarkedCounter (nn (p-1)%N) z r); flia.
Qed.

(* A branch stores the complete middle shape, not just its leading word. *)
Record Branch := BranchMake { bh:Kind; bx:N; bz:N; bk:Kind; bd:N }.
Record Triple := TripleMake { ti:Kind; tp:N; td:N; tj:Kind; tq:N; te:N;
  branches:list Branch }.
Inductive Three T : nat->side->nat->side->Prop :=
| ThreeIntro B a b c r s t v: In B (branches T) ->
  P (nn (tp T)) (form (ti T) (nn (tp T)) (nn (td T)+b) r) s ->
  P (nn (tq T)) (form (tj T) (nn (tq T)) (nn (te T)) s)
    (form (bh B) (nn (bx B)+a) (nn (bz B)+c) t) ->
  P (nn (bx B)+a+nn (bd B)) (form (bk B) (nn (bx B)+a+nn (bd B)) c t) v ->
  Three T b r a v.
Definition TwoN h p k := Two (form h (nn p)) (nn p) (nn k).

Lemma Three_local T B sigma t m1 m2 x a c r s:
  In B (branches T) -> mo m2=bh B -> 2<=x ->
  Local (ti T) (tp T) (td T+sigma)%N t m1 ->
  Local (tj T) (tq T) (te T) (mo m1) m2 ->
  x+nn (mx m1)+nn (mx m2)=nn (bx B)+a ->
  P (nn (bx B)+a+nn (bd B)) (form (bk B) (nn (bx B)+a+nn (bd B)) c r) s ->
  Three T (nn sigma) (form t x (nn (mz m1)+nn (mz m2)+nn (bz B)+c) r) a s.
Proof.
  intros HB Hm Hx L1 L2 Ha H.
  eapply ThreeIntro with (B:=B) (c:=c) (t:=r)
    (s:=form (mo m1) (x+nn (mx m1)) (nn (mz m2)+nn (bz B)+c) r); try eassumption.
  - applys_eq (L1 x (nn (mz m2)+nn (bz B)+c) r Hx); flia.
  - rewrite <-Hm; applys_eq (L2 (x+nn (mx m1)) (nn (bz B)+c) r); flia.
Qed.
Lemma Three_fixed T B m a b c r s:
  In B (branches T) -> mo m=bh B -> head_ok (ti T) (tp T)=true ->
  Local (tj T) (tq T) (te T) C0 m ->
  nn (produced (ti T) (tp T))+nn (mx m)=nn (bx B)+a ->
  nn (td T)+b=nn (threshold (ti T) (tp T))+nn (mz m)+nn (bz B)+c ->
  P (nn (bx B)+a+nn (bd B)) (form (bk B) (nn (bx B)+a+nn (bd B)) c r) s ->
  Three T b r a s.
Proof.
  intros HB Hm Hok L Ha Hd H.
  eapply ThreeIntro with (B:=B) (c:=c) (t:=r)
    (s:=Col (nn (produced (ti T) (tp T))) (nn (mz m)+nn (bz B)+c) r); try eassumption.
  - applys_eq (counter_spec (ti T) (tp T) (nn (mz m)+nn (bz B)+c) r Hok); flia.
  - rewrite <-Hm; applys_eq (L (nn (produced (ti T) (tp T))) (nn (bz B)+c) r
      (produced_ge (ti T) (tp T))); cbn [form]; flia.
Qed.
Lemma Two_local h p k sigma t m x a z r s:
  Local h p sigma t m -> 2<=x -> x+nn (mx m)=nn k+a ->
  P (nn k+a) (form (mo m) (nn k+a) z r) s ->
  TwoN h p k (nn sigma) (form t x (nn (mz m)+z) r) a s.
Proof.
  intros L Hx Ha H; eapply TwoIntro with (s:=form (mo m) (x+nn (mx m)) z r).
  - apply L; assumption.
  - applys_eq H; flia.
Qed.
Lemma Two_fixed h p k a b c r s: head_ok h p=true ->
  nn (produced h p)=nn k+a -> b=nn (threshold h p)+c ->
  P (nn k+a) (Col (nn k+a) c r) s -> TwoN h p k b r a s.
Proof.
  intros Hok Ha Hb H; eapply TwoIntro with (s:=Col (nn (produced h p)) c r).
  - applys_eq (counter_spec h p c r Hok); flia.
  - applys_eq H; flia.
Qed.

Definition Large (R:nat->side->nat->side->Prop) sigma n cut := forall z r,
  R (nn cut+z) r (nn sigma) (Col (nn n) z r).
Lemma Three_large T B m sigma n cut:
  In B (branches T) -> mo m=bh B -> head_ok (ti T) (tp T)=true ->
  Local (tj T) (tq T) (te T) C0 m ->
  (produced (ti T) (tp T)+mx m=bx B+sigma)%N ->
  head_ok (bk B) (bx B+sigma+bd B)%N=true ->
  (n=produced (bk B) (bx B+sigma+bd B))%N ->
  (td T+cut=threshold (ti T) (tp T)+mz m+bz B+threshold (bk B) (bx B+sigma+bd B))%N ->
  Large (Three T) sigma n cut.
Proof.
  intros HB Hm H1 L Ha H2 Hn Hd z r.
  applys_eq (Three_fixed T B m (nn sigma) (nn cut+z)
    (nn (threshold (bk B) (bx B+sigma+bd B))%N+z) r (Col (nn n) z r)); try assumption; try lia.
  applys_eq (counter_spec (bk B) (bx B+sigma+bd B)%N z r H2); flia.
Qed.
Lemma Two_large h p k sigma n cut: head_ok h p=true ->
  (produced h p=k+sigma)%N -> (n=produced C0 (produced h p))%N ->
  (cut=threshold h p+threshold C0 (produced h p))%N -> Large (TwoN h p k) sigma n cut.
Proof.
  intros H1 Ha Hn Hd z r.
  applys_eq (Two_fixed h p k (nn sigma) (nn cut+z)
    (nn (threshold C0 (produced h p))+z) r (Col (nn n) z r)); try assumption; try lia.
  applys_eq (counter_spec C0 (produced h p) z r eq_refl); cbn [form]; flia.
Qed.

(* Residue 2 leaves exactly one recursive call. Its returned zero count is
   not predicted; z is universally quantified. *)
Definition Recursive h p d k n := forall z r s,
  P (nn k+z) r s -> P (nn p) (form h (nn p) (nn d) r) (Col (nn n) z s).
Definition recursive_check h p d i b := (
  match h with
  | C0 => if (p =? i+2+b) && (d =? 3+i*3)
      then Some (b*3+3,b*2+i*2+4) else None
  | M1 => if (p =? i+2+b) && (d =? 2+i*3)
      then Some (b*3+3,b*2+i*2+6) else None
  | M4 => if (p =? i+3+b) && (d =? 2+i*3)
      then Some (b*3+3,b*2+i*2+8) else None
  end)%N.
Lemma recursive_check_spec h p d i b k n:
  recursive_check h p d i b=Some (k,n) -> Recursive h p d k n.
Proof.
  unfold recursive_check; destruct h.
  - destruct ((p =? i+2+b) && (d =? 3+i*3))%N eqn:E; try discriminate.
    intros H; injection H as Hk Hn; subst k n; unbool; intros z r s H; cbn [form].
    applys_eq (Head0 (nn p) (nn d-1) r (Col (nn (b*2+i*2+4)%N) z s)); try flia.
    applys_eq (RInc (nn i) (2+nn b) 0 2 r (Col (nn (b*2+i*2+4)%N) z s)); try flia.
    applys_eq (Call2 (nn b) (nn i*2) z r s); try flia. applys_eq H; flia.
  - destruct ((p =? i+2+b) && (d =? 2+i*3))%N eqn:E; try discriminate.
    intros H; injection H as Hk Hn; subst k n; unbool; intros z r s H.
    apply Head1.
    applys_eq (RInc (nn i) (2+nn b) 2 2 r (Col (nn (b*2+i*2+6)%N) z s)); try flia.
    applys_eq (Call2 (nn b) (nn i*2+2) z r s); try flia. applys_eq H; flia.
  - destruct ((p =? i+3+b) && (d =? 2+i*3))%N eqn:E; try discriminate.
    intros H; injection H as Hk Hn; subst k n; unbool; intros z r s H; cbn [form].
    applys_eq (Head4 (nn p-1) (nn d) r (Col (nn (b*2+i*2+8)%N) z s)); try flia.
    applys_eq (RInc (nn i) (2+nn b) 4 2 r (Col (nn (b*2+i*2+8)%N) z s)); try flia.
    applys_eq (Call2 (nn b) (nn i*2+4) z r s); try flia. applys_eq H; flia.
Qed.

(* These three interfaces are the phases of a four-step layer change. *)
Definition Pass (R:nat->side->nat->side->Prop) sigma h x z out k p := forall a c r s,
  P (nn p+a) (form k (nn p+a) c r) s ->
  R (nn sigma) (form h (nn x+a) (nn z+c) r) (nn out+a) s.
Definition Fixed (R:nat->side->nat->side->Prop) b a h p d := forall r s,
  P (nn p) (form h (nn p) (nn d) r) s -> R (nn b) r (nn a) s.

Lemma Three_pass T B sigma h m1 m2 x z out p:
  In B (branches T) -> mo m2=bh B -> (2<=x)%N ->
  Local (ti T) (tp T) (td T+sigma)%N h m1 ->
  Local (tj T) (tq T) (te T) (mo m1) m2 ->
  (x+mx m1+mx m2=bx B+out)%N -> (z=mz m1+mz m2+bz B)%N ->
  (p=bx B+out+bd B)%N -> Pass (Three T) sigma h x z out (bk B) p.
Proof.
  intros HB Hm Hx L1 L2 Ha Hz Hp a c r s H.
  applys_eq (Three_local T B sigma h m1 m2 (nn x+a) (nn out+a) c r s);
    try assumption; try flia.
  applys_eq H; flia.
Qed.
Lemma Two_pass h p k sigma t m x z out:
  Local h p sigma t m -> (2<=x)%N -> (x+mx m=k+out)%N -> (z=mz m)%N ->
  Pass (TwoN h p k) sigma t x z out (mo m) (x+mx m)%N.
Proof.
  intros L Hx Ha Hz a c r s H.
  applys_eq (Two_local h p k sigma t m (nn x+a) (nn out+a) c r s);
    try assumption; try flia.
  applys_eq H; flia.
Qed.
Lemma Three_fixed_phase T B m b a p d:
  In B (branches T) -> mo m=bh B -> head_ok (ti T) (tp T)=true ->
  Local (tj T) (tq T) (te T) C0 m ->
  (produced (ti T) (tp T)+mx m=bx B+a)%N ->
  (td T+b=threshold (ti T) (tp T)+mz m+bz B+d)%N ->
  (p=bx B+a+bd B)%N -> Fixed (Three T) b a (bk B) p d.
Proof.
  intros HB Hm Hok L Ha Hd Hp r s H.
  applys_eq (Three_fixed T B m (nn a) (nn b) (nn d) r s);
    try assumption; try flia.
  applys_eq H; flia.
Qed.
Lemma Two_fixed_phase h p k b a d:
  head_ok h p=true -> (produced h p=k+a)%N -> (b=threshold h p+d)%N ->
  Fixed (TwoN h p k) b a C0 (produced h p) d.
Proof.
  intros Hok Ha Hd r s H.
  applys_eq (Two_fixed h p k (nn a) (nn b) (nn d) r s);
    try assumption; try flia.
  applys_eq H; cbn [form]; flia.
Qed.

Lemma Grow4 R T sigma n g a1 cut:
  Pass R sigma C0 n (g-td T)%N a1 (ti T) (tp T) -> (td T<=g)%N ->
  Fixed R a1 sigma (tj T) (tq T) (te T) ->
  (forall B, In B (branches T) ->
    Pass R sigma (bh B) (bx B) (bz B) (cut+g)%N (bk B) (bx B+bd B)%N) ->
  Large R sigma n cut ->
  forall b r a s, Three T b r a s ->
    Walk R 4 (nn sigma) (Col (nn n) (nn g+b) r)
      (nn sigma) (Col (nn n) (nn g+a) s).
Proof.
  intros F Hg M K L b r a s H; destruct H as [B a b c r s t v HB H1 H2 H3].
  eapply RMore with (a:=nn a1) (s:=s).
  - applys_eq (F 0%nat (nn (td T)+b) r s); cbn [form]; try flia.
    applys_eq H1; flia.
  - eapply RMore with (a:=nn sigma) (s:=form (bh B) (nn (bx B)+a) (nn (bz B)+c) t).
    + apply M; assumption.
    + eapply RMore with (a:=nn (cut+g)%N+a) (s:=v).
      * apply K; try assumption. applys_eq H3; flia.
      * apply ROne; applys_eq (L (nn g+a) v); flia.
Qed.

Definition Relay (R:nat->side->nat->side->Prop) b a n g k := forall z r s,
  P (nn k+z) r s -> R (nn b) r (nn a) (Col (nn n) (nn g+z) s).
Lemma Three_relay T B m b a p d k0 n g k:
  In B (branches T) -> mo m=bh B -> head_ok (ti T) (tp T)=true ->
  Local (tj T) (tq T) (te T) C0 m ->
  (produced (ti T) (tp T)+mx m=bx B+a)%N ->
  (td T+b=threshold (ti T) (tp T)+mz m+bz B+d)%N ->
  (p=bx B+a+bd B)%N -> Recursive (bk B) p d k0 n -> (k=k0+g)%N ->
  Relay (Three T) b a n g k.
Proof.
  intros HB Hm Hok L Ha Hd Hp F Hk z r s H.
  eapply Three_fixed_phase; try eassumption.
  apply F; applys_eq H; flia.
Qed.
Lemma Two_relay h p k b a d k0 n g k1:
  head_ok h p=true -> (produced h p=k+a)%N -> (b=threshold h p+d)%N ->
  Recursive C0 (produced h p) d k0 n -> (k1=k0+g)%N -> Relay (TwoN h p k) b a n g k1.
Proof.
  intros Hok Ha Hd F Hk z r s H.
  eapply Two_fixed_phase; try eassumption.
  apply F; applys_eq H; flia.
Qed.
Lemma Grow2 R h p k sigma n g a1:
  Pass R sigma C0 n g a1 h p -> Relay R a1 sigma n g k ->
  forall b r a s, TwoN h p k b r a s ->
    Walk R 2 (nn sigma) (Col (nn n) (nn g+b) r)
      (nn sigma) (Col (nn n) (nn g+a) s).
Proof.
  intros F L b r a s H; destruct H as [b a r s t H K].
  eapply RMore with (a:=nn a1) (s:=s).
  - applys_eq (F 0%nat b r s); cbn [form]; try flia. applys_eq H; flia.
  - apply ROne; apply L; assumption.
Qed.

Definition Turn (R:nat->side->nat->side->Prop) rho h p k := forall d r s t,
  P (nn k+d) r s -> P (nn p) (form h (nn p) d s) t -> R (nn rho) r (nn rho) t.
Lemma Three_turn T B m rho k0 n k p:
  In B (branches T) -> mo m=bh B ->
  Recursive (ti T) (tp T) (td T+rho)%N k0 n ->
  Local (tj T) (tq T) (te T) C0 m -> (2<=n)%N ->
  (n+mx m=bx B+rho)%N -> (k=k0+mz m+bz B)%N -> (p=bx B+rho+bd B)%N ->
  Turn (Three T) rho (bk B) p k.
Proof.
  intros HB Hm F L Hn Hx Hk Hp d r s t H K.
  eapply ThreeIntro with (B:=B) (c:=d) (t:=s)
    (s:=Col (nn n) (nn (mz m)+nn (bz B)+d) s); try assumption.
  - applys_eq (F (nn (mz m)+nn (bz B)+d) r s); try flia. applys_eq H; flia.
  - rewrite <-Hm; applys_eq (L (nn n) (nn (bz B)+d) s); cbn [form]; flia.
  - applys_eq K; flia.
Qed.
Lemma Two_turn h p k rho k0 n:
  Recursive h p rho k0 n -> (n=k+rho)%N -> Turn (TwoN h p k) rho C0 n k0.
Proof.
  intros F Hn d r s t H K.
  eapply TwoIntro with (s:=Col (nn n) d s).
  - apply F; assumption.
  - applys_eq K; cbn [form]; flia.
Qed.
Lemma Walk_turn R rho h p k n b r a s: Turn R rho h p k ->
  Walk (TwoN h p k) n b r a s -> forall t, P (nn k+b) t r ->
  exists v, Walk R n (nn rho) t (nn rho) v /\ P (nn k+a) v s.
Proof.
  intros F H; induction H as [b r a s H|n b r a s c t H J IH];
    destruct H as [b a r s t1 H K]; intros v V.
  - exists s; split; [apply ROne; eapply F; eassumption|exact K].
  - destruct (IH s K) as [w [W X]].
    exists w; split; [eapply RMore; [eapply F; eassumption|exact W]|exact X].
Qed.
Lemma Infinite_turn R rho h p k b r s: Turn R rho h p k ->
  P (nn k+b) r s -> Infinite (TwoN h p k) b s -> Infinite R (nn rho) r.
Proof.
  intros F H I n; destruct (I n) as [m [a [t [Hm M]]]].
  destruct (Walk_turn _ _ _ _ _ _ _ _ _ _ F M r H) as [v [V K]].
  exists m,(nn rho),v; auto.
Qed.

Lemma Round_three T B u w:
  In B (branches T) -> ti T=M1 -> tj T=M1 -> bh B=C0 -> bk B=M1 ->
  (tp T=20+u*18)%N -> (td T=15+u*18+w*12)%N ->
  (tq T=5+u*6)%N -> (te T=3+u*6+w*6)%N ->
  (bx B=57+u*48)%N -> (bz B=12+(u-w)*6)%N -> (bd B=5+u*6)%N ->
  forall b r a s, Round (nn u) (nn w) b r a s -> Three T b r a s.
Proof.
  intros HB Hi Hj Hh Hk Hp Hd Hq He Hx Hz Hdelta b r a s H.
  destruct H as [a b c r s t v H1 H2 H3].
  eapply ThreeIntro with (B:=B) (c:=c) (s:=s) (t:=t); try assumption.
  - rewrite Hi; applys_eq H1; cbn [form]; flia.
  - rewrite Hj,Hh; applys_eq H2; cbn [form]; flia.
  - rewrite Hk; applys_eq H3; cbn [form]; flia.
Qed.
Lemma Infinite_mono R S b r:
  (forall b r a s, R b r a s -> S b r a s) -> Infinite R b r -> Infinite S b r.
Proof.
  intros H I; eapply (Infinite_embed R S (fun b r => b) (fun b r => r) 1);
    try exact I; try lia.
  intros; apply ROne; eauto.
Qed.
Lemma StableA_N R u w t b y:
  (forall b r a s, Round (nn u) (nn w) b r a s -> R b r a s) ->
  (4<=u)%N -> (w<=u)%N -> (t<=u)%N ->
  (b=3+t*6)%N -> (y=135+u*108+t*12)%N -> Infinite R (nn b) (Col (nn y) 0 0inf).
Proof.
  intros H Hu Hw Ht Hb Hy; eapply Infinite_mono; [exact H|].
  applys_eq (InfiniteA (nn u) (nn w) (nn t)); unfold TailA; flia.
Qed.
Lemma StableB_N R u w e b y:
  (forall b r a s, Round (nn u) (nn w) b r a s -> R b r a s) ->
  (4<=u)%N -> (w<=u)%N -> (e<=u)%N ->
  (b=90+u*108-e*6)%N -> (y=309+u*324-e*12)%N -> Infinite R (nn b) (Col (nn y) 0 0inf).
Proof.
  intros H Hu Hw He Hb Hy; eapply Infinite_mono; [exact H|].
  applys_eq (InfiniteB (nn u) (nn w) (nn e)); unfold TailB; flia.
Qed.

End Layers7.
End FT7TM7Layers.

(* Shared definitions from FT7TM7Entry.v. *)
Module FT7TM7Entry.
(* Numeric layer states and a checker for one complete layer transition. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat List.
Import FT7TM7Rules FT7TM7Stages FT7TM7Invariant FT7TM7Layers FT7TM7Compute.
Module Entry7.
Import Rules7 Stages7 Invariant7 Layers7 Compute7.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).
Definition formN h x z r := pairs x (match h with
  | C0=>zeros z r | M1=>zeros 1 (pairs 2 (zeros z r))
  | M4=>zeros 4 (pairs 2 (zeros z r)) end).
Lemma formN_spec h x z r: denote (formN h x z r)=form h (nn x) (nn z) (denote r).
Proof. destruct h; unfold formN, form, Col, Mark; tape_simpl; reflexivity. Qed.
Inductive Layer := LTwo (h:Kind) (p k:N) | LThree (T:Triple).
Definition relation L := match L with LTwo h p k=>TwoN h p k | LThree T=>Three T end.
Record State := St { count:N; right:Tape }.
Definition infinite L s := Infinite (relation L) (nn (count s)) (denote (right s)).
Definition state_eqb s t := (count s =? count t)%N && tape_eqb (right s) (right t).
Lemma state_eqb_spec s t: state_eqb s t=true -> s=t.
Proof.
  destruct s,t; unfold state_eqb; cbn [count right].
  intros H; apply and_true_iff in H; destruct H as [Hn Hr].
  apply N.eqb_eq in Hn; apply tape_eqb_spec in Hr; congruence.
Qed.
Inductive Witness := WTwo (m:Tape) | WThree (j:nat) (m:Tape) (c:N) (s:Tape).
Definition check_step fuel L b r a t w := match L,w with
  | LTwo h p k,WTwo m => check_call fuel (formN h p b r) p m &&
      check_call fuel m (k+a)%N t
  | LThree T,WThree j m c s => match nth_error (branches T) j with
    | Some br => check_call fuel (formN (ti T) (tp T) (td T+b)%N r) (tp T) m &&
        check_call fuel (formN (tj T) (tq T) (te T) m) (tq T)
          (formN (bh br) (bx br+a)%N (bz br+c)%N s) &&
        check_call fuel (formN (bk br) (bx br+a+bd br)%N c s) (bx br+a+bd br)%N t
    | None=>false end
  | _,_=>false end.
Lemma check_step_spec fuel L b r a t w:
  check_step fuel L b r a t w=true -> relation L (nn b) (denote r) (nn a) (denote t).
Proof.
  destruct L as [h p k|T],w as [m|j m c s]; cbn [check_step relation]; try discriminate.
  - intros H; apply and_true_iff in H; destruct H as [H1 H2].
    eapply TwoIntro with (s:=denote m).
    + applys_eq (check_call_spec _ _ _ _ H1); repeat rewrite formN_spec; reflexivity.
    + applys_eq (check_call_spec _ _ _ _ H2); flia.
  - destruct (nth_error (branches T) j) as [B|] eqn:E; try discriminate.
    intros H; apply and_true_iff in H; destruct H as [H12 H3].
    apply and_true_iff in H12; destruct H12 as [H1 H2].
    eapply ThreeIntro with (B:=B) (c:=nn c) (s:=denote m) (t:=denote s).
    + eapply nth_error_In; eassumption.
    + applys_eq (check_call_spec _ _ _ _ H1); repeat rewrite formN_spec; flia.
    + applys_eq (check_call_spec _ _ _ _ H2); repeat rewrite formN_spec; flia.
    + applys_eq (check_call_spec _ _ _ _ H3); repeat rewrite formN_spec; flia.
Qed.
Definition lift sigma n g s := St sigma (formN C0 n (g+count s)%N (right s)).
Lemma lift_infinite L child sigma n g m s: 1<=m ->
  (forall b r a t, relation child b r a t ->
    Walk (relation L) m (nn sigma) (Col (nn n) (nn g+b) r)
      (nn sigma) (Col (nn n) (nn g+a) t)) ->
  infinite child s -> infinite L (lift sigma n g s).
Proof.
  intros Hm H I; unfold infinite, lift; cbn [count right]; rewrite formN_spec; cbn [form].
  applys_eq (Infinite_embed (relation child) (relation L)
    (fun b r => nn sigma) (fun b r => Col (nn n) (nn g+b) r) m
    (nn (count s)) (denote (right s)) Hm H I); cbn beta; flia.
Qed.
End Entry7.
End FT7TM7Entry.

(* Shared definitions from FT7TM7Simulator.v. *)
Module FT7TM7Simulator.
(* Data-driven accelerated execution through the finite hierarchy. The
   proposal functions do not belong to the proof: their outputs are checked. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat List.
Import FT7TM7Rules FT7TM7Stages FT7TM7Invariant FT7TM7Layers FT7TM7Compute FT7TM7Entry.
Module Simulator7.
Import Rules7 Stages7 Invariant7 Layers7 Compute7 Entry7.
Local Open Scope N_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.
Local Notation "a || b" := (if a then true else b) : bool_scope.
Local Lemma or_true_iff (a b:bool): (a || b)=true <-> a=true \/ b=true.
Proof. destruct a,b; tauto. Qed.
Fixpoint branch_for h bs := match bs with
  | nil=>None
  | br::bs=>if keqb h (bh br) then Some (0%nat,br) else
      match branch_for h bs with Some (j,b)=>Some (S j,b) | None=>None end end.
Definition middle r := match r with
  | Pairs x (Zeros h (Pairs k r)) =>
      if (k=?2) && ((h=?1)||(h=?4)) then Some (if h=?1 then M1 else M4,x,r)
      else Some (C0,x,Zeros h (Pairs k r))
  | Pairs x r => Some (C0,x,r) | _=>None end.
Definition remaining z r := match r with
  | Blank=>Some (0,Blank)
  | Zeros d r=>if z<=?d then Some (d-z,r) else None
  | _=>None end.
Definition propose fuel L start : option (Witness*State) :=
  let b:=count start in let r:=right start in match L with
  | LTwo h p k => match send (run fuel) (formN h p b r) with
    | Some (_,m) => match send (run fuel) m with
      | Some (u,t) => if k<=?u then Some (WTwo m,St (u-k) t) else None
      | None=>None end | None=>None end
  | LThree T => match send (run fuel) (formN (ti T) (tp T) (td T+b) r) with
    | Some (_,m) => match send (run fuel) (formN (tj T) (tq T) (te T) m) with
      | Some (_,v) => match middle v with
        | Some (h,x,r) => match branch_for h (branches T) with
          | Some (j,br) => if bx br<=?x then match remaining (bz br) r with
            | Some (c,s) => match send (run fuel) (formN (bk br) (x+bd br) c s) with
              | Some (_,t)=>Some (WThree j m c s,St (x-bx br) t) | None=>None end
            | None=>None end else None
          | None=>None end | None=>None end
      | None=>None end | None=>None end end.
Definition step fuel L start := match propose fuel L start with
  | Some (w,s) => if check_step fuel L (count start) (right start) (count s) (right s) w
      then Some s else None | None=>None end.

Inductive Edge := Grow (next:Layer) (sigma n g:N) (m:nat)
  | Rotate (rho:N) (h:Kind) (p k:N).
Definition child e := match e with Grow next _ _ _ _=>next | Rotate _ h p k=>LTwo h p k end.
Definition minimum L := match L with LTwo C0 _ _=>1 | _=>0 end.
Definition propose_cut fuel e start := match e with
  | Grow next sigma n g m => match right start with
      | Pairs _ Blank=>Some (St (minimum next) Blank)
      | Pairs _ (Zeros d s)=>if g<=?d then Some (St (d-g) s) else None
      | _=>None end
  | Rotate rho h p k => match send (run fuel) (right start) with
      | Some (u,r)=>if k<=?u then Some (St (u-k) r) else None
      | None=>None end end.
Definition check_cut fuel e start s := match e with
  | Grow next sigma n g m=>state_eqb start (lift sigma n g s)
  | Rotate rho h p k=>(count start=?rho) && check_call fuel (right start) (k+count s) (right s)
  end.
Definition cut fuel e start := match propose_cut fuel e start with
  | Some s=>if check_cut fuel e start s then Some s else None | None=>None end.
Fixpoint seek budget fuel L e (next:State->bool) start :=
  let accepted := match cut fuel e start with Some s=>next s | None=>false end in
  if accepted then true else match budget with
  | O=>false | S budget=>match step fuel L start with
    | Some s=>seek budget fuel L e next s | None=>false end end.
Fixpoint simulate (terminal:State->bool) fuel budget L edges start := match edges with
  | nil=>terminal start
  | e::edges=>seek budget fuel L e (simulate terminal fuel budget (child e) edges) start end.

Local Close Scope N_scope.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).
Definition edge_valid L e := match e with
  | Grow next sigma n g m=> 1<=m /\
      forall b r a s, relation next b r a s ->
      Walk (relation L) m (nn sigma) (Col (nn n) (nn g+b) r)
        (nn sigma) (Col (nn n) (nn g+a) s)
  | Rotate rho h p k=>Turn (relation L) rho h p k end.
Fixpoint valid_program (terminal:State->bool) L edges := match edges with
  | nil=>forall s, terminal s=true -> infinite L s
  | e::edges=>edge_valid L e /\ valid_program terminal (child e) edges end.
Lemma step_spec fuel L start s: step fuel L start=Some s ->
  relation L (nn (count start)) (denote (right start)) (nn (count s)) (denote (right s)).
Proof.
  unfold step; destruct (propose fuel L start) as [[w t]|]; try discriminate.
  destruct (check_step fuel L (count start) (right start) (count t) (right t) w) eqn:E; try discriminate.
  intros H; injection H as Hs; subst; eapply check_step_spec; exact E.
Qed.
Lemma cut_spec fuel L e start s: edge_valid L e -> cut fuel e start=Some s ->
  infinite (child e) s -> infinite L start.
Proof.
  intros V; unfold cut; destruct (propose_cut fuel e start) as [t|]; try discriminate.
  destruct (check_cut fuel e start t) eqn:E; try discriminate.
  intros H I; injection H as Hs; subst t.
  destruct e as [next sigma n g m|rho h p k]; cbn [check_cut] in E.
  - apply state_eqb_spec in E; subst start; destruct V as [Hm H].
    eapply lift_infinite; eassumption.
  - apply and_true_iff in E; destruct E as [Hb HP]; apply N.eqb_eq in Hb.
    unfold infinite; rewrite Hb; eapply Infinite_turn; [exact V| |exact I].
    applys_eq (check_call_spec _ _ _ _ HP); flia.
Qed.
Lemma seek_spec budget fuel L e next start: edge_valid L e ->
  (forall s, next s=true -> infinite (child e) s) ->
  seek budget fuel L e next start=true -> infinite L start.
Proof.
  intros V Hnext; revert start; induction budget as [|budget IH]; intros start; cbn [seek];
    destruct (cut fuel e start) as [s|] eqn:E.
  - destruct (next s) eqn:H; [intros _; eapply cut_spec; eauto|discriminate].
  - discriminate.
  - destruct (next s) eqn:H.
    + intros _; eapply cut_spec; eauto.
    + destruct (step fuel L start) as [t|] eqn:K; try discriminate; intros I.
      eapply Infinite_back; [apply ROne; eapply step_spec; exact K|apply IH; exact I].
  - destruct (step fuel L start) as [t|] eqn:K; try discriminate; intros I.
    eapply Infinite_back; [apply ROne; eapply step_spec; exact K|apply IH; exact I].
Qed.
Theorem simulate_spec terminal fuel budget L edges start:
  valid_program terminal L edges -> simulate terminal fuel budget L edges start=true -> infinite L start.
Proof.
  revert L start; induction edges as [|e edges IH]; intros L start V; cbn [simulate].
  - apply V.
  - destruct V as [H V]; apply seek_spec; [exact H|intros; eapply IH; eassumption].
Qed.

(* The final layer is checked by inequalities, not by a list of five points. *)
Definition terminal u w s := match right s with
  | Pairs y Blank => let b:=count s in
    (4<=?u)%N && (w<=?u)%N &&
    (let t:=(b-3)/6 in (t<=?u) && (b=?3+t*6) && (y=?135+u*108+t*12))%N ||
    ((4<=?u)%N && (w<=?u)%N &&
    (let e:=(90+u*108-b)/6 in (e<=?u) && (b+e*6=?90+u*108) && (y+e*12=?309+u*324))%N)
  | _=>false end.
Lemma terminal_spec L u w:
  (forall b r a s, Round (nn u) (nn w) b r a s -> relation L b r a s) ->
  forall s, terminal u w s=true -> infinite L s.
Proof.
  intros H [b r]; destruct r as [|z r|y r|r]; cbn [terminal right count]; try discriminate.
  destruct r; try discriminate; intros K; apply or_true_iff in K; destruct K as [K|K]; unbool.
  - unfold infinite; cbn [count right denote]; applys_eq (StableA_N (relation L) u w ((b-3)/6)%N b y H);
      try lia; unfold Col; reflexivity.
  - unfold infinite; cbn [count right denote]; applys_eq (StableB_N (relation L) u w ((90+u*108-b)/6)%N b y H);
      try lia; unfold Col; reflexivity.
Qed.
End Simulator7.
End FT7TM7Simulator.

(* Shared definitions from FT7TM7Interfaces.v. *)
Module FT7TM7Interfaces.
(* Arithmetic interface checking for the hierarchy simulator. No trace or
   layer-specific proof is stored here. Every accepted interface is universal
   in its suffix, including all middle branches of a three-call layer. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat List.
Import FT7TM7Rules FT7TM7Stages FT7TM7Invariant FT7TM7Layers FT7TM7Compute FT7TM7Entry FT7TM7Simulator.
Module Interfaces7.
Import Rules7 Stages7 Invariant7 Layers7 Compute7 Entry7 Simulator7.
Local Open Scope N_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.
Definition choose b d t := match d,t with
  | 0,C0=>Some (ZC,b)
  | 0,M1=>Some (if N.even b then Z1E else Z1O,b/2)
  | 0,M4=>if b=?0 then Some (Z4Empty,0) else
      Some (if N.even (b-1) then Z4E else Z4O,(b-1)/2)
  | 1,C0=>Some (if N.even b then DCE else DCO,(b-2)/2)
  | 1,M1=>Some (if N.even b then D1E else D1O,(b-4)/2)
  | 1,M4=>Some (if N.even b then D4E else D4O,(b-4)/2)
  | _,_=>None end.
Definition head h p d := match h with
  | C0=>(p,d-1) | M1=>(p,d) | M4=>(p-1,d) end.
Definition loc h p d t :=
  let '(b,z):=head h p d in let i:=N.min b (z/3) in
  match choose (b-i) (z-i*3) t with
  | Some (e,n)=>local_check h p d t i e n | None=>None end.
Definition rec h p d :=
  let '(b,z):=head h p d in let i:=N.min b (z/3) in
  recursive_check h p d i (b-i-2).
Fixpoint pick h bs := match bs with
  | nil=>None | br::bs=>if keqb h (bh br) then Some br else pick h bs end.

Lemma loc_spec h p d t m: loc h p d t=Some m -> Local h p d t m.
Proof.
  unfold loc; destruct (head h p d) as [b z];
    destruct (choose (b-N.min b (z/3)) (z-N.min b (z/3)*3) t) as [[e n]|];
    try discriminate; apply local_check_spec.
Qed.
Lemma rec_spec h p d k n: rec h p d=Some (k,n) -> Recursive h p d k n.
Proof. unfold rec; destruct (head h p d); apply recursive_check_spec. Qed.
Lemma pick_spec h bs br: pick h bs=Some br -> In br bs /\ h=bh br.
Proof.
  induction bs as [|b bs IH]; cbn [pick]; try discriminate.
  destruct (keqb h (bh b)) eqn:E.
  - intros H; injection H as H; subst; apply keqb_spec in E; split; [left; reflexivity|exact E].
  - intros H; destruct (IH H); split; [right; assumption|assumption].
Qed.
Ltac decode := unbool; repeat match goal with
  | H:keqb _ _=true |- _=>apply keqb_spec in H end.

Definition pass L sigma h x z out k p := match L with
  | LTwo hi pi ki=>match loc hi pi sigma h with
    | Some m=>(2<=?x) && (x+mx m=?ki+out) && (z=?mz m) &&
        keqb k (mo m) && (p=?x+mx m)
    | None=>false end
  | LThree T=>match loc (ti T) (tp T) (td T+sigma) h with
    | Some m1=>match loc (tj T) (tq T) (te T) (mo m1) with
      | Some m2=>match pick (mo m2) (branches T) with
        | Some br=>(2<=?x) && (x+mx m1+mx m2=?bx br+out) &&
            (z=?mz m1+mz m2+bz br) && keqb k (bk br) && (p=?bx br+out+bd br)
        | None=>false end | None=>false end | None=>false end end.
Lemma pass_spec L sigma h x z out k p:
  pass L sigma h x z out k p=true -> Pass (relation L) sigma h x z out k p.
Proof.
  destruct L as [hi pi ki|T]; cbn [pass relation].
  - destruct (loc hi pi sigma h) as [m|] eqn:E; try discriminate.
    intros H; decode; apply loc_spec in E.
    applys_eq (Two_pass hi pi ki sigma h m x z out); eauto; congruence.
  - destruct (loc (ti T) (tp T) (td T+sigma) h) as [m1|] eqn:E1; try discriminate.
    destruct (loc (tj T) (tq T) (te T) (mo m1)) as [m2|] eqn:E2; try discriminate.
    destruct (pick (mo m2) (branches T)) as [br|] eqn:B; try discriminate.
    intros H; decode; apply loc_spec in E1; apply loc_spec in E2; apply pick_spec in B; destruct B.
    applys_eq (Three_pass T br sigma h m1 m2 x z out p); eauto; congruence.
Qed.

Definition fixed L b a h p d := match L with
  | LTwo hi pi ki=>head_ok hi pi && (produced hi pi=?ki+a) &&
      (b=?threshold hi pi+d) && keqb h C0 && (p=?produced hi pi)
  | LThree T=>match loc (tj T) (tq T) (te T) C0 with
    | Some m=>match pick (mo m) (branches T) with
      | Some br=>head_ok (ti T) (tp T) && (produced (ti T) (tp T)+mx m=?bx br+a) &&
          (td T+b=?threshold (ti T) (tp T)+mz m+bz br+d) &&
          keqb h (bk br) && (p=?bx br+a+bd br)
      | None=>false end | None=>false end end.
Lemma fixed_spec L b a h p d: fixed L b a h p d=true -> Fixed (relation L) b a h p d.
Proof.
  destruct L as [hi pi ki|T]; cbn [fixed relation].
  - intros H; decode; applys_eq (Two_fixed_phase hi pi ki b a d); eauto; congruence.
  - destruct (loc (tj T) (tq T) (te T) C0) as [m|] eqn:E; try discriminate.
    destruct (pick (mo m) (branches T)) as [br|] eqn:B; try discriminate.
    intros H; decode; apply loc_spec in E; apply pick_spec in B; destruct B.
    applys_eq (Three_fixed_phase T br m b a p d); eauto; congruence.
Qed.

Definition large L sigma n cut := match L with
  | LTwo h p k=>head_ok h p && (produced h p=?k+sigma) &&
      (n=?produced C0 (produced h p)) && (cut=?threshold h p+threshold C0 (produced h p))
  | LThree T=>match loc (tj T) (tq T) (te T) C0 with
    | Some m=>match pick (mo m) (branches T) with
      | Some br=>head_ok (ti T) (tp T) && (produced (ti T) (tp T)+mx m=?bx br+sigma) &&
          head_ok (bk br) (bx br+sigma+bd br) && (n=?produced (bk br) (bx br+sigma+bd br)) &&
          (td T+cut=?threshold (ti T) (tp T)+mz m+bz br+threshold (bk br) (bx br+sigma+bd br))
      | None=>false end | None=>false end end.
Lemma large_spec L sigma n cut: large L sigma n cut=true -> Large (relation L) sigma n cut.
Proof.
  destruct L as [h p k|T]; cbn [large relation].
  - intros H; decode; apply Two_large; assumption.
  - destruct (loc (tj T) (tq T) (te T) C0) as [m|] eqn:E; try discriminate.
    destruct (pick (mo m) (branches T)) as [br|] eqn:B; try discriminate.
    intros H; decode; apply loc_spec in E; apply pick_spec in B; destruct B.
    eapply Three_large; eassumption.
Qed.

Definition relay L b a n g k := match L with
  | LTwo h p ki=>let d:=b-threshold h p in
      match rec C0 (produced h p) d with
      | Some (k0,n0)=>head_ok h p && (produced h p=?ki+a) && (b=?threshold h p+d) &&
          (n=?n0) && (k=?k0+g) | None=>false end
  | LThree T=>match loc (tj T) (tq T) (te T) C0 with
    | Some m=>match pick (mo m) (branches T) with
      | Some br=>let d:=td T+b-(threshold (ti T) (tp T)+mz m+bz br) in
          match rec (bk br) (bx br+a+bd br) d with
          | Some (k0,n0)=>head_ok (ti T) (tp T) && (produced (ti T) (tp T)+mx m=?bx br+a) &&
              (td T+b=?threshold (ti T) (tp T)+mz m+bz br+d) && (n=?n0) && (k=?k0+g)
          | None=>false end | None=>false end | None=>false end end.
Lemma relay_spec L b a n g k: relay L b a n g k=true -> Relay (relation L) b a n g k.
Proof.
  destruct L as [h p ki|T]; cbn [relay relation].
  - destruct (rec C0 (produced h p) (b-threshold h p)) as [[k0 n0]|] eqn:E; try discriminate.
    intros H; decode; subst n0; apply rec_spec in E.
    eapply Two_relay; eassumption.
  - destruct (loc (tj T) (tq T) (te T) C0) as [m|] eqn:E; try discriminate.
    destruct (pick (mo m) (branches T)) as [br|] eqn:B; try discriminate.
    destruct (rec (bk br) (bx br+a+bd br) (td T+b-(threshold (ti T) (tp T)+mz m+bz br)))
      as [[k0 n0]|] eqn:K; try discriminate.
    intros H; decode; subst n0; apply loc_spec in E; apply pick_spec in B; destruct B; apply rec_spec in K.
    eapply Three_relay; eauto.
Qed.

Definition turn L rho h p k := match L with
  | LTwo hi pi ki=>match rec hi pi rho with
    | Some (k0,n)=>keqb h C0 && (p=?n) && (k=?k0) && (n=?ki+rho) | None=>false end
  | LThree T=>match rec (ti T) (tp T) (td T+rho) with
    | Some (k0,n)=>match loc (tj T) (tq T) (te T) C0 with
      | Some m=>match pick (mo m) (branches T) with
        | Some br=>(2<=?n) && (n+mx m=?bx br+rho) && (k=?k0+mz m+bz br) &&
            (p=?bx br+rho+bd br) && keqb h (bk br)
        | None=>false end | None=>false end | None=>false end end.
Lemma turn_spec L rho h p k: turn L rho h p k=true -> Turn (relation L) rho h p k.
Proof.
  destruct L as [hi pi ki|T]; cbn [turn relation].
  - destruct (rec hi pi rho) as [[k0 n]|] eqn:E; try discriminate.
    intros H; decode; subst h p k; apply rec_spec in E; apply Two_turn; assumption.
  - destruct (rec (ti T) (tp T) (td T+rho)) as [[k0 n]|] eqn:K; try discriminate.
    destruct (loc (tj T) (tq T) (te T) C0) as [m|] eqn:E; try discriminate.
    destruct (pick (mo m) (branches T)) as [br|] eqn:B; try discriminate.
    intros H; decode; subst h; apply loc_spec in E; apply rec_spec in K; apply pick_spec in B; destruct B.
    eapply Three_turn; eassumption.
Qed.
(* Guesses are deliberately separate from the guards above: no arithmetic
   fact about a guess is trusted without the corresponding checked equation. *)
Definition first_guess L sigma x := match L with
  | LTwo h p k=>match loc h p sigma C0 with Some m=>x+mx m-k | None=>0 end
  | LThree T=>match loc (ti T) (tp T) (td T+sigma) C0 with
    | Some m1=>match loc (tj T) (tq T) (te T) (mo m1) with
      | Some m2=>match pick (mo m2) (branches T) with
        | Some br=>x+mx m1+mx m2-bx br | None=>0 end
      | None=>0 end | None=>0 end end.
Definition large_guess L := match L with
  | LTwo h p k=>let t:=produced h p in (t-k,produced C0 t,threshold h p+threshold C0 t)
  | LThree T=>match loc (tj T) (tq T) (te T) C0 with
    | Some m=>match pick (mo m) (branches T) with
      | Some br=>let s:=produced (ti T) (tp T)+mx m-bx br in
          let p:=bx br+s+bd br in
          (s,produced (bk br) p,threshold (ti T) (tp T)+mz m+bz br+threshold (bk br) p-td T)
      | None=>(0,0,0) end | None=>(0,0,0) end end.
Definition edge_check L e := match e with
  | Grow next sigma n g m=>let a1:=first_guess L sigma n in
      match m,next with
      | 4%nat,LThree T=>let '(_,_,cut):=large_guess L in
          pass L sigma C0 n (g-td T) a1 (ti T) (tp T) && (td T<=?g) &&
          fixed L a1 sigma (tj T) (tq T) (te T) &&
          forallb (fun br=>pass L sigma (bh br) (bx br) (bz br) (cut+g) (bk br) (bx br+bd br))
            (branches T) && large L sigma n cut
      | 2%nat,LTwo h p k=>pass L sigma C0 n g a1 h p && relay L a1 sigma n g k
      | _,_=>false end
  | Rotate rho h p k=>turn L rho h p k end.
Lemma edge_check_spec L e: edge_check L e=true -> edge_valid L e.
Proof.
  destruct e as [next sigma n g m|rho h p k]; cbn [edge_check edge_valid].
  - destruct m as [|[|[|[|[|m]]]]]; try discriminate;
      destruct next as [h p k|T]; try discriminate.
    + intros H; decode; split; [lia|].
      apply Grow2 with (a1:=first_guess L sigma n); [apply pass_spec|apply relay_spec]; assumption.
    + destruct (large_guess L) as [[sigma0 n0] cut]; intros H; decode; split; [lia|].
      apply Grow4 with (a1:=first_guess L sigma n) (cut:=cut).
      * apply pass_spec; assumption.
      * assumption.
      * apply fixed_spec; assumption.
      * intros br HB; apply pass_spec; rewrite forallb_forall in *; eauto.
      * apply large_spec; assumption.
  - apply turn_spec.
Qed.

Definition stable L u w := match L with
  | LTwo _ _ _=>false
  | LThree T=>match pick C0 (branches T) with
    | Some br=>keqb (ti T) M1 && keqb (tj T) M1 && keqb (bk br) M1 &&
        (tp T=?20+u*18) && (td T=?15+u*18+w*12) &&
        (tq T=?5+u*6) && (te T=?3+u*6+w*6) &&
        (bx br=?57+u*48) && (bz br=?12+(u-w)*6) && (bd br=?5+u*6)
    | None=>false end end.
Lemma stable_spec L u w: stable L u w=true ->
  forall b r a s, Round (N.to_nat u) (N.to_nat w) b r a s -> relation L b r a s.
Proof.
  destruct L as [h p k|T]; cbn [stable relation]; try discriminate.
  destruct (pick C0 (branches T)) as [br|] eqn:B; try discriminate.
  intros H; decode; apply pick_spec in B; destruct B.
  eapply Round_three; eauto.
Qed.
Fixpoint program_check u w L edges := match edges with
  | nil=>stable L u w
  | e::edges=>edge_check L e && program_check u w (child e) edges end.
Theorem program_check_spec u w L edges:
  program_check u w L edges=true -> valid_program (terminal u w) L edges.
Proof.
  revert L; induction edges as [|e edges IH]; intros L; cbn [program_check valid_program].
  - intros H; apply terminal_spec; apply stable_spec; assumption.
  - intros H; apply and_true_iff in H; destruct H; split; [apply edge_check_spec|apply IH]; assumption.
Qed.
End Interfaces7.
End FT7TM7Interfaces.

(* Shared definitions from FT7TM7LayerCertificate.v. *)
Module FT7TM7LayerCertificate.
(* Generated data; all interfaces are checked by Interfaces7. *)
Import BusyCoq.Individual62.
Import NArith List.
Import FT7TM7Layers FT7TM7Entry FT7TM7Simulator FT7TM7Interfaces.
Import Layers7 Entry7 Simulator7 Interfaces7 ListNotations.
Module LayerCertificate7.
Definition L0 := LTwo M4 497 461.
Definition T1 := TripleMake M1 2839 2577 C0 999 887 [BranchMake M4 7326 632 M1 840; BranchMake C0 7328 636 M1 838; BranchMake M1 7326 635 M1 840].
Definition L1 := LThree T1.
Definition T2 := TripleMake M1 24512 21209 M1 8169 8359 [BranchMake M1 62675 6003 M1 7181; BranchMake C0 61687 7984 M1 8169; BranchMake M4 62675 6000 M1 7181].
Definition L2 := LThree T2.
Definition L3 := LTwo M1 69856 69097.
Definition T4 := TripleMake C0 419154 351082 C0 139717 140486 [BranchMake M1 1071298 92636 M4 116558; BranchMake C0 1048139 138951 C0 139717; BranchMake M4 1071297 92632 M1 116559].
Definition L4 := LThree T4.
Definition T5 := TripleMake M4 3563582 3023212 M4 1187859 1190926 [BranchMake M1 9107445 882668 M4 1036797; BranchMake C0 8956383 1184797 M4 1187859; BranchMake M4 9107444 882667 M4 1036798].
Definition L5 := LThree T5.
Definition T6 := TripleMake M4 29154818 25587031 M4 10144245 8878606 [BranchMake M1 75005776 7576122 M4 8866325; BranchMake C0 75005778 7576123 M4 8866323; BranchMake M4 75005776 7576119 M4 8866325].
Definition L6 := LThree T6.
Definition L7 := LTwo M4 241303410 241205118.
Definition L8 := LTwo C0 482606822 482508522.
Definition T9 := TripleMake C0 2895640944 2413263491 C0 965213647 965311952 [BranchMake M1 7399987684 643410232 M4 804361089; BranchMake C0 7239135126 965115345 C0 965213647; BranchMake M4 7399987683 643410228 M1 804361090].
Definition L9 := LThree T9.
Definition T10 := TripleMake M4 23567436442 20659237160 M4 8204348776 7159132096 [BranchMake M4 60634584735 6112735784 M4 7158738887; BranchMake C0 60634584737 6112735788 M4 7158738885; BranchMake M1 60634584735 6112735787 M4 7158738887].
Definition L10 := LThree T10.
Definition L11 := LTwo M4 67793323622 67791750770.
Definition L12 := LTwo M1 384162429347 384159283628.
Definition L13 := LTwo M1 2176920957266 2176914665819.
Definition T14 := TripleMake M1 12335886473098 10763679587982 C0 4353841914537 3628208935478 [BranchMake M1 31807237307250 2902557082055 M1 3628202644023; BranchMake C0 31807237307252 2902557082056 M1 3628202644021; BranchMake M4 31807237307250 2902557082052 M1 3628202644023].
Definition L14 := LThree T14.
Definition T15 := TripleMake M1 106306319853833 90120564424135 M1 35435439951276 35435465117098 [BranchMake M1 271671710487434 26687421508354 M1 31061443312726; BranchMake C0 267297713848884 35435414785459 M1 35435439951276; BranchMake M4 271671710487434 26687421508351 M1 31061443312726].
Definition L15 := LThree T15.
Definition T16 := TripleMake M1 870066395544266 762800051405309 M1 302733153800163 264600188607229 [BranchMake M1 2238332553223319 226466921424417 M1 264600087943937; BranchMake C0 2238332553223321 226466921424418 M1 264600087943935; BranchMake M4 2238332553223319 226466921424414 M1 264600087943937].
Definition L16 := LThree T16.
Definition L17 := LTwo M1 2502932641167256 2502932238514081.
Definition T18 := TripleMake C0 15017595847003554 12514664145360386 C0 5005865282334517 5005865684987702 [BranchMake M1 38378300565006834 3337243253120892 M4 4171554469054294; BranchMake C0 37543989751726611 5005864879681335 C0 5005865282334517; BranchMake M4 38378300565006833 3337243253120888 M1 4171554469054295].
Definition L18 := LThree T18.
Definition L19 := LTwo M4 122226544536241682 122226541315016222.
Definition T20 := TripleMake M1 692617086242240458 604342366701532910 C0 244453089072483369 203710911318499190 [BranchMake M1 1785865624646289170 162968723900838599 M1 203710908097273719; BranchMake C0 1785865624646289172 162968723900838600 M1 203710908097273717; BranchMake M4 1785865624646289170 162968723900838596 M1 203710908097273719].
Definition L20 := LThree T20.
Definition L21 := LTwo M1 1989576532743562889 1989576519858661010.
Definition L22 := LTwo M1 11274267021027673364 11274266995257869597.
Definition T23 := TripleMake M1 63887513123451783040 55744986998148866111 C0 22548534042055346733 18790445065110893348 [BranchMake M1 164729568154171735073 15032356010857028639 M1 18790445039341089573; BranchMake C0 164729568154171735075 15032356010857028640 M1 18790445039341089571; BranchMake M4 164729568154171735073 15032356010857028636 M1 18790445039341089573].
Definition L23 := LThree T23.
Definition L24 := LTwo M1 183520013193512824646 183520013090433609551.
Definition T25 := TripleMake M1 1039946741447085875526 1039946741653244305729 C0 367040026387025649297 305866688776113792034 [BranchMake C0 2813973535668223049651 244693350855964289464 M1 305866688673034576929; BranchMake M1 2813973535668223049649 244693350855964289463 M1 305866688673034576931; BranchMake M4 2813973535668223049649 244693350855964289460 M1 305866688673034576931].
Definition L25 := LThree T25.
Definition T26 := TripleMake M1 8880329527511610133635 7760517596039183664649 M1 3119840224341257626583 2640649079241411740878 [BranchMake M4 22880527571408675330628 2161457932904615273932 M1 2640649078829094880466; BranchMake C0 22880527571408675330630 2161457932904615273936 M1 2640649078829094880464; BranchMake M1 22880527571408675330628 2161457932904615273935 M1 2640649078829094880466].
Definition L26 := LThree T26.
Definition T27 := TripleMake M1 73416784786297369510586 73416784789595904393909 M1 25521176650237770211097 22374431487471096530049 [BranchMake C0 197875922873070279443373 19227686319756620524020 M1 22374431485821829088387; BranchMake M1 197875922873070279443371 19227686319756620524019 M1 22374431485821829088389; BranchMake M4 197875922873070279443371 19227686319756620524016 M1 22374431485821829088389].
Definition L27 := LThree T27.
Definition T28 := TripleMake M1 660751063076676325595294 660751063089870465128601 M1 220250354358892108531763 220250354365489178298417 [BranchMake C0 1762002834871136868254121 220250354352295038765114 M1 220250354358892108531763; BranchMake M1 1795506612876559937960968 153242798341448899351415 M1 186746576353469038824916; BranchMake M4 1795506612876559937960968 153242798341448899351412 M1 186746576353469038824916].
Definition L28 := LThree T28.
Definition T29 := TripleMake M1 5946759567690086930357666 5946759567742863488490909 M1 1982253189230028976785887 1982253189256417255852509 [BranchMake C0 15858025513840231814287113 1982253189203640697719270 M1 1982253189230028976785887; BranchMake M1 16185196430987545827152986 1327911354909012671987519 M1 1655082272082714963920014; BranchMake M4 16185196430987545827152986 1327911354909012671987516 M1 1655082272082714963920014].
Definition L29 := LThree T29.
Definition T30 := TripleMake M1 53520836109210782373219014 53520836109421888605752001 M1 17840278703070260791073003 17840278703175813907339497 [BranchMake C0 142722229624562086328584041 17840278702964707674806514 M1 17840278703070260791073003; BranchMake M1 145692404794002911504297788 11899928364083057323379015 M1 14870103533629435615359256; BranchMake M4 145692404794002911504297788 11899928364083057323379012 M1 14870103533629435615359256].
Definition L30 := LThree T30.
Definition T31 := TripleMake M1 481687524982897041358971146 481687524983741466289103109 M1 160562508327632347119657047 160562508328054559584723029 [BranchMake C0 1284500066621058776957256393 160562508327210134654591070 M1 160562508327632347119657047; BranchMake M1 1311257280061207173296267566 107048081446913341976568719 M1 133805294887483950780645874; BranchMake M4 1311257280061207173296267566 107048081446913341976568716 M1 133805294887483950780645874].
Definition L31 := LThree T31.
Definition T32 := TripleMake M1 4335187724846073372230740334 4335187724849451071951268201 M1 1445062574948691124076913443 1445062574950379973937177377 [BranchMake C0 11560500599589528992615307561 1445062574947002274216649514 M1 1445062574948691124076913443; BranchMake M1 11801341157466309412214661808 963381459193441435017941015 M1 1204222017071910704477559196; BranchMake M4 11801341157466309412214661808 963381459193441435017941012 M1 1204222017071910704477559196].
Definition L32 := LThree T32.
Definition program : list Edge := [
  Grow L1 538 2001 3213 4;
  Grow L2 3 16343 29193 4;
  Rotate 0 M1 69856 69097;
  Grow L4 70620 279437 490033 4;
  Grow L5 3 2375723 4208009 4;
  Grow L6 3 20288495 33163154 4;
  Grow L7 3 167744210 63197154 2;
  Rotate 241401704 C0 482606822 482508522;
  Grow L9 482705125 1930427297 3378378836 4;
  Grow L10 3 16408697557 26771972948 4;
  Rotate 0 M4 67793323622 67791750770;
  Grow L12 67794896479 271173294498 90390049592 2;
  Grow L13 384165575071 1536649717398 512214475316 2;
  Grow L14 2176927248718 8707683829077 13666236670038 4;
  Grow L15 3 70870879902557 125555979209594 4;
  Grow L16 3 605466307600331 989266972829727 4;
  Rotate 0 M1 2502932641167256 2502932238514081;
  Grow L18 2502933043820436 10011730564669037 17520529025041721 4;
  Grow L19 3 85099710068122264 31703812291564979 2;
  Grow L20 122226547757467147 488906178144966741 767311090602371510 4;
  Rotate 0 M1 1989576532743562889 1989576519858661010;
  Grow L22 1989576545628464773 7958306130974251566 2652768701734815932 2;
  Grow L23 11274267046797477136 45097068084110693469 70777343009005894751 4;
  Rotate 0 M1 183520013193512824646 183520013090433609551;
  Grow L25 183520013296592039746 734080052774051298597 1284640092509208595193 4;
  Grow L26 3 6239680448682515253171 9921975528943798938585 4;
  Grow L27 3 51042353300475540422199 92644471109352524917929 4;
  Grow L28 3 440500708717784217063531 881001417442165503893715 4;
  Grow L29 3 3964506378460057953571779 7929012756946504186210179 4;
  Grow L30 3 35680557406140521582146011 71361114812386596280558515 4;
  Grow L31 3 321125016655264694239314099 642250033310951600943694179 4;
  Grow L32 3 2890125149897382248153826891 5780250299796453346167917715 4].
Definition stop := terminal 240843762491448520679485573 281474976710656.
Lemma program_valid: valid_program stop L0 program.
Proof. apply program_check_spec; vm_compute; reflexivity. Qed.
End LayerCertificate7.
End FT7TM7LayerCertificate.

(* Shared definitions from FT7TM7EntryCertificate.v. *)
Module FT7TM7EntryCertificate.
(* Generated program data; Simulator7 checks the actual execution. *)
Import BusyCoq.Individual62.
Import NArith List Lia.
Import FT7TM7Rules FT7TM7Stages FT7TM7Invariant FT7TM7Layers FT7TM7LayerCertificate FT7TM7Compute FT7TM7Entry FT7TM7Simulator.
Import Rules7 Stages7 Invariant7 Layers7 LayerCertificate7 Compute7 Entry7 Simulator7 ListNotations.
Module EntryCertificate7.
Local Opaque N.to_nat.
(* TM3: Eight seed n=65, new-left visit=805. *)
Definition seed3 := St 538 (Pairs 32018 (Zeros 4 (Pairs 2 Blank))).
Lemma seed3_infinite: infinite L0 seed3.
Proof. apply (simulate_spec stop 256 16 L0 program); [exact program_valid|vm_compute; reflexivity]. Qed.
Theorem seed3_nonhalt: ~halts tm (0inf <{{A}} G 65 (N.to_nat (count seed3)) (denote (right seed3))).
Proof. apply Eight_nonhalt; exact seed3_infinite. Qed.
(* TM4: Eight seed n=69, new-left visit=843. *)
Definition seed4 := St 25656 (Pairs 52239 Blank).
Lemma seed4_infinite: infinite L0 seed4.
Proof. apply (simulate_spec stop 256 16 L0 program); [exact program_valid|vm_compute; reflexivity]. Qed.
Theorem seed4_nonhalt: ~halts tm (0inf <{{A}} G 69 (N.to_nat (count seed4)) (denote (right seed4))).
Proof. apply Eight_nonhalt; exact seed4_infinite. Qed.
(* TM5: Eight seed n=65, new-left visit=807. *)
Definition seed5 := St 538 (Pairs 2001 (Zeros 14060 (Pairs 38031 Blank))).
Lemma seed5_infinite: infinite L0 seed5.
Proof. apply (simulate_spec stop 256 16 L0 program); [exact program_valid|vm_compute; reflexivity]. Qed.
Theorem seed5_nonhalt: ~halts tm (0inf <{{A}} G 65 (N.to_nat (count seed5)) (denote (right seed5))).
Proof. apply Eight_nonhalt; exact seed5_infinite. Qed.
(* TM6: Eight seed n=66, new-left visit=809. *)
Definition seed6 := St 538 (Pairs 2001 (Zeros 14060 (Pairs 38031 Blank))).
Lemma seed6_infinite: infinite L0 seed6.
Proof. apply (simulate_spec stop 256 16 L0 program); [exact program_valid|vm_compute; reflexivity]. Qed.
Theorem seed6_nonhalt: ~halts tm (0inf <{{A}} G 66 (N.to_nat (count seed6)) (denote (right seed6))).
Proof. apply Eight_nonhalt; exact seed6_infinite. Qed.
(* TM7: Eight seed n=68, new-left visit=836. *)
Definition seed7 := St 25864 (Pairs 52655 Blank).
Lemma seed7_infinite: infinite L0 seed7.
Proof. apply (simulate_spec stop 256 16 L0 program); [exact program_valid|vm_compute; reflexivity]. Qed.
Theorem seed7_nonhalt: ~halts tm (0inf <{{A}} G 68 (N.to_nat (count seed7)) (denote (right seed7))).
Proof. apply Eight_nonhalt; exact seed7_infinite. Qed.
End EntryCertificate7.
End FT7TM7EntryCertificate.

(* Shared definitions from FT7TM7Bootstrap.v. *)
Module FT7TM7Bootstrap.
(* Short early execution: the same two complete returns repeated by Cycle.
   The growing W prefix is justified by Cycle, never expanded by the simulator. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat.
Import FT7TM7Rules FT7TM7Stages FT7TM7Invariant FT7TM7Layers FT7TM7Compute FT7TM7Entry FT7TM7LayerCertificate.
Module Bootstrap7.
Import Rules7 Stages7 Invariant7 Layers7 Compute7 Entry7 LayerCertificate7.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).
Local Open Scope N_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.
Definition first s := pairs 6 (zeros 1 (pairs 4 (zeros (count s) (right s)))).
Definition tick fuel s := match send (run fuel) (first s) with
  | Some (u,r)=>match send (run fuel) r with
    | Some (v,t)=>if (u=?6) && (13<=?v) then Some (St (v-13) t) else None
    | None=>None end | None=>None end.
Fixpoint reaches fuel cycles start target := match cycles with
  | O=>state_eqb start target
  | S cycles=>match tick fuel start with
    | Some s=>reaches fuel cycles s target | None=>false end end.
Definition eight s := St 6 (formN Layers7.C0 41 77
  (formN Layers7.C0 346 (116+count s) (right s))).
Local Close Scope N_scope.
Definition config n s := 0inf <{{A}} T n (A0 (nn (count s)) (denote (right s))).
Lemma first_spec s: denote (first s)=A0 (nn (count s)) (denote (right s)).
Proof. unfold first,A0; tape_simpl; reflexivity. Qed.
Lemma tick_spec fuel s t: tick fuel s=Some t -> forall n,
  config n s -[tm]->+ config (1+n) t.
Proof.
  unfold tick; destruct (send (run fuel) (first s)) as [[u r]|] eqn:E; try discriminate.
  destruct (send (run fuel) r) as [[v w]|] eqn:F; try discriminate.
  destruct ((u=?6) && (13<=?v))%N eqn:G; try discriminate.
  intros H n; injection H as H; subst t; unbool; subst u.
  unfold config; cbn [count right]; eapply Cycle.
  - applys_eq (send_spec _ (run_spec fuel) _ _ _ E); rewrite first_spec; reflexivity.
  - applys_eq (send_spec _ (run_spec fuel) _ _ _ F); flia.
Qed.
Lemma reaches_nonhalt fuel cycles target:
  (forall n, ~halts tm (config n target)) ->
  forall start, reaches fuel cycles start target=true -> forall n, ~halts tm (config n start).
Proof.
  intros H; induction cycles as [|cycles IH]; intros start; cbn [reaches].
  - intros E; apply state_eqb_spec in E; subst; exact H.
  - destruct (tick fuel start) as [s|] eqn:E; try discriminate; intros K n.
    eapply multistep_nonhalt; [apply progress_evstep; eapply tick_spec; exact E|apply IH; exact K].
Qed.
Lemma eight_nonhalt s: infinite L0 s -> forall n, ~halts tm (config n (eight s)).
Proof.
  intros I n; unfold config,eight; cbn [count right]; rewrite !formN_spec; cbn [form].
  applys_eq (Eight_nonhalt n (nn (count s)) (denote (right s)) I); unfold G; flia.
Qed.
Theorem bootstrap_nonhalt fuel cycles start target:
  reaches fuel cycles start (eight target)=true -> infinite L0 target ->
  forall n, ~halts tm (config n start).
Proof. intros H I; eapply reaches_nonhalt; [apply eight_nonhalt; exact I|exact H]. Qed.
End Bootstrap7.
End FT7TM7Bootstrap.

Import BusyCoq.Individual62.
Import NArith String.
Import FT7TM7Rules FT7TM7Compute FT7TM7Entry FT7TM7EntryCertificate FT7TM7Bootstrap.
Import Compute7 Entry7 EntryCertificate7 Bootstrap7.

Definition start := St 15 (Pairs 53 Blank).
Lemma init: c0 -[tm]->* config 0 start.
Proof.
  eapply without_counter with (n:=N.to_nat 8046%N).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (bootstrap_nonhalt 256 68 start seed7); [vm_compute; reflexivity|exact seed7_infinite].
Qed.
End TM7.

Module TM3.
Import BusyCoq.Individual62.
Import NArith String.
Import TM7.FT7TM7Rules TM7.FT7TM7Compute TM7.FT7TM7Entry TM7.FT7TM7EntryCertificate TM7.FT7TM7Bootstrap.
Import Compute7 Entry7 EntryCertificate7 Bootstrap7.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE1RF_1LB0LE_1RA---").
Definition rename q := match q with A=>E | B=>B | C=>C | D=>D | E=>A | F=>F end.
Lemma perm: Perm TM7.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Definition start := St 12 (Pairs 44 (Zeros 63 (Pairs 213 Blank))).
Lemma init: (E,snd c0) -[TM7.tm]->* config 1 start.
Proof.
  eapply without_counter with (n:=N.to_nat 138449%N).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (@perm_nonhalt' TM7.tm tm rename E _); [apply perm|].
  eapply multistep_nonhalt; [apply init|].
  eapply (bootstrap_nonhalt 256 64 start seed3); [vm_compute; reflexivity|exact seed3_infinite].
Qed.
End TM3.

Module TM4.
Import BusyCoq.Individual62.
Import NArith String.
Import TM7.FT7TM7Rules TM7.FT7TM7Compute TM7.FT7TM7Entry TM7.FT7TM7EntryCertificate TM7.FT7TM7Bootstrap.
Import Compute7 Entry7 EntryCertificate7 Bootstrap7.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC0RA_1LD1RF_1LA0LD_1RA0LC_1RE---").
Definition rename q := match q with A=>D | B=>A | C=>B | D=>C | E=>E | F=>F end.
Lemma perm: Perm TM7.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Definition start := St 64 (Pairs 151 Blank).
Lemma init: (B,snd c0) -[TM7.tm]->* config 2 start.
Proof.
  eapply without_counter with (n:=N.to_nat 62661%N).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (@perm_nonhalt' TM7.tm tm rename B _); [apply perm|].
  eapply multistep_nonhalt; [apply init|].
  eapply (bootstrap_nonhalt 256 67 start seed4); [vm_compute; reflexivity|exact seed4_infinite].
Qed.
End TM4.

Module TM5.
Import BusyCoq.Individual62.
Import NArith String.
Import TM7.FT7TM7Rules TM7.FT7TM7Compute TM7.FT7TM7Entry TM7.FT7TM7EntryCertificate TM7.FT7TM7Bootstrap.
Import Compute7 Entry7 EntryCertificate7 Bootstrap7.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1RD0RE_0RA0RC_1RC0LA_1RE---").
Definition rename q := match q with A=>B | B=>C | C=>D | D=>A | E=>E | F=>F end.
Lemma perm: Perm TM7.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Definition start := St 12 (Pairs 44 (Zeros 105 (Pairs 261 Blank))).
Lemma init: (D,snd c0) -[TM7.tm]->* config 1 start.
Proof.
  eapply without_counter with (n:=N.to_nat 205561%N).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (@perm_nonhalt' TM7.tm tm rename D _); [apply perm|].
  eapply multistep_nonhalt; [apply init|].
  eapply (bootstrap_nonhalt 256 64 start seed5); [vm_compute; reflexivity|exact seed5_infinite].
Qed.
End TM5.

Module TM6.
Import BusyCoq.Individual62.
Import NArith String.
Import TM7.FT7TM7Rules TM7.FT7TM7Compute TM7.FT7TM7Entry TM7.FT7TM7EntryCertificate TM7.FT7TM7Bootstrap.
Import Compute7 Entry7 EntryCertificate7 Bootstrap7.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LE_1RD0RB_0RE0RC_1LF1RA_1LC0LF").
Definition rename q := match q with A=>F | B=>C | C=>D | D=>E | E=>B | F=>A end.
Lemma perm: Perm TM7.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Definition start := St 12 (Pairs 44 (Zeros 105 (Pairs 261 Blank))).
Lemma init: (F,snd c0) -[TM7.tm]->* config 2 start.
Proof.
  eapply without_counter with (n:=N.to_nat 206147%N).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (@perm_nonhalt' TM7.tm tm rename F _); [apply perm|].
  eapply multistep_nonhalt; [apply init|].
  eapply (bootstrap_nonhalt 256 64 start seed6); [vm_compute; reflexivity|exact seed6_infinite].
Qed.
End TM6.

(* Shared definitions from FT7TM3_7.v. *)

(* Shared definitions from FT7TM8.v. *)
Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC0RA_1LE1RD_0RC---_1LA0LE_1RA0LC").

Module FT7TM8.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3 BusyCoq.Eqb.
Import ZArith ZifyNat Lia String List.

(* ft7.txt row 8: complete nonhalting proof, original state names. *)

Module Rules8.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{BB62.A}} [1]*>[1;0]^^b*>[0]*>[1;0]^^c*>[0]^^d*>r.
Ltac run := unfold S1; ES_v2.es.
Lemma Inc l a b c d r:
  S1 l a (1+b) c (3+d) r -->* S1 l (1+a) b (2+c) d r.
Proof. run. Qed.
Lemma Incs n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->* S1 l (n+a) b (n*2+c) d r.
Proof. gen a b c d; ind n Inc. Qed.
Lemma Empty_b l a c d r:
  S1 l a 0 c (3+d) r -->* l <{{BB62.E}} [0]^^a*>[1;0]^^(3+c)*>[0]^^d*>r.
Proof. run. Qed.
Lemma Inc2 l a b c r:
  S1 l a (1+b) c 2 r -->* S1 l (1+a) b (1+c) 0 ([1]*>r).
Proof. run. Qed.
Definition P u r r' := forall l,
  l <* [0] <{{BB62.A}} [1]*>r -->* l <{{BB62.E}} [0]^^u*>r'.
Lemma Enter l a b c r:
  S1 l a (1+b) c 0 ([1]*>r) -->*
  l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <* [0] <{{BB62.A}} [1]*>r.
Proof. run. Qed.
Lemma Return l a b c d r:
  l <* [1]^^a <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <{{BB62.E}} [0]^^d*>r -->*
  S1 l a b c d r.
Proof. run. Qed.
Lemma Call l a b c u r r':
  P u r r' -> S1 l a (1+b) c 0 ([1]*>r) -->* S1 l (1+a) b c u r'.
Proof. intros H; follow Enter; follow H; follow Return; finish. Qed.
Lemma Empty0_call l a c u r r':
  P u r r' -> S1 l a 0 c 0 ([1]*>r) -->*
  l <{{BB62.E}} [0]^^a*>[1;0]^^(1+c)*>[0]^^u*>r'.
Proof.
  intros H; unfold S1.
  mid (l <* [1]^^a <* [0;1]^^(1+c) <* [0] <{{BB62.A}} [1]*>r).
  ES_v2.es. follow H; ES_v2.es.
Qed.
Lemma D1_merge l a b c y d r:
  S1 l a (1+b) c 1 ([1;0]^^y*>[0]^^(2+d)*>r) -->*
  S1 l (1+a) b (c+y+2) d r.
Proof. run. Qed.
Lemma D1_empty l a c y d r:
  S1 l a 0 c 1 ([1;0]^^y*>[0]^^(2+d)*>r) -->*
  l <{{BB62.E}} [0]^^a*>[1;0]^^(c+y+3)*>[0]^^d*>r.
Proof. run. Qed.
Lemma RunTail l a b c d:
  S1 l a b c d 0inf -->* l <{{BB62.E}} [0]^^(a+b)*>[1;0]^^(b*2+c+3)*>0inf.
Proof.
  mid (S1 l a (b+0) c (b*3+3) 0inf).
  - unfold S1; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; finish.
  - follow Incs; follow Empty_b; finish.
Qed.

End Rules8.

Module Clock8.
Import Rules8.
Definition F (r:side) := 0inf <{{BB62.E}} r.
Definition C r := F ([1;0]^^17*>[0]^^27*>r).
Lemma P_front u r s: P u r s -> F r -[tm]->+ F ([0]^^u*>s).
Proof.
  intros H; unfold F.
  eapply progress_evstep_trans with (c':=0inf<*[0] <{{BB62.A}} [1]*>r).
  - es' & r.
  - apply H.
Qed.
Lemma First17 d r s: P (31+d) r s ->
  P 17 ([1;0]^^17*>[0]^^27*>r) ([1;0]^^34*>[0]^^(7+d)*>s).
Proof.
  intros H l.
  change (S1 l 0 17 0 26 r -->*
    l <{{BB62.E}} [0]^^17*>[1;0]^^34*>[0]^^(7+d)*>s).
  follow (Incs 8 l 0 9 0 2 r).
  follow Inc2; follow (Call l 9 7 17 (31+d) r s H).
  follow (Incs 7 l 10 0 17 (10+d) s).
  follow Empty_b; finish.
Qed.
Lemma Close17 d s:
  F ([0]^^17*>[1;0]^^34*>[0]^^(7+d)*>s) -[tm]->+
  F ([1;0]^^51*>[0]^^d*>s).
Proof. unfold F; es' d & s. Qed.
Lemma Reset51 s:
  F ([0]^^51*>s) -[tm]->+ C s.
Proof. unfold C,F; es' & s. Qed.
End Clock8.

Module Columns8.
Import Rules8.
Definition Col x z r := [1;0]^^x*>[0]^^z*>r.
Lemma Counter p z r:
  P p (Col p (1+(p*3+(3+z))) r) (Col (p*2+3) z r).
Proof.
  intros l; unfold Col.
  mid (S1 l 0 (p+0) 0 (p*3+(3+z)) r).
  unfold S1; finish.
  follow Incs; follow Empty_b; finish; flia.
Qed.
Lemma MergeCounter i j x z r:
  P (i+j) (Col (i+j) (1+(i*3+0)) (Col x (j*3+3+z) r))
    (Col (x+(i+j)*2+3) z r).
Proof.
  intros l; unfold Col.
  mid (S1 l 0 (i+j) 0 (i*3+0) ([1;0]^^x*>[0]^^(j*3+3+z)*>r)).
  unfold S1; finish.
  follow Incs.
  mid (S1 l i (j+0) (i*2+x) (j*3+(3+z)) r).
  unfold S1; rewrite (lpow_add _ (i*2) x); simpl_tape; finish; flia.
  follow Incs; follow Empty_b; finish; flia.
Qed.
Lemma MergeOne i j x z r:
  P (i+(1+j)) (Col (i+(1+j)) (1+(i*3+1))
    (Col x (2+(j*3+(3+z))) r))
    (Col (x+(i+(1+j))*2+3) z r).
Proof.
  intros l; unfold Col.
  mid (S1 l 0 (i+(1+j)) 0 (i*3+1) ([1;0]^^x*>[0]^^(2+(j*3+(3+z)))*>r)).
  unfold S1; finish.
  follow Incs; follow D1_merge.
  follow (Incs j l (1+i) 0 (i*2+x+2) (3+z) r).
  follow Empty_b; finish; flia.
Qed.
Lemma MergeOneEmpty i x z r:
  P i (Col i (1+(i*3+1)) (Col x (2+z) r)) (Col (x+i*2+3) z r).
Proof.
  intros l; unfold Col.
  mid (S1 l 0 (i+0) 0 (i*3+1) ([1;0]^^x*>[0]^^(2+z)*>r)).
  unfold S1; finish.
  follow Incs; follow D1_empty; finish; flia.
Qed.
End Columns8.

Module Layers8.
Import Rules8 Columns8.
(* q=6u+3, v=6w; all three premises are complete finite returns. *)
Inductive Round u w : nat->side->nat->side->Prop :=
| RoundIntro a b c r s t v:
  P (12+u*18) (Col (12+u*18) (10+u*18+w*12+b) r) s ->
  P (3+u*6) (Col (3+u*6) (4+u*6+w*6) s)
    (Col (33+u*48+a) (5+(u-w)*6+c) t) ->
  P (36+u*54+a) (Col (36+u*54+a) c t) v ->
  Round u w b r a v.
Lemma Round_merge u w x z r s: w<=u ->
  P (39+u*54+x) (Col (39+u*54+x) z r) s ->
  Round u w 3 (Col x (41+u*54-w*24+z) r) (x+3) s.
Proof.
  intros Hw H.
  eapply RoundIntro with (c:=z) (t:=r)
    (s:=Col (x+27+u*36) (14+u*18-w*12+z) r).
  - applys_eq (MergeCounter (4+u*6+w*4) (8+u*12-w*4) x
      (14+u*18-w*12+z) r); flia.
  - applys_eq (MergeCounter (1+u*2+w*2) (2+u*4-w*2) (x+27+u*36)
      (5+(u-w)*6+z) r); flia.
  - applys_eq H; flia.
Qed.
Lemma Round_call u w c r s: w<=u ->
  P (39+u*54) (Col (39+u*54) c r) s ->
  Round u w (44+u*54-w*24+c) r 3 s.
Proof.
  intros Hw H.
  eapply RoundIntro with (c:=c) (t:=r)
    (s:=Col (27+u*36) (14+u*18-w*12+c) r).
  - applys_eq (Counter (12+u*18) (14+u*18-w*12+c) r); flia.
  - applys_eq (MergeCounter (1+u*2+w*2) (2+u*4-w*2) (27+u*36)
      (5+(u-w)*6+c) r); flia.
  - applys_eq H; flia.
Qed.
Lemma Round_large u w z r: w<=u ->
  Round u w (165+u*216-w*24+z) r 3 (Col (81+u*108) z r).
Proof.
  intros Hw; applys_eq (Round_call u w (1+((39+u*54)*3+(3+z))) r
    (Col (81+u*108) z r)); try flia.
  applys_eq (Counter (39+u*54) z r); flia.
Qed.
Inductive Walk (R:nat->side->nat->side->Prop) : nat->side->nat->side->Prop :=
| One b r a s: R b r a s -> Walk R b r a s
| More b r a s c t: R b r a s -> Walk R a s c t -> Walk R b r c t.
Definition Embed u w b r := Col (81+u*108) (159+u*216+w*24+b) r.
Lemma Grow u w b r a v: w<=u -> Round (6+u*9) (w*4) b r a v ->
  Walk (Round u w) 3 (Embed u w b r) 3 (Embed u w a v).
Proof.
  intros Hw H; destruct H as [a b c r s t v H1 H2 H3]; unfold Embed.
  eapply More with (a:=84+u*108) (s:=s).
  - applys_eq (Round_merge u w (81+u*108)
      (10+(6+u*9)*18+(w*4)*12+b) r s); try flia.
    applys_eq H1; flia.
  - eapply More with (a:=3)
      (s:=Col (33+(6+u*9)*48+a) (5+(6+u*9-w*4)*6+c) t).
    + applys_eq (Round_call u w (4+(6+u*9)*6+(w*4)*6) s
        (Col (33+(6+u*9)*48+a) (5+(6+u*9-w*4)*6+c) t)); try flia.
      applys_eq H2; flia.
    + eapply More with (a:=324+u*432+a) (s:=v).
      * applys_eq (Round_merge u w (33+(6+u*9)*48+a) c t v); try flia.
        applys_eq H3; flia.
      * apply One; applys_eq (Round_large u w (159+u*216+w*24+a) v); flia.
Qed.
End Layers8.

(* One returning-call evaluator for both concrete and affine counters. *)
Import Rules8 Columns8 ListNotations.

Module Compute8.
Record Ops (A:Type) := OpsMake {
  lit:Z->A; plus:A->A->A; minus:A->A->A; scale:Z->A->A;
  third:A->A; ge0:A->bool; same:A->A->bool
}.
Arguments lit {A} _ _.
Arguments plus {A} _ _ _.
Arguments minus {A} _ _ _.
Arguments scale {A} _ _ _.
Arguments third {A} _ _.
Arguments ge0 {A} _ _.
Arguments same {A} _ _ _.
Record Laws {A} (op:Ops A) (value:A->Z) : Prop := LawsMake {
  value_lit:forall z, value (lit op z)=z;
  value_plus:forall x y, value (plus op x y)=(value x+value y)%Z;
  value_minus:forall x y, value (minus op x y)=(value x-value y)%Z;
  value_scale:forall z x, value (scale op z x)=(z*value x)%Z;
  ge0_sound:forall x, ge0 op x=true -> (0<=value x)%Z;
  same_sound:forall x y, same op x y=true -> value x=value y
}.
Arguments value_lit {A op value} _ _.
Arguments value_plus {A op value} _ _ _.
Arguments value_minus {A op value} _ _ _.
Arguments value_scale {A op value} _ _ _.
Arguments ge0_sound {A op value} _ _ _.
Arguments same_sound {A op value} _ _ _ _.

Section Program.
Context {A:Type} (op:Ops A).
Local Notation "'K' n" := (lit op n) (at level 10).
Local Infix "+" := (plus op).
Local Infix "-" := (minus op).
Local Notation "n '*:' x" := (scale op n x) (at level 40).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition Tape := list (A*A).
Definition bump x z (r:Tape) := match r with
  | nil=>[(x,K 0)]
  | (y,d)::r=>if same op z (K 0) then (x+y,d)::r else (x,z)::(y,d)::r end.
Fixpoint valid (r:Tape) := match r with
  | nil=>true | (x,d)::r=>ge0 op x && ge0 op d && valid r end.
Definition send (core:A->A->A->Tape->option Tape) (r:Tape) : option (A*Tape) :=
  match r with
  | nil=>Some (K 0,bump (K 3) (K 0) nil)
  | (x,d)::nil=>if ge0 op x then Some (x,bump (2*:x+K 3) (K 0) nil) else None
  | (x,d)::r=>if ge0 op x && ge0 op (d-K 1) then
      match core x (K 0) (d-K 1) r with Some s=>Some (x,s) | None=>None end
      else None end.
Fixpoint run fuel b c d r : option Tape := match fuel with
  | O=>None
  | S fuel=>if ge0 op b && ge0 op c && ge0 op d && valid r then
      match r with
      | nil=>Some (bump (2*:b+c+K 3) (K 0) nil)
      | (x,z)::r' =>
        if ge0 op (d-(3*:b+K 3)) then
          Some (bump (2*:b+c+K 3) (d-(3*:b+K 3)) r)
        else let i:=third op d in let e:=d-3*:i in
          if ge0 op i && ge0 op (b-i) then
            let b':=b-i in let c':=2*:i+c in
            if same op e (K 0) then run fuel b' (c'+x) z r'
            else if same op e (K 1) then
              match r' with
              | nil=>Some (bump (2*:b'+c'+x+K 3) (K 0) nil)
              | _=>if ge0 op (z-K 2) then
                  if same op b' (K 0) then Some (bump (c'+x+K 3) (z-K 2) r')
                  else if ge0 op (b'-K 1) then run fuel (b'-K 1) (c'+x+K 2) (z-K 2) r'
                  else None
                else None end
            else if same op e (K 2) && ge0 op (b'-K 2) then
              match send (run fuel) r with
              | Some (u,s)=>run fuel (b'-K 2) (c'+K 1) u s
              | None=>None end
            else None
          else None
      end
    else None
  end.
End Program.

(* A small semantic API; the evaluator never unfolds the machine's table. *)
Definition RunN b c d r s := forall l a,
  S1 l a b c d r -->* l <{{BB62.E}} [0]^^(a+b)*>s.
Lemma RInc n b c d r s:
  RunN b (n*2+c) d r s -> RunN (n+b) c (n*3+d) r s.
Proof. intros H l a; follow Incs; follow (H l (n+a)); finish; flia. Qed.
Lemma RMerge b c x d r s:
  RunN b (c+x) d r s -> RunN b c 0 (Col x d r) s.
Proof.
  intros H l a; applys_eq (H l a); unfold S1,Col;
    rewrite (lpow_add _ c x); simpl_tape; reflexivity.
Qed.
Lemma ROne b c x d r s:
  RunN b (c+x+2) d r s -> RunN (1+b) c 1 (Col x (2+d) r) s.
Proof. intros H l a; unfold Col; follow D1_merge; follow (H l (1+a)); finish; flia. Qed.
Lemma ROneEmpty c x d r:
  RunN 0 c 1 (Col x (2+d) r) (Col (c+x+3) d r).
Proof. intros l a; unfold Col; follow D1_empty; finish; flia. Qed.
Lemma RTail b c d: RunN b c d 0inf (Col (b*2+c+3) 0 0inf).
Proof. intros l a; follow RunTail; unfold Col; finish. Qed.
Lemma ROneTail b c x z: RunN b c 1 (Col x z 0inf) (Col (b*2+c+x+3) 0 0inf).
Proof.
  intros l a.
  mid (S1 l a b c 1 (Col x 2 0inf)).
  unfold S1,Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; finish.
  destruct b as [|b]; unfold Col.
  - follow D1_empty; finish; flia.
  - follow D1_merge; follow RunTail; finish; flia.
Qed.
Lemma REmpty b c d r:
  RunN b c (b*3+(3+d)) r (Col (b*2+c+3) d r).
Proof. intros l a; follow (Incs b l a 0 c (3+d) r); follow Empty_b; unfold Col; finish; flia. Qed.
Lemma RCall b c u r t s:
  P u r t -> RunN b (c+1) u t s -> RunN (2+b) c 2 r s.
Proof.
  intros H K l a; follow Inc2; follow (Call l (1+a) b (1+c) u r t H).
  follow (K l (2+a)); finish; flia.
Qed.
Lemma PTail p z: P p (Col p z 0inf) (Col (p*2+3) 0 0inf).
Proof.
  intros l; unfold Col.
  mid (S1 l 0 p 0 0 0inf).
  unfold S1; cbn [lpow Str_app]; repeat rewrite (lpow_all0 [0]) by solve_const0_eq.
  rewrite <- (const_unfold _ 0); finish.
  follow RunTail; finish; flia.
Qed.
Lemma PHead b d r s: RunN b 0 d r s -> P b (Col b (1+d) r) s.
Proof. intros H l; exact (H l 0%nat). Qed.

Section Soundness.
Context {A:Type} (op:Ops A) (value:A->Z) (law:Laws op value).
Local Notation "'nn' x" := (Z.to_nat (value x)) (at level 10).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Fixpoint denote (r:@Tape A) := match r with
  | nil=>0inf | (x,z)::r=>Col (nn x) (nn z) (denote r) end.
Definition Run b c d r s := RunN (nn b) (nn c) (nn d) (denote r) (denote s).
Ltac vals := repeat first [rewrite (value_lit law) in * |
  rewrite (value_plus law) in * | rewrite (value_minus law) in * |
  rewrite (value_scale law) in *].
Ltac decode := repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:ge0 op ?x=true |- _=>apply (ge0_sound law x) in H
  | H:same op ?x ?y=true |- _=>apply (same_sound law x y) in H end; vals.
Lemma valid_spec r: valid op r=true ->
  Forall (fun xd=>(0<=value (fst xd) /\ 0<=value (snd xd))%Z) r.
Proof.
  induction r as [|[x d] r IH]; cbn [valid]; intros H; [constructor|].
  apply and_true_iff in H; destruct H as [H Hr].
  apply and_true_iff in H; destruct H as [Hx Hd].
  constructor; [cbn; split; eapply ge0_sound; eassumption|apply IH; exact Hr].
Qed.
Lemma bump_spec x z r: (0<=value x)%Z ->
  Forall (fun xd=>(0<=value (fst xd) /\ 0<=value (snd xd))%Z) r ->
  denote (bump op x z r)=Col (nn x) (nn z) (denote r).
Proof.
  intros Hx Hr; destruct r as [|[y d] r]; cbn [bump denote].
  - unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
  - destruct (same op z (lit op 0)) eqn:E; [|reflexivity].
    inversion Hr as [|p ps Hhd Htl]; subst; cbn in Hhd.
    apply (same_sound law) in E; vals.
    cbn [denote]; vals; unfold Col; rewrite E; cbn.
    rewrite Z2Nat.inj_add by lia.
    rewrite (lpow_add _ (nn x) (nn y)); simpl_tape; reflexivity.
Qed.
Lemma send_spec core r u s:
  (forall b c d r s, core b c d r=Some s -> Run b c d r s) ->
  send op core r=Some (u,s) -> P (nn u) (denote r) (denote s).
Proof.
  intros H; destruct r as [|[x d] r]; cbn [send].
  - intros E; injection E as Eu Es; subst u s; cbn [bump denote]; vals.
    applys_eq (PTail 0 0); unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
  -
  destruct r as [|[y e] r].
  + destruct (ge0 op x) eqn:Hx; try discriminate.
    intros E; injection E as Eu Es; subst u s; cbn [bump denote]; decode.
    applys_eq (PTail (nn x) (nn d)); f_equal; lia.
  + destruct (ge0 op x && ge0 op (minus op d (lit op 1))) eqn:E; try discriminate.
    destruct (core x (lit op 0) (minus op d (lit op 1)) ((y,e)::r)) as [t|] eqn:C; try discriminate.
    intros K; injection K as Eu Es; subst u s; apply H in C; unfold Run in C; decode.
    cbn [denote]; applys_eq (PHead _ _ _ _ C); vals; flia.
Qed.

Local Opaque bump.
Theorem run_spec fuel b c d r s:
  run op fuel b c d r=Some s -> Run b c d r s.
Proof.
  revert b c d r s; induction fuel as [|fuel IH]; intros b c d r s; cbn [run]; [discriminate|].
  destruct (ge0 op b && ge0 op c && ge0 op d && valid op r) eqn:OK; try discriminate.
  apply and_true_iff in OK; destruct OK as [OK Hr]; apply valid_spec in Hr; decode.
  destruct r as [|[x z] r].
  - intros E; inversion E; subst; unfold Run; cbn [bump denote]; vals.
    applys_eq (RTail (nn b) (nn c) (nn d)); flia.
  - inversion Hr as [|p ps Hhd Htail]; subst; cbn in Hhd; destruct Hhd as [Hx Hz].
    destruct (ge0 op (minus op d (plus op (scale op 3 b) (lit op 3)))) eqn:Ebig.
    + intros E; inversion E; subst; unfold Run; rewrite bump_spec; try assumption; vals; try lia.
      apply (ge0_sound law) in Ebig; vals.
      applys_eq (REmpty (nn b) (nn c) (Z.to_nat (value d-(3*value b+3))) (denote ((x,z)::r))); flia.
    + set (i:=third op d).
      destruct (ge0 op i && ge0 op (minus op b i)) eqn:Ei; try discriminate.
      destruct (same op (minus op d (scale op 3 i)) (lit op 0)) eqn:E0.
      * intros E; apply IH in E; unfold Run in *; decode.
        applys_eq (RInc (nn i) (nn (minus op b i)) (nn c) 0 (denote ((x,z)::r)) (denote s)); try (vals; flia).
        cbn [denote]; apply RMerge.
        applys_eq E; vals; flia.
      * destruct (same op (minus op d (scale op 3 i)) (lit op 1)) eqn:E1.
        -- destruct r as [|[y w] r].
           ++ intros E; inversion E; subst; unfold Run; cbn [bump denote]; decode.
              applys_eq (RInc (nn i) (nn (minus op b i)) (nn c) 1 (Col (nn x) (nn z) 0inf)
                (Col (Z.to_nat (2*(value b-value i)+(2*value i+value c)+value x+3)) 0 0inf)); try (vals; flia).
              applys_eq (ROneTail (nn (minus op b i)) (nn i*2+nn c) (nn x) (nn z)); vals; flia.
           ++ destruct (ge0 op (minus op z (lit op 2))) eqn:Ez; try discriminate.
              destruct (same op (minus op b i) (lit op 0)) eqn:Eb.
              ** intros E; inversion E; subst; decode; unfold Run; rewrite bump_spec; try assumption; vals; try lia.
                 applys_eq (RInc (nn i) 0 (nn c) 1 (denote ((x,z)::(y,w)::r))
                   (Col (Z.to_nat (2*value i+value c+value x+3)) (Z.to_nat (value z-2)) (denote ((y,w)::r)))); try flia.
                 cbn [denote]; applys_eq (ROneEmpty (nn i*2+nn c) (nn x) (Z.to_nat (value z-2))
                   (denote ((y,w)::r))); flia.
              ** destruct (ge0 op (minus op (minus op b i) (lit op 1))) eqn:Eb1; try discriminate.
                 intros E; apply IH in E; unfold Run in *; decode.
                 applys_eq (RInc (nn i) (1+nn (minus op (minus op b i) (lit op 1))) (nn c) 1
                   (denote ((x,z)::(y,w)::r)) (denote s)); try (vals; flia).
                 cbn [denote].
                 applys_eq (ROne (nn (minus op (minus op b i) (lit op 1))) (nn i*2+nn c)
                   (nn x) (Z.to_nat (value z-2)) (denote ((y,w)::r)) (denote s)); try (vals; flia).
                 applys_eq E; vals; flia.
        -- destruct (same op (minus op d (scale op 3 i)) (lit op 2) &&
             ge0 op (minus op (minus op b i) (lit op 2))) eqn:E2; try discriminate.
           destruct (send op (run op fuel) ((x,z)::r)) as [[u t]|] eqn:Pcall; try discriminate.
           intros E; apply IH in E.
           apply (send_spec _ _ _ _ IH) in Pcall; unfold Run in *; decode.
           applys_eq (RInc (nn i) (2+nn (minus op (minus op b i) (lit op 2))) (nn c) 2
             (denote ((x,z)::r)) (denote s)); try (vals; flia).
           eapply RCall; [exact Pcall|].
           applys_eq E; vals; flia.
Qed.
Corollary call_spec fuel r u s:
  send op (run op fuel) r=Some (u,s) -> P (nn u) (denote r) (denote s).
Proof. apply send_spec, run_spec. Qed.
End Soundness.

Definition concrete := @OpsMake Z (fun z=>z) Z.add Z.sub Z.mul
  (fun z=>(z/3)%Z) (Z.leb 0) Z.eqb.
Lemma concrete_laws: Laws concrete (fun z=>z).
Proof.
  constructor; cbn; intros; try reflexivity.
  - apply Z.leb_le; assumption.
  - apply Z.eqb_eq; assumption.
Qed.
Example seed_call:
  send concrete (run concrete 64) [(105%Z,123%Z);(619%Z,0%Z)]=
    Some (105%Z,[(210%Z,427%Z);(1241%Z,0%Z)]).
Proof. vm_compute; reflexivity. Qed.
End Compute8.

(* Three complete calls per layer event, with one shared soundness lemma. *)
Import Rules8 Columns8 Layers8 Compute8 ListNotations.

Module Program8.
Section Definitions.
Context {A:Type} (op:Ops A).
Local Notation "'K' z" := (lit op z) (at level 10).
Local Infix "+" := (plus op).
Local Infix "-" := (minus op).
Local Notation "z '*:' x" := (scale op z x) (at level 40).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition invoke fuel p d r := match send op (run op fuel) ((p,d)::r) with
  | Some (u,s)=>if same op u p then Some s else None | None=>None end.
Definition middle u w r := match r with
  | nil=>None
  | (x,z)::r=>let a:=x-(K 33+48*:u) in
      if ge0 op a then match r with
        | nil=>Some (a,K 0,nil)
        | _=>let c:=z-(K 5+6*:(u-w)) in
            if ge0 op c then Some (a,c,r) else None end
      else None end.
Definition step fuel u w b r :=
  if ge0 op w && ge0 op (u-w) && ge0 op b then
    match invoke fuel (K 12+18*:u) (K 10+18*:u+12*:w+b) r with
    | Some s=>match invoke fuel (K 3+6*:u) (K 4+6*:u+6*:w) s with
      | Some t=>match middle u w t with
        | Some (a,c,v)=>match invoke fuel (K 36+54*:u+a) c v with
          | Some out=>Some (a,out) | None=>None end
        | None=>None end | None=>None end | None=>None end
  else None.
End Definitions.

Section Soundness.
Context {A:Type} (op:Ops A) (value:A->Z) (law:Laws op value).
Local Notation "'nn' x" := (Z.to_nat (value x)) (at level 10).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Ltac vals := repeat first [rewrite (value_lit law) in * |
  rewrite (value_plus law) in * | rewrite (value_minus law) in * |
  rewrite (value_scale law) in *].
Ltac decode := repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:ge0 op ?x=true |- _=>apply (ge0_sound law x) in H
  | H:same op ?x ?y=true |- _=>apply (same_sound law x y) in H end; vals.
Lemma invoke_spec fuel p d r s:
  invoke op fuel p d r=Some s ->
  P (nn p) (Col (nn p) (nn d) (denote value r)) (denote value s).
Proof.
  unfold invoke; destruct (send op (run op fuel) ((p,d)::r)) as [[u t]|] eqn:E; try discriminate.
  destruct (same op u p) eqn:K; try discriminate.
  intros H; injection H as H; subst t.
  apply (call_spec op value law) in E; apply (same_sound law) in K; cbn [denote] in E.
  rewrite K in E; exact E.
Qed.
Lemma middle_spec u w r a c t:
  (0<=value w<=value u)%Z -> middle op u w r=Some (a,c,t) ->
  (0<=value a /\ 0<=value c)%Z /\
  denote value r=Col (33+nn u*48+nn a) (5+(nn u-nn w)*6+nn c) (denote value t).
Proof.
  intros Hw; destruct r as [|[x z] r]; cbn [middle]; try discriminate.
  destruct (ge0 op (minus op x (plus op (lit op 33) (scale op 48 u)))) eqn:Ea; try discriminate.
  destruct r as [|[y d] r].
  - intros H; injection H as Ha Hc Ht; subst a c t; decode; split; [lia|].
    cbn [denote]; vals; unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq.
    f_equal; f_equal; lia.
  - destruct (ge0 op (minus op z (plus op (lit op 5) (scale op 6 (minus op u w))))) eqn:Ec; try discriminate.
    intros H; injection H as Ha Hc Ht; subst a c t; decode; split; [lia|].
    cbn [denote]; vals; f_equal; lia.
Qed.
Lemma step_spec fuel u w b r a s:
  step op fuel u w b r=Some (a,s) ->
  Round (nn u) (nn w) (nn b) (denote value r) (nn a) (denote value s).
Proof.
  unfold step.
  destruct (ge0 op w && ge0 op (minus op u w) && ge0 op b) eqn:K; try discriminate.
  destruct (invoke op fuel (plus op (lit op 12) (scale op 18 u))
    (plus op (plus op (plus op (lit op 10) (scale op 18 u)) (scale op 12 w)) b) r) as [v|] eqn:E1; try discriminate.
  destruct (invoke op fuel (plus op (lit op 3) (scale op 6 u))
    (plus op (plus op (lit op 4) (scale op 6 u)) (scale op 6 w)) v) as [t|] eqn:E2; try discriminate.
  destruct (middle op u w t) as [[[aa c] tail]|] eqn:M; try discriminate.
  destruct (invoke op fuel (plus op (plus op (lit op 36) (scale op 54 u)) aa) c tail) as [out|] eqn:E3; try discriminate.
  intros H; injection H as Ha Hs; subst aa out.
  decode; apply invoke_spec in E1,E2,E3.
  apply middle_spec in M; [destruct M as [[Ha Hc] Mt]|lia].
  eapply RoundIntro with (c:=nn c) (t:=denote value tail) (s:=denote value v).
  - applys_eq E1; vals; flia.
  - rewrite Mt in E2; applys_eq E2; vals; flia.
  - applys_eq E3; vals; flia.
Qed.
End Soundness.

Inductive Action := Do | Up | Down.
Record Config (A:Type) := Cfg {
  parents:list (A*A); current_u:A; current_w:A; count:A; right:@Tape A
}.
Arguments parents {A} _.
Arguments current_u {A} _.
Arguments current_w {A} _.
Arguments count {A} _.
Arguments right {A} _.
Section Plan.
Context {A:Type} (op:Ops A).
Local Notation "'K' z" := (lit op z) (at level 10).
Local Infix "+" := (plus op).
Local Infix "-" := (minus op).
Local Notation "z '*:' x" := (scale op z x) (at level 40).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition next_u u := K 6+9*:u.
Definition next_w w := 4*:w.
Definition column u := K 81+108*:u.
Definition offset u w := K 159+216*:u+24*:w.
Definition action fuel act (s:Config A) :=
  let ps:=parents s in let u:=current_u s in let w:=current_w s in
  let b:=count s in let r:=right s in match act with
  | Do=>match step op fuel u w b r with
    | Some (a,t)=>Some (@Cfg A ps u w a t) | None=>None end
  | Up=>match r with
    | (x,z)::t=>let a:=z-offset u w in
      if ge0 op w && ge0 op (u-w) && same op b (K 3) && same op x (column u) && ge0 op a
      then Some (@Cfg A ((u,w)::ps) (next_u u) (next_w w) a t) else None
    | nil=>None end
  | Down=>match ps with
    | (u0,w0)::ps=>if ge0 op b && ge0 op w0 && ge0 op (u0-w0) &&
      same op u (next_u u0) && same op w (next_w w0)
      then Some (@Cfg A ps u0 w0 (K 3) ((column u0,offset u0 w0+b)::r)) else None
    | nil=>None end end.
Fixpoint execute fuel code s := match code with
  | nil=>Some s | a::code=>match action fuel a s with
    | Some t=>execute fuel code t | None=>None end end.
End Plan.

(* Generated by the already audited affine trace. No intermediate tapes. *)
Definition seven := [Do;Do;Do;Do;Do;Do;Do;Up;Do;Do;Do;Do;Do;Do;Up;
  Do;Do;Do;Do;Do;Do;Up;Do;Do;Do;Do;Do;Up;Do;Do;Do;Do;Do;Up;
  Do;Do;Do;Do;Do;Up;Down;Do;Do;Do;Do;Up;Do;Do;Up].

(* Semantics of the frame stack. Only Do is a physical transition; Up/Down
   change its representation. A frame expands a child event into a walk. *)
Lemma walk_trans R b r a s c t:
  Walk R b r a s -> Walk R a s c t -> Walk R b r c t.
Proof. intros H; induction H; eauto using More. Qed.
Lemma grow_walk u w b r a s: w<=u ->
  Walk (Round (6+u*9) (w*4)) b r a s ->
  Walk (Round u w) 3 (Embed u w b r) 3 (Embed u w a s).
Proof.
  intros Hw H; induction H.
  - apply Grow; assumption.
  - eapply walk_trans; [apply Grow; eassumption|exact IHWalk].
Qed.
Record Point := Pt { root_u:nat; root_w:nat; number:nat; suffix:side }.
Fixpoint flatten (ps:list (nat*nat)) u w b r := match ps with
  | nil=>Pt u w b r
  | (u0,w0)::ps=>flatten ps u0 w0 3 (Embed u0 w0 b r) end.
Inductive Well : list (nat*nat)->nat->nat->Prop :=
| Wnil u w: Well nil u w
| Wcons ps u w: w<=u -> Well ps u w -> Well ((u,w)::ps) (6+u*9) (w*4).
Inductive Moves : Point->Point->Prop :=
| Move u w b r a s: Walk (Round u w) b r a s -> Moves (Pt u w b r) (Pt u w a s).
Lemma lift_walk ps u w b r a s: Well ps u w -> Walk (Round u w) b r a s ->
  Moves (flatten ps u w b r) (flatten ps u w a s).
Proof.
  intros W; revert b r a s; induction W; intros b r a s K; cbn [flatten].
  - constructor; exact K.
  - apply IHW, grow_walk; assumption.
Qed.
Lemma moves_trans p q r: Moves p q -> Moves q r -> Moves p r.
Proof.
  intros H K; inversion H; subst; inversion K; subst;
    constructor; eapply walk_trans; eassumption.
Qed.
Definition Path p q := p=q \/ Moves p q.
Lemma path_trans p q r: Path p q -> Path q r -> Path p r.
Proof.
  intros [H|H] [K|K]; subst; unfold Path; eauto using moves_trans.
Qed.
Lemma moves_path p q r: Moves p q -> Path q r -> Moves p r.
Proof. intros H [K|K]; subst; eauto using moves_trans. Qed.

Section ExecuteSoundness.
Context {A:Type} (op:Ops A) (value:A->Z) (law:Laws op value).
Local Notation "'nn' x" := (Z.to_nat (value x)) (at level 10).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition mapped ps := map (fun uw=>(nn (fst uw),nn (snd uw))) ps.
Definition well s := Well (mapped (parents s)) (nn (current_u s)) (nn (current_w s)).
Definition point s := flatten (mapped (parents s)) (nn (current_u s)) (nn (current_w s))
  (nn (count s)) (denote value (right s)).
Ltac vals := repeat first [rewrite (value_lit law) in * |
  rewrite (value_plus law) in * | rewrite (value_minus law) in * |
  rewrite (value_scale law) in *].
Ltac decode := repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:ge0 op ?x=true |- _=>apply (ge0_sound law x) in H
  | H:same op ?x ?y=true |- _=>apply (same_sound law x y) in H end; vals.
Ltac state_simpl := unfold well,point in *; cbn [parents current_u current_w count right mapped map
  fst snd flatten denote] in *.

Theorem action_spec fuel act s t: well s -> action op fuel act s=Some t ->
  well t /\ match act with Do=>Moves (point s) (point t) | _=>point s=point t end.
Proof.
  destruct s as [ps u w b r]; intros W; destruct act;
    cbn [action parents current_u current_w count right].
  - destruct (step op fuel u w b r) as [[a v]|] eqn:E; try discriminate.
    intros H; injection H as H; subst t; state_simpl; split; [exact W|].
    apply lift_walk; [exact W|apply One; eapply step_spec; eassumption].
  - destruct r as [|[x z] r]; try discriminate.
    destruct (ge0 op w && ge0 op (minus op u w) && same op b (lit op 3) &&
      same op x (column op u) && ge0 op (minus op z (offset op u w))) eqn:K; try discriminate.
    intros H; injection H as H; subst t; state_simpl.
    unfold next_u,next_w,column,offset in *; decode; split.
    + applys_eq (Wcons (mapped ps) (nn u) (nn w)); try assumption; flia.
    + unfold Embed; f_equal; try flia; f_equal; flia.
  - destruct ps as [|[u0 w0] ps]; try discriminate.
    destruct (ge0 op b && ge0 op w0 && ge0 op (minus op u0 w0) &&
      same op u (next_u op u0) && same op w (next_w op w0)) eqn:K; try discriminate.
    intros H; injection H as H; subst t; state_simpl.
    unfold next_u,next_w,column,offset in *; decode; split.
    + inversion W; subst; assumption.
    + unfold Embed; f_equal; try flia; f_equal; flia.
Qed.
Theorem execute_spec fuel code s t: well s -> execute op fuel code s=Some t ->
  well t /\ Path (point s) (point t).
Proof.
  revert s t; induction code as [|act code IH]; intros s t W; cbn [execute].
  - intros H; injection H as H; subst t; split; [exact W|left; reflexivity].
  - destruct (action op fuel act s) as [v|] eqn:E; try discriminate.
    intros K; destruct (action_spec fuel act s v W E) as [V P].
    destruct (IH v t V K) as [T R]; split; [exact T|].
    eapply path_trans; [|exact R]; destruct act; [right|left|left]; exact P.
Qed.
Theorem execute_progress fuel code s t: well s -> execute op fuel (Do::code) s=Some t ->
  well t /\ Moves (point s) (point t).
Proof.
  intros W; cbn [execute]; destruct (action op fuel Do s) as [v|] eqn:E; try discriminate.
  intros K; destruct (action_spec fuel Do s v W E) as [V P].
  destruct (execute_spec fuel code v t V K) as [T R]; split; [exact T|].
  eapply moves_path; eassumption.
Qed.
End ExecuteSoundness.

(* Count nonempty walks, not representation changes. This lower bound on
   progress is retained when a whole child computation is lifted. *)
Definition plug ps p := flatten ps (root_u p) (root_w p) (number p) (suffix p).
Lemma lift_moves ps p q: Well ps (root_u p) (root_w p) -> Moves p q ->
  Moves (plug ps p) (plug ps q).
Proof. intros W H; destruct H; apply lift_walk; assumption. Qed.
Inductive Chain : nat->Point->Point->Prop :=
| Done p: Chain 0 p p
| Link n p q r: Moves p q -> Chain n q r -> Chain (1+n) p r.
Lemma lift_chain ps n p q: Well ps (root_u p) (root_w p) -> Chain n p q ->
  Chain n (plug ps p) (plug ps q).
Proof.
  intros W H; revert W; induction H; intros W.
  - constructor.
  - eapply Link; [apply lift_moves; eassumption|apply IHChain].
    destruct H; exact W.
Qed.
Definition Infinite p := forall n, exists q, Chain n p q.
Lemma infinite_lift ps p: Well ps (root_u p) (root_w p) -> Infinite p ->
  Infinite (plug ps p).
Proof. intros W I n; destruct (I n) as [q H]; eauto using lift_chain. Qed.
End Program8.

(* Affine integer counters and a sufficient, exact polyhedral guard. *)
Import Compute8 Program8 ListNotations.
Module Affine8.
Local Open Scope Z_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.
Record Aff := F { ac:Z; au:Z; aw:Z; ab:Z; ah:Z }.
Record Env := E { eu:Z; ew:Z; eb:Z; et:Z }.
Definition eval e f := ac f + au f*eu e + aw f*ew e + ab f*eb e + ah f*et e.
Definition constant z := F z 0 0 0 0.
Definition add x y := F (ac x+ac y) (au x+au y) (aw x+aw y) (ab x+ab y) (ah x+ah y).
Definition neg x := F (-ac x) (-au x) (-aw x) (-ab x) (-ah x).
Definition sub x y := add x (neg y).
Definition mul z x := F (z*ac x) (z*au x) (z*aw x) (z*ab x) (z*ah x).
Definition div3 x := F (ac x/3) (au x/3) (aw x/3) (ab x/3) (ah x/3).
Definition eqb x y := (ac x=?ac y) && (au x=?au y) && (aw x=?aw y) &&
  (ab x=?ab y) && (ah x=?ah y).
Definition slope x := 40*au x + Z.min (aw x) 0 +
  Z.min (60*ab x) (80*ab x) + Z.min (840*ah x) (870*ah x).
Definition offset x := 240*ac x-120*au x-200*ab x-40*ah x.
Definition guard x := (0<=?slope x) && (0<=?offset x+70000*slope x).
Definition op := @OpsMake Aff constant add sub mul div3 guard eqb.
Definition good e :=
  let q:=6*eu e+3 in let v:=6*ew e in let b:=6*eb e+5 in let t:=6*et e+1 in
  70000<=q /\ 0<=40*v /\ 40*v<=q /\
  3*q<=2*b /\ 2*b<=4*q /\ 84*q<=4*t /\ 4*t<=87*q.

Lemma box_terms q v b t u w k h:
  0<=q -> 0<=40*v -> 40*v<=q ->
  3*q<=2*b -> 2*b<=4*q -> 84*q<=4*t -> 4*t<=87*q ->
  (40*u+Z.min w 0+Z.min (60*k) (80*k)+Z.min (840*h) (870*h))*q
    <=40*u*q+40*w*v+40*k*b+40*h*t.
Proof.
  intros Hq Hv0 Hv Hb0 Hb Ht0 Ht.
  assert (Z.min w 0*q<=40*w*v) as Hw.
  { destruct (Z_le_dec 0 w); [rewrite Z.min_r by lia|rewrite Z.min_l by lia]; nia. }
  assert (Z.min (60*k) (80*k)*q<=40*k*b) as Hk.
  { destruct (Z_le_dec 0 k); [rewrite Z.min_l by lia|rewrite Z.min_r by lia]; nia. }
  assert (Z.min (840*h) (870*h)*q<=40*h*t) as Hh.
  { destruct (Z_le_dec 0 h); [rewrite Z.min_l by lia|rewrite Z.min_r by lia]; nia. }
  nia.
Qed.
Lemma guard_spec e x: good e -> guard x=true -> 0<=eval e x.
Proof.
  intros H G; unfold guard in G; apply and_true_iff in G; destruct G as [Gs Gc].
  apply Z.leb_le in Gs,Gc.
  unfold good in H; destruct H as [Hq [Hv0 [Hv [Hb0 [Hb [Ht0 Ht]]]]]].
  pose proof (box_terms (6*eu e+3) (6*ew e) (6*eb e+5) (6*et e+1)
    (au x) (aw x) (ab x) (ah x) ltac:(lia) Hv0 Hv Hb0 Hb Ht0 Ht) as B.
  fold (slope x) in B.
  assert (240*eval e x=offset x+40*au x*(6*eu e+3)+40*aw x*(6*ew e)+
    40*ab x*(6*eb e+5)+40*ah x*(6*et e+1)) by (unfold eval,offset; ring).
  nia.
Qed.
Lemma eqb_spec e x y: eqb x y=true -> eval e x=eval e y.
Proof.
  unfold eqb; intros H; repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:Z.eqb _ _=true |- _=>apply Z.eqb_eq in H end.
  unfold eval; congruence.
Qed.
Lemma laws e: good e -> Laws op (eval e).
Proof.
  intros G; constructor; cbn [op].
  - intros; unfold eval,constant; cbn; ring.
  - intros; unfold eval,add; cbn; ring.
  - intros; unfold sub,eval,add,neg; cbn; ring.
  - intros; unfold eval,mul; cbn; ring.
  - intros; eapply guard_spec; eassumption.
  - apply eqb_spec.
Qed.

Definition U := F 0 1 0 0 0.
Definition W := F 0 0 1 0 0.
Definition B := F 5 0 0 6 0.
Definition T := F 1 0 0 0 6.
Definition start := @Cfg Aff nil U W B [(T,constant 0)].
Fixpoint ancestry n u w := match n with
  | O=>nil
  | S n=>ancestry n (next_u op u) (next_w op w) ++ [(u,w)] end.
Definition target := @Cfg Aff (ancestry 7 U W)
  (F 3587226 4782969 0 0 0) (F 0 0 16384 0 0)
  (F 36295979 48438324 0 0 196608)
  [(F 460012441 613437300 0 0 393216,constant 0)].
(* This calculation checks the whole parameter region, not a concrete run. *)
Example seven_exec: execute op 64 seven start=Some target.
Proof. vm_compute; reflexivity. Qed.

Definition next_b := F 6049329 8073054 0 0 32768.
Definition next_t := F 76668740 102239550 0 0 65536.
Definition region u w b t :=
  let q:=add (constant 3) (mul 6 u) in let v:=mul 6 w in
  let b:=add (constant 5) (mul 6 b) in let t:=add (constant 1) (mul 6 t) in
  guard (sub q (constant 70000)) && guard (mul 40 v) && guard (sub q (mul 40 v)) &&
  guard (sub (mul 2 b) (mul 3 q)) && guard (sub (mul 4 q) (mul 2 b)) &&
  guard (sub (mul 4 t) (mul 84 q)) && guard (sub (mul 87 q) (mul 4 t)).
Lemma region_spec e u w b t: good e -> region u w b t=true ->
  good (E (eval e u) (eval e w) (eval e b) (eval e t)).
Proof.
  intros G H; pose proof (laws e G) as L; unfold region in H.
  repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:guard ?x=true |- _=>apply (guard_spec e x G) in H end.
  repeat first [rewrite (value_lit L) in * | rewrite (value_plus L) in * |
    rewrite (value_minus L) in * | rewrite (value_scale L) in *].
  unfold good; cbn [eu ew eb et]; lia.
Qed.
Example region_result: region (current_u target) (current_w target) next_b next_t=true.
Proof. vm_compute; reflexivity. Qed.
Definition next_env e := E (eval e (current_u target)) (eval e (current_w target))
  (eval e next_b) (eval e next_t).
Theorem region_closed e: good e -> good (next_env e).
Proof. intros G; apply region_spec; [exact G|exact region_result]. Qed.
Example seed_region: good (E 12939 256 20511 273938).
Proof. unfold good; cbn; lia. Qed.

Definition seed e := point (eval e) start.
Definition frames e := mapped (eval e) (parents target).
Lemma target_local e:
  eval e (count target)=eval (next_env e) B /\
  eval e (fst (hd (constant 0,constant 0) (right target)))=eval (next_env e) T.
Proof.
  unfold next_env,target,next_b,next_t,B,T,eval;
    cbn [count right fst hd current_u current_w eu ew eb et ac au aw ab ah]; split; ring.
Qed.
Lemma target_point e: point (eval e) target=plug (frames e) (seed (next_env e)).
Proof.
  destruct (target_local e) as [Hb Ht].
  unfold seed,point,plug,frames,start; cbn [mapped map flatten parents current_u current_w count right
    root_u root_w number suffix Compute8.denote].
  unfold target in *; cbn [parents current_u current_w count right fst hd Compute8.denote] in *.
  rewrite Hb,Ht; f_equal; try reflexivity;
    f_equal; unfold next_env,target,eval,U,W,constant;
    cbn [current_u current_w eu ew eb et ac au aw ab ah]; ring.
Qed.
Lemma target_well e: well (eval e) target ->
  Well (frames e) (root_u (seed (next_env e))) (root_w (seed (next_env e))).
Proof.
  unfold well,frames,seed,point,start; cbn [mapped map flatten parents current_u current_w
    root_u root_w]; unfold next_env,target,eval,U,W;
    cbn [parents current_u current_w eu ew eb et ac au aw ab ah]; intros H.
  applys_eq H; f_equal; ring.
Qed.
Theorem seven_moves e: good e ->
  Well (frames e) (root_u (seed (next_env e))) (root_w (seed (next_env e))) /\
  Moves (seed e) (plug (frames e) (seed (next_env e))).
Proof.
  intros G.
  destruct (execute_progress op (eval e) (laws e G) 64 (tl seven) start target)
    as [W H]; [constructor|exact seven_exec|].
  split; [apply target_well; exact W|rewrite <-target_point; exact H].
Qed.
Theorem infinite_region e: good e -> Infinite (seed e).
Proof.
  intros G n; revert e G; induction n; intros e G.
  - exists (seed e); constructor.
  - destruct (seven_moves e G) as [W H].
    destruct (IHn (next_env e) (region_closed e G)) as [q K].
    exists (plug (frames e) q); eapply Link; [exact H|apply lift_chain; assumption].
Qed.
Theorem infinite_seed: Infinite (seed (E 12939 256 20511 273938)).
Proof. apply infinite_region, seed_region. Qed.
End Affine8.

(* The first layer and the positive physical progress behind abstract walks. *)
Import Rules8 Clock8 Columns8 Layers8 Program8 ListNotations.

Module Base8.
Inductive Two : nat->side->nat->side->Prop :=
| TwoIntro d a r s t: P 51 (Col 51 d r) s -> P (31+a) s t -> Two d r a t.
Definition cut d r := F (Col 51 d r).
Lemma two_realizes d r a t: Two d r a t -> cut d r -[tm]->+ cut a t.
Proof.
  intros H; destruct H as [d a r s t H K]; unfold cut.
  eapply progress_trans; [apply P_front,H|].
  eapply progress_trans; [apply Reset51|].
  eapply progress_trans; [apply P_front,First17,K|apply Close17].
Qed.
Lemma two_local x z r s: P (105+x) (Col (105+x) z r) s ->
  Two 74 (Col x (83+z) r) (74+x) s.
Proof.
  intros H; eapply TwoIntro with (s:=Col (105+x) z r).
  - applys_eq (MergeOne 24 26 x z r); flia.
  - applys_eq H; flia.
Qed.
Lemma two_fixed z r s: P 105 (Col 105 z r) s -> Two (157+z) r 74 s.
Proof.
  intros H; eapply TwoIntro with (s:=Col 105 z r).
  - exact (Counter 51 z r).
  - exact H.
Qed.
Lemma two_large z r: Two (476+z) r 74 (Col 213 z r).
Proof. applys_eq (two_fixed (319+z) r (Col 213 z r)); try flia; exact (Counter 105 z r). Qed.
Definition embed b r := Col 213 (447+b) r.
Lemma first_grow b r a t: Round 17 4 b r a t ->
  Walk Two 74 (embed b r) 74 (embed a t).
Proof.
  intros H; destruct H as [a b c r s v t H1 H2 H3]; unfold embed.
  eapply More with (a:=287) (s:=s).
  - applys_eq (two_local 213 (364+b) r s); try flia; exact H1.
  - eapply More with (a:=74) (s:=Col (849+a) (83+c) v).
    + apply (two_fixed 130 s); exact H2.
    + eapply More with (a:=923+a) (s:=t).
      * applys_eq (two_local (849+a) c v t); try flia; applys_eq H3; flia.
      * apply One; applys_eq (two_large (447+a) t); flia.
Qed.

Lemma walk_sound R f:
  (forall b r a s, R b r a s -> f b r -[tm]->+ f a s) ->
  forall b r a s, Walk R b r a s -> f b r -[tm]->+ f a s.
Proof. intros H b r a s K; induction K; eauto using progress_trans. Qed.
Definition base b r := cut 74 (embed b r).
Lemma base_realizes b r a s: Round 17 4 b r a s -> base b r -[tm]->+ base a s.
Proof. intros H; apply (walk_sound Two cut two_realizes),first_grow,H. Qed.

Lemma chain_sound u w f:
  (forall b r a s, Round u w b r a s -> f b r -[tm]->+ f a s) ->
  forall n p q, Chain n p q -> root_u p=u -> root_w p=w ->
  exists k, n<=k /\ f (number p) (suffix p) -[tm]->>k / f (number q) (suffix q).
Proof.
  intros R n p q H; induction H; intros Hu Hw.
  - exists O; split; [lia|constructor].
  - destruct H as [u0 w0 b0 s0 a0 s1 K]; cbn [root_u root_w number suffix] in *; subst u0 w0.
    destruct (progress_multistep _ _ _ (walk_sound _ _ R _ _ _ _ K)) as [k Hk].
    destruct (IHChain eq_refl eq_refl) as [j [Hj J]].
    exists (S k+j); split; [lia|eapply multistep_trans; eassumption].
Qed.
Theorem infinite_nonhalt b r: Infinite (Pt 17 4 b r) -> ~halts tm (base b r).
Proof.
  intros I [n Hn]; destruct (I (S n)) as [q K].
  destruct (chain_sound 17 4 base base_realizes _ _ _ K eq_refl eq_refl) as [j [Hj J]].
  eapply exceeds_halt with (n:=j); [exact Hn|lia|exact J].
Qed.
End Base8.

(* The finite entry uses the same returning-call evaluator as the symbolic
   seven-layer proof. Only the outer two-call control is added here. *)
Import Rules8 Columns8 Compute8 Program8 Base8 ListNotations.

Module Entry8.
Local Open Scope Z_scope.
Local Notation "'nn' n" := (Z.to_nat n) (at level 10).
Definition den := denote (fun z:Z=>z).
Definition State := (Z * @Tape Z)%type.
Definition config (s:State) := cut (nn (fst s)) (den (snd s)).
Definition next (s:State) := match invoke concrete 64 51 (fst s) (snd s) with
  | None=>None
  | Some r=>match send concrete (run concrete 64) r with
    | Some (u,t)=>if 31<=?u then Some (u-31,t) else None | None=>None end end.
Fixpoint advance n s := match n with
  | O=>Some s | S n=>match next s with Some t=>advance n t | None=>None end end.
Lemma next_spec s t: next s=Some t -> config s -[tm]->+ config t.
Proof.
  destruct s as [b r]; unfold next; cbn [fst snd].
  destruct (invoke concrete 64 51 b r) as [v|] eqn:E; try discriminate.
  destruct (send concrete (run concrete 64) v) as [[u w]|] eqn:K; try discriminate.
  destruct (31<=?u) eqn:G; try discriminate.
  intros H; injection H as H; subst t; apply Z.leb_le in G.
  apply (invoke_spec concrete (fun z:Z=>z) concrete_laws) in E.
  apply (call_spec concrete (fun z:Z=>z) concrete_laws) in K.
  unfold config,den; cbn [fst snd]; apply two_realizes.
  eapply TwoIntro; [exact E|applys_eq K; flia].
Qed.
Lemma advance_spec n s t: advance n s=Some t -> config s -[tm]->* config t.
Proof.
  revert s t; induction n; intros s t; cbn [advance].
  - intros H; injection H as H; subst t; apply evstep_refl.
  - destruct (next s) as [v|] eqn:E; try discriminate.
    intros H; eapply evstep_trans; [apply progress_evstep,next_spec,E|apply IHn,H].
Qed.
Definition start:State := (74,[(210,427);(1241,0)]).
Definition target:State := (74,[(213,450);(1917,3930);(17253,34890);
  (155277,435158);(1643629,0)]).
Example entry_exec: advance 296 start=Some target.
Proof. vm_compute; reflexivity. Qed.

Definition outer := [(1437%nat,64%nat);(159%nat,16%nat);(17%nat,4%nat)].
Definition environment := Affine8.E 12939 256 20511 273938.
Definition endpoint := plug outer (Affine8.seed environment).
Lemma endpoint_infinite: Infinite endpoint.
Proof.
  apply infinite_lift; [|exact Affine8.infinite_seed].
  change (Well outer 12939 256); unfold outer.
  apply (Wcons _ 1437 64); [lia|].
  apply (Wcons _ 159 16); [lia|].
  apply (Wcons _ 17 4); [lia|constructor].
Qed.
Local Opaque Z.to_nat Col.
Lemma target_config: config target=base (number endpoint) (suffix endpoint).
Proof.
  unfold config,target,base,cut,embed,endpoint,plug,outer,Affine8.seed,environment,
    point,Affine8.start,Affine8.eval,Affine8.U,Affine8.W,Affine8.B,Affine8.T,Affine8.constant.
  cbn [fst snd parents current_u current_w count right mapped map flatten
    root_u root_w number suffix Affine8.eu Affine8.ew Affine8.eb Affine8.et
    Affine8.ac Affine8.au Affine8.aw Affine8.ab Affine8.ah den denote].
  unfold Layers8.Embed; apply (f_equal Clock8.F).
  repeat first [apply (f_equal3 Col) | solve [flia] | reflexivity].
Qed.
Theorem target_nonhalt: ~halts tm (config target).
Proof.
  rewrite target_config; apply infinite_nonhalt.
  change (Infinite endpoint); exact endpoint_infinite.
Qed.
Theorem start_nonhalt: ~halts tm (config start).
Proof. eapply multistep_nonhalt; [eapply advance_spec; exact entry_exec|apply target_nonhalt]. Qed.
End Entry8.

(* ft7 row 8: original state names, blank-tape entry, and the final theorem. *)
Import Columns8 Compute8 ListNotations.

(* The installed Bouncer_v3.vo has stale ES_v3 assumptions. Copy its small
   chunked evaluator here, proving only the forward implication needed below. *)
Module Chunk8.
Fixpoint multistep_c' tm n1 n2 n3 c := match n1 with
  | O=>multistep_c tm n3 c
  | S n1=>match multistep_c tm n2 c with
    | Some c=>multistep_c' tm n1 n2 n3 c | None=>None end end.
Lemma multistep_c'_spec tm n1 n2 n3 c c':
  multistep_c' tm n1 n2 n3 c=Some c' -> c -[tm]->* c'.
Proof.
  revert c c'; induction n1; intros c c'; cbn [multistep_c'].
  - intros H; apply multistep_c_spec in H; eapply without_counter; exact H.
  - destruct (multistep_c tm n2 c) as [d|] eqn:E; try discriminate.
    intros H; eapply evstep_trans; [|apply IHn1,H].
    apply multistep_c_spec in E; eapply without_counter; exact E.
Qed.
End Chunk8.
End FT7TM8.

Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3 BusyCoq.Eqb.
Import ZArith ZifyNat Lia String List.

Import FT7TM8.
Import Columns8 Compute8 ListNotations.

Definition clockseed := Clock8.C (Col 105 123 (Col 619 0 0inf)).
Lemma init: c0 -[tm]->* clockseed.
Proof.
  apply (Chunk8.multistep_c'_spec _ 1041 1040 471).
  vm_compute; simpl_tape; reflexivity.
Qed.
Lemma seed_start: clockseed -[tm]->+ Entry8.config Entry8.start.
Proof.
  unfold clockseed,Entry8.config,Entry8.start,Entry8.den,Base8.cut; cbn [fst snd denote].
  eapply progress_trans; [apply Clock8.P_front,Clock8.First17|apply Clock8.Close17].
  exact (call_spec concrete (fun z:Z=>z) concrete_laws _ _ _ _ seed_call).
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt; [apply progress_evstep,seed_start|apply Entry8.start_nonhalt].
Qed.
End TM8.

(* Shared definitions from FT7TM15.v. *)
Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_0RD---").

Module FT7TM15.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3 BusyCoq.Eqb.
Import ZArith ZifyNat Lia String List.

(* ft7.txt row 15. Complete proof from the actual blank-tape start.
   Returning-call checker, guarded affine macros, two descents and ascents. *)

Module Rules15.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition S1 l a b c d r :=
  l <* [1]^^a <* [0] <{{BB62.A}} [1]*>[1;0]^^b*>[0]*>[1;0]^^c*>[0]^^d*>r.
Ltac run := unfold S1; ES_v2.es.
Ltac es5 a b c d e l r :=
  es_v3_pre; es_v3_nmp_smp
    (fun s=>if (s=?"a")%string then a else if (s=?"b")%string then b else
      if (s=?"c")%string then c else if (s=?"d")%string then d else
      if (s=?"e")%string then e else O)
    (fun s=>if (s=?"l")%string then l else if (s=?"r")%string then r else 0inf).
Lemma Inc l a b c d r:
  S1 l a (1+b) c (3+d) r -->* S1 l (1+a) b (2+c) d r.
Proof. run. Qed.
Lemma Incs n l a b c d r:
  S1 l a (n+b) c (n*3+d) r -->* S1 l (n+a) b (n*2+c) d r.
Proof. gen a b c d; ind n Inc. Qed.
Lemma Empty_b l a c d r:
  S1 l a 0 c (3+d) r -->* l <{{BB62.D}} [0]^^a*>[1;0]^^(3+c)*>[0]^^d*>r.
Proof. run. Qed.
Lemma Inc2 l a b c r:
  S1 l a (1+b) c 2 r -->* S1 l (1+a) b (1+c) 0 ([1]*>r).
Proof. run. Qed.
Definition P u r r' := forall l,
  l <* [0] <{{BB62.A}} [1]*>r -->* l <{{BB62.D}} [0]^^u*>r'.
Lemma Enter l a b c r:
  S1 l a (1+b) c 0 ([1]*>r) -->*
  l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <* [0] <{{BB62.A}} [1]*>r.
Proof. run. Qed.
Lemma Return l a b c d r:
  l <* [1]^^a <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <{{BB62.D}} [0]^^d*>r -->*
  S1 l a b c d r.
Proof. run. Qed.
Lemma Call l a b c u r r':
  P u r r' -> S1 l a (1+b) c 0 ([1]*>r) -->* S1 l (1+a) b c u r'.
Proof. intros H; follow Enter; follow H; follow Return; finish. Qed.
Lemma D1_merge l a b c y d r:
  S1 l a (1+b) c 1 ([1;0]^^(y*2)*>[0]^^(2+d)*>r) -->*
  S1 l (1+a) b (c+y*2+2) d r.
Proof. run. Qed.
Lemma D1_empty l a c y d r:
  S1 l a 0 c 1 ([1;0]^^(y*2)*>[0]^^(2+d)*>r) -->*
  l <{{BB62.D}} [0]^^a*>[1;0]^^(c+y*2+3)*>[0]^^d*>r.
Proof. run. Qed.
Lemma Even_short l a b c y r:
  S1 l a (1+b) c 1 ([1;0]^^(y*2)*>[0]*>r) -->*
  S1 l (1+a) b (c+y*2+1) 0 ([1]*>r).
Proof. run. Qed.
Lemma Odd_enter l b r:
  l<*[0] <{{BB62.A}} [1]*>[1;0]^^(1+b)*>[1;1;0]*>r -->* S1 l 1 b 1 1 r.
Proof. run. Qed.
Lemma RunTail l a b c d:
  S1 l a b c d 0inf -->* l <{{BB62.D}} [0]^^(a+b)*>[1;0]^^(b*2+c+3)*>0inf.
Proof.
  mid (S1 l a (b+0) c (b*3+3) 0inf).
  - unfold S1; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; finish.
  - follow Incs; follow Empty_b; finish.
Qed.

Lemma Odd_start l a b c y d r:
  S1 l a b c 1 ([1;0]^^(1+y*2)*>[0]^^(6+d)*>r) -->*
  S1 (l<*[1]^^(1+a)<*[0]<*[1;0]^^b<*[0;1]^^(y*2+c)) 1 3 0 d r.
Proof. unfold S1; es5 a b c y d l r. Qed.
Lemma Odd_five l a b c y x d r:
  S1 l a b c 1 ([1;0]^^(1+y*2)*>[0]^^5*>[1;0]^^x*>[0]^^(1+d)*>r) -->*
  S1 (l<*[1]^^(1+a)<*[0]<*[1;0]^^b<*[0;1]^^(y*2+c)) 1 (3+x) 0 d r.
Proof. run. Qed.
Lemma Odd_short_start l a b c y r:
  S1 l a b c 1 ([1;0]^^(1+y*2)*>[0]*>r) -->*
  l<*[1]^^(1+a)<*[0]<*[1;0]^^b<*[0;1]^^(y*2+c)<*[0;0;1]<*[0] <{{BB62.A}} [1]*>r.
Proof. run. Qed.
Lemma Return100 l d r:
  l<*[0;0;1] <{{BB62.D}} [0]^^(4+d)*>r -->*
  l <{{BB62.D}} [0]*>[1;0]^^3*>[0]^^d*>r.
Proof. ES_v2.es. Qed.
Lemma Return_empty l a c d r:
  l<*[1]^^(1+a)<*[0]<*[0;1]^^c <{{BB62.D}} [0]^^d*>r -->*
  l <{{BB62.D}} [0]^^a*>[1;0]^^(1+c)*>[0]^^d*>r.
Proof. ES_v2.es. Qed.
Lemma Odd_call l a b c y d r v s:
  (forall l, S1 l 1 3 0 d r -->* l <{{BB62.D}} [0]^^v*>s) ->
  S1 l a (1+b) c 1 ([1;0]^^(1+y*2)*>[0]^^(6+d)*>r) -->*
  S1 l (1+a) b (c+y*2) v s.
Proof. intros H; follow Odd_start; follow H; follow Return; finish; flia. Qed.

Lemma Odd_tail l a b c y:
  S1 l a (1+b) c 1 ([1;0]^^(1+y*2)*>0inf) -->*
  S1 l (1+a) b (c+y*2) 4 ([1;0]^^9*>0inf).
Proof.
  applys_eq (Odd_call l a b c y 0 0inf 4 ([1;0]^^9*>0inf));
    repeat rewrite (lpow_all0 [0]) by solve_const0_eq; try flia.
  intros l0; applys_eq (RunTail l0 1 3 0 0); flia.
Qed.
Lemma TailStep l a b c:
  S1 l a (2+b) c 4 ([1;0]^^9*>0inf) -->*
  S1 l (2+a) b (10+c) 4 ([1;0]^^9*>0inf).
Proof. follow Inc; follow (Odd_tail l (1+a) b (2+c) 4); finish; flia. Qed.
Lemma TailSteps n l a b c:
  S1 l a (n*2+b) c 4 ([1;0]^^9*>0inf) -->*
  S1 l (n*2+a) b (n*10+c) 4 ([1;0]^^9*>0inf).
Proof. gen a b c; ind n TailStep. Qed.

End Rules15.

Module Clock15.
Import Rules15.
Definition Col x z r := [1;0]^^x*>[0]^^z*>r.
Definition F (r:side) := 0inf <{{BB62.D}} r.
Definition C r := F (Col 3 6 r).
Notation "c -+ c'" := (progress tm c c') (at level 40).

Lemma P_front u r s: P u r s -> F r -+ F ([0]^^u*>s).
Proof.
  intros H; unfold F.
  eapply progress_evstep_trans with (c':=0inf<*[0] <{{BB62.A}} [1]*>r).
  - es' &r.
  - apply H.
Qed.
Lemma First3 u r s:
  P (23+u) r s -> P 3 (Col 3 6 r) (Col 6 (20+u) s).
Proof.
  intros H l.
  change (S1 l 0 3 0 5 r -->* l <{{BB62.D}} [0]^^3*>Col 6 (20+u) s).
  follow Inc; follow Inc2; follow (Call l 2 0 3 (23+u) r s H);
    follow Empty_b; finish.
Qed.
Lemma Small l d r:
  S1 l 1 3 0 (14+d) r -->* l <{{BB62.D}} [0]^^4*>Col 9 (2+d) r.
Proof. follow (Incs 3 l 1 0 0 (5+d) r); follow Empty_b; finish. Qed.
Lemma Odd2 u r:
  P 2 ([1;0]^^2*>[1]*>Col 6 (20+u) r) (Col 8 1 (Col 9 (2+u) r)).
Proof.
  intros l; unfold Col; follow Odd_enter.
  follow (Odd_call l 1 0 1 2 (14+u) r 4 (Col 9 (2+u) r)
    (fun l=>Small l u r)); follow Empty_b; finish.
Qed.
Lemma Odd10 u r s:
  (forall l, S1 l 2 8 11 u r -->* l <{{BB62.D}} [0]^^10*>s) ->
  P 10 ([1;0]^^10*>[1]*>Col 9 (2+u) r) s.
Proof.
  intros H l; unfold Col; follow Odd_enter;
    follow (D1_merge l 1 8 1 4 u r); apply H.
Qed.
Lemma Zero3 r: F ([0]^^3*>r) -+ F ([1;0]^^2*>[1]*>r).
Proof. unfold F; es' &r. Qed.
Lemma Zero2 r: F ([0]^^2*>Col 8 1 r) -+ F ([1;0]^^10*>[1]*>r).
Proof. unfold F, Col; es' &r. Qed.
Lemma Zero10 r: F ([0]^^10*>r) -+ C r.
Proof. unfold C, F, Col; es' &r. Qed.
Lemma Cycle u r s t:
  P (23+u) r s ->
  (forall l, S1 l 2 8 11 u s -->* l <{{BB62.D}} [0]^^10*>t) ->
  C r -+ C t.
Proof.
  intros H K; unfold C.
  eapply progress_trans; [apply P_front, First3, H|].
  eapply progress_trans; [apply Zero3|].
  eapply progress_trans; [apply P_front, Odd2|].
  eapply progress_trans; [apply Zero2|].
  eapply progress_trans; [apply P_front, Odd10, K|].
  apply Zero10.
Qed.
End Clock15.

Import ListNotations Rules15 Clock15.

Module Compute15.
Definition Pad k r := [1;0]^^k*>r.
Lemma pad_col k x z r: Pad k (Col x z r)=Col (k+x) z r.
Proof. unfold Pad,Col; rewrite (lpow_add _ k x); simpl_tape; reflexivity. Qed.
Definition RunN b c d r s := forall l a k,
  S1 l a b (c+k) d r -->* l <{{BB62.D}} [0]^^(a+b)*>Pad k s.
Definition ResumeN b c u t s := forall l a k,
  l<*[1]^^(1+a)<*[0]<*[1;0]^^b<*[0;1]^^(c+k) <{{BB62.D}} [0]^^u*>t -->*
  l <{{BB62.D}} [0]^^(a+b)*>Pad k s.
Lemma run_base b c d r s: RunN b c d r s -> forall l a,
  S1 l a b c d r -->* l <{{BB62.D}} [0]^^(a+b)*>s.
Proof. intros H l a; applys_eq (H l a 0%nat); cbn [Pad]; flia. Qed.

Lemma RInc n b c d r s:
  RunN b (n*2+c) d r s -> RunN (n+b) c (n*3+d) r s.
Proof. intros H l a k; follow Incs; applys_eq (H l (n+a) k); flia. Qed.
Lemma RMerge b c x d r s:
  RunN b (c+x) d r s -> RunN b c 0 (Col x d r) s.
Proof.
  intros H l a k; mid (S1 l a b (c+k+x) d r).
  - unfold S1,Col; rewrite (lpow_add _ (c+k) x); simpl_tape; finish.
  - applys_eq (H l a k); flia.
Qed.
Lemma ROne b c y d r s:
  RunN b (c+y*2+2) d r s -> RunN (1+b) c 1 (Col (y*2) (2+d) r) s.
Proof. intros H l a k; unfold Col; follow D1_merge; applys_eq (H l (1+a) k); flia. Qed.
Lemma ROneEmpty c y d r:
  RunN 0 c 1 (Col (y*2) (2+d) r) (Col (c+y*2+3) d r).
Proof. intros l a k; rewrite pad_col; unfold Col; follow D1_empty; finish; flia. Qed.
Lemma RTail b c d: RunN b c d 0inf (Col (b*2+c+3) 0 0inf).
Proof. intros l a k; rewrite pad_col; follow RunTail; unfold Col; finish; flia. Qed.
Lemma ROneTail b c y z:
  RunN b c 1 (Col (y*2) z 0inf) (Col (b*2+c+y*2+3) 0 0inf).
Proof.
  intros l a k; rewrite pad_col; mid (S1 l a b (c+k) 1 (Col (y*2) 2 0inf)).
  unfold S1,Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; finish.
  destruct b as [|b]; unfold Col.
  - follow D1_empty; finish; flia.
  - follow D1_merge; follow RunTail; finish; flia.
Qed.
Lemma REmpty b c d r:
  RunN b c (b*3+(3+d)) r (Col (b*2+c+3) d r).
Proof. intros l a k; rewrite pad_col; follow (Incs b l a 0 (c+k) (3+d) r);
  follow Empty_b; unfold Col; finish; flia. Qed.
Lemma RCall b c u r t s:
  P u r t -> RunN b (c+1) u t s -> RunN (2+b) c 2 r s.
Proof.
  intros H K l a k; follow Inc2; follow (Call l (1+a) b (1+(c+k)) u r t H).
  applys_eq (K l (2+a) k); flia.
Qed.
Lemma RShort b c y u r t s:
  P u r t -> RunN b (c+y*2+1) u t s ->
  RunN (2+b) c 1 (Col (y*2) 1 r) s.
Proof.
  intros H K l a k; unfold Col; follow Even_short;
    follow (Call l (1+a) b (c+k+y*2+1) u r t H); applys_eq (K l (2+a) k); flia.
Qed.
Lemma PTail p z: P p (Col p z 0inf) (Col (p*2+3) 0 0inf).
Proof.
  intros l; unfold Col; mid (S1 l 0 p 0 0 0inf).
  unfold S1; cbn [lpow Str_app]; repeat rewrite (lpow_all0 [0]) by solve_const0_eq.
  rewrite <- (const_unfold _ 0); finish.
  follow RunTail; finish; flia.
Qed.
Lemma PHead b d r s: RunN b 0 d r s -> P b (Col b (1+d) r) s.
Proof. intros H l; exact (run_base _ _ _ _ _ H l 0%nat). Qed.

Lemma ResumeEmpty c u t: ResumeN 0 c u t (Col (c+1) u t).
Proof. intros l a k; rewrite pad_col; follow Return_empty; unfold Col; finish; flia. Qed.
Lemma ResumeMore b c u t s: RunN b c u t s -> ResumeN (1+b) c u t s.
Proof. intros H l a k; follow Return; applys_eq (H l (1+a) k); flia. Qed.
Lemma ROdd b c y d r t s:
  RunN 3 0 d r t -> ResumeN b (c+y*2) 4 t s ->
  RunN b c 1 (Col (1+y*2) (6+d) r) s.
Proof.
  intros H K l a k; unfold Col; follow Odd_start; follow (run_base _ _ _ _ _ H);
    applys_eq (K l a k); flia.
Qed.
Lemma ROddFive b c y x d r t s:
  RunN (3+x) 0 d r t -> ResumeN b (c+y*2) (4+x) t s ->
  RunN b c 1 (Col (1+y*2) 5 (Col x (1+d) r)) s.
Proof.
  intros H K l a k; unfold Col; follow Odd_five; follow (run_base _ _ _ _ _ H);
    applys_eq (K l a k); flia.
Qed.
Lemma ROddShort b c y u r t s:
  P (4+u) r t -> ResumeN b (c+y*2) 1 (Col 3 u t) s ->
  RunN b c 1 (Col (1+y*2) 1 r) s.
Proof.
  intros H K l a k; unfold Col; follow Odd_short_start; follow H; follow Return100;
    applys_eq (K l a k); unfold Col; flia.
Qed.
Lemma ROddTail b c y z s:
  ResumeN b (c+y*2) 4 (Col 9 0 0inf) s ->
  RunN b c 1 (Col (1+y*2) z 0inf) s.
Proof.
  intros H; applys_eq (ROdd b c y 0 0inf (Col 9 0 0inf) s).
  - unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
  - apply RTail.
  - exact H.
Qed.
Lemma RLoopEven k c z:
  RunN (k*2) c 4 (Col 9 z 0inf) (Col (k*10+c+3) 1 (Col 9 0 0inf)).
Proof.
  intros l a h; rewrite pad_col; unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq.
  follow (TailSteps k l a 0 (c+h)); follow Empty_b; finish; flia.
Qed.
Lemma RLoopOdd k c z:
  RunN (k*2+1) c 4 (Col 9 z 0inf) (Col (k*10+c+11) 4 (Col 9 0 0inf)).
Proof.
  intros l a h; unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq.
  follow (TailSteps k l a 1 (c+h)); follow Inc.
  applys_eq (ROddTail 0 (k*10+c+2) 4 0 _
    (ResumeEmpty (k*10+c+2+4*2) 4 (Col 9 0 0inf)) l (k*2+a+1) h); unfold Col; flia.
Qed.

Record Ops (A:Type) := OpsMake {
  lit:Z->A; plus:A->A->A; minus:A->A->A; scale:Z->A->A;
  third:A->A; half:A->A; ge0:A->bool; same:A->A->bool
}.
Arguments lit {A} _ _.
Arguments plus {A} _ _ _.
Arguments minus {A} _ _ _.
Arguments scale {A} _ _ _.
Arguments third {A} _ _.
Arguments half {A} _ _.
Arguments ge0 {A} _ _.
Arguments same {A} _ _ _.
Record Laws {A} (op:Ops A) (value:A->Z) : Prop := LawsMake {
  value_lit:forall z, value (lit op z)=z;
  value_plus:forall x y, value (plus op x y)=(value x+value y)%Z;
  value_minus:forall x y, value (minus op x y)=(value x-value y)%Z;
  value_scale:forall z x, value (scale op z x)=(z*value x)%Z;
  ge0_sound:forall x, ge0 op x=true -> (0<=value x)%Z;
  same_sound:forall x y, same op x y=true -> value x=value y
}.
Arguments value_lit {A op value} _ _.
Arguments value_plus {A op value} _ _ _.
Arguments value_minus {A op value} _ _ _.
Arguments value_scale {A op value} _ _ _.
Arguments ge0_sound {A op value} _ _ _.
Arguments same_sound {A op value} _ _ _ _.

Section Program.
Context {A:Type} (op:Ops A).
Local Notation "'K' n" := (lit op n) (at level 10).
Local Infix "+" := (plus op).
Local Infix "-" := (minus op).
Local Notation "n '*:' x" := (scale op n x) (at level 40).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition Tape := list (A*A).
Definition bump x z (r:Tape) := match r with
  | nil=>[(x,K 0)]
  | (y,d)::r=>if same op z (K 0) then (x+y,d)::r else (x,z)::(y,d)::r end.
Fixpoint valid (r:Tape) := match r with
  | nil=>true | (x,d)::r=>ge0 op x && ge0 op d && valid r end.
Definition send (core:A->A->A->Tape->option Tape) (r:Tape) : option (A*Tape) :=
  match r with
  | nil=>Some (K 0,bump (K 3) (K 0) nil)
  | (x,d)::nil=>if ge0 op x then Some (x,bump (2*:x+K 3) (K 0) nil) else None
  | (x,d)::r=>if ge0 op x && ge0 op (d-K 1) then
      match core x (K 0) (d-K 1) r with Some s=>Some (x,s) | None=>None end
      else None end.
Definition resume core b c u (t:Tape) :=
  if ge0 op b && ge0 op c && ge0 op u then
    if same op b (K 0) then Some ((c+K 1,u)::t)
    else if ge0 op (b-K 1) then core (b-K 1) c u t else None
  else None.
Definition even core b c y z (r:Tape) := match r with
  | nil=>Some (bump (2*:b+c+2*:y+K 3) (K 0) nil)
  | _=>if ge0 op (z-K 2) then
      if same op b (K 0) then Some (bump (c+2*:y+K 3) (z-K 2) r)
      else if ge0 op (b-K 1) then core (b-K 1) (c+2*:y+K 2) (z-K 2) r else None
    else if same op z (K 1) && ge0 op (b-K 2) then
      match send core r with
      | Some (u,t)=>core (b-K 2) (c+2*:y+K 1) u t | None=>None end
    else None end.
Definition odd core b c y z (r:Tape) := match r with
  | nil=>resume core b (c+2*:y) (K 4) [(K 9,K 0)]
  | _=>if ge0 op (z-K 6) then
      match core (K 3) (K 0) (z-K 6) r with
      | Some t=>resume core b (c+2*:y) (K 4) t | None=>None end
    else if same op z (K 1) then
      match send core r with
      | Some (u,t)=>if ge0 op (u-K 4)
        then resume core b (c+2*:y) (K 1) ((K 3,u-K 4)::t) else None
      | None=>None end
    else if same op z (K 5) then match r with
      | (x,w)::r'=>let d:=match r' with nil=>K 0 | _=>w-K 1 end in
        if ge0 op d then match core (K 3+x) (K 0) d r' with
        | Some t=>resume core b (c+2*:y) (K 4+x) t | None=>None end else None
      | nil=>None end
    else None end.
Definition one core b c x z r :=
  let y:=half op x in
  if ge0 op b && ge0 op c && ge0 op y && ge0 op z && valid r then
    if same op x (2*:y) then even core b c y z r
    else if same op x (K 1+2*:y) then odd core b c y z r else None
  else None.
Definition loop b c := let k:=half op b in
  if ge0 op k then
    if same op b (2*:k) then Some [(10*:k+c+K 3,K 1);(K 9,K 0)]
    else if same op b (2*:k+K 1) then Some [(10*:k+c+K 11,K 4);(K 9,K 0)]
    else None
  else None.
Definition normal core b c d x z r :=
  if ge0 op (d-(3*:b+K 3)) then
    Some (bump (2*:b+c+K 3) (d-(3*:b+K 3)) ((x,z)::r))
  else let i:=third op d in let e:=d-3*:i in
    if ge0 op i && ge0 op (b-i) then
      let b':=b-i in let c':=2*:i+c in
      if same op e (K 0) then core b' (c'+x) z r
      else if same op e (K 1) then one core b' c' x z r
      else if same op e (K 2) && ge0 op (b'-K 2) then
        match send core ((x,z)::r) with
        | Some (u,t)=>core (b'-K 2) (c'+K 1) u t | None=>None end
      else None
    else None.
Fixpoint run fuel b c d r : option Tape := match fuel with
  | O=>None
  | S fuel=>if ge0 op b && ge0 op c && ge0 op d && valid r then
      match r with
      | nil=>Some (bump (2*:b+c+K 3) (K 0) nil)
      | (x,z)::r'=>match r' with
          | nil=>if same op d (K 4) && same op x (K 9) then loop b c
            else normal (run fuel) b c d x z r'
          | _=>normal (run fuel) b c d x z r' end
      end else None end.
End Program.

Section Soundness.
Context {A:Type} (op:Ops A) (value:A->Z) (law:Laws op value).
Local Notation "'nn' x" := (Z.to_nat (value x)) (at level 10).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Fixpoint denote (r:@Tape A) := match r with
  | nil=>0inf | (x,z)::r=>Col (nn x) (nn z) (denote r) end.
Definition Run b c d r s := RunN (nn b) (nn c) (nn d) (denote r) (denote s).
Definition Sound core := forall b c d r s, core b c d r=Some s -> Run b c d r s.
Ltac vals := repeat first [rewrite (value_lit law) in * |
  rewrite (value_plus law) in * | rewrite (value_minus law) in * |
  rewrite (value_scale law) in *].
Ltac decode := repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:ge0 op ?x=true |- _=>apply (ge0_sound law x) in H
  | H:same op ?x ?y=true |- _=>apply (same_sound law x y) in H end; vals.
Lemma valid_spec r: valid op r=true ->
  Forall (fun xd=>(0<=value (fst xd) /\ 0<=value (snd xd))%Z) r.
Proof.
  induction r as [|[x d] r IH]; cbn [valid]; intros H; [constructor|].
  apply and_true_iff in H; destruct H as [H Hr].
  apply and_true_iff in H; destruct H as [Hx Hd].
  constructor; [cbn; split; eapply ge0_sound; eassumption|apply IH; exact Hr].
Qed.
Lemma bump_spec x z r: (0<=value x)%Z ->
  Forall (fun xd=>(0<=value (fst xd) /\ 0<=value (snd xd))%Z) r ->
  denote (bump op x z r)=Col (nn x) (nn z) (denote r).
Proof.
  intros Hx Hr; destruct r as [|[y d] r]; cbn [bump denote].
  - unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
  - destruct (same op z (lit op 0)) eqn:E; [|reflexivity].
    inversion Hr as [|p ps Hhd Htl]; subst; cbn in Hhd.
    apply (same_sound law) in E; vals.
    cbn [denote]; vals; unfold Col; rewrite E; cbn.
    rewrite Z2Nat.inj_add by lia.
    rewrite (lpow_add _ (nn x) (nn y)); simpl_tape; reflexivity.
Qed.
Lemma send_spec core r u s:
  Sound core -> send op core r=Some (u,s) -> P (nn u) (denote r) (denote s).
Proof.
  intros H; destruct r as [|[x d] r]; cbn [send].
  - intros E; injection E as Eu Es; subst u s; cbn [bump denote]; vals.
    applys_eq (PTail 0 0); unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
  - destruct r as [|[y e] r].
    + destruct (ge0 op x) eqn:Hx; try discriminate.
      intros E; injection E as Eu Es; subst u s; cbn [bump denote]; decode.
      applys_eq (PTail (nn x) (nn d)); f_equal; lia.
    + destruct (ge0 op x && ge0 op (minus op d (lit op 1))) eqn:E; try discriminate.
      destruct (core x (lit op 0) (minus op d (lit op 1)) ((y,e)::r)) as [t|] eqn:C; try discriminate.
      intros K; injection K as Eu Es; subst u s; apply H in C; unfold Run in C; decode.
      cbn [denote]; applys_eq (PHead _ _ _ _ C); vals; flia.
Qed.
Lemma resume_spec core b c u t s:
  Sound core -> resume op core b c u t=Some s ->
  ResumeN (nn b) (nn c) (nn u) (denote t) (denote s).
Proof.
  intros H; unfold resume.
  destruct (ge0 op b && ge0 op c && ge0 op u) eqn:OK; try discriminate.
  destruct (same op b (lit op 0)) eqn:E.
  - intros K; inversion K; subst; cbn [denote]; decode.
    applys_eq (ResumeEmpty (nn c) (nn u) (denote t)); flia.
  - destruct (ge0 op (minus op b (lit op 1))) eqn:Eb; try discriminate.
    intros K; apply H in K; unfold Run in K; decode.
    applys_eq (ResumeMore _ _ _ _ _ K); flia.
Qed.

Local Opaque bump.
Lemma even_spec core b c y z r s:
  Sound core -> (0<=value b)%Z -> (0<=value c)%Z -> (0<=value y)%Z ->
  (0<=value z)%Z -> Forall (fun xd=>(0<=value (fst xd) /\ 0<=value (snd xd))%Z) r ->
  even op core b c y z r=Some s ->
  RunN (nn b) (nn c) 1 (Col (nn y*2) (nn z) (denote r)) (denote s).
Proof.
  intros H Hb Hc Hy Hz Hr; destruct r as [|[x w] r]; cbn [even].
  - intros E; inversion E; subst; cbn [bump denote]; vals.
    applys_eq (ROneTail (nn b) (nn c) (nn y) (nn z)); flia.
  - destruct (ge0 op (minus op z (lit op 2))) eqn:Ez.
    + destruct (same op b (lit op 0)) eqn:Eb.
      * intros E; inversion E; subst; rewrite bump_spec; try assumption; vals; try lia; decode.
        applys_eq (ROneEmpty (nn c) (nn y) (Z.to_nat (value z-2)) (denote ((x,w)::r))); flia.
      * destruct (ge0 op (minus op b (lit op 1))) eqn:Eb1; try discriminate.
        intros E; apply H in E; unfold Run in E; decode.
        applys_eq (ROne (nn (minus op b (lit op 1))) (nn c) (nn y)
          (nn (minus op z (lit op 2))) (denote ((x,w)::r)) (denote s)); try (vals; flia).
        applys_eq E; vals; flia.
    + destruct (same op z (lit op 1) && ge0 op (minus op b (lit op 2))) eqn:Eshort; try discriminate.
      destruct (send op core ((x,w)::r)) as [[u t]|] eqn:C; try discriminate.
      intros E; apply H in E; apply (send_spec _ _ _ _ H) in C; unfold Run in E; decode.
      applys_eq (RShort (nn (minus op b (lit op 2))) (nn c) (nn y) (nn u)
        (denote ((x,w)::r)) (denote t) (denote s)); try (vals; flia).
      exact C. applys_eq E; vals; flia.
Qed.
Lemma odd_spec core b c y z r s:
  Sound core -> (0<=value b)%Z -> (0<=value c)%Z -> (0<=value y)%Z ->
  (0<=value z)%Z -> Forall (fun xd=>(0<=value (fst xd) /\ 0<=value (snd xd))%Z) r ->
  odd op core b c y z r=Some s ->
  RunN (nn b) (nn c) 1 (Col (1+nn y*2) (nn z) (denote r)) (denote s).
Proof.
  intros H Hb Hc Hy Hz Hr; destruct r as [|[x w] r]; cbn [odd].
  - intros K; apply (resume_spec _ _ _ _ _ _ H) in K; cbn [denote] in K; vals.
    apply ROddTail; applys_eq K; flia.
  - inversion Hr as [|p ps Hhd Htail]; subst; cbn in Hhd; destruct Hhd as [Hx Hw].
    destruct (ge0 op (minus op z (lit op 6))) eqn:Ez.
    + destruct (core (lit op 3) (lit op 0) (minus op z (lit op 6)) ((x,w)::r)) as [t|] eqn:C; try discriminate.
      intros K; apply H in C; apply (resume_spec _ _ _ _ _ _ H) in K; unfold Run in C; decode.
      applys_eq (ROdd (nn b) (nn c) (nn y) (Z.to_nat (value z-6))
        (denote ((x,w)::r)) (denote t) (denote s)); try flia.
      applys_eq C; flia. applys_eq K; flia.
    + destruct (same op z (lit op 1)) eqn:E1.
      * destruct (send op core ((x,w)::r)) as [[u t]|] eqn:C; try discriminate.
        destruct (ge0 op (minus op u (lit op 4))) eqn:Eu; try discriminate.
        intros K; apply (send_spec _ _ _ _ H) in C; apply (resume_spec _ _ _ _ _ _ H) in K;
          cbn [denote] in K; decode.
        applys_eq (ROddShort (nn b) (nn c) (nn y) (Z.to_nat (value u-4))
          (denote ((x,w)::r)) (denote t) (denote s)); try flia.
        applys_eq C; flia. applys_eq K; flia.
      * destruct (same op z (lit op 5)) eqn:E5; try discriminate.
        destruct r as [|[xx ww] r]; cbn.
        -- destruct (ge0 op (lit op 0)) eqn:E0; try discriminate.
           destruct (core (plus op (lit op 3) x) (lit op 0) (lit op 0) nil) as [t|] eqn:C; try discriminate.
           intros K; apply H in C; apply (resume_spec _ _ _ _ _ _ H) in K;
             unfold Run in C; cbn [denote] in *; decode.
           applys_eq (ROddFive (nn b) (nn c) (nn y) (nn x) 0 0inf (denote t) (denote s));
             try (unfold Col; rewrite E5; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity).
           applys_eq C; flia. applys_eq K; flia.
        -- destruct (ge0 op (minus op w (lit op 1))) eqn:Ew; try discriminate.
           destruct (core (plus op (lit op 3) x) (lit op 0) (minus op w (lit op 1)) ((xx,ww)::r)) as [t|] eqn:C;
             try discriminate.
           intros K; apply H in C; apply (resume_spec _ _ _ _ _ _ H) in K; unfold Run in C; decode.
           cbn [denote].
           applys_eq (ROddFive (nn b) (nn c) (nn y) (nn x) (Z.to_nat (value w-1))
             (denote ((xx,ww)::r)) (denote t) (denote s)).
           { assert (nn w=1+Z.to_nat (value w-1)) as Ew' by lia.
             rewrite E5,Ew'; reflexivity. }
           applys_eq C; flia. applys_eq K; flia.
Qed.

Lemma one_spec core b c x z r s:
  Sound core -> one op core b c x z r=Some s ->
  RunN (nn b) (nn c) 1 (Col (nn x) (nn z) (denote r)) (denote s).
Proof.
  intros H; unfold one; set (y:=half op x).
  destruct (ge0 op b && ge0 op c && ge0 op y && ge0 op z && valid op r) eqn:OK; try discriminate.
  apply and_true_iff in OK; destruct OK as [OK Hr]; apply valid_spec in Hr; decode.
  destruct (same op x (scale op 2 y)) eqn:Ex.
  - intros E; apply (even_spec _ _ _ _ _ _ _ H) in E; try assumption.
    decode; applys_eq E; flia.
  - destruct (same op x (plus op (lit op 1) (scale op 2 y))) eqn:Ey; try discriminate.
    intros E; apply (odd_spec _ _ _ _ _ _ _ H) in E; try assumption.
    decode; applys_eq E; flia.
Qed.
Lemma loop_spec b c z s: (0<=value c)%Z -> loop op b c=Some s ->
  RunN (nn b) (nn c) 4 (Col 9 (nn z) 0inf) (denote s).
Proof.
  intros Hc; unfold loop; set (k:=half op b).
  destruct (ge0 op k) eqn:Hk; try discriminate.
  destruct (same op b (scale op 2 k)) eqn:E0.
  - intros E; inversion E; subst; cbn [denote]; decode.
    applys_eq (RLoopEven (nn k) (nn c) (nn z)); flia.
  - destruct (same op b (plus op (scale op 2 k) (lit op 1))) eqn:E1; try discriminate.
    intros E; inversion E; subst; cbn [denote]; decode.
    applys_eq (RLoopOdd (nn k) (nn c) (nn z)); flia.
Qed.
Lemma normal_spec core b c d x z r s:
  Sound core -> (0<=value b)%Z -> (0<=value c)%Z -> (0<=value d)%Z ->
  (0<=value x)%Z -> (0<=value z)%Z ->
  Forall (fun xd=>(0<=value (fst xd) /\ 0<=value (snd xd))%Z) r ->
  normal op core b c d x z r=Some s -> Run b c d ((x,z)::r) s.
Proof.
  intros H Hb Hc Hd Hx Hz Hr; unfold normal.
  destruct (ge0 op (minus op d (plus op (scale op 3 b) (lit op 3)))) eqn:Ebig.
  - intros E; inversion E; subst; unfold Run; rewrite bump_spec;
      try (constructor; [cbn; auto|assumption]); vals; try lia; decode.
    applys_eq (REmpty (nn b) (nn c) (Z.to_nat (value d-(3*value b+3))) (denote ((x,z)::r))); flia.
  - set (i:=third op d).
    destruct (ge0 op i && ge0 op (minus op b i)) eqn:Ei; try discriminate.
    destruct (same op (minus op d (scale op 3 i)) (lit op 0)) eqn:E0.
    + intros E; apply H in E; unfold Run in *; decode.
      applys_eq (RInc (nn i) (nn (minus op b i)) (nn c) 0 (denote ((x,z)::r)) (denote s));
        try (vals; flia).
      cbn [denote]; apply RMerge; applys_eq E; vals; flia.
    + destruct (same op (minus op d (scale op 3 i)) (lit op 1)) eqn:E1.
      * intros E; apply (one_spec _ _ _ _ _ _ _ H) in E; unfold Run; decode.
        applys_eq (RInc (nn i) (nn (minus op b i)) (nn c) 1 (denote ((x,z)::r)) (denote s));
          try (vals; flia).
        cbn [denote]; applys_eq E; vals; flia.
      * destruct (same op (minus op d (scale op 3 i)) (lit op 2) &&
          ge0 op (minus op (minus op b i) (lit op 2))) eqn:E2; try discriminate.
        destruct (send op core ((x,z)::r)) as [[u t]|] eqn:C; try discriminate.
        intros E; apply H in E; apply (send_spec _ _ _ _ H) in C; unfold Run in *; decode.
        applys_eq (RInc (nn i) (2+nn (minus op (minus op b i) (lit op 2))) (nn c) 2
          (denote ((x,z)::r)) (denote s)); try (vals; flia).
        eapply RCall; [exact C|]; applys_eq E; vals; flia.
Qed.
Theorem run_spec fuel: Sound (run op fuel).
Proof.
  induction fuel as [|fuel IH]; intros b c d r s; cbn [run]; [discriminate|].
  destruct (ge0 op b && ge0 op c && ge0 op d && valid op r) eqn:OK; try discriminate.
  apply and_true_iff in OK; destruct OK as [OK Hr]; apply valid_spec in Hr; decode.
  destruct r as [|[x z] r].
  - intros E; inversion E; subst; unfold Run; cbn [bump denote]; vals.
    applys_eq (RTail (nn b) (nn c) (nn d)); flia.
  - inversion Hr as [|p ps Hhd Htail]; subst; cbn in Hhd; destruct Hhd as [Hx Hz].
    destruct r as [|[y w] r].
    + destruct (same op d (lit op 4) && same op x (lit op 9)) eqn:Eloop.
      * intros E; apply (loop_spec _ _ z _) in E; try assumption.
        unfold Run; cbn [denote]; decode; applys_eq E; flia.
      * apply normal_spec; assumption.
    + apply normal_spec; assumption.
Qed.
Corollary call_spec fuel r u s:
  send op (run op fuel) r=Some (u,s) -> P (nn u) (denote r) (denote s).
Proof. apply send_spec, run_spec. Qed.
End Soundness.

Definition concrete := @OpsMake Z (fun z=>z) Z.add Z.sub Z.mul
  (fun z=>(z/3)%Z) (fun z=>(z/2)%Z) (Z.leb 0) Z.eqb.
Lemma concrete_laws: Laws concrete (fun z=>z).
Proof.
  constructor; cbn; intros; try reflexivity.
  - apply Z.leb_le; assumption.
  - apply Z.eqb_eq; assumption.
Qed.

End Compute15.

Import ListNotations Rules15 Clock15 Compute15.

Module Program15.
Section Definitions.
Context {A:Type} (op:Ops A).
Local Notation "'K' z" := (lit op z) (at level 10).
Local Infix "+" := (plus op).
Local Infix "-" := (minus op).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition clock fuel r := match send op (run op fuel) r with
  | Some (u,s)=>if ge0 op (u-K 23) then run op fuel (K 8) (K 11) (u-K 23) s else None
  | None=>None end.
Fixpoint clocks fuel n r := match n with
  | O=>Some r | S n=>match clock fuel r with
    | Some s=>clocks fuel n s | None=>None end end.
Definition start b (r:@Tape A) := (K 108,K 4)::(K 9,K 120)::(K 684,K 1416+b)::r.
Definition finish_root (r:@Tape A) := match r with
  | (x,d)::(y,e)::(z,f)::r=>
    if same op x (K 108) && same op d (K 4) && same op y (K 9) &&
      same op e (K 120) && same op z (K 684) && ge0 op (f-K 1416)
    then Some (f-K 1416,r) else None
  | _=>None end.
Definition root_step fuel b r := if ge0 op b then
  match clocks fuel 16 (start b r) with Some s=>finish_root s | None=>None end
  else None.
End Definitions.

Section Soundness.
Context {A:Type} (op:Ops A) (value:A->Z) (law:Laws op value).
Local Notation "'nn' x" := (Z.to_nat (value x)) (at level 10).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Ltac vals := repeat first [rewrite (value_lit law) in * |
  rewrite (value_plus law) in * | rewrite (value_minus law) in * |
  rewrite (value_scale law) in *].
Ltac decode := repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:ge0 op ?x=true |- _=>apply (ge0_sound law x) in H
  | H:same op ?x ?y=true |- _=>apply (same_sound law x y) in H end; vals.
Lemma clock_spec fuel r t:
  clock op fuel r=Some t -> C (denote value r) -[tm]->+ C (denote value t).
Proof.
  unfold clock; destruct (send op (run op fuel) r) as [[u s]|] eqn:H; try discriminate.
  destruct (ge0 op (minus op u (lit op 23))) eqn:Hu; try discriminate.
  intros K; apply (call_spec op value law) in H; apply (run_spec op value law) in K;
    unfold Run in K; decode.
  eapply (Cycle (nn (minus op u (lit op 23))) _ (denote value s)).
  - applys_eq H; vals; flia.
  - intros l; applys_eq (run_base _ _ _ _ _ K l 2); vals; flia.
Qed.
Lemma clocks_spec fuel n r s:
  clocks op fuel n r=Some s -> C (denote value r) -->* C (denote value s).
Proof.
  revert r s; induction n as [|n IH]; intros r s; cbn [clocks].
  - intros H; injection H as H; subst; finish.
  - destruct (clock op fuel r) as [t|] eqn:H; try discriminate.
    intros K; apply IH in K; apply clock_spec in H.
    eapply evstep_trans; [apply progress_evstep,H|exact K].
Qed.
Lemma clocks_progress fuel n r s:
  clocks op fuel (1+n) r=Some s -> C (denote value r) -[tm]->+ C (denote value s).
Proof.
  cbn [clocks Nat.add]; destruct (clock op fuel r) as [t|] eqn:H; try discriminate.
  intros K; apply clocks_spec in K; apply clock_spec in H;
    eapply progress_evstep_trans; eassumption.
Qed.
Definition Root b r := C (Col 108 4 (Col 9 120 (Col 684 (1416+b) r))).
Lemma start_spec b r: (0<=value b)%Z -> C (denote value (start op b r))=Root (nn b) (denote value r).
Proof. intros H; unfold start,Root; cbn [denote]; vals; flia. Qed.
Lemma finish_root_spec r b s: finish_root op r=Some (b,s) ->
  (0<=value b)%Z /\ C (denote value r)=Root (nn b) (denote value s).
Proof.
  destruct r as [|[x d] [|[y e] [|[z f] r]]]; cbn [finish_root]; try discriminate.
  destruct (same op x (lit op 108) && same op d (lit op 4) && same op y (lit op 9) &&
    same op e (lit op 120) && same op z (lit op 684) && ge0 op (minus op f (lit op 1416))) eqn:H;
    try discriminate.
  intros K; injection K as Hb Hs; subst b s; decode; split; [lia|].
  unfold Root; cbn [denote]; vals; flia.
Qed.
Lemma root_step_spec fuel b r a s:
  root_step op fuel b r=Some (a,s) ->
  Root (nn b) (denote value r) -[tm]->+ Root (nn a) (denote value s).
Proof.
  unfold root_step; destruct (ge0 op b) eqn:Hb; try discriminate.
  destruct (clocks op fuel 16 (start op b r)) as [t|] eqn:H; try discriminate.
  intros K; apply finish_root_spec in K; destruct K as [_ K].
  apply (clocks_progress fuel 15) in H; decode; rewrite start_spec in H by assumption.
  rewrite K in H; exact H.
Qed.
End Soundness.

Example seed_cycle:
  clocks concrete 64 64 [(85%Z,0%Z)] =
    Some [(108%Z,4%Z);(9%Z,120%Z);(684%Z,1416%Z);(6156%Z,15080%Z);(60547%Z,0%Z)].
Proof. vm_compute; reflexivity. Qed.

Lemma init: c0 -->* C (Col 85 0 0inf).
Proof.
  eapply without_counter; apply (multistep_c_spec _ 12775).
  vm_compute; simpl_tape; reflexivity.
Qed.
Lemma seed_peak: c0 -->* Root 0 (Col 6156 15080 (Col 60547 0 0inf)).
Proof.
  eapply evstep_trans; [apply init|].
  applys_eq (clocks_spec concrete (fun z:Z=>z) concrete_laws _ _ _ _ seed_cycle);
    unfold Root; cbn [denote]; reflexivity.
Qed.
End Program15.

Import ListNotations Rules15 Clock15 Compute15.

Module Layers15.
Lemma MergeCounter i j c x z r:
  RunN (i+j) c (i*3) (Col x (j*3+3+z) r)
    (Col (x+(i+j)*2+c+3) z r).
Proof.
  applys_eq (RInc i j c 0 (Col x (j*3+3+z) r) (Col (x+(i+j)*2+c+3) z r)); try flia.
  apply RMerge; applys_eq (REmpty j (i*2+c+x) z r); flia.
Qed.
Inductive EvenHead : side->Prop :=
| even_head x z r: EvenHead (Col (x*2) z r).
Lemma even_head_spec x z r: Nat.Even x -> EvenHead (Col x z r).
Proof. intros [n H]; applys_eq (even_head n z r); flia. Qed.

(* q=3u+2, v=3w. The premises are complete returns, including a c-frame.
   Parity is only required at the two interfaces where the caller uses it. *)
Inductive Round u w : nat->side->nat->side->Prop :=
| RoundIntro a b c r s t v:
  EvenHead s -> Nat.Even a ->
  RunN (u*9+20) 11 (u*9+w*6+9+b) r s ->
  RunN (u*3+2) 11 ((u+w-3)*3) s
    (Col (u*24+72+a) ((u-w)*3+27+c) t) ->
  RunN (u*27+74+a) 11 c t v -> Round u w b r a v.
Lemma Round_merge u w x z r s: 4<=w -> w<=u -> Nat.Even x ->
  RunN (u*27+74+x) 11 z r s ->
  Round u w 0 (Col x (u*27-w*12+99+z) r) x s.
Proof.
  intros Hw Hu Hx H; eapply RoundIntro with (c:=z) (t:=r)
    (s:=Col (x+u*18+54) (u*9-w*6+45+z) r).
  - apply even_head_spec; destruct Hx as [n Hx]; exists (n+u*9+27); lia.
  - exact Hx.
  - applys_eq (MergeCounter (u*3+w*2+3) (u*6-w*2+17) 11 x
      (u*9-w*6+45+z) r); flia.
  - applys_eq (MergeCounter (u+w-3) (u*2-w+5) 11 (x+u*18+54)
      ((u-w)*3+27+z) r); flia.
  - exact H.
Qed.
Lemma Round_call u w z r s: 4<=w -> w<=u ->
  RunN (u*27+74) 11 z r s ->
  Round u w (u*27-w*12+99+z) r 0 s.
Proof.
  intros Hw Hu H; eapply RoundIntro with (c:=z) (t:=r)
    (s:=Col (u*18+54) (u*9-w*6+45+z) r).
  - applys_eq (even_head (u*9+27) (u*9-w*6+45+z) r); flia.
  - exists 0%nat; reflexivity.
  - applys_eq (REmpty (u*9+20) 11 (u*9-w*6+45+z) r); flia.
  - applys_eq (MergeCounter (u+w-3) (u*2-w+5) 11 (u*18+54)
      ((u-w)*3+27+z) r); flia.
  - applys_eq H; flia.
Qed.
Lemma Round_large u w z r: 4<=w -> w<=u ->
  Round u w (u*108-w*12+324+z) r 0 (Col (u*54+162) z r).
Proof.
  intros Hw Hu; applys_eq (Round_call u w ((u*27+74)*3+3+z) r
    (Col (u*54+162) z r)); try flia.
  applys_eq (REmpty (u*27+74) 11 z r); flia.
Qed.
Inductive Walk (R:nat->side->nat->side->Prop) : nat->side->nat->side->Prop :=
| One b r a s: R b r a s -> Walk R b r a s
| More b r a s c t: R b r a s -> Walk R a s c t -> Walk R b r c t.
Definition Embed u w b r := Col (u*54+162) (u*108+w*12+324+b) r.
Lemma Grow u w b r a v: 4<=w -> w<=u -> Round (u*9+24) (w*4) b r a v ->
  Walk (Round u w) 0 (Embed u w b r) 0 (Embed u w a v).
Proof.
  intros Hw Hu H; destruct H as [a b c r s t v Hs Ha H1 H2 H3]; unfold Embed.
  eapply More with (a:=u*54+162) (s:=s).
  - applys_eq (Round_merge u w (u*54+162)
      ((u*9+24)*9+(w*4)*6+9+b) r s); try flia.
    + exists (u*27+81); lia.
    + applys_eq H1; flia.
  - eapply More with (a:=0%nat)
      (s:=Col ((u*9+24)*24+72+a) ((u*9+24-w*4)*3+27+c) t).
    + applys_eq (Round_call u w ((u*9+24+w*4-3)*3) s
        (Col ((u*9+24)*24+72+a) ((u*9+24-w*4)*3+27+c) t)); try flia.
      applys_eq H2; flia.
    + eapply More with (a:=u*216+648+a) (s:=v).
      * applys_eq (Round_merge u w ((u*9+24)*24+72+a) c t v); try flia.
        -- destruct Ha as [n Ha]; exists ((u*9+24)*12+36+n); lia.
        -- applys_eq H3; flia.
      * apply One; applys_eq (Round_large u w (u*108+w*12+324+a) v); flia.
Qed.
End Layers15.

Module LayerProgram15.
Import Layers15.
Section Definitions.
Context {A:Type} (op:Ops A).
Local Notation "'K' n" := (lit op n) (at level 10).
Local Infix "+" := (plus op).
Local Infix "-" := (minus op).
Local Notation "n '*:' x" := (scale op n x) (at level 40).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition even_count x := ge0 op (half op x) && same op x (2*:half op x).
Definition even_head (r:@Tape A) := match r with
  | (x,z)::r=>even_count x | nil=>false end.
Definition middle u w (r:@Tape A) := match r with
  | (x,z)::r=>let a:=x-(24*:u+K 72) in
    let c:=match r with nil=>K 0 | _=>z-(3*:(u-w)+K 27) end in
    if ge0 op a && ge0 op c && even_count a then Some (a,c,r) else None
  | nil=>None end.
Definition step fuel u w b r :=
  if ge0 op (w-K 4) && ge0 op (u-w) && ge0 op b then
    match run op fuel (9*:u+K 20) (K 11) (9*:u+6*:w+K 9+b) r with
    | Some s=>if even_head s then
      match run op fuel (3*:u+K 2) (K 11) (3*:(u+w-K 3)) s with
      | Some t=>match middle u w t with
        | Some (a,c,v)=>match run op fuel (27*:u+K 74+a) (K 11) c v with
          | Some out=>Some (a,out) | None=>None end
        | None=>None end | None=>None end else None
    | None=>None end else None.
Definition twice fuel u w b r := match step fuel u w b r with
  | Some (a,s)=>step fuel u w a s | None=>None end.
End Definitions.
Section Soundness.
Context {A:Type} (op:Ops A) (value:A->Z) (law:Laws op value).
Local Notation "'nn' x" := (Z.to_nat (value x)) (at level 10).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Ltac vals := repeat first [rewrite (value_lit law) in * |
  rewrite (value_plus law) in * | rewrite (value_minus law) in * |
  rewrite (value_scale law) in *].
Ltac decode := repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:ge0 op ?x=true |- _=>apply (ge0_sound law x) in H
  | H:same op ?x ?y=true |- _=>apply (same_sound law x y) in H end; vals.
Lemma even_count_spec x: even_count op x=true -> Nat.Even (nn x).
Proof. unfold even_count; intros H; decode; exists (nn (half op x)); lia. Qed.
Lemma even_head_spec r: even_head op r=true -> EvenHead (denote value r).
Proof.
  destruct r as [|[x z] r]; cbn [even_head]; try discriminate.
  intros H; apply even_count_spec in H; apply Layers15.even_head_spec,H.
Qed.
Lemma middle_spec u w r a c t: (4<=value w<=value u)%Z ->
  middle op u w r=Some (a,c,t) ->
  (0<=value a /\ 0<=value c)%Z /\ Nat.Even (nn a) /\
  denote value r=Col (nn u*24+72+nn a) ((nn u-nn w)*3+27+nn c) (denote value t).
Proof.
  intros Hw; destruct r as [|[x z] r]; cbn [middle]; try discriminate.
  set (aa:=minus op x (plus op (scale op 24 u) (lit op 72))).
  set (cc:=match r with nil=>lit op 0 | _=>minus op z
    (plus op (scale op 3 (minus op u w)) (lit op 27)) end).
  destruct (ge0 op aa && ge0 op cc && even_count op aa) eqn:H; try discriminate.
  intros E; injection E as Ha Hc Ht; subst a c t.
  unfold even_count in H; decode.
  assert (Hpar:Nat.Even (nn aa)) by (exists (nn (half op aa)); lia).
  unfold aa,cc in *; destruct r as [|[y d] r]; vals;
    split; [lia| |lia|]; split; [exact Hpar| |exact Hpar|]; cbn [denote].
  - unfold Col; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; f_equal; f_equal; lia.
  - flia.
Qed.
Lemma step_spec fuel u w b r a s: step op fuel u w b r=Some (a,s) ->
  Round (nn u) (nn w) (nn b) (denote value r) (nn a) (denote value s).
Proof.
  unfold step.
  destruct (ge0 op (minus op w (lit op 4)) && ge0 op (minus op u w) && ge0 op b) eqn:K; try discriminate.
  destruct (run op fuel (plus op (scale op 9 u) (lit op 20)) (lit op 11)
    (plus op (plus op (plus op (scale op 9 u) (scale op 6 w)) (lit op 9)) b) r) as [v|] eqn:E1; try discriminate.
  destruct (even_head op v) eqn:Hv; try discriminate.
  destruct (run op fuel (plus op (scale op 3 u) (lit op 2)) (lit op 11)
    (scale op 3 (minus op (plus op u w) (lit op 3))) v) as [t|] eqn:E2; try discriminate.
  destruct (middle op u w t) as [[[aa c] tail]|] eqn:M; try discriminate.
  destruct (run op fuel (plus op (plus op (scale op 27 u) (lit op 74)) aa)
    (lit op 11) c tail) as [out|] eqn:E3; try discriminate.
  intros H; injection H as Ha Hs; subst aa out; decode.
  apply (run_spec op value law) in E1,E2,E3; unfold Run in E1,E2,E3.
  apply middle_spec in M; [destruct M as [[Ha Hc] [Hpar Mt]]|lia].
  eapply RoundIntro with (c:=nn c) (t:=denote value tail) (s:=denote value v).
  - apply even_head_spec,Hv.
  - exact Hpar.
  - applys_eq E1; vals; flia.
  - rewrite Mt in E2; applys_eq E2; vals; flia.
  - applys_eq E3; vals; flia.
Qed.
Lemma twice_spec fuel u w b r a s: twice op fuel u w b r=Some (a,s) ->
  Walk (Round (nn u) (nn w)) (nn b) (denote value r) (nn a) (denote value s).
Proof.
  unfold twice; destruct (step op fuel u w b r) as [[c t]|] eqn:E; try discriminate.
  intros H; eapply More; [apply (step_spec fuel),E|apply One,(step_spec fuel),H].
Qed.
End Soundness.
End LayerProgram15.

Import ListNotations Rules15 Clock15 Compute15 Program15.

Module Affine15.
Record Expr := E {e0:Z;e1:Z;e2:Z;e3:Z;e4:Z;e5:Z}.
Definition K z := E z 0 0 0 0 0.
Definition add x y := E (e0 x+e0 y) (e1 x+e1 y) (e2 x+e2 y)
  (e3 x+e3 y) (e4 x+e4 y) (e5 x+e5 y).
Definition sub x y := E (e0 x-e0 y) (e1 x-e1 y) (e2 x-e2 y)
  (e3 x-e3 y) (e4 x-e4 y) (e5 x-e5 y).
Definition mul z x := E (z*e0 x) (z*e1 x) (z*e2 x) (z*e3 x) (z*e4 x) (z*e5 x).
Definition divide z x := E (e0 x/z) (e1 x/z) (e2 x/z) (e3 x/z) (e4 x/z) (e5 x/z).
Local Notation "x && y" := (if x then y else false) : bool_scope.
Definition nonneg x := Z.leb 0 (e0 x) && Z.leb 0 (e1 x) && Z.leb 0 (e2 x) &&
  Z.leb 0 (e3 x) && Z.leb 0 (e4 x) && Z.leb 0 (e5 x).
Definition equal x y := Z.eqb (e0 x) (e0 y) && Z.eqb (e1 x) (e1 y) &&
  Z.eqb (e2 x) (e2 y) && Z.eqb (e3 x) (e3 y) && Z.eqb (e4 x) (e4 y) && Z.eqb (e5 x) (e5 y).
Definition ops := @OpsMake Expr K add sub mul (divide 3) (divide 2) nonneg equal.
Definition den u v w x y a := (e0 a+e1 a*u+e2 a*v+e3 a*w+e4 a*x+e5 a*y)%Z.
Ltac bools := repeat match goal with
  | H:(if _ then _ else false)=true |- _=>apply and_true_iff in H; destruct H
  | H:Z.leb _ _=true |- _=>apply Z.leb_le in H
  | H:Z.eqb _ _=true |- _=>apply Z.eqb_eq in H end.
Lemma laws u v w x y:
  (0<=u)%Z -> (0<=v)%Z -> (0<=w)%Z -> (0<=x)%Z -> (0<=y)%Z ->
  Laws ops (den u v w x y).
Proof.
  intros; constructor; intros; cbv [ops lit plus minus scale K add sub mul den e0 e1 e2 e3 e4 e5]; try ring.
  - cbv [ops ge0 nonneg e0 e1 e2 e3 e4 e5] in *; bools; nia.
  - cbv [ops same equal e0 e1 e2 e3 e4 e5] in *; bools; congruence.
Qed.

(* N=16b+32v+4+24w, b=1004+12u, v=192+12v'. The residual
   variables are nonnegative. This parametrizes the needed lattice region. *)
Definition normal_input := [(E 8025 96 192 12 0 0,E 17767 132 240 12 0 0);
  (E 48425 432 768 48 0 0,K 0)].
Definition normal_a := E 8010 96 192 12 0 0.
Definition normal_output := [(E 88919 780 1488 96 0 0,K 1);(K 9,K 0)].
Lemma normal_exec: root_step ops 64 (K 0) normal_input=Some (normal_a,normal_output).
Proof. vm_compute; reflexivity. Qed.

Definition marked_input := [(E 5 12 0 0 0 0,K 1);(K 9,K 0)].
Definition marked_a := E 2840 12 0 0 0 0.
Definition marked_output := [(E 11827 24 0 0 0 0,K 0)].
Lemma marked_exec: root_step ops 64 (K 0) marked_input=Some (marked_a,marked_output).
Proof. vm_compute; reflexivity. Qed.

Lemma normal_spec u v w: (0<=u)%Z -> (0<=v)%Z -> (0<=w)%Z ->
  Root 0 (denote (den u v w 0 0) normal_input) -[tm]->+
  Root (Z.to_nat (den u v w 0 0 normal_a)) (denote (den u v w 0 0) normal_output).
Proof.
  intros Hu Hv Hw.
  exact (root_step_spec ops (den u v w 0 0) (laws u v w 0 0 Hu Hv Hw (Z.le_refl 0) (Z.le_refl 0))
    _ _ _ _ _ normal_exec).
Qed.
Lemma marked_spec u: (0<=u)%Z ->
  Root 0 (denote (den u 0 0 0 0) marked_input) -[tm]->+
  Root (Z.to_nat (den u 0 0 0 0 marked_a)) (denote (den u 0 0 0 0) marked_output).
Proof.
  intros Hu.
  exact (root_step_spec ops (den u 0 0 0 0) (laws u 0 0 0 0 Hu
    (Z.le_refl 0) (Z.le_refl 0) (Z.le_refl 0) (Z.le_refl 0)) _ _ _ _ _ marked_exec).
Qed.
End Affine15.

Module LayerAffine15.
Import Affine15 Layers15.
(* q=203+12u+48v, v_layer=48+12v. This is the lattice q=11 mod 12,
   v_layer=0 mod 12, q>=4*v_layer, v_layer>=48. *)
Definition U := E 67 4 16 0 0 0.
Definition W := E 16 0 4 0 0 0.
Definition N := add (mul 54 U) (K 162).
Definition gap := add (mul 2 N) (mul 12 W).
Definition X := E 9 0 0 12 0 0.
Definition GapRest := E 7 0 0 0 12 0.
Definition T := E 5 0 0 0 0 12.
Definition normal_input := [(N,gap);(X,add (mul 4 N) GapRest);(T,K 0)].
Definition normal_output := [(add X (mul 4 N),add GapRest (mul 36 W));(T,K 0)].
Lemma normal_exec:
  LayerProgram15.twice ops 128 U W (K 0) normal_input=Some (K 0,normal_output).
Proof. vm_compute; reflexivity. Qed.
Definition marked_input := [(N,gap);(T,K 1);(K 9,K 0)].
Definition marked_output := [(sub (add T (mul 8 N)) (mul 36 W),K 1);(K 9,K 0)].
Lemma marked_exec:
  LayerProgram15.twice ops 128 U W (K 0) marked_input=Some (K 0,marked_output).
Proof. vm_compute; reflexivity. Qed.
Definition turn_input := [(N,sub gap (K 18));(add T (K 6),K 1);(K 9,K 0)].
Definition turn_output := [(add (sub (add T (mul 8 N)) (mul 36 W)) (K 24),K 1);(K 9,K 0)].
Lemma turn_exec:
  LayerProgram15.twice ops 128 U W (K 0) turn_input=Some (K 0,turn_output).
Proof. vm_compute; reflexivity. Qed.
Section Soundness.
Context (u v x z t: Z).
Hypothesis Hu:(0<=u)%Z.
Hypothesis Hv:(0<=v)%Z.
Hypothesis Hx:(0<=x)%Z.
Hypothesis Hz:(0<=z)%Z.
Hypothesis Ht:(0<=t)%Z.
Local Notation val := (den u v x z t).
Lemma normal_spec: Walk (Round (Z.to_nat (val U)) (Z.to_nat (val W)))
  0 (denote val normal_input) 0 (denote val normal_output).
Proof. exact (LayerProgram15.twice_spec ops val (laws u v x z t Hu Hv Hx Hz Ht)
  _ _ _ _ _ _ _ normal_exec). Qed.
Lemma marked_spec: Walk (Round (Z.to_nat (val U)) (Z.to_nat (val W)))
  0 (denote val marked_input) 0 (denote val marked_output).
Proof. exact (LayerProgram15.twice_spec ops val (laws u v x z t Hu Hv Hx Hz Ht)
  _ _ _ _ _ _ _ marked_exec). Qed.
Lemma turn_spec: Walk (Round (Z.to_nat (val U)) (Z.to_nat (val W)))
  0 (denote val turn_input) 0 (denote val turn_output).
Proof. exact (LayerProgram15.twice_spec ops val (laws u v x z t Hu Hv Hx Hz Ht)
  _ _ _ _ _ _ _ turn_exec). Qed.
End Soundness.
End LayerAffine15.

Module PeakAffine15.
Import Affine15 Layers15.
Local Notation "x && y" := (if x then y else false) : bool_scope.
(* The only extra comparison information is 192*b <= 11812+1944*u+6240*v.
   A negative b coefficient is eliminated against this upper bound. *)
Definition bound := E 11812 1944 6240 (-192) 0 0.
Definition guard a := if nonneg a then true else
  Z.leb (e3 a) 0 && nonneg (add (mul 192 a) (mul (e3 a) bound)).
Definition ops := @OpsMake Expr K add sub mul (divide 3) (divide 2) guard equal.
Lemma cone u v b a: (0<=u)%Z -> (0<=v)%Z -> (0<=b)%Z ->
  nonneg a=true -> (0<=den u v b 0 0 a)%Z.
Proof.
  intros Hu Hv Hb H; exact (ge0_sound (laws u v b 0 0 Hu Hv Hb
    (Z.le_refl 0) (Z.le_refl 0)) _ H).
Qed.
Lemma laws u v b: (0<=u)%Z -> (0<=v)%Z -> (0<=b)%Z ->
  (192*b<=11812+1944*u+6240*v)%Z -> Laws ops (den u v b 0 0).
Proof.
  intros Hu Hv Hb Hbound; constructor; intros;
    cbv [ops lit plus minus scale K add sub mul den e0 e1 e2 e3 e4 e5]; try ring.
  - unfold ops,ge0,guard in H; destruct (nonneg x) eqn:E.
    + apply cone; assumption.
    + apply and_true_iff in H; destruct H as [Hc H]; apply Z.leb_le in Hc.
      apply (cone u v b _ Hu Hv Hb) in H.
      cbv [den add mul bound e0 e1 e2 e3 e4 e5] in *; nia.
  - cbv [ops same equal e0 e1 e2 e3 e4 e5] in *; bools; congruence.
Qed.
Definition B := E 1004 0 0 12 0 0.
Definition T := sub (add (mul 2 B) (mul 9 LayerAffine15.N)) (K 9).
Definition input := [(LayerAffine15.N,add LayerAffine15.gap B);(T,K 0)].
Definition output := [(sub (mul 4 LayerAffine15.N) (K 3),
    add (sub (add T B) (mul 4 LayerAffine15.N)) (add (mul 36 LayerAffine15.W) (K 4)));
  (add (mul 2 T) (K 3),K 0)].
Lemma exec: LayerProgram15.twice ops 128 LayerAffine15.U LayerAffine15.W (K 0) input=
  Some (K 0,output).
Proof. vm_compute; reflexivity. Qed.
Lemma spec u v b: (0<=u)%Z -> (0<=v)%Z -> (0<=b)%Z ->
  (192*b<=11812+1944*u+6240*v)%Z ->
  Walk (Round (Z.to_nat (den u v b 0 0 LayerAffine15.U))
    (Z.to_nat (den u v b 0 0 LayerAffine15.W)))
    0 (denote (den u v b 0 0) input) 0 (denote (den u v b 0 0) output).
Proof.
  intros Hu Hv Hb Hbound; exact (LayerProgram15.twice_spec ops (den u v b 0 0)
    (laws u v b Hu Hv Hb Hbound) _ _ _ _ _ _ _ exec).
Qed.
End PeakAffine15.

Import ListNotations Rules15 Clock15 Compute15 Program15 Layers15.

Module Base15.
Lemma ROddPass b c y d r s:
  RunN b (c+y*2) 4 (Col 9 d r) s ->
  RunN (1+b) c 1 (Col (1+y*2) (18+d) r) s.
Proof.
  intros H; applys_eq (ROdd (1+b) c y (12+d) r (Col 9 d r) s); try flia.
  - applys_eq (REmpty 3 0 d r); flia.
  - apply ResumeMore,H.
Qed.
Lemma ROddEnd c y d r:
  RunN 0 c 1 (Col (1+y*2) (18+d) r) (Col (c+y*2+1) 4 (Col 9 d r)).
Proof.
  applys_eq (ROdd 0 c y (12+d) r (Col 9 d r) (Col (c+y*2+1) 4 (Col 9 d r))); try flia.
  - applys_eq (REmpty 3 0 d r); flia.
  - apply ResumeEmpty.
Qed.
Lemma RRightStep b c d r s:
  RunN b (c+10) 4 (Col 9 d r) s ->
  RunN (2+b) c 4 (Col 9 (18+d) r) s.
Proof.
  intros H; applys_eq (RInc 1 (1+b) c 1 (Col 9 (18+d) r) s); try flia.
  applys_eq (ROddPass b (2+c) 4 d r s); flia.
  applys_eq H; flia.
Qed.
Lemma RRightLoop n c d r:
  RunN (n*2+1) c 4 (Col 9 ((n+1)*18+d) r)
    (Col (c+n*10+11) 4 (Col 9 d r)).
Proof.
  revert c; induction n as [|n IH]; intros c.
  - applys_eq (RInc 1 0 c 1 (Col 9 (18+d) r) (Col (c+11) 4 (Col 9 d r))); try flia.
    applys_eq (ROddEnd (2+c) 4 d r); flia.
  - applys_eq (RRightStep (n*2+1) c ((n+1)*18+d) r
      (Col (c+(1+n)*10+11) 4 (Col 9 d r))); try flia.
    applys_eq (IH (c+10)); flia.
Qed.
Lemma Odd8 y z r:
  RunN 8 11 7 (Col (1+y*2) (72+z) r) (Col (46+y*2) 4 (Col 9 z r)).
Proof.
  applys_eq (RInc 2 6 11 1 (Col (1+y*2) (72+z) r) (Col (46+y*2) 4 (Col 9 z r))); try flia.
  applys_eq (ROddPass 5 15 y (54+z) r (Col (46+y*2) 4 (Col 9 z r))); try flia.
  applys_eq (RRightLoop 2 (15+y*2) z r); flia.
Qed.

Definition D p z r := C (Col (1+p) 4 (Col 9 z r)).
Lemma head_clock u z r s t:
  RunN (23+u) 0 z r s -> RunN 8 11 u s t ->
  C (Col (23+u) (1+z) r) -[tm]->+ C t.
Proof.
  intros H K; eapply Cycle; [apply PHead,H|].
  intros l; exact (run_base _ _ _ _ _ K l 2%nat).
Qed.
Lemma Dclock u z r s t:
  RunN (22+u) 11 z r s -> RunN 8 11 u s t ->
  D (22+u) z r -[tm]->+ C t.
Proof.
  intros H K; unfold D; applys_eq (head_clock u 3 (Col 9 z r) s t); try flia.
  - applys_eq (RInc 1 (22+u) 0 0 (Col 9 z r) s); try flia.
    apply RMerge; exact H.
  - exact K.
Qed.
Lemma After30 x z r:
  C (Col 30 58 (Col (x*2+228) (108+z) r)) -[tm]->+ D (x*2+335) z r.
Proof.
  unfold D; applys_eq (head_clock 7 57 (Col (x*2+228) (108+z) r)
    (Col (x*2+291) (72+z) r) (Col (1+(x*2+335)) 4 (Col 9 z r))); try flia.
  - applys_eq (RInc 19 11 0 0 (Col (x*2+228) (108+z) r)
      (Col (x*2+291) (72+z) r)); try flia.
    apply RMerge; applys_eq (REmpty 11 (38+(x*2+228)) (72+z) r); flia.
  - applys_eq (Odd8 (x+145) z r); flia.
Qed.
Lemma Dmerge x z r:
  D 107 120 (Col (x*2) (312+z) r) -[tm]->+ D (x*2+335) z r.
Proof.
  eapply progress_trans; [|apply After30].
  applys_eq (Dclock 85 120 (Col (x*2) (312+z) r)
    (Col (x*2+228) (108+z) r) (Col 30 58 (Col (x*2+228) (108+z) r))); try flia.
  - applys_eq (MergeCounter 40 67 11 (x*2) (108+z) r); flia.
  - applys_eq (REmpty 8 11 58 (Col (x*2+228) (108+z) r)); flia.
Qed.
Lemma Dfixed z r: D 107 (432+z) r -[tm]->+ D 335 z r.
Proof.
  eapply progress_trans; [|apply (After30 0 z r)].
  applys_eq (Dclock 85 (432+z) r (Col 228 (108+z) r) (Col 30 58 (Col 228 (108+z) r))); try flia.
  - applys_eq (REmpty 107 11 (108+z) r); flia.
  - applys_eq (REmpty 8 11 58 (Col 228 (108+z) r)); flia.
Qed.
Lemma Dreturn n z r s: RunN (215+n) 11 z r s ->
  D (215+n) z r -[tm]->+ D 107 n s.
Proof.
  intros H; eapply progress_trans with (c':=C (Col 30 (166+n) s)).
  - applys_eq (Dclock (193+n) z r s (Col 30 (166+n) s)); try flia.
    + applys_eq H; flia.
    + applys_eq (REmpty 8 11 (166+n) s); flia.
  - unfold D; applys_eq (head_clock 7 (165+n) s (Col 63 (72+n) s)
      (Col 108 4 (Col 9 n s))); try flia.
    + applys_eq (REmpty 30 0 (72+n) s); flia.
    + applys_eq (Odd8 31 n s); flia.
Qed.

Lemma root_realizes b r a v: Round 111 16 b r a v -> Root b r -[tm]->+ Root a v.
Proof.
  intros H; destruct H as [a b c r s t v Hs [x Ha] H1 H2 H3]; unfold Root.
  change (D 107 120 (Col 684 (1416+b) r) -[tm]->+ D 107 120 (Col 684 (1416+a) v)).
  eapply progress_trans; [applys_eq (Dmerge 342 (1104+b) r); flia|].
  eapply progress_trans; [apply (Dreturn 804); applys_eq H1; flia|].
  eapply progress_trans; [apply (Dfixed 372)|].
  eapply progress_trans; [apply (Dreturn 120); applys_eq H2; flia|].
  eapply progress_trans; [applys_eq (Dmerge (1368+x) c t); flia|].
  eapply progress_trans; [applys_eq (Dreturn (2856+a) c t v); try flia; applys_eq H3; flia|].
  eapply progress_trans; [applys_eq (Dfixed (2424+a) v); flia|].
  apply (Dreturn 120); applys_eq (REmpty 335 11 (1416+a) v); flia.
Qed.
Lemma walk_sound R f:
  (forall b r a s, R b r a s -> f b r -[tm]->+ f a s) ->
  forall b r a s, Walk R b r a s -> f b r -[tm]->+ f a s.
Proof. intros H b r a s K; induction K; eauto using progress_trans. Qed.
Fixpoint U n := match n with O=>111 | S n=>U n*9+24 end.
Fixpoint W n := match n with O=>16 | S n=>W n*4 end.
Fixpoint config n b r := match n with
  | O=>Root b r | S n=>config n 0%nat (Embed (U n) (W n) b r) end.
Lemma parameters n: 4<=W n /\ W n<=U n.
Proof. induction n as [|n [Hw Hu]]; cbn [U W]; split; lia. Qed.
Lemma layer_realizes n b r a s: Round (U n) (W n) b r a s ->
  config n b r -[tm]->+ config n a s.
Proof.
  revert b r a s; induction n as [|n IH]; intros b r a s H; cbn [config U W] in *.
  - apply root_realizes,H.
  - apply (walk_sound _ _ IH),Grow; try apply (proj1 (parameters n));
      try apply (proj2 (parameters n)); exact H.
Qed.
Lemma layer_walk n b r a s: Walk (Round (U n) (W n)) b r a s ->
  config n b r -[tm]->+ config n a s.
Proof. apply walk_sound,layer_realizes. Qed.
End Base15.

Import ListNotations Rules15 Clock15 Compute15 Program15 Layers15 Base15.

Module Loop15.
Local Open Scope Z_scope.
Local Notation nn := Z.to_nat.
Definition col x z r := Col (nn x) (nn z) r.
Definition E t := col t 0 0inf.
Definition M t := col t 1 (col 9 0 0inf).
Definition C n b r := config n (nn b) r.
Definition N n := Z.of_nat (U n)*54+162.
Definition V n := Z.of_nat (W n)*3.
Definition Sum n := Z.of_nat (U n)*27-2997.
Lemma numbers n:
  N (S n)=9*N n /\ V (S n)=4*V n /\
  Sum (S n)=Sum n+4*N n /\ N n=2*Sum n+6156.
Proof. unfold N,V,Sum; cbn [U W]; lia. Qed.
Lemma lattice n: exists u v:Z, 11<=u /\ 0<=v /\
  Z.of_nat (U n)=67+4*u+16*v /\ Z.of_nat (W n)=16+4*v.
Proof.
  induction n as [|n [u [v [Hu [Hv [EU EW]]]]]].
  - exists 11,0; cbn [U W]; repeat split; lia.
  - exists (92+9*u+20*v),(12+4*v); cbn [U W]; repeat split; lia.
Qed.
Lemma bounds n: 6156<=N n /\ 48<=V n /\ 12*V n<=N n /\
  0<=Sum n /\ N n mod 24=12 /\ V n mod 12=0.
Proof.
  destruct (lattice n) as [u [v [Hu [Hv [EU EW]]]]]; unfold N,V,Sum;
    rewrite EU,EW; repeat split; lia.
Qed.
Lemma large n z r: 0<=z ->
  C n (2*N n-4*V n+z) r -[tm]->+ C n 0 (col (N n) z r).
Proof.
  intros Hz; destruct (parameters n) as [Hw Hu]; unfold C,col.
  apply layer_realizes; applys_eq (Round_large (U n) (W n) (nn z) r);
    unfold N,V; flia.
Qed.
Lemma ascend n b r: 0<=b -> C n (4*N n+b) r -[tm]->+ C (S n) b r.
Proof.
  intros Hb; destruct (bounds n) as [HN [HV Hrest]].
  applys_eq (large n (2*N n+4*V n+b) r); try lia.
  all: unfold C,col; cbn [config]; unfold Embed,N,V; flia.
Qed.
Lemma ascending n b r: 0<=b -> C 0 (Sum n+b) r -->* C n b r.
Proof.
  revert b; induction n as [|n IH]; intros b Hb.
  - cbn [Sum U]; finish.
  - destruct (numbers n) as [HN [HV [HS HN0]]].
    destruct (bounds n) as [HNlo [HVlo Hrest]]; rewrite HS.
    mid (C n (4*N n+b) r).
    + applys_eq (IH (4*N n+b)); flia.
    + apply progress_evstep,ascend,Hb.
Qed.
Ltac affine := cbn [denote];
  cbv [LayerAffine15.U LayerAffine15.W LayerAffine15.N LayerAffine15.gap
    LayerAffine15.X LayerAffine15.GapRest LayerAffine15.T
    LayerAffine15.normal_input LayerAffine15.normal_output
    LayerAffine15.marked_input LayerAffine15.marked_output
    LayerAffine15.turn_input LayerAffine15.turn_output
    Affine15.den Affine15.K Affine15.add Affine15.sub Affine15.mul
    Affine15.e0 Affine15.e1 Affine15.e2 Affine15.e3 Affine15.e4 Affine15.e5];
  cbn [denote]; unfold E,M,col,Embed; unfold N,V in *; flia.
Lemma normal_one n x z t:
  9<=x -> x mod 12=9 -> 4*N n<=z -> z mod 12=7 -> 5<=t -> t mod 12=5 ->
  C (S n) 0 (col x z (E t)) -[tm]->+
  C n 0 (col (x+4*N n) (z-4*N n+12*V n) (E t)).
Proof.
  intros Hx Ex Hz Ez Ht Et; destruct (lattice n) as [u [v [Hu [Hv [EU EW]]]]].
  unfold C; cbn [config]; apply layer_walk.
  applys_eq (LayerAffine15.normal_spec u v ((x-9)/12) ((z-4*N n-7)/12) ((t-5)/12)).
  all: affine.
Qed.
Lemma marked_one n t: 5<=t -> t mod 12=5 ->
  C (S n) 0 (M t) -[tm]->+ C n 0 (M (t+8*N n-12*V n)).
Proof.
  intros Ht Et; destruct (lattice n) as [u [v [Hu [Hv [EU EW]]]]].
  unfold C; cbn [config]; apply layer_walk.
  applys_eq (LayerAffine15.marked_spec u v 0 0 ((t-5)/12)).
  all: affine.
Qed.
Lemma turn_one n t: 11<=t -> t mod 12=11 ->
  C n 0 (col (N n) (2*N n+4*V n-18) (M t)) -[tm]->+
  C n 0 (M (t+8*N n-12*V n+18)).
Proof.
  intros Ht Et; destruct (lattice n) as [u [v [Hu [Hv [EU EW]]]]].
  unfold C; apply layer_walk.
  applys_eq (LayerAffine15.turn_spec u v 0 0 ((t-11)/12)).
  all: affine.
Qed.
Lemma normal_descending n x z t:
  9<=x -> x mod 12=9 -> N n<=z -> z mod 12=7 -> 5<=t -> t mod 12=5 ->
  C n 0 (col x z (E t)) -->*
  C 0 0 (col (x+Sum n) (z-Sum n+4*(V n-48)) (E t)).
Proof.
  revert x z t; induction n as [|n IH]; intros x z t Hx Ex Hz Ez Ht Et.
  - unfold Sum,V; cbn [U W]; finish; flia.
  - destruct (numbers n) as [HN [HV [HS HN0]]].
    destruct (bounds n) as [HNlo [HVlo [HNV [HSlo [EN EV]]]]].
    mid (C n 0 (col (x+4*N n) (z-4*N n+12*V n) (E t))).
    + apply progress_evstep,normal_one; lia.
    + applys_eq (IH (x+4*N n) (z-4*N n+12*V n) t); flia.
Qed.
Lemma marked_descending n t: 5<=t -> t mod 12=5 ->
  C n 0 (M t) -->* C 0 0 (M (t+N n-6156-4*(V n-48))).
Proof.
  revert t; induction n as [|n IH]; intros t Ht Et.
  - unfold N,V; cbn [U W]; finish; flia.
  - destruct (numbers n) as [HN [HV [HS HN0]]].
    destruct (bounds n) as [HNlo [HVlo [HNV [HSlo [EN EV]]]]].
    mid (C n 0 (M (t+8*N n-12*V n))).
    + apply progress_evstep,marked_one; lia.
    + applys_eq (IH (t+8*N n-12*V n)); flia.
Qed.
Lemma near_turn n t: 11<=t -> t mod 12=11 ->
  C 0 (Sum (S n)-18) (M t) -->*
  C 0 0 (M (t+N (S n)-6156-4*(V (S n)-48)+18)).
Proof.
  intros Ht Et; destruct (numbers n) as [HN [HV [HS HN0]]].
  destruct (bounds n) as [HNlo [HVlo [HNV [HSlo [EN EV]]]]].
  mid (C n (4*N n-18) (M t)).
  - applys_eq (ascending n (4*N n-18) (M t)); flia.
  - mid (C n 0 (col (N n) (2*N n+4*V n-18) (M t))).
    + apply progress_evstep; applys_eq (large n (2*N n+4*V n-18) (M t)); flia.
    + mid (C n 0 (M (t+8*N n-12*V n+18))).
      * apply progress_evstep,turn_one; lia.
      * applys_eq (marked_descending n (t+8*N n-12*V n+18)); flia.
Qed.
Lemma open_peak n b: 1000<=b -> b mod 12=8 -> 16*b+128*V n<=9*N n ->
  C (S n) b (E (2*b+N (S n)-9)) -[tm]->+
  C n 0 (col (4*N n-3) (3*b+5*N n+12*V n-5) (E (4*b+18*N n-15))).
Proof.
  intros Hb Eb Hbound; destruct (numbers n) as [HN Hrest].
  destruct (lattice n) as [u [v [Hu [Hv [EU EW]]]]].
  unfold C; cbn [config]; apply layer_walk.
  applys_eq (PeakAffine15.spec u v ((b-1004)/12)).
  all: cbv [PeakAffine15.input PeakAffine15.output PeakAffine15.B PeakAffine15.T];
    rewrite ?HN; affine.
Qed.
Ltac root_affine := cbn [denote];
  cbv [Affine15.normal_input Affine15.normal_output Affine15.normal_a
    Affine15.marked_input Affine15.marked_output Affine15.marked_a
    Affine15.den Affine15.K Affine15.e0 Affine15.e1 Affine15.e2
    Affine15.e3 Affine15.e4 Affine15.e5];
  cbn [denote]; unfold C,E,M,col; cbn [config]; unfold N,V,Sum in *; flia.
Lemma root_normal n b:
  1000<=b -> b mod 12=8 -> 192<=V n -> 16*b+32*V n<=N n ->
  C 0 0 (col (Sum n-3) (3*b+Sum n+4*V n+5959) (E (4*b+2*N n-15))) -[tm]->+
  C 0 (Sum n-18) (M (4*N n+b-4*V n-165)).
Proof.
  intros Hb Eb HV Hbound; destruct (bounds n) as [HNlo [HVlo [HNV [HS [EN EV]]]]].
  applys_eq (Affine15.normal_spec ((b-1004)/12) ((V n-192)/12)
    ((N n-16*b-32*V n-4)/24)).
  all: root_affine.
Qed.
Lemma root_marked t: 5<=t -> t mod 12=5 ->
  C 0 0 (M t) -[tm]->+ C 0 (t+2835) (E (2*t+11817)).
Proof.
  intros Ht Et; applys_eq (Affine15.marked_spec ((t-5)/12)).
  all: root_affine.
Qed.

Definition Peak n b := C (S n) b (E (2*b+N (S n)-9)).
Definition Good n b := 1000<=b /\ b mod 12=8 /\ 16*b+32*V (S n)<=N (S n).
Definition next n b := b+Sum (S n)-8*V (S n)+2880.
Lemma closed n b: Good n b -> Good (S n) (next n b).
Proof.
  intros [Hb [Eb Hbound]]; destruct (numbers (S n)) as [HN [HV [HS HN0]]].
  destruct (bounds (S n)) as [HNlo [HVlo [HNV [HSlo [EN EV]]]]].
  unfold Good,next; repeat split; lia.
Qed.
Lemma cycle n b: Good n b -> Peak n b -[tm]->+ Peak (S n) (next n b).
Proof.
  intros Hgood; destruct (closed n b Hgood) as [Hb' Hrest].
  destruct Hgood as [Hb [Eb Hbound]].
  destruct (numbers n) as [HN [HV [HS HN0]]].
  destruct (numbers (S n)) as [HN' [HV' [HS' HN0']]].
  destruct (bounds n) as [HNlo [HVlo [HNV [HSlo [EN EV]]]]].
  destruct (bounds (S n)) as [HNlo' [HVlo' [HNV' [HSlo' [EN' EV']]]]].
  unfold Peak; eapply progress_evstep_trans; [apply open_peak; lia|].
  mid (C 0 0 (col (Sum (S n)-3) (3*b+Sum (S n)+4*V (S n)+5959)
    (E (4*b+2*N (S n)-15)))).
  - applys_eq (normal_descending n (4*N n-3) (3*b+5*N n+12*V n-5)
      (4*b+18*N n-15)); flia.
  - mid (C 0 (Sum (S n)-18) (M (4*N (S n)+b-4*V (S n)-165))).
    + apply progress_evstep,root_normal; lia.
    + mid (C 0 0 (M (5*N (S n)+b-8*V (S n)-6111))).
      * applys_eq (near_turn n (4*N (S n)+b-4*V (S n)-165)); flia.
      * mid (C 0 (5*N (S n)+b-8*V (S n)-3276)
          (E (10*N (S n)+2*b-16*V (S n)-405))).
        -- apply progress_evstep; applys_eq (root_marked (5*N (S n)+b-8*V (S n)-6111)); flia.
        -- applys_eq (ascending (S (S n)) (next n b)
            (E (2*next n b+N (S (S n))-9))); unfold next in *; flia.
Qed.
Inductive Inv : state*tape->Prop :=
| InPeak n b: Good n b -> Inv (Peak n b).
Lemma inv_step c: Inv c -> exists c', Inv c' /\ c -[tm]->+ c'.
Proof.
  intros H; destruct H as [n b H]; exists (Peak (S n) (next n b)); split.
  - apply InPeak,closed,H.
  - apply cycle,H.
Qed.
Theorem region_nonhalt n b: Good n b -> ~halts tm (Peak n b).
Proof. intros H; eapply progress_nonhalt; [apply inv_step|apply InPeak,H]. Qed.
Lemma seed_good: Good 0 2576.
Proof. unfold Good,N,V; cbn [U W]; repeat split; lia. Qed.
Lemma seed_config: Peak 0 2576=Root 0 (Col 6156 15080 (Col 60547 0 0inf)).
Proof. unfold Peak,C,E,col; cbn [config U W]; unfold Embed,N; reflexivity. Qed.
Theorem initial_nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply seed_peak|].
  rewrite <-seed_config; apply region_nonhalt,seed_good.
Qed.
End Loop15.
End FT7TM15.

Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3 BusyCoq.Eqb.
Import ZArith ZifyNat Lia String List.

Import FT7TM15.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply Loop15.initial_nonhalt.
Qed.
End TM15.
