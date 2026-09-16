(* TM20 in its physical state names. These local rules are rechecked for
   this transition table, not assumed from TM13 despite identical shapes. *)
From BusyCoq Require Import Individual62 ES_v2 ES_v3.
Require Import ZifyNat Lia NArith String.

Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC0RA_0RD0RB_1LE0RF_1LB0LE_1LE---").
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
  S1 l a 0 c (3+d) r -->* l <{{E}} [0]^^a *> [1;0]^^(3+c) *> [0]^^d *> r.
Proof. run. Qed.
Lemma Inc2 l a b c r:
  S1 l a (1+b) c 2 r -->* S1 l (1+a) b (1+c) 0 ([1]*>r).
Proof. run. Qed.
Lemma Enter l a b c r:
  S1 l a (1+b) c 0 ([1]*>r) -->*
  l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <* [0] <{{B}} [1] *> r.
Proof. run. Qed.
Lemma Return l a b c d r:
  l <* [1]^^a <* [0] <* [1;0]^^(1+b) <* [0;1]^^c <{{E}} [0]^^d *> r -->*
  S1 l a b c d r.
Proof. run. Qed.
Definition P u r r' := forall l,
  l <* [0] <{{B}} [1] *> r -->* l <{{E}} [0]^^u *> r'.
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
  l <{{E}} [0]^^a *> [1;0]^^(1+c) *> [0;1;0;1;0;0] *> r.
Proof. run. Qed.
Definition LO := [0]^^6 ++ [1;0]^^6 ++ [0] ++ [1;0]^^2 ++ [0] ++ [1;0]^^37 ++ [0]^^120.
Definition LE := [0]^^6 ++ [1;0]^^5 ++ [0]^^3 ++ [1;0]^^11 ++ [0]^^13 ++ [1;0]^^109 ++ [0]^^300.
Definition K0 := 0inf <* [1]^^7 <* [1;0]^^5 <* <[1;1;0;0;1] <* [0;1]^^8
  <* [1]^^9 <* [0] <* [1;0]^^8 <* [0;1]^^92.
Definition K1 := 0inf <* [1]^^3 <* [0] <* [1;0]^^4 <* <[1;0;1;0;1;1;0;0;1;1;0;1;1;0]
  <* [1;0]^^12 <* [0;1]^^3 <* [1]^^75 <* [0] <* [1;0]^^88 <* [0;1]^^147.

Lemma Left0 r r':
  P 324 r r' -> 0inf <{{E}} LO *> r -[tm]->+ 0inf <{{E}} LE *> r'.
Proof.
  intros H; unfold LO, LE.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (K0 <* [0] <{{B}} [1] *> r).
  unfold K0; es' & r.
  follow H.
  unfold K0; es' & r'.
Qed.
Lemma Left1 d r r':
  P (264+d) r r' -> 0inf <{{E}} LE *> r -[tm]->+
  0inf <{{E}} LO *> [1;0]^^324 *> [0]^^d *> r'.
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
| IO d r: 1<=d -> d<324 -> Good 108 r -> Inv (0inf <{{E}} LO *> C 108 d r)
| IE d r: 1<=d -> d<648 -> Good 216 r -> Inv (0inf <{{E}} LE *> C 216 d r).
Lemma Inv_step c: Inv c -> exists c', Inv c' /\ c -[tm]->+ c'.
Proof.
  intros H; destruct H as [d r Hd Hd' HG|d r Hd Hd' HG];
    destruct (Good_step _ _ HG) as [u [r' [Hu [Hu' [HP Hr]]]]].
  - exists (0inf <{{E}} LE *> C 216 (u+d-324) r'); split.
    + apply IE; try lia; exact Hr.
    + apply Left0; unfold C; applys_eq (Column3 108 d u r r'); try assumption; flia.
  - exists (0inf <{{E}} LO *> C 108 128 (C 432 (u+d-648) r')); split.
    + apply IO; try lia. apply Good_cons; try lia; exact Hr.
    + apply (Left1 384); unfold C; applys_eq (Column3 216 d u r r'); try assumption; flia.
Qed.
Theorem region_nonhalt c: Inv c -> ~halts tm c.
Proof. eapply progress_nonhalt; apply Inv_step. Qed.

(* Keep every unary fuel small. The total count is never materialised. *)
Fixpoint chunks n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm n3 c
  | S n1 => match multistep_c tm n2 c with
            | Some c => chunks n1 n2 n3 c
            | None => None
            end
  end.
Lemma chunks_spec n1 n2 n3 c c': chunks n1 n2 n3 c = Some c' ->
  c -->* c'.
Proof.
  gen c; induction n1; intros c; cbn [chunks].
  - intros H; apply multistep_c_spec in H; eapply without_counter; exact H.
  - destruct (multistep_c tm n2 c) eqn:H; try discriminate.
    apply multistep_c_spec in H; intros H'.
    eapply evstep_trans; [eapply without_counter; exact H|apply IHn1; exact H'].
Qed.
Lemma init: c0 -->* 0inf <{{E}} LO *> C 108 114 (C 416 1101 (E 2399)).
Proof.
  apply (chunks_spec 12651 12652 6645).
  native_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply region_nonhalt, IO; try lia.
  apply Good_cons; try lia.
  apply Good_tail; lia.
Qed.
End TM20.
