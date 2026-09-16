From BusyCoq Require Import Individual62 ES_v2 ES_v3 Eqb.
Require Import ZifyNat Lia NArith String Bool.
From BusyCoq Require Import Individual62 ES_v2 ES_v3.
Require Import ZifyNat Lia NArith String.
From BusyCoq Require Import Individual62 Eqb.
Require Import NArith Lia ZifyNat Bool.
Require Import NArith Bool.
Require Import ZifyNat Lia NArith.
Require Import ZifyNat Lia NArith PeanoNat.
From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia NArith PeanoNat Bool.
Require Import NArith String.
Require Import String.

(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md. *)

Module FT7Compute.
Module Compute13.
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

Definition State := (Q * list Sym * Tape)%type.

Definition config (s:State) := let '(q,l,r) := s in (l *> 0inf) {{q}}> denote r.

Fixpoint strip (w:list Sym) r : option Tape :=
  match w with
  | nil => Some r
  | b::w => let '(a,s) := pop r in if sym_eqb a b then strip w s else None
  end.

Fixpoint tape_eqb r s : bool :=
  match r,s with
  | Blank,Blank => true
  | Zeros n r,Zeros m s | Pairs n r,Pairs m s => (n =? m) && tape_eqb r s
  | OneBit r,OneBit s => tape_eqb r s
  | _,_ => false
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

Fixpoint allzero (l:list Sym) : bool :=
  match l with nil => true | S0::l => allzero l | _ => false end.
End Compute13.
End FT7Compute.

Module FT7ComputeSpec.
Import FT7Compute.
Module ComputeSpec13.
Import Compute13.
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
Ltac unbool :=
  repeat match goal with
  | H: (if _ then _ else false) = true |- _ =>
      apply andb_true_iff in H; destruct H
  | H: N.eqb _ _ = true |- _ => apply N.eqb_eq in H
  | H: N.leb _ _ = true |- _ => apply N.leb_le in H
  | H: N.ltb _ _ = true |- _ => apply N.ltb_lt in H
  end.
End ComputeSpec13.
End FT7ComputeSpec.

(* Shared definitions from FT7TM17Rules.v. *)
Module TM17.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RE_0RD0RB_1LA1RE_1RB0LF_1LA---").

Module FT7TM17Rules.
(* Common region for TM16--19 in TM17 state names, followed by the final
   blank-tape theorem for TM19. TM17/TM18 finite entries are certified in
   the TM17/TM18 modules below; TM16 uses its separate formalized cycle. *)
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.

Module Rules17.
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
Lemma Empty2 l a c r:
  S1 l a 0 c 2 r -->* l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[1]*>r.
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
Lemma Empty0_call l a c u r r':
  P u r r' -> S1 l a 0 c 0 ([1]*>r) -->*
  l <{{A}} [0]^^a*>[1;0]^^(1+c)*>[0]^^u*>r'.
Proof.
  intros H; unfold S1.
  mid (l <* [1]^^a <* [0;1]^^(1+c) <* [0] <{{B}} [1]*>r).
  ES_v2.es. follow H; ES_v2.es.
Qed.

(* Transient d=1 behavior. These rules preserve the literal complete suffix;
   no restriction on how many short-gap columns follow is imposed. *)
Lemma D1_inc l a b c y z r:
  S1 l a (1+b) c 1 ([1;0]^^(1+y)*>[0]^^(3+z)*>r) -->*
  S1 l (1+a) b (1+c) 1 ([1;0]^^y*>[0;1;0;1]*>[0]^^z*>r).
Proof. run. Qed.
Lemma D1_empty l a c y z r:
  S1 l a 0 c 1 ([1;0]^^(1+y)*>[0]^^(3+z)*>r) -->*
  l <{{A}} [0]^^a *> [1;0]^^(2+c) *> [0] *> [1;0]^^y *>
    [0;1;0;1] *> [0]^^z *> r.
Proof. run. Qed.
Lemma D1_call l a b c y u r r':
  P u r r' -> S1 l a (1+b) c 1 ([1;0]^^(1+y)*>[0;1]*>r) -->*
  S1 l (1+a) b (1+c) 1 ([1;0]^^y*>[0]^^(1+u)*>r').
Proof.
  intros H; unfold S1.
  mid (l <* [1]^^(1+a) <* [0] <* [1;0]^^(1+b) <* [0;1]^^(1+c)
    <* [1;1] <* [1;0]^^y <* [0] <{{B}} [1]*>r).
  ES_v2.es. follow H; ES_v2.es.
Qed.
Lemma D1_empty_call l a c y u r r':
  P u r r' -> S1 l a 0 c 1 ([1;0]^^(1+y)*>[0;1]*>r) -->*
  l <{{A}} [0]^^a*>[1;0]^^(2+c)*>[0]*>[1;0]^^y*>[0]^^(1+u)*>r'.
Proof.
  intros H; unfold S1.
  mid (l <* [1]^^a <* [0;1]^^(2+c) <* [1;1] <* [1;0]^^y
    <* [0] <{{B}} [1]*>r).
  ES_v2.es. follow H; ES_v2.es.
Qed.
Lemma D1_shift l a b c y v z r:
  S1 l a (1+b) c 1 ([1;0]^^(1+y)*>[0]*>[1;0]^^(1+v)*>[0]^^(3+z)*>r) -->*
  S1 l (1+a) b (1+c) 1 ([1;0]^^y*>[0]*>[1;0]^^(3+v)*>[0]^^z*>r).
Proof. run. Qed.
Lemma D1_shifts n l a b c y v z r:
  S1 l a (n+b) c 1 ([1;0]^^(n+y)*>[0]*>[1;0]^^(1+v)*>[0]^^(n*3+z)*>r) -->*
  S1 l (n+a) b (n+c) 1 ([1;0]^^y*>[0]*>[1;0]^^(1+v+n*2)*>[0]^^z*>r).
Proof. gen a b c y v z; ind n D1_shift. Qed.
Lemma D1_shift4 l a b c y v w t z r:
  S1 l a (1+b) c 1 ([1;0]^^(1+y)*>[0]*>[1;0]^^(1+v)*>[0]*>
    [1;0]^^(1+w)*>[0]*>[1;0]^^(1+t)*>[0]^^(3+z)*>r) -->*
  S1 l (1+a) b (1+c) 1 ([1;0]^^y*>[0]*>[1;0]^^(2+v)*>[0]*>
    [1;0]^^w*>[0]*>[1;0]^^(3+t)*>[0]^^z*>r).
Proof. run. Qed.
Lemma D1_shifts4 n l a b c y v w t z r:
  S1 l a (n+b) c 1 ([1;0]^^(n+y)*>[0]*>[1;0]^^(1+v)*>[0]*>
    [1;0]^^(n+w)*>[0]*>[1;0]^^(1+t)*>[0]^^(n*3+z)*>r) -->*
  S1 l (n+a) b (n+c) 1 ([1;0]^^y*>[0]*>[1;0]^^(1+v+n)*>[0]*>
    [1;0]^^w*>[0]*>[1;0]^^(1+t+n*2)*>[0]^^z*>r).
Proof. gen a b c y v w t z; ind n D1_shift4. Qed.

(* n iterations remain, k have elapsed. Intermediate even-position columns
   gain k pairs, the last gains 2k, and all odd positions contain n+y pairs.
   The list length is unrestricted; the last zero run has length 3n+z. *)
Fixpoint D1Chain n k (xs:list (nat*nat)) c z r :=
  match xs with
  | [] => [1;0]^^(c+k*2)*>[0]^^(n*3+z)*>r
  | (y,v)::xs => [1;0]^^(c+k)*>[0]*>[1;0]^^(n+y)*>[0]*>
      D1Chain n k xs (1+v) z r
  end.
Lemma D1Chain_succ n k xs c z r:
  D1Chain n k xs (1+c) z r = [1;0]*>D1Chain n k xs c z r.
Proof. destruct xs as [|[y v] xs]; reflexivity. Qed.
Lemma D1Chain_step n k xs c z r:
  P 0 ([0]*>D1Chain (1+n) k xs c z r) (D1Chain n (1+k) xs (1+c) z r).
Proof.
  gen c; induction xs as [|[y v] xs IH]; intros c l; cbn [D1Chain].
  - applys_eq (Empty_b l 0 (c+k*2) (n*3+z) r); unfold S1; flia.
  - rewrite (D1Chain_succ (1+n) k xs v z r).
    applys_eq (D1_empty_call l 0 (c+k) (n+y) 0
      ([0]*>D1Chain (1+n) k xs v z r) (D1Chain n (1+k) xs (1+v) z r));
      try (unfold S1; flia).
    apply IH.
Qed.
Lemma D1Chain_inc n k xs l a b c y v z r:
  S1 l a (1+b) c 1 ([1;0]^^(1+n+y)*>[0]*>D1Chain (1+n) k xs (1+v) z r) -->*
  S1 l (1+a) b (1+c) 1 ([1;0]^^(n+y)*>[0]*>D1Chain n (1+k) xs (1+v) z r).
Proof.
  rewrite (D1Chain_succ (1+n) k xs v z r).
  applys_eq (D1_call l a b c (n+y) 0
    ([0]*>D1Chain (1+n) k xs v z r) (D1Chain n (1+k) xs (1+v) z r)); try flia.
  apply D1Chain_step.
Qed.
Lemma D1Chain_incs n k xs l a b c y v z r:
  S1 l a (n+b) c 1 ([1;0]^^(n+y)*>[0]*>D1Chain n k xs (1+v) z r) -->*
  S1 l (n+a) b (n+c) 1 ([1;0]^^y*>[0]*>D1Chain 0 (n+k) xs (1+v) z r).
Proof. gen k a b c; induction n; intros; [finish|].
  follow D1Chain_inc; follow IHn; finish.
Qed.

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

(* The parameter is one less than the physical (01)-counter: n=0
   must still contain one pair. The literal empty counter is not covered. *)
Definition LO n := [0] ++ [0;1]^^(1+n) ++ [0]^^55.
Definition LE n := [0] ++ [0;1]^^(1+n) ++ [0]^^19 ++ [1;0]^^36 ++ [0]^^66.
Definition K0 n := 0inf <* [1]^^3 <* [1;0]^^(11+n) <* [1]^^4 <* [0]
  <* [1;0]^^14 <* [0;1]^^7.
Definition K1 n := 0inf <* [1]^^3 <* [1;0]^^(11+n) <* [1]^^14 <* [0]
  <* [1;0]^^40 <* [0;1]^^27.
Lemma Left0 n r r':
  P 108 r r' -> 0inf <{{A}} LO n *> r -[tm]->+ 0inf <{{A}} LE (n+10) *> r'.
Proof.
  intros H; unfold LO, LE.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (K0 n <* [0] <{{B}} [1] *> r).
  unfold K0; es' n & r.
  follow H.
  unfold K0; es' n & r'.
Qed.
Lemma Left1 n d r r':
  P (120+d) r r' -> 0inf <{{A}} LE n *> r -[tm]->+
  0inf <{{A}} LO (n+10) *> [1;0]^^108 *> [0]^^d *> r'.
Proof.
  intros H; unfold LO, LE.
  eapply progress_intro; [prove_step|simpl_tape].
  mid (K1 n <* [0] <{{B}} [1] *> r).
  unfold K1; es' n & r.
  follow H.
  unfold K1; es' n d & r'.
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
| IO n d r: 1<=d -> d<108 -> Good 36 r -> Inv (0inf <{{A}} LO n *> C 36 d r)
| IE n d r: 1<=d -> d<216 -> Good 72 r -> Inv (0inf <{{A}} LE n *> C 72 d r).
Lemma Inv_step c: Inv c -> exists c', Inv c' /\ c -[tm]->+ c'.
Proof.
  intros H; destruct H as [n d r Hd Hd' HG|n d r Hd Hd' HG];
    destruct (Good_step _ _ HG) as [u [r' [Hu [Hu' [HP Hr]]]]].
  - exists (0inf <{{A}} LE (n+10) *> C 72 (u+d-108) r'); split.
    + apply IE; try lia; exact Hr.
    + apply Left0; unfold C; applys_eq (Column3 36 d u r r'); try assumption; flia.
  - exists (0inf <{{A}} LO (n+10) *> C 36 32 (C 144 (u+d-216) r')); split.
    + apply IO; try lia. apply Good_cons; try lia; exact Hr.
    + apply (Left1 n 96); unfold C; applys_eq (Column3 72 d u r r'); try assumption; flia.
Qed.
Theorem region_nonhalt c: Inv c -> ~halts tm c.
Proof. eapply progress_nonhalt; apply Inv_step. Qed.

(* Early TM17 checkpoint. FT7TM17ComputeSpec certifies the subsequent
   42 returning-call stages; FT7TM17.v connects them to region_nonhalt. *)
Fixpoint seed_chunks n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm n3 c
  | S n1 => match multistep_c tm n2 c with
            | Some c => seed_chunks n1 n2 n3 c
            | None => None
            end
  end.
Lemma seed_chunks_spec n1 n2 n3 c c':
  seed_chunks n1 n2 n3 c = Some c' -> c -->* c'.
Proof.
  gen c; induction n1; intros c; cbn [seed_chunks].
  - intros H; apply multistep_c_spec in H; eapply without_counter; exact H.
  - destruct (multistep_c tm n2 c) eqn:H; try discriminate.
    apply multistep_c_spec in H; intros H'.
    eapply evstep_trans; [eapply without_counter; exact H|apply IHn1; exact H'].
Qed.
Definition seed := 0inf <{{A}} LO 87 *> [1;0]^^108 *> [0]^^213 *> [1;0]^^2174 *> 0inf.
Lemma seed_init: c0 -->* seed.
Proof.
  apply (seed_chunks_spec 2995 2996 2064).
  native_compute; simpl_tape; reflexivity.
Qed.
End Rules17.
End FT7TM17Rules.

(* Shared definitions from FT7TM17Compute.v. *)
Module FT7TM17Compute.
(* A partial returning-call checker for the finite TM16--18 entries. Unmatched
   cases return None; all counters stay binary during computation. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat Bool.
Import FT7TM17Rules FT7Compute FT7ComputeSpec.

Module Compute17.
Import FT7TM17Rules.Rules17 Compute13.
Local Open Scope N_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.

Definition takezeros n r :=
  match r with
  | Blank => Some Blank
  | Zeros z s => if n <=? z then Some (zeros (z-n) s) else None
  | _ => None
  end.
(* The parser merely proposes a witness. Its reconstructed input is checked
   for exact equality, so no parser invariant enters the soundness proof. *)
Fixpoint chain_tape n k (xs:list (N*N)) c z r :=
  match xs with
  | nil => pairs (c+k*2) (zeros (n*3+z) r)
  | (y,v)::xs => pairs (c+k) (zeros 1 (pairs (n+y)
      (zeros 1 (chain_tape n k xs (1+v) z r))))
  end.
Record ChainWitness := Witness { cn:N; cy:N; cv:N; cxs:list (N*N); cz:N; cr:Tape }.
Definition chain_input w := let '(Witness n y v xs z r):=w in
  pairs (n+y) (zeros 1 (chain_tape n 0 xs (1+v) z r)).
Definition chain_output w := let '(Witness n y v xs z r):=w in
  pairs y (zeros 1 (chain_tape 0 n xs (1+v) z r)).
Definition check_batch b r w :=
  if (1 <=? cn w) && (cn w <=? b) && tape_eqb r (chain_input w) then
    Some (cn w,chain_output w)
  else None.
Fixpoint read_chain r : option (list N*N*Tape) :=
  match r with
  | Pairs x Blank => Some ([x],0,Blank)
  | Pairs x (Zeros z s) => if z =? 1 then
      match read_chain s with
      | Some (xs,z,t) => Some (x::xs,z,t)
      | None => None
      end
    else Some ([x],z,s)
  | _ => None
  end.
Fixpoint odd_min b xs := match xs with
  | x::_::xs => N.min x (odd_min b xs)
  | _ => b
  end.
Fixpoint relative_pairs n xs := match xs with
  | y::v::xs => (y-n,v-1)::relative_pairs n xs
  | _ => nil
  end.
Definition chain_witness b r :=
  match read_chain r with
  | Some (y::v::xs,z,s) =>
      let n := odd_min b (y::v::xs) in
      let n := match s with Blank=>n | _=>N.min n (z/3) end in
      Some (Witness n (y-n) (v-1) (relative_pairs n xs) (z-n*3) s)
  | _ => None
  end.
Definition batch b r := match chain_witness b r with
  | Some w => check_batch b r w
  | None => None
  end.

Definition send (f:N->N->N->Tape->option Tape) r : option (N*Tape) :=
  match r with
  | Blank => Some (0,Pairs 3 Blank)
  | Pairs x Blank => Some (x,Pairs (x*2+3) Blank)
  | Pairs x (Zeros d s) => if d =? 0 then None else
      match f x 0 (d-1) s with Some s' => Some (x,s') | None => None end
  | Zeros d s => if d =? 0 then None else
      match f 0 0 (d-1) s with Some s' => Some (0,s') | None => None end
  | _ => None
  end.
Definition onecall f r :=
  let '(b,s) := pop r in match b with S0=>None | BusyCoq.BB62.S1=>send f s end.
Definition d1next f r : option Tape :=
  match r with
  | Pairs y s => if 1 <=? y then
      match takezeros 3 s with
      | Some t => Some (pairs (y-1) (push S0 (push 1%sym (push S0 (push 1%sym t)))))
      | None => match s with
        | Zeros z t => if z =? 1 then
            match onecall f t with
            | Some (u,t) => Some (pairs (y-1) (zeros (1+u) t))
            | None => None
            end
          else None
        | _ => None
        end
      end
    else None
  | _ => None
  end.
Definition resume f (b c d:N) r : option Tape :=
  if (b =? 0) && (3 <=? d) then Some (pairs (c+3) (zeros (d-3) r)) else
  if d =? 0 then
    match r with
    | Pairs y s => f b (c+y) 0 s
    | Zeros z s => f b c z s
    | OneBit s => match send f s with
        | Some (u,t) => if b =? 0 then Some (pairs (c+1) (zeros u t))
                       else f (b-1) c u t
        | None => None
        end
    | Blank => Some (Pairs (b*2+c+3) Blank)
    end
  else if d =? 2 then
    if b =? 0 then Some (pairs (c+2) (push 1%sym r))
    else f (b-1) (c+1) 0 (push 1%sym r)
  else if d =? 1 then
    match batch b r with
    | Some (n,s) => f (b-n) (c+n) 1 s
    | None => match d1next f r with
      | Some s => if b =? 0 then Some (pairs (c+2) (zeros 1 s))
                  else f (b-1) (c+1) 1 s
      | None => None
      end
    end
  else None.
Fixpoint run fuel (b c d:N) r : option Tape :=
  match fuel with
  | O => None
  | S fuel => match r with
    | Blank => Some (Pairs (b*2+c+3) Blank)
    | Zeros z s => run fuel b c (d+z) s
    | _ => let n := N.min b (d/3) in
      if (n <=? b) && (n*3 <=? d) then
        resume (run fuel) (b-n) (c+n*2) (d-n*3) r
      else None
    end
  end.
Definition Stage := (N*bool*Tape)%type.
Definition stage_config (s:Stage) := let '(n,p,r):=s in
  0inf <{{A}} (if p then LE (N.to_nat n) else LO (N.to_nat n)) *> denote r.
Definition stage_step fuel (s:Stage) : option Stage :=
  let '(n,p,r) := s in match send (run fuel) r with
  | None => None
  | Some (u,r) => if p then
      if 120 <=? u then Some (n+10,false,pairs 108 (zeros (u-120) r)) else None
    else if u =? 108 then Some (n+10,true,r) else None
  end.
Definition regionb (s:Stage) : bool :=
  let '(n,p,r) := s in let x := if p then 72 else 36 in
  match r with
  | Pairs y (Zeros z s) => let d:=z/3 in
      (y =? x*3) && (z =? d*3) && (1 <=? d) && (d <? x*3) && goodb x s
  | _ => false
  end.
Fixpoint check_stages count fuel s : bool :=
  if regionb s then true else match count with
  | O => false
  | S count => match stage_step fuel s with
               | Some s => check_stages count fuel s
               | None => false
               end
  end.
Definition seed : Stage := (87,false,Pairs 108 (Zeros 213 (Pairs 2174 Blank))).

End Compute17.
End FT7TM17Compute.

(* Shared definitions from FT7TM16Compute.v. *)
Module FT7TM16Compute.
(* Finite entry checker. Arithmetic and tape lengths stay binary. *)
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Bool.
Import FT7TM17Rules FT7Compute FT7TM17Compute.

Module Compute16.
Import FT7TM17Rules.Rules17 Compute13 Compute17.
Local Open Scope N_scope.
Local Notation "a && b" := (if a then b else false) : bool_scope.

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
  let '(q,l,r) := s in match q,pop r with
  | B,(S0,r) => match pop r with
    | (BusyCoq.BB62.S1,r) => match send (run fuel) r with
      | Some (u,r) => match l with
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
Definition at_stage (s:State) (target:Stage) : bool :=
  let '(n,p,t) := target in match s with
  | (A,l,r) => if allzero l then
      match pop r with
      | (S0,r) => match strip (if p then LE (N.to_nat n) else LO (N.to_nat n)) r with
                  | Some r => tape_eqb r t
                  | None => false
                  end
      | _ => false
      end
    else false
  | _ => false
  end.
Fixpoint seek count fuel s target : bool :=
  if at_stage s target then true else match count with
  | O => false
  | S count => match machine_step fuel s with
               | Some s => seek count fuel s target
               | None => false
               end
  end.
Definition seed : Stage := (144,false,Pairs 108 (Zeros 2548 (Pairs 4167
  (Zeros 1 (Pairs 3853 (Zeros 1 (Pairs 1484 Blank))))))).

Fixpoint topN (n:nat) x := match n with O=>x | S n=>topN n (x*4) end.
Fixpoint gN (n:nat) x r := match n with
  | O=>r
  | S n=>pairs (x*9) (zeros (x*9-12) (gN n (x*4) r))
  end.
Definition scaleN (p:bool) n := topN n 12 * (if p then 8 else 4).
Definition target l (p:bool) n z t : Stage := (l,p,
  gN (n+2)%nat (if p then 24 else 12)
    (pairs (scaleN p n*36) (zeros (z*9) (Pairs (t*3) Blank)))).
Definition boundsb p n z t := let x:=scaleN p n in
  (x*20+2 <=? z) && (z <=? x*24) && (x*132 <=? t) && (t <=? x*156).
Definition stage_eqb (s t:Stage) := let '(n,p,r):=s in let '(m,q,t):=t in
  (n =? m) && Bool.eqb p q && tape_eqb r t.
Fixpoint reaches count fuel s t :=
  if stage_eqb s t then true else match count with
  | O => false
  | S count => match stage_step fuel s with
               | Some s => reaches count fuel s t
               | None => false
               end
  end.
End Compute16.
End FT7TM16Compute.

(* Shared definitions from FT7TM17ComputeSpec.v. *)
Module FT7TM17ComputeSpec.
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat Bool.
Import FT7TM17Rules FT7Compute FT7ComputeSpec FT7TM17Compute.

Module ComputeSpec17.
Import FT7TM17Rules.Rules17 Compute13 ComputeSpec13 Compute17.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).
Local Opaque zeros pairs push pop.
Local Opaque N.add N.sub N.mul.

Lemma takezeros_spec n r s: takezeros n r = Some s ->
  denote r = [0]^^(nn n) *> denote s.
Proof.
  destruct r; cbn [takezeros]; try discriminate.
  - intros H; inversion H; subst; cbn [denote].
    rewrite (lpow_all0 [0]) by solve_const0_eq; reflexivity.
  - destruct (N.leb n n0) eqn:E; try discriminate; apply N.leb_le in E.
    intros H; inversion H; subst; cbn [denote]; rewrite zeros_spec.
    replace (nn n0) with (nn n + nn (n0-n)%N) by lia.
    rewrite lpow_add; simpl_tape; reflexivity.
Qed.
Definition BatchSpec f := forall b r n s, f b r = Some (n,s) ->
  (n<=b)%N /\ forall l a b c,
  S1 l a (nn n+b) c 1 (denote r) -[tm]->*
  S1 l (nn n+a) b (nn n+c) 1 (denote s).
Definition chain_nats (xs:list (N*N)) := List.map (fun '(y,v)=>(nn y,nn v)) xs.
Lemma chain_tape_spec n k xs c z r:
  denote (chain_tape n k xs c z r) =
  D1Chain (nn n) (nn k) (chain_nats xs) (nn c) (nn z) (denote r).
Proof.
  gen c; induction xs as [|[y v] xs IH]; intros c; cbn [chain_tape chain_nats List.map D1Chain].
  - rewrite pairs_spec, zeros_spec; flia.
  - repeat (rewrite pairs_spec || rewrite zeros_spec); rewrite IH; flia.
Qed.
Lemma check_batch_spec w: BatchSpec (fun b r=>check_batch b r w).
Proof.
  intros b r n s; destruct w as [k y v xs z t]; unfold check_batch; cbn [cn].
  match goal with |- (if ?e then _ else _) = _ -> _ => destruct e eqn:E end;
    try discriminate; unbool.
  match goal with H: tape_eqb _ _ = true |- _ => apply tape_eqb_spec in H; subst r end.
  intros ER; injection ER as Hn Hs; subst n s; split; [assumption|].
  intros l a b' c; unfold chain_input, chain_output.
  repeat (rewrite pairs_spec || rewrite zeros_spec || rewrite chain_tape_spec).
  applys_eq (D1Chain_incs (nn k) 0 (chain_nats xs) l a b' c
    (nn y) (nn v) (nn z) (denote t)); flia.
Qed.
Lemma batch_spec: BatchSpec batch.
Proof.
  intros b r n s; unfold batch; destruct (chain_witness b r); try discriminate.
  apply check_batch_spec.
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
  - destruct (N.eqb d 0) eqn:Hd; try discriminate.
    destruct (f 0%N 0%N (d-1)%N r) eqn:E; try discriminate.
    intros H l; injection H as Hu Hs; subst u s; apply N.eqb_neq in Hd.
    mid (S1 l 0 0 0 (nn (d-1)%N) (denote r)).
    + unfold S1; cbn [denote]; rewrite (nn_pred _ Hd); finish.
    + exact (HF _ _ _ _ _ 0%nat l E).
  - destruct r as [|d r|d r|r]; try discriminate.
    + intros H; inversion H; subst; cbn [denote].
      rewrite N2Nat.inj_add, N2Nat.inj_mul; apply Tail.
    + destruct (N.eqb d 0) eqn:Hd; try discriminate.
      destruct (f x 0%N (d-1)%N r) eqn:E; try discriminate.
      intros H l; injection H as Hu Hs; subst u s; apply N.eqb_neq in Hd.
      mid (S1 l 0 (nn x) 0 (nn (d-1)%N) (denote r)).
      * unfold S1; cbn [denote]; rewrite (nn_pred _ Hd); finish.
      * exact (HF _ _ _ _ _ 0%nat l E).
Qed.
Lemma onecall_spec f r u s: RunSpec f -> onecall f r = Some (u,s) ->
  exists t, denote r = [1] *> denote t /\ P (nn u) (denote t) (denote s).
Proof.
  intros HF; unfold onecall; specialize (pop_spec r) as Hr.
  destruct (pop r) as [b t]; destruct b; try discriminate.
  intros H; exists t; split; [exact Hr|eapply send_spec; eauto].
Qed.
Definition D1Spec r s :=
  (forall l a b c, S1 l a (1+b) c 1 (denote r) -[tm]->*
    S1 l (1+a) b (1+c) 1 (denote s)) /\
  (forall l a c, S1 l a 0 c 1 (denote r) -[tm]->*
    l <{{A}} [0]^^a *> [1;0]^^(2+c) *> [0] *> denote s).
Lemma d1next_spec f: RunSpec f -> forall r s,
  d1next f r = Some s -> D1Spec r s.
Proof.
  intros HF r s; destruct r as [|y r|y r|r]; try discriminate.
  cbn [d1next]; destruct (N.leb 1 y) eqn:Hy; try discriminate; apply N.leb_le in Hy.
  destruct (takezeros 3 r) eqn:Hr.
  - intros H; injection H as H; subst s; split; intros; cbn [denote];
      rewrite (takezeros_spec _ _ _ Hr), pairs_spec;
      repeat rewrite push_spec.
    + applys_eq (D1_inc l a b c (nn (y-1)%N) 0 (denote t)); flia.
    + applys_eq (D1_empty l a c (nn (y-1)%N) 0 (denote t)); flia.
  - destruct r as [|z r|z r|r]; try discriminate.
    destruct (N.eqb z 1) eqn:Hz; try discriminate; apply N.eqb_eq in Hz; subst z.
    destruct (onecall f r) as [[u t]|] eqn:Ht; try discriminate.
    intros H; injection H as H; subst s.
    destruct (onecall_spec _ _ _ _ HF Ht) as [v [Hv HP]].
    split; intros; cbn [denote]; rewrite Hv, pairs_spec, zeros_spec.
    + applys_eq (D1_call l a b c (nn (y-1)%N) (nn u) (denote v) (denote t) HP); flia.
    + applys_eq (D1_empty_call l a c (nn (y-1)%N) (nn u) (denote v) (denote t) HP); flia.
Qed.

Lemma resume_spec f: RunSpec f -> RunSpec (resume f).
Proof.
  intros HF b c d r r' a l; unfold resume.
  destruct (if (b =? 0)%N then (3 <=? d)%N else false) eqn:Hempty.
  - unbool; subst b; intros H; injection H as H; subst r'.
    rewrite pairs_spec, zeros_spec.
    follow (Empty_b l a (nn c) (nn (d-3)%N) (denote r)); finish; flia.
  - destruct (N.eqb d 0) eqn:Hd.
    + apply N.eqb_eq in Hd; subst d; destruct r as [|z s|y s|s].
      * intros H; injection H as H; subst r'; cbn [denote].
        follow RunTail; finish; flia.
      * intros H; applys_eq (HF _ _ _ _ _ a l H); unfold S1; cbn [denote]; simpl_tape; reflexivity.
      * intros H; applys_eq (HF _ _ _ _ _ a l H); unfold S1; cbn [denote].
        rewrite N2Nat.inj_add, lpow_add; simpl_tape; reflexivity.
      * destruct (send f s) as [[u t]|] eqn:E; try discriminate.
        specialize (send_spec _ HF _ _ _ E) as HP.
        destruct (N.eqb b 0) eqn:Hb.
        -- apply N.eqb_eq in Hb; subst b; intros H; injection H as H; subst r'.
           rewrite pairs_spec, zeros_spec.
           follow (Empty0_call l a (nn c) (nn u) (denote s) (denote t) HP); finish; flia.
        -- apply N.eqb_neq in Hb; intros H.
           follow (Call l a (nn (b-1)%N) (nn c) (nn u) (denote s) (denote t) HP).
           follow (HF _ _ _ _ _ (1+a) l H); finish; flia.
    + destruct (N.eqb d 2) eqn:Hd2.
      * apply N.eqb_eq in Hd2; subst d; destruct (N.eqb b 0) eqn:Hb.
        -- apply N.eqb_eq in Hb; subst b; intros H; injection H as H; subst r'.
           rewrite pairs_spec, push_spec.
           follow Empty2; finish; flia.
        -- apply N.eqb_neq in Hb; intros H.
           mid (S1 l (1+a) (nn (b-1)%N) (nn (c+1)%N) 0 (denote (push 1%sym r))).
           { rewrite push_spec; applys_eq (Inc2 l a (nn (b-1)%N) (nn c) (denote r)); flia. }
           follow (HF _ _ _ _ _ (1+a) l H); finish; flia.
      * destruct (N.eqb d 1) eqn:Hd1; try discriminate.
        apply N.eqb_eq in Hd1; subst d.
        destruct (batch b r) as [[n s]|] eqn:E.
        -- destruct (batch_spec _ _ _ _ E) as [Hb HS]; intros H.
           follow (HS l a (nn (b-n)%N) (nn c)).
           follow (HF _ _ _ _ _ (nn n+a) l H); finish; flia.
        -- destruct (d1next f r) eqn:E1; try discriminate.
           destruct (d1next_spec _ HF _ _ E1) as [HI HE].
           destruct (N.eqb b 0) eqn:Hb.
           ++ apply N.eqb_eq in Hb; subst b; intros H; injection H as H; subst r'.
              rewrite pairs_spec, zeros_spec; follow HE; finish; flia.
           ++ apply N.eqb_neq in Hb; intros H.
              follow (HI l a (nn (b-1)%N) (nn c)).
              follow (HF _ _ _ _ _ (1+a) l H); finish; flia.
Qed.
Lemma run_spec fuel: RunSpec (run fuel).
Proof.
  induction fuel as [|fuel IH]; [intros b c d r r' a l H; discriminate|].
  intros b c d r r' a l; destruct r; cbn [run].
  - intros H; injection H as H; subst r'; cbn [denote].
    follow RunTail; finish; flia.
  - intros H; applys_eq (IH _ _ _ _ _ a l H); unfold S1; cbn [denote].
    rewrite N2Nat.inj_add, lpow_add; simpl_tape; reflexivity.
  - remember (N.min b (d/3)) as k eqn:En.
    destruct (if (k <=? b)%N then (k*3 <=? d)%N else false) eqn:Hn; try discriminate; unbool.
    intros ER; follow (Incs (nn k) l a (nn (b-k)%N) (nn c) (nn (d-k*3)%N) (denote (Pairs n r))).
    follow (resume_spec _ IH _ _ _ _ _ (nn k+a) l ER); finish; flia.
  - remember (N.min b (d/3)) as k eqn:En.
    destruct (if (k <=? b)%N then (k*3 <=? d)%N else false) eqn:Hn; try discriminate; unbool.
    intros ER; follow (Incs (nn k) l a (nn (b-k)%N) (nn c) (nn (d-k*3)%N) (denote (OneBit r))).
    follow (resume_spec _ IH _ _ _ _ _ (nn k+a) l ER); finish; flia.
Qed.
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
  destruct s as [[n p] r]; destruct r as [|y r|y r|r]; try discriminate.
  destruct r as [|z r|z r|r]; try discriminate.
  destruct p; cbn [regionb stage_config]; intros H; unbool.
  - applys_eq (IE (nn n) (nn (z/3)%N) (denote r)); try (unfold C; cbn [denote]; flia).
    apply (goodb_spec r 72%N); assumption.
  - applys_eq (IO (nn n) (nn (z/3)%N) (denote r)); try (unfold C; cbn [denote]; flia).
    apply (goodb_spec r 36%N); assumption.
Qed.
Lemma stage_step_spec fuel s s': stage_step fuel s = Some s' ->
  stage_config s -[tm]->* stage_config s'.
Proof.
  destruct s as [[n p] r]; unfold stage_step.
  destruct (send (run fuel) r) as [[u t]|] eqn:E; try discriminate.
  specialize (send_spec _ (run_spec fuel) _ _ _ E) as HP; destruct p.
  - destruct (N.leb 120 u) eqn:Hu; try discriminate; apply N.leb_le in Hu.
    intros H; injection H as H; subst s'; cbn [stage_config]; rewrite pairs_spec, zeros_spec.
    apply progress_evstep; applys_eq (Left1 (nn n) (nn (u-120)%N) (denote r) (denote t)); try flia.
    applys_eq HP; flia.
  - destruct (N.eqb u 108) eqn:Hu; try discriminate; apply N.eqb_eq in Hu; subst u.
    intros H; injection H as H; subst s'; cbn [stage_config].
    apply progress_evstep; applys_eq (Left0 (nn n) (denote r) (denote t) HP); flia.
Qed.
Lemma check_stages_spec count fuel s: check_stages count fuel s = true ->
  ~halts tm (stage_config s).
Proof.
  gen s; induction count; intros s; cbn [check_stages]; destruct (regionb s) eqn:E;
    try solve [intros _; apply region_nonhalt, regionb_spec, E].
  - discriminate.
  - destruct (stage_step fuel s) eqn:H; try discriminate.
    intros Ht; eapply multistep_nonhalt; [eapply stage_step_spec; eauto|eauto].
Qed.
End ComputeSpec17.
End FT7TM17ComputeSpec.

(* Shared definitions from FT7TM16Cycle.v. *)
Module FT7TM16Cycle.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith.
Import FT7TM17Rules.

Module Cycle16.
Import FT7TM17Rules.Rules17.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(* Full returns, with the left zero count implicit. *)
Definition Run b c d r r' := forall l a,
  S1 l a b c d r -->* l <{{A}} [0]^^(a+b) *> r'.
Lemma RInc n b c d r r':
  Run b (n*2+c) d r r' -> Run (n+b) c (n*3+d) r r'.
Proof. intros H l a; follow Incs; follow (H l (n+a)); finish. Qed.
Lemma REnd c d r: Run 0 c (3+d) r ([1;0]^^(3+c)*>[0]^^d*>r).
Proof. intros l a; follow Empty_b; finish. Qed.
Lemma RTail b c d: Run b c d 0inf ([1;0]^^(b*2+c+3)*>0inf).
Proof.
  intros l a; mid (S1 l a (b+0) c (b*3+3) 0inf).
  - unfold S1; repeat rewrite (lpow_all0 [0]) by solve_const0_eq; finish.
  - follow Incs; follow Empty_b; finish.
Qed.
Lemma RMerge b c d y r r':
  Run b (c+y) d r r' -> Run b c 0 ([1;0]^^y*>[0]^^d*>r) r'.
Proof. intros H l a; applys_eq (H l a); unfold S1; rewrite lpow_add; simpl_tape; reflexivity. Qed.
Lemma RZeros b c d z r r':
  Run b c (d+z) r r' -> Run b c d ([0]^^z*>r) r'.
Proof. intros H l a; applys_eq (H l a); unfold S1; rewrite lpow_add; simpl_tape; reflexivity. Qed.
Lemma RP x d r r':
  Run x 0 d r r' -> P x ([1;0]^^x*>[0]^^(1+d)*>r) r'.
Proof. intros H l; applys_eq (H l 0%nat); unfold S1; simpl_tape; flia. Qed.
Lemma RCall2 b c u r r1 r2:
  P u r r1 -> Run b (c+1) u r1 r2 -> Run (2+b) c 2 r r2.
Proof. intros H1 H2 l a; follow Inc2; follow Call; follow (H2 l (2+a)); finish. Qed.
Lemma RD1 b c y z r r':
  Run b (1+c) 1 ([1;0]^^y*>[0;1;0;1]*>[0]^^z*>r) r' ->
  Run (1+b) c 1 ([1;0]^^(1+y)*>[0]^^(3+z)*>r) r'.
Proof. intros H l a; follow D1_inc; follow (H l (1+a)); finish. Qed.
Lemma RD1Call b c y u r r1 r2:
  P u r r1 -> Run b (1+c) 1 ([1;0]^^y*>[0]^^(1+u)*>r1) r2 ->
  Run (1+b) c 1 ([1;0]^^(1+y)*>[0;1]*>r) r2.
Proof. intros H1 H2 l a; follow D1_call; follow (H2 l (1+a)); finish. Qed.
Lemma RD1Empty c y u r r':
  P u r r' -> Run 0 c 1 ([1;0]^^(1+y)*>[0;1]*>r)
    ([1;0]^^(2+c)*>[0]*>[1;0]^^y*>[0]^^(1+u)*>r').
Proof. intros H l a; follow D1_empty_call; finish. Qed.
Lemma RZeroTail v: P 0 ([0]*>[1;0]^^v*>0inf) ([1;0]^^(v+3)*>0inf).
Proof.
  applys_eq (RP 0 0 ([1;0]^^v*>0inf) ([1;0]^^(v+3)*>0inf)); try reflexivity.
  applys_eq (RMerge 0 0 0 v 0inf ([1;0]^^(v+3)*>0inf)); try reflexivity.
  applys_eq (RTail 0 v 0); flia.
Qed.
Lemma RD1Tail c y v:
  Run 0 c 1 ([1;0]^^(1+y)*>[0]*>[1;0]^^(1+v)*>0inf)
    ([1;0]^^(2+c)*>[0]*>[1;0]^^y*>[0]*>[1;0]^^(v+3)*>0inf).
Proof. applys_eq (RD1Empty c y 0 ([0]*>[1;0]^^v*>0inf)
  ([1;0]^^(v+3)*>0inf)); try reflexivity. apply RZeroTail. Qed.
Lemma RShift n b c y v z r r':
  Run b (n+c) 1 ([1;0]^^y*>[0]*>[1;0]^^(1+v+n*2)*>[0]^^z*>r) r' ->
  Run (n+b) c 1 ([1;0]^^(n+y)*>[0]*>[1;0]^^(1+v)*>[0]^^(n*3+z)*>r) r'.
Proof. intros H l a; follow D1_shifts; follow (H l (n+a)); finish. Qed.

Definition W0 n r := [0]^^n *> r.
Definition W1 n r := [1;0]^^n *> r.
Ltac eqs := try unfold W0; try unfold W1;
  repeat rewrite (lpow_all0 [0]) by solve_const0_eq;
  let rec go := first [solve [lia] |
    solve [cbn [Str_app lpow List.app]; repeat rewrite <-const_unfold; reflexivity] |
    progress f_equal; go] in
  first [solve [go] |
    solve [f_equal; [flia|cbn; repeat rewrite <-const_unfold; reflexivity]] |
    simpl_tape; repeat rewrite <-const_unfold; solve [flia]].
Ltac e_inc n := match goal with |- Run ?b ?c ?d ?r ?r' =>
  applys_eq (RInc n (b-n) c (d-n*3) r r'); try eqs end.
Ltac e_end := match goal with |- Run ?b ?c ?d ?r ?r' =>
  applys_eq (REnd c (d-3) r); eqs end.
Ltac e_tail := match goal with |- Run ?b ?c ?d ?r ?r' =>
  applys_eq (RTail b c d); eqs end.
Ltac e_merge y d r := match goal with |- Run ?b ?c _ _ ?r' =>
  applys_eq (RMerge b c d y r r'); try eqs end.
Ltac e_zeros z r := match goal with |- Run ?b ?c ?d _ ?r' =>
  applys_eq (RZeros b c d z r r'); try eqs end.
Ltac e_call2 u r1 := match goal with |- Run ?b ?c _ ?r ?r2 =>
  applys_eq (RCall2 (b-2) c u r r1 r2); try eqs end.
Ltac e_d1 y z r := match goal with |- Run ?b ?c _ _ ?r' =>
  applys_eq (RD1 (b-1) c y z r r'); try eqs end.
Ltac e_d1call y u r r1 := match goal with |- Run ?b ?c _ _ ?r2 =>
  applys_eq (RD1Call (b-1) c y u r r1 r2); try eqs end.
Ltac e_d1empty y u r r1 := match goal with |- Run _ ?c _ _ _ =>
  applys_eq (RD1Empty c y u r r1); try eqs end.
Ltac e_d1tail y v := match goal with |- Run _ ?c _ _ _ =>
  applys_eq (RD1Tail c y v); try eqs end.
Ltac e_shift n y v z r := match goal with |- Run ?b ?c _ _ ?r' =>
  applys_eq (RShift n (b-n) c y v z r r'); try eqs end.
Ltac p_start x d r := match goal with |- P _ _ ?r' =>
  applys_eq (RP x d r r'); try eqs end.
Ltac p_tail n := applys_eq (Tail n); eqs.

Lemma Local1 x z t:
  3<=x -> x*20+2<=z -> z<=x*24 -> x*132<=t -> t<=x*156 ->
  P (x*9%nat) (W1 (x*9%nat) (W0 (x*9-(12)%nat) (W1 (x*36%nat) (W0 (z*9%nat) (W1 (t*3%nat) 0inf)))))
    (W1 (x*18%nat) (W0 (x*18-(12)%nat) (W1 (x*72+3%nat) (W0 (z*9-(x*108+4)%nat) (W1 (t*3%nat) 0inf))))).
Proof. intros.
  p_start (x*9%nat) (x*9-(13)%nat) (W1 (x*36%nat) (W0 (z*9%nat) (W1 (t*3%nat) 0inf))).
  e_inc (x*3-(5)%nat).
  e_call2 (x*36%nat) (W1 (x*72+3%nat) (W0 (z*9-(x*108+4)%nat) (W1 (t*3%nat) 0inf))).
  {
    p_start (x*36%nat) (z*9-(1)%nat) (W1 (t*3%nat) 0inf).
    e_inc (x*36%nat).
    e_end.
  }
  e_inc (x*6+3%nat).
  e_end.
Qed.

Lemma Local2 x z t:
  3<=x -> x*20+2<=z -> z<=x*24 -> x*132<=t -> t<=x*156 ->
  P (x*18%nat) (W1 (x*18%nat) (W0 (x*18-(12)%nat) (W1 (x*72+3%nat) (W0 (z*9-(x*108+4)%nat) (W1 (t*3%nat) 0inf)))))
    (W1 (x*36%nat) (W0 (x*36-(9)%nat) (W1 (x*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-(x*108+6)%nat) (W0 (1%nat) (W1 (x*216+12-(z*6)%nat) 0inf))))))).
Proof. intros.
  p_start (x*18%nat) (x*18-(13)%nat) (W1 (x*72+3%nat) (W0 (z*9-(x*108+4)%nat) (W1 (t*3%nat) 0inf))).
  e_inc (x*6-(5)%nat).
  e_call2 (x*72+3%nat) (W1 (x*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-(x*108+6)%nat) (W0 (1%nat) (W1 (x*216+12-(z*6)%nat) 0inf))))).
  {
    p_start (x*72+3%nat) (z*9-(x*108+5)%nat) (W1 (t*3%nat) 0inf).
    e_inc (z*3-(x*36+2)%nat).
    e_d1 (t*3-(1)%nat) (0%nat) 0inf.
    e_shift (x*108+4-(z*3)%nat) (z*3+t*3-(x*108+5)%nat) (1%nat) (0%nat) 0inf.
    e_d1tail (z*3+t*3-(x*108+6)%nat) (x*216+9-(z*6)%nat).
  }
  e_inc (x*12+3%nat).
  e_end.
Qed.

Lemma Local3 x z t:
  3<=x -> x*20+2<=z -> z<=x*24 -> x*132<=t -> t<=x*156 ->
  P (x*9%nat) (W1 (x*9%nat) (W0 (x*9-(12)%nat) (W1 (x*36%nat) (W0 (x*36-(9)%nat) (W1 (x*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-(x*108+6)%nat) (W0 (1%nat) (W1 (x*216+12-(z*6)%nat) 0inf)))))))))
    (W1 (x*18%nat) (W0 (x*18-(12)%nat) (W1 (x*72%nat) (W0 (z*3-(x*36+6)%nat) (W1 (z*15+t*3-(x*252+12)%nat) (W0 (x*972+54-(z*39)%nat) (W1 (x*864+51-(z*24)%nat) 0inf))))))).
Proof. intros.
  p_start (x*9%nat) (x*9-(13)%nat) (W1 (x*36%nat) (W0 (x*36-(9)%nat) (W1 (x*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-(x*108+6)%nat) (W0 (1%nat) (W1 (x*216+12-(z*6)%nat) 0inf))))))).
  e_inc (x*3-(5)%nat).
  e_call2 (x*36%nat) (W1 (x*72%nat) (W0 (z*3-(x*36+6)%nat) (W1 (z*15+t*3-(x*252+12)%nat) (W0 (x*972+54-(z*39)%nat) (W1 (x*864+51-(z*24)%nat) 0inf))))).
  {
    p_start (x*36%nat) (x*36-(10)%nat) (W1 (x*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-(x*108+6)%nat) (W0 (1%nat) (W1 (x*216+12-(z*6)%nat) 0inf))))).
    e_inc (x*12-(4)%nat).
    e_call2 (x*36+z*3+3%nat) (W1 (z*15+t*3-(x*252+12)%nat) (W0 (x*972+54-(z*39)%nat) (W1 (x*864+51-(z*24)%nat) 0inf))).
    {
      p_start (x*36+z*3+3%nat) (0%nat) (W1 (z*3+t*3-(x*108+6)%nat) (W0 (1%nat) (W1 (x*216+12-(z*6)%nat) 0inf))).
      e_merge (z*3+t*3-(x*108+6)%nat) (1%nat) (W1 (x*216+12-(z*6)%nat) 0inf).
      e_d1 (x*216+11-(z*6)%nat) (0%nat) 0inf.
      e_shift (x*216+11-(z*6)%nat) (0%nat) (1%nat) (0%nat) 0inf.
      e_zeros (1%nat) (W1 (x*432+24-(z*12)%nat) 0inf).
      { change ([0]*>[1;0]^^(1+1+(x*216+11-(z*6)%nat)*2)*>0inf =
          [0]*>(W1 (x*432+24-(z*12)%nat) 0inf)). unfold W1; flia. }
      e_call2 (x*432+24-(z*12)%nat) (W1 (x*864+51-(z*24)%nat) 0inf).
      {
        p_tail (x*432+24-(z*12)%nat).
      }
      e_inc (z*9-(x*180+11)%nat).
      e_end.
    }
    e_inc (x*24+2%nat).
    e_end.
  }
  e_inc (x*6+3%nat).
  e_end.
Qed.

Lemma Local4 x z t:
  3<=x -> x*20+2<=z -> z<=x*24 -> x*132<=t -> t<=x*156 ->
  P (x*18%nat) (W1 (x*18%nat) (W0 (x*18-(12)%nat) (W1 (x*72%nat) (W0 (z*3-(x*36+6)%nat) (W1 (z*15+t*3-(x*252+12)%nat) (W0 (x*972+54-(z*39)%nat) (W1 (x*864+51-(z*24)%nat) 0inf)))))))
    (W1 (x*36%nat) (W0 (x*36-(12)%nat) (W1 (x*144%nat) (W0 (z*18+t*3-(x*504+18)%nat) (W1 (x*1224+t*6+81-(z*18)%nat) 0inf))))).
Proof. intros.
  p_start (x*18%nat) (x*18-(13)%nat) (W1 (x*72%nat) (W0 (z*3-(x*36+6)%nat) (W1 (z*15+t*3-(x*252+12)%nat) (W0 (x*972+54-(z*39)%nat) (W1 (x*864+51-(z*24)%nat) 0inf))))).
  e_inc (x*6-(5)%nat).
  e_call2 (x*72%nat) (W1 (x*144%nat) (W0 (z*18+t*3-(x*504+18)%nat) (W1 (x*1224+t*6+81-(z*18)%nat) 0inf))).
  {
    p_start (x*72%nat) (z*3-(x*36+7)%nat) (W1 (z*15+t*3-(x*252+12)%nat) (W0 (x*972+54-(z*39)%nat) (W1 (x*864+51-(z*24)%nat) 0inf))).
    e_inc (z-(x*12+3)%nat).
    e_call2 (z*15+t*3-(x*252+12)%nat) (W1 (x*1224+t*6+81-(z*18)%nat) 0inf).
    {
      p_start (z*15+t*3-(x*252+12)%nat) (x*972+53-(z*39)%nat) (W1 (x*864+51-(z*24)%nat) 0inf).
      e_inc (x*324+17-(z*13)%nat).
      e_call2 (x*864+51-(z*24)%nat) (W1 (x*1728+105-(z*48)%nat) 0inf).
      {
        p_tail (x*864+51-(z*24)%nat).
      }
      e_inc (x*288+17-(z*8)%nat).
      e_merge (x*1728+105-(z*48)%nat) (0%nat) 0inf.
      e_tail.
    }
    e_inc (x*84+1-(z)%nat).
    e_end.
  }
  e_inc (x*12+3%nat).
  e_end.
Qed.

Lemma Local5 x z t:
  3<=x -> x*20+2<=z -> z<=x*24 -> x*132<=t -> t<=x*156 ->
  P (x*36%nat) (W1 (x*36%nat) (W0 (x*36-(12)%nat) (W1 (x*144%nat) (W0 (z*18+t*3-(x*504+18)%nat) (W1 (x*1224+t*6+81-(z*18)%nat) 0inf)))))
    (W1 (x*72%nat) (W0 (x*72-(12)%nat) (W1 (x*288%nat) (W0 (x*288+t*9+63%nat) (W1 (x*2448+t*12+165-(z*36)%nat) 0inf))))).
Proof. intros.
  p_start (x*36%nat) (x*36-(13)%nat) (W1 (x*144%nat) (W0 (z*18+t*3-(x*504+18)%nat) (W1 (x*1224+t*6+81-(z*18)%nat) 0inf))).
  e_inc (x*12-(5)%nat).
  e_call2 (x*144%nat) (W1 (x*288%nat) (W0 (x*288+t*9+63%nat) (W1 (x*2448+t*12+165-(z*36)%nat) 0inf))).
  {
    p_start (x*144%nat) (z*18+t*3-(x*504+19)%nat) (W1 (x*1224+t*6+81-(z*18)%nat) 0inf).
    e_inc (z*6+t-(x*168+7)%nat).
    e_call2 (x*1224+t*6+81-(z*18)%nat) (W1 (x*2448+t*12+165-(z*36)%nat) 0inf).
    {
      p_tail (x*1224+t*6+81-(z*18)%nat).
    }
    e_inc (x*312+5-(z*6+t)%nat).
    e_end.
  }
  e_inc (x*24+3%nat).
  e_end.
Qed.

End Cycle16.
End FT7TM16Cycle.

(* Shared definitions from FT7TM16Prefix.v. *)
Module FT7TM16Prefix.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith PeanoNat.
Import FT7TM17Rules FT7TM16Cycle.

Module Prefix16.
Import FT7TM17Rules.Rules17 Cycle16.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Definition Top n x := x*4^n.
Lemma Top_succ n x: Top (S n) x = Top n (x*4).
Proof. unfold Top; cbn [Nat.pow]; nia. Qed.
Lemma Top_mul n x y: Top n (x*y)=Top n x*y.
Proof. unfold Top; nia. Qed.
Lemma Top_ge n x: x<=Top n x.
Proof. unfold Top; nia. Qed.
Lemma Top_add n m x: Top (n+m) x=Top m (Top n x).
Proof. unfold Top; rewrite Nat.pow_add_r; nia. Qed.

Definition Ideal x r := [1;0]^^(x*9)*>[0]^^(x*9-12)*>r.
Fixpoint G n x r := match n with
  | O => r
  | S n => Ideal x (G n (x*4) r)
  end.
Lemma G_spec n x r r':
  2<=x -> P (Top n x*9) r r' -> P (x*9) (G n x r) (G n (x*2) r').
Proof.
  gen x; induction n; intros x Hx HP; cbn [G].
  - applys_eq HP; unfold Top; cbn [Nat.pow]; flia.
  - rewrite Top_succ in HP; unfold Ideal.
    applys_eq (Column3 (x*3) (x*3-4) (x*12)
      (G n (x*4) r) (G n (x*8) r')); try flia.
    applys_eq (IHn (x*4)); try flia; assumption.
Qed.
Lemma G_snoc n x r:
  G (S n) x r = G n x (Ideal (Top n x) r).
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

Definition Config (p:bool) l n r :=
  0inf <{{A}} (if p then LE l else LO l) *> G n (if p then 24 else 12) r.
Lemma Step0 l n x r r': Top n 12=x -> P (x*9) r r' ->
  Config false l n r -->+ Config true (l+10) n r'.
Proof.
  intros H HP; apply Left0, G_spec; try lia.
  applys_eq HP; flia.
Qed.
Lemma Step1 l n x r r': Top n 12=x -> P (x*18) r r' ->
  Config true l n r -->+ Config false (l+10) n (Ideal x r').
Proof.
  intros H HP; unfold Config; rewrite <-H, <-G_snoc; cbn [G]; unfold Ideal.
  apply (Left1 l 96), G_spec; try lia.
  applys_eq HP; unfold Top in *; flia.
Qed.
Ltac geqs := cbn [G]; unfold Ideal; Cycle16.eqs.

Definition R0_1 q z t := G 2 (q*1) (W1 ((q*4)*36%nat) (W0 (z*9%nat) (W1 (t*3%nat) 0inf))).
Definition R0_2 q z t := G 2 (q*2) (W1 ((q*4)*72+3%nat) (W0 (z*9-((q*4)*108+4)%nat) (W1 (t*3%nat) 0inf))).
Definition R0_3 q z t := G 2 (q*1) (W1 ((q*4)*36%nat) (W0 ((q*4)*36-(9)%nat) (W1 ((q*4)*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-((q*4)*108+6)%nat) (W0 (1%nat) (W1 ((q*4)*216+12-(z*6)%nat) 0inf))))))).
Definition R0_4 q z t := G 2 (q*2) (W1 ((q*4)*72%nat) (W0 (z*3-((q*4)*36+6)%nat) (W1 (z*15+t*3-((q*4)*252+12)%nat) (W0 ((q*4)*972+54-(z*39)%nat) (W1 ((q*4)*864+51-(z*24)%nat) 0inf))))).
Definition R0_5 q z t := G 3 (q*1) (W1 ((q*4)*144%nat) (W0 (z*18+t*3-((q*4)*504+18)%nat) (W1 ((q*4)*1224+t*6+81-(z*18)%nat) 0inf))).
Definition R0_6 q z t := G 3 (q*2) (W1 ((q*4)*288%nat) (W0 ((q*4)*288+t*9+63%nat) (W1 ((q*4)*2448+t*12+165-(z*36)%nat) 0inf))).

Definition O0_1 q z t := (R0_2 q z t).
Lemma Flow0_1 q z t: 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  P (q*9) (R0_1 q z t) (O0_1 q z t).
Proof. intros; unfold R0_1, O0_1, R0_2.
  applys_eq (G_spec 1 (q*1) (W1 ((q*4)*9%nat) (W0 ((q*4)*9-(12)%nat) (W1 ((q*4)*36%nat) (W0 (z*9%nat) (W1 (t*3%nat) 0inf))))) (W1 ((q*4)*18%nat) (W0 ((q*4)*18-(12)%nat) (W1 ((q*4)*72+3%nat) (W0 (z*9-((q*4)*108+4)%nat) (W1 (t*3%nat) 0inf)))))); try geqs; try lia.
  applys_eq (Local1 (q*4) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans0_1 l n q z t: Top n 12=q -> 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  Config false l n (R0_1 q z t) -->+ Config true (l+10) n (R0_2 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step0 l n q (R0_1 q z t) (O0_1 q z t) H);
    try (unfold Config, R0_2, O0_1; geqs).
  apply Flow0_1; assumption.
Qed.

Definition O0_2 q z t := (G 1 (q*4) (W1 ((q*4)*36%nat) (W0 ((q*4)*36-(9)%nat) (W1 ((q*4)*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-((q*4)*108+6)%nat) (W0 (1%nat) (W1 ((q*4)*216+12-(z*6)%nat) 0inf)))))))).
Lemma Flow0_2 q z t: 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  P (q*18) (R0_2 q z t) (O0_2 q z t).
Proof. intros; unfold R0_2, O0_2.
  applys_eq (G_spec 1 (q*2) (W1 ((q*4)*18%nat) (W0 ((q*4)*18-(12)%nat) (W1 ((q*4)*72+3%nat) (W0 (z*9-((q*4)*108+4)%nat) (W1 (t*3%nat) 0inf))))) (W1 ((q*4)*36%nat) (W0 ((q*4)*36-(9)%nat) (W1 ((q*4)*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-((q*4)*108+6)%nat) (W0 (1%nat) (W1 ((q*4)*216+12-(z*6)%nat) 0inf)))))))); try geqs; try lia.
  applys_eq (Local2 (q*4) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans0_2 l n q z t: Top n 12=q -> 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  Config true l n (R0_2 q z t) -->+ Config false (l+10) n (R0_3 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step1 l n q (R0_2 q z t) (O0_2 q z t) H);
    try (unfold Config, R0_3, O0_2; geqs).
  apply Flow0_2; assumption.
Qed.

Definition O0_3 q z t := (R0_4 q z t).
Lemma Flow0_3 q z t: 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  P (q*9) (R0_3 q z t) (O0_3 q z t).
Proof. intros; unfold R0_3, O0_3, R0_4.
  applys_eq (G_spec 1 (q*1) (W1 ((q*4)*9%nat) (W0 ((q*4)*9-(12)%nat) (W1 ((q*4)*36%nat) (W0 ((q*4)*36-(9)%nat) (W1 ((q*4)*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-((q*4)*108+6)%nat) (W0 (1%nat) (W1 ((q*4)*216+12-(z*6)%nat) 0inf))))))))) (W1 ((q*4)*18%nat) (W0 ((q*4)*18-(12)%nat) (W1 ((q*4)*72%nat) (W0 (z*3-((q*4)*36+6)%nat) (W1 (z*15+t*3-((q*4)*252+12)%nat) (W0 ((q*4)*972+54-(z*39)%nat) (W1 ((q*4)*864+51-(z*24)%nat) 0inf)))))))); try geqs; try lia.
  applys_eq (Local3 (q*4) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans0_3 l n q z t: Top n 12=q -> 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  Config false l n (R0_3 q z t) -->+ Config true (l+10) n (R0_4 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step0 l n q (R0_3 q z t) (O0_3 q z t) H);
    try (unfold Config, R0_4, O0_3; geqs).
  apply Flow0_3; assumption.
Qed.

Definition O0_4 q z t := (G 2 (q*4) (W1 ((q*4)*144%nat) (W0 (z*18+t*3-((q*4)*504+18)%nat) (W1 ((q*4)*1224+t*6+81-(z*18)%nat) 0inf)))).
Lemma Flow0_4 q z t: 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  P (q*18) (R0_4 q z t) (O0_4 q z t).
Proof. intros; unfold R0_4, O0_4.
  applys_eq (G_spec 1 (q*2) (W1 ((q*4)*18%nat) (W0 ((q*4)*18-(12)%nat) (W1 ((q*4)*72%nat) (W0 (z*3-((q*4)*36+6)%nat) (W1 (z*15+t*3-((q*4)*252+12)%nat) (W0 ((q*4)*972+54-(z*39)%nat) (W1 ((q*4)*864+51-(z*24)%nat) 0inf))))))) (W1 ((q*4)*36%nat) (W0 ((q*4)*36-(12)%nat) (W1 ((q*4)*144%nat) (W0 (z*18+t*3-((q*4)*504+18)%nat) (W1 ((q*4)*1224+t*6+81-(z*18)%nat) 0inf)))))); try geqs; try lia.
  applys_eq (Local4 (q*4) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans0_4 l n q z t: Top n 12=q -> 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  Config true l n (R0_4 q z t) -->+ Config false (l+10) n (R0_5 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step1 l n q (R0_4 q z t) (O0_4 q z t) H);
    try (unfold Config, R0_5, O0_4; geqs).
  apply Flow0_4; assumption.
Qed.

Definition O0_5 q z t := (R0_6 q z t).
Lemma Flow0_5 q z t: 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  P (q*9) (R0_5 q z t) (O0_5 q z t).
Proof. intros; unfold R0_5, O0_5, R0_6.
  applys_eq (G_spec 2 (q*1) (W1 ((q*4)*36%nat) (W0 ((q*4)*36-(12)%nat) (W1 ((q*4)*144%nat) (W0 (z*18+t*3-((q*4)*504+18)%nat) (W1 ((q*4)*1224+t*6+81-(z*18)%nat) 0inf))))) (W1 ((q*4)*72%nat) (W0 ((q*4)*72-(12)%nat) (W1 ((q*4)*288%nat) (W0 ((q*4)*288+t*9+63%nat) (W1 ((q*4)*2448+t*12+165-(z*36)%nat) 0inf)))))); try geqs; try lia.
  applys_eq (Local5 (q*4) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans0_5 l n q z t: Top n 12=q -> 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  Config false l n (R0_5 q z t) -->+ Config true (l+10) n (R0_6 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step0 l n q (R0_5 q z t) (O0_5 q z t) H);
    try (unfold Config, R0_6, O0_5; geqs).
  apply Flow0_5; assumption.
Qed.

Lemma Cycle0 l n q z t: Top n 12=q -> 12<=q -> q*4*20+2<=z -> z<=q*4*24 -> q*4*132<=t -> t<=q*4*156 ->
  Config false l n (R0_1 q z t) -->+ Config true (l+50) n (R0_6 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  follow11 (Trans0_1 l n q z t H H0 H1 H2 H3 H4).
  follow11 (Trans0_2 (l+10) n q z t H H0 H1 H2 H3 H4).
  follow11 (Trans0_3 ((l+10)+10) n q z t H H0 H1 H2 H3 H4).
  follow11 (Trans0_4 (((l+10)+10)+10) n q z t H H0 H1 H2 H3 H4).
  applys_eq (Trans0_5 ((((l+10)+10)+10)+10) n q z t H H0 H1 H2 H3 H4); flia.
Qed.

Definition R1_1 q z t := G 2 (q*2) (W1 ((q*8)*36%nat) (W0 (z*9%nat) (W1 (t*3%nat) 0inf))).
Definition R1_2 q z t := G 3 (q*1) (W1 ((q*8)*72+3%nat) (W0 (z*9-((q*8)*108+4)%nat) (W1 (t*3%nat) 0inf))).
Definition R1_3 q z t := G 2 (q*2) (W1 ((q*8)*36%nat) (W0 ((q*8)*36-(9)%nat) (W1 ((q*8)*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-((q*8)*108+6)%nat) (W0 (1%nat) (W1 ((q*8)*216+12-(z*6)%nat) 0inf))))))).
Definition R1_4 q z t := G 3 (q*1) (W1 ((q*8)*72%nat) (W0 (z*3-((q*8)*36+6)%nat) (W1 (z*15+t*3-((q*8)*252+12)%nat) (W0 ((q*8)*972+54-(z*39)%nat) (W1 ((q*8)*864+51-(z*24)%nat) 0inf))))).
Definition R1_5 q z t := G 3 (q*2) (W1 ((q*8)*144%nat) (W0 (z*18+t*3-((q*8)*504+18)%nat) (W1 ((q*8)*1224+t*6+81-(z*18)%nat) 0inf))).
Definition R1_6 q z t := G 4 (q*1) (W1 ((q*8)*288%nat) (W0 ((q*8)*288+t*9+63%nat) (W1 ((q*8)*2448+t*12+165-(z*36)%nat) 0inf))).

Definition O1_1 q z t := (G 2 (q*4) (W1 ((q*8)*72+3%nat) (W0 (z*9-((q*8)*108+4)%nat) (W1 (t*3%nat) 0inf)))).
Lemma Flow1_1 q z t: 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  P (q*18) (R1_1 q z t) (O1_1 q z t).
Proof. intros; unfold R1_1, O1_1.
  applys_eq (G_spec 1 (q*2) (W1 ((q*8)*9%nat) (W0 ((q*8)*9-(12)%nat) (W1 ((q*8)*36%nat) (W0 (z*9%nat) (W1 (t*3%nat) 0inf))))) (W1 ((q*8)*18%nat) (W0 ((q*8)*18-(12)%nat) (W1 ((q*8)*72+3%nat) (W0 (z*9-((q*8)*108+4)%nat) (W1 (t*3%nat) 0inf)))))); try geqs; try lia.
  applys_eq (Local1 (q*8) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans1_1 l n q z t: Top n 12=q -> 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  Config true l n (R1_1 q z t) -->+ Config false (l+10) n (R1_2 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step1 l n q (R1_1 q z t) (O1_1 q z t) H);
    try (unfold Config, R1_2, O1_1; geqs).
  apply Flow1_1; assumption.
Qed.

Definition O1_2 q z t := (R1_3 q z t).
Lemma Flow1_2 q z t: 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  P (q*9) (R1_2 q z t) (O1_2 q z t).
Proof. intros; unfold R1_2, O1_2, R1_3.
  applys_eq (G_spec 2 (q*1) (W1 ((q*8)*18%nat) (W0 ((q*8)*18-(12)%nat) (W1 ((q*8)*72+3%nat) (W0 (z*9-((q*8)*108+4)%nat) (W1 (t*3%nat) 0inf))))) (W1 ((q*8)*36%nat) (W0 ((q*8)*36-(9)%nat) (W1 ((q*8)*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-((q*8)*108+6)%nat) (W0 (1%nat) (W1 ((q*8)*216+12-(z*6)%nat) 0inf)))))))); try geqs; try lia.
  applys_eq (Local2 (q*8) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans1_2 l n q z t: Top n 12=q -> 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  Config false l n (R1_2 q z t) -->+ Config true (l+10) n (R1_3 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step0 l n q (R1_2 q z t) (O1_2 q z t) H);
    try (unfold Config, R1_3, O1_2; geqs).
  apply Flow1_2; assumption.
Qed.

Definition O1_3 q z t := (G 2 (q*4) (W1 ((q*8)*72%nat) (W0 (z*3-((q*8)*36+6)%nat) (W1 (z*15+t*3-((q*8)*252+12)%nat) (W0 ((q*8)*972+54-(z*39)%nat) (W1 ((q*8)*864+51-(z*24)%nat) 0inf)))))).
Lemma Flow1_3 q z t: 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  P (q*18) (R1_3 q z t) (O1_3 q z t).
Proof. intros; unfold R1_3, O1_3.
  applys_eq (G_spec 1 (q*2) (W1 ((q*8)*9%nat) (W0 ((q*8)*9-(12)%nat) (W1 ((q*8)*36%nat) (W0 ((q*8)*36-(9)%nat) (W1 ((q*8)*36+z*3+3%nat) (W0 (1%nat) (W1 (z*3+t*3-((q*8)*108+6)%nat) (W0 (1%nat) (W1 ((q*8)*216+12-(z*6)%nat) 0inf))))))))) (W1 ((q*8)*18%nat) (W0 ((q*8)*18-(12)%nat) (W1 ((q*8)*72%nat) (W0 (z*3-((q*8)*36+6)%nat) (W1 (z*15+t*3-((q*8)*252+12)%nat) (W0 ((q*8)*972+54-(z*39)%nat) (W1 ((q*8)*864+51-(z*24)%nat) 0inf)))))))); try geqs; try lia.
  applys_eq (Local3 (q*8) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans1_3 l n q z t: Top n 12=q -> 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  Config true l n (R1_3 q z t) -->+ Config false (l+10) n (R1_4 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step1 l n q (R1_3 q z t) (O1_3 q z t) H);
    try (unfold Config, R1_4, O1_3; geqs).
  apply Flow1_3; assumption.
Qed.

Definition O1_4 q z t := (R1_5 q z t).
Lemma Flow1_4 q z t: 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  P (q*9) (R1_4 q z t) (O1_4 q z t).
Proof. intros; unfold R1_4, O1_4, R1_5.
  applys_eq (G_spec 2 (q*1) (W1 ((q*8)*18%nat) (W0 ((q*8)*18-(12)%nat) (W1 ((q*8)*72%nat) (W0 (z*3-((q*8)*36+6)%nat) (W1 (z*15+t*3-((q*8)*252+12)%nat) (W0 ((q*8)*972+54-(z*39)%nat) (W1 ((q*8)*864+51-(z*24)%nat) 0inf))))))) (W1 ((q*8)*36%nat) (W0 ((q*8)*36-(12)%nat) (W1 ((q*8)*144%nat) (W0 (z*18+t*3-((q*8)*504+18)%nat) (W1 ((q*8)*1224+t*6+81-(z*18)%nat) 0inf)))))); try geqs; try lia.
  applys_eq (Local4 (q*8) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans1_4 l n q z t: Top n 12=q -> 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  Config false l n (R1_4 q z t) -->+ Config true (l+10) n (R1_5 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step0 l n q (R1_4 q z t) (O1_4 q z t) H);
    try (unfold Config, R1_5, O1_4; geqs).
  apply Flow1_4; assumption.
Qed.

Definition O1_5 q z t := (G 3 (q*4) (W1 ((q*8)*288%nat) (W0 ((q*8)*288+t*9+63%nat) (W1 ((q*8)*2448+t*12+165-(z*36)%nat) 0inf)))).
Lemma Flow1_5 q z t: 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  P (q*18) (R1_5 q z t) (O1_5 q z t).
Proof. intros; unfold R1_5, O1_5.
  applys_eq (G_spec 2 (q*2) (W1 ((q*8)*36%nat) (W0 ((q*8)*36-(12)%nat) (W1 ((q*8)*144%nat) (W0 (z*18+t*3-((q*8)*504+18)%nat) (W1 ((q*8)*1224+t*6+81-(z*18)%nat) 0inf))))) (W1 ((q*8)*72%nat) (W0 ((q*8)*72-(12)%nat) (W1 ((q*8)*288%nat) (W0 ((q*8)*288+t*9+63%nat) (W1 ((q*8)*2448+t*12+165-(z*36)%nat) 0inf)))))); try geqs; try lia.
  applys_eq (Local5 (q*8) z t); try (unfold Top; cbn [Nat.pow]; geqs); lia.
Qed.
Lemma Trans1_5 l n q z t: Top n 12=q -> 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  Config true l n (R1_5 q z t) -->+ Config false (l+10) n (R1_6 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  applys_eq (Step1 l n q (R1_5 q z t) (O1_5 q z t) H);
    try (unfold Config, R1_6, O1_5; geqs).
  apply Flow1_5; assumption.
Qed.

Lemma Cycle1 l n q z t: Top n 12=q -> 12<=q -> q*8*20+2<=z -> z<=q*8*24 -> q*8*132<=t -> t<=q*8*156 ->
  Config true l n (R1_1 q z t) -->+ Config false (l+50) n (R1_6 q z t).
Proof. intros H H0 H1 H2 H3 H4.
  follow11 (Trans1_1 l n q z t H H0 H1 H2 H3 H4).
  follow11 (Trans1_2 (l+10) n q z t H H0 H1 H2 H3 H4).
  follow11 (Trans1_3 ((l+10)+10) n q z t H H0 H1 H2 H3 H4).
  follow11 (Trans1_4 (((l+10)+10)+10) n q z t H H0 H1 H2 H3 H4).
  applys_eq (Trans1_5 ((((l+10)+10)+10)+10) n q z t H H0 H1 H2 H3 H4); flia.
Qed.

End Prefix16.
End FT7TM16Prefix.

(* Shared definitions from FT7TM16Nonhalt.v. *)
Module FT7TM16Nonhalt.
Import BusyCoq.Individual62.
Import ZifyNat Lia NArith PeanoNat Bool.
Import FT7TM17Rules FT7TM16Cycle FT7TM16Prefix.

Module Nonhalt16.
Import FT7TM17Rules.Rules17 Cycle16 Prefix16.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Definition scale (p:bool) n := Top n 12*(if p then 8 else 4).
Definition Entry (p:bool) l n z t :=
  Config p l n ((if p then R1_1 else R0_1) (Top n 12) z t).
Definition nextn (p:bool) n := n+(if p then 2 else 1).
Definition nextz x t := x*32+t+7.
Definition nextt x z t := x*816+t*4+55-z*12.
Definition Bounds x z t := x*20+2<=z /\ z<=x*24 /\ x*132<=t /\ t<=x*156.
Lemma bounds_next x z t: 3<=x -> Bounds x z t ->
  Bounds (x*8) (nextz x t) (nextt x z t).
Proof. unfold Bounds, nextz, nextt; intros; lia. Qed.
Lemma scale_next p n: scale (negb p) (nextn p n)=scale p n*8.
Proof. destruct p; unfold scale, nextn; rewrite Top_add; unfold Top; cbn [Nat.pow negb]; nia. Qed.
Lemma Top24 n: Top n 24=Top n 12*2.
Proof. unfold Top; lia. Qed.
Lemma entry_shape p l n z t:
  Entry p l n z t = 0inf <{{A}} (if p then LE l else LO l) *>
    G (n+2) (if p then 24 else 12)
      (W1 (scale p n*36) (W0 (z*9) (W1 (t*3) 0inf))).
Proof.
  destruct p; unfold Entry, Config, R0_1, R1_1, scale.
  - rewrite <-Top24, G_app; reflexivity.
  - rewrite Nat.mul_1_r, G_app; reflexivity.
Qed.
Lemma repack p l n z t:
  Config (negb p) l n ((if p then R1_6 else R0_6) (Top n 12) z t) =
  Entry (negb p) l (nextn p n) (nextz (scale p n) t) (nextt (scale p n) z t).
Proof.
  rewrite entry_shape, scale_next.
  destruct p; unfold Config, R0_6, R1_6, nextn, scale, nextz, nextt; cbn [negb].
  - rewrite Nat.mul_1_r, G_app; Cycle16.eqs.
  - rewrite <-Top24, G_app; Cycle16.eqs.
Qed.
Lemma entry_step p l n z t: Bounds (scale p n) z t ->
  Entry p l n z t -->+
  Entry (negb p) (l+50) (nextn p n) (nextz (scale p n) t) (nextt (scale p n) z t).
Proof.
  intros HB; rewrite <-repack; unfold Entry; destruct p; cbn [negb].
  - apply Cycle1; try reflexivity; try apply Top_ge; unfold Bounds, scale in HB; lia.
  - apply Cycle0; try reflexivity; try apply Top_ge; unfold Bounds, scale in HB; lia.
Qed.
Inductive Inv : Q*tape -> Prop :=
| Intro p l n z t: Bounds (scale p n) z t -> Inv (Entry p l n z t).
Lemma Inv_step c: Inv c -> exists c', Inv c' /\ c -->+ c'.
Proof.
  intros H; destruct H as [p l n z t HB].
  eexists; split; [constructor|apply entry_step; exact HB].
  rewrite scale_next; apply bounds_next; [|exact HB].
  unfold scale; pose proof (Top_ge n 12); destruct p; lia.
Qed.
Theorem entry_nonhalt p l n z t: Bounds (scale p n) z t -> ~halts tm (Entry p l n z t).
Proof. intros; eapply progress_nonhalt; [apply Inv_step|constructor; assumption]. Qed.
End Nonhalt16.
End FT7TM16Nonhalt.

(* Shared definitions from FT7TM16ComputeSpec.v. *)
Module FT7TM16ComputeSpec.
Import BusyCoq.Individual62 BusyCoq.Eqb.
Import NArith Lia ZifyNat Bool.
Import FT7TM17Rules FT7Compute FT7ComputeSpec FT7TM17Compute FT7TM17ComputeSpec FT7TM16Cycle FT7TM16Prefix FT7TM16Nonhalt FT7TM16Compute.

Module ComputeSpec16.
Import FT7TM17Rules.Rules17 Compute13 ComputeSpec13 Compute17 ComputeSpec17 Cycle16 Prefix16 Nonhalt16 Compute16.
Local Notation "'nn' n" := (N.to_nat n) (at level 10).
Local Opaque zeros pairs push pop.
Local Opaque N.add N.sub N.mul.

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

Lemma at_stage_spec s t: at_stage s t = true -> config s = stage_config t.
Proof.
  destruct s as [[q l] r], t as [[n p] t]; unfold at_stage.
  destruct q; try discriminate.
  destruct (allzero l) eqn:Hl; try discriminate.
  specialize (pop_spec r) as Hr; destruct (pop r) as [b s]; destruct b; try discriminate.
  destruct (strip (if p then LE (nn n) else LO (nn n)) s) eqn:E; try discriminate.
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
Lemma topN_spec n x: nn (topN n x)=Top n (nn x).
Proof.
  gen x; induction n; intros x; cbn [topN].
  - unfold Top; cbn [Nat.pow]; lia.
  - rewrite IHn, Top_succ; unfold Top; lia.
Qed.
Lemma scaleN_spec p n: nn (scaleN p n)=scale p n.
Proof. unfold scaleN, scale; rewrite N2Nat.inj_mul, topN_spec; destruct p; reflexivity. Qed.
Lemma gN_spec n x r: denote (gN n x r)=G n (nn x) (denote r).
Proof.
  gen x; induction n; intros x; cbn [gN G]; [reflexivity|].
  rewrite pairs_spec, zeros_spec, IHn; unfold Ideal; flia.
Qed.
Lemma target_spec l p n z t:
  stage_config (target l p n z t)=Entry p (nn l) n (nn z) (nn t).
Proof.
  rewrite entry_shape; unfold target; cbn [stage_config].
  rewrite gN_spec, pairs_spec, zeros_spec; cbn [denote].
  rewrite N2Nat.inj_mul, scaleN_spec.
  destruct p; Cycle16.eqs.
Qed.
Lemma boundsb_spec p n z t: boundsb p n z t=true -> Bounds (scale p n) (nn z) (nn t).
Proof.
  unfold boundsb; intros H; unbool.
  rewrite <-scaleN_spec; unfold Bounds; lia.
Qed.
Lemma stage_eqb_spec s t: stage_eqb s t=true -> s=t.
Proof.
  destruct s as [[l p] r], t as [[m q] t]; unfold stage_eqb.
  destruct p,q; intros H; unbool; try discriminate;
    match goal with H: tape_eqb _ _ = true |- _ => apply tape_eqb_spec in H end;
    subst; reflexivity.
Qed.
Lemma reaches_spec count fuel s t: reaches count fuel s t=true ->
  stage_config s -[tm]->* stage_config t.
Proof.
  gen s; induction count; intros s; cbn [reaches]; destruct (stage_eqb s t) eqn:E;
    try solve [intros _; apply stage_eqb_spec in E; subst; apply evstep_refl].
  - discriminate.
  - destruct (stage_step fuel s) eqn:H; try discriminate.
    intros Ht; eapply evstep_trans; [eapply stage_step_spec; eauto|eauto].
Qed.
Theorem checked_nonhalt count fuel s l p n z t:
  reaches count fuel s (target l p n z t)=true ->
  boundsb p n z t=true -> ~halts tm (stage_config s).
Proof.
  intros Hr Hb; eapply multistep_nonhalt; [eapply reaches_spec; exact Hr|].
  rewrite target_spec; apply entry_nonhalt, boundsb_spec, Hb.
Qed.
End ComputeSpec16.
End FT7TM16ComputeSpec.

Import BusyCoq.Individual62.
Import String.
Import FT7TM17Rules FT7TM17Compute FT7TM17ComputeSpec.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply FT7TM17Rules.Rules17.seed_init|].
  change (~halts tm (Compute17.stage_config Compute17.seed)).
  apply (ComputeSpec17.check_stages_spec 42 2048 Compute17.seed).
  native_compute; reflexivity.
Qed.
End TM17.

Module TM19.
Import BusyCoq.Individual62 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia NArith String.

Import TM17.FT7TM17Rules.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC0RA_1LD1RE_1LA0LD_1RA0LF_1LD---").
Definition rename q := match q with A=>D | B=>A | C=>B | D=>C | E=>E | F=>F end.
Lemma perm: Perm TM17.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Fixpoint chunks n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm n3 c
  | S n1 => match multistep_c tm n2 c with
            | Some c => chunks n1 n2 n3 c
            | None => None
            end
  end.
Lemma chunks_spec n1 n2 n3 c c': chunks n1 n2 n3 c = Some c' -> c -[tm]->* c'.
Proof.
  gen c; induction n1; intros c; cbn [chunks].
  - intros H; apply multistep_c_spec in H; eapply without_counter; exact H.
  - destruct (multistep_c tm n2 c) eqn:H; try discriminate.
    apply multistep_c_spec in H; intros H'.
    eapply evstep_trans; [eapply without_counter; exact H|apply IHn1; exact H'].
Qed.
Lemma init: c0 -[tm]->* 0inf <{{D}} Rules17.LO 46 *> Rules17.C 36 43 (Rules17.E 159).
Proof.
  apply (chunks_spec 845 846 255).
  native_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (@perm_nonhalt' TM17.tm tm rename A _); [apply perm|].
  apply Rules17.region_nonhalt, Rules17.IO; try lia.
  apply Rules17.Good_tail; lia.
Qed.
End TM19.

Module TM16.
Import BusyCoq.Individual62.
Import NArith String.
Import TM17.FT7TM17Rules FT7Compute TM17.FT7TM17Compute TM17.FT7TM16Compute TM17.FT7TM16ComputeSpec.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD0RE_0RA0RC_1RC0LF_1LB---").
Definition rename q := match q with A=>B | B=>C | C=>D | D=>A | E=>E | F=>F end.
Lemma perm: Perm TM17.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.

Lemma init: (D,snd c0) -[TM17.tm]->* Compute17.stage_config Compute16.seed.
Proof.
  apply (ComputeSpec16.seek_spec 20000 256 (D,nil,Compute13.Blank) Compute16.seed).
  native_compute; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (@perm_nonhalt' TM17.tm tm rename D _); [apply perm|].
  eapply multistep_nonhalt; [apply init|].
  apply (ComputeSpec16.checked_nonhalt 580 4096 Compute16.seed 5944%N false 117
    30119251419673895931027391474996164521916877933726321544322199749607594450%N
    184994257267974893945090611672377262990398332994181268136611579109978997219%N);
    native_compute; reflexivity.
Qed.
End TM16.

Module TM18.
Import BusyCoq.Individual62.
Import NArith String.
Import TM17.FT7TM17Rules FT7Compute TM17.FT7TM17Compute TM17.FT7TM17ComputeSpec.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC0RA_0RD0RB_1LE1RA_1LB0LE_1LE---").
Definition rename q := match q with A=>E | B=>B | C=>C | D=>D | E=>A | F=>F end.
Lemma perm: Perm TM17.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.

Definition seed : Compute17.Stage := (85%N,false,
  Compute13.Pairs 108 (Compute13.Zeros 438 (Compute13.Pairs 622
  (Compute13.Zeros 1 (Compute13.Pairs 416 (Compute13.Zeros 1 (Compute13.Pairs 1030 Compute13.Blank))))))).
Lemma init: (E,snd c0) -[TM17.tm]->* Compute17.stage_config seed.
Proof.
  apply (TM17.FT7TM17Rules.Rules17.seed_chunks_spec 3113 3114 1363).
  native_compute; simpl_tape; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply (@perm_nonhalt' TM17.tm tm rename E _); [apply perm|].
  eapply multistep_nonhalt; [apply init|].
  apply (ComputeSpec17.check_stages_spec 1129 4096 seed).
  native_compute; reflexivity.
Qed.
End TM18.
