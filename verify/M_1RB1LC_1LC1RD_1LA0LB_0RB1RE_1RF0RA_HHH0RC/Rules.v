From BusyCoq Require Import Individual62.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Visits.
Require Import Lia List String PeanoNat Arith.
Import Nat.
Open Scope sym_scope.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC"%string).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma shD j l r : l {{D}}> [0;1]^^j *> r -->* l <* [1;0]^^j {{D}}> r.
Proof.
  revert l. induction j; intros l.
  - finish.
  - cbn [lpow]. rewrite Str_app_assoc. do 2 step.
    follow IHj. apply evstep_refl'. change (1 >> 0 >> l) with ([1;0] *> l). rewrite lpow_shift'. reflexivity.
Qed.

Lemma shC j l r : l <* [0;1]^^j {{C}}> [1] *> r -->* l {{C}}> [1] *> [1;0]^^j *> r.
Proof.
  revert r. induction j; intros r.
  - finish.
  - cbn [lpow]. rewrite Str_app_assoc. do 2 step.
    eapply evstep_trans; [apply (IHj ([1;0] *> r))|]. apply evstep_refl'. rewrite lpow_shift'. reflexivity.
Qed.

Lemma shC2 j l r : l <* [1;0]^^j {{C}}> [0] *> r -->* l {{C}}> [0] *> [1;1]^^j *> r.
Proof.
  revert r. induction j; intros r.
  - finish.
  - cbn [lpow]. rewrite Str_app_assoc. do 2 step.
    eapply evstep_trans; [apply (IHj ([1;1] *> r))|]. apply evstep_refl'. rewrite lpow_shift'. reflexivity.
Qed.

Lemma rot0 j (X : side) : 0 >> [1;0]^^j *> X = [0;1]^^j *> 0 >> X.
Proof. induction j; [reflexivity|]. cbn [lpow]. rewrite !Str_app_assoc. cbn. rewrite IHj. reflexivity. Qed.
Lemma rot1 j (X : side) : 1 >> [0;1]^^j *> X = [1;0]^^j *> 1 >> X.
Proof. induction j; [reflexivity|]. cbn [lpow]. rewrite !Str_app_assoc. cbn. rewrite IHj. reflexivity. Qed.
Lemma ones_S n (X : side) : [1]^^n *> 1 >> X = [1]^^(S n) *> X.
Proof. induction n; [reflexivity|]. cbn [lpow]. cbn. rewrite IHn. reflexivity. Qed.
Lemma cons1 n (X : side) : 1 >> [1]^^n *> X = [1]^^(S n) *> X.
Proof. reflexivity. Qed.
Lemma ones_add n m (X : side) : [1]^^n *> [1]^^m *> X = [1]^^(n + m) *> X.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.
Lemma tt_ones j (X : side) : [1;1]^^j *> X = [1]^^(2 * j) *> X.
Proof.
  induction j; [reflexivity|]. replace (2 * S j) with (S (S (2 * j))) by lia.
  cbn [lpow]. rewrite Str_app_assoc, IHj. reflexivity.
Qed.

(** Frames (blank tape around):
    b: 1^l B> 10 (10)^j 1^r     a: 1^l (10)^j 110 A> 1^r     c: 1^l 0 C> 0 (10)^j 1^r
    d: 1^l A> 01 (10)^j 1^r     e: 1^l (10)^j B>              f: 1^l (10)^j 1101 B>       *)
Definition Fb l j r := 0inf <* [1]^^l {{B}}> [1;0] *> [1;0]^^j *> [1]^^r *> 0inf.
Definition Fa l j r := 0inf <* [1]^^l <* [0;1]^^j <* [0;1;1] {{A}}> [1]^^r *> 0inf.
Definition Fc l j r := 0inf <* [1]^^l <* [0] {{C}}> [0] *> [1;0]^^j *> [1]^^r *> 0inf.
Definition Fd l j r := 0inf <* [1]^^l {{A}}> [0;1] *> [1;0]^^j *> [1]^^r *> 0inf.
Definition Fe l j := 0inf <* [1]^^l <* [0;1]^^j {{B}}> 0inf.
Definition Ff l j := 0inf <* [1]^^l <* [0;1]^^j <* [1;0;1;1] {{B}}> 0inf.

Ltac fin := apply evstep_refl';
  repeat (rewrite <- ?rot1, <- ?rot0); repeat rewrite ?Str_app_assoc; repeat rewrite ?tt_ones;
  repeat rewrite ?cons1, ?ones_S, ?ones_add; try reflexivity; lia_refl.
Ltac rwl := match goal with |- ?c -->* ?d =>
  let X := fresh "X" in let HX := fresh "HX" in remember d as X eqn:HX; (rewrite rot1 || rewrite rot0); subst X end.
Ltac rwl0 := match goal with |- ?c -->* ?d =>
  let X := fresh "X" in let HX := fresh "HX" in remember d as X eqn:HX; rewrite rot0; subst X end.
Ltac lhs_simpl := match goal with |- ?c -->* ?d =>
  let X := fresh "X" in let HX := fresh "HX" in remember d as X eqn:HX; cbn [Str_app app lpow]; subst X end.
Ltac go := repeat (try solve [fin]; first [follow shC2 | follow shD | follow shC | step]).
Ltac piece := unfold Fa, Fb, Fc, Fd, Fe, Ff; lhs_simpl; try rwl0; go.
Ltac piece_e := unfold Fa, Fb, Fc, Fd, Fe, Ff; lhs_simpl; step; rwl; go.

Lemma pc_b0 l j : Fb l j 0 -->* Fe l (S j).          Proof. piece. Qed.
Lemma pc_b1 l j : Fb l j 1 -->* Fe l (S (S j)).      Proof. piece. Qed.
Lemma pc_b3 l j : Fb l j 3 -->* Ff l (S j).          Proof. piece. Qed.
Lemma pc_b4 l j r : Fb l j (S (S (S (S r)))) -->* Fa l (S j) (S r). Proof. piece. Qed.
Lemma pc_a0 l j : Fa l j 0 -->* Ff l j.              Proof. piece. Qed.
Lemma pc_a1 j r : Fa 0 j (S r) -->* Fd 0 (S j) (S (S (S r))). Proof. piece. Qed.
Lemma pc_a2 l j r : Fa (S l) j (S r) -->* Fb l j (S (S (S r))). Proof. piece. Qed.
Lemma pc_c0 l r : Fc l 0 r -->* Fd l 0 r.            Proof. piece. Qed.
Lemma pc_c1 l j : Fc l (S j) 0 -->* Fd l j 1.        Proof. piece. Qed.
Lemma pc_c2 l j r : Fc l (S j) (S r) -->* Fd l (S j) (S r). Proof. piece. Qed.
Lemma pc_d0 l : Fd l 0 0 -->* Fe (S l) 1.            Proof. piece. Qed.
Lemma pc_d2 l : Fd l 0 2 -->* Ff (S l) 0.            Proof. piece. Qed.
Lemma pc_d3 l r : Fd l 0 (S (S (S r))) -->* Fa (S l) 0 (S r). Proof. piece. Qed.
Lemma pc_d5 l : Fd l 1 1 -->* Fc (4 + l) 0 0.        Proof. piece. Qed.
Lemma pc_d6 l : Fd l 1 2 -->* Fb (2 + l) 0 1.        Proof. piece. Qed.
Lemma pc_d7 l r : Fd l 1 (S (S (S r))) -->* Fb (2 + l) 1 (S r). Proof. piece. Qed.
Lemma pc_d8 l r : Fd l 2 r -->* Fc (4 + l) 0 r.      Proof. piece. Qed.
Lemma pc_d9 l j : Fd l (S (S (S j))) 0 -->* Fc (4 + l) j 1. Proof. piece. Qed.
Lemma pc_d10 l j r : Fd l (S (S (S j))) (S r) -->* Fc (4 + l) (S j) (S r). Proof. piece. Qed.
Lemma pc_e0a : Fe 0 0 -->* Fd 0 0 1.                 Proof. piece. Qed.
Lemma pc_e0b j : Fe 0 (S j) -->* Fd 0 0 (2 * j + 3). Proof. piece_e. Qed.
Lemma pc_e1a : Fe 1 0 -->* Fd 0 1 1.                 Proof. piece. Qed.
Lemma pc_e1b j : Fe 1 (S j) -->* Fd 0 1 (2 * j + 3). Proof. piece_e. Qed.
Lemma pc_e2a l : Fe (S (S l)) 0 -->* Fb l 0 1.       Proof. piece. Qed.
Lemma pc_e2b l j : Fe (S (S l)) (S j) -->* Fb l 0 (2 * j + 3). Proof. piece_e. Qed.
Lemma pc_f0 l : Ff l 0 -->* Fb l 1 1.                Proof. piece. Qed.
Lemma pc_f1 l j : Ff l (S j) -->* Fe l (4 + j).      Proof. piece. Qed.

(** The three halting frames and the start. *)
Lemma halted_F l : halted tm (l {{F}}> 0inf).
Proof. reflexivity. Qed.
Lemma pc_b2 l j : halts tm (Fb l j 2).
Proof.
  eapply halts_evstep; [apply halted_halts, (halted_F (0inf <* [1]^^l <* [1] <* [1;0]^^j <* [1;1;1;0]))|].
  piece.
Qed.
Lemma pc_d1 l : halts tm (Fd l 0 1).
Proof. eapply halts_evstep; [apply halted_halts, (halted_F (0inf <* [1]^^l <* [1;1;1;1]))|]. piece. Qed.
Lemma pc_d4 l : halts tm (Fd l 1 0).
Proof. eapply halts_evstep; [apply halted_halts, (halted_F (0inf <* [1]^^l <* [1;1;1;1]))|]. piece. Qed.
Lemma pc_init : c0 -->* Fe 1 0.
Proof. unfold Fe. step. finish. Qed.

(** * The rules on A(a, b) *)
Ltac tr H := eapply evstep_trans; [apply H|].
Ltac feq := apply evstep_refl'; f_equal; lia.

Lemma loop_ba k : forall l j r, Fb (k + l) j (k + S (S (S r))) -->* Fb l (k + j) (S (S (S r))).
Proof.
  induction k; intros l j r; [finish|].
  replace (S k + S (S (S r))) with (S (S (S (S (k + r))))) by lia.
  tr pc_b4. tr pc_a2.
  replace (S (S (S (k + r)))) with (k + S (S (S r))) by lia.
  tr IHk. feq.
Qed.

Lemma loop_cd k : forall l j r, Fc l (j + 2 * k + 1) (S r) -->* Fc (l + 4 * k) (S j) (S r).
Proof.
  induction k; intros l j r.
  - replace (j + 2 * 0 + 1) with (S j) by lia. replace (l + 4 * 0) with l by lia. finish.
  - replace (j + 2 * S k + 1) with (S (S (S (j + 2 * k)))) by lia.
    tr pc_c2. tr pc_d10.
    replace (S (j + 2 * k)) with (j + 2 * k + 1) by lia.
    tr IHk. feq.
Qed.

(** The visit A(a, b) = 0^inf 1^a 0 C> 1^b 0^inf, as a frame (three or five steps before it). *)
Definition V (a b : nat) := match a with S (S a') => Fb a' 1 (b - 1) | _ => Fd 0 2 (b - 1) end.

Lemma r_b2 n : V (n + 4) 2 -->* V (n + 1) 7.
Proof.
  replace (n + 4) with (S (S (S (S n)))) by lia. cbn [V Nat.sub].
  tr pc_b1. change (S (S 1)) with (S 2). tr pc_e2b. cbn [Nat.mul Nat.add].
  tr pc_b4. destruct n as [|n].
  - tr pc_a1. finish.
  - tr pc_a2. replace (S n + 1) with (S (S n)) by lia. finish.
Qed.

Lemma r_ge c d : V (d + c + 4) (c + 4) -->* V (d + 1) (2 * c + 11).
Proof.
  replace (d + c + 4) with (S (S (c + S (S d)))) by lia. cbn [V].
  replace (c + 4 - 1) with (c + S (S (S 0))) by lia.
  tr (loop_ba c (S (S d)) 1 0).
  tr pc_b3. tr pc_f1. replace (4 + (c + 1)) with (S (c + 4)) by lia. tr pc_e2b.
  replace (2 * (c + 4) + 3) with (S (S (S (S (2 * c + 7))))) by lia.
  tr pc_b4. destruct d as [|d].
  - tr pc_a1. cbn [V Nat.add]. feq.
  - tr pc_a2. replace (S d + 1) with (S (S d)) by lia. cbn [V]. feq.
Qed.

Lemma r_p1 n : V (n + 3) (n + 4) -->* V 4 (2 * n + 10).
Proof.
  replace (n + 3) with (S (S (n + 1))) by lia. cbn [V].
  replace (n + 4 - 1) with (n + S (S (S 0))) by lia.
  tr (loop_ba n 1 1 0).
  tr pc_b3. tr pc_f1. replace (4 + (n + 1)) with (S (n + 4)) by lia. tr pc_e1b.
  replace (2 * (n + 4) + 3) with (S (S (S (2 * n + 8)))) by lia.
  tr pc_d7. cbn [V]. feq.
Qed.

Lemma r_p2 n : V (n + 2) (n + 4) -->* V 1 (2 * n + 11).
Proof.
  replace (n + 2) with (S (S (n + 0))) by lia. cbn [V].
  replace (n + 4 - 1) with (n + S (S (S 0))) by lia.
  tr (loop_ba n 0 1 0).
  tr pc_b3. tr pc_f1. replace (4 + (n + 1)) with (S (n + 4)) by lia. tr pc_e0b.
  replace (2 * (n + 4) + 3) with (S (S (S (2 * n + 8)))) by lia.
  tr pc_d3. tr pc_a2.
  replace (S (S (S (2 * n + 8)))) with (S (S (S (S (2 * n + 7))))) by lia.
  tr pc_b4. tr pc_a1. cbn [V]. feq.
Qed.

Lemma r_de m s : V (2 * m + 2) (s + 2 * m + 5) -->* V (4 * m + 8) (s + 2).
Proof.
  replace (2 * m + 2) with (S (S (2 * m + 0))) by lia. replace (4 * m + 8) with (S (S (4 * m + 6))) by lia.
  cbn [V].
  replace (s + 2 * m + 5 - 1) with (2 * m + S (S (S (S s)))) by lia.
  tr (loop_ba (2 * m) 0 1 (S s)).
  replace (S (S (S (S s)))) with (S (S (S (S s)))) by lia. tr pc_b4. tr pc_a1.
  replace (S (S (2 * m + 1))) with (S (S (S (2 * m)))) by lia.
  tr pc_d10. replace (S (2 * m)) with (0 + 2 * m + 1) by lia.
  tr (loop_cd m 4 0 (S (S s))). tr pc_c2. tr pc_d7. feq.
Qed.

Lemma r_do m s : V (2 * m + 3) (s + 2 * m + 7) -->* V (4 * m + 9) (s + 4).
Proof.
  replace (2 * m + 3) with (S (S (2 * m + 1 + 0))) by lia. replace (4 * m + 9) with (S (S (4 * m + 7))) by lia.
  cbn [V].
  replace (s + 2 * m + 7 - 1) with ((2 * m + 1) + S (S (S (S (S s))))) by lia.
  tr (loop_ba (2 * m + 1) 0 1 (S (S s))). tr pc_b4. tr pc_a1.
  replace (S (S (2 * m + 1 + 1))) with (S (S (S (2 * m + 1)))) by lia.
  tr pc_d10. replace (S (2 * m + 1)) with (1 + 2 * m + 1) by lia.
  tr (loop_cd m 4 1 (S (S (S s)))). tr pc_c2. tr pc_d8. tr pc_c0. tr pc_d3. tr pc_a2. tr pc_b4. tr pc_a2. feq.
Qed.

Lemma r_do1 s : V 1 (s + 5) -->* V 5 (s + 4).
Proof.
  cbn [V]. replace (s + 5 - 1) with (S (S (S (S s)))) by lia. replace (s + 4 - 1) with (S (S (S s))) by lia.
  tr pc_d8. tr pc_c0. tr pc_d3. tr pc_a2. tr pc_b4. tr pc_a2. finish.
Qed.

Lemma r_p3 m : V (2 * m + 3) (2 * m + 6) -->* V (4 * m + 7) 9.
Proof.
  replace (2 * m + 3) with (S (S (2 * m + 1 + 0))) by lia. replace (4 * m + 7) with (S (S (4 * m + 5))) by lia.
  cbn [V].
  replace (2 * m + 6 - 1) with ((2 * m + 1) + S (S (S (S 0)))) by lia.
  tr (loop_ba (2 * m + 1) 0 1 1). tr pc_b4. tr pc_a1.
  replace (S (S (2 * m + 1 + 1))) with (S (S (S (2 * m + 1)))) by lia.
  tr pc_d10. replace (S (2 * m + 1)) with (1 + 2 * m + 1) by lia.
  tr (loop_cd m 4 1 2). tr pc_c2. tr pc_d8. tr pc_c0. tr pc_d3. tr pc_a2. tr pc_b3. tr pc_f1. tr pc_e2b.
  cbn [Nat.mul Nat.add]. tr pc_b4. tr pc_a2. feq.
Qed.

Lemma r_p3_1 : V 1 4 -->* V 3 9.
Proof. cbn [V Nat.sub]. tr pc_d8. tr pc_c0. tr pc_d3. tr pc_a2. tr pc_b3. tr pc_f1. tr pc_e2b. cbn [Nat.mul Nat.add]. tr pc_b4. tr pc_a2. finish. Qed.

Lemma start : c0 -->* V 2 9.
Proof.
  tr pc_init. tr pc_e1a. tr pc_d5. tr pc_c0. tr pc_d0. tr pc_e2b. tr pc_b3. tr pc_f1. tr pc_e2b.
  cbn [Nat.mul Nat.add]. tr pc_b4. tr pc_a2. finish.
Qed.

(** * The map on visits, and halting *)
Close Scope sym_scope.
Open Scope nat_scope.
Definition dom (a b : nat) : Prop := 1 <= a /\ 2 <= b /\ (b <> 2 \/ 4 <= a) /\ (b <> 3 \/ 2 <= a).

Ltac finr H := eapply evstep_trans; [apply H|]; apply evstep_refl'; f_equal; lia.

Lemma op_step a b a' b' : dom a b -> op (a, b) = Some (a', b') -> dom a' b' /\ V a b -->* V a' b'.
Proof.
  intros (H1 & H2 & H3 & H4) E. unfold op in E.
  destruct (Nat.eqb_spec b 3) as [|N3]; [discriminate|].
  destruct (Nat.eqb_spec b 2) as [->|N2].
  { injection E as <- <-. destruct H3 as [H3|H3]; [lia|]. split; [unfold dom; lia|].
    pose (n := a - 4). assert (Ha : a = n + 4) by lia. clearbody n. subst a. finr r_b2. }
  destruct (Nat.leb_spec b a) as [Le|Lt].
  { injection E as <- <-. split; [unfold dom; lia|].
    pose (c := b - 4). pose (d := a - b). assert (Ha : a = d + c + 4) by lia. assert (Hb : b = c + 4) by lia.
    clearbody c d. subst a b. finr r_ge. }
  destruct (Nat.eqb_spec b (a + 1)) as [->|N4].
  { injection E as <- <-. split; [unfold dom; lia|].
    pose (n := a - 3). assert (Ha : a = n + 3) by lia. clearbody n. subst a.
    replace (n + 3 + 1) with (n + 4) by lia. finr r_p1. }
  destruct (Nat.eqb_spec b (a + 2)) as [->|N5].
  { injection E as <- <-. split; [unfold dom; lia|].
    pose (n := a - 2). assert (Ha : a = n + 2) by lia. clearbody n. subst a.
    replace (n + 2 + 2) with (n + 4) by lia. finr r_p2. }
  destruct (Nat.even a) eqn:Ev.
  { injection E as <- <-. split; [unfold dom; lia|].
    apply Nat.even_spec in Ev as [m Hm].
    pose (k := m - 1). pose (s := b - a - 3). assert (Ha : a = 2 * k + 2) by lia.
    assert (Hb : b = s + 2 * k + 5) by lia. clearbody k s. clear Hm. subst a b. finr r_de. }
  assert (Od : Nat.Odd a) by (apply Nat.odd_spec; rewrite <- Nat.negb_even, Ev; reflexivity).
  destruct Od as [m Hm]. subst a.
  destruct (Nat.eqb_spec b (2 * m + 1 + 3)) as [->|N7].
  { injection E as <- <-. split; [unfold dom; lia|]. destruct m as [|m].
    - apply r_p3_1.
    - replace (2 * S m + 1) with (2 * m + 3) by lia. replace (2 * m + 3 + 3) with (2 * m + 6) by lia. finr r_p3. }
  injection E as <- <-. split; [unfold dom; lia|]. destruct m as [|m].
  - pose (s := b - 5). assert (Hb : b = s + 5) by lia. clearbody s. subst b. finr r_do1.
  - replace (2 * S m + 1) with (2 * m + 3) by lia.
    pose (s := b - 2 * m - 7). assert (Hb : b = s + 2 * m + 7) by lia. clearbody s. subst b. finr r_do.
Qed.

Lemma op_none a b : dom a b -> op (a, b) = None -> halts tm (V a b).
Proof.
  intros (H1 & H2 & H3 & H4) E. unfold op in E.
  destruct (Nat.eqb_spec b 3) as [->|].
  - destruct H4 as [H4|H4]; [lia|]. destruct a as [|[|a]]; try lia. apply pc_b2.
  - repeat match type of E with context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

Lemma orbit k : forall a b, opIter k (2, 9) = Some (a, b) -> dom a b /\ c0 -->* V a b.
Proof.
  enough (G : forall x a b, dom (fst x) (snd x) -> c0 -->* V (fst x) (snd x) ->
    opIter k x = Some (a, b) -> dom a b /\ c0 -->* V a b).
  { intros a b H. apply (G (2, 9)); [unfold dom; cbn; lia|apply start|exact H]. }
  induction k as [|k IH]; intros [a0 b0] a b D R H; cbn [fst snd opIter] in *.
  - injection H as <- <-. auto.
  - destruct (op (a0, b0)) as [[a1 b1]|] eqn:E; [|discriminate].
    destruct (op_step a0 b0 a1 b1 D E) as [D1 R1].
    apply (IH (a1, b1)); cbn; [exact D1|eapply evstep_trans; eauto|exact H].
Qed.

Theorem halts_of_orbit k a : opIter k (2, 9) = Some (a, 3) -> halts tm c0.
Proof.
  intros H. destruct (orbit k a 3 H) as [D R]. eapply halts_evstep; [|exact R].
  apply op_none; [exact D|]. reflexivity.
Qed.
