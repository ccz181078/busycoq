From BusyCoq Require Import Individual62 ES_v3 Longitudinal.
Require Import String List Lia ZifyNat PeanoNat Wf_nat.
Import ListNotations.

(* Fractal-in-bouncer TM3: every positive odd singleton has a finite,
   positive return to a positive odd singleton. The intermediate periodic
   families are kept separate; no closure for arbitrary odd run lists is used. *)
Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Definition S a := 0inf <{{A}} [1]^^a *> 0inf.

Lemma C_ones n l r:
  l {{C}}> [1]^^n *> r -->* l <* [1]^^n {{C}}> r.
Proof. es' n & l r. Qed.

Lemma B_scan n l r:
  l {{B}}> [0] *> [1]^^n *> r -->* l <* [1]^^(1+n) {{C}}> r.
Proof. es' n & l r. Qed.

Lemma C_scan n l r:
  l {{C}}> [0] *> [1]^^n *> r -->* l <* [1]^^n <* [0] {{D}}> r.
Proof. es' n & l r. Qed.

Lemma D_ones n l r:
  l <* [0] {{D}}> [1]^^n *> r -->* l <* [1]^^n <* [0] {{D}}> r.
Proof. es' n & l r. Qed.

Lemma D_odd n l r:
  l <* [0] {{D}}> [0] *> [1]^^(1+n*2) *> r -->*
  l <* [1] <* <[1;0]^^(1+n) {{B}}> r.
Proof. es' n & l r. Qed.

Lemma E_odd n l r:
  l {{E}}> [1]^^(1+n*2) *> [0] *> r -->*
  l <* <[0;1]^^(1+n) {{C}}> r.
Proof. es' n & l r. Qed.

Lemma B_even n l r:
  l <* [1]^^(n*2) <{{B}} [0] *> r -->*
  l <{{B}} [0] *> [1]^^(n*2) *> r.
Proof. es' n & l r. Qed.

Lemma return_pair n l r:
  l <* [0] <* [1]^^(1+n*2) <* <[0;1] <{{A}} r -->*
  l <{{A}} [1]^^(3+n*2) *> [0] *> r.
Proof. es' n & l r. Qed.

Lemma return_bridge n l r:
  l <* [0] <* [1]^^(1+n*2) <* [0] <{{E}} r -->*
  l <{{A}} [1]^^(3+n*2) *> r.
Proof. es' n & l r. Qed.

Lemma even_A_pair n l r:
  l <* [0] <* [1]^^(2+n*2) <* <[0;1] <{{A}} r -->*
  l <* [1]^^(5+n*2) {{E}}> r.
Proof. es' n & l r. Qed.

Lemma D_last n l r:
  l <* [0] {{D}}> [1]^^(1+n) *> r -->*
  l <* [1]^^(1+n) {{C}}> [0] *> r.
Proof.
  replace (1+n) with (n+1) by lia.
  rewrite lpow_add, Str_app_assoc.
  follow (D_ones n l ([1] *> r)); es.
Qed.

Lemma absorb_zero n l:
  l <* <[1;0] <* [1]^^(n*2) {{C}}> 0inf -->*
  l <* [1]^^(4+n*2) {{C}}> 0inf.
Proof.
  eapply evstep_trans with (c':=l <* <[1;1;0] {{D}}> [1]^^(2+n*2) *> 0inf).
  - es' n & l.
  - follow (D_last (1+n*2) (l <* [1;1]) 0inf); simpl_tape; finish.
    now rewrite !lpow_shift1.
Qed.

Lemma odd_transfer n l:
  l <* <[1;1;0] <* [1]^^(1+n*2) {{C}}> 0inf -->*
  l <* [0] <* [1]^^(6+n*2) {{C}}> 0inf.
Proof. es' n & l. Qed.

Lemma odd_release n l:
  l <* <[1;0] <* [1]^^(1+n*2) {{C}}> 0inf -->*
  l <{{E}} [0] *> [1]^^(5+n*2) *> 0inf.
Proof. es' n & l. Qed.

Lemma finish_odd n:
  0inf <* [1]^^(1+n*2) {{C}}> 0inf -->+ S (5+n*2).
Proof. unfold S; es' n. Qed.

Lemma finish_even n:
  0inf <* [1]^^(2+n*2) {{C}}> 0inf -->+ S (9+n*2).
Proof. unfold S; es' n. Qed.

Lemma init: c0 -->* S 9.
Proof. unfold S; esx. Qed.

(* An even accumulator absorbs one positive run. Its parity only depends
   on the parity of the absorbed run, not on any unread left context. *)
Lemma absorb_run a b l:
  l <* [1]^^(1+b) <* [0] <* [1]^^(a*2) {{C}}> 0inf -->*
  l <* [1]^^(4+a*2+b) {{C}}> 0inf.
Proof.
  applys_eq (absorb_zero a (l <* [1]^^b)); simpl_tape;
    rewrite ?lpow_shift1, ?lpow_add'; flia.
Qed.

(* The parameters of Post are half-runs: x denotes the positive odd run
   1+2*x. Thus no parity test is needed inside the list induction. *)
Fixpoint Post (xs : list nat) : list Sym :=
  match xs with
  | [] => []
  | x::xs => [1]^^(1+x*2) ++ [0] ++ Post xs
  end.
Fixpoint mass (xs : list nat) : nat :=
  match xs with [] => 0 | x::xs => x+2+mass xs end.

Lemma Post_app xs ys: Post (xs++ys) = Post xs ++ Post ys.
Proof.
  induction xs as [|x xs IH]; cbn [Post app]; [reflexivity|].
  rewrite IH, <- app_assoc; reflexivity.
Qed.

Lemma rev_ones n: rev ([1]^^n) = [1]^^n.
Proof. induction n; cbn; [reflexivity|rewrite IHn; exact (lpow_shift [1] n)]. Qed.

Lemma even_absorb_list xs a l:
  l <* (rev (Post xs)) <* [1]^^(a*2) {{C}}> 0inf -->*
  l <* [1]^^((a+mass xs)*2) {{C}}> 0inf.
Proof.
  revert a l; induction xs as [|x xs IH]; intros a l.
  - cbn [Post mass]; finish.
  - cbn [Post mass]; rewrite !rev_app_distr, rev_ones; simpl_tape.
    follow (IH a (l <* [1]^^(1+x*2) <* [0])).
    applys_eq (absorb_run (a+mass xs) (x*2) l); flia.
Qed.

Lemma even_absorb_power n xs a l:
  l <* (rev (Post xs))^^n <* [1]^^(a*2) {{C}}> 0inf -->*
  l <* [1]^^((a+n*mass xs)*2) {{C}}> 0inf.
Proof.
  revert a l; induction n; intros a l.
  - cbn; finish.
  - cbn [lpow]; rewrite Str_app_assoc.
    follow (even_absorb_list xs a (l <* (rev (Post xs))^^n)).
    applys_eq (IHn (a+mass xs) l); flia.
Qed.

Lemma A_first7 n l r:
  l {{A}}> [0] *> [1]^^(7+n*12) *> [0] *> r -->*
  l <* [0] <* <[1;1;1;1;1;1;1;1;1;0;1;0]^^n
    <* [1]^^7 <* [0] {{D}}> r.
Proof. es' n & l r. Qed.

Fixpoint Pairs (xs : list nat) : list Sym :=
  match xs with
  | [] => []
  | x::xs => [0] ++ [1]^^(1+x*2) ++ [0;1] ++ Pairs xs
  end.

Lemma Pairs_cons x xs:
  rev (Pairs (x::xs)) = rev (Pairs xs) ++ <[0;1] ++ [1]^^(1+x*2) ++ [0].
Proof. cbn [Pairs]; rewrite !rev_app_distr, rev_ones, !app_assoc; reflexivity. Qed.

Lemma A_return_list xs l r:
  l <* (rev (Pairs xs)) <{{A}} r -->*
  l <{{A}} Post (map (fun x => 1+x) xs) *> r.
Proof.
  revert l r; induction xs as [|x xs IH]; intros l r.
  - cbn [Pairs Post map]; finish.
  - cbn [Pairs Post map]; rewrite !rev_app_distr, rev_ones; simpl_tape.
    follow (IH (l <* [0] <* [1]^^(1+x*2) <* <[0;1]) r).
    applys_eq (return_pair x l (Post (map (fun x => 1+x) xs) *> r));
      simpl_tape; flia.
Qed.

Lemma C_recover_one x a l:
  l <* [0] <* [1]^^(1+x*2) <* <[0;1;0]
    <* [1]^^(1+a*2) {{C}}> 0inf -->*
  l <{{A}} [1]^^(3+x*2) *> [0] *> [1]^^(5+a*2) *> 0inf.
Proof.
  follow (odd_release a (l <* [0] <* [1]^^(1+x*2) <* [0])).
  apply return_bridge.
Qed.

Lemma C_recover_list x xs a l:
  l <* (rev (Pairs (x::xs))) <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  l <{{A}} Post (map (fun x => 1+x) (x::xs)) *> [1]^^(5+a*2) *> 0inf.
Proof.
  revert x l; induction xs as [|y xs IH]; intros x l.
  - cbn [Pairs Post map]; rewrite !rev_app_distr, rev_ones; simpl_tape.
    applys_eq (C_recover_one x a l); simpl_tape; flia.
  - rewrite Pairs_cons, !Str_app_assoc.
    follow (IH y (l <* [0] <* [1]^^(1+x*2) <* <[0;1])).
    applys_eq (return_pair x l
      (Post (map (fun x => 1+x) (y::xs)) *> [1]^^(5+a*2) *> 0inf));
      cbn [Post map]; simpl_tape; flia.
    simpl_tape; reflexivity.
Qed.

Lemma odd_recover_list xs a:
  0inf <* (rev (Pairs xs)) <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  0inf <{{A}} Post (map (fun x => 1+x) xs) *> [1]^^(5+a*2) *> 0inf.
Proof.
  destruct xs as [|x xs].
  - cbn [Pairs Post map]; simpl_tape; apply progress_evstep, finish_odd.
  - apply C_recover_list.
Qed.

Definition Field x := [0] ++ [1]^^(1+x*2).
Fixpoint TripleWord (ts : list (nat*nat*nat)) : list Sym :=
  match ts with
  | [] => []
  | (a,b,c)::ts => Field a ++ Field b ++ Field c ++ TripleWord ts
  end.
Fixpoint triple_mass (ts : list (nat*nat*nat)) : nat :=
  match ts with [] => 0 | (a,b,c)::ts => 4+a*2+b+c+triple_mass ts end.

Lemma D_pair u v l r:
  l <* [0] {{D}}> Field u *> Field v *> r -->*
  l <* [1] <* (rev (Post [0%nat]))^^(1+u) <* [1]^^(2+v*2) {{C}}> r.
Proof. cbn [Field Post]; follow (D_odd u l (Field v *> r)); apply B_scan. Qed.

Lemma D_triple a b c l r:
  l <* [0] {{D}}> Field a *> Field b *> Field c *> r -->*
  l <* [1] <* (rev (Post [0%nat]))^^(1+a)
    <* [1]^^(3+(b+c)*2) <* [0] {{D}}> r.
Proof.
  follow (D_pair a b l (Field c *> r)).
  applys_eq (C_scan (1+c*2)
    (l <* [1] <* (rev (Post [0%nat]))^^(1+a) <* [1]^^(2+b*2)) r);
    cbn [Field]; rewrite ?lpow_add'; flia.
Qed.

Lemma D_sweep ts u v l:
  l <* [0] {{D}}> TripleWord ts *> Field u *> Field v *> 0inf -->*
  l <* [1]^^(7+(u*2+v+triple_mass ts)*2) {{C}}> 0inf.
Proof.
  revert l; induction ts as [|[[a b] c] ts IH]; intros l.
  - cbn [TripleWord triple_mass]; follow (D_pair u v l 0inf).
    follow (even_absorb_power (1+u) [0%nat] (1+v) (l <* [1])).
    change (l <* [1]) with (l <* [1]^^1).
    rewrite lpow_add'; cbn [mass]; finish.
  - cbn [TripleWord triple_mass]; rewrite !Str_app_assoc.
    follow (D_triple a b c l (TripleWord ts *> Field u *> Field v *> 0inf)).
    follow (IH (l <* [1] <* (rev (Post [0%nat]))^^(1+a) <* [1]^^(3+(b+c)*2))).
    rewrite lpow_add'.
    follow (even_absorb_power (1+a) [0%nat] (5+b+c+u*2+v+triple_mass ts) (l <* [1])).
    change (l <* [1]) with (l <* [1]^^1).
    rewrite lpow_add'; cbn [mass]; finish.
Qed.

Definition M9 := [1]^^9 ++ [0;1;0].

Lemma Pairs_repeat x n:
  rev (Pairs (repeat x n)) = (<[0;1] ++ [1]^^(1+x*2) ++ [0])^^n.
Proof.
  induction n; [reflexivity|].
  cbn [repeat]; rewrite Pairs_cons, IHn.
  exact (lpow_shift (<[0;1] ++ [1]^^(1+x*2) ++ [0]) n).
Qed.

Lemma M9_pairs n l:
  l <* [0] <* (rev M9)^^n = l <* (rev (Pairs (repeat 4 n))) <* [0].
Proof.
  rewrite Pairs_repeat; cbn [M9 lpow rev app].
  rewrite <- Str_app_assoc, lpow_rotate_list, app_nil_r; reflexivity.
Qed.

Lemma M9_recover n a:
  0inf <* [0] <* (rev M9)^^n <* [1]^^(1+a*2) {{C}}> 0inf -->*
  0inf <{{A}} Post (repeat 5 n) *> [1]^^(5+a*2) *> 0inf.
Proof.
  rewrite M9_pairs.
  applys_eq (odd_recover_list (repeat 4 n) a); rewrite ?map_repeat; reflexivity.
Qed.

(* Half-run parameters encode all positive odd triples, including 1.
   This single ordered-list return subsumes both the T and M entrances. *)
Lemma Root7_ordered n ts u v:
  0inf <{{A}} [1]^^(7+n*12) *> [0] *> [1]^^3 *>
    TripleWord ts *> Field u *> Field v *> 0inf -->*
  0inf <{{A}} Post (repeat 5 n) *>
    [1]^^(21+(u*2+v+triple_mass ts)*2) *> 0inf.
Proof.
  follow (A_first7 n 0inf ([1]^^3 *> TripleWord ts *> Field u *> Field v *> 0inf)).
  follow (D_ones 3 (0inf <* [0] <* (rev M9)^^n <* [1]^^7)
    (TripleWord ts *> Field u *> Field v *> 0inf)).
  rewrite lpow_add'.
  follow (D_sweep ts u v (0inf <* [0] <* (rev M9)^^n <* [1]^^10)).
  rewrite lpow_add'.
  follow (M9_recover n (8+u*2+v+triple_mass ts)); finish.
Qed.

Lemma triple_mass_app xs ys:
  triple_mass (xs++ys) = triple_mass xs + triple_mass ys.
Proof. induction xs as [|[[a b] c] xs IH]; cbn; [reflexivity|rewrite IH; lia]. Qed.

Lemma triple_mass_power xs n:
  triple_mass (xs^^n) = n*triple_mass xs.
Proof.
  induction n; [reflexivity|].
  cbn [lpow]; rewrite triple_mass_app, IHn; lia.
Qed.

(* Half-run triples for P after its initial 91,3; B without its final 11;
   and the complete 93-field period W of the informal M family. *)
Definition M_head : list (nat*nat*nat) :=
  [(1,13,1); (1,13,1); (1,9,29); (1,1,13)]%nat.
Definition M_tail : list (nat*nat*nat) :=
  repeat (1,1,1)%nat 18 ++
  [(1,1,5); (1,1,1); (1,49,1); (1,13,1); (1,13,1);
   (1,9,5); (5,5,5); (5,5,5)]%nat.
Definition M_period := M_tail ++ [(5,113,1)]%nat ++ M_head.
Definition M n :=
  0inf <{{A}} [1]^^91 *> [0] *> [1]^^3 *>
    TripleWord (M_head ++ M_period^^n ++ M_tail) *> Field 5 *> Field 110 *> 0inf.

Lemma M_entry n:
  M n -->* 0inf <{{A}} Post (repeat 5 7) *> [1]^^(1125+n*1120) *> 0inf.
Proof.
  unfold M.
  applys_eq (Root7_ordered 7 (M_head ++ M_period^^n ++ M_tail) 5 110).
  rewrite !triple_mass_app, triple_mass_power.
  change (triple_mass M_head) with 104.
  change (triple_mass M_period) with 560.
  change (triple_mass M_tail) with 328.
  flia.
Qed.
(* A nonempty odd bridge really returns A to the even left caller.
   The empty case has a different boundary and is deliberately excluded. *)
Lemma C_turn e x xs a l:
  l <* [0] <* [1]^^(2+e*2) <* <[0;1] <* (rev (Pairs (x::xs)))
    <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  l <* [1]^^(5+e*2) {{E}}>
    Post (map (fun x => 1+x) (x::xs)) *> [1]^^(5+a*2) *> 0inf.
Proof.
  follow (C_recover_list x xs a (l <* [0] <* [1]^^(2+e*2) <* <[0;1])).
  apply even_A_pair.
Qed.

Lemma D_zero l r:
  l <* [0] {{D}}> [0] *> r -->* l <* [1]^^2 {{E}}> r.
Proof. es. Qed.

Lemma E_triple a b c l r:
  l {{E}}> Post [a;b;c] *> r -->*
  l <* <[0;1]^^(1+a) <* [1]^^(4+(b+c)*2) {{E}}> r.
Proof.
  change (Post [a;b;c]) with
    ([1]^^(1+a*2) ++ [0] ++ [1]^^(1+b*2) ++ [0] ++ [1]^^(1+c*2) ++ [0]).
  rewrite !Str_app_assoc.
  follow (E_odd a l ([1]^^(1+b*2) *> [0] *> [1]^^(1+c*2) *> [0] *> r)).
  follow (C_ones (1+b*2) (l <* <[0;1]^^(1+a))
    ([0] *> [1]^^(1+c*2) *> [0] *> r)).
  follow (C_scan (1+c*2) (l <* <[0;1]^^(1+a) <* [1]^^(1+b*2)) ([0] *> r)).
  follow (D_zero (l <* <[0;1]^^(1+a) <* [1]^^(1+b*2) <* [1]^^(1+c*2)) r).
  rewrite !lpow_add'; finish.
Qed.

Lemma E_terminal1 a l:
  l {{E}}> [1]^^(1+a*2) *> 0inf -->*
  l <* <[0;1]^^(1+a) {{C}}> 0inf.
Proof. applys_eq (E_odd a l 0inf); simpl_tape; reflexivity. Qed.

Lemma E_terminal2 a b l:
  l {{E}}> Post [a] *> [1]^^(1+b*2) *> 0inf -->*
  l <* <[0;1]^^(1+a) <* [1]^^(1+b*2) {{C}}> 0inf.
Proof.
  change (Post [a]) with ([1]^^(1+a*2) ++ [0]); rewrite Str_app_assoc.
  follow (E_odd a l ([1]^^(1+b*2) *> 0inf)); apply C_ones.
Qed.

Lemma E_terminal3 a b c l:
  l {{E}}> Post [a;b] *> [1]^^(1+c*2) *> 0inf -->*
  l <* <[0;1]^^(1+a) <* [1]^^(2+(b+c)*2) {{C}}> 0inf.
Proof.
  change (Post [a;b]) with ([1]^^(1+a*2) ++ [0] ++ [1]^^(1+b*2) ++ [0]).
  rewrite !Str_app_assoc.
  follow (E_odd a l ([1]^^(1+b*2) *> [0] *> [1]^^(1+c*2) *> 0inf)).
  follow (C_ones (1+b*2) (l <* <[0;1]^^(1+a))
    ([0] *> [1]^^(1+c*2) *> 0inf)).
  step.
  follow (D_last (c*2) (l <* <[0;1]^^(1+a) <* [1]^^(1+b*2)) 0inf).
  rewrite lpow_add'.
  replace (1+c*2+(1+b*2)) with (2+(b+c)*2) by lia; simpl_tape; finish.
Qed.

Fixpoint TripleFields (ts : list (nat*nat*nat)) : list nat :=
  match ts with [] => [] | (a,b,c)::ts => a::b::c::TripleFields ts end.
Fixpoint EWord (ts : list (nat*nat*nat)) : list Sym :=
  match ts with
  | [] => []
  | (a,b,c)::ts => [0;1]^^(1+a) ++ [1]^^(4+(b+c)*2) ++ EWord ts
  end.

Lemma rev_power (w : list Sym) n: rev (w^^n) = (rev w)^^n.
Proof.
  induction n; [reflexivity|].
  cbn [lpow]; rewrite rev_app_distr, IHn; apply lpow_shift.
Qed.

Lemma E_sweep ts l r:
  l {{E}}> Post (TripleFields ts) *> r -->*
  l <* (rev (EWord ts)) {{E}}> r.
Proof.
  revert l; induction ts as [|[[a b] c] ts IH]; intros l.
  - cbn [TripleFields Post EWord]; finish.
  - change (TripleFields ((a,b,c)::ts)) with ([a;b;c] ++ TripleFields ts).
    rewrite Post_app, Str_app_assoc.
    follow (E_triple a b c l (Post (TripleFields ts) *> r)).
    applys_eq (IH (l <* <[0;1]^^(1+a) <* [1]^^(4+(b+c)*2)));
      cbn [EWord]; rewrite !rev_app_distr, ?rev_power, ?rev_ones; simpl_tape; reflexivity.
Qed.

(* The repeated triple (3,3,1+2x+2) leaves a pair (1,1+2x+8).
   This list identity is the shared middle phase of NEXT, K and FOUR11. *)
Definition Spaced (xs : list nat) := flat_map (fun x => [0;0;x]%nat) xs.
Definition Raised (xs : list nat) := flat_map (fun x => [1;1;1+x]%nat) xs.

Lemma Spaced_map xs:
  map (fun x => 1+x) (Spaced xs ++ [0;0]%nat) = Raised xs ++ [1;1]%nat.
Proof.
  unfold Spaced, Raised; induction xs as [|x xs IH]; cbn [flat_map app map];
    rewrite ?IH; flia.
Qed.

Lemma E_pairs xs a l:
  l {{E}}> Post (Raised xs ++ [1;1]%nat) *> [1]^^(5+a*2) *> 0inf -->*
  l <* <[0;1] <* (rev (Pairs (map (fun x => 4+x) xs)))
    <* [0] <* [1]^^(9+a*2) {{C}}> 0inf.
Proof.
  revert l; induction xs as [|x xs IH]; intros l.
  - change (Raised [] ++ [1;1]%nat) with [1;1]%nat.
    follow (E_terminal3 1 1 (2+a) l).
    replace (1+1) with 2 by lia.
    replace (2+(1+(2+a))*2) with (8+a*2) by lia.
    cbn [map Pairs]; simpl_tape; finish; now rewrite !lpow_shift1.
  - change (Raised (x::xs) ++ [1;1]%nat) with ([1;1;1+x] ++ (Raised xs ++ [1;1]))%nat.
    rewrite Post_app, Str_app_assoc.
    follow (E_triple 1 1 (1+x) l (Post (Raised xs ++ [1;1]%nat) *> [1]^^(5+a*2) *> 0inf)).
    follow (IH (l <* <[0;1]^^2 <* [1]^^(4+(1+(1+x))*2))).
    cbn [map]; rewrite Pairs_cons, !Str_app_assoc.
    replace (4+(1+(1+x))*2) with (8+x*2) by lia.
    replace (1+(4+x)*2) with (9+x*2) by lia.
    simpl_tape; finish; now rewrite !lpow_shift1.
Qed.

Lemma Two_turns e x xs a l:
  l <* [0;1;0] <* [1]^^(2+e*2) <* <[0;1]
    <* (rev (Pairs (Spaced (x::xs) ++ [0;0]%nat))) <* [0]
    <* [1]^^(1+a*2) {{C}}> 0inf -->*
  l <* [1]^^(9+e*2) {{E}}>
    Post (map (fun x => 5+x) (x::xs)) *> [1]^^(13+a*2) *> 0inf.
Proof.
  follow (C_turn e 0 (0::x::Spaced xs ++ [0;0])%nat a (l <* [0] <* [1])).
  change (0::0::x::Spaced xs ++ [0;0])%nat with (Spaced (x::xs) ++ [0;0]%nat).
  rewrite Spaced_map.
  follow (E_pairs (x::xs) a (l <* [0] <* [1] <* [1]^^(5+e*2))).
  change (l <* [0] <* [1]) with (l <* [0] <* [1]^^1).
  rewrite lpow_add'.
  follow (C_turn (2+e) (4+x) (map (fun x => 4+x) xs) (4+a) l).
  change (4+x::map (fun x => 4+x) xs)%nat with (map (fun x => 4+x) (x::xs)).
  rewrite map_map.
  rewrite (map_ext (fun x => 1+(4+x)) (fun x => 5+x) ltac:(intros; lia)).
  finish.
Qed.

Lemma Csmall a:
  0inf <* [1]^^7 <* [0] <* [1]^^9 <* <[0;1;0]
    <* [1]^^(1+a*2) {{C}}> 0inf -->* S (35+a*2).
Proof. unfold S; es' a. Qed.

Lemma D_left_ones n l r:
  l <* [1]^^(n*2) <{{D}} r -->* l <{{D}} [1]^^(n*2) *> r.
Proof. es' n & l r. Qed.

Lemma D_absorb01 a l:
  l <* <[0;1] <{{D}} [1]^^(a*2) *> 0inf -->*
  l <{{D}} [1]^^(4+a*2) *> 0inf.
Proof. es' a & l. Qed.

Lemma D_absorb_alt n a l:
  l <* <[0;1]^^n <{{D}} [1]^^(a*2) *> 0inf -->*
  l <{{D}} [1]^^((a+n*2)*2) *> 0inf.
Proof.
  revert a l; induction n; intros a l.
  - cbn [lpow]; finish.
  - cbn [lpow]; rewrite Str_app_assoc.
    follow (D_absorb01 a (l <* <[0;1]^^n)).
    applys_eq (IHn (a+2) l); flia.
Qed.

Definition Block b r c := [1]^^b ++ [0;1]^^r ++ [0] ++ [1]^^c.

Lemma D_block b r c a l:
  l <* (rev (Block (b*2) r (1+c*2))) <{{D}} [1]^^(a*2) *> 0inf -->*
  l <{{D}} [1]^^((a+b+c+r*2+2)*2) *> 0inf.
Proof.
  unfold Block; rewrite !rev_app_distr, !rev_power, !Str_app_assoc.
  rewrite (Nat.add_comm 1 (c*2)), lpow_add, Str_app_assoc.
  follow (D_left_ones c (l <* [1]^^(b*2) <* <[0;1]^^r <* <[0;1])
    ([1]^^(a*2) *> 0inf)).
  rewrite lpow_add'.
  follow (D_absorb01 (c+a) (l <* [1]^^(b*2) <* <[0;1]^^r)).
  follow (D_absorb_alt r (c+a+2) (l <* [1]^^(b*2))).
  follow (D_left_ones b l ([1]^^((c+a+2+r*2)*2) *> 0inf)).
  rewrite lpow_add'; finish.
Qed.

Lemma D_block_power n b r c a l:
  l <* (rev (Block (b*2) r (1+c*2)))^^n <{{D}} [1]^^(a*2) *> 0inf -->*
  l <{{D}} [1]^^((a+n*(b+c+r*2+2))*2) *> 0inf.
Proof.
  revert a l; induction n; intros a l.
  - cbn [lpow]; finish.
  - cbn [lpow]; rewrite Str_app_assoc.
    follow (D_block b r c a (l <* (rev (Block (b*2) r (1+c*2)))^^n)).
    applys_eq (IHn (a+b+c+r*2+2) l); flia.
Qed.

Lemma C_absorb_alt n a b l:
  l <* [1]^^(1+b) <* <[0;1]^^n <* [0] <* [1]^^(a*2) {{C}}> 0inf -->*
  l <* [1]^^(4+b+(a+n*2)*2) {{C}}> 0inf.
Proof.
  revert a l; induction n; intros a l.
  - cbn [lpow]; applys_eq (absorb_run a b l); flia.
  - cbn [lpow]; rewrite Str_app_assoc.
    follow (absorb_zero a (l <* [1]^^(1+b) <* <[0;1]^^n <* [0])).
    applys_eq (IHn (a+2) l); flia.
Qed.

Lemma C_block k b r c a l:
  a+c=k*2 ->
  l <* (rev (Block (1+b) r c)) <* [1]^^a {{C}}> 0inf -->*
  l <* [1]^^(a+4+b+c+r*4) {{C}}> 0inf.
Proof.
  intro H; unfold Block; rewrite !rev_app_distr, !rev_power, !Str_app_assoc.
  rewrite lpow_add', H.
  applys_eq (C_absorb_alt r k b l); flia.
Qed.

Lemma C_block_power n b r c a d k l:
  b+c=d*2 -> a+c=k*2 ->
  l <* (rev (Block (1+b) r c))^^n <* [1]^^a {{C}}> 0inf -->*
  l <* [1]^^(a+n*(4+b+c+r*4)) {{C}}> 0inf.
Proof.
  intro Hd; revert a k l; induction n; intros a k l Ha.
  - cbn [lpow]; finish.
  - cbn [lpow]; rewrite Str_app_assoc.
    follow (C_block k b r c a (l <* (rev (Block (1+b) r c))^^n) Ha).
    applys_eq (IHn (a+4+b+c+r*4) (k+2+d+r*2) l ltac:(lia)); flia.
Qed.

Definition H n :=
  0inf <{{A}} [1]^^53 *> ([0]++[1]^^107)^^n *> [1]^^2 *> 0inf.
Definition H_A := Post ([2;0] ++ [4;0]^^3 ++ [3] ++ [4;0]^^9)%nat.

Lemma H_entry2 n:
  H (2+n*3) -->* 0inf <* (rev H_A) <* [1]^^111
    <* (rev (Block 109 53 108))^^n <* [1]^^2 {{C}}> 0inf.
Proof. unfold H, H_A, Block, Post; es' n. Qed.

Lemma H_entry4 n:
  H (4+n*3) -->* 0inf <* (rev H_A) <* [1]^^218
    <* (rev (Block 2 53 215))^^n <* [1]^^153 {{C}}> 0inf.
Proof. unfold H, H_A, Block, Post; es' n. Qed.

Lemma H_A_finish a:
  0inf <* (rev H_A) <* [1]^^(1+a*2) {{C}}> 0inf -->* S (225+a*2).
Proof. unfold H_A, Post, S; es' a. Qed.

Lemma H_two n: H (2+n*3) -->* S (337+n*432).
Proof.
  follow (H_entry2 n).
  follow (C_block_power n 108 53 108 2 108 55
    (0inf <* (rev H_A) <* [1]^^111) ltac:(lia) ltac:(lia)).
  rewrite lpow_add'.
  applys_eq (H_A_finish (56+n*216)); flia.
Qed.

Lemma H_four n: H (4+n*3) -->* S (595+n*432).
Proof.
  follow (H_entry4 n).
  follow (C_block_power n 1 53 215 153 108 184
    (0inf <* (rev H_A) <* [1]^^218) ltac:(lia) ltac:(lia)).
  rewrite lpow_add'.
  applys_eq (H_A_finish (185+n*216)); flia.
Qed.

Lemma H_one: H 1 -->* S 227.
Proof. unfold H, S; es'. Qed.

Lemma H_three: H 3 -->* S 441.
Proof. unfold H, S; es'. Qed.

Lemma B_triple p l r:
  l {{B}}> ([0]++[1]^^(1+p*2))^^3 *> r -->*
  l <* (rev (Block (5+p*4) p 0)) {{B}}> r.
Proof.
  cbn [lpow]; rewrite !Str_app_assoc.
  follow (B_scan (1+p*2) l ([0] *> [1]^^(1+p*2) *> [0] *> [1]^^(1+p*2) *> r)).
  follow (C_scan (1+p*2) (l <* [1]^^(1+(1+p*2))) ([0] *> [1]^^(1+p*2) *> r)).
  follow (D_odd p (l <* [1]^^(1+(1+p*2)) <* [1]^^(1+p*2)) r).
  unfold Block; rewrite !rev_app_distr, !rev_power; simpl_tape.
  rewrite !lpow_shift1, !lpow_add'; finish.
  cbn; rewrite lpow_rotate; cbn; flia.
Qed.

Lemma B_batch p n l r:
  l {{B}}> ([0]++[1]^^(1+p*2))^^(n*3) *> r -->*
  l <* (rev (Block (5+p*4) p 0))^^n {{B}}> r.
Proof.
  revert l; induction n; intros l.
  - cbn [Nat.mul lpow]; finish.
  - replace (Datatypes.S n*3) with (3+n*3) by lia.
    rewrite lpow_add, Str_app_assoc.
    follow (B_triple p l (([0]++[1]^^(1+p*2))^^(n*3) *> r)).
    applys_eq (IHn (l <* (rev (Block (5+p*4) p 0))));
      cbn [lpow]; rewrite <- Str_app_assoc, lpow_shift; reflexivity.
Qed.

Lemma B_complete p n l:
  l {{B}}> ([0]++[1]^^(1+p*2))^^(n*3) *>
    [0] *> [1]^^(3+p*2) *> 0inf -->*
  l <* [1]^^(4+p*2+n*(8+p*8)) {{C}}> 0inf.
Proof.
  follow (B_batch p n l ([0] *> [1]^^(3+p*2) *> 0inf)).
  follow (B_scan (3+p*2) (l <* (rev (Block (5+p*4) p 0))^^n) 0inf).
  applys_eq (C_block_power n (4+p*4) p 0 (4+p*2) (2+p*2) (2+p) l
    ltac:(lia) ltac:(lia)); flia.
Qed.

Definition H_Z := Post ([2;0] ++ [4;0]^^3 ++ [3] ++ [4;0]^^5)%nat.
Definition H_YM := Post ([2;0] ++ [4;0]^^3 ++ [2;12] ++ repeat 0 5 ++ [11])%nat.

Lemma Z_entry9 n:
  0inf <* (rev H_Z) <* [1]^^(9+n*12) {{C}}> 0inf -->*
  0inf <* (rev H_YM) <* (rev M9)^^(1+n) <* [1]^^6 {{C}}> 0inf.
Proof. unfold H_Z, H_YM, Post, M9; es' n. Qed.

Lemma H_YM_finish a:
  0inf <* (rev H_YM) <* [1]^^(a*2) {{C}}> 0inf -->* S (149+a*2).
Proof.
  unfold H_YM.
  follow (even_absorb_list ([2;0] ++ [4;0]^^3 ++ [2;12] ++ repeat 0 5 ++ [11])%nat a 0inf).
  apply progress_evstep; applys_eq (finish_even (70+a)); cbn [mass lpow repeat app]; flia.
Qed.

Lemma Z_nine n:
  0inf <* (rev H_Z) <* [1]^^(9+n*12) {{C}}> 0inf -->* S (171+n*16).
Proof.
  follow (Z_entry9 n).
  change M9 with (Block 9 1 0).
  follow (C_block_power (1+n) 8 1 0 6 4 3 (0inf <* (rev H_YM)) ltac:(lia) ltac:(lia)).
  applys_eq (H_YM_finish (11+n*8)); flia.
Qed.

Lemma H_nine_entry n:
  H (9+n*9) -->* 0inf <* (rev H_Z) <* [1]^^284 <* <[0;1]^^161 <* [0]
    {{B}}> ([0]++[1]^^323)^^(n*3) *> [0] *> [1]^^325 *> 0inf.
Proof. unfold H, H_Z, Post; es' n. Qed.

Lemma H_nine n: H (9+n*9) -->* S (1835+n*1728).
Proof.
  follow (H_nine_entry n).
  follow (B_complete 161 n (0inf <* (rev H_Z) <* [1]^^284 <* <[0;1]^^161 <* [0])).
  follow (C_absorb_alt 161 (163+n*648) 283 (0inf <* (rev H_Z))).
  applys_eq (Z_nine (104+n*108)); flia.
Qed.
Lemma C_tag_block b r c a l:
  l <* (rev (Block (2+b*2) r (1+c*2))) <* [0] <* [1]^^(a*2) {{C}}> 0inf -->*
  l <* [1]^^(9+(a+b+c+r*2)*2) {{C}}> 0inf.
Proof.
  unfold Block; rewrite !rev_app_distr, !rev_power, !Str_app_assoc.
  follow (absorb_run a (c*2) (l <* [1]^^(2+b*2) <* <[0;1]^^r <* [0])).
  applys_eq (C_absorb_alt r (a+c+2) (1+b*2) l); flia.
Qed.

Lemma tagged_even n e b r c a l:
  l <* [1]^^(1+e) <* (rev (Block (2+b*2) r (1+c*2)))^^n
    <* [0] <* [1]^^(a*2) {{C}}> 0inf -->*
  l <* [1]^^(4+e+a*2+n*(6+b*2+c*2+r*4)) {{C}}> 0inf.
Proof.
  destruct n as [|n].
  - cbn [lpow]; applys_eq (absorb_run a e l); flia.
  - cbn [lpow]; rewrite Str_app_assoc.
    follow (C_tag_block b r c a
      (l <* [1]^^(1+e) <* (rev (Block (2+b*2) r (1+c*2)))^^n)).
    follow (C_block_power n (1+b*2) r (1+c*2) (9+(a+b+c+r*2)*2)
      (1+b+c) (5+a+b+c*2+r*2) (l <* [1]^^(1+e)) ltac:(lia) ltac:(lia)).
    rewrite lpow_add'; finish.
Qed.

Lemma absorb_odd_run a e l:
  l <* [1]^^(3+e) <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  l <* [1]^^(10+e+a*2) {{C}}> 0inf.
Proof.
  replace (3+e) with (2+(1+e)) by lia.
  rewrite lpow_add, Str_app_assoc.
  follow (odd_transfer a (l <* [1]^^(1+e))).
  applys_eq (absorb_run (3+a) e l); flia.
Qed.

Lemma C_tag_block_odd b r c a l:
  l <* (rev (Block (2+b*2) r (3+c*2))) <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  l <* [1]^^(15+(a+b+c+r*2)*2) {{C}}> 0inf.
Proof.
  unfold Block; rewrite !rev_app_distr, !rev_power, !Str_app_assoc.
  follow (absorb_odd_run a (c*2) (l <* [1]^^(2+b*2) <* <[0;1]^^r <* [0])).
  applys_eq (C_absorb_alt r (a+c+5) (1+b*2) l); flia.
Qed.

Lemma tagged_odd n e b r c a l:
  l <* [1]^^(3+e) <* (rev (Block (2+b*2) r (3+c*2)))^^n
    <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  l <* [1]^^(10+e+a*2+n*(8+b*2+c*2+r*4)) {{C}}> 0inf.
Proof.
  destruct n as [|n].
  - cbn [lpow]; applys_eq (absorb_odd_run a e l); flia.
  - cbn [lpow]; rewrite Str_app_assoc.
    follow (C_tag_block_odd b r c a
      (l <* [1]^^(3+e) <* (rev (Block (2+b*2) r (3+c*2)))^^n)).
    follow (C_block_power n (1+b*2) r (3+c*2) (15+(a+b+c+r*2)*2)
      (2+b+c) (9+a+b+c*2+r*2) (l <* [1]^^(3+e)) ltac:(lia) ltac:(lia)).
    rewrite lpow_add'; finish.
Qed.

Definition H_S0 := Post ([2;0] ++ [4;0]^^3 ++ [1;16;0])%nat.

Lemma Z_entry3 n:
  0inf <* (rev H_Z) <* [1]^^(3+n*12) {{C}}> 0inf -->*
  0inf <* (rev H_S0) <* [1]^^31 <* (rev (Block 2 1 7))^^n
    <* [0] <* [1]^^9 {{C}}> 0inf.
Proof. unfold H_Z, H_S0, Block, Post; es' n. Qed.

Lemma H_S0_finish a:
  0inf <* (rev H_S0) <* [1]^^(a*2) {{C}}> 0inf -->* S (113+a*2).
Proof.
  unfold H_S0.
  follow (even_absorb_list ([2;0] ++ [4;0]^^3 ++ [1;16;0])%nat a 0inf).
  apply progress_evstep; applys_eq (finish_even (52+a)); cbn [mass lpow app]; flia.
Qed.

Lemma H_Z_three n:
  0inf <* (rev H_Z) <* [1]^^(3+n*12) {{C}}> 0inf -->* S (159+n*16).
Proof.
  follow (Z_entry3 n).
  follow (tagged_odd n 28 0 1 2 4 (0inf <* (rev H_S0))).
  applys_eq (H_S0_finish (23+n*8)); flia.
Qed.

Lemma H_six_entry n:
  H (6+n*9) -->* 0inf <* (rev H_Z) <* [1]^^282
    <* (rev (Block 2 161 647))^^n <* [1]^^2 <* <[0;1]^^163 {{C}}> 0inf.
Proof. unfold H, H_Z, Block, Post; es' n. Qed.

Lemma C_alt_one n l:
  l <* [1]^^2 <* <[0;1]^^(1+n*6) {{C}}> 0inf -->*
  l <* [0] <* (rev M9)^^n <* [1]^^6 {{C}}> 0inf.
Proof. unfold M9; es' n & l. Qed.

Lemma C_alt_one_total n l:
  l <* [1]^^2 <* <[0;1]^^(1+n*6) {{C}}> 0inf -->*
  l <* [0] <* [1]^^(6+n*16) {{C}}> 0inf.
Proof.
  follow (C_alt_one n l).
  change M9 with (Block 9 1 0).
  applys_eq (C_block_power n 8 1 0 6 4 3 (l <* [0]) ltac:(lia) ltac:(lia)); flia.
Qed.

Lemma H_six_tail l:
  l <* [1]^^2 <* <[0;1]^^163 {{C}}> 0inf -->*
  l <* [0] <* [1]^^438 {{C}}> 0inf.
Proof. exact (C_alt_one_total 27 l). Qed.

Lemma H_six n: H (6+n*9) -->* S (1119+n*1728).
Proof.
  follow (H_six_entry n).
  follow (H_six_tail (0inf <* (rev H_Z) <* [1]^^282 <* (rev (Block 2 161 647))^^n)).
  follow (tagged_even n 281 0 161 323 219 (0inf <* (rev H_Z))).
  applys_eq (H_Z_three (60+n*108)); flia.
Qed.
Definition V_word c := [1;1] ++ [0;1;1;1]^^80 ++ [0] ++ [1]^^c.

Lemma B_odd_bridge c l r:
  l <* [0] <* [1]^^(1+c*2) <{{B}} [0] *> r -->*
  l <{{A}} [1]^^(3+c*2) *> r.
Proof. es' c & l r. Qed.

Lemma A_alt_return a l r:
  l <* <[0;1]^^(1+a*2) <{{A}} r -->*
  l <{{F}} [1] *> [0;1;1;1]^^a *> [0] *> r.
Proof. es' a & l r. Qed.

Lemma B_half a c l r:
  l <* (rev (Block 2 (1+a*2) (1+c*2))) <{{B}} [0] *> r -->*
  l <{{B}} [0;1;1] *> [0;1;1;1]^^a *> [0] *> [1]^^(3+c*2) *> r.
Proof.
  unfold Block; rewrite !rev_app_distr, !rev_power, !Str_app_assoc.
  follow (B_odd_bridge c (l <* [1]^^2 <* <[0;1]^^(1+a*2)) r).
  follow (A_alt_return a (l <* [1]^^2) ([1]^^(3+c*2) *> r)).
  es; finish.
Qed.

Lemma B_half_power n a c l r:
  l <* (rev (Block 2 (1+a*2) (1+c*2)))^^n <{{B}} [0] *> r -->*
  l <{{B}} [0] *> ([1;1] ++ [0;1;1;1]^^a ++ [0] ++ [1]^^(3+c*2))^^n *> r.
Proof.
  revert l r; induction n; intros l r.
  - cbn [lpow]; finish.
  - cbn [lpow]; rewrite !Str_app_assoc.
    follow (B_half a c (l <* (rev (Block 2 (1+a*2) (1+c*2)))^^n) r).
    applys_eq (IHn l ([1;1] *> [0;1;1;1]^^a *> [0] *> [1]^^(3+c*2) *> r));
      rewrite <- !Str_app_assoc, <- !app_assoc, lpow_shift, <- !app_assoc; reflexivity.
Qed.

Definition sweep_h : DH0*DH0 := ((D,[0]),(B,[0;1;1])).

Lemma sweep_triple a b c:
  segRLs tm [sweep_h] [sweep_h]
    (Field (1+a*2) ++ Field b ++ Field c)
    ((Field 1)^^a ++ Field (3+b+c)).
Proof.
  unfold sweep_h.
  eapply segRLs_lrcons with (ls2:=[]) (ls3:=[]) (ls4:=[])
    (w3:=rev (Block 2 (1+a*2) (3+(b+c)*2)))
    (w4:=rev (Block 2 (1+a*2) (3+(b+c)*2)))
    (w5:=(Field 1)^^a ++ Field (3+b+c)).
  - intros l r; cbn [to_DH_config]; rewrite !Str_app_assoc.
    follow (D_triple (1+a*2) b c l r).
    unfold Block; rewrite !rev_app_distr, !rev_power.
    cbn [Post]; simpl_tape; finish.
    cbn; rewrite lpow_rotate; reflexivity.
  - intros l r; cbn [to_DH_config].
    follow (B_half a (1+b+c) l ([1;1] *> r)).
    unfold Field; simpl_tape; finish; cbn; rewrite !lpow_shift1; flia.
  - constructor.
  - constructor.
Qed.

Definition Fields (xs : list nat) := flat_map Field xs.

Lemma Fields_app xs ys: Fields (xs++ys) = Fields xs ++ Fields ys.
Proof. apply flat_map_app. Qed.

Lemma Fields_repeat a n: Fields (repeat a n) = (Field a)^^n.
Proof. unfold Fields; induction n; cbn [repeat flat_map lpow]; congruence. Qed.

Inductive Sweep : list nat -> list nat -> Prop :=
| Sweep_nil: Sweep [] []
| Sweep_cons a b c xs ys:
    Sweep xs ys ->
    Sweep ((1+a*2)::b::c::xs)%nat (repeat 1 a ++ (3+b+c)::ys)%nat.

Lemma Sweep_spec xs ys:
  Sweep xs ys -> segRLs tm [sweep_h] [sweep_h] (Fields xs) (Fields ys).
Proof.
  intro H; induction H.
  - apply segRLs_nil.
  - rewrite Fields_app, Fields_repeat; cbn [Fields flat_map].
    applys_eq (segRLs_concat (sweep_triple a b c) IHSweep); rewrite !app_assoc; reflexivity.
Qed.

Lemma sweep_power n hs xs ys:
  segRLs tm hs hs xs ys -> segRLs tm hs hs (xs^^n) (ys^^n).
Proof.
  intro H; induction n.
  - apply segRLs_nil.
  - cbn [lpow]; eapply segRLs_concat; eauto.
Qed.

Fixpoint sweep_step (xs : list nat) : option (list nat) :=
  match xs with
  | [] => Some []
  | a::b::c::xs =>
      if a mod 2 =? 1 then
        match sweep_step xs with
        | Some ys => Some (repeat 1 (a/2) ++ (3+b+c)::ys)%nat
        | None => None
        end
      else None
  | _ => None
  end.

Lemma sweep_step_spec xs ys: sweep_step xs = Some ys -> Sweep xs ys.
Proof.
  revert xs ys; fix IH 1; intros xs ys Hs.
  destruct xs as [|a [|b [|c xs]]]; cbn [sweep_step] in Hs; try discriminate.
  - inversion Hs; constructor.
  - destruct (a mod 2 =? 1) eqn:Ha; [|discriminate].
    destruct (sweep_step xs) as [zs|] eqn:Hz; [|discriminate].
    inversion Hs; subst ys.
    apply Nat.eqb_eq in Ha.
    replace a with (1+(a/2)*2)%nat at 1 by lia.
    constructor; now apply IH.
Qed.

Fixpoint sweep_iter k xs :=
  match k with
  | O => Some xs
  | Datatypes.S k =>
      match sweep_step xs with Some ys => sweep_iter k ys | None => None end
  end.

Lemma sweep_iter_spec k xs ys:
  sweep_iter k xs = Some ys ->
  segRLs tm ([sweep_h]^^k) ([sweep_h]^^k) (Fields xs) (Fields ys).
Proof.
  revert xs ys; induction k; intros xs ys Hs.
  - cbn [sweep_iter] in Hs; inversion Hs; constructor.
  - cbn [sweep_iter] in Hs.
    destruct (sweep_step xs) as [zs|] eqn:Hz; [|discriminate].
    replace (Datatypes.S k) with (1+k)%nat by lia; rewrite !lpow_add.
    eapply segRLs_trans; [apply Sweep_spec, sweep_step_spec, Hz|now apply IHk].
Qed.

Lemma D_blank l:
  l <* [0] {{D}}> 0inf -->* l <{{B}} [0;1;1] *> 0inf.
Proof. es' & l. Qed.

Lemma H_K_entry n:
  H (12+n*9) -->* 0inf <* (rev H_Z) <* [1]^^282
    <* (rev (Block 2 161 647))^^n <* (rev (Block 2 161 649)) <* [0] {{D}}> 0inf.
Proof. unfold H, H_Z, Post, Block; es' n. Qed.

Lemma H_V_entry n:
  H (12+n*9) -->* 0inf <* (rev H_Z) <* [1]^^282 <{{B}}
    [0] *> (V_word 649)^^n *> V_word 653 *> 0inf.
Proof.
  follow (H_K_entry n).
  follow (D_blank (0inf <* (rev H_Z) <* [1]^^282
    <* (rev (Block 2 161 647))^^n <* (rev (Block 2 161 649)))).
  follow (B_half 80 324 (0inf <* (rev H_Z) <* [1]^^282 <* (rev (Block 2 161 647))^^n)
      ([1;1] *> 0inf)).
  follow (B_half_power n 80 323 (0inf <* (rev H_Z) <* [1]^^282)
      ([1;1] *> [0;1;1;1]^^80 *> [0] *> [1]^^651 *> [1;1] *> 0inf)).
  unfold V_word; simpl_tape; finish.
Qed.

Lemma blank_sweeps k: sideRLs tm ([sweep_h]^^k) 0inf 0inf.
Proof. apply sideRLs_wall; unfold sweep_h; es'. Qed.

Lemma right_sweeps k n xs ys xt yt:
  sweep_iter k xs = Some ys -> sweep_iter k xt = Some yt ->
  sideRLs tm ([sweep_h]^^k)
    ((Fields xs)^^n *> Fields xt *> 0inf)
    ((Fields ys)^^n *> Fields yt *> 0inf).
Proof.
  intros Hx Ht.
  eapply segRLs_sideRLs_concat; [apply sweep_power, sweep_iter_spec, Hx|].
  eapply segRLs_sideRLs_concat; [apply sweep_iter_spec, Ht|apply blank_sweeps].
Qed.

Lemma V_fields n r:
  (V_word 649)^^n *> V_word 653 *> r =
  [1;1] *> (Fields (repeat 1 80 ++ [325])%nat)^^n *>
    Fields (repeat 1 80 ++ [326])%nat *> r.
Proof.
  induction n.
  - cbn [lpow]; reflexivity.
  - cbn [lpow]; rewrite Str_app_assoc, IHn.
    cbn [V_word]; rewrite !Fields_app, !Fields_repeat.
    cbn [Fields flat_map Field]; simpl_tape; reflexivity.
Qed.

Lemma caller_one a l:
  sideRLs (flip tm) [((B,[0;1;1]),(D,[0]))]
    (l <* [0] <* [1]^^(a*2)) (l <* [1]^^(3+a*2)).
Proof. es' a & l. Qed.

Lemma caller_pair a x l:
  sideRLs (flip tm) [((B,[0;1;1]),(D,[0]))]
    (l <* [1]^^(1+x*2) <* [0] <* [1]^^(a*2))
    (l <* [1]^^((a+x+2)*2)).
Proof.
  applys_eq (caller_one a (l <* [1]^^(1+x*2))); rewrite lpow_add'; flia.
Qed.

Lemma caller_list xs a l:
  sideRLs (flip tm) ([((B,[0;1;1]),(D,[0]))]^^length xs)
    (l <* (rev (Post xs)) <* [1]^^(a*2))
    (l <* [1]^^((a+mass xs)*2)).
Proof.
  revert a l; induction xs as [|x xs IH]; intros a l.
  - cbn [Post mass length lpow]; replace (a+0)%nat with a by lia; constructor.
  - cbn [Post mass length]; rewrite !rev_app_distr, rev_ones, !Str_app_assoc.
    replace (Datatypes.S (length xs)) with (length xs+1)%nat by lia.
    rewrite lpow_add; eapply sideRLs_trans.
    + apply (IH a (l <* [1]^^(1+x*2) <* [0])).
    + applys_eq (caller_pair (a+mass xs) x l); flia.
Qed.

Lemma V_caller:
  sideRLs (flip tm) ([((B,[0;1;1]),(D,[0]))]^^15)
    (0inf <* (rev H_Z) <* [1]^^282)
    (0inf <* (rev (Post [2;0;4;0]%nat)) <* [1]^^404).
Proof.
  change H_Z with (Post [2;0;4;0]%nat ++ Post ([4;0]^^2 ++ [3] ++ [4;0]^^5)%nat).
  rewrite rev_app_distr, Str_app_assoc.
  exact (caller_list ([4;0]^^2 ++ [3] ++ [4;0]^^5)%nat 141
    (0inf <* (rev (Post [2;0;4;0]%nat)))).
Qed.

Lemma V_sweep15 n:
  0inf <* (rev H_Z) <* [1]^^282 <{{B}}
    [0] *> (V_word 649)^^n *> V_word 653 *> 0inf -->*
  0inf <* (rev (Post [2;0;4;0]%nat)) <* [1]^^404
    <{{B}} [0;1;1] *> ([0]++[1]^^971)^^n *> [0] *> [1]^^973 *> 0inf.
Proof.
  rewrite V_fields.
  applys_eq (sideRLs_concat_1L
    (right_sweeps 15 n (repeat 1 80 ++ [325])%nat [485]%nat
      (repeat 1 80 ++ [326])%nat [486]%nat eq_refl eq_refl) V_caller);
    reflexivity.
Qed.

Lemma H_sweep_entry n:
  H (12+n*9) -->* 0inf <* (rev (Post [2;0;4;0]%nat)) <* [1]^^404
    <{{B}} [0;1;1] *> ([0]++[1]^^971)^^n *> [0] *> [1]^^973 *> 0inf.
Proof. follow (H_V_entry n); apply V_sweep15. Qed.

Definition H_U := Post [2;0;4]%nat.

Lemma H_U_finish a:
  0inf <* (rev H_U) <* [1]^^(1+a*2) {{C}}> 0inf -->* S (35+a*2).
Proof. unfold H_U, Post, S; es' a. Qed.

Lemma H_twelve_entry n:
  H (12+n*27) -->* 0inf <* (rev H_U) <* [1]^^408
    <* (rev (Block 2 485 1943))^^n <* [1]^^2 <* <[0;1]^^487 {{C}}> 0inf.
Proof.
  follow (H_sweep_entry (n*3)).
  unfold H_U, Post, Block; es' n.
Qed.

Lemma H_twelve_tail l:
  l <* [1]^^2 <* <[0;1]^^487 {{C}}> 0inf -->*
  l <* [0] <* [1]^^1302 {{C}}> 0inf.
Proof. exact (C_alt_one_total 81 l). Qed.

Lemma H_twelve n: H (12+n*27) -->* S (1747+n*3888).
Proof.
  follow (H_twelve_entry n).
  follow (H_twelve_tail (0inf <* (rev H_U) <* [1]^^408 <* (rev (Block 2 485 1943))^^n)).
  follow (tagged_even n 407 0 485 971 651 (0inf <* (rev H_U))).
  applys_eq (H_U_finish (856+n*1944)); flia.
Qed.

Lemma H_twentyone_entry n:
  H (21+n*27) -->* 0inf <* (rev H_U) <* [1]^^410 <* <[0;1]^^485 <* [0]
    {{B}}> ([0]++[1]^^971)^^(n*3) *> [0] *> [1]^^973 *> 0inf.
Proof.
  follow (H_sweep_entry (1+n*3)).
  unfold H_U, Post; es' n.
Qed.

Lemma H_twentyone n: H (21+n*27) -->* S (3361+n*3888).
Proof.
  follow (H_twentyone_entry n).
  follow (B_complete 485 n (0inf <* (rev H_U) <* [1]^^410 <* <[0;1]^^485 <* [0])).
  follow (C_absorb_alt 485 (487+n*1944) 409 (0inf <* (rev H_U))).
  applys_eq (H_U_finish (1663+n*1944)); flia.
Qed.
Definition T_tail : list (nat*nat*nat) :=
  ([(1,1,1);(1,1,1);(1,37,1)]^^8 ++ [(1,1,1);(1,1,1)])%nat.
Definition T_period := T_tail ++ [(1,1009,1)]%nat.
Definition T n := 0inf <{{A}} [1]^^439 *> [0] *> [1]^^3 *>
  TripleWord (T_period^^n ++ T_tail) *> Field 1 *> Field 1010 *> 0inf.

Lemma T_entry n:
  T n -->* 0inf <{{A}} Post (repeat 5 36) *> [1]^^(3037+n*3024) *> 0inf.
Proof.
  unfold T; follow (Root7_ordered 36 (T_period^^n ++ T_tail) 1 1010).
  rewrite triple_mass_app, triple_mass_power.
  change (triple_mass T_period) with 1512%nat.
  change (triple_mass T_tail) with 496%nat.
  replace (21+(1*2+1010+(n*1512+496))*2)%nat with (3037+n*3024)%nat by lia.
  finish.
Qed.

Lemma Next36 a:
  0inf <{{A}} Post (repeat 5 36) *> [1]^^(1+a*2) *> 0inf -->* S (593+a*2).
Proof. unfold S, Post; es' a. Qed.

Lemma H_zero: H 0 -->* S 55.
Proof. unfold H, S; finish. Qed.

Local Opaque S.
Lemma T_return n: T n -->* S (3629+n*3024).
Proof.
  follow (T_entry n).
  replace (3037+n*3024) with (1+(1518+n*1512)*2)%nat by lia.
  replace (3629+n*3024) with (593+(1518+n*1512)*2)%nat by lia.
  apply Next36.
Qed.
Definition V2_word c := [1;1] ++ [0;1;1;1]^^242 ++ [0] ++ [1]^^c.

Lemma H_thirty_entry n:
  H (30+n*27) -->* 0inf <* (rev H_U) <* [1]^^408
    <* (rev (Block 2 485 1943))^^n <* (rev (Block 2 485 1945)) <* [0] {{D}}> 0inf.
Proof.
  follow (H_sweep_entry (2+n*3)).
  unfold H_U, Post, Block; es' n.
Qed.

Lemma H_V2_entry n:
  H (30+n*27) -->* 0inf <* (rev H_U) <* [1]^^408 <{{B}}
    [0] *> (V2_word 1945)^^n *> V2_word 1949 *> 0inf.
Proof.
  follow (H_thirty_entry n).
  follow (D_blank (0inf <* (rev H_U) <* [1]^^408
    <* (rev (Block 2 485 1943))^^n <* (rev (Block 2 485 1945)))).
  follow (B_half 242 972 (0inf <* (rev H_U) <* [1]^^408 <* (rev (Block 2 485 1943))^^n)
    ([1;1] *> 0inf)).
  follow (B_half_power n 242 971 (0inf <* (rev H_U) <* [1]^^408)
    ([1;1] *> [0;1;1;1]^^242 *> [0] *> [1]^^1947 *> [1;1] *> 0inf)).
  unfold V2_word; simpl_tape; finish.
Qed.

Lemma V2_fields n r:
  (V2_word 1945)^^n *> V2_word 1949 *> r =
  [1;1] *> (Fields (repeat 1 242 ++ [973])%nat)^^n *>
    Fields (repeat 1 242 ++ [974])%nat *> r.
Proof.
  induction n.
  - cbn [lpow]; reflexivity.
  - cbn [lpow]; rewrite Str_app_assoc, IHn.
    cbn [V2_word]; rewrite !Fields_app, !Fields_repeat.
    cbn [Fields flat_map Field]; simpl_tape; reflexivity.
Qed.

Lemma V2_caller:
  sideRLs (flip tm) ([((B,[0;1;1]),(D,[0]))]^^4)
    (0inf <* (rev H_U) <* [1]^^408) (0inf <* [1]^^435).
Proof.
  change 4 with (3+1)%nat; rewrite lpow_add.
  eapply sideRLs_trans; [apply (caller_list [2;0;4]%nat 204 0inf)|].
  applys_eq (caller_one 216 0inf); simpl_tape; reflexivity.
Qed.

Definition T_runs c := ((repeat 1 8 ++ [37])^^8 ++ repeat 1 8 ++ [c])%nat.

Lemma TripleWord_app xs ys: TripleWord (xs++ys) = TripleWord xs ++ TripleWord ys.
Proof.
  induction xs as [|[[a b] c] xs IH]; cbn [TripleWord app];
    rewrite ?IH; repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma TripleWord_power xs n: TripleWord (xs^^n) = (TripleWord xs)^^n.
Proof. induction n; cbn [lpow]; rewrite ?TripleWord_app, ?IHn; reflexivity. Qed.

Lemma T_fields n r:
  (Fields (T_runs 1009))^^n *> Fields (T_runs 1010) *> r =
  Field 1 *> TripleWord (T_period^^n ++ T_tail) *> Field 1 *> Field 1010 *> r.
Proof.
  rewrite TripleWord_app, TripleWord_power, !Str_app_assoc.
  change (Fields (T_runs 1009)) with (Field 1 ++ (TripleWord T_tail ++ Field 1 ++ Field 1009)).
  change (Fields (T_runs 1010)) with (Field 1 ++ TripleWord T_tail ++ Field 1 ++ Field 1010).
  change (TripleWord T_period) with ((TripleWord T_tail ++ Field 1 ++ Field 1009) ++ Field 1).
  rewrite !Str_app_assoc, lpow_rotate'; reflexivity.
Qed.

Lemma B_odd_root c r:
  0inf <* [1]^^(1+c*2) <{{B}} [0] *> r -->* 0inf <{{A}} [1]^^(3+c*2) *> r.
Proof. applys_eq (B_odd_bridge c 0inf r); solve_const0_eq. Qed.

Lemma H_to_T n: H (30+n*27) -->* T n.
Proof.
  follow (H_V2_entry n); rewrite V2_fields.
  follow (sideRLs_concat_1L
    (right_sweeps 4 n (repeat 1 242 ++ [973])%nat (T_runs 1009)
      (repeat 1 242 ++ [974])%nat (T_runs 1010) eq_refl eq_refl) V2_caller).
  cbn [to_DH_config sweep_h]; rewrite T_fields.
  follow (B_odd_root 217
    ([1;1] *> Field 1 *> TripleWord (T_period^^n ++ T_tail) *> Field 1 *> Field 1010 *> 0inf)).
  unfold T; simpl_tape; finish.
Qed.

Lemma H_thirty n: H (30+n*27) -->* S (3629+n*3024).
Proof. follow (H_to_T n); apply T_return. Qed.

Lemma H_return k: exists a, H k -->* S (1+a*2).
Proof.
  destruct (Nat.lt_ge_cases k 4) as [Hk|Hk].
  - destruct k as [|[|[|k]]].
    + exists 27; apply H_zero.
    + exists 113; apply H_one.
    + exists 168; apply (H_two 0).
    + assert (k=0)%nat by lia; subst; exists 220; apply H_three.
  - assert (k mod 3=0 \/ k mod 3=1 \/ k mod 3=2)%nat as Hr by lia.
    destruct Hr as [Hr|[Hr|Hr]].
    + assert (k mod 9=0 \/ k mod 9=3 \/ k mod 9=6)%nat as H9 by lia.
      destruct H9 as [H9|[H9|H9]].
      * exists (917+(k/9-1)*864)%nat; applys_eq (H_nine (k/9-1)); flia.
      * assert (k mod 27=3 \/ k mod 27=12 \/ k mod 27=21)%nat as H27 by lia.
        destruct H27 as [H27|[H27|H27]].
        -- exists (1814+(k/27-1)*1512)%nat; applys_eq (H_thirty (k/27-1)); flia.
        -- exists (873+(k/27)*1944)%nat; applys_eq (H_twelve (k/27)); flia.
        -- exists (1680+(k/27)*1944)%nat; applys_eq (H_twentyone (k/27)); flia.
      * exists (559+(k/9)*864)%nat; applys_eq (H_six (k/9)); flia.
    + exists (297+(k/3-1)*216)%nat; applys_eq (H_four (k/3-1)); flia.
    + exists (168+(k/3)*216)%nat; applys_eq (H_two (k/3)); flia.
Qed.
Definition P z := 0inf <{{A}} Post [3;5]%nat *> [1]^^z *> 0inf.
Definition Q n := 0inf <{{A}} [1]^^25 *> ([0]++[1]^^11)^^n *> [0] *> [1]^^13 *> 0inf.
Definition Q_L := Post [2;0;4;0]%nat.

Lemma P_to_Q n: P (11+n*12) -->* Q n.
Proof. unfold P, Q, Post; es' n. Qed.

Lemma Q_D1 n:
  Q (1+n*3) -->* 0inf <* (rev Q_L) <* (rev (Block 20 5 5))^^n <{{D}} [1]^^46 *> 0inf.
Proof. unfold Q, Q_L, Block, Post; es' n. Qed.

Lemma Q_D2 n:
  Q (2+n*3) -->* 0inf <* (rev Q_L) <* (rev (Block 20 5 5))^^n <{{D}} [1]^^60 *> 0inf.
Proof. unfold Q, Q_L, Block, Post; es' n. Qed.

Lemma Q_L_finish a:
  0inf <* (rev Q_L) <{{D}} [1]^^(a*2) *> 0inf -->* P (1+a*2).
Proof. unfold Q_L, P, Post; es' a. Qed.

Lemma Q_one_P n: Q (1+n*3) -->* P (47+n*48).
Proof.
  follow (Q_D1 n).
  follow (D_block_power n 10 5 2 23 (0inf <* (rev Q_L))).
  applys_eq (Q_L_finish (23+n*24)); flia.
Qed.

Lemma Q_two_P n: Q (2+n*3) -->* P (61+n*48).
Proof.
  follow (Q_D2 n).
  follow (D_block_power n 10 5 2 30 (0inf <* (rev Q_L))).
  applys_eq (Q_L_finish (30+n*24)); flia.
Qed.

Lemma P_one_entry n:
  P (1+n*12) -->* 0inf <* [1]^^18 <* [0] <* (rev M9)^^n <* [1]^^6 {{C}}> 0inf.
Proof. unfold P, Post, M9; es' n. Qed.

Lemma P_one n: P (1+n*12) -->* S (31+n*16).
Proof.
  follow (P_one_entry n).
  change M9 with (Block 9 1 0).
  follow (C_block_power n 8 1 0 6 4 3 (0inf <* [1]^^18 <* [0]) ltac:(lia) ltac:(lia)).
  follow (absorb_run (3+n*8) 17 0inf).
  apply progress_evstep; applys_eq (finish_odd (13+n*8)); flia.
Qed.

Lemma Q_loop n: Q (1+n*3) -->* Q (3+n*4).
Proof. follow (Q_one_P n); applys_eq (P_to_Q (3+n*4)); flia. Qed.

Lemma Q_two n: Q (2+n*3) -->* S (111+n*64).
Proof. follow (Q_two_P n); applys_eq (P_one (5+n*4)); flia. Qed.

Lemma Q_to_H n: Q (n*9) -->* H n.
Proof. unfold Q, H; es' n. Qed.

Lemma Q_three_entry n:
  Q (3+n*9) -->* 0inf <* [1]^^5 <* <[0;1;0] <* [1]^^34
    <* (rev (Block 2 17 71))^^n <* [1]^^57 {{C}}> 0inf.
Proof. unfold Q, Block; es' n. Qed.

Lemma Q_six_entry n:
  Q (6+n*9) -->* 0inf <* [1]^^5 <* <[0;1;0]
    <* (rev (Block 36 17 12)) <* (rev (Block 61 17 12))^^n <* [1]^^26 {{C}}> 0inf.
Proof. unfold Q, Block; es' n. Qed.

Local Transparent S.
Lemma Q_C_finish n:
  0inf <* [1]^^5 <* <[0;1;0] <* [1]^^(1+n*6) {{C}}> 0inf -->* S (19+n*6).
Proof. unfold S; es' n. Qed.
Local Opaque S.

Lemma Q_three n: Q (3+n*9) -->* S (109+n*144).
Proof.
  follow (Q_three_entry n).
  follow (C_block_power n 1 17 71 57 36 64 (0inf <* [1]^^5 <* <[0;1;0] <* [1]^^34)
    ltac:(lia) ltac:(lia)).
  rewrite lpow_add'; applys_eq (Q_C_finish (15+n*24)); flia.
Qed.

Lemma Q_six n: Q (6+n*9) -->* S (163+n*144).
Proof.
  follow (Q_six_entry n).
  follow (C_block_power n 60 17 12 26 36 19
    (0inf <* [1]^^5 <* <[0;1;0] <* (rev (Block 36 17 12))) ltac:(lia) ltac:(lia)).
  follow (C_block (19+n*72) 35 17 12 (26+n*144)
    (0inf <* [1]^^5 <* <[0;1;0]) ltac:(lia)).
  applys_eq (Q_C_finish (24+n*24)); flia.
Qed.

Lemma Q_nonone n: n mod 3<>1%nat -> exists a, Q n -->* S (1+a*2).
Proof.
  intro Hr; assert (n mod 3=0 \/ n mod 3=2)%nat as H3 by lia.
  destruct H3 as [H3|H3].
  - assert (n mod 9=0 \/ n mod 9=3 \/ n mod 9=6)%nat as H9 by lia.
    destruct H9 as [H9|[H9|H9]].
    + destruct (H_return (n/9)) as [a Ha]; exists a.
      follow (Q_to_H (n/9)); apply Ha.
    + exists (54+(n/9)*72)%nat; applys_eq (Q_three (n/9)); flia.
    + exists (81+(n/9)*72)%nat; applys_eq (Q_six (n/9)); flia.
  - exists (55+(n/3)*32)%nat; applys_eq (Q_two (n/3)); flia.
Qed.

Lemma Q_rank e n u:
  u mod 3<>0%nat -> n+5=3^e*u -> exists a, Q n -->* S (1+a*2).
Proof.
  revert n u; induction e; intros n u Hu He.
  - apply Q_nonone; cbn [Nat.pow] in He; lia.
  - assert (n mod 3=1)%nat as Hr by (cbn [Nat.pow] in He; nia).
    destruct (IHe (3+(n/3)*4) (u*4) ltac:(lia) ltac:(cbn [Nat.pow] in He; nia)) as [a Ha].
    exists a; follow (Q_loop (n/3)); apply Ha.
Qed.

Lemma factor_three x:
  (0<x)%nat -> exists e u, x=3^e*u /\ u mod 3<>0%nat.
Proof.
  induction x as [x IH] using lt_wf_ind; intro Hx.
  destruct (Nat.eq_dec (x mod 3) 0%nat) as [Hx3|Hx3].
  - assert (Hxq: x=(x/3)*3) by (pose proof (Nat.div_mod x 3 ltac:(lia)); lia).
    destruct (IH (x/3) ltac:(apply Nat.div_lt; lia) ltac:(lia)) as [e [u [He Hu]]].
    exists (Datatypes.S e), u; split; [rewrite Nat.pow_succ_r'; nia|assumption].
  - exists 0%nat, x; cbn; auto.
Qed.

Lemma Q_return n: exists a, Q n -->* S (1+a*2).
Proof.
  destruct (factor_three (n+5) ltac:(lia)) as [e [u [He Hu]]].
  exact (Q_rank e n u Hu He).
Qed.
(* The three 35-column families share their entire interior; only the
   untailed endpoint is separate. Tail parameters denote positive odd runs. *)
Definition U n := 0inf <{{A}} [1]^^25 *> ([0]++[1]^^35)^^n *> 0inf.
Definition R35 n a := 0inf <{{A}} [1]^^25 *> ([0]++[1]^^35)^^n *>
  [0] *> [1]^^(1+a*2) *> 0inf.
Definition Chain r c n a l :=
  l <* (rev (Block 0 r c))^^n <* <[0;1]^^r <* [0] <* [1]^^a {{C}}> 0inf.
Definition C0 n a := Chain 17 73 n a (0inf <* (rev Q_L) <* [1]^^44).
Definition Z n a := 0inf <* [1]^^5 <* [0] <* [1]^^64
  <* (rev (Block 0 1 105))^^n <* <[0;1;0] <* [1]^^(1+a*2) {{C}}> 0inf.

Lemma U_D n:
  U (n*3) -->* 0inf <* (rev Q_L) <* (rev (Block 44 17 29))^^n <{{D}} [1]^^10 *> 0inf.
Proof. unfold U, Q_L, Post, Block; es' n. Qed.

Lemma U_three n: U (n*3) -->* Q (n*12).
Proof.
  follow (U_D n).
  follow (D_block_power n 22 17 14 5 (0inf <* (rev Q_L))).
  follow (Q_L_finish (5+n*72)).
  replace (1+(5+n*72)*2) with (11+(n*12)*12) by lia; apply P_to_Q.
Qed.

Lemma U_two_entry n: U (2+n*3) -->* C0 n 1.
Proof. unfold U, C0, Chain, Q_L, Post, Block; es' n. Qed.

Lemma R35_one_entry n a:
  R35 (1+n*3) a -->* 0inf <* (rev Q_L) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^(1+a) {{C}}> 0inf.
Proof. unfold R35, Q_L, Post, Block; es' n a. Qed.

Lemma R35_two_entry n a: R35 (2+n*3) a -->* C0 n (2+a*2).
Proof. unfold R35, C0, Chain, Q_L, Post, Block; es' n a. Qed.

Lemma R35_D n r:
  0inf <{{A}} [1]^^25 *> ([0]++[1]^^35)^^(n*3) *> [0] *> r -->*
  0inf <* (rev Q_L) <* (rev (Block 44 17 29))^^n <* [1]^^7 <* [0] {{D}}> r.
Proof. unfold Q_L, Post, Block; es' n & r. Qed.

Lemma D_tail b a l:
  l <* [1]^^b <* [0] {{D}}> [1]^^(1+a*2) *> 0inf -->*
  l <* [1]^^(1+b+a*2) {{C}}> 0inf.
Proof.
  follow (D_last (a*2) (l <* [1]^^b) 0inf).
  rewrite lpow_add'; replace (1+a*2+b) with (1+b+a*2) by lia; simpl_tape; finish.
Qed.

Lemma R35_zero_entry n a:
  R35 (n*3) a -->* 0inf <* (rev Q_L) <* (rev (Block 44 17 29))^^n
    <* [1]^^(8+a*2) {{C}}> 0inf.
Proof.
  unfold R35; follow (R35_D n ([1]^^(1+a*2) *> 0inf)).
  apply D_tail.
Qed.

Lemma R35_three_entry n a: R35 (3+n*3) a -->* C0 n (37+a*2).
Proof.
  follow (R35_zero_entry (1+n) a).
  unfold C0, Chain, Q_L, Post, Block; es' n a.
Qed.

Definition C1 n a := 0inf <* (rev (Post [2;0;4]%nat)) <* [1]^^48
  <* (rev (Fields [0;4;0;4;0;40]%nat))^^n
  <* (rev (Fields [0;4;0;4;0]%nat)) <* [0] <* [1]^^(9+a*2) {{C}}> 0inf.
Definition C2 n a := Chain 5 97 n (25+a*2) (0inf <* (rev (Post [2;0]%nat)) <* [1]^^60).

Lemma C0_E n a:
  C0 n (1+a*2) -->* 0inf <* (rev (Post [2;0;4]%nat)) <* [1]^^48 {{E}}>
    (Post (repeat 1 8 ++ [37])%nat)^^n *> Post (repeat 1 8)%nat *> [1]^^(5+a*2) *> 0inf.
Proof. unfold C0, Chain, Q_L, Post, Block; es' n a. Qed.

Lemma E_C1_D n l r:
  l {{E}}> (Post (repeat 1 8 ++ [37])%nat)^^n *> Post (repeat 1 8)%nat *> r -->*
  l <* (rev (Fields [0;4;0;4;0;40]%nat))^^n
    <* (rev (Fields [0;4;0;4;0]%nat)) <* [0] <* [1]^^4 <* [0] {{D}}> r.
Proof. unfold Post, Fields, Field; es' n & l r. Qed.

Lemma C0_C1 n a: C0 n (1+a*2) -->* C1 n a.
Proof.
  follow (C0_E n a).
  follow (E_C1_D n (0inf <* (rev (Post [2;0;4]%nat)) <* [1]^^48) ([1]^^(5+a*2) *> 0inf)).
  unfold C1; apply (D_tail 4 (2+a)).
Qed.

Lemma C1_E n a:
  C1 n a -->* 0inf <* (rev (Post [2;0]%nat)) <* [1]^^60 {{E}}>
    (Post [5;5;41]%nat)^^n *> Post [5;5]%nat *> [1]^^(13+a*2) *> 0inf.
Proof. unfold C1, Post, Fields, Field; es' n a. Qed.

Lemma E_C2_D n l r:
  l {{E}}> (Post [5;5;41]%nat)^^n *> Post [5;5]%nat *> r -->*
  l <* (rev (Block 0 5 97))^^n <* <[0;1]^^5 <* [0] <* [1]^^12 <* [0] {{D}}> r.
Proof. unfold Post, Block; es' n & l r. Qed.

Lemma C1_D n a:
  C1 n a -->* 0inf <* (rev (Post [2;0]%nat)) <* [1]^^60
    <* (rev (Block 0 5 97))^^n <* <[0;1]^^5 <* [0] <* [1]^^12 <* [0]
    {{D}}> [1]^^(13+a*2) *> 0inf.
Proof. follow (C1_E n a); apply E_C2_D. Qed.

Lemma C1_C2 n a: C1 n a -->* C2 n a.
Proof. follow (C1_D n a); unfold C2, Chain; apply (D_tail 12 (6+a)). Qed.

Lemma C2_E n a:
  C2 n a -->* 0inf <* [1]^^5 <* [0] <* [1]^^64 {{E}}>
    (Post [1;1;49]%nat)^^n *> Post [1;1]%nat *> [1]^^(29+a*2) *> 0inf.
Proof. unfold C2, Chain, Post, Block; es' n a. Qed.

Lemma E_C3_D n l r:
  l {{E}}> (Post [1;1;49]%nat)^^n *> Post [1;1]%nat *> r -->*
  l <* (rev (Block 0 1 105))^^n <* <[0;1;0] <* [1]^^4 <* [0] {{D}}> r.
Proof. unfold Post, Block; es' n & l r. Qed.

Lemma C2_D n a:
  C2 n a -->* 0inf <* [1]^^5 <* [0] <* [1]^^64
    <* (rev (Block 0 1 105))^^n <* <[0;1;0] <* [1]^^4 <* [0]
    {{D}}> [1]^^(29+a*2) *> 0inf.
Proof. follow (C2_E n a); apply E_C3_D. Qed.

Lemma C2_Z n a: C2 n a -->* Z n (16+a).
Proof.
  follow (C2_D n a); unfold Z; apply (D_tail 4 (14+a)).
Qed.

Lemma C0_Z n a: C0 n (1+a*2) -->* Z n (16+a).
Proof. follow (C0_C1 n a); follow (C1_C2 n a); apply C2_Z. Qed.

Lemma U_R35 n: U (1+n) = R35 n 17.
Proof.
  replace (1+n) with (n+1) by lia; unfold U, R35.
  rewrite lpow_add; cbn [lpow]; rewrite !app_nil_r, !Str_app_assoc; reflexivity.
Qed.

Lemma U_four_Z n: U (4+n*3) -->* Z n 51.
Proof.
  replace (4+n*3) with (1+(3+n*3)) by lia; rewrite U_R35.
  follow (R35_three_entry n 17); apply (C0_Z n 35).
Qed.

Lemma Z_zero a:
  Z 0 a -->* 0inf <* [1]^^72 <* <[0;1]^^(3+a) {{C}}> 0inf.
Proof. unfold Z, Block; es' a. Qed.

Lemma Z_three n a:
  Z (n*3) a -->* 0inf <* [1]^^72 <* (rev (Block 0 53 217))^^n
    <* <[0;1]^^(3+a) {{C}}> 0inf.
Proof. unfold Z, Block; es' n a. Qed.

Lemma Z_one n a: Z (1+n*3) a -->* Chain 53 217 n (6+a*2) (0inf <* [1]^^72).
Proof. unfold Z, Chain, Block; es' n a. Qed.

Lemma Z_E n a:
  Z (1+n) a -->* 0inf <* [1]^^72 {{E}}>
    (Post [53%nat])^^(1+n) *> [1]^^(5+a*2) *> 0inf.
Proof. unfold Z, Post, Block; es' n a. Qed.

Lemma E_Z_D n l r:
  l {{E}}> (Post [53%nat])^^(2+n*3) *> r -->*
  l <* (rev (Block 0 53 217))^^n <* <[0;1]^^53 <* [0]
    <* [1]^^108 <* [0] {{D}}> r.
Proof. unfold Post, Block; es' n & l r. Qed.

Lemma Z_two_D n a:
  Z (2+n*3) a -->* 0inf <* [1]^^72 <* (rev (Block 0 53 217))^^n
    <* <[0;1]^^53 <* [0] <* [1]^^108 <* [0] {{D}}> [1]^^(5+a*2) *> 0inf.
Proof. follow (Z_E (1+n*3) a); apply E_Z_D. Qed.

Lemma Z_two n a: Z (2+n*3) a -->* Chain 53 217 n (113+a*2) (0inf <* [1]^^72).
Proof. follow (Z_two_D n a); unfold Chain; apply (D_tail 108 (2+a)). Qed.

(* A train with an even last run is absorbed without inspecting its
   interior. The final even left run is used only after the odd train. *)
Lemma Chain_even r c n a b l:
  Chain r (1+c*2) n (a*2) (l <* [1]^^(1+b)) -->*
  l <* [1]^^(4+b+a*2+r*4+n*(4+c*2+r*4)) {{C}}> 0inf.
Proof.
  revert a b l; induction n; intros a b l; unfold Chain.
  - cbn [lpow]; applys_eq (C_absorb_alt r a b l); flia.
  - cbn [lpow]; rewrite <- lpow_shift, !Str_app_assoc.
    unfold Block; rewrite !rev_app_distr, !rev_power; simpl_tape.
    unfold Chain, Block in IHn; rewrite !rev_app_distr, !rev_power in IHn.
    follow (IHn a (c*2) (l <* [1]^^(1+b) <* <[0;1]^^r <* [0])).
    applys_eq (C_absorb_alt r (2+c+a+r*2+n*(2+c+r*2)) b l); flia.
    rewrite !lpow_add'; flia.
    change ([1]^^(4+(b+a*2+r*4+(4+(c*2+r*4+n*(4+(c*2+r*4)))))) *> l =
      [1]^^(4+b+(2+c+a+r*2+n*(2+c+r*2)+r*2)*2) *> l).
    flia.
Qed.
Lemma Q_L_C a:
  0inf <* (rev Q_L) <* [1]^^(1+a*2) {{C}}> 0inf -->* P (5+a*2).
Proof. unfold Q_L, P, Post; es' a. Qed.

Lemma C0_even n a: C0 n (a*2) -->* P (119+a*2+n*144).
Proof.
  unfold C0; follow (Chain_even 17 36 n a 43 (0inf <* (rev Q_L))).
  applys_eq (Q_L_C (57+a+n*72)); flia.
Qed.

Lemma Z_one_return n a: Z (1+n*3) a -->* S (297+a*2+n*432).
Proof.
  follow (Z_one n a).
  follow (Chain_even 53 108 n (3+a) 71 0inf).
  apply progress_evstep; applys_eq (finish_odd (146+a+n*216)); flia.
Qed.

Definition K n a := 0inf <{{A}} [1]^^77 *>
  (Field 5^^8++Field 113)^^n *> Field 5^^8 *> Field a *> 0inf.
Definition K_L := Post ([2;0]++[4;0]^^5++[3])%nat.

Definition K_C n a := 0inf <* (rev K_L) <* [1]^^9 <* <[0;1;0] <* [1]^^28
  <* (rev (Block 0 5 25++Block 0 5 241++Block 0 5 25))^^n
  <* (rev (Block 0 5 25)) <* <[0;1]^^5 <* [0] <* [1]^^(13+a*2) {{C}}> 0inf.

Lemma K_D n r:
  0inf <{{A}} [1]^^77 *> (Field 5^^8++Field 113)^^n *> Field 5^^8 *> [0] *> r -->*
  0inf <* (rev K_L) <* [1]^^9 <* <[0;1;0] <* [1]^^28
    <* (rev (Block 0 5 25++Block 0 5 241++Block 0 5 25))^^n
    <* (rev (Block 0 5 25)) <* <[0;1]^^5 <* [0] <* [1]^^12 <* [0] {{D}}> r.
Proof. unfold K_L, Post, Field, Block; es' n & r. Qed.

Lemma K_first n a: K n a -->* K_C n a.
Proof.
  unfold K; follow (K_D n ([1]^^(1+a*2) *> 0inf)).
  unfold K_C; apply (D_tail 12 a).
Qed.

Lemma K_C_E n a:
  K_C n a -->* 0inf <* (rev K_L) <* [1]^^44 {{E}}>
    (Post [17;125;17]%nat)^^n *> Post [17%nat] *> [1]^^(25+a*2) *> 0inf.
Proof. unfold K_C, K_L, Post, Block; es' n a. Qed.

Lemma K_E n a:
  K n a -->* 0inf <* (rev K_L) <* [1]^^44 {{E}}>
    (Post [17;125;17]%nat)^^n *> Post [17%nat] *> [1]^^(25+a*2) *> 0inf.
Proof. follow (K_first n a); apply K_C_E. Qed.

Lemma K_E_scan n a l:
  l {{E}}> (Post [17;125;17]%nat)^^n *> Post [17%nat] *> [1]^^(25+a*2) *> 0inf -->*
  Chain 17 289 n (26+a*2) l.
Proof. unfold Post, Chain, Block; es' n a & l. Qed.

Lemma K_entry n a:
  K n a -->* Chain 17 289 n (26+a*2) (0inf <* (rev K_L) <* [1]^^44).
Proof. follow (K_E n a); apply K_E_scan. Qed.

Local Transparent S.
Lemma K_finish a:
  0inf <* (rev K_L) <* [1]^^(1+a*2) {{C}}> 0inf -->* S (113+a*2).
Proof. unfold K_L, Post, S; es' a. Qed.
Local Opaque S.

Lemma K_return n a: K n a -->* S (253+a*2+n*360).
Proof.
  follow (K_entry n a).
  follow (Chain_even 17 144 n (13+a) 43 (0inf <* (rev K_L))).
  applys_eq (K_finish (70+a+n*180)); flia.
Qed.

Lemma Chain_K_E n a:
  Chain 53 217 n (1+a*2) (0inf <* [1]^^72) -->* 0inf <* [1]^^75 {{E}}>
    (Post (repeat 1 26++[109])%nat)^^n *> Post (repeat 1 26)%nat *> [1]^^(5+a*2) *> 0inf.
Proof. unfold Chain, Block, Post; es' n a. Qed.

Definition K_back n a := 0inf <* [1]^^75
  <* (rev (Fields ([0;4]^^8++[0;112])%nat))^^n
  <* (rev (Fields ([0;4]^^8++[0])%nat)) <* [0] <* [1]^^(9+a*2) {{C}}> 0inf.

Lemma E_K_D n l r:
  l {{E}}> (Post (repeat 1 26++[109])%nat)^^n *> Post (repeat 1 26)%nat *> r -->*
  l <* (rev (Fields ([0;4]^^8++[0;112])%nat))^^n
    <* (rev (Fields ([0;4]^^8++[0])%nat)) <* [0] <* [1]^^4 <* [0] {{D}}> r.
Proof. unfold Post, Fields, Field; es' n & l r. Qed.

Lemma K_back_tail a l:
  l <* (rev (Fields ([0;4]^^8++[0])%nat)) <* [0] <* [1]^^(9+a*2) {{C}}> 0inf -->*
  l <* <[0;1] <{{A}} Post (repeat 5 8)%nat *> [1]^^(13+a*2) *> 0inf.
Proof. unfold Fields, Field, Post; es' a & l. Qed.

Lemma K_back_scan n l r:
  l <* (rev (Fields ([0;4]^^8++[0;112])%nat))^^n <* <[0;1] <{{A}} r -->*
  l <* <[0;1] <{{A}} (Post (repeat 5 8++[113])%nat)^^n *> r.
Proof.
  revert l r; induction n; intros l r; cbn [lpow]; [finish|].
  rewrite Str_app_assoc.
  eapply evstep_trans with (c':=
    l <* (rev (Fields ([0;4]^^8++[0;112])%nat))^^n <* <[0;1] <{{A}}
      Post (repeat 5 8++[113])%nat *> r).
  - applys_eq (A_return_list (repeat 4 8++[112])%nat
      (l <* (rev (Fields ([0;4]^^8++[0;112])%nat))^^n <* <[0;1]) r);
      cbn [Pairs Fields Field Post map repeat lpow app]; simpl_tape; reflexivity.
  - applys_eq (IHn l (Post (repeat 5 8++[113])%nat *> r));
      rewrite <- !Str_app_assoc, lpow_shift; reflexivity.
Qed.

Lemma Post_Fields xs r: [0] *> Post xs *> r = Fields xs *> [0] *> r.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change ([0] *> ([1]^^(1+x*2)++[0]++Post xs) *> r =
    ([0]++[1]^^(1+x*2)++Fields xs) *> [0] *> r).
  rewrite !Str_app_assoc.
  exact (f_equal (fun t => [0] *> [1]^^(1+x*2) *> t) IH).
Qed.

Lemma Post_Fields_power n xs r:
  [0] *> (Post xs)^^n *> r = (Fields xs)^^n *> [0] *> r.
Proof.
  induction n; cbn [lpow]; [reflexivity|].
  rewrite !Str_app_assoc, Post_Fields, IHn; reflexivity.
Qed.

Lemma A_odd_root_pair a r:
  0inf <* [1]^^(1+a*2) <* <[0;1] <{{A}} r -->*
  0inf <{{A}} [1]^^(3+a*2) *> [0] *> r.
Proof. applys_eq (return_pair a 0inf r); solve_const0_eq. Qed.

Lemma K_back_return n a: K_back n a -->* K n (6+a).
Proof.
  unfold K_back; follow (K_back_tail a (0inf <* [1]^^75
    <* (rev (Fields ([0;4]^^8++[0;112])%nat))^^n)).
  follow (K_back_scan n (0inf <* [1]^^75)
    (Post (repeat 5 8)%nat *> [1]^^(13+a*2) *> 0inf)).
  follow (A_odd_root_pair 37 ((Post (repeat 5 8++[113])%nat)^^n *>
    Post (repeat 5 8)%nat *> [1]^^(13+a*2) *> 0inf)).
  rewrite Post_Fields_power, Post_Fields, Fields_app, !Fields_repeat.
  unfold K, Fields, Field; simpl_tape; finish; flia.
Qed.

Lemma Chain_K n a:
  Chain 53 217 n (1+a*2) (0inf <* [1]^^72) -->* K n (6+a).
Proof.
  follow (Chain_K_E n a).
  follow (E_K_D n (0inf <* [1]^^75) ([1]^^(5+a*2) *> 0inf)).
  eapply evstep_trans with (c':=K_back n a).
  - unfold K_back; apply (D_tail 4 (2+a)).
  - apply K_back_return.
Qed.

Lemma Z_two_return n a: Z (2+n*3) a -->* S (377+a*2+n*360).
Proof.
  follow (Z_two n a); follow (Chain_K n (56+a)).
  applys_eq (K_return n (62+a)); flia.
Qed.
Lemma Z_16_entry n:
  Z (n*3) 16 -->* 0inf <* [1]^^70 <* (rev (Block 2 53 215))^^n
    <* [0] <* [1]^^54 {{C}}> 0inf.
Proof. follow (Z_three n 16); unfold Block; es' n. Qed.

Lemma Z_40_entry n:
  Z (n*3) 40 -->* 0inf <* [1]^^70 <* (rev (Block 2 53 215))^^n
    <* [0] <* [1]^^118 {{C}}> 0inf.
Proof. follow (Z_three n 40); unfold Block; es' n. Qed.

Lemma Z_48_entry n:
  Z (n*3) 48 -->* 0inf <* [1]^^68 <* (rev (Block 4 53 213))^^n
    <* [0] <* [1]^^144 {{C}}> 0inf.
Proof. follow (Z_three n 48); unfold Block; es' n. Qed.

Lemma Z_51_tail l:
  l <* [1]^^2 <* <[0;1]^^54 {{C}}> 0inf -->*
  l <{{B}} [0;1;1] *> [0;1;1;1]^^26 *> [0] *> [1]^^5 *> 0inf.
Proof. es' & l. Qed.

Lemma Z_51_left n:
  Z (n*3) 51 -->* 0inf <* [1]^^70 <* (rev (Block 2 53 215))^^n
    <{{B}} [0;1;1] *> [0;1;1;1]^^26 *> [0] *> [1]^^5 *> 0inf.
Proof.
  follow (Z_three n 51).
  eapply evstep_trans with (c':=0inf <* [1]^^70 <* (rev (Block 2 53 215))^^n
    <* [1]^^2 <* <[0;1]^^54 {{C}}> 0inf).
  - unfold Block; es' n.
  - apply Z_51_tail.
Qed.

Lemma Z_51_B n:
  Z (n*3) 51 -->* 0inf <* [1]^^70 <{{B}} [0;1;1] *>
    (Fields (repeat 1 26++[109])%nat)^^n *> Fields (repeat 1 26++[2])%nat *> 0inf.
Proof.
  follow (Z_51_left n).
  follow (B_half_power n 26 107 (0inf <* [1]^^70)
    ([1;1] *> [0;1;1;1]^^26 *> [0] *> [1]^^5 *> 0inf)).
  unfold Fields, Field; simpl_tape; finish.
  cbn [flat_map repeat lpow app]; simpl_rotate; reflexivity.
Qed.

Lemma Z_51_K n: Z (n*3) 51 -->* K n 6.
Proof.
  follow (Z_51_B n).
  assert (sideRLs (flip tm) [((B,[0;1;1]),(D,[0]))]
    (0inf <* [1]^^70) (0inf <* [1]^^73)) as HC.
  { applys_eq (caller_one 35 0inf); solve_const0_eq. }
  follow (sideRLs_concat_1L
    (right_sweeps 1 n (repeat 1 26++[109])%nat (repeat 5 8++[113])%nat
      (repeat 1 26++[2])%nat (repeat 5 8++[6])%nat eq_refl eq_refl)
    HC).
  follow (B_odd_root 36 ([1;1] *> (Fields (repeat 5 8++[113])%nat)^^n *>
    Fields (repeat 5 8++[6])%nat *> 0inf)).
  unfold K; rewrite !Fields_app, !Fields_repeat.
  unfold Fields, Field; simpl_tape; finish.
Qed.

Lemma Z_16_return n: Z (n*3) 16 -->* S (131+n*432).
Proof.
  follow (Z_16_entry n); follow (tagged_even n 69 0 53 107 27 0inf).
  apply progress_evstep; applys_eq (finish_odd (63+n*216)); flia.
Qed.

Lemma Z_40_return n: Z (n*3) 40 -->* S (195+n*432).
Proof.
  follow (Z_40_entry n); follow (tagged_even n 69 0 53 107 59 0inf).
  apply progress_evstep; applys_eq (finish_odd (95+n*216)); flia.
Qed.

Lemma Z_48_return n: Z (n*3) 48 -->* S (219+n*432).
Proof.
  follow (Z_48_entry n); follow (tagged_even n 67 1 53 106 72 0inf).
  apply progress_evstep; applys_eq (finish_odd (107+n*216)); flia.
Qed.

Lemma Z_return n a:
  (a=16 \/ a=40 \/ a=48 \/ a=51)%nat -> exists b, Z n a -->* S (1+b*2).
Proof.
  intro Ha; assert (n mod 3=0 \/ n mod 3=1 \/ n mod 3=2)%nat as Hr by lia.
  destruct Hr as [Hr|[Hr|Hr]].
  - replace n with ((n/3)*3) by lia; destruct Ha as [-> | [-> | [-> | ->]]].
    + exists (65+(n/3)*216)%nat; applys_eq (Z_16_return (n/3)); flia.
    + exists (97+(n/3)*216)%nat; applys_eq (Z_40_return (n/3)); flia.
    + exists (109+(n/3)*216)%nat; applys_eq (Z_48_return (n/3)); flia.
    + exists (132+(n/3)*180)%nat.
      follow (Z_51_K (n/3)); applys_eq (K_return (n/3) 6); flia.
  - exists (148+a+(n/3)*216)%nat; applys_eq (Z_one_return (n/3) a); flia.
  - exists (188+a+(n/3)*180)%nat; applys_eq (Z_two_return (n/3) a); flia.
Qed.

Local Transparent S.
Lemma U_one: U 1 -->* S 77.
Proof. unfold U, S; es'. Qed.
Local Opaque S.

Lemma U_return n: exists a, U n -->* S (1+a*2).
Proof.
  assert (n mod 3=0 \/ n mod 3=1 \/ n mod 3=2)%nat as Hr by lia.
  destruct Hr as [Hr|[Hr|Hr]].
  - destruct (Q_return ((n/3)*12)) as [a Ha]; exists a.
    follow (U_three (n/3)); apply Ha.
  - destruct (Nat.eq_dec n 1) as [->|Hn].
    + exists 38%nat; apply U_one.
    + destruct (Z_return (n/3-1) 51 ltac:(auto)) as [a Ha]; exists a.
      follow (U_four_Z (n/3-1)); apply Ha.
  - destruct (Z_return (n/3) 16 ltac:(auto)) as [a Ha]; exists a.
    follow (U_two_entry (n/3)); follow (C0_Z (n/3) 0); apply Ha.
Qed.
Lemma P_five_entry n:
  P (5+n*36) -->* 0inf <* [1]^^16 <* [0]
    <* (rev (Block 25 5 0))^^n <* [1]^^14 {{C}}> 0inf.
Proof. unfold P, Post, Block; es' n. Qed.

Lemma P_five n: P (5+n*36) -->* S (37+n*48).
Proof.
  follow (P_five_entry n).
  follow (C_block_power n 24 5 0 14 12 7 (0inf <* [1]^^16 <* [0]) ltac:(lia) ltac:(lia)).
  follow (absorb_run (7+n*24) 15 0inf).
  apply progress_evstep; applys_eq (finish_odd (16+n*24)); flia.
Qed.

Lemma R35_zero a: R35 0 a -->* S (43+a*2).
Proof.
  follow (R35_zero_entry 0 a); cbn [lpow].
  unfold Q_L; follow (even_absorb_list [2;0;4;0]%nat (4+a) 0inf).
  apply progress_evstep; applys_eq (finish_even (17+a)); cbn [mass]; flia.
Qed.

Lemma R35_one6_entry n:
  R35 (1+n*3) 6 -->* 0inf <* (rev Q_L) <* [1]^^42
    <* (rev (Block 2 17 71))^^n <* [0] <* [1]^^22 {{C}}> 0inf.
Proof. follow (R35_one_entry n 6); unfold Q_L, Post, Block; es' n. Qed.

Lemma R35_one14_entry n:
  R35 (1+n*3) 14 -->* 0inf <* (rev Q_L) <* [1]^^40
    <* (rev (Block 4 17 69))^^n <* [0] <* [1]^^48 {{C}}> 0inf.
Proof. follow (R35_one_entry n 14); unfold Q_L, Post, Block; es' n. Qed.

Lemma R35_one6 n: R35 (1+n*3) 6 -->* Q (5+n*12).
Proof.
  follow (R35_one6_entry n).
  follow (tagged_even n 41 0 17 35 11 (0inf <* (rev Q_L))).
  follow (Q_L_C (33+n*72)); applys_eq (P_to_Q (5+n*12)); flia.
Qed.

Lemma R35_one14 n: R35 (1+n*3) 14 -->* Q (7+n*12).
Proof.
  follow (R35_one14_entry n).
  follow (tagged_even n 39 1 17 34 24 (0inf <* (rev Q_L))).
  follow (Q_L_C (45+n*72)); applys_eq (P_to_Q (7+n*12)); flia.
Qed.

Lemma R35_two6 n: R35 (2+n*3) 6 -->* S (207+n*192).
Proof.
  follow (R35_two_entry n 6); follow (C0_even n 7).
  applys_eq (P_one (11+n*12)); flia.
Qed.

Lemma R35_two14 n: R35 (2+n*3) 14 -->* S (229+n*192).
Proof.
  follow (R35_two_entry n 14); follow (C0_even n 15).
  applys_eq (P_five (4+n*4)); flia.
Qed.

Lemma R35_return n a: (a=6 \/ a=14)%nat -> exists b, R35 n a -->* S (1+b*2).
Proof.
  intro Ha; destruct (Nat.eq_dec n 0) as [->|Hn].
  - exists (21+a)%nat; applys_eq (R35_zero a); flia.
  - assert (n mod 3=0 \/ n mod 3=1 \/ n mod 3=2)%nat as Hr by lia.
    destruct Hr as [Hr|[Hr|Hr]].
    + destruct (Z_return (n/3-1) (34+a) ltac:(destruct Ha; lia)) as [b Hb]; exists b.
      follow (R35_three_entry (n/3-1) a).
      follow (C0_Z (n/3-1) (18+a)); applys_eq Hb; flia.
    + destruct Ha as [-> | ->].
      * destruct (Q_return (5+(n/3)*12)) as [b Hb]; exists b.
        follow (R35_one6 (n/3)); apply Hb.
      * destruct (Q_return (7+(n/3)*12)) as [b Hb]; exists b.
        follow (R35_one14 (n/3)); apply Hb.
    + destruct Ha as [-> | ->].
      * exists (103+(n/3)*96)%nat; applys_eq (R35_two6 (n/3)); flia.
      * exists (114+(n/3)*96)%nat; applys_eq (R35_two14 (n/3)); flia.
Qed.
(* The last large family first collapses to seven 11-columns and one
   variable odd tail. Only its alternating terminal needs a new split. *)
Definition N7 a := 0inf <{{A}} Post (repeat 5 7)%nat *> [1]^^(1+a*2) *> 0inf.
Definition N7_L := Post [3;4;0]%nat ++ [1]^^28 ++ [0;1]^^5 ++ [0] ++ [1]^^23.

Lemma N4_prefix l r:
  l <* [0] <{{A}} Post (repeat 5 4)%nat *> r -->*
  l <* [0] <* (rev (Post [3;4;0]%nat)) <* [1]^^28 {{E}}> r.
Proof. unfold Post; es' & l r. Qed.

Lemma N4_E r:
  0inf <{{A}} Post (repeat 5 4)%nat *> r -->*
  0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^28 {{E}}> r.
Proof. applys_eq (N4_prefix 0inf r); solve_const0_eq. Qed.

Lemma N7_E r:
  0inf <{{A}} Post (repeat 5 7)%nat *> r -->*
  0inf <* (rev N7_L) <* [1]^^2 {{E}}> r.
Proof.
  follow (N4_E (Post [5;5;5]%nat *> r)).
  follow (E_triple 5 5 5 (0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^28) r).
  unfold N7_L, Post; simpl_tape; finish.
Qed.

Lemma N7_entry a:
  N7 a -->* 0inf <* (rev N7_L) <* [1]^^2 <* <[0;1]^^(1+a) {{C}}> 0inf.
Proof. unfold N7; follow (N7_E ([1]^^(1+a*2) *> 0inf)); apply E_terminal1. Qed.

Lemma C_alt_five n l:
  l <* [1]^^2 <* <[0;1]^^(5+n*6) {{C}}> 0inf -->*
  l <* [0] <* (rev M9)^^n <* [1]^^22 {{C}}> 0inf.
Proof. unfold M9; es' n & l. Qed.

Lemma C_alt_three n l:
  l <* [1]^^2 <* <[0;1]^^(3+n*6) {{C}}> 0inf -->*
  l <* [0] <* (rev M9)^^n <* [1]^^9 {{C}}> 0inf.
Proof. unfold M9; es' n & l. Qed.

Local Transparent S.
Lemma N7_finish a:
  0inf <* (rev N7_L) <* [0] <* [1]^^(a*2) {{C}}> 0inf -->* S (111+a*2).
Proof. unfold N7_L, Post, S; es' a. Qed.
Local Opaque S.

Lemma N7_even n a:
  0inf <* (rev N7_L) <* [0] <* (rev M9)^^n <* [1]^^(a*2) {{C}}> 0inf -->*
  S (111+a*2+n*16).
Proof.
  change M9 with (Block 9 1 0).
  follow (C_block_power n 8 1 0 (a*2) 4 a
    (0inf <* (rev N7_L) <* [0]) ltac:(lia) ltac:(lia)).
  applys_eq (N7_finish (a+n*8)); flia.
Qed.

Lemma M_three n: M (n*3) -->* S (1621+n*4480).
Proof.
  follow (M_entry (n*3)).
  replace (1125+n*3*1120) with (1+(562+n*1680)*2) by lia.
  follow (N7_entry (562+n*1680)).
  follow (C_alt_five (93+n*280) (0inf <* (rev N7_L))).
  applys_eq (N7_even (93+n*280) 11); flia.
Qed.

Lemma M_one n: M (1+n*3) -->* S (3109+n*4480).
Proof.
  follow (M_entry (1+n*3)).
  replace (1125+(1+n*3)*1120) with (1+(1122+n*1680)*2) by lia.
  follow (N7_entry (1122+n*1680)).
  follow (C_alt_one (187+n*280) (0inf <* (rev N7_L))).
  applys_eq (N7_even (187+n*280) 3); flia.
Qed.
Definition N7_U := Post [3;4;0]%nat ++ [1]^^28 ++ [0;1]^^5 ++ [0].
Definition N7_odd n := 0inf <* (rev N7_L) <* [0] <* (rev M9)^^n <* [1]^^9 {{C}}> 0inf.

Lemma N7_finish_run b a:
  0inf <* (rev N7_U) <* [1]^^(1+b*2) <* [0] <* [1]^^(a*2) {{C}}> 0inf -->*
  S (89+b*2+a*2).
Proof.
  follow (absorb_run a (b*2) (0inf <* (rev N7_U))).
  unfold N7_U; rewrite !rev_app_distr, !rev_power, !Str_app_assoc.
  follow (C_absorb_alt 5 (2+a+b) 27 (0inf <* (rev (Post [3;4;0]%nat)))).
  applys_eq (Csmall (27+a+b)); flia.
Qed.

Lemma N7_odd3_entry n:
  N7_odd (3+n*3) -->* Chain 5 25 n 14
    (0inf <* (rev N7_U) <* [1]^^21 <* [0] <* [1]^^25).
Proof. unfold N7_odd, N7_L, N7_U, Chain, Block, Post, M9; es' n. Qed.

Lemma N7_odd4_entry n:
  N7_odd (4+n*3) -->* Chain 1 33 n 30
    (0inf <* (rev N7_U) <* [1]^^19 <* [0] <* [1]^^33).
Proof. unfold N7_odd, N7_L, N7_U, Chain, Block, Post, M9; es' n. Qed.

Lemma N7_odd5_entry n:
  N7_odd (5+n*3) -->* Chain 5 25 n 48
    (0inf <* (rev N7_U) <* [1]^^21 <* [0] <* [1]^^25).
Proof. unfold N7_odd, N7_L, N7_U, Chain, Block, Post, M9; es' n. Qed.

Lemma N7_odd3 n: N7_odd (3+n*3) -->* S (171+n*48).
Proof.
  follow (N7_odd3_entry n).
  follow (Chain_even 5 12 n 7 24 (0inf <* (rev N7_U) <* [1]^^21 <* [0])).
  applys_eq (N7_finish_run 10 (31+n*24)); flia.
Qed.

Lemma N7_odd4 n: N7_odd (4+n*3) -->* S (177+n*40).
Proof.
  follow (N7_odd4_entry n).
  follow (Chain_even 1 16 n 15 32 (0inf <* (rev N7_U) <* [1]^^19 <* [0])).
  applys_eq (N7_finish_run 9 (35+n*20)); flia.
Qed.

Lemma N7_odd5 n: N7_odd (5+n*3) -->* S (205+n*48).
Proof.
  follow (N7_odd5_entry n).
  follow (Chain_even 5 12 n 24 24 (0inf <* (rev N7_U) <* [1]^^21 <* [0])).
  applys_eq (N7_finish_run 10 (48+n*24)); flia.
Qed.

Lemma M_two_entry n: M (2+n*3) -->* N7_odd (280+n*280).
Proof.
  follow (M_entry (2+n*3)).
  replace (1125+(2+n*3)*1120) with (1+(1682+n*1680)*2) by lia.
  follow (N7_entry (1682+n*1680)).
  applys_eq (C_alt_three (280+n*280) (0inf <* (rev N7_L))); flia.
Qed.

Local Opaque M N7_odd.
Lemma N7_odd_return n: 3<=n -> exists a, N7_odd n -->* S (1+a*2).
Proof.
  intro Hn; assert (n mod 3=0 \/ n mod 3=1 \/ n mod 3=2)%nat as Hr by lia.
  destruct Hr as [Hr|[Hr|Hr]].
  - exists (85+(n/3-1)*24)%nat; applys_eq (N7_odd3 (n/3-1)); flia.
  - exists (88+(n/3-1)*20)%nat; applys_eq (N7_odd4 (n/3-1)); flia.
  - exists (102+(n/3-1)*24)%nat; applys_eq (N7_odd5 (n/3-1)); flia.
Qed.

Lemma M_return n: exists a, M n -->* S (1+a*2).
Proof.
  assert (n mod 3=0 \/ n mod 3=1 \/ n mod 3=2)%nat as Hr by lia.
  destruct Hr as [Hr|[Hr|Hr]].
  - exists (810+(n/3)*2240)%nat; applys_eq (M_three (n/3)); flia.
  - exists (1554+(n/3)*2240)%nat; applys_eq (M_one (n/3)); flia.
  - destruct (N7_odd_return (280+(n/3)*280) ltac:(lia)) as [a Ha]; exists a.
    follow (M_two_entry (n/3)); apply Ha.
Qed.
Local Transparent M N7_odd.
Definition J n a := 0inf <{{A}} [1]^^59 *>
  (Fields [1;1;49]%nat)^^n *> Fields [1;1;a]%nat *> 0inf.
Definition J_L := Post ([4;0]^^4++[3])%nat.

Lemma J_prefix n l r:
  l <* [0] <{{A}} [1]^^59 *> (Fields [1;1;49]%nat)^^n *>
    Fields [1;1]%nat *> [0] *> r -->*
  l <* [0] <* (rev J_L) <* [1]^^12 <* (rev (Block 0 49 9))^^n {{E}}> r.
Proof. unfold Fields, Field, J_L, Post, Block; es' n & l r. Qed.

Lemma J_E n r:
  0inf <{{A}} [1]^^59 *> (Fields [1;1;49]%nat)^^n *>
    Fields [1;1]%nat *> [0] *> r -->*
  0inf <* (rev J_L) <* [1]^^12 <* (rev (Block 0 49 9))^^n {{E}}> r.
Proof. applys_eq (J_prefix n 0inf r); solve_const0_eq. Qed.

Lemma J_entry n a:
  J n a -->* 0inf <* (rev J_L) <* [1]^^12
    <* (rev (Block 0 49 9))^^n <* <[0;1]^^(1+a) {{C}}> 0inf.
Proof.
  unfold J, Fields, Field; cbn [flat_map]; rewrite !app_nil_r, !Str_app_assoc.
  follow (J_E n ([1]^^(1+a*2) *> 0inf)); apply E_terminal1.
Qed.

Lemma J_29_entry n:
  J n 14 -->* 0inf <* (rev J_L) <* [1]^^8
    <* (rev (Block 4 49 5))^^n <* [0] <* [1]^^48 {{C}}> 0inf.
Proof. follow (J_entry n 14); unfold Block; es' n. Qed.

Lemma J_77_entry n:
  J n 38 -->* 0inf <* (rev J_L) <* [1]^^8
    <* (rev (Block 4 49 5))^^n <* [0] <* [1]^^110 {{C}}> 0inf.
Proof. follow (J_entry n 38); unfold Block; es' n. Qed.

Lemma J_93_entry n:
  J n 46 -->* 0inf <* (rev J_L) <* [1]^^10
    <* (rev (Block 2 49 7))^^n <* [0] <* [1]^^134 {{C}}> 0inf.
Proof. follow (J_entry n 46); unfold Block; es' n. Qed.

Local Transparent S.
Lemma J_finish a:
  0inf <* (rev J_L) <* [1]^^(1+a*2) {{C}}> 0inf -->* S (85+a*2).
Proof. unfold J_L, Post, S; es' a. Qed.
Local Opaque S.

Lemma J_29 n: J n 14 -->* S (143+n*208).
Proof.
  follow (J_29_entry n).
  follow (tagged_even n 7 1 49 2 24 (0inf <* (rev J_L))).
  applys_eq (J_finish (29+n*104)); flia.
Qed.

Lemma J_77 n: J n 38 -->* S (205+n*208).
Proof.
  follow (J_77_entry n).
  follow (tagged_even n 7 1 49 2 55 (0inf <* (rev J_L))).
  applys_eq (J_finish (60+n*104)); flia.
Qed.

Lemma J_93 n: J n 46 -->* S (231+n*208).
Proof.
  follow (J_93_entry n).
  follow (tagged_even n 9 0 49 3 67 (0inf <* (rev J_L))).
  applys_eq (J_finish (73+n*104)); flia.
Qed.
Lemma C_odd_two b a:
  0inf <* [1]^^(3+b*2) <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  S (17+b*2+a*2).
Proof.
  follow (absorb_odd_run a (b*2) 0inf).
  apply progress_evstep; applys_eq (finish_even (4+a+b)); flia.
Qed.

Lemma N4_train n:
  0inf <{{A}} Post (repeat 5 4)%nat *> [1]^^(23+n*36) *> 0inf -->*
  Chain 5 25 n 14 (0inf <* [1]^^7 <* [0] <* [1]^^44).
Proof.
  follow (N4_E ([1]^^(23+n*36) *> 0inf)).
  follow (E_terminal1 (11+n*18) (0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^28)).
  unfold Chain, Block, Post; es' n.
Qed.

Lemma N4_return n:
  0inf <{{A}} Post (repeat 5 4)%nat *> [1]^^(23+n*36) *> 0inf -->* S (101+n*48).
Proof.
  follow (N4_train n).
  follow (Chain_even 5 12 n 7 43 (0inf <* [1]^^7 <* [0])).
  applys_eq (C_odd_two 2 (40+n*24)); flia.
Qed.

Definition CPeriod n p e q w t a := 0inf <* (rev (Post p)) <* [1]^^e <* [0]
  <* (rev (Post q)) <* (rev (Post w))^^n <* (rev (Post t)) <* [1]^^(a*2) {{C}}> 0inf.

Lemma CPeriod_collapse n p e q w t a:
  CPeriod n p (2+e*2) q w t a -->*
  0inf <* (rev (Post p)) <* [1]^^(5+e*2+(a+mass t+n*mass w+mass q)*2) {{C}}> 0inf.
Proof.
  unfold CPeriod; follow (even_absorb_list t a
    (0inf <* (rev (Post p)) <* [1]^^(2+e*2) <* [0]
      <* (rev (Post q)) <* (rev (Post w))^^n)).
  follow (even_absorb_power n w (a+mass t)
    (0inf <* (rev (Post p)) <* [1]^^(2+e*2) <* [0] <* (rev (Post q)))).
  follow (even_absorb_list q (a+mass t+n*mass w)
    (0inf <* (rev (Post p)) <* [1]^^(2+e*2) <* [0])).
  applys_eq (absorb_run (a+mass t+n*mass w+mass q) (1+e*2) (0inf <* (rev (Post p)))); flia.
Qed.

Definition J99_w0 : list nat :=
  ([0;4]^^8 ++ repeat 0 5 ++ [4;0]^^8 ++ [8] ++ [0;4]^^7 ++ [0;8])%nat.
Definition J99_w1 : list nat :=
  (repeat 0 4 ++ [4;0]^^8 ++ ([8]++[0;4]^^7++[0])^^2 ++ [4;0])%nat.
Definition J99_q := (repeat 0 49 ++ [4;0;4;0;12] ++ repeat 0 22)%nat.
Definition J99_w2 := (repeat 0 7 ++ [108;0;4;0;4] ++ repeat 0 5 ++ [36] ++
  repeat 0 57 ++ [52;0;4;0;8] ++ repeat 0 5 ++ [88] ++ J99_q)%nat.
Definition J99_t2 := (repeat 0 7 ++ [108;0;4;0;4] ++ repeat 0 5 ++ [35] ++ [4;0]^^9)%nat.

Lemma J99_zero_entry n:
  J (n*3) 49 -->* CPeriod n ([4;0]^^4)%nat 22 [] J99_w0 ([0;4]^^7++[0;2])%nat 7.
Proof.
  follow (J_entry (n*3) 49).
  unfold CPeriod, J99_w0, J_L, Post, Block; es' n.
Qed.

Lemma J99_one_entry n:
  J (1+n*3) 49 -->* CPeriod n ([4;0]^^4)%nat 22 ([0;4]^^8++[0])%nat
    J99_w1 (repeat 0 4++[4;0]^^8)%nat 3.
Proof.
  follow (J_entry (1+n*3) 49).
  unfold CPeriod, J99_w1, J_L, Post, Block; es' n.
Qed.

Lemma J99_two_entry n:
  J (2+n*9) 49 -->* CPeriod n [4%nat] 74 J99_q J99_w2 (repeat 0 7)%nat 55.
Proof.
  follow (J_entry (2+n*9) 49).
  unfold CPeriod, J99_q, J99_w2, J_L, Post, Block; es' n.
Qed.

Lemma J99_five_entry n:
  J (5+n*9) 49 -->* CPeriod n [4%nat] 74 J99_q J99_w2 J99_t2 3.
Proof.
  follow (J_entry (5+n*9) 49).
  unfold CPeriod, J99_t2, J99_w2, J99_q, J_L, Post, Block; es' n.
Qed.


Lemma A_return_power n xs l r:
  l <* (rev (Pairs xs))^^n <{{A}} r -->*
  l <{{A}} (Post (map (fun x => 1+x) xs))^^n *> r.
Proof.
  revert l r; induction n; intros l r; [cbn; finish|].
  cbn [lpow]; rewrite !Str_app_assoc.
  follow (A_return_list xs (l <* (rev (Pairs xs))^^n) r).
  follow (IHn l (Post (map (fun x => 1+x) xs) *> r)).
  apply evstep_refl'; rewrite <- !Str_app_assoc, lpow_shift; reflexivity.
Qed.

Lemma C_recover_period n p w x xs a:
  0inf <* (rev (Pairs p)) <* (rev (Pairs w))^^n
    <* (rev (Pairs (x::xs))) <* [0] <* [1]^^(1+a*2) {{C}}> 0inf -->*
  0inf <{{A}} Post (map (fun z => 1+z) p) *>
    (Post (map (fun z => 1+z) w))^^n *>
    Post (map (fun z => 1+z) (x::xs)) *> [1]^^(5+a*2) *> 0inf.
Proof.
  follow (C_recover_list x xs a (0inf <* (rev (Pairs p)) <* (rev (Pairs w))^^n)).
  follow (A_return_power n w (0inf <* (rev (Pairs p)))
    (Post (map (fun z => 1+z) (x::xs)) *> [1]^^(5+a*2) *> 0inf)).
  apply A_return_list.
Qed.

Definition JM_A := [0;0;12;0;0;12;0;0;8]%nat.
Definition JM_B := (repeat 0 56 ++ [4] ++ repeat 0 4 ++ [48] ++ JM_A ++ repeat 4 8)%nat.
Definition JM_P := ([44] ++ JM_A ++ [28;0;0;12])%nat.
Definition JM_W := (JM_B ++ [112] ++ JM_A ++ [28;0;0;12])%nat.

Lemma J99_M_prefix n l:
  l <* [0;0] <* (rev J_L) <* [1]^^12
    <* (rev (Block 0 49 9))^^(8+n*9) <* <[0;1]^^50 {{C}}> 0inf -->*
  l <{{A}} Post (map (fun x => 1+x) JM_P) *>
    (Post (map (fun x => 1+x) JM_W))^^n *>
    Post (map (fun x => 1+x) JM_B) *> [1]^^221 *> 0inf.
Proof. unfold JM_P, JM_W, JM_B, JM_A, J_L, Post, Block; es' n & l. Qed.

Lemma JM_P_word r:
  Post (map (fun x => 1+x) JM_P) *> r =
  [1]^^91 *> [0] *> [1]^^3 *> TripleWord M_head *> [0] *> r.
Proof. reflexivity. Qed.
Lemma JM_W_word: Fields (map (fun x => 1+x) JM_W) = TripleWord M_period.
Proof. reflexivity. Qed.
Lemma JM_B_word r:
  [0] *> Post (map (fun x => 1+x) JM_B) *> [1]^^221 *> r =
  TripleWord M_tail *> Field 5 *> Field 110 *> r.
Proof. reflexivity. Qed.
Lemma J99_to_M n: J (8+n*9) 49 -->* M n.
Proof.
  follow (J_entry (8+n*9) 49).
  eapply evstep_trans; [applys_eq (J99_M_prefix n 0inf); solve_const0_eq|].
  rewrite JM_P_word, Post_Fields_power, JM_W_word, JM_B_word.
  unfold M; rewrite !TripleWord_app, TripleWord_power, !Str_app_assoc; finish.
Qed.

Lemma J99_four_end a:
  0inf <* (rev (Post ([4;0]^^4)%nat)) <* [1]^^(1+a*2) {{C}}> 0inf -->*
  0inf <{{A}} Post (repeat 5 4)%nat *> [1]^^(5+a*2) *> 0inf.
Proof. applys_eq (M9_recover 4 a); simpl_tape; reflexivity. Qed.

Lemma J99_zero n: J (n*3) 49 -->* S (293+n*576).
Proof.
  follow (J99_zero_entry n).
  follow (CPeriod_collapse n ([4;0]^^4)%nat 10 [] J99_w0 ([0;4]^^7++[0;2])%nat 7).
  change (mass J99_w0) with 216; change (mass ([0;4]^^7++[0;2])%nat) with 62; cbn [mass].
  follow (J99_four_end (81+n*216)); applys_eq (N4_return (4+n*12)); flia.
Qed.

Lemma J99_one n: J (1+n*3) 49 -->* S (485+n*576).
Proof.
  follow (J99_one_entry n).
  follow (CPeriod_collapse n ([4;0]^^4)%nat 10 ([0;4]^^8++[0])%nat
    J99_w1 (repeat 0 4++[4;0]^^8)%nat 3).
  change (mass J99_w1) with 216; change (mass (repeat 0 4++[4;0]^^8)%nat) with 72.
  change (mass ([0;4]^^8++[0])%nat) with 66.
  follow (J99_four_end (153+n*216)); applys_eq (N4_return (8+n*12)); flia.
Qed.

Lemma J99_two n: J (2+n*9) 49 -->* S (581+n*1296).
Proof.
  follow (J99_two_entry n).
  follow (CPeriod_collapse n [4%nat] 36 J99_q J99_w2 (repeat 0 7)%nat 55).
  change (mass J99_q) with 172; change (mass J99_w2) with 648.
  change (mass (repeat 0 7)%nat) with 14.
  change (rev (Post [4]%nat)) with ([0]++[1]^^9).
  rewrite Str_app_assoc.
  applys_eq (C_odd_two 3 (279+n*648)); flia.
Qed.

Lemma J99_five n: J (5+n*9) 49 -->* S (967+n*1296).
Proof.
  follow (J99_five_entry n).
  follow (CPeriod_collapse n [4%nat] 36 J99_q J99_w2 J99_t2 3).
  change (mass J99_q) with 172; change (mass J99_w2) with 648.
  change (mass J99_t2) with 259.
  change (rev (Post [4]%nat)) with ([0]++[1]^^9).
  rewrite Str_app_assoc.
  applys_eq (C_odd_two 3 (472+n*648)); flia.
Qed.

Local Opaque J.
Lemma J_return n a:
  (a=14 \/ a=38 \/ a=46 \/ a=49)%nat -> exists b, J n a -->* S (1+b*2).
Proof.
  intros [-> | [-> | [-> | ->]]].
  - exists (71+n*104)%nat; applys_eq (J_29 n); flia.
  - exists (102+n*104)%nat; applys_eq (J_77 n); flia.
  - exists (115+n*104)%nat; applys_eq (J_93 n); flia.
  - assert (n mod 3=0 \/ n mod 3=1 \/ n mod 3=2)%nat as Hr by lia.
    destruct Hr as [Hr|[Hr|Hr]].
    + exists (146+(n/3)*288)%nat; applys_eq (J99_zero (n/3)); flia.
    + exists (242+(n/3)*288)%nat; applys_eq (J99_one (n/3)); flia.
    + assert (n mod 9=2 \/ n mod 9=5 \/ n mod 9=8)%nat as Hq by lia.
      destruct Hq as [Hq|[Hq|Hq]].
      * exists (290+(n/9)*648)%nat; applys_eq (J99_two (n/9)); flia.
      * exists (483+(n/9)*648)%nat; applys_eq (J99_five (n/9)); flia.
      * destruct (M_return (n/9)) as [b Hb]; exists b.
        follow (J99_to_M (n/9)); apply Hb.
Qed.
Local Transparent J.


Local Transparent S.
Lemma S_three_prefix n l r:
  l {{A}}> [0] *> [1]^^(3+n*12) *> [0] *> r -->*
  l <* [0] <* (rev M9)^^n <* [1]^^4 {{C}}> r.
Proof. unfold M9; es' n & l r. Qed.
Lemma S_three_entry n:
  S (3+n*12) -->* 0inf <* (rev M9)^^n <* [1]^^4 {{C}}> 0inf.
Proof. unfold S; applys_eq (S_three_prefix n 0inf 0inf); solve_const0_eq. Qed.
Lemma S_three n: S (3+n*12) -->+ S (11+n*16).
Proof.
  follow (S_three_entry n).
  change M9 with (Post [4;0]%nat).
  follow (even_absorb_power n [4;0]%nat 2 0inf).
  applys_eq (finish_even (1+n*8)); cbn [mass]; flia.
Qed.
Lemma S_nine_prefix n l r:
  l <* [0] {{A}}> [0] *> [1]^^(9+n*12) *> [0] *> r -->*
  l <* [1]^^5 <* <[0;1;0] <* (rev M9)^^n <* [1]^^4 {{C}}> r.
Proof. unfold M9; es' n & l r. Qed.
Lemma S_nine_entry n:
  S (9+n*12) -->* 0inf <* [1]^^5 <* <[0;1;0] <* (rev M9)^^n <* [1]^^4 {{C}}> 0inf.
Proof. unfold S; applys_eq (S_nine_prefix n 0inf 0inf); solve_const0_eq. Qed.
Lemma S_nine n: S (9+n*12) -->+ S (23+n*16).
Proof.
  follow (S_nine_entry n).
  change M9 with (Post [4;0]%nat).
  follow (even_absorb_power n [4;0]%nat 2 (0inf <* [1]^^5 <* <[0;1;0])).
  change (mass [4;0]%nat) with 8.
  follow (C_absorb_alt 1 (2+n*8) 4 0inf).
  applys_eq (finish_even (7+n*8)); flia.
Qed.
Lemma S_one_prefix n l r:
  l <* [0]^^4 <{{A}} [1]^^(37+n*36) *> [0]^^3 *> r -->*
  l <* [0] <* [1]^^20 <* (rev (Block 0 5 25))^^n
    <* <[0;1]^^5 <* [0] <* [1]^^12 {{C}}> r.
Proof. unfold Block; es' n & l r. Qed.
Lemma S_one_entry n:
  S (37+n*36) -->* Chain 5 25 n 12 (0inf <* [1]^^20).
Proof. unfold S, Chain; applys_eq (S_one_prefix n 0inf 0inf); solve_const0_eq. Qed.
Lemma S_one n: S (37+n*36) -->+ S (59+n*48).
Proof.
  follow (S_one_entry n); follow (Chain_even 5 12 n 6 19 0inf).
  applys_eq (finish_odd (27+n*24)); flia.
Qed.
Lemma S_U_prefix n l:
  l <* [0]^^5 <{{A}} [1]^^(13+n*36) *> 0inf -->+ l <{{A}} [1]^^25 *> ([0]++[1]^^35)^^n *> 0inf.
Proof. es' n & l. Qed.
Lemma S_U n: S (13+n*36) -->+ U n.
Proof. unfold S, U; applys_eq (S_U_prefix n 0inf); solve_const0_eq. Qed.
Lemma S_R6_prefix n l:
  l <* [0]^^5 <{{A}} [1]^^(25+n*36) *> 0inf -->+ l <{{A}} [1]^^25 *> ([0]++[1]^^35)^^n *> [0] *> [1]^^13 *> 0inf.
Proof. es' n & l. Qed.
Lemma S_R6 n: S (25+n*36) -->+ R35 n 6.
Proof. unfold S, R35; applys_eq (S_R6_prefix n 0inf); solve_const0_eq. Qed.
Lemma S_R14_prefix n l:
  l <* [0]^^5 <{{A}} [1]^^(41+n*36) *> 0inf -->+ l <{{A}} [1]^^25 *> ([0]++[1]^^35)^^n *> [0] *> [1]^^29 *> 0inf.
Proof. es' n & l. Qed.
Lemma S_R14 n: S (41+n*36) -->+ R35 n 14.
Proof. unfold S, R35; applys_eq (S_R14_prefix n 0inf); solve_const0_eq. Qed.

Lemma S_seventeen_prefix n l r:
  l <* [0]^^4 <{{A}} [1]^^(17+n*36) *> [0]^^6 *> r -->*
  l <* [0] <* [1]^^20 <* (rev (Block 0 5 25))^^n <* <[0;1]^^3 {{C}}> r.
Proof. unfold Block; es' n & l r. Qed.
Lemma S_seventeen_entry n:
  S (17+n*36) -->* 0inf <* [1]^^18 <* (rev (Block 2 5 23))^^n
    <* [0] <* [1]^^9 {{C}}> 0inf.
Proof.
  unfold S; eapply evstep_trans; [applys_eq (S_seventeen_prefix n 0inf 0inf); solve_const0_eq|].
  unfold Block; es' n.
Qed.
Lemma S_seventeen n: S (17+n*36) -->+ S (37+n*48).
Proof.
  follow (S_seventeen_entry n); follow (tagged_odd n 15 0 5 10 4 0inf).
  applys_eq (finish_odd (16+n*24)); flia.
Qed.
Lemma S_twentynine_prefix n l r:
  l <* [0]^^4 <{{A}} [1]^^(29+n*36) *> [0]^^5 *> r -->*
  l <* [0] <* [1]^^20 <* (rev (Block 0 5 25))^^n
    <* <[0;1]^^5 <* [0] <* [1]^^6 {{C}}> r.
Proof. unfold Block; es' n & l r. Qed.
Lemma S_twentynine_entry n:
  S (29+n*36) -->* Chain 5 25 n 6 (0inf <* [1]^^20).
Proof. unfold S, Chain; applys_eq (S_twentynine_prefix n 0inf 0inf); solve_const0_eq. Qed.
Lemma S_twentynine n: S (29+n*36) -->+ S (53+n*48).
Proof.
  follow (S_twentynine_entry n); follow (Chain_even 5 12 n 3 19 0inf).
  applys_eq (finish_odd (24+n*24)); flia.
Qed.
Local Opaque S.

Definition Train n a := Chain 17 73 n a (0inf <* (rev (Post [3]%nat)) <* [1]^^44).

Definition Train1 n a := 0inf <* [1]^^54
  <* (rev (Fields [0;4;0;4;0;40]%nat))^^n
  <* (rev (Fields [0;4;0;4;0]%nat)) <* [0] <* [1]^^(9+a*2) {{C}}> 0inf.
Definition Train2 n a := Chain 5 97 n (25+a*2) (0inf <* [1]^^57).
Lemma Train_E n a:
  Train n (1+a*2) -->* 0inf <* [1]^^54 {{E}}>
    (Post (repeat 1 8++[37])%nat)^^n *> Post (repeat 1 8)%nat *> [1]^^(5+a*2) *> 0inf.
Proof. unfold Train, Chain, Post, Block; es' n a. Qed.
Lemma Train_1 n a: Train n (1+a*2) -->* Train1 n a.
Proof.
  follow (Train_E n a).
  follow (E_C1_D n (0inf <* [1]^^54) ([1]^^(5+a*2) *> 0inf)).
  unfold Train1; apply (D_tail 4 (2+a)).
Qed.
Lemma Train1_E n a:
  Train1 n a -->* 0inf <* [1]^^57 {{E}}>
    (Post [5;5;41]%nat)^^n *> Post [5;5]%nat *> [1]^^(13+a*2) *> 0inf.
Proof. unfold Train1, Post, Fields, Field; es' n a. Qed.
Lemma Train_2 n a: Train1 n a -->* Train2 n a.
Proof.
  follow (Train1_E n a).
  follow (E_C2_D n (0inf <* [1]^^57) ([1]^^(13+a*2) *> 0inf)).
  unfold Train2, Chain; apply (D_tail 12 (6+a)).
Qed.
Lemma Train2_J n a: Train2 n a -->* J n (14+a).
Proof.
  applys_eq (C_recover_period n [28]%nat [0;0;48]%nat 0 [0]%nat (12+a));
    unfold Train2, Chain, Block, J, Fields, Field, Pairs, Post;
    cbn [map]; simpl_tape; simpl_rotate; try flia; try solve_const0_eq.
Qed.
Lemma Train_odd n a: Train n (1+a*2) -->* J n (14+a).
Proof. follow (Train_1 n a); follow (Train_2 n a); apply Train2_J. Qed.

Lemma Train_even n a: Train n (a*2) -->* S (135+a*2+n*144).
Proof.
  unfold Train; follow (Chain_even 17 36 n a 43 (0inf <* (rev (Post [3]%nat)))).
  change (rev (Post [3]%nat)) with ([0]++[1]^^7).
  rewrite Str_app_assoc.
  applys_eq (C_odd_two 2 (57+a+n*72)); flia.
Qed.

Lemma Train_alt7_entry n:
  0inf <* (rev (Post [3]%nat)) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^7 {{C}}> 0inf -->*
  0inf <* (rev (Post [3]%nat)) <* [1]^^42
    <* (rev (Block 2 17 71))^^n <* [0] <* [1]^^22 {{C}}> 0inf.
Proof. unfold Post, Block; es' n. Qed.
Lemma Train_alt7 n:
  0inf <* (rev (Post [3]%nat)) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^7 {{C}}> 0inf -->* S (87+n*144).
Proof.
  follow (Train_alt7_entry n).
  follow (tagged_even n 41 0 17 35 11 (0inf <* (rev (Post [3]%nat)))).
  change (rev (Post [3]%nat)) with ([0]++[1]^^7).
  rewrite Str_app_assoc.
  applys_eq (C_odd_two 2 (33+n*72)); flia.
Qed.
Lemma Train_alt15_entry n:
  0inf <* (rev (Post [3]%nat)) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^15 {{C}}> 0inf -->*
  0inf <* (rev (Post [3]%nat)) <* [1]^^40
    <* (rev (Block 4 17 69))^^n <* [0] <* [1]^^48 {{C}}> 0inf.
Proof. unfold Post, Block; es' n. Qed.
Lemma Train_alt15 n:
  0inf <* (rev (Post [3]%nat)) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^15 {{C}}> 0inf -->* S (111+n*144).
Proof.
  follow (Train_alt15_entry n).
  follow (tagged_even n 39 1 17 34 24 (0inf <* (rev (Post [3]%nat)))).
  change (rev (Post [3]%nat)) with ([0]++[1]^^7).
  rewrite Str_app_assoc.
  applys_eq (C_odd_two 2 (45+n*72)); flia.
Qed.

Definition SmallTrain n a := Chain 5 25 n a (0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^28).
Lemma SmallTrain_even n a: SmallTrain n (a*2) -->* S (85+a*2+n*48).
Proof.
  unfold SmallTrain; follow (Chain_even 5 12 n a 27 (0inf <* (rev (Post [3;4;0]%nat)))).
  applys_eq (Csmall (25+a+n*24)); flia.
Qed.
Lemma SmallTrain_alt3_entry n:
  0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^28
    <* (rev (Block 0 5 25))^^n <* <[0;1]^^3 {{C}}> 0inf -->*
  0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^26
    <* (rev (Block 2 5 23))^^n <* [0] <* [1]^^9 {{C}}> 0inf.
Proof. unfold Post, Block; es' n. Qed.
Lemma SmallTrain_alt3 n:
  0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^28
    <* (rev (Block 0 5 25))^^n <* <[0;1]^^3 {{C}}> 0inf -->* S (75+n*48).
Proof.
  follow (SmallTrain_alt3_entry n).
  follow (tagged_odd n 23 0 5 10 4 (0inf <* (rev (Post [3;4;0]%nat)))).
  applys_eq (Csmall (20+n*24)); flia.
Qed.

(* The finite outer entrance table is checked with unread contexts on both
   sides. In particular its C endpoint is not skipped by a subsequent scan. *)
Inductive TrainSource : nat -> nat -> nat -> Prop :=
| TS79 : TrainSource 79 1 8
| TS91 : TrainSource 91 14 9
| TS107 : TrainSource 107 30 9
| TS115 : TrainSource 115 36 7.

Lemma S_train_prefix n s a z l r: TrainSource s a z ->
  l <* [0]^^2 <{{A}} [1]^^(s+n*108) *> [0]^^z *> r -->+
  l <* [0] <* (rev (Post [3]%nat)) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^17 <* [0] <* [1]^^a {{C}}> r.
Proof.
  intro H; destruct H; unfold Post, Block; es' n & l r.
Qed.
Local Transparent S.
Lemma S_train_entry n s a z: TrainSource s a z ->
  S (s+n*108) -->+ Train n a.
Proof.
  intro H; generalize (S_train_prefix n s a z 0inf 0inf H).
  destruct H; intro Hp; unfold S, Train, Chain; applys_eq Hp; solve_const0_eq.
Qed.
Local Opaque S.

Lemma Train_return n a:
  (a=1 \/ a=14 \/ a=30 \/ a=36 \/ a=49 \/ a=65 \/ a=71)%nat ->
  exists b, Train n a -->* S (1+b*2).
Proof.
  intro Ha; destruct (Nat.eq_dec (a mod 2) 0) as [He|He].
  - exists (67+a/2+n*72)%nat; applys_eq (Train_even n (a/2)); flia.
  - destruct (J_return n (14+a/2) ltac:(lia)) as [b Hb]; exists b.
    follow (Train_odd n (a/2)); apply Hb.
Qed.
Lemma S_train_return n s a z: TrainSource s a z ->
  exists b, S (s+n*108) -->+ S (1+b*2).
Proof.
  intro H; destruct (Train_return n a ltac:(destruct H; lia)) as [b Hb].
  exists b; eapply progress_evstep_trans; [apply (S_train_entry n s a z H)|apply Hb].
Qed.


Inductive JSource : nat -> nat -> Prop :=
| JS127 : JSource 127 38
| JS143 : JSource 143 46
| JS151 : JSource 151 49.
Lemma S_J_prefix n s a l: JSource s a ->
  l <* [0]^^3 <{{A}} [1]^^(s+n*108) *> 0inf -->+
  l <{{A}} [1]^^59 *> (Fields [1;1;49]%nat)^^n *> Fields [1;1;a]%nat *> 0inf.
Proof. intro H; destruct H; unfold Fields, Field; es' n & l. Qed.
Local Transparent S.
Lemma S_J_entry n s a: JSource s a -> S (s+n*108) -->+ J n a.
Proof. intro H; unfold S, J; applys_eq (S_J_prefix n s a 0inf H); solve_const0_eq. Qed.
Local Opaque S.
Lemma S_J_return n s a: JSource s a ->
  exists b, S (s+n*108) -->+ S (1+b*2).
Proof.
  intro H; destruct (J_return n a ltac:(destruct H; tauto)) as [b Hb]; exists b.
  eapply progress_evstep_trans; [apply (S_J_entry n s a H)|apply Hb].
Qed.

Inductive AltSource : nat -> nat -> Prop :=
| AS55 : AltSource 55 7
| AS71 : AltSource 71 15.
Lemma S_alt_prefix n s a l r: AltSource s a ->
  l <* [0]^^2 <{{A}} [1]^^(s+n*108) *> [0]^^10 *> r -->+
  l <* [0] <* (rev (Post [3]%nat)) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^a {{C}}> r.
Proof. intro H; destruct H; unfold Post, Block; es' n & l r. Qed.
Local Transparent S.
Lemma S_alt_entry n s a: AltSource s a ->
  S (s+n*108) -->+ 0inf <* (rev (Post [3]%nat)) <* [1]^^44
    <* (rev (Block 0 17 73))^^n <* <[0;1]^^a {{C}}> 0inf.
Proof. intro H; unfold S; applys_eq (S_alt_prefix n s a 0inf 0inf H); solve_const0_eq. Qed.
Local Opaque S.
Lemma S_alt_return n s a: AltSource s a ->
  exists b, S (s+n*108) -->+ S (1+b*2).
Proof.
  intro H; destruct H.
  - exists (43+n*72)%nat; eapply progress_evstep_trans;
      [apply S_alt_entry; constructor|applys_eq (Train_alt7 n); flia].
  - exists (55+n*72)%nat; eapply progress_evstep_trans;
      [apply S_alt_entry; constructor|applys_eq (Train_alt15 n); flia].
Qed.

Inductive SmallSource : nat -> nat -> nat -> Prop :=
| SS59 : SmallSource 59 6 5
| SS67 : SmallSource 67 12 3.
Lemma S_small_prefix n s a z l r: SmallSource s a z ->
  l <* [0]^^2 <{{A}} [1]^^(s+n*36) *> [0]^^z *> r -->+
  l <* [0] <* (rev (Post [3;4;0]%nat)) <* [1]^^28
    <* (rev (Block 0 5 25))^^n <* <[0;1]^^5 <* [0] <* [1]^^a {{C}}> r.
Proof. intro H; destruct H; unfold Post, Block; es' n & l r. Qed.
Local Transparent S.
Lemma S_small_entry n s a z: SmallSource s a z ->
  S (s+n*36) -->+ SmallTrain n a.
Proof.
  intro H; generalize (S_small_prefix n s a z 0inf 0inf H).
  destruct H; intro Hp; unfold S, SmallTrain, Chain; applys_eq Hp; solve_const0_eq.
Qed.
Local Opaque S.
Lemma S_small_return n s a z: SmallSource s a z ->
  exists b, S (s+n*36) -->+ S (1+b*2).
Proof.
  intro H; exists (42+a/2+n*24)%nat.
  eapply progress_evstep_trans; [apply (S_small_entry n s a z H)|].
  applys_eq (SmallTrain_even n (a/2)); destruct H; flia.
Qed.

Lemma S47_prefix n l r:
  l <* [0]^^2 <{{A}} [1]^^(47+n*36) *> [0]^^6 *> r -->+
  l <* [0] <* (rev (Post [3;4;0]%nat)) <* [1]^^28
    <* (rev (Block 0 5 25))^^n <* <[0;1]^^3 {{C}}> r.
Proof. unfold Post, Block; es' n & l r. Qed.
Local Transparent S.
Lemma S47_entry n:
  S (47+n*36) -->+ 0inf <* (rev (Post [3;4;0]%nat)) <* [1]^^28
    <* (rev (Block 0 5 25))^^n <* <[0;1]^^3 {{C}}> 0inf.
Proof. unfold S; applys_eq (S47_prefix n 0inf 0inf); solve_const0_eq. Qed.
Local Opaque S.
Lemma S47_return n: S (47+n*36) -->+ S (75+n*48).
Proof. eapply progress_evstep_trans; [apply S47_entry|apply SmallTrain_alt3]. Qed.

Local Transparent S.
Lemma S_base s: In s [1;5;7;11;19;23;31;35;43]%nat ->
  exists b, S s -->+ S (1+b*2).
Proof.
  intro H; cbn in H.
  destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|H]]]]]]]]].
  - exists 3%nat; unfold S; es'.
  - exists 9%nat; unfold S; es'.
  - exists 5%nat; unfold S; es'.
  - exists 13%nat; unfold S; es'.
  - exists 18%nat; unfold S; es'.
  - exists 21%nat; unfold S; es'.
  - exists 24%nat; unfold S; es'.
  - exists 26%nat; unfold S; es'.
  - exists 29%nat; unfold S; es'.
  - contradiction.
Qed.
Local Opaque S.

Ltac return_via H :=
  let b:=fresh "b" in let Hb:=fresh "Hb" in
  destruct H as [b Hb]; exists b; applys_eq Hb; flia.

Lemma S_E0 n: exists b, S (7+n*12) -->+ S (1+b*2).
Proof.
  destruct (Nat.eq_dec (n mod 3) 2) as [Hr|Hr].
  - destruct (Nat.eq_dec n 2) as [->|Hn].
    + return_via (S_base 31 ltac:(cbn; tauto)).
    + return_via (S_small_return (n/3-1) 67 12 3 SS67).
  - assert (n mod 9=0 \/ n mod 9=1 \/ n mod 9=3 \/
            n mod 9=4 \/ n mod 9=6 \/ n mod 9=7)%nat as Hq by lia.
    destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]].
    + destruct (Nat.eq_dec n 0) as [->|Hn].
      * return_via (S_base 7 ltac:(cbn; tauto)).
      * return_via (S_train_return (n/9-1) 115 36 7 TS115).
    + destruct (Nat.eq_dec n 1) as [->|Hn].
      * return_via (S_base 19 ltac:(cbn; tauto)).
      * return_via (S_J_return (n/9-1) 127 38 JS127).
    + destruct (Nat.eq_dec n 3) as [->|Hn].
      * return_via (S_base 43 ltac:(cbn; tauto)).
      * return_via (S_J_return (n/9-1) 151 49 JS151).
    + return_via (S_alt_return (n/9) 55 7 AS55).
    + return_via (S_train_return (n/9) 79 1 8 TS79).
    + return_via (S_train_return (n/9) 91 14 9 TS91).
Qed.
Lemma S_E5 n: exists b, S (11+n*12) -->+ S (1+b*2).
Proof.
  assert (n mod 3=0 \/ n mod 3=1 \/ n mod 3=2)%nat as Hr by lia.
  destruct Hr as [Hr|[Hr|Hr]].
  - destruct (Nat.eq_dec n 0) as [->|Hn].
    + return_via (S_base 11 ltac:(cbn; tauto)).
    + exists (37+(n/3-1)*24)%nat; applys_eq (S47_return (n/3-1)); flia.
  - destruct (Nat.eq_dec n 1) as [->|Hn].
    + return_via (S_base 23 ltac:(cbn; tauto)).
    + return_via (S_small_return (n/3-1) 59 6 5 SS59).
  - assert (n mod 9=2 \/ n mod 9=5 \/ n mod 9=8)%nat as Hq by lia.
    destruct Hq as [Hq|[Hq|Hq]].
    + destruct (Nat.eq_dec n 2) as [->|Hn].
      * return_via (S_base 35 ltac:(cbn; tauto)).
      * return_via (S_J_return (n/9-1) 143 46 JS143).
    + return_via (S_alt_return (n/9) 71 15 AS71).
    + return_via (S_train_return (n/9) 107 30 9 TS107).
Qed.

Lemma S_return a: exists b, S (1+a*2) -->+ S (1+b*2).
Proof.
  assert (a mod 6=0 \/ a mod 6=1 \/ a mod 6=2 \/
          a mod 6=3 \/ a mod 6=4 \/ a mod 6=5)%nat as Hr by lia.
  destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]].
  - assert (a mod 18=0 \/ a mod 18=6 \/ a mod 18=12)%nat as Hq by lia.
    destruct Hq as [Hq|[Hq|Hq]].
    + destruct (Nat.eq_dec a 0) as [->|Ha].
      * return_via (S_base 1 ltac:(cbn; tauto)).
      * exists (29+(a/18-1)*24)%nat; applys_eq (S_one (a/18-1)); flia.
    + destruct (U_return (a/18)) as [b Hb]; exists b.
      eapply progress_evstep_trans; [applys_eq (S_U (a/18)); flia|apply Hb].
    + destruct (R35_return (a/18) 6 ltac:(tauto)) as [b Hb]; exists b.
      eapply progress_evstep_trans; [applys_eq (S_R6 (a/18)); flia|apply Hb].
  - exists (5+(a/6)*8)%nat; applys_eq (S_three (a/6)); flia.
  - assert (a mod 18=2 \/ a mod 18=8 \/ a mod 18=14)%nat as Hq by lia.
    destruct Hq as [Hq|[Hq|Hq]].
    + destruct (Nat.eq_dec a 2) as [->|Ha].
      * return_via (S_base 5 ltac:(cbn; tauto)).
      * destruct (R35_return (a/18-1) 14 ltac:(tauto)) as [b Hb]; exists b.
        eapply progress_evstep_trans; [applys_eq (S_R14 (a/18-1)); flia|apply Hb].
    + exists (18+(a/18)*24)%nat; applys_eq (S_seventeen (a/18)); flia.
    + exists (26+(a/18)*24)%nat; applys_eq (S_twentynine (a/18)); flia.
  - return_via (S_E0 (a/6)).
  - exists (11+(a/6)*8)%nat; applys_eq (S_nine (a/6)); flia.
  - return_via (S_E5 (a/6)).
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  apply (progress_nonhalt_simple tm nat (fun a => S (1+a*2)) 4).
  apply S_return.
Qed.

End TM3.
