(* 1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_---0RD does not halt from the blank tape: TM1.M030top.nonhalt.
   At each state-D left record the tape is 0 1 1 (0 1)^N REGION, where REGION lists the lengths of 1-runs.
   Every sweep is one of three micro rules (R1, R2, RB) or a special event, and the micro rules give two
   absorption macros by induction (binary counters). The proof: the opening to a main-phase record (M030open);
   level 1 as macro stretches and 29 special sweeps, each replayed by a framed concrete run (M030L1); and a
   final translated cycler with period 85 and shift 1 (M030run, M030c). *)
From BusyCoq Require Import Individual62.
Require Import Lia List NArith String.

Module TM1.
Module M030a.
(* M030a: definitions and the generic sweep lemmas.
   - The record `rec N zs`: the head in state D on a 0 at the left end, then 0 1 1, (0 1)^N and the region zs
     (each z is a 0 followed by z ones), then blank.
   - Generic sweep lemmas: the inchworms over the long run (0 1)^N. *)
Import ListNotations.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_---0RD").

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

(* ---------- definitions ---------- *)
(* one region run: a 0, then z ones *)
Definition tok (z : nat) : list Sym := 0 :: [1]^^z.
Fixpoint reg (zs : list nat) : list Sym :=
  match zs with [] => [] | z :: t => tok z ++ reg t end.
(* the record: head on a 0 in state D; then 0 1 1, (0 1)^N, the region; blank after *)
Definition rec (N : nat) (zs : list nat) : Q * tape :=
  const 0 {{D}}> [0;0;1;1] *> [0;1]^^N *> reg zs *> const 0.

(* ---------- generic sweep lemmas ---------- *)
(* the rightward inchworm, seen at the B phase: a [1;0;0] block (nearest-first) walks right, leaving 1 1 behind *)
Lemma inchB_n l r n : l <* [1;0;0] {{B}}> [0;1]^^n *> r -->* l <* [1;1]^^n <* [1;0;0] {{B}}> r.
Proof. shift_rule. execute. Qed.

(* the leftward inchworm: D on the nearest 1 of the converted run, [0;0;1] ahead; it restores (0 1) pairs *)
Lemma inchD_n l r n : l <* [1;1]^^n <{{D}} [0;0;1] *> r -->* l <{{D}} [0;0;1] *> [0;1]^^n *> r.
Proof. shift_rule. execute. Qed.

(* the start of a sweep: from the record to the B phase on the first pair (8 steps; r is never read) *)
Lemma sweep_start r :
  const 0 {{D}}> [0;0;1;1] *> r -->+ const 0 <* [1;1] <* [1;0;0] {{B}}> r.
Proof. execute. Qed.

(* the whole rightward crossing of the long run *)
Lemma cross_r N r :
  const 0 {{D}}> [0;0;1;1] *> [0;1]^^N *> r -->+ const 0 <* [1;1]^^(S N) <* [1;0;0] {{B}}> r.
Proof.
  eapply progress_evstep_trans; [apply sweep_start|].
  eapply evstep_trans; [apply inchB_n|].
  rewrite lpow_S, Str_app_assoc, lpow_shift'. apply evstep_refl.
Qed.

(* the end of a sweep: from the last 1 of the converted run to the record form *)
Lemma sweep_end r : const 0 <* [1] <{{D}} [0;0;1] *> r -->+ const 0 {{D}}> [0;0;1;1;0;1] *> r.
Proof. execute. Qed.

End M030a.
Optimize Heap.

Module M030g.
(* M030g: a framed concrete stepper and its soundness, generic in the machine. The left side beyond the
   concrete frame is an arbitrary side L, so a step that would read it fails, and a run that succeeds is valid
   for every L. The special events are replayed this way while the long run stays symbolic. *)
Import ListNotations.

Section Framed.
Context (tm : TM).

(* (l, r, m, s): l = concrete left part, nearest-first; r = right part (blank beyond); m = head symbol; s = state *)
Definition fcfg : Set := (list Sym * list Sym * Sym * Q)%type.

Definition fcfg_to (Lf : side) (x : fcfg) : Q * tape :=
  let '(l, r, m, s) := x in (s, (Lf <* l, m, r *> const 0)).

Definition fstep (x : fcfg) : option fcfg :=
  let '(l, r, m, s) := x in
  match tm (s, m) with
  | Some (o, L, s') => match l with a :: l' => Some (l', o :: r, a, s') | [] => None end
  | Some (o, R, s') => Some (o :: l, tl r, hd 0 r, s')
  | None => None
  end.

Lemma fstep_sound Lf x y : fstep x = Some y -> fcfg_to Lf x -[ tm ]->* fcfg_to Lf y.
Proof.
  destruct x as [[[l r] m] s]. unfold fstep, fcfg_to.
  destruct (tm (s, m)) as [[[o d] s']|] eqn:E; [|discriminate].
  destruct d.
  - destruct l as [|a l']; [discriminate|].
    intro H. injection H as <-.
    eapply evstep_step; [apply (step_left E)|].
    apply evstep_refl'. reflexivity.
  - intro H. injection H as <-.
    eapply evstep_step; [apply (step_right E)|].
    apply evstep_refl'. destruct r as [|b r']; reflexivity.
Qed.

(* the stop test is a parameter: frun stops (without stepping) as soon as it holds *)
Context (stopb : fcfg -> bool).

Inductive fres := Stop (x : fcfg) | Run (x : fcfg) | Fail.

Definition fres_cfg (o : fres) : option fcfg :=
  match o with Stop x => Some x | Run x => Some x | Fail => None end.

Definition fone (x : fcfg) : fres :=
  if stopb x then Stop x else match fstep x with Some y => Run y | None => Fail end.

(* up to p steps, binary recursion depth *)
Fixpoint frun (p : positive) (x : fcfg) : fres :=
  match p with
  | xH => fone x
  | xO p' => match frun p' x with Run y => frun p' y | o => o end
  | xI p' => match fone x with
             | Run y => match frun p' y with Run z => frun p' z | o => o end
             | o => o
             end
  end.

Lemma fone_sound Lf x y : fres_cfg (fone x) = Some y -> fcfg_to Lf x -[ tm ]->* fcfg_to Lf y.
Proof.
  unfold fone. destruct (stopb x).
  - intro H. injection H as <-. apply evstep_refl.
  - destruct (fstep x) as [z|] eqn:E; [|discriminate].
    intro H. injection H as <-. apply fstep_sound. exact E.
Qed.

Lemma frun_sound p : forall Lf x y, fres_cfg (frun p x) = Some y -> fcfg_to Lf x -[ tm ]->* fcfg_to Lf y.
Proof.
  induction p as [p IH|p IH|]; intros Lf x y H; cbn [frun] in H.
  - destruct (fone x) as [z|z|] eqn:E1.
    + cbn in H. injection H as <-. apply fone_sound. rewrite E1. reflexivity.
    + eapply evstep_trans; [apply fone_sound with (y := z); rewrite E1; reflexivity|].
      destruct (frun p z) as [w|w|] eqn:E2.
      * cbn in H. injection H as <-. apply IH. rewrite E2. reflexivity.
      * eapply evstep_trans; [apply IH with (y := w); rewrite E2; reflexivity|].
        apply IH. exact H.
      * discriminate.
    + discriminate.
  - destruct (frun p x) as [z|z|] eqn:E1.
    + cbn in H. injection H as <-. apply IH. rewrite E1. reflexivity.
    + eapply evstep_trans; [apply IH with (y := z); rewrite E1; reflexivity|].
      apply IH. exact H.
    + discriminate.
  - apply fone_sound. exact H.
Qed.

(* the form used for each event: a Stop whose right part equals a given list up to trailing blanks *)
Lemma frun_stop_sound p Lf x l r m s r' :
  frun p x = Stop (l, r, m, s) -> cside_eqb r r' = true ->
  fcfg_to Lf x -[ tm ]->* (s, (Lf <* l, m, r' *> const 0)).
Proof.
  intros H1 H2.
  rewrite <- (cside_eqb_spec r r' H2).
  apply (frun_sound p Lf x (l, r, m, s)). rewrite H1. reflexivity.
Qed.
End Framed.
End M030g.
Optimize Heap.

Module M030h.
(* M030h: a two-sided framed stepper (generic) and the micro rule R2 proved with it. Both sides beyond the
   concrete lists are arbitrary, so a successful run is valid for every long run and every right part. R2's
   region work is 125 concrete steps that never read past the separator before y's run. *)
Import M030a M030g.
Import ListNotations.
Open Scope list.

Section Framed2.
Context (tm : TM).

Definition fcfg_to2 (Lf Rf : side) (x : fcfg) : Q * tape :=
  let '(l, r, m, s) := x in (s, (Lf <* l, m, r *> Rf)).

Definition fstep2 (x : fcfg) : option fcfg :=
  let '(l, r, m, s) := x in
  match tm (s, m) with
  | Some (o, L, s') => match l with a :: l' => Some (l', o :: r, a, s') | [] => None end
  | Some (o, R, s') => match r with b :: r' => Some (o :: l, r', b, s') | [] => None end
  | None => None
  end.

Lemma fstep2_sound Lf Rf x y : fstep2 x = Some y -> fcfg_to2 Lf Rf x -[ tm ]->* fcfg_to2 Lf Rf y.
Proof.
  destruct x as [[[l r] m] s]. unfold fstep2, fcfg_to2.
  destruct (tm (s, m)) as [[[o d] s']|] eqn:E; [|discriminate].
  destruct d.
  - destruct l as [|a l']; [discriminate|].
    intro H. injection H as <-.
    eapply evstep_step; [apply (step_left E)|].
    apply evstep_refl'. reflexivity.
  - destruct r as [|b r']; [discriminate|].
    intro H. injection H as <-.
    eapply evstep_step; [apply (step_right E)|].
    apply evstep_refl'. reflexivity.
Qed.

Context (stopb : fcfg -> bool).

Definition fone2 (x : fcfg) : fres :=
  if stopb x then Stop x else match fstep2 x with Some y => Run y | None => Fail end.

Fixpoint frun2 (p : positive) (x : fcfg) : fres :=
  match p with
  | xH => fone2 x
  | xO p' => match frun2 p' x with Run y => frun2 p' y | o => o end
  | xI p' => match fone2 x with
             | Run y => match frun2 p' y with Run z => frun2 p' z | o => o end
             | o => o
             end
  end.

Lemma fone2_sound Lf Rf x y : fres_cfg (fone2 x) = Some y -> fcfg_to2 Lf Rf x -[ tm ]->* fcfg_to2 Lf Rf y.
Proof.
  unfold fone2. destruct (stopb x).
  - intro H. injection H as <-. apply evstep_refl.
  - destruct (fstep2 x) as [z|] eqn:E; [|discriminate].
    intro H. injection H as <-. apply fstep2_sound. exact E.
Qed.

Lemma frun2_sound p : forall Lf Rf x y, fres_cfg (frun2 p x) = Some y ->
  fcfg_to2 Lf Rf x -[ tm ]->* fcfg_to2 Lf Rf y.
Proof.
  induction p as [p IH|p IH|]; intros Lf Rf x y H; cbn [frun2] in H.
  - destruct (fone2 x) as [z|z|] eqn:E1.
    + cbn in H. injection H as <-. apply fone2_sound. rewrite E1. reflexivity.
    + eapply evstep_trans; [apply fone2_sound with (y := z); rewrite E1; reflexivity|].
      destruct (frun2 p z) as [w|w|] eqn:E2.
      * cbn in H. injection H as <-. apply IH. rewrite E2. reflexivity.
      * eapply evstep_trans; [apply IH with (y := w); rewrite E2; reflexivity|].
        apply IH. exact H.
      * discriminate.
    + discriminate.
  - destruct (frun2 p x) as [z|z|] eqn:E1.
    + cbn in H. injection H as <-. apply IH. rewrite E1. reflexivity.
    + eapply evstep_trans; [apply IH with (y := z); rewrite E1; reflexivity|].
      apply IH. exact H.
    + discriminate.
  - apply fone2_sound. exact H.
Qed.
End Framed2.

(* ---------- the stop form and an exact Stop check ---------- *)
Fixpoint ones_even (l : list Sym) : bool :=
  match l with
  | [] => true
  | a :: [] => false
  | a :: b :: t => if sym_eqb a 1 then (if sym_eqb b 1 then ones_even t else false) else false
  end.
Definition pre001 (r : list Sym) : bool :=
  match r with
  | a :: b :: c :: _ => if sym_eqb a 0 then (if sym_eqb b 0 then sym_eqb c 1 else false) else false
  | _ => false
  end.
Definition isD (s : Q) : bool := match s with D => true | _ => false end.
Definition stopb (x : fcfg) : bool :=
  let '(l, r, m, s) := x in
  if isD s then if sym_eqb m 1 then if pre001 r then ones_even l else false else false else false.

Fixpoint lst_eqb (x y : list Sym) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => if sym_eqb a b then lst_eqb x' y' else false
  | _, _ => false
  end.
Lemma lst_eqb_spec x : forall y, lst_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
  destruct (sym_eqb_spec a b) as [->|]; [|discriminate].
  f_equal. apply IH. exact H.
Qed.

Definition stop2_ok (o : fres) (lexp rexp : list Sym) : bool :=
  match o with
  | Stop (l, r, m, s) =>
      if isD s then if sym_eqb m 1 then if lst_eqb l lexp then lst_eqb r rexp else false else false else false
  | _ => false
  end.

Lemma stop2_ok_sound p x Lf Rf lexp rexp :
  stop2_ok (frun2 tm stopb p x) lexp rexp = true ->
  fcfg_to2 Lf Rf x -[ tm ]->* (D, (Lf <* lexp, 1, rexp *> Rf)).
Proof.
  unfold stop2_ok. destruct (frun2 tm stopb p x) as [[[[l r] m] s]| |] eqn:E; try discriminate.
  destruct s; try discriminate. cbn [isD].
  destruct (sym_eqb_spec m 1) as [->|]; [|discriminate].
  destruct (lst_eqb l lexp) eqn:El; [|discriminate].
  apply lst_eqb_spec in El. subst lexp. intro H. apply lst_eqb_spec in H. subst rexp.
  apply (frun2_sound tm stopb p Lf Rf x (l, r, 1, D)). rewrite E. reflexivity.
Qed.

(* ---------- runs of ones ---------- *)
Lemma ones_add a b X : [1]^^(a + b) *> X = [1]^^a *> [1]^^b *> X.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.
Lemma pairs_ones n X : [1;1]^^n *> X = [1]^^(n + n) *> X.
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (S n + S n) with (S (S (n + n))) by lia.
  cbn [lpow]. rewrite Str_app_assoc, IH. reflexivity.
Qed.
Lemma ones_eq a b X : a = b -> [1]^^a *> X = [1]^^b *> X.
Proof. intros ->. reflexivity. Qed.

(* ---------- R2 ---------- *)
(* frame: the last 2 long-run pairs and the region prefix tok 4 ++ tok 1 ++ [0] *)
Definition R2_start : fcfg := ([1;0;0], [1;0;1] ++ [0;1;1;1;1;0;1;0], 0, B).

Lemma R2_frame : stop2_ok (frun2 tm stopb 200%positive R2_start) ([1]^^4) ([0;0;1] ++ [1]^^7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma R2_shape N (R : side) :
  (D, ((const 0 <* [1;1]^^(S N)) <* [1]^^4, 1, R)) =
  (const 0 <* [1] <* [1;1]^^(N + 3) <{{D}} R).
Proof.
  assert (HL : (const 0 <* [1;1]^^(S N)) <* [1]^^4 = [1]^^(4 + (S N + S N)) *> const 0).
  { change ((const 0 <* [1;1]^^(S N)) <* [1]^^4) with ([1]^^4 *> [1;1]^^(S N) *> const 0).
    rewrite pairs_ones, <- ones_add. reflexivity. }
  assert (HX : const 0 <* [1] <* [1;1]^^(N + 3) = [1] *> [1]^^(4 + (S N + S N)) *> const 0).
  { change (const 0 <* [1] <* [1;1]^^(N + 3)) with ([1;1]^^(N + 3) *> [1] *> const 0).
    rewrite pairs_ones.
    change ([1] *> const 0) with ([1]^^1 *> const 0).
    rewrite <- ones_add.
    change ([1] *> [1]^^(4 + (S N + S N)) *> const 0) with ([1]^^1 *> [1]^^(4 + (S N + S N)) *> const 0).
    rewrite <- ones_add.
    apply ones_eq. lia. }
  rewrite HL, HX. reflexivity.
Qed.

Lemma R2_tail N y zs :
  [0;0;1;1;0;1] *> [0;1]^^(N + 3) *> [1]^^7 *> [1]^^y *> reg zs *> const 0 =
  [0;0;1;1] *> [0;1]^^(N + 3) *> reg ((y + 8) :: zs) *> const 0.
Proof.
  change (reg ((y + 8) :: zs)) with ((0 :: [1]^^(y + 8)) ++ reg zs).
  change [0;0;1;1;0;1] with ([0;0;1;1] ++ [0;1]).
  rewrite !Str_app_assoc. f_equal.
  rewrite <- lpow_shift'. f_equal.
  change ([0;1] *> [1]^^7 *> [1]^^y *> reg zs *> const 0)
    with (0 >> ([1]^^1 *> [1]^^7 *> [1]^^y *> reg zs *> const 0)).
  change ((0 :: [1]^^(y + 8)) *> reg zs *> const 0) with (0 >> ([1]^^(y + 8) *> reg zs *> const 0)).
  rewrite <- (ones_add 7 y), <- (ones_add 1 (7 + y)).
  f_equal. apply ones_eq. lia.
Qed.

Lemma reg_R2 y zs :
  reg (4 :: 1%nat :: y :: zs) *> const 0 = [0;1;1;1;1;0;1;0] *> [1]^^y *> reg zs *> const 0.
Proof. cbn [reg tok app lpow Str_app]. rewrite Str_app_assoc. reflexivity. Qed.

Lemma R2_ok N y zs : rec (N + 2) (4 :: 1%nat :: y :: zs) -[ tm ]->+ rec (N + 3) ((y + 8) :: zs).
Proof.
  unfold rec at 1. rewrite lpow_add, Str_app_assoc, reg_R2.
  eapply progress_evstep_trans; [apply cross_r|].
  eapply evstep_trans.
  { pose proof (stop2_ok_sound 200%positive R2_start (const 0 <* [1;1]^^(S N))
                 ([1]^^y *> reg zs *> const 0) _ _ R2_frame) as H.
    unfold fcfg_to2, R2_start in H. exact H. }
  eapply evstep_trans; [apply evstep_refl'; apply (R2_shape N)|].
  eapply evstep_trans; [apply inchD_n|].
  eapply evstep_trans; [apply progress_evstep, sweep_end|].
  unfold rec. rewrite <- R2_tail. apply evstep_refl.
Qed.
End M030h.
Optimize Heap.

Module M030e0.
(* M030e0: special event 0 as a complete lemma,
     rec (M+8) [2432]  -->*  rec (M+8) Z1,     Z1 = 9 1^1200 7 1^2 7 5^2 1^5 2,   for every M,
   built from cross_r, the framed concrete run (M030g; checked here by vm_compute), inchD_n and sweep_end. *)
Import M030a M030g.
Import ListNotations.
Open Scope list.

(* ---------- the stop form for the framed run ---------- *)
Fixpoint ones_even (l : list Sym) : bool :=
  match l with
  | [] => true
  | a :: [] => false
  | a :: b :: t => if sym_eqb a 1 then (if sym_eqb b 1 then ones_even t else false) else false
  end.
Definition pre001 (r : list Sym) : bool :=
  match r with
  | a :: b :: c :: _ => if sym_eqb a 0 then (if sym_eqb b 0 then sym_eqb c 1 else false) else false
  | _ => false
  end.
Definition isD (s : Q) : bool := match s with D => true | _ => false end.
Definition stopb (x : fcfg) : bool :=
  let '(l, r, m, s) := x in
  if isD s then if sym_eqb m 1 then if pre001 r then ones_even l else false else false else false.

(* ---------- checking a Stop ---------- *)
Fixpoint lst_eqb (x y : list Sym) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => if sym_eqb a b then lst_eqb x' y' else false
  | _, _ => false
  end.

Lemma lst_eqb_spec x : forall y, lst_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
  destruct (sym_eqb_spec a b) as [->|]; [|discriminate].
  f_equal. apply IH. exact H.
Qed.

Definition stop_ok (o : fres) (lexp rexp : list Sym) : bool :=
  match o with
  | Stop (l, r, m, s) =>
      if isD s then if sym_eqb m 1 then if lst_eqb l lexp then cside_eqb r rexp else false else false else false
  | _ => false
  end.

Lemma stop_ok_sound p x Lf lexp rexp :
  stop_ok (frun tm stopb p x) lexp rexp = true ->
  fcfg_to Lf x -[ tm ]->* (D, (Lf <* lexp, 1, rexp *> const 0)).
Proof.
  unfold stop_ok. destruct (frun tm stopb p x) as [[[[l r] m] s]| |] eqn:E; try discriminate.
  destruct s; try discriminate. cbn [isD].
  destruct (sym_eqb_spec m 1) as [->|]; [|discriminate].
  destruct (lst_eqb l lexp) eqn:El; [|discriminate].
  apply lst_eqb_spec in El. subst lexp. intro H.
  exact (frun_stop_sound tm stopb p Lf x l r 1 D rexp E H).
Qed.

(* ---------- runs of ones ---------- *)
Lemma ones_add a b X : [1]^^(a + b) *> X = [1]^^a *> [1]^^b *> X.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma pairs_ones n X : [1;1]^^n *> X = [1]^^(n + n) *> X.
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (S n + S n) with (S (S (n + n))) by lia.
  cbn [lpow]. rewrite Str_app_assoc, IH. reflexivity.
Qed.

(* ---------- event 0 ---------- *)
Definition Z1 : list nat :=
  [9%nat] ++ repeat 1%nat 1200 ++ [7%nat; 1%nat; 1%nat; 7%nat; 5%nat; 5%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 2%nat].

Definition ev0_start : fcfg := ([1;0;0], [1] ++ [0;1]^^7 ++ reg [2432%nat], 0, B).

(* the concrete part: 6,844,263 framed steps; the match stays inline in the statement *)
Lemma ev0_frame :
  stop_ok (frun tm stopb (6844273)%positive ev0_start) ([1]^^14) ([0;0;1] ++ [1]^^8 ++ reg (tl Z1)) = true.
Proof. Time vm_compute. reflexivity. Time Qed.

Lemma ones_eq a b X : a = b -> [1]^^a *> X = [1]^^b *> X.
Proof. intros ->. reflexivity. Qed.

Lemma reg_cons z zs : reg (z :: zs) = tok z ++ reg zs.
Proof. reflexivity. Qed.

(* the configuration after the frame, in the leftward-inchworm form: all its ones as one run *)
Lemma ev0_shape M R :
  (D, (([1]^^14 ++ [1;1]^^(S M)) *> const 0, 1, ([0;0;1] ++ R) *> const 0)) =
  (const 0 <* [1] <* [1;1]^^(M + 8) <{{D}} [0;0;1] *> R *> const 0).
Proof.
  assert (HL : ([1]^^14 ++ [1;1]^^(S M)) *> const 0 = [1]^^(14 + (S M + S M)) *> const 0).
  { rewrite Str_app_assoc, pairs_ones, <- ones_add. reflexivity. }
  assert (HX : const 0 <* [1] <* [1;1]^^(M + 8) = [1] *> [1]^^(14 + (S M + S M)) *> const 0).
  { change (const 0 <* [1] <* [1;1]^^(M + 8)) with ([1;1]^^(M + 8) *> [1] *> const 0).
    rewrite pairs_ones.
    change ([1] *> const 0) with ([1]^^1 *> const 0).
    rewrite <- ones_add.
    change ([1] *> [1]^^(14 + (S M + S M)) *> const 0) with ([1]^^1 *> [1]^^(14 + (S M + S M)) *> const 0).
    rewrite <- ones_add.
    apply ones_eq. lia. }
  rewrite HL, HX, Str_app_assoc. reflexivity.
Qed.

(* the record after the sweep: the last restored (0 1) pair joins the next run *)
Lemma ev0_tail M :
  [0;0;1;1;0;1] *> [0;1]^^(M + 8) *> ([1]^^8 ++ reg (tl Z1)) *> const 0 =
  [0;0;1;1] *> [0;1]^^(M + 8) *> reg Z1 *> const 0.
Proof.
  change [0;0;1;1;0;1] with ([0;0;1;1] ++ [0;1]).
  rewrite Str_app_assoc. f_equal.
  rewrite <- lpow_shift'. f_equal.   (* the rest closes by conversion: [0;1] ++ 1^8 ++ reg (tl Z1) = reg Z1 *)
Qed.

Lemma ev0 M : rec (M + 8) [2432%nat] -[ tm ]->* rec (M + 8) Z1.
Proof.
  unfold rec at 1. rewrite lpow_add, Str_app_assoc.
  (* cross M pairs of the long run *)
  eapply evstep_trans; [apply progress_evstep, cross_r|].
  (* the frame: 6,844,263 concrete steps, checked by ev0_frame *)
  eapply evstep_trans.
  { pose proof (stop_ok_sound (6844273)%positive ev0_start (const 0 <* [1;1]^^(S M)) _ _ ev0_frame) as H.
    unfold fcfg_to, ev0_start in H.
    rewrite <- !Str_app_assoc in H. exact H. }
  (* the leftward inchworm over all the converted ones, then the left end *)
  eapply evstep_trans; [apply evstep_refl'; apply (ev0_shape M ([1]^^8 ++ reg (tl Z1)))|].
  eapply evstep_trans; [apply inchD_n|].
  eapply evstep_trans; [apply progress_evstep, sweep_end|].
  unfold rec. rewrite ev0_tail. apply evstep_refl.
Qed.
End M030e0.
Optimize Heap.

Module M030ev.
(* M030ev: one generic lemma for the special events. For a special sweep from region zs: if the framed run
   (the last K+1 long-run pairs and the region) stops in the leftward-inchworm form with left [1]^^(c+c) and
   right [0;0;1] ++ X, and [0;1] ++ X = [0;1]^^d ++ reg zs', then
       rec (M + S K) zs  -->*  rec (M + 1 + c + d) zs'      for every M.
   Each special sweep is then an instance: one vm_compute check (the frame) and one decode equation. *)
Import M030a M030g M030e0.
Import ListNotations.
Open Scope list.

Definition ev_start (K : nat) (zs : list nat) : fcfg := ([1;0;0], [1] ++ [0;1]^^K ++ reg zs, 0, B).

Lemma shape_gen M c (R : side) :
  (D, ((const 0 <* [1;1]^^(S M)) <* [1]^^(c + c), 1, R)) =
  (const 0 <* [1] <* [1;1]^^(M + 1 + c) <{{D}} R).
Proof.
  assert (HL : (const 0 <* [1;1]^^(S M)) <* [1]^^(c + c) = [1]^^((c + c) + (S M + S M)) *> const 0).
  { change ((const 0 <* [1;1]^^(S M)) <* [1]^^(c + c)) with ([1]^^(c + c) *> [1;1]^^(S M) *> const 0).
    rewrite pairs_ones, <- ones_add. reflexivity. }
  assert (HX : const 0 <* [1] <* [1;1]^^(M + 1 + c) = [1] *> [1]^^((c + c) + (S M + S M)) *> const 0).
  { change (const 0 <* [1] <* [1;1]^^(M + 1 + c)) with ([1;1]^^(M + 1 + c) *> [1] *> const 0).
    rewrite pairs_ones.
    change ([1] *> const 0) with ([1]^^1 *> const 0).
    rewrite <- ones_add.
    change ([1] *> [1]^^((c + c) + (S M + S M)) *> const 0)
      with ([1]^^1 *> [1]^^((c + c) + (S M + S M)) *> const 0).
    rewrite <- ones_add.
    apply ones_eq. lia. }
  rewrite HL, HX. reflexivity.
Qed.

Lemma tail_gen n X d zs' :
  [0;1] ++ X = [0;1]^^d ++ reg zs' ->
  [0;0;1;1;0;1] *> [0;1]^^n *> X *> const 0 = [0;0;1;1] *> [0;1]^^(n + d) *> reg zs' *> const 0.
Proof.
  intro E.
  change [0;0;1;1;0;1] with ([0;0;1;1] ++ [0;1]).
  rewrite Str_app_assoc. f_equal.
  rewrite <- lpow_shift'.
  change ([0;1] *> X *> const 0) with (([0;1] ++ X) *> const 0).
  rewrite E, lpow_add, !Str_app_assoc. reflexivity.
Qed.

Lemma event_gen K c X d zs zs' p M :
  stop_ok (frun tm stopb p (ev_start K zs)) ([1]^^(c + c)) ([0;0;1] ++ X) = true ->
  [0;1] ++ X = [0;1]^^d ++ reg zs' ->
  rec (M + S K) zs -[ tm ]->* rec (M + 1 + c + d) zs'.
Proof.
  intros Hf Hd.
  unfold rec at 1. rewrite lpow_add, Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep, cross_r|].
  eapply evstep_trans.
  { pose proof (stop_ok_sound p (ev_start K zs) (const 0 <* [1;1]^^(S M)) _ _ Hf) as H.
    unfold fcfg_to, ev_start in H. rewrite !Str_app_assoc in H. exact H. }
  eapply evstep_trans; [apply evstep_refl'; apply (shape_gen M c)|].
  eapply evstep_trans; [apply inchD_n|].
  eapply evstep_trans; [apply progress_evstep, sweep_end|].
  unfold rec. rewrite <- (tail_gen _ _ _ _ Hd). apply evstep_refl.
Qed.


(* event 0 again, as an instance: K = 7, c = 7, d = 0 *)
Lemma ev0' M : rec (M + 8) [2432%nat] -[ tm ]->* rec (M + 8) Z1.
Proof.
  replace (rec (M + 8) Z1) with (rec (M + 1 + 7 + 0) Z1) by (f_equal; lia).
  apply (event_gen 7 7 ([1]^^8 ++ reg (tl Z1)) 0 [2432%nat] Z1 (6844273)%positive M).
  - exact ev0_frame.
  - reflexivity.
Qed.
End M030ev.
Optimize Heap.

Module M030r1.
(* M030r1: the micro rules R1 and RB (at the end), proved with two-sided frames that are the same for every
   accumulator size. R1:
     rec (M+8) ((2a+7) :: e :: zs) -->+ rec (M+10) (4 :: 1^a ++ (e+2) :: zs).
   frame A (89 steps): from the B phase on the last 8 long-run pairs to B on the accumulator's first 1;
   B-shift over the 2a+7 ones; frame B (6 steps): at the separator, into the leftward inchworm;
   inchD_n over the accumulator; frame C (19 steps): the turn at the region start; inchD_n over the long run;
   sweep_end. *)
Import M030a M030g M030h.
Import ListNotations.
Open Scope list.

(* ---------- the B-shift over a run of ones ---------- *)
Lemma B_ones l r n : l {{B}}> [1]^^n *> r -[ tm ]->* l <* [1]^^n {{B}}> r.
Proof. shift_rule. execute. Qed.

(* ---------- frame A's stop: B on the frame's last cell, reading 1 ---------- *)
Definition stopA (x : fcfg) : bool :=
  let '(l, r, m, s) := x in
  match s with B => if sym_eqb m 1 then (match r with [] => true | _ => false end) else false | _ => false end.

Definition okA (o : fres) (lexp : list Sym) : bool :=
  match o with Stop (l, r, m, s) => if lst_eqb l lexp then stopA (l, r, m, s) else false | _ => false end.

Lemma okA_sound p x Lf Rf lexp :
  okA (frun2 tm stopA p x) lexp = true -> fcfg_to2 Lf Rf x -[ tm ]->* (B, (Lf <* lexp, 1, Rf)).
Proof.
  unfold okA. destruct (frun2 tm stopA p x) as [[[[l r] m] s]| |] eqn:E; try discriminate.
  destruct (lst_eqb l lexp) eqn:El; [|discriminate]. apply lst_eqb_spec in El. subst lexp.
  unfold stopA. destruct s; try discriminate.
  destruct (sym_eqb_spec m 1) as [->|]; [|discriminate].
  destruct r as [|b r]; [|discriminate]. intros _.
  apply (frun2_sound tm stopA p Lf Rf x (l, [], 1, B)). rewrite E. reflexivity.
Qed.

(* ---------- the three concrete frames ---------- *)
Definition lA : list Sym := [0;0] ++ [1]^^18.
Definition R1A_start : fcfg := ([1;0;0], [1] ++ [0;1]^^7 ++ [0;1], 0, B).
Lemma R1A : okA (frun2 tm stopA 100%positive R1A_start) lA = true.
Proof. vm_compute. reflexivity. Qed.

Definition R1B_start : fcfg := ([1;1;1;1;1;1], [], 0, B).
Lemma R1B : stop2_ok (frun2 tm stopb 10%positive R1B_start) [1;1] [0;0;1;1] = true.
Proof. vm_compute. reflexivity. Qed.

Definition R1C_start : fcfg := ([0] ++ [1]^^18, [0;0;1;0;1], 0, D).
Lemma R1C : stop2_ok (frun2 tm stopb 30%positive R1C_start) ([1]^^18) [0;0;1;1;1;1] = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------- list algebra ---------- *)
Lemma ones_S n X : [1]^^(S n) *> X = 1 >> [1]^^n *> X.
Proof. reflexivity. Qed.

Lemma reg_ones a : reg (repeat 1%nat a) = [0;1]^^a.
Proof. induction a as [|a IH]; [reflexivity|]. cbn [repeat reg lpow]. rewrite IH. reflexivity. Qed.

Lemma reg_app xs ys : reg (xs ++ ys) = reg xs ++ reg ys.
Proof. induction xs as [|x xs IH]; [reflexivity|]. cbn [app reg]. rewrite IH, app_assoc. reflexivity. Qed.

(* the accumulator's ones as pairs, for the inchworm (L = everything left of them) *)
Lemma acc_shape a L (R : side) :
  (D, ((L <* [1]^^(2*a+1)) <* [1;1], 1, R)) = (L <* [1;1]^^(a+2) <{{D}} R).
Proof.
  assert (H1 : (L <* [1]^^(2*a+1)) <* [1;1] = 1 >> [1]^^(2*a+2) *> L).
  { change ((L <* [1]^^(2*a+1)) <* [1;1]) with ([1;1] *> [1]^^(2*a+1) *> L).
    change ([1;1] *> [1]^^(2*a+1) *> L) with (1 >> ([1] *> [1]^^(2*a+1) *> L)).
    f_equal. change ([1] *> [1]^^(2*a+1) *> L) with ([1]^^(S (2*a+1)) *> L).
    apply ones_eq. lia. }
  assert (H2 : L <* [1;1]^^(a+2) = 1 >> 1 >> [1]^^(2*a+2) *> L).
  { change (L <* [1;1]^^(a+2)) with ([1;1]^^(a+2) *> L).
    rewrite pairs_ones. replace (a + 2 + (a + 2)) with (S (S (2*a+2))) by lia. reflexivity. }
  rewrite H1, H2. reflexivity.
Qed.

Lemma R1_tail M a e zs :
  [0;0;1;1;0;1] *> [0;1]^^(M + 10) *> [1;1;1] *> [0;1]^^(a+1) *> [1] *> [1]^^e *> reg zs *> const 0 =
  [0;0;1;1] *> [0;1]^^(M + 10) *> reg (4 :: repeat 1%nat a ++ (e+2) :: zs) *> const 0.
Proof.
  change (reg (4 :: repeat 1%nat a ++ (e + 2) :: zs)) with (tok 4 ++ reg (repeat 1%nat a ++ (e + 2) :: zs)).
  rewrite reg_app, reg_ones.
  change (reg ((e + 2) :: zs)) with ((0 :: [1]^^(e + 2)) ++ reg zs).
  change [0;0;1;1;0;1] with ([0;0;1;1] ++ [0;1]).
  rewrite !Str_app_assoc. f_equal.
  rewrite <- lpow_shift'. f_equal.
  (* [0;1] [1;1;1] (0 1)^(a+1) [1] 1^e  =  0 1111 (0 1)^a 0 1^(e+2) *)
  change ([0;1] *> [1;1;1] *> [0;1]^^(a+1) *> [1] *> [1]^^e *> reg zs *> const 0)
    with (tok 4 *> [0;1]^^(a+1) *> [1] *> [1]^^e *> reg zs *> const 0).
  f_equal.
  replace (a + 1) with (S a) by lia. cbn [lpow]. rewrite Str_app_assoc.
  rewrite <- lpow_shift'. f_equal.
  change ([0;1] *> [1] *> [1]^^e *> reg zs *> const 0) with (0 >> [1]^^(S (S e)) *> reg zs *> const 0).
  change ((0 :: [1]^^(e + 2)) *> reg zs *> const 0) with (0 >> [1]^^(e + 2) *> reg zs *> const 0).
  f_equal. apply ones_eq. lia.
Qed.

Lemma reg_R1 a e zs :
  reg ((2*a+7) :: e :: zs) *> const 0 = [0;1] *> [1]^^(2*a+6) *> [0] *> [1]^^e *> reg zs *> const 0.
Proof.
  replace (2*a+7) with (S (2*a+6)) by lia.
  cbn [reg tok]. rewrite !Str_app_assoc. reflexivity.
Qed.

(* ---------- R1 ---------- *)
Lemma R1_ok M a e zs :
  rec (M + 8) ((2*a+7) :: e :: zs) -[ tm ]->+ rec (M + 10) (4 :: repeat 1%nat a ++ (e+2) :: zs).
Proof.
  set (Lf := const 0 <* [1;1]^^(S M)).
  set (RB := [1]^^e *> reg zs *> const 0).
  unfold rec at 1. rewrite reg_R1, lpow_add, Str_app_assoc.
  eapply progress_evstep_trans; [apply cross_r|].
  (* frame A *)
  eapply evstep_trans.
  { pose proof (okA_sound 100%positive R1A_start Lf ([1]^^(2*a+6) *> [0] *> RB) lA R1A) as H.
    unfold fcfg_to2, R1A_start in H. rewrite !Str_app_assoc in H.
    exact H. }
  (* the B-shift over the accumulator *)
  change (B, (Lf <* lA, 1, [1]^^(2*a+6) *> [0] *> RB)) with (Lf <* lA {{B}}> [1]^^(S (2*a+6)) *> [0] *> RB).
  eapply evstep_trans; [apply B_ones|].
  (* frame B: the accumulator's last 6 ones *)
  replace (S (2*a+6)) with (6 + (2*a+1)) by lia. rewrite lpow_add.
  eapply evstep_trans.
  { pose proof (stop2_ok_sound 10%positive R1B_start (Lf <* lA <* [1]^^(2*a+1)) RB _ _ R1B) as H.
    unfold fcfg_to2, R1B_start in H. exact H. }
  (* inchworm over the accumulator *)
  eapply evstep_trans; [apply evstep_refl'; apply (acc_shape a (Lf <* lA))|].
  eapply evstep_trans; [apply inchD_n|].
  (* frame C: the turn at the region start *)
  eapply evstep_trans.
  { pose proof (stop2_ok_sound 30%positive R1C_start Lf ([0;1]^^(a+1) *> [1] *> RB) _ _ R1C) as H.
    unfold fcfg_to2, R1C_start in H.
    replace (a + 2) with (S (a + 1)) by lia. cbn [lpow]. rewrite !Str_app_assoc.
    exact H. }
  (* inchworm over the long run, then the left end *)
  eapply evstep_trans; [apply evstep_refl'; apply (M030ev.shape_gen M 9)|].
  eapply evstep_trans; [apply inchD_n|].
  eapply evstep_trans; [apply progress_evstep, sweep_end|].
  replace (M + 1 + 9) with (M + 10) by lia.
  unfold rec. rewrite <- R1_tail. unfold RB. apply evstep_refl.
Qed.


(* ======================= RB (frames of 132, 6 and 42 steps, identical for every x) ======================= *)
Definition lB' : list Sym := [0;0;1;0;0] ++ [1]^^16.
Definition RBA_start : fcfg := ([1;0;0], [1] ++ [0;1]^^7 ++ [0;1;1;1;1] ++ [0;1], 0, B).
Lemma RBA : okA (frun2 tm stopA 200%positive RBA_start) ([1;1;1;1] ++ lB') = true.
Proof. vm_compute. reflexivity. Qed.

Definition RBC_start : fcfg := ([0;1;0;0] ++ [1]^^16, [0;0;1;0;1], 0, D).
Lemma RBC : stop2_ok (frun2 tm stopb 60%positive RBC_start) ([1]^^16) [0;0;1;1;1;1;1;1;1] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma reg_RB b y zs :
  reg (4 :: (2*b+3) :: y :: zs) *> const 0 =
  [0;1;1;1;1] *> [0;1] *> [1]^^(2*b+2) *> [0] *> [1]^^y *> reg zs *> const 0.
Proof.
  replace (2*b+3) with (S (2*b+2)) by lia.
  cbn [reg tok]. rewrite !Str_app_assoc. reflexivity.
Qed.

(* the accumulator after the B-shift: x ones plus the four converted ones of the 4-token, regrouped *)
Lemma RB_regroup b L :
  ((L <* lB') <* [1;1;1;1]) <* [1]^^(S (2*b+2)) = ((L <* lB') <* [1]^^(2*b+1)) <* [1]^^6.
Proof.
  change (((L <* lB') <* [1;1;1;1]) <* [1]^^(S (2*b+2))) with ([1]^^(S (2*b+2)) *> [1]^^4 *> (L <* lB')).
  change (((L <* lB') <* [1]^^(2*b+1)) <* [1]^^6) with ([1]^^6 *> [1]^^(2*b+1) *> (L <* lB')).
  rewrite <- !ones_add. apply ones_eq. lia.
Qed.

Lemma RB_tail M b y zs :
  [0;0;1;1;0;1] *> [0;1]^^(M + 9) *> [1;1;1;1;1;1] *> [0;1]^^(b+1) *> [1] *> [1]^^y *> reg zs *> const 0 =
  [0;0;1;1] *> [0;1]^^(M + 9) *> reg (7 :: repeat 1%nat b ++ (y+2) :: zs) *> const 0.
Proof.
  change (reg (7 :: repeat 1%nat b ++ (y + 2) :: zs)) with (tok 7 ++ reg (repeat 1%nat b ++ (y + 2) :: zs)).
  rewrite reg_app, reg_ones.
  change (reg ((y + 2) :: zs)) with ((0 :: [1]^^(y + 2)) ++ reg zs).
  change [0;0;1;1;0;1] with ([0;0;1;1] ++ [0;1]).
  rewrite !Str_app_assoc. f_equal.
  rewrite <- lpow_shift'. f_equal.
  change ([0;1] *> [1;1;1;1;1;1] *> [0;1]^^(b+1) *> [1] *> [1]^^y *> reg zs *> const 0)
    with (tok 7 *> [0;1]^^(b+1) *> [1] *> [1]^^y *> reg zs *> const 0).
  f_equal.
  replace (b + 1) with (S b) by lia. cbn [lpow]. rewrite Str_app_assoc.
  rewrite <- lpow_shift'. f_equal.
  change ([0;1] *> [1] *> [1]^^y *> reg zs *> const 0) with (0 >> [1]^^(S (S y)) *> reg zs *> const 0).
  change ((0 :: [1]^^(y + 2)) *> reg zs *> const 0) with (0 >> [1]^^(y + 2) *> reg zs *> const 0).
  f_equal. apply ones_eq. lia.
Qed.

Lemma RB_ok M b y zs :
  rec (M + 8) (4 :: (2*b+3) :: y :: zs) -[ tm ]->+ rec (M + 9) (7 :: repeat 1%nat b ++ (y+2) :: zs).
Proof.
  set (Lf := const 0 <* [1;1]^^(S M)).
  set (RY := [1]^^y *> reg zs *> const 0).
  unfold rec at 1. rewrite reg_RB, lpow_add, Str_app_assoc.
  eapply progress_evstep_trans; [apply cross_r|].
  (* frame A: the R2-like stretch, until B is on x's first 1 *)
  eapply evstep_trans.
  { pose proof (okA_sound 200%positive RBA_start Lf ([1]^^(2*b+2) *> [0] *> RY) _ RBA) as H.
    unfold fcfg_to2, RBA_start in H. rewrite !Str_app_assoc in H.
    exact H. }
  (* the B-shift over x = 2b+3 ones *)
  change (B, ([1;1;1;1] *> lB' *> Lf, 1, [1]^^(2*b+2) *> [0] *> RY))
    with ((Lf <* lB') <* [1;1;1;1] {{B}}> [1]^^(S (2*b+2)) *> [0] *> RY).
  eapply evstep_trans; [apply B_ones|].
  rewrite RB_regroup.
  (* frame B *)
  eapply evstep_trans.
  { pose proof (stop2_ok_sound 10%positive R1B_start (Lf <* lB' <* [1]^^(2*b+1)) RY _ _ R1B) as H.
    unfold fcfg_to2, R1B_start in H. exact H. }
  (* inchworm over the accumulator *)
  eapply evstep_trans; [apply evstep_refl'; apply (acc_shape b (Lf <* lB'))|].
  eapply evstep_trans; [apply inchD_n|].
  (* frame C: the turn *)
  eapply evstep_trans.
  { pose proof (stop2_ok_sound 60%positive RBC_start Lf ([0;1]^^(b+1) *> [1] *> RY) _ _ RBC) as H.
    unfold fcfg_to2, RBC_start in H.
    replace (b + 2) with (S (b + 1)) by lia. cbn [lpow]. rewrite !Str_app_assoc.
    exact H. }
  (* the long run and the left end *)
  eapply evstep_trans; [apply evstep_refl'; apply (M030ev.shape_gen M 8)|].
  eapply evstep_trans; [apply inchD_n|].
  eapply evstep_trans; [apply progress_evstep, sweep_end|].
  replace (M + 1 + 8) with (M + 9) by lia.
  unfold rec. rewrite <- RB_tail. unfold RY. apply evstep_refl.
Qed.
End M030r1.
Optimize Heap.

Module M030d.
(* M030d: the macro driver for level 1. mstep applies one macro or micro rule to a region and mrun iterates
   it; M030m.mrun_soundK turns any run into reachability. A stretch of the real orbit between two special events
   is then one vm_compute equation  mrun 5000 Zout_k = Zin_(k+1). *)
Import M030a.
Import ListNotations.
Open Scope list.

Definition oddb (n : nat) : bool := PeanoNat.Nat.odd n.

(* half n = n / 2, as a plain fixpoint (Nat.div unfolds to divmod in proofs) *)
Fixpoint half (n : nat) : nat := match n with S (S k) => S (half k) | _ => O end.
Lemma half_double k : half (2 * k) = k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (2 * S k) with (S (S (2 * k))) by lia. cbn [half]. rewrite IH. reflexivity.
Qed.

(* one step; None = no rule applies (a special event) *)
Definition mstep (zs : list nat) : option (list nat) :=
  match zs with
  | X :: y :: t =>
      if andb (oddb X) (PeanoNat.Nat.leb 9 X) then Some ((X + y + 1) :: t)            (* class I *)
      else if PeanoNat.Nat.eqb X 7 then
        (if oddb y then
           match t with
           | y' :: t' => Some (7 :: (y + y' + 1) :: t')                               (* class II *)
           | [] => Some (4 :: (y + 2) :: t)                                           (* A at the edge *)
           end
         else Some (4 :: (y + 2) :: t))                                               (* A, even x *)
      else if PeanoNat.Nat.eqb X 4 then
        match t with
        | y' :: t' =>
            if PeanoNat.Nat.eqb y 1 then Some ((y' + 8) :: t')                         (* R2 *)
            else if andb (oddb y) (PeanoNat.Nat.leb 3 y)
                 then Some (7 :: repeat 1%nat (half (y - 3)) ++ (y' + 2) :: t')         (* RB *)
                 else None
        | [] => None
        end
      else None
  | _ => None
  end.

Fixpoint mrun (fuel : nat) (zs : list nat) : list nat :=
  match fuel with
  | O => zs
  | S f => match mstep zs with Some zs' => mrun f zs' | None => zs end
  end.

Lemma odd_form n : PeanoNat.Nat.odd n = true -> exists k, n = 2 * k + 1.
Proof.
  intro H. apply PeanoNat.Nat.odd_spec in H. destruct H as [k Hk]. exists k. lia.
Qed.

End M030d.
Optimize Heap.

Module M030m.
(* M030m: the absorption macros and the driver's soundness over reachK (long run >= 8), with R1, R2 and RB from
   M030r1.R1_ok, M030h.R2_ok and M030r1.RB_ok. *)
Import M030a M030d.
Import ListNotations.
Open Scope list.

Definition reachK (zs zs' : list nat) : Prop :=
  forall N, 8 <= N -> exists N', 8 <= N' /\ rec N zs -[ tm ]->* rec N' zs'.

Lemma reachK_refl zs : reachK zs zs.
Proof. intros N HN. exists N. split; [exact HN | apply evstep_refl]. Qed.

Lemma reachK_trans a b c : reachK a b -> reachK b c -> reachK a c.
Proof.
  intros H1 H2 N HN. destruct (H1 N HN) as [N1 [L1 E1]]. destruct (H2 N1 L1) as [N2 [L2 E2]].
  exists N2. split; [exact L2 | eapply evstep_trans; eauto].
Qed.

Lemma reachK_eq a b c : b = c -> reachK a b -> reachK a c.
Proof. intros ->. auto. Qed.

Lemma reachK_R1 a e zs : reachK ((2*a+7) :: e :: zs) (4 :: repeat 1%nat a ++ (e+2) :: zs).
Proof.
  intros N HN. exists (N - 8 + 10). split; [lia|].
  replace N with (N - 8 + 8) at 1 by lia. apply progress_evstep, M030r1.R1_ok.
Qed.

(* R2 from R2_ok (two-sided frame) *)
Lemma reachK_R2 y zs : reachK (4 :: 1%nat :: y :: zs) ((y+8) :: zs).
Proof.
  intros N HN. exists (N - 2 + 3). split; [lia|].
  replace N with (N - 2 + 2) at 1 by lia. apply progress_evstep, M030h.R2_ok.
Qed.

Lemma reachK_RB b y zs : reachK (4 :: (2*b+3) :: y :: zs) (7 :: repeat 1%nat b ++ (y+2) :: zs).
Proof.
  intros N HN. exists (N - 8 + 9). split; [lia|].
  replace N with (N - 8 + 8) at 1 by lia. apply progress_evstep, M030r1.RB_ok.
Qed.

(* ---------- class I absorption ---------- *)
Definition PIK (a : nat) : Prop := forall y zs, reachK ((2*a+7) :: y :: zs) ((2*a+8+y) :: zs).

(* absorbing k ones with accumulators a, a+1, ..., a+k-1 *)
Lemma onesIK k : forall a zs, (forall i, a <= i < a + k -> PIK i) ->
  reachK ((2*a+7) :: repeat 1%nat k ++ zs) ((2*a+7+2*k) :: zs).
Proof.
  induction k as [|k IH]; intros a zs H.
  - replace (2*a+7+2*0) with (2*a+7) by lia. cbn [repeat app]. apply reachK_refl.
  - cbn [repeat app].
    eapply reachK_trans.
    + apply (H a). lia.
    + replace (2*a+8+1) with (2*(S a)+7) by lia.
      replace (2*a+7+2*S k) with (2*(S a)+7+2*k) by lia.
      apply IH. intros i Hi. apply H. lia.
Qed.

Lemma absorbIK : forall a, 1 <= a -> PIK a.
Proof.
  induction a as [a IH] using strong_induction.
  intros Ha y zs.
  destruct (PeanoNat.Nat.eq_dec a 1) as [->|Hne].
  - (* 9 y  -R1->  4 1 (y+2)  -R2->  (y+10) *)
    eapply reachK_trans; [apply (reachK_R1 1 y zs)|].
    cbn [repeat app].
    eapply reachK_eq; [|apply reachK_R2]. f_equal. lia.
  - (* a = a'+2:  R1, R2 (y = 1), absorb a' ones from 9, then absorb (y+2) with a'+1 *)
    destruct a as [|[|a']]; [lia | contradiction |].
    eapply reachK_trans; [apply (reachK_R1 (S (S a')) y zs)|].
    cbn [repeat app].
    eapply reachK_trans; [apply (reachK_R2 1%nat (repeat 1%nat a' ++ (y+2) :: zs))|].
    eapply reachK_trans; [apply (onesIK a' 1 ((y+2) :: zs)); intros i Hi; apply IH; lia|].
    replace (2*1+7+2*a') with (2*(S a')+7) by lia.
    eapply reachK_eq; [|apply (IH (S a')); lia].
    f_equal. lia.
Qed.

Lemma absorbIK_ones k a zs : 1 <= a ->
  reachK ((2*a+7) :: repeat 1%nat k ++ zs) ((2*a+7+2*k) :: zs).
Proof. intro Ha. apply onesIK. intros i Hi. apply absorbIK. lia. Qed.

(* ---------- class II absorption: 7 x y .. -> 7 (x+y+1) .., x = 2b+1 ---------- *)
Definition PIIK (b : nat) : Prop := forall y zs, reachK (7 :: (2*b+1) :: y :: zs) (7 :: (2*b+2+y) :: zs).

Lemma onesIIK k : forall b zs, (forall i, b <= i < b + k -> PIIK i) ->
  reachK (7 :: (2*b+1) :: repeat 1%nat k ++ zs) (7 :: (2*b+1+2*k) :: zs).
Proof.
  induction k as [|k IH]; intros b zs H.
  - replace (2*b+1+2*0) with (2*b+1) by lia. cbn [repeat app]. apply reachK_refl.
  - cbn [repeat app].
    eapply reachK_trans.
    + apply (H b). lia.
    + replace (2*b+2+1) with (2*(S b)+1) by lia.
      replace (2*b+1+2*S k) with (2*(S b)+1+2*k) by lia.
      apply IH. intros i Hi. apply H. lia.
Qed.

Lemma absorbIIK : forall b, PIIK b.
Proof.
  induction b as [b IH] using strong_induction.
  intros y zs.
  (* A = R1 at a = 0:  7 (2b+1) y ..  ->  4 (2b+3) y .. *)
  eapply reachK_trans; [apply (reachK_R1 0 (2*b+1) (y :: zs))|].
  cbn [repeat app].
  replace (2*b+1+2) with (2*b+3) by lia.
  (* RB:  4 (2b+3) y ..  ->  7 1^b (y+2) .. *)
  eapply reachK_trans; [apply reachK_RB|].
  destruct b as [|b'].
  - cbn [repeat app]. eapply reachK_eq; [|apply reachK_refl]. f_equal. f_equal. lia.
  - (* 7 1 1^b' (y+2) ..: class II with x = 1 absorbs b' ones, then (y+2) with x = 2b'+1 *)
    cbn [repeat app].
    eapply reachK_trans; [apply (onesIIK b' 0 ((y+2) :: zs)); intros i Hi; apply IH; lia|].
    replace (2*0+1+2*b') with (2*b'+1) by lia.
    eapply reachK_eq; [|apply (IH b'); lia].
    f_equal. f_equal. lia.
Qed.

Lemma absorbIIK_ones k b zs :
  reachK (7 :: (2*b+1) :: repeat 1%nat k ++ zs) (7 :: (2*b+1+2*k) :: zs).
Proof. apply onesIIK. intros i Hi. apply absorbIIK. Qed.


Lemma mstep_soundK zs zs' : mstep zs = Some zs' -> reachK zs zs'.
Proof.
  unfold mstep. destruct zs as [|X [|y t]]; try discriminate.
  destruct (andb (oddb X) (PeanoNat.Nat.leb 9 X)) eqn:E1.
  - (* class I *)
    intro H. injection H as <-.
    apply Bool.andb_true_iff in E1. destruct E1 as [Eo El].
    apply odd_form in Eo. destruct Eo as [k ->]. apply PeanoNat.Nat.leb_le in El.
    replace (2 * k + 1) with (2 * (k - 3) + 7) by lia.
    eapply reachK_eq; [|apply absorbIK; lia]. f_equal. lia.
  - destruct (PeanoNat.Nat.eqb X 7) eqn:E7.
    + apply PeanoNat.Nat.eqb_eq in E7. subst X.
      destruct (oddb y) eqn:Ey.
      * destruct t as [|y' t'].
        -- intro H. injection H as <-.
           pose proof (reachK_R1 0 y []) as R. cbn [repeat app] in R. exact R.
        -- intro H. injection H as <-.
           apply odd_form in Ey. destruct Ey as [b ->].
           eapply reachK_eq; [|apply absorbIIK]. f_equal. f_equal. lia.
      * intro H. injection H as <-.
        pose proof (reachK_R1 0 y t) as R. cbn [repeat app] in R. exact R.
    + destruct (PeanoNat.Nat.eqb X 4) eqn:E4; [|discriminate].
      apply PeanoNat.Nat.eqb_eq in E4. subst X.
      destruct t as [|y' t']; [discriminate|].
      destruct (PeanoNat.Nat.eqb y 1) eqn:Ey1.
      * apply PeanoNat.Nat.eqb_eq in Ey1. subst y.
        intro H. injection H as <-. apply reachK_R2.
      * destruct (andb (oddb y) (PeanoNat.Nat.leb 3 y)) eqn:Eb; [|discriminate].
        intro H. injection H as <-.
        apply Bool.andb_true_iff in Eb. destruct Eb as [Eo El].
        apply odd_form in Eo. destruct Eo as [k ->]. apply PeanoNat.Nat.leb_le in El.
        replace (2 * k + 1) with (2 * (k - 1) + 3) by lia.
        replace (2 * (k - 1) + 3 - 3) with (2 * (k - 1)) by lia. rewrite half_double.
        apply reachK_RB.
Qed.

Lemma mrun_soundK fuel : forall zs, reachK zs (mrun fuel zs).
Proof.
  induction fuel as [|f IH]; intro zs; cbn [mrun]; [apply reachK_refl|].
  destruct (mstep zs) as [zs'|] eqn:E; [|apply reachK_refl].
  eapply reachK_trans; [apply mstep_soundK; exact E|]. apply IH.
Qed.
End M030m.
Optimize Heap.

Module M030evs_00.
(* M030evs_00: special event 0 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 0, sweep 0: 6844263 framed steps; region [2432] -> [9 1^1200 7 1^2 7 5^2 1^5 2] *)
Module sw_00_0.
Definition zin : list nat := [2432%nat].
Definition zout : list nat := [9%nat] ++ repeat 1%nat 1200 ++ [7%nat] ++ repeat 1%nat 2 ++ [7%nat] ++ repeat 5%nat 2 ++ repeat 1%nat 5 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (6844273)%positive (ev_start 7 zin)) ([1]^^(7 + 7)) ([0;0;1] ++ [1]^^8 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 7 + 0) zout.
Proof. apply (event_gen 7 7 ([1]^^8 ++ reg (tl zout)) 0 zin zout (6844273)%positive M frame). reflexivity. Qed.
End sw_00_0.
End M030evs_00.
Optimize Heap.

Module M030evs_01.
(* M030evs_01: special event 1 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 1, sweep 0: 20782439 framed steps; region [2454] -> [10 1^1208 4 1 3 1 7 1^6 3 1^4 2] *)
Module sw_01_0.
Definition zin : list nat := [2454%nat].
Definition zout : list nat := [10%nat] ++ repeat 1%nat 1208 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ [7%nat] ++ repeat 1%nat 6 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (20782449)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^9 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^9 ++ reg (tl zout)) 0 zin zout (20782449)%positive M frame). reflexivity. Qed.
End sw_01_0.


(* event 1, sweep 1: 779 framed steps; region [10 1^1208 4 1 3 1 7 1^6 3 1^4 2] -> [13 1^2 5 1^1202 4 1 3 1 7 1^6 3 1^4 2] *)
Module sw_01_1.
Definition zin : list nat := [10%nat] ++ repeat 1%nat 1208 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ [7%nat] ++ repeat 1%nat 6 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [13%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ repeat 1%nat 1202 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ [7%nat] ++ repeat 1%nat 6 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (789)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^12 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^12 ++ reg (tl zout)) 0 zin zout (789)%positive M frame). reflexivity. Qed.
End sw_01_1.
End M030evs_01.
Optimize Heap.

Module M030evs_02.
(* M030evs_02: special event 2 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 2, sweep 0: 7012217 framed steps; region [2432 1 3 1 7 1^6 3 1^4 2] -> [4 1^1217 4 7 3 5^2 1^3 2] *)
Module sw_02_0.
Definition zin : list nat := [2432%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ [7%nat] ++ repeat 1%nat 6 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1217 ++ [4%nat] ++ [7%nat] ++ [3%nat] ++ repeat 5%nat 2 ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7012227)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7012227)%positive M frame). reflexivity. Qed.
End sw_02_0.
End M030evs_02.
Optimize Heap.

Module M030evs_03.
(* M030evs_03: special event 3 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 3, sweep 0: 7028291 framed steps; region [2444 7 3 5^2 1^3 2] -> [9 1^1217 9 1 5 1 3 5 1^2 2] *)
Module sw_03_0.
Definition zin : list nat := [2444%nat] ++ [7%nat] ++ [3%nat] ++ repeat 5%nat 2 ++ repeat 1%nat 3 ++ [2%nat].
Definition zout : list nat := [9%nat] ++ repeat 1%nat 1217 ++ [9%nat] ++ [1%nat] ++ [5%nat] ++ [1%nat] ++ [3%nat] ++ [5%nat] ++ repeat 1%nat 2 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7028301)%positive (ev_start 7 zin)) ([1]^^(7 + 7)) ([0;0;1] ++ [1]^^8 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 7 + 0) zout.
Proof. apply (event_gen 7 7 ([1]^^8 ++ reg (tl zout)) 0 zin zout (7028301)%positive M frame). reflexivity. Qed.
End sw_03_0.
End M030evs_03.
Optimize Heap.

Module M030evs_04.
(* M030evs_04: special event 4 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 4, sweep 0: 7118045 framed steps; region [2480] -> [9 1^1224 7 1^2 3 1 7 5 1^5 2] *)
Module sw_04_0.
Definition zin : list nat := [2480%nat].
Definition zout : list nat := [9%nat] ++ repeat 1%nat 1224 ++ [7%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ [1%nat] ++ [7%nat] ++ [5%nat] ++ repeat 1%nat 5 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7118055)%positive (ev_start 7 zin)) ([1]^^(7 + 7)) ([0;0;1] ++ [1]^^8 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 7 + 0) zout.
Proof. apply (event_gen 7 7 ([1]^^8 ++ reg (tl zout)) 0 zin zout (7118055)%positive M frame). reflexivity. Qed.
End sw_04_0.
End M030evs_04.
Optimize Heap.

Module M030evs_05.
(* M030evs_05: special event 5 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 5, sweep 0: 21609079 framed steps; region [2502] -> [10 1^1232 4 1 3 1^2 7 1^5 3 1^4 2] *)
Module sw_05_0.
Definition zin : list nat := [2502%nat].
Definition zout : list nat := [10%nat] ++ repeat 1%nat 1232 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 2 ++ [7%nat] ++ repeat 1%nat 5 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (21609089)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^9 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^9 ++ reg (tl zout)) 0 zin zout (21609089)%positive M frame). reflexivity. Qed.
End sw_05_0.


(* event 5, sweep 1: 779 framed steps; region [10 1^1232 4 1 3 1^2 7 1^5 3 1^4 2] -> [13 1^2 5 1^1226 4 1 3 1^2 7 1^5 3 1^4 2] *)
Module sw_05_1.
Definition zin : list nat := [10%nat] ++ repeat 1%nat 1232 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 2 ++ [7%nat] ++ repeat 1%nat 5 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [13%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ repeat 1%nat 1226 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 2 ++ [7%nat] ++ repeat 1%nat 5 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (789)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^12 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^12 ++ reg (tl zout)) 0 zin zout (789)%positive M frame). reflexivity. Qed.
End sw_05_1.
End M030evs_05.
Optimize Heap.

Module M030evs_06.
(* M030evs_06: special event 6 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 6, sweep 0: 20679207 framed steps; region [2480 1 3 1^2 7 1^5 3 1^4 2] -> [10 1^1205 4 1^3 3 1^4 5 3 1^9 3 9 1^2 3 1^9 3 1^3 2] *)
Module sw_06_0.
Definition zin : list nat := [2480%nat] ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 2 ++ [7%nat] ++ repeat 1%nat 5 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [10%nat] ++ repeat 1%nat 1205 ++ [4%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 4 ++ [5%nat] ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (20679217)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^9 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^9 ++ reg (tl zout)) 0 zin zout (20679217)%positive M frame). reflexivity. Qed.
End sw_06_0.


(* event 6, sweep 1: 779 framed steps; region [10 1^1205 4 1^3 3 1^4 5 3 1^9 3 9 1^2 3 1^9 3 1^3 2] -> [13 1^2 5 1^1199 4 1^3 3 1^4 5 3 1^9 3 9 1^2 3 1^9 3 1^3 2] *)
Module sw_06_1.
Definition zin : list nat := [10%nat] ++ repeat 1%nat 1205 ++ [4%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 4 ++ [5%nat] ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Definition zout : list nat := [13%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ repeat 1%nat 1199 ++ [4%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 4 ++ [5%nat] ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (789)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^12 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^12 ++ reg (tl zout)) 0 zin zout (789)%positive M frame). reflexivity. Qed.
End sw_06_1.
End M030evs_06.
Optimize Heap.

Module M030evs_07.
(* M030evs_07: special event 7 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 7, sweep 0: 6953847 framed steps; region [2426 1^3 3 1^4 5 3 1^9 3 9 1^2 3 1^9 3 1^3 2] -> [4 1^1212 4 3 1 3 9 3 1^8 3 9 1^2 3 1^9 3 1^3 2] *)
Module sw_07_0.
Definition zin : list nat := [2426%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 4 ++ [5%nat] ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1212 ++ [4%nat] ++ [3%nat] ++ [1%nat] ++ [3%nat] ++ [9%nat] ++ [3%nat] ++ repeat 1%nat 8 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (6953857)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (6953857)%positive M frame). reflexivity. Qed.
End sw_07_0.
End M030evs_07.
Optimize Heap.

Module M030evs_08.
(* M030evs_08: special event 8 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 8, sweep 0: 6976721 framed steps; region [2434 3 1 3 9 3 1^8 3 9 1^2 3 1^9 3 1^3 2] -> [4 1^1214 4 11 1^3 5 1^7 3 9 1^2 3 1^9 3 1^3 2] *)
Module sw_08_0.
Definition zin : list nat := [2434%nat] ++ [3%nat] ++ [1%nat] ++ [3%nat] ++ [9%nat] ++ [3%nat] ++ repeat 1%nat 8 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1214 ++ [4%nat] ++ [11%nat] ++ repeat 1%nat 3 ++ [5%nat] ++ repeat 1%nat 7 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (6976731)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (6976731)%positive M frame). reflexivity. Qed.
End sw_08_0.
End M030evs_08.
Optimize Heap.

Module M030evs_09.
(* M030evs_09: special event 9 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 9, sweep 0: 6993959 framed steps; region [2438 11 1^3 5 1^7 3 9 1^2 3 1^9 3 1^3 2] -> [9 1^1214 11 7 1^2 5 1^6 3 9 1^2 3 1^9 3 1^3 2] *)
Module sw_09_0.
Definition zin : list nat := [2438%nat] ++ [11%nat] ++ repeat 1%nat 3 ++ [5%nat] ++ repeat 1%nat 7 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Definition zout : list nat := [9%nat] ++ repeat 1%nat 1214 ++ [11%nat] ++ [7%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ repeat 1%nat 6 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 9 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (6993969)%positive (ev_start 7 zin)) ([1]^^(7 + 7)) ([0;0;1] ++ [1]^^8 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 7 + 0) zout.
Proof. apply (event_gen 7 7 ([1]^^8 ++ reg (tl zout)) 0 zin zout (6993969)%positive M frame). reflexivity. Qed.
End sw_09_0.
End M030evs_09.
Optimize Heap.

Module M030evs_10.
(* M030evs_10: special event 10 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 10, sweep 0: 22133925 framed steps; region [2532] -> [10 1^1247 4 1^3 3^2 1 3 1^4 3 1^4 2] *)
Module sw_10_0.
Definition zin : list nat := [2532%nat].
Definition zout : list nat := [10%nat] ++ repeat 1%nat 1247 ++ [4%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 2 ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 4 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (22133935)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^9 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^9 ++ reg (tl zout)) 0 zin zout (22133935)%positive M frame). reflexivity. Qed.
End sw_10_0.


(* event 10, sweep 1: 779 framed steps; region [10 1^1247 4 1^3 3^2 1 3 1^4 3 1^4 2] -> [13 1^2 5 1^1241 4 1^3 3^2 1 3 1^4 3 1^4 2] *)
Module sw_10_1.
Definition zin : list nat := [10%nat] ++ repeat 1%nat 1247 ++ [4%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 2 ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 4 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [13%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ repeat 1%nat 1241 ++ [4%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 2 ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 4 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (789)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^12 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^12 ++ reg (tl zout)) 0 zin zout (789)%positive M frame). reflexivity. Qed.
End sw_10_1.
End M030evs_10.
Optimize Heap.

Module M030evs_11.
(* M030evs_11: special event 11 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 11, sweep 0: 7440599 framed steps; region [2510 1^3 3^2 1 3 1^4 3 1^4 2] -> [4 1^1254 4 3 1 3 5^2 3 1^4 2] *)
Module sw_11_0.
Definition zin : list nat := [2510%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 2 ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 4 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1254 ++ [4%nat] ++ [3%nat] ++ [1%nat] ++ [3%nat] ++ repeat 5%nat 2 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7440609)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7440609)%positive M frame). reflexivity. Qed.
End sw_11_0.
End M030evs_11.
Optimize Heap.

Module M030evs_12.
(* M030evs_12: special event 12 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 12, sweep 0: 7464251 framed steps; region [2518 3 1 3 5^2 3 1^4 2] -> [4 1^1256 4 5 11 1^2 3 1^3 2] *)
Module sw_12_0.
Definition zin : list nat := [2518%nat] ++ [3%nat] ++ [1%nat] ++ [3%nat] ++ repeat 5%nat 2 ++ [3%nat] ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1256 ++ [4%nat] ++ [5%nat] ++ [11%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7464261)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7464261)%positive M frame). reflexivity. Qed.
End sw_12_0.
End M030evs_12.
Optimize Heap.

Module M030evs_13.
(* M030evs_13: special event 13 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 13, sweep 0: 7482089 framed steps; region [2522 5 11 1^2 3 1^3 2] -> [9 1^1256 9 3 1^2 11 1^3 2] *)
Module sw_13_0.
Definition zin : list nat := [2522%nat] ++ [5%nat] ++ [11%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 3 ++ [2%nat].
Definition zout : list nat := [9%nat] ++ repeat 1%nat 1256 ++ [9%nat] ++ [3%nat] ++ repeat 1%nat 2 ++ [11%nat] ++ repeat 1%nat 3 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7482099)%positive (ev_start 7 zin)) ([1]^^(7 + 7)) ([0;0;1] ++ [1]^^8 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 7 + 0) zout.
Proof. apply (event_gen 7 7 ([1]^^8 ++ reg (tl zout)) 0 zin zout (7482099)%positive M frame). reflexivity. Qed.
End sw_13_0.
End M030evs_13.
Optimize Heap.

Module M030evs_14.
(* M030evs_14: special event 14 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 14, sweep 0: 7592111 framed steps; region [2560] -> [4 1^1266 4 5 1^2 9 5 1^5 2] *)
Module sw_14_0.
Definition zin : list nat := [2560%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1266 ++ [4%nat] ++ [5%nat] ++ repeat 1%nat 2 ++ [9%nat] ++ [5%nat] ++ repeat 1%nat 5 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7592121)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7592121)%positive M frame). reflexivity. Qed.
End sw_14_0.
End M030evs_14.
Optimize Heap.

Module M030evs_15.
(* M030evs_15: special event 15 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 15, sweep 0: 7606607 framed steps; region [2542 5 1^2 9 5 1^5 2] -> [4 1^1268 4 1^6 3 1 3^2 1^4 2] *)
Module sw_15_0.
Definition zin : list nat := [2542%nat] ++ [5%nat] ++ repeat 1%nat 2 ++ [9%nat] ++ [5%nat] ++ repeat 1%nat 5 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1268 ++ [4%nat] ++ repeat 1%nat 6 ++ [3%nat] ++ [1%nat] ++ repeat 3%nat 2 ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7606617)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7606617)%positive M frame). reflexivity. Qed.
End sw_15_0.
End M030evs_15.
Optimize Heap.

Module M030evs_16.
(* M030evs_16: special event 16 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 16, sweep 0: 7654259 framed steps; region [2546 1^6 3 1 3^2 1^4 2] -> [4 1^1272 4 1^3 5 1 3 1 3 1^2 2] *)
Module sw_16_0.
Definition zin : list nat := [2546%nat] ++ repeat 1%nat 6 ++ [3%nat] ++ [1%nat] ++ repeat 3%nat 2 ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1272 ++ [4%nat] ++ repeat 1%nat 3 ++ [5%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 2 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7654269)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7654269)%positive M frame). reflexivity. Qed.
End sw_16_0.
End M030evs_16.
Optimize Heap.

Module M030evs_17.
(* M030evs_17: special event 17 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 17, sweep 0: 22977345 framed steps; region [2554 1^3 5 1 3 1 3 1^2 2] -> [10 1^1271 4 1^3 3 1^2 5 1 6] *)
Module sw_17_0.
Definition zin : list nat := [2554%nat] ++ repeat 1%nat 3 ++ [5%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ [3%nat] ++ repeat 1%nat 2 ++ [2%nat].
Definition zout : list nat := [10%nat] ++ repeat 1%nat 1271 ++ [4%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ [1%nat] ++ [6%nat].
Lemma frame : stop_ok (frun tm stopb (22977355)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^9 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^9 ++ reg (tl zout)) 0 zin zout (22977355)%positive M frame). reflexivity. Qed.
End sw_17_0.


(* event 17, sweep 1: 779 framed steps; region [10 1^1271 4 1^3 3 1^2 5 1 6] -> [13 1^2 5 1^1265 4 1^3 3 1^2 5 1 6] *)
Module sw_17_1.
Definition zin : list nat := [10%nat] ++ repeat 1%nat 1271 ++ [4%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ [1%nat] ++ [6%nat].
Definition zout : list nat := [13%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ repeat 1%nat 1265 ++ [4%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ [1%nat] ++ [6%nat].
Lemma frame : stop_ok (frun tm stopb (789)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^12 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^12 ++ reg (tl zout)) 0 zin zout (789)%positive M frame). reflexivity. Qed.
End sw_17_1.
End M030evs_17.
Optimize Heap.

Module M030evs_18.
(* M030evs_18: special event 18 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 18, sweep 0: 4908929 framed steps; region [2558 1^3 3 1^2 5 1 6] -> [9 1^965 4 1^2 3 1^3 3^2 1^296 3 9 1^8 2] *)
Module sw_18_0.
Definition zin : list nat := [2558%nat] ++ repeat 1%nat 3 ++ [3%nat] ++ repeat 1%nat 2 ++ [5%nat] ++ [1%nat] ++ [6%nat].
Definition zout : list nat := [9%nat] ++ repeat 1%nat 965 ++ [4%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 2 ++ repeat 1%nat 296 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 8 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (4908939)%positive (ev_start 7 zin)) ([1]^^(7 + 7)) ([0;0;1] ++ [1]^^8 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 7 + 0) zout.
Proof. apply (event_gen 7 7 ([1]^^8 ++ reg (tl zout)) 0 zin zout (4908939)%positive M frame). reflexivity. Qed.
End sw_18_0.
End M030evs_18.
Optimize Heap.

Module M030evs_19.
(* M030evs_19: special event 19 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 19, sweep 0: 4471239 framed steps; region [1944 1^2 3 1^3 3^2 1^296 3 9 1^8 2] -> [4 1^970 4 1^2 3 11 3 1^293 3 9 1^8 2] *)
Module sw_19_0.
Definition zin : list nat := [1944%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 2 ++ repeat 1%nat 296 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 8 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 970 ++ [4%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ [11%nat] ++ [3%nat] ++ repeat 1%nat 293 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 8 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (4471249)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (4471249)%positive M frame). reflexivity. Qed.
End sw_19_0.
End M030evs_19.
Optimize Heap.

Module M030evs_20.
(* M030evs_20: special event 20 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 20, sweep 0: 4493741 framed steps; region [1950 1^2 3 11 3 1^293 3 9 1^8 2] -> [9 1^971 7 1^3 3^2 1^2 5 1^290 3 9 1^8 2] *)
Module sw_20_0.
Definition zin : list nat := [1950%nat] ++ repeat 1%nat 2 ++ [3%nat] ++ [11%nat] ++ [3%nat] ++ repeat 1%nat 293 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 8 ++ [2%nat].
Definition zout : list nat := [9%nat] ++ repeat 1%nat 971 ++ [7%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 2 ++ repeat 1%nat 2 ++ [5%nat] ++ repeat 1%nat 290 ++ [3%nat] ++ [9%nat] ++ repeat 1%nat 8 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (4493751)%positive (ev_start 7 zin)) ([1]^^(7 + 7)) ([0;0;1] ++ [1]^^8 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 7 + 0) zout.
Proof. apply (event_gen 7 7 ([1]^^8 ++ reg (tl zout)) 0 zin zout (4493751)%positive M frame). reflexivity. Qed.
End sw_20_0.
End M030evs_20.
Optimize Heap.

Module M030evs_21.
(* M030evs_21: special event 21 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 21, sweep 0: 7807763 framed steps; region [2596] -> [4 1^1284 4 9^2 5 1^5 2] *)
Module sw_21_0.
Definition zin : list nat := [2596%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1284 ++ [4%nat] ++ repeat 9%nat 2 ++ [5%nat] ++ repeat 1%nat 5 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7807773)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7807773)%positive M frame). reflexivity. Qed.
End sw_21_0.
End M030evs_21.
Optimize Heap.

Module M030evs_22.
(* M030evs_22: special event 22 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 22, sweep 0: 7822607 framed steps; region [2578 9^2 5 1^5 2] -> [4 1^1286 4 1 3 1 3^2 1 3^2 1^4 2] *)
Module sw_22_0.
Definition zin : list nat := [2578%nat] ++ repeat 9%nat 2 ++ [5%nat] ++ repeat 1%nat 5 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1286 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ repeat 3%nat 2 ++ [1%nat] ++ repeat 3%nat 2 ++ repeat 1%nat 4 ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7822617)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7822617)%positive M frame). reflexivity. Qed.
End sw_22_0.
End M030evs_22.
Optimize Heap.

Module M030evs_23.
(* M030evs_23: special event 23 of level 1; each of its sweeps is an instance of
   M030ev.event_gen. *)
Import M030a M030g M030e0 M030ev.
Import ListNotations.
Open Scope list.


(* event 23, sweep 0: 7895573 framed steps; region [2582 1 3 1 3^2 1 3^2 1^4 2] -> [4 1^1292 4 1 3 5 9 1 2] *)
Module sw_23_0.
Definition zin : list nat := [2582%nat] ++ [1%nat] ++ [3%nat] ++ [1%nat] ++ repeat 3%nat 2 ++ [1%nat] ++ repeat 3%nat 2 ++ repeat 1%nat 4 ++ [2%nat].
Definition zout : list nat := [4%nat] ++ repeat 1%nat 1292 ++ [4%nat] ++ [1%nat] ++ [3%nat] ++ [5%nat] ++ [9%nat] ++ [1%nat] ++ [2%nat].
Lemma frame : stop_ok (frun tm stopb (7895583)%positive (ev_start 7 zin)) ([1]^^(8 + 8)) ([0;0;1] ++ [1]^^3 ++ reg (tl zout)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweep M : rec (M + S 7) zin -[ tm ]->* rec (M + 1 + 8 + 0) zout.
Proof. apply (event_gen 7 8 ([1]^^3 ++ reg (tl zout)) 0 zin zout (7895583)%positive M frame). reflexivity. Qed.
End sw_23_0.
End M030evs_23.
Optimize Heap.

Module M030c.
(* M030c: the final translated cycler. From the runaway (the last special event of level 1), every 85 steps
   the head is in state B on the new rightmost (blank) cell, and the 14 cells to its left read
   0 0 0 0 0 1 0 0 1 1 1 1 1 1. The head never goes more than 11 cells behind the edge, so everything left of
   those 14 cells is never read. *)
Import M030a.
Import ListNotations.
Open Scope list.

(* the 14 cells left of the head, nearest-first (reading order: 0 0 0 0 0 1 0 0 1 1 1 1 1 1) *)
Definition P : list Sym := [1;1;1;1;1;1;0;0;1;0;0;0;0;0].

Lemma cycle Lf : Lf <* P {{B}}> const 0 -[ tm ]->+ (Lf <* [0]) <* P {{B}}> const 0.
Proof. unfold P. execute. Qed.

Theorem cycler_nonhalt Lf : ~ halts tm (Lf <* P {{B}}> const 0).
Proof.
  apply (progress_nonhalt_simple tm side (fun L => L <* P {{B}}> const 0) Lf).
  intro L. exists (L <* [0]). apply cycle.
Qed.
End M030c.
Optimize Heap.

Module M030run.
(* M030run: the end of level 1. From the runaway region Z24 = 2594 1 3 5 9 1 2 a framed run (29,582 steps)
   reaches the cycler record, so rec (M+8) Z24 never halts. *)
Import M030a M030g M030e0 M030ev M030c.
Import ListNotations.
Open Scope list.

Definition Z24 : list nat := [2594%nat; 1%nat; 3%nat; 5%nat; 9%nat; 1%nat; 2%nat].

Fixpoint prefixb (p l : list Sym) : bool :=
  match p, l with
  | [], _ => true
  | a :: p', b :: l' => if sym_eqb a b then prefixb p' l' else false
  | _ :: _, [] => false
  end.

Lemma prefixb_spec p : forall l, prefixb p l = true -> exists rest, l = p ++ rest.
Proof.
  induction p as [|a p IH]; intros l H.
  - exists l. reflexivity.
  - destruct l as [|b l]; [discriminate|]. cbn in H.
    destruct (sym_eqb_spec a b) as [->|]; [|discriminate].
    destruct (IH l H) as [rest ->]. exists rest. reflexivity.
Qed.

(* the cycler record: state B on a blank with only blanks to the right, the 14 cells behind = P *)
Definition stopc (x : fcfg) : bool :=
  let '(l, r, m, s) := x in
  match s with
  | B => if sym_eqb m 0 then (match r with [] => prefixb P l | _ => false end) else false
  | _ => false
  end.

Definition run_ok (o : fres) : bool :=
  match o with Stop x => stopc x | _ => false end.

Lemma run_ok_sound p x Lf :
  run_ok (frun tm stopc p x) = true -> exists L, fcfg_to Lf x -[ tm ]->* L <* P {{B}}> const 0.
Proof.
  unfold run_ok. destruct (frun tm stopc p x) as [[[[l r] m] s]| |] eqn:E; try discriminate.
  unfold stopc. destruct s; try discriminate.
  destruct (sym_eqb_spec m 0) as [->|]; [|discriminate].
  destruct r as [|b r]; [|discriminate].
  intro H. apply prefixb_spec in H. destruct H as [rest ->].
  exists (Lf <* rest).
  pose proof (frun_sound tm stopc p Lf x (P ++ rest, [], 0, B)) as K.
  rewrite E in K. specialize (K eq_refl).
  unfold fcfg_to in K. rewrite Str_app_assoc in K. exact K.
Qed.

Lemma runaway_frame : run_ok (frun tm stopc 29600%positive (ev_start 7 Z24)) = true.
Proof. Time vm_compute. reflexivity. Qed.

Lemma runaway M : exists L, rec (M + 8) Z24 -[ tm ]->* L <* P {{B}}> const 0.
Proof.
  destruct (run_ok_sound 29600%positive (ev_start 7 Z24) (const 0 <* [1;1]^^(S M)) runaway_frame) as [L H].
  exists L.
  unfold rec. rewrite lpow_add, Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep, cross_r|].
  unfold fcfg_to, ev_start in H. rewrite !Str_app_assoc in H. exact H.
Qed.

Theorem from_Z24 M : ~ halts tm (rec (M + 8) Z24).
Proof.
  destruct (runaway M) as [L H].
  eapply multistep_nonhalt; [exact H | apply cycler_nonhalt].
Qed.
End M030run.
Optimize Heap.

Module M030open.
(* M030open: the opening, c0 -->* rec 1788 Z0, by a concrete stepper with a binary step count
   (21,824,158 steps). *)
Import M030a.
Import ListNotations.
Open Scope list.

Section BinStepper.
Context (tm : TM).

Fixpoint ccsteps (p : positive) (x : cconfig) : option cconfig :=
  match p with
  | xH => cconfig_step tm x
  | xO p' => match ccsteps p' x with Some x' => ccsteps p' x' | None => None end
  | xI p' => match cconfig_step tm x with
             | Some x1 => match ccsteps p' x1 with Some x2 => ccsteps p' x2 | None => None end
             | None => None
             end
  end.

Lemma cstep1 x y : cconfig_step tm x = Some y -> cconfig_to_config x -[ tm ]->* cconfig_to_config y.
Proof. intro H. pose proof (cconfig_step_spec tm x) as K. rewrite H in K. eapply evstep_step; [exact K|apply evstep_refl]. Qed.

Lemma ccsteps_sound p : forall x y, ccsteps p x = Some y -> cconfig_to_config x -[ tm ]->* cconfig_to_config y.
Proof.
  induction p as [p IH|p IH|]; intros x y H; cbn [ccsteps] in H.
  - destruct (cconfig_step tm x) as [x1|] eqn:E1; [|discriminate].
    destruct (ccsteps p x1) as [x2|] eqn:E2; [|discriminate].
    eapply evstep_trans; [apply cstep1; exact E1|]. eapply evstep_trans; [apply IH; exact E2|]. apply IH. exact H.
  - destruct (ccsteps p x) as [x1|] eqn:E1; [|discriminate].
    eapply evstep_trans; [apply IH; exact E1|]. apply IH. exact H.
  - apply cstep1. exact H.
Qed.

Definition ccreach (p : positive) (x y : cconfig) : bool :=
  match ccsteps p x with Some x' => cconfig_eqb x' y | None => false end.

Lemma ccreach_spec p x y : ccreach p x y = true -> cconfig_to_config x -[ tm ]->* cconfig_to_config y.
Proof.
  unfold ccreach. destruct (ccsteps p x) as [x'|] eqn:E; [|discriminate]. intro H.
  rewrite <- (cconfig_eqb_spec _ _ H). exact (ccsteps_sound p _ _ E).
Qed.
End BinStepper.

Definition Z0 : list nat :=
  [4%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 3 ++ [1%nat; 3%nat] ++ repeat 1%nat 1185 ++ [3%nat; 9%nat] ++
  repeat 1%nat 8 ++ [2%nat].

Definition open_target : cconfig := ([], [0;1;1] ++ [0;1]^^1788 ++ reg Z0, 0, D).

(* the check stays inline in the statement: vm_compute of a Definition holding it uses far more memory *)
Lemma opening_cc : ccreach tm 21824158%positive ([], [], 0, A) open_target = true.
Proof. Time vm_compute. reflexivity. Time Qed.

Lemma opening : c0 -[ tm ]->* rec 1788 Z0.
Proof.
  pose proof (ccreach_spec tm 21824158%positive _ _ opening_cc) as H.
  unfold cconfig_to_config, open_target in H. rewrite !Str_app_assoc in H.
  exact H.
Qed.
End M030open.
Optimize Heap.

Module M030L1.
(* M030L1: level 1, from the main-phase region Z0 to the runaway region Z24, as one chain of reach8 (= reachK,
   long run >= 8) steps. Stretches between special events are mrun equations (vm_compute, sound by
   M030m.mrun_soundK); the special sweeps come from M030evs_00 .. M030evs_23. *)
Import M030a M030g M030e0 M030ev M030d M030m.
Import M030evs_00 M030evs_01 M030evs_02 M030evs_03 M030evs_04 M030evs_05 M030evs_06 M030evs_07 M030evs_08 M030evs_09 M030evs_10 M030evs_11 M030evs_12 M030evs_13 M030evs_14 M030evs_15 M030evs_16 M030evs_17 M030evs_18 M030evs_19 M030evs_20 M030evs_21 M030evs_22 M030evs_23.
Import ListNotations.
Open Scope list.

Definition reach8 := reachK.

Lemma reach8_trans a b c : reach8 a b -> reach8 b c -> reach8 a c.
Proof. apply reachK_trans. Qed.

Lemma reach8_mrun f a b : mrun f a = b -> reach8 a b.
Proof. intros <-. apply mrun_soundK. Qed.

Lemma reach8_sweep c d zin zout : 7 <= c + d ->
  (forall M, rec (M + S 7) zin -[ tm ]->* rec (M + 1 + c + d) zout) -> reach8 zin zout.
Proof.
  intros Hc H N HN. exists (N - 8 + 1 + c + d). split; [lia|].
  replace N with (N - 8 + S 7) at 1 by lia. apply H.
Qed.

Definition Z0 : list nat :=
  [4%nat] ++ repeat 1%nat 3 ++ repeat 3%nat 3 ++ [1%nat; 3%nat] ++ repeat 1%nat 1185 ++ [3%nat; 9%nat] ++
  repeat 1%nat 8 ++ [2%nat].
Definition Z24 : list nat := [2594%nat; 1%nat; 3%nat; 5%nat; 9%nat; 1%nat; 2%nat].

Lemma st_00 : reach8 Z0 sw_00_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_00_0 : reach8 sw_00_0.zin sw_00_0.zout.
Proof. apply (reach8_sweep 7 0); [lia | exact sw_00_0.sweep]. Qed.

Lemma st_01 : reach8 sw_00_0.zout sw_01_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_01_0 : reach8 sw_01_0.zin sw_01_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_01_0.sweep]. Qed.

Lemma ev_01_1 : reach8 sw_01_1.zin sw_01_1.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_01_1.sweep]. Qed.

Lemma st_02 : reach8 sw_01_1.zout sw_02_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_02_0 : reach8 sw_02_0.zin sw_02_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_02_0.sweep]. Qed.

Lemma st_03 : reach8 sw_02_0.zout sw_03_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_03_0 : reach8 sw_03_0.zin sw_03_0.zout.
Proof. apply (reach8_sweep 7 0); [lia | exact sw_03_0.sweep]. Qed.

Lemma st_04 : reach8 sw_03_0.zout sw_04_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_04_0 : reach8 sw_04_0.zin sw_04_0.zout.
Proof. apply (reach8_sweep 7 0); [lia | exact sw_04_0.sweep]. Qed.

Lemma st_05 : reach8 sw_04_0.zout sw_05_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_05_0 : reach8 sw_05_0.zin sw_05_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_05_0.sweep]. Qed.

Lemma ev_05_1 : reach8 sw_05_1.zin sw_05_1.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_05_1.sweep]. Qed.

Lemma st_06 : reach8 sw_05_1.zout sw_06_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_06_0 : reach8 sw_06_0.zin sw_06_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_06_0.sweep]. Qed.

Lemma ev_06_1 : reach8 sw_06_1.zin sw_06_1.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_06_1.sweep]. Qed.

Lemma st_07 : reach8 sw_06_1.zout sw_07_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_07_0 : reach8 sw_07_0.zin sw_07_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_07_0.sweep]. Qed.

Lemma st_08 : reach8 sw_07_0.zout sw_08_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_08_0 : reach8 sw_08_0.zin sw_08_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_08_0.sweep]. Qed.

Lemma st_09 : reach8 sw_08_0.zout sw_09_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_09_0 : reach8 sw_09_0.zin sw_09_0.zout.
Proof. apply (reach8_sweep 7 0); [lia | exact sw_09_0.sweep]. Qed.

Lemma st_10 : reach8 sw_09_0.zout sw_10_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_10_0 : reach8 sw_10_0.zin sw_10_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_10_0.sweep]. Qed.

Lemma ev_10_1 : reach8 sw_10_1.zin sw_10_1.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_10_1.sweep]. Qed.

Lemma st_11 : reach8 sw_10_1.zout sw_11_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_11_0 : reach8 sw_11_0.zin sw_11_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_11_0.sweep]. Qed.

Lemma st_12 : reach8 sw_11_0.zout sw_12_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_12_0 : reach8 sw_12_0.zin sw_12_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_12_0.sweep]. Qed.

Lemma st_13 : reach8 sw_12_0.zout sw_13_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_13_0 : reach8 sw_13_0.zin sw_13_0.zout.
Proof. apply (reach8_sweep 7 0); [lia | exact sw_13_0.sweep]. Qed.

Lemma st_14 : reach8 sw_13_0.zout sw_14_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_14_0 : reach8 sw_14_0.zin sw_14_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_14_0.sweep]. Qed.

Lemma st_15 : reach8 sw_14_0.zout sw_15_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_15_0 : reach8 sw_15_0.zin sw_15_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_15_0.sweep]. Qed.

Lemma st_16 : reach8 sw_15_0.zout sw_16_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_16_0 : reach8 sw_16_0.zin sw_16_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_16_0.sweep]. Qed.

Lemma st_17 : reach8 sw_16_0.zout sw_17_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_17_0 : reach8 sw_17_0.zin sw_17_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_17_0.sweep]. Qed.

Lemma ev_17_1 : reach8 sw_17_1.zin sw_17_1.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_17_1.sweep]. Qed.

Lemma st_18 : reach8 sw_17_1.zout sw_18_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_18_0 : reach8 sw_18_0.zin sw_18_0.zout.
Proof. apply (reach8_sweep 7 0); [lia | exact sw_18_0.sweep]. Qed.

Lemma st_19 : reach8 sw_18_0.zout sw_19_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_19_0 : reach8 sw_19_0.zin sw_19_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_19_0.sweep]. Qed.

Lemma st_20 : reach8 sw_19_0.zout sw_20_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_20_0 : reach8 sw_20_0.zin sw_20_0.zout.
Proof. apply (reach8_sweep 7 0); [lia | exact sw_20_0.sweep]. Qed.

Lemma st_21 : reach8 sw_20_0.zout sw_21_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_21_0 : reach8 sw_21_0.zin sw_21_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_21_0.sweep]. Qed.

Lemma st_22 : reach8 sw_21_0.zout sw_22_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_22_0 : reach8 sw_22_0.zin sw_22_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_22_0.sweep]. Qed.

Lemma st_23 : reach8 sw_22_0.zout sw_23_0.zin.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma ev_23_0 : reach8 sw_23_0.zin sw_23_0.zout.
Proof. apply (reach8_sweep 8 0); [lia | exact sw_23_0.sweep]. Qed.

Lemma st_last : reach8 sw_23_0.zout Z24.
Proof. apply (reach8_mrun 2000). vm_compute. reflexivity. Qed.

Lemma level1 : reach8 Z0 Z24.
Proof.
  eapply reach8_trans; [exact st_00|].
  eapply reach8_trans; [exact ev_00_0|].
  eapply reach8_trans; [exact st_01|].
  eapply reach8_trans; [exact ev_01_0|].
  eapply reach8_trans; [exact ev_01_1|].
  eapply reach8_trans; [exact st_02|].
  eapply reach8_trans; [exact ev_02_0|].
  eapply reach8_trans; [exact st_03|].
  eapply reach8_trans; [exact ev_03_0|].
  eapply reach8_trans; [exact st_04|].
  eapply reach8_trans; [exact ev_04_0|].
  eapply reach8_trans; [exact st_05|].
  eapply reach8_trans; [exact ev_05_0|].
  eapply reach8_trans; [exact ev_05_1|].
  eapply reach8_trans; [exact st_06|].
  eapply reach8_trans; [exact ev_06_0|].
  eapply reach8_trans; [exact ev_06_1|].
  eapply reach8_trans; [exact st_07|].
  eapply reach8_trans; [exact ev_07_0|].
  eapply reach8_trans; [exact st_08|].
  eapply reach8_trans; [exact ev_08_0|].
  eapply reach8_trans; [exact st_09|].
  eapply reach8_trans; [exact ev_09_0|].
  eapply reach8_trans; [exact st_10|].
  eapply reach8_trans; [exact ev_10_0|].
  eapply reach8_trans; [exact ev_10_1|].
  eapply reach8_trans; [exact st_11|].
  eapply reach8_trans; [exact ev_11_0|].
  eapply reach8_trans; [exact st_12|].
  eapply reach8_trans; [exact ev_12_0|].
  eapply reach8_trans; [exact st_13|].
  eapply reach8_trans; [exact ev_13_0|].
  eapply reach8_trans; [exact st_14|].
  eapply reach8_trans; [exact ev_14_0|].
  eapply reach8_trans; [exact st_15|].
  eapply reach8_trans; [exact ev_15_0|].
  eapply reach8_trans; [exact st_16|].
  eapply reach8_trans; [exact ev_16_0|].
  eapply reach8_trans; [exact st_17|].
  eapply reach8_trans; [exact ev_17_0|].
  eapply reach8_trans; [exact ev_17_1|].
  eapply reach8_trans; [exact st_18|].
  eapply reach8_trans; [exact ev_18_0|].
  eapply reach8_trans; [exact st_19|].
  eapply reach8_trans; [exact ev_19_0|].
  eapply reach8_trans; [exact st_20|].
  eapply reach8_trans; [exact ev_20_0|].
  eapply reach8_trans; [exact st_21|].
  eapply reach8_trans; [exact ev_21_0|].
  eapply reach8_trans; [exact st_22|].
  eapply reach8_trans; [exact ev_22_0|].
  eapply reach8_trans; [exact st_23|].
  eapply reach8_trans; [exact ev_23_0|].
  exact st_last.
Qed.
End M030L1.
Optimize Heap.

Module M030top.
(* M030top: the theorem. The opening (M030open), level 1 (M030L1: macro stretches and the 29 special sweeps),
   then the runaway and the cycler (M030run). *)
Import M030a M030open M030L1 M030run.
Import ListNotations.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply opening|].
  destruct (level1 1788 ltac:(lia)) as [N' [HN' H1]].
  change M030open.Z0 with M030L1.Z0.
  eapply multistep_nonhalt; [exact H1|].
  replace N' with ((N' - 8) + 8) by lia.
  change M030L1.Z24 with M030run.Z24.
  apply from_Z24.
Qed.

End M030top.
Optimize Heap.

(* the theorem at the top of TM1 *)
Definition tm := M030a.tm.
Theorem nonhalt : ~ halts tm c0.
Proof. exact M030top.nonhalt. Qed.
Print Assumptions nonhalt.

End TM1.
