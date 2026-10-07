(* M1: macro-inductive nonhalting proof, ported to current BusyCoq.
   The two finite symbolic bridges are generated and checked inside Coq;
   no external trace table or generator is needed to compile this file. *)
From Coq Require Import Lia PeanoNat String ZArith List.
From BusyCoq Require Import Individual62 SimplTape.
Set Default Goal Selector "!".

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_0LC1RE_1LD1LC_1LA1RD_---1RF_0RA0RF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Tape algebra *)

Lemma lpow_snoc : forall (s : Sym) n (l : side),
  l << s <* [s]^^n = l <* [s]^^(S n).
Proof.
  intros s n l. induction n as [| n IH]; [reflexivity |].
  cbn [lpow app Str_app] in *. rewrite IH. reflexivity.
Qed.

Lemma lpow_snoc' : forall (s : Sym) n (l : side),
  s >> [s]^^n *> l = [s]^^n *> s >> l.
Proof. intros. symmetry. apply (lpow_snoc s n l). Qed.

Lemma lpow_app : forall (xs : list Sym) a b (r : side),
  xs^^a *> xs^^b *> r = xs^^(a + b) *> r.
Proof.
  intros. rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma lpow_cons_r : forall (s : Sym) n (r : side),
  [s]^^n *> s >> r = [s]^^(S n) *> r.
Proof.
  intros s n r. induction n as [| n IH]; [reflexivity |].
  cbn [lpow app Str_app] in *. rewrite IH. reflexivity.
Qed.

Lemma lpow_mul_S : forall (xs : list Sym) k (r : side),
  xs^^(S k) *> r = xs *> xs^^k *> r.
Proof. intros. cbn [lpow]. apply Str_app_assoc. Qed.

(** Replace the left-hand side of an [-->*] goal by a convertible term. *)
Ltac lhs_raw c :=
  lazymatch goal with
  | |- _ -[ ?t ]->* ?c' => change (c -[ t ]->* c')
  end.

(** Merge adjacent runs of the same symbol into one power, moving the
    concrete cells next to the head (convertible with "constant + ..." powers). *)
Ltac merge := repeat (rewrite lpow_cons_r || rewrite lpow_snoc).

Ltac lhs c := first [ lhs_raw c | merge; lhs_raw c ].

(** Normalise tapes: move concrete cells next to the head, so that
    convertibility checks succeed. *)
Ltac tnorm := repeat (rewrite lpow_cons_r || rewrite lpow_snoc); simpl_tape.
Ltac fin := solve [finish | merge; finish | tnorm; finish].

(** Stronger closing tactic: merge every pair of adjacent equal-symbol runs,
    then compare the exponents with [lia]. *)
Ltac fin2 :=
  apply evstep_refl';
  repeat (rewrite lpow_app || rewrite lpow_cons_r || rewrite lpow_snoc);
  simpl; lia_refl.

(** ** Sweeps (over runs of any length, including 0) *)

Lemma sweepC : forall e l r,
  l <* [1]^^e <{{C}} r -->* l <{{C}} [1]^^e *> r.
Proof.
  induction e as [| e IH]; intros l r.
  - finish.
  - cbn [lpow app Str_app]. step.
    follow IH. apply evstep_refl'. now rewrite lpow_cons_r.
Qed.

Lemma sweepD : forall e l r,
  l {{D}}> [1]^^e *> r -->* l <* [1]^^e {{D}}> r.
Proof.
  induction e as [| e IH]; intros l r.
  - finish.
  - cbn [lpow app Str_app]. step.
    follow IH. apply evstep_refl'. now rewrite lpow_snoc.
Qed.

Lemma sweepF : forall e l r,
  l {{F}}> [1]^^e *> r -->* l <* [0]^^e {{F}}> r.
Proof.
  induction e as [| e IH]; intros l r.
  - finish.
  - cbn [lpow app Str_app]. step.
    follow IH. apply evstep_refl'. now rewrite lpow_snoc.
Qed.

(** ** E(j), Climb, X1 (mutual strong induction on j) *)

Definition E_stmt j := forall l r m, j <= m ->
  l << 1 <* [0]^^(1 + j*3) {{A}}> 1 >> [1]^^m *> 0 >> r -->*
  l << 1 <* [1]^^(1 + j*3) <{{A}} 1 >> [1]^^m *> 0 >> r.

Lemma E0 : E_stmt 0.
Proof. intros l r m _. execute. Qed.

Lemma Climb_of_E : forall i, E_stmt i -> forall l r n, i + 1 <= n ->
  l <* [0]^^3 {{A}}> 0 >> [1]^^(2 + i*3) *> 0 >> [1]^^n *> 0 >> r -->*
  l {{A}}> 0 >> [1]^^(5 + i*3) *> 0 >> [1]^^n *> 0 >> r.
Proof.
  intros i HE l r n Hn.
  destruct n as [| n]; [lia |].
  execute.
  follow sweepF. step.
  follow HE; try lia.
  step. follow sweepC. execute.
Qed.

Lemma X1_of_E : forall i, E_stmt i -> forall l r n, i + 1 <= n ->
  l << 1 << 0 {{A}}> 0 >> [1]^^(2 + i*3) *> 0 >> [1]^^n *> 0 >> r -->*
  l <* [1]^^(5 + i*3) <{{A}} 1 >> [1]^^n *> 0 >> r.
Proof.
  intros i HE l r n Hn.
  destruct n as [| n]; [lia |].
  execute.
  follow sweepF. step.
  follow HE; try lia.
  step. follow sweepC. execute.
  follow sweepD. execute. fin.
Qed.

Lemma Climbs_of_E : forall k i,
  (forall i', i <= i' -> i' < i + k -> E_stmt i') ->
  forall l r n, i + k <= n ->
  l <* [0]^^(k*3) {{A}}> 0 >> [1]^^(2 + i*3) *> 0 >> [1]^^n *> 0 >> r -->*
  l {{A}}> 0 >> [1]^^(2 + (i + k)*3) *> 0 >> [1]^^n *> 0 >> r.
Proof.
  induction k as [| k IH]; intros i HE l r n Hn.
  - finish.
  - follow (Climb_of_E i (HE i ltac:(lia) ltac:(lia))
             ([0]^^(k*3) *> l) r n ltac:(lia)).
    follow (IH (S i)); try lia.
    + intros i' H1 H2. apply HE; lia.
    + finish.
Qed.


Lemma E_all : forall j, E_stmt j.
Proof.
  induction j as [j IH] using strong_induction.
  destruct j as [| j']. { apply E0. }
  intros l r m Hm. destruct m as [| m]; [lia |].
  destruct j' as [| j''].
  - execute.
  - do 18 step.
    rewrite (lpow_snoc' 0 (j''*3)).
    follow (Climbs_of_E j'' 1 (fun i' H1 H2 => IH i' ltac:(lia))
              (0 >> 1 >> l) r (S m) ltac:(lia)).
    follow (X1_of_E (S j'') (IH (S j'') ltac:(lia)) l r (S m) ltac:(lia)).
    fin.
Qed.

Lemma Climb : forall i l r n, i + 1 <= n ->
  l <* [0]^^3 {{A}}> 0 >> [1]^^(2 + i*3) *> 0 >> [1]^^n *> 0 >> r -->*
  l {{A}}> 0 >> [1]^^(5 + i*3) *> 0 >> [1]^^n *> 0 >> r.
Proof. intros. apply Climb_of_E; [apply E_all | assumption]. Qed.

Lemma Climbs : forall k i l r n, i + k <= n ->
  l <* [0]^^(k*3) {{A}}> 0 >> [1]^^(2 + i*3) *> 0 >> [1]^^n *> 0 >> r -->*
  l {{A}}> 0 >> [1]^^(2 + (i + k)*3) *> 0 >> [1]^^n *> 0 >> r.
Proof. intros. apply Climbs_of_E; [intros; apply E_all | assumption]. Qed.

Lemma X1 : forall i l r n, i + 1 <= n ->
  l << 1 << 0 {{A}}> 0 >> [1]^^(2 + i*3) *> 0 >> [1]^^n *> 0 >> r -->*
  l <* [1]^^(5 + i*3) <{{A}} 1 >> [1]^^n *> 0 >> r.
Proof. intros. apply X1_of_E; [apply E_all | assumption]. Qed.

(** ** Fail(J) for J >= 2, written with J = j + 2 *)

Lemma FailStep : forall j l r,
  l << 1 <* [0]^^(7 + j*3) {{A}}> 1 >> [1]^^(S j) *> 0 >> r -->*
  l << 1 << 0 << 1 << 1 << 1 <* [0]^^(4 + j*3) {{A}}> 1 >> [1]^^j *> 0 >> r.
Proof.
  intros j l r.
  do 18 step.
  rewrite (lpow_snoc' 0 (j*3)).
  follow (Climbs j 1 (0 >> 1 >> l) r (S j) ltac:(lia)).
  execute. follow sweepF. step. fin.
Qed.

Lemma lpow_shift_str : forall (xs : list Sym) n (r : side),
  xs^^n *> xs *> r = xs *> xs^^n *> r.
Proof. intros. apply lpow_shift'. Qed.

Lemma FailChain' : forall j l r,
  l << 1 <* [0]^^(7 + j*3) {{A}}> 1 >> [1]^^(S j) *> 0 >> r -->*
  l << 1 <* [1;1;1;0]^^(S j) <* [0]^^4 {{A}}> 1 >> 0 >> r.
Proof.
  induction j as [| j IH]; intros l r.
  - follow FailStep. finish.
  - follow FailStep.
    follow (IH (1 >> 1 >> 0 >> 1 >> l) r).
    apply evstep_refl'.
    change (1 >> 1 >> 1 >> 0 >> 1 >> l) with ([1;1;1;0] *> 1 >> l).
    rewrite lpow_shift_str. reflexivity.
Qed.

Lemma G_shift : forall n (l : side),
  [1;1;1;0]^^(S n) *> l = 1 >> 1 >> 1 >> [0;1;1;1]^^n *> 0 >> l.
Proof.
  induction n as [| n IH]; intros l; [reflexivity |].
  change ([1;1;1;0]^^(S (S n)) *> l)
    with (1 >> 1 >> 1 >> 0 >> [1;1;1;0]^^(S n) *> l).
  rewrite IH. reflexivity.
Qed.

(** The Fail(J) ... Fail(2) chain, conclusion written as in symsim.py:
    [L 0 (1110)^(J-2) 111 0^4 [A1] 0]  with  J = g + 2. *)
Lemma FailChain : forall g l r,
  l << 1 <* [0]^^(7 + g*3) {{A}}> 1 >> [1]^^(S g) *> 0 >> r -->*
  l << 1 << 0 <* [0;1;1;1]^^g <* [1]^^3 <* [0]^^4 {{A}}> 1 >> 0 >> r.
Proof.
  intros g l r. follow FailChain'.
  apply evstep_refl'. rewrite G_shift. reflexivity.
Qed.

(** ** ML *)

Lemma ML1 : forall m l r,
  l <* [1]^^3 << 0 <* [1]^^(S m) {{A}}> 1 >> r -->*
  l <* [1]^^(S m + 3) {{A}}> 1 >> 1 >> r.
Proof.
  intros m l r.
  step. lhs (l <* [1]^^3 << 0 <* [1]^^(S m) <{{C}} 0 >> r).
  follow sweepC. execute. follow sweepD. execute. fin.
Qed.

Lemma MLs : forall g m l r,
  l <* [0;1;1;1]^^g <* [1]^^(S m) {{A}}> 1 >> r -->*
  l <* [1]^^(S m + g*3) {{A}}> 1 >> [1]^^g *> r.
Proof.
  induction g as [| g IH]; intros m l r.
  - finish.
  - follow (ML1 m ([0;1;1;1]^^g *> l) r).
    follow (IH (m + 3) l (1 >> r)).
    apply evstep_refl'. rewrite lpow_cons_r. f_equal. f_equal. f_equal. f_equal.
    f_equal. lia.
Qed.

(** ** Macro forms used by the generated proofs (Tail.v, Base.v).
    All run lengths are separate variables, related by hypotheses that the
    generated script discharges with [lia]. *)

Lemma Mac_E : forall j z m l r, z = 1 + j*3 -> j <= m ->
  l << 1 <* [0]^^z {{A}}> 1 >> [1]^^m *> 0 >> r -->*
  l << 1 <* [1]^^z <{{A}} 1 >> [1]^^m *> 0 >> r.
Proof. intros. subst. apply E_all. assumption. Qed.

Lemma Mac_Fail : forall g z m l r, z = 7 + g*3 -> m = S g ->
  l << 1 <* [0]^^z {{A}}> 1 >> [1]^^m *> 0 >> r -->*
  l << 1 << 0 <* [0;1;1;1]^^g <* [1]^^3 <* [0]^^4 {{A}}> 1 >> 0 >> r.
Proof. intros. subst. apply FailChain. Qed.

Lemma Mac_Climb : forall k i x x' m m' n l r,
  x = x' + k*3 -> m = 2 + i*3 -> m' = m + k*3 -> i + k <= n ->
  l <* [0]^^x {{A}}> 0 >> [1]^^m *> 0 >> [1]^^n *> 0 >> r -->*
  l <* [0]^^x' {{A}}> 0 >> [1]^^m' *> 0 >> [1]^^n *> 0 >> r.
Proof.
  intros. subst.
  replace ([0]^^(x' + k*3) *> l) with ([0]^^(k*3) *> [0]^^x' *> l).
  2:{ rewrite lpow_app. f_equal. f_equal. lia. }
  follow (Climbs k i ([0]^^x' *> l) r n ltac:(lia)). finish.
Qed.

Lemma Mac_ML : forall g m m' l r, m' = m + g*3 -> 1 <= m ->
  l <* [0;1;1;1]^^g <* [1]^^m {{A}}> 1 >> r -->*
  l <* [1]^^m' {{A}}> 1 >> [1]^^g *> r.
Proof.
  intros. subst. destruct m as [| m]; [lia |]. apply MLs.
Qed.

(** Apply a macro lemma whose numeric arguments are given explicitly; its
    arithmetic side conditions are discharged by [lia]. *)
Ltac mac H := eapply evstep_trans; [ eapply H; lia | ].

(** Same as [lhs], after unfolding the blank right end once
    ([const 0 = 0 >> const 0]); used when the lemma needs an explicit
    0 taken from the blank part of the tape. *)
Ltac lhs0 c := rewrite const_unfold at 1; lhs c.

Lemma Fail1 : forall c l,
  l <* [0]^^4 {{A}}> 1 >> 0 >> [1]^^(S (S c)) *> const 0 -->*
  l << 0 << 1 << 1 << 1 << 0 << 1 << 1 << 1 <* [0]^^(S c) {{A}}> 0 >> const 0.
Proof.
  intros c l. execute. follow sweepF. execute.
Qed.

Lemma A4 : forall b l r,
  l <* [0]^^3 {{A}}> 0 >> [1]^^4 *> 0 >> [1]^^(S (S b)) *> 0 >> r -->*
  l {{A}}> 0 >> [1]^^8 *> 0 >> [1]^^(S b) *> 0 >> r.
Proof.
  intros b l r. execute.
Qed.

Lemma GenStart : forall b c l, 1 <= b ->
  l {{A}}> 0 >> [1]^^(2 + b*3) *> 0 >> [1]^^b *> 0 >> [1]^^(S (S c)) *> const 0 -->*
  l <* [0;1;1;1]^^(S b) <* [1]^^3 <* [0]^^(S c) {{A}}> 0 >> const 0.
Proof.
  intros b c l Hb.
  destruct b as [| b]; [lia |].
  execute. follow sweepF. step.
  destruct b as [| g].
  - follow Fail1. finish.
  - merge. follow (FailChain g (1 >> 1 >> l) ([1]^^(S (S c)) *> const 0)).
    follow Fail1.
    apply evstep_refl'.
    change (0 >> 1 >> 1 >> 1 >> l) with ([0;1;1;1] *> l).
    rewrite lpow_shift_str. reflexivity.
Qed.

Lemma H : forall g i B l r, i + 1 <= B ->
  l <* [0]^^3 <* [0;1;1;1]^^(S g) <* [1]^^3 {{A}}> 0 >> [1]^^(2 + i*3) *> 0 >> [1]^^B *> 0 >> r -->*
  l {{A}}> 0 >> [1]^^(11 + i*3 + g*3) *> 0 >> [1]^^(S g + B) *> 0 >> r.
Proof.
  intros g i B l r HB.
  destruct B as [| B]; [lia |].
  execute. follow sweepF. step.
  follow (E_all i (1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> [0;1;1;1]^^g *> 0 >> 0 >> 0 >> l)
            r B ltac:(lia)).
  step. follow sweepC. execute. follow sweepD. execute.
  lhs (l <* [0]^^3 <* [0;1;1;1]^^g <* [1]^^(9 + i*3) {{A}}> 1 >> 1 >> 1 >> [1]^^B *> 0 >> r).
  follow (MLs g (8 + i*3) ([0]^^3 *> l) (1 >> 1 >> [1]^^B *> 0 >> r)).
  execute. follow sweepC. follow sweepC. do 2 step. fin2.
Qed.

(* The generator below is not trusted: its instructions are replayed using
   [step] and the proved macro lemmas above.  No computed boolean is asserted
   to imply a machine transition without constructing that transition proof. *)
Local Open Scope bool_scope.
Definition maff := (Z * Z)%type.
Definition mak (n : Z) : maff := (n, 0%Z).
Definition maadd (a b : maff) : maff := ((fst a + fst b)%Z, (snd a + snd b)%Z).
Definition masub (a b : maff) : maff := ((fst a - fst b)%Z, (snd a - snd b)%Z).
Definition mamul (n : Z) (a : maff) : maff := ((n * fst a)%Z, (n * snd a)%Z).
Definition madiv3 (a : maff) : maff := ((fst a / 3)%Z, (snd a / 3)%Z).
Definition maeq (a b : maff) := Z.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
Definition mage (a b : maff) := Z.leb (fst b) (fst a) && Z.leb (snd b) (snd a).
Definition mapos (a : maff) := mage a (mak 1).
Definition mamod3 (a : maff) (r : Z) := Z.eqb (fst a mod 3) r && Z.eqb (snd a mod 3) 0.

Inductive mtoken := mZ | mO | mG.
Definition mteq a b := match a,b with mZ,mZ | mO,mO | mG,mG => true | _,_ => false end.
Definition mrun := (mtoken * option maff)%type.
Definition mrn t n : mrun := (t, Some n).
Definition minf : mrun := (mZ, None).
Definition mplus (a b : option maff) :=
  match a,b with Some x,Some y => Some (maadd x y) | _,_ => None end.
Definition mput (r : mrun) (rs : list mrun) : list mrun :=
  if match snd r with Some n => maeq n (mak 0) | None => false end then rs else
  match rs with
  | (t,n)::xs => if mteq (fst r) t then (t,mplus (snd r) n)::xs else r::rs
  | [] => [r]
  end.
Fixpoint mnorm (rs : list mrun) : list mrun :=
  match rs with [] => [] | r::xs => mput r (mnorm xs) end.
Fixpoint munroll (near_zero : bool) (rs : list mrun) : option (bool * list mrun) :=
  match rs with
  | [] => Some (false, [])
  | (mG,Some n)::xs =>
      if near_zero then
        if mapos n then Some (true, mrn mZ (mak 1)::mrn mO (mak 3)::mrn mG (masub n (mak 1))::xs)
        else None
      else match munroll false xs with Some (b,ys) => Some (b,(mG,Some n)::ys) | None => None end
  | (t,n)::xs =>
      match munroll (mteq t mZ) xs with Some (b,ys) => Some (b,(t,n)::ys) | None => None end
  end.
Fixpoint mnormL (fuel : nat) (rs : list mrun) : option (list mrun) :=
  match fuel with
  | O => None
  | S f => match munroll true (mnorm rs) with
    | Some (true,rs') => mnormL f rs'
    | Some (false,rs') => Some rs'
    | None => None
    end
  end.
Definition mpositive (rs : list mrun) :=
  forallb (fun r => match snd r with None => true | Some n => mapos n end) rs.
Record mcfg := MC { mlefts : list mrun; mhead : bool; mrights : list mrun;
                    mstate : state; mpos : maff }.
Definition mnormal c : option mcfg :=
  match mnormL 100 (mlefts c) with
  | None => None
  | Some l => let r := mnorm (mrights c) in
      if mpositive l && mpositive r then Some (MC l (mhead c) r (mstate c) (mpos c)) else None
  end.
Definition mbool t := match t with mO => true | _ => false end.
Definition mtok (b : bool) := if b then mO else mZ.
Definition msym (b : bool) : sym := if b then S1 else S0.
Definition mbsym s := match s with S0 => false | S1 => true end.
Definition mpop (right_side : bool) (rs : list mrun) : option (bool * list mrun) :=
  match rs with
  | (t,None)::_ => Some (mbool t,rs)
  | (mG,Some n)::xs =>
      if right_side && mapos n then
        Some (true,mrn mO (mak 2)::mrn mZ (mak 1)::mput (mrn mG (masub n (mak 1))) xs)
      else None
  | (t,Some n)::xs => if mapos n then Some (mbool t,mput (mrn t (masub n (mak 1))) xs) else None
  | [] => None
  end.
Definition mpush t n rs := mput (mrn t n) rs.

Inductive mside := MV | MB | MS (s : sym) (r : mside)
  | MP (w : list sym) (n : maff) (r : mside).
Definition mword (right_side : bool) t : list sym :=
  match t with mZ => [S0] | mO => [S1]
  | mG => if right_side then [S1;S1;S1;S0] else [S0;S1;S1;S1] end.
Definition mlength (r : mrun) : maff :=
  match snd r with None => mak 0 | Some n => mamul (if mteq (fst r) mG then 4 else 1) n end.
Fixpoint mlengths rs := match rs with [] => mak 0 | x::xs => maadd (mlength x) (mlengths xs) end.
Fixpoint mleftform (rs : list mrun) (base : mside) : mside :=
  match rs with
  | [] => base
  | (_,None)::_ => base
  | (t,Some n)::xs => MP (mword false t) n (mleftform xs base)
  end.
Definition mlform K p rs :=
  mleftform rs (MP [S0] (masub (maadd p (mak K)) (mlengths rs)) MV).
Fixpoint mrform (rs : list mrun) : mside :=
  match rs with
  | [] => MB
  | (_,None)::_ => MB
  | (t,Some n)::xs => MP (mword true t) n (mrform xs)
  end.
Inductive mform := MFL (l : mside) (q : state) (r : mside)
                 | MFR (l : mside) (q : state) (r : mside).
Definition mcform K c := MFR (mlform K (mpos c) (mlefts c)) (mstate c)
                              (MS (msym (mhead c)) (mrform (mrights c))).
Inductive mop := MRaw | MSC (e : maff) | MSD (e : maff) | MSF (e : maff)
  | ME (j z m : maff) | MF (g z m : maff)
  | MCl (k i x xp m mm n : maff) | MML (g m mm : maff).
Definition mevent := (mop * mform * mcfg)%type.
Definition memit op form c : option mevent :=
  match mnormal c with Some c' => Some (op,form,c') | None => None end.
Definition mraw K c : option mevent :=
  match tm (mstate c,msym (mhead c)) with
  | None => None
  | Some (s,L,q) => match mpop false (mlefts c) with
      | Some (h,l) => memit MRaw (mcform K c)
          (MC l h (mpush (mtok (mbsym s)) (mak 1) (mrights c)) q (masub (mpos c) (mak 1)))
      | None => None end
  | Some (s,R,q) => match mpop true (mrights c) with
      | Some (h,r) => memit MRaw (mcform K c)
          (MC (mpush (mtok (mbsym s)) (mak 1) (mlefts c)) h r q (maadd (mpos c) (mak 1)))
      | None => None end
  end.
Definition mdrop0 (rs : list mrun) : list mrun :=
  match rs with (t,Some n)::xs => mput (mrn t (masub n (mak 1))) xs | _ => rs end.
Definition mrightones rs :=
  match rs with (mO,Some n)::xs => (n,xs) | _ => (mak 0,rs) end.

Definition msweeps K c : option mevent :=
  if mhead c then
  match mstate c, mlefts c, mrights c with
  | C,(mO,Some n)::ls,rs =>
      let e := maadd n (mak 1) in
      let form := MFL (MP [S1] e (mlform K (masub (mpos c) n) ls)) C (mrform rs) in
      match mpop false ls with
      | Some (h,l) => memit (MSC e) form
          (MC l h (mpush mO e rs) C (masub (mpos c) e))
      | None => None end
  | D,ls,(mO,Some n)::rs =>
      let e := maadd n (mak 1) in
      let form := MFR (mlform K (mpos c) ls) D (MP [S1] e (mrform rs)) in
      match mpop true rs with
      | Some (h,r) => memit (MSD e) form (MC (mpush mO e ls) h r D (maadd (mpos c) e))
      | None => None end
  | F,ls,(mO,Some n)::rs =>
      let e := maadd n (mak 1) in
      let form := MFR (mlform K (mpos c) ls) F (MP [S1] e (mrform rs)) in
      match mpop true rs with
      | Some (h,r) => memit (MSF e) form (MC (mpush mZ e ls) h r F (maadd (mpos c) e))
      | None => None end
  | _,_,_ => None
  end else None.

Definition mefail K c : option mevent :=
  match mstate c,mhead c,mlefts c with
  | A,true,(mZ,Some z)::(mO,Some w)::ls =>
    if mage z (mak 4) && mamod3 z 1 then
      let j := madiv3 (masub z (mak 1)) in
      let '(m,rs) := mrightones (mrights c) in
      match rs with
      | (mZ,_)::_ =>
        let n := maadd m (mak 1) in
        let lp := mlform K (masub (masub (mpos c) z) w) ls in
        let form := MFR (MP [S0] z (MS S1 (MP [S1] (masub w (mak 1)) lp))) A
                        (MS S1 (MP [S1] m (MS S0 (mrform (mdrop0 rs))))) in
        if mage n (maadd j (mak 1)) then
          match mpop false (mrn mO z::mrn mO w::ls) with
          | Some (h,l) => memit (ME j z m) form
              (MC l h (mpush mO (mak 1) (mrights c)) A (masub (mpos c) (mak 1)))
          | None => None end
        else if maeq n j && negb (Z.eqb (snd j) 0) && mage j (mak 2) then
          let g := masub j (mak 2) in
          memit (MF g z m) form
             (MC (mrn mZ (mak 4)::mrn mO (mak 3)::mrn mG g::mrn mZ (mak 1)::mrn mO w::ls)
                 true rs A (maadd (mpos c) m))
        else None
      | _ => None
      end
    else None
  | _,_,_ => None
  end.

Definition mclimb K c : option mevent :=
  match mstate c,mhead c,mrights c with
  | A,false,(mO,Some m)::(mZ,Some one)::(mO,Some n)::(mZ,z)::rest =>
    let rs := (mZ,z)::rest in
    if maeq one (mak 1) && mage m (mak 2) && mamod3 m 2 then
      let i := madiv3 (masub m (mak 2)) in
      let kb := masub n i in
      let '(k,x,ls,infinite) :=
        match mlefts c with
        | (mZ,Some x)::ls =>
          let kx := madiv3 (masub x (mak (fst x mod 3))) in
          ((if mage kx kb then kb else kx),x,ls,false)
        | [(mZ,None)] => (kb,maadd (mpos c) (mak K),[],true)
        | _ => (mak 0,mak 0,mlefts c,false)
        end in
      if mapos k && mage x (mamul 3 k) then
        let xp := masub x (mamul 3 k) in
        let mm := maadd m (mamul 3 k) in
        let form := MFR (MP [S0] x (if infinite then MV else mlform K (masub (mpos c) x) ls)) A
                      (MS S0 (MP [S1] m (MS S0 (MP [S1] n (MS S0 (mrform (mdrop0 rs))))))) in
        memit (MCl k i x xp m mm n) form
           (MC (if infinite then [minf] else mrn mZ xp::ls) false
               (mrn mO mm::mrn mZ (mak 1)::mrn mO n::rs) A (masub (mpos c) (mamul 3 k)))
      else None
    else None
  | _,_,_ => None
  end.

Definition mml K c : option mevent :=
  match mstate c,mhead c,mlefts c with
  | A,true,(mO,Some m)::(mG,Some g)::ls =>
    if mapos g then
      let mm := maadd m (mamul 3 g) in
      let form := MFR (MP [S1] m (MP [S0;S1;S1;S1] g
                          (mlform K (masub (masub (mpos c) m) (mamul 4 g)) ls))) A
                      (MS S1 (mrform (mrights c))) in
      memit (MML g m mm) form
         (MC (mrn mO mm::ls) true (mpush mO g (mrights c)) A (masub (mpos c) g))
    else None
  | _,_,_ => None
  end.
Definition mnext K c : option mevent :=
  match msweeps K c with Some e => Some e | None =>
  match mefail K c with Some e => Some e | None =>
  match mclimb K c with Some e => Some e | None =>
  match mml K c with Some e => Some e | None => mraw K c end end end end.

Definition mbase := MC [minf] false [minf] A (mak 0).
Definition mtail := MC [minf] false
   [mrn mO (11%Z,3%Z); mrn mZ (mak 1); mrn mO (3%Z,1%Z); mrn mZ (mak 1);
    mrn mO (mak 67); minf] A (mak 0).
Definition mlandmark a b d c :=
  match mstate c,mhead c,mlefts c,mrights c with
  | A,false,[(mZ,None)],[(mO,Some aa);(mZ,Some o1);(mO,Some bb);(mZ,Some o2);(mO,Some dd);(mZ,None)] =>
      maeq aa a && maeq bb b && maeq dd d && maeq o1 (mak 1) && maeq o2 (mak 1)
  | _,_,_,_ => false
  end.
Fixpoint mrun_steps fuel K c :=
  match fuel with
  | O => Some c
  | S f => match mnext K c with Some (_,_,c') => mrun_steps f K c' | None => None end
  end.

Definition madvance fuel K c :=
  match mrun_steps fuel K c with Some c' => c' | None => c end.
Definition mnat (u : nat) (a : maff) : nat :=
  let c := Z.to_nat (fst a) in let k := Z.to_nat (snd a) in
  match k with
  | O => c
  | S O => match c with O => u | _ => c + u end
  | _ => match c with O => u*k | _ => c + u*k end
  end.
Fixpoint mden_side (l : side) (u : nat) (s : mside) : side :=
  match s with
  | MV => l | MB => const S0 | MS a r => a >> mden_side l u r
  | MP w n r => w^^(mnat u n) *> mden_side l u r
  end.
Definition mden_form l u f : Q * tape :=
  match f with
  | MFL a q b => mden_side l u a <{{q}} mden_side l u b
  | MFR a q b => mden_side l u a {{q}}> mden_side l u b
  end.
Definition mden K c l u := mden_form l u (mcform K c).

(* Kernel-checked instruction interpreter.  The generated state is used only
   to propose [change] expressions and applications of proved lemmas. *)
Ltac ma_term u a :=
  lazymatch a with (?c,?k) =>
    let ok := eval vm_compute in (mage a (mak 0)) in
    lazymatch ok with
    | true =>
      let cn := eval vm_compute in (Z.to_nat c) in
      let kn := eval vm_compute in (Z.to_nat k) in
      lazymatch kn with
      | O => constr:(cn)
      | S O => lazymatch cn with O => constr:(u) | _ => constr:((cn + u)%nat) end
      | _ => lazymatch cn with O => constr:((u * kn)%nat) | _ => constr:((cn + u * kn)%nat) end
      end
    | _ => fail 1 "negative affine length" a
    end
  end.
Ltac ms_term l u s :=
  lazymatch s with
  | MV => constr:(l)
  | MB => constr:(const S0)
  | MS ?a ?s' => let r := ms_term l u s' in constr:(a >> r)
  | MP ?w ?a ?s' =>
      let n := ma_term u a in let r := ms_term l u s' in
      lazymatch n with O => constr:(r) | _ => constr:(w^^n *> r) end
  end.
Ltac mf_term l u f :=
  lazymatch f with
  | MFL ?s1 ?q ?s2 => let a := ms_term l u s1 in let b := ms_term l u s2 in constr:(a <{{q}} b)
  | MFR ?s1 ?q ?s2 => let a := ms_term l u s1 in let b := ms_term l u s2 in constr:(a {{q}}> b)
  end.
Ltac mapply_op op u :=
  lazymatch op with
  | MSC ?a => let e := ma_term u a in mac (sweepC e)
  | MSD ?a => let e := ma_term u a in mac (sweepD e)
  | MSF ?a => let e := ma_term u a in mac (sweepF e)
  | ME ?a ?b ?c => let j := ma_term u a in let z := ma_term u b in let m := ma_term u c in
      mac (Mac_E j z m)
  | MF ?a ?b ?c => let g := ma_term u a in let z := ma_term u b in let m := ma_term u c in
      mac (Mac_Fail g z m)
  | MCl ?a ?b ?c ?d ?e ?f ?g =>
      let k := ma_term u a in let i := ma_term u b in let x := ma_term u c in
      let xp := ma_term u d in let m := ma_term u e in let mm := ma_term u f in let n := ma_term u g in
      mac (Mac_Climb k i x xp m mm n)
  | MML ?a ?b ?c => let g := ma_term u a in let m := ma_term u b in let mm := ma_term u c in
      mac (Mac_ML g m mm)
  end.
Ltac mreplay_chunk fuel K cfg l u :=
  lazymatch fuel with
  | O => idtac
  | S ?f =>
    let event := eval vm_compute in (mnext K cfg) in
    lazymatch event with
    | Some (MRaw,_,?nc) => step; mreplay_chunk f K nc l u
    | Some (?op,?form,?nc) =>
      let lhs' := mf_term l u form in
      first [lhs lhs' | lhs0 lhs']; mapply_op op u;
      mreplay_chunk f K nc l u
    | None => fail 1 "M1 generator stuck" cfg
    end
  end.
Ltac mbridge fuel K source :=
  idtac "M1 bridge:" source;
  let u := fresh "u" in let l := fresh "l" in intros u l;
  let cfg := eval vm_compute in source in
  let form := eval vm_compute in (mcform K cfg) in
  let lhs' := mf_term l u form in lhs lhs';
  mreplay_chunk fuel K cfg l u; fin.

Definition base0 := mbase.
Definition base1 := Eval vm_compute in madvance 180 252%Z base0.
Definition base2 := Eval vm_compute in madvance 180 252%Z base1.
Definition base3 := Eval vm_compute in madvance 180 252%Z base2.
Definition base4 := Eval vm_compute in madvance 180 252%Z base3.
Definition base5 := Eval vm_compute in madvance 180 252%Z base4.
Definition base6 := Eval vm_compute in madvance 180 252%Z base5.
Definition base7 := Eval vm_compute in madvance 180 252%Z base6.
Definition base8 := Eval vm_compute in madvance 180 252%Z base7.
Definition base9 := Eval vm_compute in madvance 180 252%Z base8.
Definition base10 := Eval vm_compute in madvance 180 252%Z base9.
Definition base11 := Eval vm_compute in madvance 180 252%Z base10.
Definition base12 := Eval vm_compute in madvance 180 252%Z base11.
Definition base13 := Eval vm_compute in madvance 180 252%Z base12.
Definition base14 := Eval vm_compute in madvance 180 252%Z base13.
Definition base15 := Eval vm_compute in madvance 180 252%Z base14.
Definition base16 := Eval vm_compute in madvance 180 252%Z base15.
Definition base17 := Eval vm_compute in madvance 180 252%Z base16.
Definition base18 := Eval vm_compute in madvance 180 252%Z base17.
Definition base19 := Eval vm_compute in madvance 180 252%Z base18.
Definition base20 := Eval vm_compute in madvance 180 252%Z base19.
Definition base21 := Eval vm_compute in madvance 180 252%Z base20.
Definition base22 := Eval vm_compute in madvance 180 252%Z base21.
Definition base23 := Eval vm_compute in madvance 180 252%Z base22.
Definition base24 := Eval vm_compute in madvance 180 252%Z base23.
Definition base25 := Eval vm_compute in madvance 180 252%Z base24.
Definition base26 := Eval vm_compute in madvance 180 252%Z base25.
Definition base27 := Eval vm_compute in madvance 180 252%Z base26.
Definition base28 := Eval vm_compute in madvance 180 252%Z base27.
Definition base29 := Eval vm_compute in madvance 180 252%Z base28.
Definition base30 := Eval vm_compute in madvance 37 252%Z base29.
Lemma base_part1 : forall u l, mden 252%Z base0 l u -->* mden 252%Z base1 l u.
Proof. mbridge 180 252%Z base0. Qed.
Lemma base_part2 : forall u l, mden 252%Z base1 l u -->* mden 252%Z base2 l u.
Proof. mbridge 180 252%Z base1. Qed.
Lemma base_part3 : forall u l, mden 252%Z base2 l u -->* mden 252%Z base3 l u.
Proof. mbridge 180 252%Z base2. Qed.
Lemma base_part4 : forall u l, mden 252%Z base3 l u -->* mden 252%Z base4 l u.
Proof. mbridge 180 252%Z base3. Qed.
Lemma base_part5 : forall u l, mden 252%Z base4 l u -->* mden 252%Z base5 l u.
Proof. mbridge 180 252%Z base4. Qed.
Lemma base_part6 : forall u l, mden 252%Z base5 l u -->* mden 252%Z base6 l u.
Proof. mbridge 180 252%Z base5. Qed.
Lemma base_part7 : forall u l, mden 252%Z base6 l u -->* mden 252%Z base7 l u.
Proof. mbridge 180 252%Z base6. Qed.
Lemma base_part8 : forall u l, mden 252%Z base7 l u -->* mden 252%Z base8 l u.
Proof. mbridge 180 252%Z base7. Qed.
Lemma base_part9 : forall u l, mden 252%Z base8 l u -->* mden 252%Z base9 l u.
Proof. mbridge 180 252%Z base8. Qed.
Lemma base_part10 : forall u l, mden 252%Z base9 l u -->* mden 252%Z base10 l u.
Proof. mbridge 180 252%Z base9. Qed.
Lemma base_part11 : forall u l, mden 252%Z base10 l u -->* mden 252%Z base11 l u.
Proof. mbridge 180 252%Z base10. Qed.
Lemma base_part12 : forall u l, mden 252%Z base11 l u -->* mden 252%Z base12 l u.
Proof. mbridge 180 252%Z base11. Qed.
Lemma base_part13 : forall u l, mden 252%Z base12 l u -->* mden 252%Z base13 l u.
Proof. mbridge 180 252%Z base12. Qed.
Lemma base_part14 : forall u l, mden 252%Z base13 l u -->* mden 252%Z base14 l u.
Proof. mbridge 180 252%Z base13. Qed.
Lemma base_part15 : forall u l, mden 252%Z base14 l u -->* mden 252%Z base15 l u.
Proof. mbridge 180 252%Z base14. Qed.
Lemma base_part16 : forall u l, mden 252%Z base15 l u -->* mden 252%Z base16 l u.
Proof. mbridge 180 252%Z base15. Qed.
Lemma base_part17 : forall u l, mden 252%Z base16 l u -->* mden 252%Z base17 l u.
Proof. mbridge 180 252%Z base16. Qed.
Lemma base_part18 : forall u l, mden 252%Z base17 l u -->* mden 252%Z base18 l u.
Proof. mbridge 180 252%Z base17. Qed.
Lemma base_part19 : forall u l, mden 252%Z base18 l u -->* mden 252%Z base19 l u.
Proof. mbridge 180 252%Z base18. Qed.
Lemma base_part20 : forall u l, mden 252%Z base19 l u -->* mden 252%Z base20 l u.
Proof. mbridge 180 252%Z base19. Qed.
Lemma base_part21 : forall u l, mden 252%Z base20 l u -->* mden 252%Z base21 l u.
Proof. mbridge 180 252%Z base20. Qed.
Lemma base_part22 : forall u l, mden 252%Z base21 l u -->* mden 252%Z base22 l u.
Proof. mbridge 180 252%Z base21. Qed.
Lemma base_part23 : forall u l, mden 252%Z base22 l u -->* mden 252%Z base23 l u.
Proof. mbridge 180 252%Z base22. Qed.
Lemma base_part24 : forall u l, mden 252%Z base23 l u -->* mden 252%Z base24 l u.
Proof. mbridge 180 252%Z base23. Qed.
Lemma base_part25 : forall u l, mden 252%Z base24 l u -->* mden 252%Z base25 l u.
Proof. mbridge 180 252%Z base24. Qed.
Lemma base_part26 : forall u l, mden 252%Z base25 l u -->* mden 252%Z base26 l u.
Proof. mbridge 180 252%Z base25. Qed.
Lemma base_part27 : forall u l, mden 252%Z base26 l u -->* mden 252%Z base27 l u.
Proof. mbridge 180 252%Z base26. Qed.
Lemma base_part28 : forall u l, mden 252%Z base27 l u -->* mden 252%Z base28 l u.
Proof. mbridge 180 252%Z base27. Qed.
Lemma base_part29 : forall u l, mden 252%Z base28 l u -->* mden 252%Z base29 l u.
Proof. mbridge 180 252%Z base28. Qed.
Lemma base_part30 : forall u l, mden 252%Z base29 l u -->* mden 252%Z base30 l u.
Proof. mbridge 37 252%Z base29. Qed.
Lemma base_gen : forall (u : nat) l,
  l <* [0]^^252 {{A}}> 0 >> const 0 -->*
  l {{A}}> 0 >> [1]^^8 *> 0 >> [1]^^203 *> 0 >> [1]^^67 *> const 0.
Proof. intros u l.
  follow (base_part1 u l).
  follow (base_part2 u l).
  follow (base_part3 u l).
  follow (base_part4 u l).
  follow (base_part5 u l).
  follow (base_part6 u l).
  follow (base_part7 u l).
  follow (base_part8 u l).
  follow (base_part9 u l).
  follow (base_part10 u l).
  follow (base_part11 u l).
  follow (base_part12 u l).
  follow (base_part13 u l).
  follow (base_part14 u l).
  follow (base_part15 u l).
  follow (base_part16 u l).
  follow (base_part17 u l).
  follow (base_part18 u l).
  follow (base_part19 u l).
  follow (base_part20 u l).
  follow (base_part21 u l).
  follow (base_part22 u l).
  follow (base_part23 u l).
  follow (base_part24 u l).
  follow (base_part25 u l).
  follow (base_part26 u l).
  follow (base_part27 u l).
  follow (base_part28 u l).
  follow (base_part29 u l).
  follow (base_part30 u l).
  fin. Qed.
Definition tail0 := mtail.
Definition tail1 := Eval vm_compute in madvance 180 180%Z tail0.
Definition tail2 := Eval vm_compute in madvance 180 180%Z tail1.
Definition tail3 := Eval vm_compute in madvance 180 180%Z tail2.
Definition tail4 := Eval vm_compute in madvance 180 180%Z tail3.
Definition tail5 := Eval vm_compute in madvance 180 180%Z tail4.
Definition tail6 := Eval vm_compute in madvance 180 180%Z tail5.
Definition tail7 := Eval vm_compute in madvance 180 180%Z tail6.
Definition tail8 := Eval vm_compute in madvance 25 180%Z tail7.
Lemma tail_part1 : forall u l, mden 180%Z tail0 l u -->* mden 180%Z tail1 l u.
Proof. mbridge 180 180%Z tail0. Qed.
Lemma tail_part2 : forall u l, mden 180%Z tail1 l u -->* mden 180%Z tail2 l u.
Proof. mbridge 180 180%Z tail1. Qed.
Lemma tail_part3 : forall u l, mden 180%Z tail2 l u -->* mden 180%Z tail3 l u.
Proof. mbridge 180 180%Z tail2. Qed.
Lemma tail_part4 : forall u l, mden 180%Z tail3 l u -->* mden 180%Z tail4 l u.
Proof. mbridge 180 180%Z tail3. Qed.
Lemma tail_part5 : forall u l, mden 180%Z tail4 l u -->* mden 180%Z tail5 l u.
Proof. mbridge 180 180%Z tail4. Qed.
Lemma tail_part6 : forall u l, mden 180%Z tail5 l u -->* mden 180%Z tail6 l u.
Proof. mbridge 180 180%Z tail5. Qed.
Lemma tail_part7 : forall u l, mden 180%Z tail6 l u -->* mden 180%Z tail7 l u.
Proof. mbridge 180 180%Z tail6. Qed.
Lemma tail_part8 : forall u l, mden 180%Z tail7 l u -->* mden 180%Z tail8 l u.
Proof. mbridge 25 180%Z tail7. Qed.
Lemma tail_gen : forall (u : nat) l,
  l <* [0]^^180 {{A}}> 0 >> [1]^^(11 + u*3) *> 0 >> [1]^^(3 + u) *> 0 >> [1]^^67 *> const 0 -->*
  l {{A}}> 0 >> [1]^^4 *> 0 >> [1]^^(216 + u*3) *> 0 >> [1]^^(71 + u) *> const 0.
Proof. intros u l.
  follow (tail_part1 u l).
  follow (tail_part2 u l).
  follow (tail_part3 u l).
  follow (tail_part4 u l).
  follow (tail_part5 u l).
  follow (tail_part6 u l).
  follow (tail_part7 u l).
  follow (tail_part8 u l).
  fin. Qed.

Fixpoint N n := match n with O => 68 | S n => 4 * N n end.
Fixpoint q n := match n with O => 9 | S n => 2 * q n + 1 end.
Definition Rr n := 3 * q n + 1.
Definition Dz n := 4 * N n + 8 - Rr n.

(** sum of N over the stages, and the left room the stage chain needs *)
Fixpoint SN n := match n with O => O | S n => N n + SN n end.
Fixpoint ZC n := match n with O => O | S n => ZC n + 3 * (3 * N n - q n - 2) + 3 end.
Definition Zs n := 3 * (3 * N n - 3) + ZC n + 180 + 3.

Lemma inv : forall n,
  68 <= N n /\ 9 <= q n /\ 3 * q n + 1 <= N n /\
  3 * SN n + 68 = N n /\ ZC n + 3 * q n + 177 = 3 * N n.
Proof.
  induction n as [| n IH]; simpl; lia.
Qed.

Lemma Dz_S : forall n, Dz (S n) = Dz n + Zs n.
Proof.
  intros n. pose proof (inv n). unfold Dz, Zs, Rr. simpl. lia.
Qed.

(** Top-level landmark [a, b, c] with left context [l]. *)
Definition lm0 (l : side) a b c : Q * tape :=
  l {{A}}> 0 >> [1]^^a *> 0 >> [1]^^b *> 0 >> [1]^^c *> const 0.

(** Traj(n+2), in the "blank run with arbitrary left context" form:
    the run never reads left of [Dz n] cells left of its start. *)
Definition Traj n := forall l,
  l <* [0]^^(Dz n) {{A}}> 0 >> const 0 -->* lm0 l 8 (3 * N n - 1) (N n - 1).

Lemma Traj0 : Traj 0.
Proof. intros l. apply (base_gen O l). Qed.

Lemma Tail : forall b l, 3 <= b ->
  l <* [0]^^180 {{A}}> 0 >> [1]^^(2 + b*3) *> 0 >> [1]^^b *> 0 >> [1]^^67 *> const 0 -->*
  lm0 l 4 (207 + b*3) (68 + b).
Proof.
  intros b l Hb. replace b with (3 + (b - 3)) by lia.
  generalize (b - 3) as u. intros u.
  replace (2 + (3 + u)*3) with (11 + u*3) by lia.
  replace (207 + (3 + u)*3) with (216 + u*3) by lia.
  replace (68 + (3 + u)) with (71 + u) by lia.
  apply tail_gen.
Qed.

Lemma A4p : forall b l r,
  l <* [0]^^3 {{A}}> 0 >> [1]^^4 *> 0 >> [1]^^(S (S b)) *> 0 >> r -->+
  l {{A}}> 0 >> [1]^^8 *> 0 >> [1]^^(S b) *> 0 >> r.
Proof.
  intros b l r. start_progress.
Qed.


(** ** Stage lemma S(j), j = m + 3: uses Traj(j-1) = Traj m on the region right
    of the wall that GenStart builds. *)
Lemma Stage : forall m, Traj m -> forall b l, 1 <= b ->
  l <* [0]^^3 {{A}}> 0 >> [1]^^(2 + b*3) *> 0 >> [1]^^b *> 0 >> [1]^^(N (S m) - 1) *> const 0 -->*
  lm0 l (8 + b*3 + q m * 3) (b + 3 * N m) (N m - 1).
Proof.
  intros m HT b l Hb. pose proof (inv m) as Hi.
  replace (N (S m) - 1) with (S (S (4 * N m - 3))) by (simpl; lia).
  follow (GenStart b (4 * N m - 3) ([0]^^3 *> l) Hb).
  (* split the zeros right of the wall: x = R - 10 next to the wall, Dz m next to the head *)
  replace ([0]^^(S (4 * N m - 3)) *> [1]^^3 *> [0;1;1;1]^^(S b) *> [0]^^3 *> l)
    with ([0]^^(Dz m) *> [0]^^((q m - 3)*3) *> [1]^^3 *> [0;1;1;1]^^(S b) *> [0]^^3 *> l).
  2:{ rewrite lpow_app. f_equal. f_equal. unfold Dz, Rr. lia. }
  (* the replay *)
  follow (HT ([0]^^((q m - 3)*3) *> [1]^^3 *> [0;1;1;1]^^(S b) *> [0]^^3 *> l)).
  unfold lm0.
  (* climb up to the wall *)
  follow (Climbs (q m - 3) 2 ([1]^^3 *> [0;1;1;1]^^(S b) *> [0]^^3 *> l)
            ([1]^^(N m - 1) *> const 0) (3 * N m - 1) ltac:(lia)).
  (* hit the wall *)
  follow (H b (q m - 1) (3 * N m - 1) l ([1]^^(N m - 1) *> const 0) ltac:(lia)).
  finish.
Qed.

(** ** The stage chain S(k), Climb, S(k-1), Climb, ..., S(3), Climb *)
Lemma Chain : forall n, (forall m, m < n -> Traj m) -> forall b l, 1 <= b ->
  l <* [0]^^(ZC n) {{A}}> 0 >> [1]^^(2 + b*3) *> 0 >> [1]^^b *> 0 >> [1]^^(N n - 1) *> const 0 -->*
  lm0 l (2 + (b + 3 * SN n)*3) (b + 3 * SN n) 67.
Proof.
  induction n as [| n IH]; intros HT b l Hb.
  - replace (b + 3 * SN 0) with b by (simpl; lia). unfold lm0. simpl ZC. simpl N. finish.
  - pose proof (inv n) as Hi.
    replace ([0]^^(ZC (S n)) *> l)
      with ([0]^^3 *> [0]^^((3 * N n - q n - 2)*3) *> [0]^^(ZC n) *> l).
    2:{ rewrite !lpow_app. f_equal. f_equal. simpl ZC. lia. }
    follow (Stage n (HT n ltac:(lia)) b ([0]^^((3 * N n - q n - 2)*3) *> [0]^^(ZC n) *> l) Hb).
    unfold lm0.
    follow (Climbs (3 * N n - q n - 2) (b + q n + 2) ([0]^^(ZC n) *> l)
              ([1]^^(N n - 1) *> const 0) (b + 3 * N n) ltac:(lia)).
    follow (IH (fun m Hm => HT m ltac:(lia)) (b + 3 * N n) l ltac:(lia)).
    unfold lm0. simpl SN. finish.
Qed.

(** ** One round: Traj(k) landmark -> Traj(k+1) landmark *)
Lemma Step : forall n, (forall m, m <= n -> Traj m) -> forall l,
  lm0 (l <* [0]^^(Zs n)) 8 (3 * N n - 1) (N n - 1) -->+
  lm0 l 8 (3 * N (S n) - 1) (N (S n) - 1).
Proof.
  intros n HT l. pose proof (inv n) as Hi.
  unfold Zs.
  replace ([0]^^(3 * (3 * N n - 3) + ZC n + 180 + 3) *> l)
    with ([0]^^((3 * N n - 3)*3) *> [0]^^(ZC n) *> [0]^^180 *> [0]^^3 *> l).
  2:{ rewrite !lpow_app. f_equal. f_equal. lia. }
  unfold lm0.
  follow (Climbs (3 * N n - 3) 2 ([0]^^(ZC n) *> [0]^^180 *> [0]^^3 *> l)
            ([1]^^(N n - 1) *> const 0) (3 * N n - 1) ltac:(lia)).
  follow (Chain n (fun m Hm => HT m ltac:(lia)) (3 * N n - 1)
            ([0]^^180 *> [0]^^3 *> l) ltac:(lia)).
  follow (Tail (3 * N n - 1 + 3 * SN n) ([0]^^3 *> l) ltac:(lia)).
  unfold lm0.
  eapply progress_evstep_trans.
  { apply (A4p (205 + (3 * N n - 1 + 3 * SN n)*3) l
                ([1]^^(68 + (3 * N n - 1 + 3 * SN n)) *> const 0)). }
  simpl N. finish.
Qed.

(** ** Traj(k) for all k, by strong induction *)
Lemma Traj_all : forall n, Traj n.
Proof.
  induction n as [n IH] using strong_induction.
  destruct n as [| n]. { apply Traj0. }
  intros l. rewrite Dz_S.
  rewrite <- lpow_app.
  follow (IH n ltac:(lia) ([0]^^(Zs n) *> l)).
  apply progress_evstep.
  apply (Step n (fun m Hm => IH m ltac:(lia)) l).
Qed.

Lemma const_zeros : forall k, [0]^^k *> const 0 = const 0.
Proof.
  induction k as [| k IH]; [reflexivity |].
  cbn [lpow app Str_app]. rewrite IH. symmetry. apply const_unfold.
Qed.

(** The landmarks of the actual blank-tape run. *)
Definition LM n : Q * tape := lm0 (const 0) 8 (3 * N n - 1) (N n - 1).

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (LM 0).
  { pose proof (Traj0 (const 0)) as H0.
    rewrite const_zeros in H0. exact H0. }
  apply progress_nonhalt_simple with (C := LM). intro n. exists (S n).
  pose proof (Step n (fun m _ => Traj_all m) (const 0)) as Hs.
  rewrite const_zeros in Hs. exact Hs.
Qed.

Print Assumptions nonhalt.

End TM1.
