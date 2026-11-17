(** * BB(6) Holdout 608:#302 / 797:#400: 1RB1LC_1LA0RD_1LA0LA_---1RE_1RB0RF_1RC0RA *)

From BusyCoq Require Import Individual62.
From Coq Require Import String Bool Lists.List Arith NArith PArith Lia.
Import ListNotations.

Definition tm : TM := TM_from_str "1RB1LC_1LA0RD_1LA0LA_---1RE_1RB0RF_1RC0RA"%string.

Module M302_Internal.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.

(** ** Section 1: Arithmetic Helpers, Macro Data Structures & Right-Wall Fuel Model *)

Lemma N_div_mod_2 (x : N) :
  x = 2 * (N.div x 2) + N.modulo x 2 /\ N.modulo x 2 < 2.
Proof.
  split; [apply N.div_mod | apply N.mod_upper_bound]; discriminate.
Qed.

Lemma N_div_mod_3 (x : N) :
  x = 3 * (N.div x 3) + N.modulo x 3 /\ N.modulo x 3 < 3.
Proof.
  split; [apply N.div_mod | apply N.mod_upper_bound]; discriminate.
Qed.

Inductive CTree : Type :=
| CLeaf (m : N)
| CNode (l r : CTree).

Inductive LSide : Type :=
| LNil
| LB0 (k : N) (tl : LSide)
| LB1 (k : N) (tl : LSide)
| LX (k : N) (tl : LSide)
| LY (k : N) (tl : LSide)
| LDL0 (k : N) (tl : LSide)
| LUL (k : N) (tl : LSide)
| LC (t : CTree) (tl : LSide).

Inductive RSide : Type :=
| RNil
| RWall
| RB0 (k : N) (tl : RSide)
| RO (k : N) (tl : RSide)
| RZ (k : N) (tl : RSide)
| RDR0 (k : N) (tl : RSide)
| RUR (k : N) (tl : RSide)
| RCR (t : CTree) (tl : RSide).

Inductive MState : Type :=
| ModeA (ls : LSide) (rs : RSide) (bnc : N)
| ModeB (ls : LSide) (rs : RSide) (bnc : N)
| MErr.

Definition mkMState (isA : bool) (ls : LSide) (rs : RSide) (bnc : N) : MState :=
  if isA then ModeA ls rs bnc else ModeB ls rs bnc.

Inductive RWallShape : Type :=
| RWEmpty
| RWO12
| RWO908
| RWO90Z (q : N).

Fixpoint fuelList (xs : list N) : N :=
  match xs with
  | [] => 0
  | m :: ms => 2 * m + 5 + fuelList ms
  end.

Definition fuelRWall (w : RWallShape) : N :=
  match w with
  | RWEmpty => 0
  | RWO12 => 4
  | RWO908 => 6
  | RWO90Z q => 2 * q + 8
  end.

Definition fuelRW (s : list N) (w : RWallShape) : N :=
  fuelList s + fuelRWall w.

Definition bounceRW (p : list N * RWallShape) : list N * RWallShape :=
  let '(s, w) := p in
  match w with
  | RWO908 => (0 :: s, RWEmpty)
  | RWO90Z q => ((q + 1) :: s, RWEmpty)
  | RWEmpty =>
    match s with
    | [] => ([], RWEmpty)
    | m0 :: s' =>
      if N.eqb m0 0 then (s', RWO12)
      else if N.eqb m0 1 then (s', RWO908)
      else (s', RWO90Z (m0 - 2))
    end
  | RWO12 =>
    match s with
    | [] => ([], RWO12)
    | m0 :: s' => (s', RWO90Z m0)
    end
  end.

Fixpoint bounceRWIterNat (n : nat) (p : list N * RWallShape) : list N * RWallShape :=
  match n with
  | O => p
  | S n' => bounceRWIterNat n' (bounceRW p)
  end.

Lemma fuelList_app (xs ys : list N) :
  fuelList (xs ++ ys) = fuelList xs + fuelList ys.
Proof.
  induction xs as [| m ms IH]; cbn [List.app fuelList]; [lia | rewrite IH; lia].
Qed.

Lemma fuelRW_bounceRW (s : list N) (w : RWallShape) :
  5 <= fuelRW s w ->
  fuelRW (fst (bounceRW (s, w))) (snd (bounceRW (s, w))) + 1 = fuelRW s w.
Proof.
  intro H; destruct w as [ | | | q].
  - destruct s as [| m0 s'].
    + unfold fuelRW in H; cbn [fuelList fuelRWall] in H; lia.
    + cbn [bounceRW].
      destruct (N.eqb m0 0) eqn:Hm0.
      * apply N.eqb_eq in Hm0; subst m0; unfold fuelRW; cbn [fst snd fuelList fuelRWall]; lia.
      * apply N.eqb_neq in Hm0.
        destruct (N.eqb m0 1) eqn:Hm1.
        -- apply N.eqb_eq in Hm1; subst m0; unfold fuelRW; cbn [fst snd fuelList fuelRWall]; lia.
        -- apply N.eqb_neq in Hm1; unfold fuelRW; cbn [fst snd fuelList fuelRWall]; lia.
  - destruct s as [| m0 s'].
    + unfold fuelRW in H; cbn [fuelList fuelRWall] in H; lia.
    + unfold fuelRW; cbn [bounceRW fst snd fuelList fuelRWall]; lia.
  - unfold fuelRW; cbn [bounceRW fst snd fuelList fuelRWall]; lia.
  - unfold fuelRW; cbn [bounceRW fst snd fuelList fuelRWall]; lia.
Qed.

Lemma bounceRWIterNat_add (a b : nat) :
  forall p : list N * RWallShape,
    bounceRWIterNat b (bounceRWIterNat a p) = bounceRWIterNat (a + b)%nat p.
Proof.
  induction a as [| a' IH]; intro p; cbn [Nat.add bounceRWIterNat]; [reflexivity | exact (IH (bounceRW p))].
Qed.

Lemma fuelRW_bounceRWIterNat (n : nat) :
  forall (s : list N) (w : RWallShape),
    N.of_nat n + 4 <= fuelRW s w ->
    fuelRW (fst (bounceRWIterNat n (s, w))) (snd (bounceRWIterNat n (s, w))) + N.of_nat n = fuelRW s w.
Proof.
  induction n as [| n' IH]; intros s w H.
  - cbn [bounceRWIterNat fst snd]; lia.
  - assert (H5 : 5 <= fuelRW s w) by lia.
    pose proof (fuelRW_bounceRW s w H5) as H1.
    destruct (bounceRW (s, w)) as [s' w'] eqn:Hb.
    cbn [fst snd] in H1.
    assert (Hn' : N.of_nat n' + 4 <= fuelRW s' w') by lia.
    pose proof (IH s' w' Hn') as H2.
    cbn [bounceRWIterNat]; rewrite Hb; lia.
Qed.

(** ** Section 2: Tape Encodings *)

Fixpoint rep0n (k : nat) (s : side) : side :=
  match k with O => s | S k' => S0 >> rep0n k' s end.

Fixpoint rep1n (k : nat) (s : side) : side :=
  match k with O => s | S k' => S1 >> rep1n k' s end.

Fixpoint repXn (k : nat) (s : side) : side :=
  match k with O => s | S k' => S1 >> S1 >> S0 >> repXn k' s end.

Fixpoint repYn (k : nat) (s : side) : side :=
  match k with O => s | S k' => S1 >> S0 >> S0 >> S1 >> S0 >> repYn k' s end.

Fixpoint repZn (k : nat) (s : side) : side :=
  match k with O => s | S k' => S1 >> S1 >> S1 >> S1 >> S1 >> S0 >> repZn k' s end.

Fixpoint repDL0n (k : nat) (s : side) : side :=
  match k with O => s | S k' => repYn 2 (repXn 3 (repDL0n k' s)) end.

Fixpoint repULn (k : nat) (s : side) : side :=
  match k with O => s | S k' => repYn 2 (repXn 7 (repULn k' s)) end.

Fixpoint repDR0n (k : nat) (s : side) : side :=
  match k with O => s | S k' => S1 >> S0 >> repZn 1 (rep1n 7 (S0 >> rep1n 3 (repDR0n k' s))) end.

Fixpoint repURn (k : nat) (s : side) : side :=
  match k with O => s | S k' => S1 >> S0 >> repZn 3 (rep1n 7 (S0 >> rep1n 3 (repURn k' s))) end.

Definition rep0 (k : N) (s : side) : side := rep0n (N.to_nat k) s.
Definition rep1 (k : N) (s : side) : side := rep1n (N.to_nat k) s.
Definition repX (k : N) (s : side) : side := repXn (N.to_nat k) s.
Definition repY (k : N) (s : side) : side := repYn (N.to_nat k) s.
Definition repZ (k : N) (s : side) : side := repZn (N.to_nat k) s.
Definition repDL0 (k : N) (s : side) : side := repDL0n (N.to_nat k) s.
Definition repUL (k : N) (s : side) : side := repULn (N.to_nat k) s.
Definition repDR0 (k : N) (s : side) : side := repDR0n (N.to_nat k) s.
Definition repUR (k : N) (s : side) : side := repURn (N.to_nat k) s.

Arguments rep0 : simpl never.
Arguments rep1 : simpl never.
Arguments repX : simpl never.
Arguments repY : simpl never.
Arguments repZ : simpl never.
Arguments repDL0 : simpl never.
Arguments repUL : simpl never.
Arguments repDR0 : simpl never.
Arguments repUR : simpl never.

Lemma rep0n_const0 (k : nat) : rep0n k (const S0) = const S0.
Proof.
  induction k as [| k' IH]; cbn [rep0n]; [reflexivity | rewrite IH, <- const_unfold; reflexivity].
Qed.

Lemma rep0_const0 (k : N) : rep0 k (const S0) = const S0.
Proof. unfold rep0; apply rep0n_const0. Qed.

Lemma rep0n_add (a b : nat) (s : side) : rep0n (a + b)%nat s = rep0n a (rep0n b s).
Proof. induction a as [| a' IH]; cbn [Nat.add rep0n]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rep1n_add (a b : nat) (s : side) : rep1n (a + b)%nat s = rep1n a (rep1n b s).
Proof. induction a as [| a' IH]; cbn [Nat.add rep1n]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repXn_add (a b : nat) (s : side) : repXn (a + b)%nat s = repXn a (repXn b s).
Proof. induction a as [| a' IH]; cbn [Nat.add repXn]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repYn_add (a b : nat) (s : side) : repYn (a + b)%nat s = repYn a (repYn b s).
Proof. induction a as [| a' IH]; cbn [Nat.add repYn]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repZn_add (a b : nat) (s : side) : repZn (a + b)%nat s = repZn a (repZn b s).
Proof. induction a as [| a' IH]; cbn [Nat.add repZn]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repDL0n_add (a b : nat) (s : side) : repDL0n (a + b)%nat s = repDL0n a (repDL0n b s).
Proof. induction a as [| a' IH]; cbn [Nat.add repDL0n]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repULn_add (a b : nat) (s : side) : repULn (a + b)%nat s = repULn a (repULn b s).
Proof. induction a as [| a' IH]; cbn [Nat.add repULn]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repDR0n_add (a b : nat) (s : side) : repDR0n (a + b)%nat s = repDR0n a (repDR0n b s).
Proof. induction a as [| a' IH]; cbn [Nat.add repDR0n]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repURn_add (a b : nat) (s : side) : repURn (a + b)%nat s = repURn a (repURn b s).
Proof. induction a as [| a' IH]; cbn [Nat.add repURn]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rep0_add (a b : N) (s : side) : rep0 (a + b) s = rep0 a (rep0 b s).
Proof. unfold rep0; rewrite N2Nat.inj_add; apply rep0n_add. Qed.

Lemma rep1_add (a b : N) (s : side) : rep1 (a + b) s = rep1 a (rep1 b s).
Proof. unfold rep1; rewrite N2Nat.inj_add; apply rep1n_add. Qed.

Lemma repX_add (a b : N) (s : side) : repX (a + b) s = repX a (repX b s).
Proof. unfold repX; rewrite N2Nat.inj_add; apply repXn_add. Qed.

Lemma repY_add (a b : N) (s : side) : repY (a + b) s = repY a (repY b s).
Proof. unfold repY; rewrite N2Nat.inj_add; apply repYn_add. Qed.

Lemma repZ_add (a b : N) (s : side) : repZ (a + b) s = repZ a (repZ b s).
Proof. unfold repZ; rewrite N2Nat.inj_add; apply repZn_add. Qed.

Lemma repDL0_add (a b : N) (s : side) : repDL0 (a + b) s = repDL0 a (repDL0 b s).
Proof. unfold repDL0; rewrite N2Nat.inj_add; apply repDL0n_add. Qed.

Lemma repUL_add (a b : N) (s : side) : repUL (a + b) s = repUL a (repUL b s).
Proof. unfold repUL; rewrite N2Nat.inj_add; apply repULn_add. Qed.

Lemma repDR0_add (a b : N) (s : side) : repDR0 (a + b) s = repDR0 a (repDR0 b s).
Proof. unfold repDR0; rewrite N2Nat.inj_add; apply repDR0n_add. Qed.

Lemma repUR_add (a b : N) (s : side) : repUR (a + b) s = repUR a (repUR b s).
Proof. unfold repUR; rewrite N2Nat.inj_add; apply repURn_add. Qed.

Fixpoint encCL (t : CTree) (s : side) : side :=
  match t with
  | CLeaf m0 => repX (2 * m0) (repY 1 (repX 3 s))
  | CNode a b => encCL a (encCL b s)
  end.

Fixpoint encCR (t : CTree) (s : side) : side :=
  match t with
  | CLeaf m0 => rep1 9 (S0 >> repZ m0 (rep1 4 s))
  | CNode a b => encCR b (encCR a s)
  end.

Fixpoint encCLList (xs : list N) (s : side) : side :=
  match xs with
  | [] => s
  | m :: ms => encCL (CLeaf m) (encCLList ms s)
  end.

Fixpoint encCRList (xs : list N) (s : side) : side :=
  match xs with
  | [] => s
  | m :: ms => encCRList ms (encCR (CLeaf m) s)
  end.

Definition encRWall (w : RWallShape) (s : side) : side :=
  match w with
  | RWEmpty => s
  | RWO12 => rep1 12 s
  | RWO908 => rep1 9 (S0 >> rep1 8 s)
  | RWO90Z q => rep1 9 (S0 >> repZ (q + 1) (rep1 8 s))
  end.

Definition encWall (s : list N) (w : RWallShape) : side :=
  encCRList s (encRWall w (const S0)).

Fixpoint encL (ls : LSide) : side :=
  match ls with
  | LNil => const S0
  | LB0 k tl => rep0 (k + 1) (encL tl)
  | LB1 k tl => rep1 (k + 1) (encL tl)
  | LX k tl => repX (k + 1) (encL tl)
  | LY k tl => repY (k + 1) (encL tl)
  | LDL0 k tl => repDL0 (k + 1) (encL tl)
  | LUL k tl => repUL (k + 1) (encL tl)
  | LC t tl => encCL t (encL tl)
  end.

Fixpoint encR (wt : side) (rs : RSide) : side :=
  match rs with
  | RNil => const S0
  | RWall => wt
  | RB0 k tl => rep0 (k + 1) (encR wt tl)
  | RO k tl => rep1 (k + 1) (encR wt tl)
  | RZ k tl => repZ (k + 1) (encR wt tl)
  | RDR0 k tl => repDR0 (k + 1) (encR wt tl)
  | RUR k tl => repUR (k + 1) (encR wt tl)
  | RCR t tl => encCR t (encR wt tl)
  end.

Definition encCfg (wt : side) (isA : bool) (ls : LSide) (rs : RSide) : Q * tape :=
  if isA then (encL ls) <{{A}} (encR wt rs)
  else (encL ls) {{B}}> (encR wt rs).

(** ** Section 3: Conduit Trees, Smart Stack Constructors & Soundness *)

Lemma rep0_0 (s : side) : rep0 0 s = s. Proof. reflexivity. Qed.
Lemma rep0_1 (s : side) : rep0 1 s = S0 >> s. Proof. reflexivity. Qed.
Lemma rep0_2 (s : side) : rep0 2 s = S0 >> S0 >> s. Proof. reflexivity. Qed.
Lemma rep1_0 (s : side) : rep1 0 s = s. Proof. reflexivity. Qed.
Lemma rep1_1 (s : side) : rep1 1 s = S1 >> s. Proof. reflexivity. Qed.
Lemma rep1_2 (s : side) : rep1 2 s = S1 >> S1 >> s. Proof. reflexivity. Qed.
Lemma rep1_3 (s : side) : rep1 3 s = S1 >> S1 >> S1 >> s. Proof. reflexivity. Qed.
Lemma rep1_4 (s : side) : rep1 4 s = S1 >> S1 >> S1 >> S1 >> s. Proof. reflexivity. Qed.
Lemma rep1_7 (s : side) : rep1 7 s = S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> s. Proof. reflexivity. Qed.
Lemma rep1_8 (s : side) : rep1 8 s = S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> s. Proof. reflexivity. Qed.
Lemma rep1_9 (s : side) : rep1 9 s = S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> S1 >> s. Proof. reflexivity. Qed.
Lemma repX_0 (s : side) : repX 0 s = s. Proof. reflexivity. Qed.
Lemma repX_1 (s : side) : repX 1 s = S1 >> S1 >> S0 >> s. Proof. reflexivity. Qed.
Lemma repX_2 (s : side) : repX 2 s = S1 >> S1 >> S0 >> S1 >> S1 >> S0 >> s. Proof. reflexivity. Qed.
Lemma repX_3 (s : side) : repX 3 s = repX 1 (repX 2 s). Proof. reflexivity. Qed.
Lemma repY_0 (s : side) : repY 0 s = s. Proof. reflexivity. Qed.
Lemma repY_1 (s : side) : repY 1 s = S1 >> S0 >> S0 >> S1 >> S0 >> s. Proof. reflexivity. Qed.
Lemma repY_2 (s : side) : repY 2 s = repY 1 (repY 1 s). Proof. reflexivity. Qed.
Lemma repZ_0 (s : side) : repZ 0 s = s. Proof. reflexivity. Qed.
Lemma repZ_1 (s : side) : repZ 1 s = S1 >> S1 >> S1 >> S1 >> S1 >> S0 >> s. Proof. reflexivity. Qed.
Lemma repDL0_0 (s : side) : repDL0 0 s = s. Proof. reflexivity. Qed.
Lemma repDL0_1 (s : side) : repDL0 1 s = repY 2 (repX 3 s). Proof. reflexivity. Qed.
Lemma repUL_0 (s : side) : repUL 0 s = s. Proof. reflexivity. Qed.
Lemma repUL_1 (s : side) : repUL 1 s = repY 2 (repX 7 s). Proof. reflexivity. Qed.
Lemma repDR0_0 (s : side) : repDR0 0 s = s. Proof. reflexivity. Qed.
Lemma repDR0_1 (s : side) : repDR0 1 s = S1 >> S0 >> repZ 1 (rep1 7 (S0 >> rep1 3 s)). Proof. reflexivity. Qed.
Lemma repUR_0 (s : side) : repUR 0 s = s. Proof. reflexivity. Qed.
Lemma repUR_1 (s : side) : repUR 1 s = S1 >> S0 >> repZ 3 (rep1 7 (S0 >> rep1 3 s)). Proof. reflexivity. Qed.

Fixpoint splitFirstAux (t r : CTree) : N * CTree :=
  match t with
  | CLeaf m => (m, r)
  | CNode a b => splitFirstAux a (CNode b r)
  end.

Definition splitFirst (t : CTree) : N * option CTree :=
  match t with
  | CLeaf m => (m, None)
  | CNode a b => let '(m, r) := splitFirstAux a b in (m, Some r)
  end.

Fixpoint splitLastAux (l t : CTree) : CTree * N :=
  match t with
  | CLeaf m => (l, m)
  | CNode a b => splitLastAux (CNode l a) b
  end.

Definition splitLast (t : CTree) : option CTree * N :=
  match t with
  | CLeaf m => (None, m)
  | CNode a b => let '(l, m) := splitLastAux a b in (Some l, m)
  end.

Definition addFirst (d : N) (t : CTree) : CTree :=
  match splitFirst t with
  | (m, None) => CLeaf (m + d)
  | (m, Some r) => CNode (CLeaf (m + d)) r
  end.

Fixpoint firstM (t : CTree) : N :=
  match t with
  | CLeaf m => m
  | CNode a _ => firstM a
  end.

Fixpoint flattenCTreeAux (t : CTree) (acc : list N) : list N :=
  match t with
  | CLeaf m => m :: acc
  | CNode l r => flattenCTreeAux l (flattenCTreeAux r acc)
  end.

Definition flattenCTree (t : CTree) : list N :=
  flattenCTreeAux t [].

Fixpoint ofListCTreeNE (x0 : N) (xs : list N) : CTree :=
  match xs with
  | [] => CLeaf x0
  | y :: ys => CNode (CLeaf x0) (ofListCTreeNE y ys)
  end.

Definition splitStep (st : list N * list N) : list N * list N :=
  match st with
  | (acc, []) => (acc, [])
  | (acc, x :: xs) => (x :: acc, xs)
  end.

Definition splitAtN (p : positive) (xs : list N) : list N * list N :=
  let '(acc_rev, rest) := Pos.iter splitStep ([], xs) p in
  (List.rev acc_rev, rest).

Fixpoint beqListN (xs ys : list N) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (N.eqb x y) (beqListN xs' ys')
  | _, _ => false
  end.

Definition beqCTreeSem (t1 t2 : CTree) : bool :=
  beqListN (flattenCTree t1) (flattenCTree t2).

Fixpoint beqLSideSem (l1 l2 : LSide) : bool :=
  match l1, l2 with
  | LNil, LNil => true
  | LB0 k1 t1, LB0 k2 t2 => andb (N.eqb k1 k2) (beqLSideSem t1 t2)
  | LB1 k1 t1, LB1 k2 t2 => andb (N.eqb k1 k2) (beqLSideSem t1 t2)
  | LX k1 t1, LX k2 t2 => andb (N.eqb k1 k2) (beqLSideSem t1 t2)
  | LY k1 t1, LY k2 t2 => andb (N.eqb k1 k2) (beqLSideSem t1 t2)
  | LDL0 k1 t1, LDL0 k2 t2 => andb (N.eqb k1 k2) (beqLSideSem t1 t2)
  | LUL k1 t1, LUL k2 t2 => andb (N.eqb k1 k2) (beqLSideSem t1 t2)
  | LC c1 t1, LC c2 t2 => andb (beqCTreeSem c1 c2) (beqLSideSem t1 t2)
  | _, _ => false
  end.

Lemma beqListN_eq (xs : list N) :
  forall ys : list N, beqListN xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn [beqListN] in H;
    try reflexivity; try discriminate.
  apply Bool.andb_true_iff in H; destruct H as [Hx Hxs].
  apply N.eqb_eq in Hx; subst y.
  rewrite (IH ys' Hxs); reflexivity.
Qed.

Lemma encCLList_flattenAux (t : CTree) :
  forall (acc : list N) (s : side),
    encCLList (flattenCTreeAux t acc) s = encCL t (encCLList acc s).
Proof.
  induction t as [m | l IHl r IHr]; intros acc s; cbn [flattenCTreeAux encCL encCLList].
  - reflexivity.
  - rewrite IHl, IHr; reflexivity.
Qed.

Lemma encCL_eq_encCLList (t : CTree) (s : side) :
  encCL t s = encCLList (flattenCTree t) s.
Proof.
  symmetry; exact (encCLList_flattenAux t [] s).
Qed.

Lemma encCRList_flattenAux (t : CTree) :
  forall (acc : list N) (s : side),
    encCRList (flattenCTreeAux t acc) s = encCRList acc (encCR t s).
Proof.
  induction t as [m | l IHl r IHr]; intros acc s; cbn [flattenCTreeAux encCR encCRList].
  - reflexivity.
  - rewrite IHl, IHr; reflexivity.
Qed.

Lemma encCR_eq_encCRList (t : CTree) (s : side) :
  encCR t s = encCRList (flattenCTree t) s.
Proof.
  symmetry; exact (encCRList_flattenAux t [] s).
Qed.

Lemma encCRList_app (a b : list N) :
  forall s : side, encCRList (a ++ b) s = encCRList b (encCRList a s).
Proof.
  induction a as [| m a' IHa]; intro s; cbn [List.app encCRList].
  - reflexivity.
  - exact (IHa (encCR (CLeaf m) s)).
Qed.

Lemma ofListCTreeNE_aux (xs : list N) :
  forall (x0 : N) (acc : list N),
    flattenCTreeAux (ofListCTreeNE x0 xs) acc = x0 :: xs ++ acc.
Proof.
  induction xs as [| y ys IH]; intros x0 acc; cbn [ofListCTreeNE flattenCTreeAux List.app].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma ofListCTreeNE_spec (x0 : N) (xs : list N) :
  flattenCTree (ofListCTreeNE x0 xs) = x0 :: xs.
Proof.
  unfold flattenCTree; rewrite ofListCTreeNE_aux, app_nil_r; reflexivity.
Qed.

Lemma splitStep_inv (st : list N * list N) :
  List.rev (fst (splitStep st)) ++ snd (splitStep st) = List.rev (fst st) ++ snd st.
Proof.
  destruct st as [acc [| x rest]]; cbn [splitStep fst snd List.rev].
  - reflexivity.
  - rewrite <- app_assoc; reflexivity.
Qed.

Lemma Pos_iter_splitStep_inv (p : positive) (st : list N * list N) :
  List.rev (fst (Pos.iter splitStep st p)) ++ snd (Pos.iter splitStep st p) =
  List.rev (fst st) ++ snd st.
Proof.
  induction p as [| p' IHp] using Pos.peano_ind.
  - exact (splitStep_inv st).
  - rewrite Pos.iter_succ, splitStep_inv; exact IHp.
Qed.

Lemma splitAtN_append (p : positive) (xs : list N) :
  fst (splitAtN p xs) ++ snd (splitAtN p xs) = xs.
Proof.
  unfold splitAtN.
  pose proof (Pos_iter_splitStep_inv p ([], xs)) as H.
  destruct (Pos.iter splitStep ([], xs) p) as [acc_rev rest].
  exact H.
Qed.

Lemma beqLSideSem_enc (l1 : LSide) :
  forall l2 : LSide, beqLSideSem l1 l2 = true -> encL l1 = encL l2.
Proof.
  induction l1 as [| k1 t1 IH | k1 t1 IH | k1 t1 IH | k1 t1 IH | k1 t1 IH | k1 t1 IH | c1 t1 IH];
    intros [| k2 t2 | k2 t2 | k2 t2 | k2 t2 | k2 t2 | k2 t2 | c2 t2] H;
    cbn [beqLSideSem] in H; try reflexivity; try discriminate;
    apply Bool.andb_true_iff in H; destruct H as [Hk Ht].
  - apply N.eqb_eq in Hk; subst k2; cbn [encL]; rewrite (IH t2 Ht); reflexivity.
  - apply N.eqb_eq in Hk; subst k2; cbn [encL]; rewrite (IH t2 Ht); reflexivity.
  - apply N.eqb_eq in Hk; subst k2; cbn [encL]; rewrite (IH t2 Ht); reflexivity.
  - apply N.eqb_eq in Hk; subst k2; cbn [encL]; rewrite (IH t2 Ht); reflexivity.
  - apply N.eqb_eq in Hk; subst k2; cbn [encL]; rewrite (IH t2 Ht); reflexivity.
  - apply N.eqb_eq in Hk; subst k2; cbn [encL]; rewrite (IH t2 Ht); reflexivity.
  - unfold beqCTreeSem in Hk; apply beqListN_eq in Hk.
    cbn [encL]; rewrite encCL_eq_encCLList, (encCL_eq_encCLList c2), Hk, (IH t2 Ht); reflexivity.
Qed.

Lemma splitFirstAux_spec (a : CTree) :
  forall (r : CTree) (s : side),
    encCL a (encCL r s) =
    repX (2 * fst (splitFirstAux a r)) (repY 1 (repX 3 (encCL (snd (splitFirstAux a r)) s))).
Proof.
  induction a as [m | a1 IHa1 a2 _]; intros r s; cbn [splitFirstAux encCL].
  - reflexivity.
  - exact (IHa1 (CNode a2 r) s).
Qed.

Lemma splitFirst_spec (t : CTree) (s : side) :
  encCL t s =
  repX (2 * fst (splitFirst t)) (repY 1 (repX 3
    (match snd (splitFirst t) with None => s | Some r => encCL r s end))).
Proof.
  destruct t as [m | a b]; cbn [splitFirst encCL].
  - reflexivity.
  - pose proof (splitFirstAux_spec a b s) as H.
    destruct (splitFirstAux a b) as [m r]; exact H.
Qed.

Lemma firstM_eq_splitFirstAux (a : CTree) :
  forall r : CTree, firstM a = fst (splitFirstAux a r).
Proof.
  induction a as [m | a1 IHa1 a2 _]; intro r; cbn [firstM splitFirstAux].
  - reflexivity.
  - exact (IHa1 (CNode a2 r)).
Qed.

Lemma firstM_eq_splitFirst (t : CTree) :
  firstM t = fst (splitFirst t).
Proof.
  destruct t as [m | a b]; cbn [firstM splitFirst].
  - reflexivity.
  - pose proof (firstM_eq_splitFirstAux a b) as H.
    destruct (splitFirstAux a b) as [m r]; exact H.
Qed.

Lemma splitLastAux_spec (b : CTree) :
  forall (l : CTree) (s : side),
    encCR b (encCR l s) =
    rep1 9 (S0 >> repZ (snd (splitLastAux l b)) (rep1 4 (encCR (fst (splitLastAux l b)) s))).
Proof.
  induction b as [m | b1 _ b2 IHb2]; intros l s; cbn [splitLastAux encCR].
  - reflexivity.
  - exact (IHb2 (CNode l b1) s).
Qed.

Lemma splitLast_spec (t : CTree) (s : side) :
  encCR t s =
  rep1 9 (S0 >> repZ (snd (splitLast t)) (rep1 4
    (match fst (splitLast t) with None => s | Some l => encCR l s end))).
Proof.
  destruct t as [m | a b]; cbn [splitLast encCR].
  - reflexivity.
  - pose proof (splitLastAux_spec b a s) as H.
    destruct (splitLastAux a b) as [l m]; exact H.
Qed.

Lemma addFirst_spec (d : N) (t : CTree) (s : side) :
  encCL (addFirst d t) s = repX (2 * d) (encCL t s).
Proof.
  pose proof (splitFirst_spec t s) as Hsp.
  unfold addFirst.
  destruct (splitFirst t) as [m [r | ]]; cbn [fst snd] in Hsp |- *;
    cbn [encCL]; rewrite Hsp, <- repX_add; f_equal; lia.
Qed.

Definition pushB0L (cnt : N) (ls : LSide) : LSide :=
  if N.eqb cnt 0 then ls
  else match ls with
       | LNil => LNil
       | LB0 k tl => LB0 (k + cnt) tl
       | _ => LB0 (cnt - 1) ls
       end.

Definition pushB0L1 (ls : LSide) : LSide :=
  match ls with
  | LNil => LNil
  | LB0 k tl => LB0 (k + 1) tl
  | _ => LB0 0 ls
  end.

Definition pushB1RawL1 (ls : LSide) : LSide :=
  match ls with
  | LB1 k tl => LB1 (k + 1) tl
  | _ => LB1 0 ls
  end.

Definition pushXRawL (cnt : N) (ls : LSide) : LSide :=
  if N.eqb cnt 0 then ls
  else match ls with
       | LX k tl => LX (k + cnt) tl
       | _ => LX (cnt - 1) ls
       end.

Definition pushXRawL1 (ls : LSide) : LSide :=
  match ls with | LX k tl => LX (k + 1) tl | _ => LX 0 ls end.

Definition pushXRawL2 (ls : LSide) : LSide :=
  match ls with | LX k tl => LX (k + 2) tl | _ => LX 1 ls end.

Definition pushXRawL3 (ls : LSide) : LSide :=
  match ls with | LX k tl => LX (k + 3) tl | _ => LX 2 ls end.

Definition pushYRawL1 (ls : LSide) : LSide :=
  match ls with | LY k tl => LY (k + 1) tl | _ => LY 0 ls end.

Definition pushULRawL (cnt : N) (ls : LSide) : LSide :=
  if N.eqb cnt 0 then ls
  else match ls with
       | LUL k tl => LUL (k + cnt) tl
       | _ => LUL (cnt - 1) ls
       end.

Definition pushULRawL1 (ls : LSide) : LSide :=
  match ls with | LUL k tl => LUL (k + 1) tl | _ => LUL 0 ls end.

Definition pushDL0RawL1 (ls : LSide) : LSide :=
  match ls with
  | LX kx tl =>
    if N.leb 3 kx then pushULRawL1 (pushXRawL (kx - 3) tl)
    else LDL0 0 (LX kx tl)
  | LDL0 k tl => LDL0 (k + 1) tl
  | _ => LDL0 0 ls
  end.

Definition pushDL0RawL (cnt : N) (ls : LSide) : LSide :=
  if N.eqb cnt 0 then ls
  else
    let l1 := pushDL0RawL1 ls in
    if N.eqb cnt 1 then l1
    else match l1 with
         | LDL0 k tl => LDL0 (k + (cnt - 1)) tl
         | _ => LDL0 (cnt - 2) l1
         end.

Fixpoint pushCLAux (f : nat) (c : CTree) (ls : LSide) : LSide :=
  match f with
  | O => LC c ls
  | S f' =>
    match ls with
    | LC c2 tl => pushCLAux f' (CNode c c2) tl
    | LX kx l1 =>
      match l1 with
      | LC c2 tl =>
        let tot := kx + 1 in
        if N.eqb (N.modulo tot 2) 0 then
          pushCLAux f' (CNode c (addFirst (N.div tot 2) c2)) tl
        else LC c ls
      | LY ky l2 =>
        if N.eqb ky 0 then
          match l2 with
          | LX kxBel tl =>
            let tot := kx + 1 in
            if andb (N.eqb (N.modulo tot 2) 0) (N.leb 2 kxBel) then
              let c' := CNode c (CLeaf (N.div tot 2)) in
              if N.eqb kxBel 2 then pushCLAux f' c' tl
              else LC c' (pushXRawL (kxBel - 2) tl)
            else LC c ls
          | _ => LC c ls
          end
        else LC c ls
      | _ => LC c ls
      end
    | LY ky l1 =>
      if N.eqb ky 0 then
        match l1 with
        | LX kxBel tl =>
          if N.leb 2 kxBel then
            let c' := CNode c (CLeaf 0) in
            if N.eqb kxBel 2 then pushCLAux f' c' tl
            else LC c' (pushXRawL (kxBel - 2) tl)
          else LC c ls
        | _ => LC c ls
        end
      else LC c ls
    | _ => LC c ls
    end
  end.

Definition pushCL (c : CTree) (ls : LSide) : LSide := pushCLAux 8%nat c ls.

Fixpoint coalesceLAux (f : nat) (ls : LSide) : LSide :=
  match f with
  | O => ls
  | S f' =>
    match ls with
    | LX kx l1 =>
      match l1 with
      | LC c tl =>
        let tot := kx + 1 in
        if N.eqb (N.modulo tot 2) 0 then
          coalesceLAux f' (pushCL (addFirst (N.div tot 2) c) tl)
        else ls
      | LY ky l2 =>
        if N.eqb ky 0 then
          match l2 with
          | LX kxBel tl =>
            let tot := kx + 1 in
            if andb (N.eqb (N.modulo tot 2) 0) (N.leb 2 kxBel) then
              coalesceLAux f' (pushCL (CLeaf (N.div tot 2)) (pushXRawL (kxBel - 2) tl))
            else ls
          | _ => ls
          end
        else ls
      | _ => ls
      end
    | LY ky l1 =>
      if N.eqb ky 0 then
        match l1 with
        | LC c tl =>
          if N.eqb (firstM c) 0 then
            match splitFirst c with
            | (_, None) => coalesceLAux f' (pushDL0RawL1 tl)
            | (_, Some c') => coalesceLAux f' (pushDL0RawL1 (pushCL c' tl))
            end
          else ls
        | LX kx tl =>
          if N.leb 2 kx then
            coalesceLAux f' (pushCL (CLeaf 0) (pushXRawL (kx - 2) tl))
          else ls
        | _ => ls
        end
      else if N.eqb ky 1 then
        match l1 with
        | LX kx tl =>
          if N.leb 6 kx then
            coalesceLAux f' (pushULRawL1 (pushXRawL (kx - 6) tl))
          else if N.leb 2 kx then
            coalesceLAux f' (pushDL0RawL1 (pushXRawL (kx - 2) tl))
          else ls
        | _ => ls
        end
      else ls
    | _ => ls
    end
  end.

Definition coalesceL (ls : LSide) : LSide := coalesceLAux 3%nat ls.

Definition pushXL (cnt : N) (ls : LSide) : LSide :=
  if N.eqb cnt 0 then ls else coalesceL (pushXRawL cnt ls).

Definition pushXL1 (ls : LSide) : LSide := coalesceL (pushXRawL1 ls).
Definition pushXL2 (ls : LSide) : LSide := coalesceL (pushXRawL2 ls).
Definition pushYL1 (ls : LSide) : LSide := coalesceL (pushYRawL1 ls).

Definition pushYL (n : N) (ls : LSide) : LSide :=
  match n with
  | N0 => ls
  | Npos p => Pos.iter pushYL1 ls p
  end.

Definition normTopL (ls : LSide) : LSide :=
  match ls with
  | LB1 k1 l1 =>
    if N.eqb k1 1 then
      match l1 with
      | LB0 kb0 tl => pushXL1 (pushB0L kb0 tl)
      | _ => ls
      end
    else if N.eqb k1 0 then
      match l1 with
      | LB0 k2 l2 =>
        if N.eqb k2 1 then
          match l2 with
          | LB1 k3 l3 =>
            if N.eqb k3 0 then
              match l3 with
              | LB0 kb0 tl => pushYL1 (pushB0L kb0 tl)
              | _ => ls
              end
            else ls
          | _ => ls
          end
        else ls
      | _ => ls
      end
    else ls
  | _ => ls
  end.

Definition pushBitL1 (ls : LSide) : LSide := normTopL (pushB1RawL1 ls).

Definition popBitL (ls : LSide) : bool * LSide :=
  match ls with
  | LNil => (false, LNil)
  | LB0 k tl => if N.eqb k 0 then (false, tl) else (false, LB0 (k - 1) tl)
  | LB1 k tl => if N.eqb k 0 then (true, tl) else (true, LB1 (k - 1) tl)
  | LX k tl =>
    if N.eqb k 0 then (true, pushBitL1 (pushB0L1 tl))
    else (true, LB1 0 (LB0 0 (LX (k - 1) tl)))
  | LY k tl =>
    if N.eqb k 0 then (true, pushB0L1 (pushB0L1 (pushBitL1 (pushB0L1 tl))))
    else (true, LB0 1 (LB1 0 (LB0 0 (LY (k - 1) tl))))
  | LDL0 k tl =>
    if N.eqb k 0 then (true, LB0 1 (LB1 0 (LB0 0 (LY 0 (pushXRawL3 tl)))))
    else (true, LB0 1 (LB1 0 (LB0 0 (LY 0 (LX 2 (LDL0 (k - 1) tl))))))
  | LUL k tl =>
    if N.eqb k 0 then (true, LB0 1 (LB1 0 (LB0 0 (LY 0 (pushXRawL 7 tl)))))
    else (true, LB0 1 (LB1 0 (LB0 0 (LY 0 (LX 6 (LUL (k - 1) tl))))))
  | LC t tl =>
    let '(m0, optC) := splitFirst t in
    let tl' := match optC with None => tl | Some c' => LC c' tl end in
    let base := pushXRawL3 tl' in
    if N.eqb m0 0 then (true, LB0 1 (LB1 0 (LB0 0 base)))
    else (true, LB1 0 (LB0 0 (pushXRawL (2 * (m0 - 1) + 1) (LY 0 base))))
  end.

Definition pushB0R1 (rs : RSide) : RSide :=
  match rs with
  | RNil => RNil
  | RB0 k tl => RB0 (k + 1) tl
  | _ => RB0 0 rs
  end.

Definition pushOR (cnt : N) (rs : RSide) : RSide :=
  if N.eqb cnt 0 then rs
  else match rs with
       | RO k tl => RO (k + cnt) tl
       | _ => RO (cnt - 1) rs
       end.

Definition pushOR1 (rs : RSide) : RSide := match rs with RO k tl => RO (k + 1) tl | _ => RO 0 rs end.
Definition pushOR2 (rs : RSide) : RSide := match rs with RO k tl => RO (k + 2) tl | _ => RO 1 rs end.
Definition pushOR3 (rs : RSide) : RSide := match rs with RO k tl => RO (k + 3) tl | _ => RO 2 rs end.
Definition pushOR4 (rs : RSide) : RSide := match rs with RO k tl => RO (k + 4) tl | _ => RO 3 rs end.
Definition pushOR6 (rs : RSide) : RSide := match rs with RO k tl => RO (k + 6) tl | _ => RO 5 rs end.
Definition pushOR8 (rs : RSide) : RSide := match rs with RO k tl => RO (k + 8) tl | _ => RO 7 rs end.

Definition pushZR (cnt : N) (rs : RSide) : RSide :=
  if N.eqb cnt 0 then rs
  else match rs with
       | RZ k tl => RZ (k + cnt) tl
       | _ => RZ (cnt - 1) rs
       end.

Definition pushDR0R (cnt : N) (rs : RSide) : RSide :=
  if N.eqb cnt 0 then rs
  else match rs with
       | RDR0 k tl => RDR0 (k + cnt) tl
       | _ => RDR0 (cnt - 1) rs
       end.

Definition pushURR (cnt : N) (rs : RSide) : RSide :=
  if N.eqb cnt 0 then rs
  else match rs with
       | RUR k tl => RUR (k + cnt) tl
       | _ => RUR (cnt - 1) rs
       end.

Definition pushCRR (c : CTree) (rs : RSide) : RSide :=
  match rs with
  | RCR cBelow tl => RCR (CNode cBelow c) tl
  | _ => RCR c rs
  end.

Definition popBitR (rs : RSide) : option (bool * RSide) :=
  match rs with
  | RNil => Some (false, RNil)
  | RWall => None
  | RB0 k tl => if N.eqb k 0 then Some (false, tl) else Some (false, RB0 (k - 1) tl)
  | RO k tl => if N.eqb k 0 then Some (true, tl) else Some (true, RO (k - 1) tl)
  | RZ k tl =>
    if N.eqb k 0 then Some (true, RO 3 (pushB0R1 tl))
    else Some (true, RO 3 (RB0 0 (RZ (k - 1) tl)))
  | RDR0 k tl =>
    if N.eqb k 0 then Some (true, RB0 0 (RZ 0 (RO 6 (RB0 0 (pushOR3 tl)))))
    else Some (true, RB0 0 (RZ 0 (RO 6 (RB0 0 (RO 2 (RDR0 (k - 1) tl))))))
  | RUR k tl =>
    if N.eqb k 0 then Some (true, RB0 0 (RZ 2 (RO 6 (RB0 0 (pushOR3 tl)))))
    else Some (true, RB0 0 (RZ 2 (RO 6 (RB0 0 (RO 2 (RUR (k - 1) tl))))))
  | RCR t tl =>
    let '(optC, m0) := splitLast t in
    let tl' := match optC with None => tl | Some c' => pushCRR c' tl end in
    Some (true, RO 7 (RB0 0 (pushZR m0 (pushOR4 tl'))))
  end.

Lemma pushB0L_spec (cnt : N) (ls : LSide) :
  encL (pushB0L cnt ls) = rep0 cnt (encL ls).
Proof.
  unfold pushB0L.
  destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite rep0_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [encL].
    + symmetry; apply rep0_const0.
    + replace (k + cnt + 1) with (cnt + (k + 1)) by lia; apply rep0_add.
    + f_equal; lia.
    + f_equal; lia.
    + f_equal; lia.
    + f_equal; lia.
    + f_equal; lia.
    + f_equal; lia.
Qed.

Lemma pushB0L1_spec (ls : LSide) :
  encL (pushB0L1 ls) = S0 >> encL ls.
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushB0L1 encL];
    try (rewrite rep0_1; reflexivity).
  - apply const_unfold.
  - replace (k + 1 + 1) with (1 + (k + 1)) by lia; rewrite rep0_add, rep0_1; reflexivity.
Qed.

Lemma pushB1RawL1_spec (ls : LSide) :
  encL (pushB1RawL1 ls) = S1 >> encL ls.
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushB1RawL1 encL];
    try (rewrite rep1_1; reflexivity).
  replace (k + 1 + 1) with (1 + (k + 1)) by lia; rewrite rep1_add, rep1_1; reflexivity.
Qed.

Lemma pushXRawL_spec (cnt : N) (ls : LSide) :
  encL (pushXRawL cnt ls) = repX cnt (encL ls).
Proof.
  unfold pushXRawL.
  destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite repX_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [encL];
      try (f_equal; lia).
    replace (k + cnt + 1) with (cnt + (k + 1)) by lia; apply repX_add.
Qed.

Lemma pushXRawL1_spec (ls : LSide) : encL (pushXRawL1 ls) = repX 1 (encL ls).
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushXRawL1 encL];
    try reflexivity.
  replace (k + 1 + 1) with (1 + (k + 1)) by lia; apply repX_add.
Qed.

Lemma pushXRawL2_spec (ls : LSide) : encL (pushXRawL2 ls) = repX 2 (encL ls).
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushXRawL2 encL];
    try reflexivity.
  replace (k + 2 + 1) with (2 + (k + 1)) by lia; apply repX_add.
Qed.

Lemma pushXRawL3_spec (ls : LSide) : encL (pushXRawL3 ls) = repX 3 (encL ls).
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushXRawL3 encL];
    try reflexivity.
  replace (k + 3 + 1) with (3 + (k + 1)) by lia; apply repX_add.
Qed.

Lemma pushYRawL1_spec (ls : LSide) : encL (pushYRawL1 ls) = repY 1 (encL ls).
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushYRawL1 encL];
    try reflexivity.
  replace (k + 1 + 1) with (1 + (k + 1)) by lia; apply repY_add.
Qed.

Lemma pushULRawL_spec (cnt : N) (ls : LSide) :
  encL (pushULRawL cnt ls) = repUL cnt (encL ls).
Proof.
  unfold pushULRawL.
  destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite repUL_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [encL];
      try (f_equal; lia).
    replace (k + cnt + 1) with (cnt + (k + 1)) by lia; apply repUL_add.
Qed.

Lemma pushULRawL1_spec (ls : LSide) : encL (pushULRawL1 ls) = repUL 1 (encL ls).
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushULRawL1 encL];
    try reflexivity.
  replace (k + 1 + 1) with (1 + (k + 1)) by lia; apply repUL_add.
Qed.

Lemma pushDL0RawL1_spec (ls : LSide) : encL (pushDL0RawL1 ls) = repDL0 1 (encL ls).
Proof.
  destruct ls as [| k tl | k tl | kx tl | k tl | k tl | k tl | t tl]; cbn [pushDL0RawL1];
    try reflexivity.
  - destruct (N.leb 3 kx) eqn:H3.
    + apply N.leb_le in H3.
      rewrite pushULRawL1_spec, pushXRawL_spec.
      cbn [encL]; rewrite repUL_1, repDL0_1, <- repX_add.
      replace (7 + (kx - 3)) with (3 + (kx + 1)) by lia.
      rewrite repX_add; reflexivity.
    + reflexivity.
  - cbn [encL]; replace (k + 1 + 1) with (1 + (k + 1)) by lia; apply repDL0_add.
Qed.

Lemma pushDL0RawL_spec (cnt : N) (ls : LSide) :
  encL (pushDL0RawL cnt ls) = repDL0 cnt (encL ls).
Proof.
  unfold pushDL0RawL.
  destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite repDL0_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct (N.eqb cnt 1) eqn:H1.
    + apply N.eqb_eq in H1; subst cnt; exact (pushDL0RawL1_spec ls).
    + apply N.eqb_neq in H1.
      pose proof (pushDL0RawL1_spec ls) as Hl1.
      destruct (pushDL0RawL1 ls) as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl];
        cbn [encL] in Hl1 |- *.
      all: try (replace (cnt - 2 + 1) with (cnt - 1) by lia;
                rewrite Hl1, <- repDL0_add; f_equal; lia).
      replace (k + (cnt - 1) + 1) with ((cnt - 1) + (k + 1)) by lia.
      rewrite repDL0_add, Hl1, <- repDL0_add; f_equal; lia.
Qed.

Lemma pushCLAux_spec (f : nat) :
  forall (c : CTree) (ls : LSide), encL (pushCLAux f c ls) = encCL c (encL ls).
Proof.
  induction f as [| f' IH]; intros c ls; cbn [pushCLAux].
  - reflexivity.
  - destruct ls as [| k tl | k tl | kx l1 | ky l1 | k tl | k tl | c2 tl]; try reflexivity.
    + destruct l1 as [| k2 tl | k2 tl | k2 tl | ky l2 | k2 tl | k2 tl | c2 tl]; try reflexivity.
      * destruct (N.eqb ky 0) eqn:Hky; [| reflexivity].
        apply N.eqb_eq in Hky; subst ky.
        destruct l2 as [| k3 tl | k3 tl | kxBel tl | k3 tl | k3 tl | k3 tl | c3 tl]; try reflexivity.
        destruct (N.eqb (N.modulo (kx + 1) 2) 0) eqn:Hm; [| reflexivity].
        destruct (N.leb 2 kxBel) eqn:Hbel; [| reflexivity].
        cbn [andb].
        apply N.eqb_eq in Hm; apply N.leb_le in Hbel.
        destruct (N_div_mod_2 (kx + 1)) as [Hdm _].
        destruct (N.eqb kxBel 2) eqn:Hb2.
        -- apply N.eqb_eq in Hb2; subst kxBel.
           rewrite IH; cbn [encCL encL].
           replace (2 * N.div (kx + 1) 2) with (kx + 1) by lia; reflexivity.
        -- cbn [encL encCL]; rewrite pushXRawL_spec, <- repX_add.
           replace (2 * N.div (kx + 1) 2) with (kx + 1) by lia.
           replace (3 + (kxBel - 2)) with (kxBel + 1) by lia; reflexivity.
      * destruct (N.eqb (N.modulo (kx + 1) 2) 0) eqn:Hm; [| reflexivity].
        apply N.eqb_eq in Hm; destruct (N_div_mod_2 (kx + 1)) as [Hdm _].
        rewrite IH; cbn [encCL encL]; rewrite addFirst_spec.
        replace (2 * N.div (kx + 1) 2) with (kx + 1) by lia; reflexivity.
    + destruct (N.eqb ky 0) eqn:Hky; [| reflexivity].
      apply N.eqb_eq in Hky; subst ky.
      destruct l1 as [| k2 tl | k2 tl | kxBel tl | k2 tl | k2 tl | k2 tl | c2 tl]; try reflexivity.
      destruct (N.leb 2 kxBel) eqn:Hbel; [| reflexivity].
      apply N.leb_le in Hbel.
      destruct (N.eqb kxBel 2) eqn:Hb2.
      * apply N.eqb_eq in Hb2; subst kxBel.
        rewrite IH; cbn [encCL encL N.mul]; rewrite repX_0; reflexivity.
      * cbn [encL encCL N.mul]; rewrite repX_0, pushXRawL_spec, <- repX_add.
        replace (3 + (kxBel - 2)) with (kxBel + 1) by lia; reflexivity.
    + rewrite IH; reflexivity.
Qed.

Lemma pushCL_spec (c : CTree) (ls : LSide) :
  encL (pushCL c ls) = encCL c (encL ls).
Proof. exact (pushCLAux_spec 8%nat c ls). Qed.

Lemma coalesceLAux_spec (f : nat) :
  forall ls : LSide, encL (coalesceLAux f ls) = encL ls.
Proof.
  induction f as [| f' IH]; intro ls; cbn [coalesceLAux].
  - reflexivity.
  - destruct ls as [| k tl | k tl | kx l1 | ky l1 | k tl | k tl | c tl]; try reflexivity.
    + destruct l1 as [| k2 tl | k2 tl | k2 tl | ky l2 | k2 tl | k2 tl | c tl]; try reflexivity.
      * destruct (N.eqb ky 0) eqn:Hky; [| reflexivity].
        apply N.eqb_eq in Hky; subst ky.
        destruct l2 as [| k3 tl | k3 tl | kxBel tl | k3 tl | k3 tl | k3 tl | c3 tl]; try reflexivity.
        destruct (N.eqb (N.modulo (kx + 1) 2) 0) eqn:Hm; [| reflexivity].
        destruct (N.leb 2 kxBel) eqn:Hbel; [| reflexivity].
        cbn [andb].
        apply N.eqb_eq in Hm; apply N.leb_le in Hbel.
        destruct (N_div_mod_2 (kx + 1)) as [Hdm _].
        rewrite IH, pushCL_spec, pushXRawL_spec; cbn [encCL encL].
        rewrite <- repX_add.
        replace (2 * N.div (kx + 1) 2) with (kx + 1) by lia.
        replace (3 + (kxBel - 2)) with (kxBel + 1) by lia; reflexivity.
      * destruct (N.eqb (N.modulo (kx + 1) 2) 0) eqn:Hm; [| reflexivity].
        apply N.eqb_eq in Hm; destruct (N_div_mod_2 (kx + 1)) as [Hdm _].
        rewrite IH, pushCL_spec, addFirst_spec; cbn [encL].
        replace (2 * N.div (kx + 1) 2) with (kx + 1) by lia; reflexivity.
    + destruct (N.eqb ky 0) eqn:Hky0.
      * apply N.eqb_eq in Hky0; subst ky.
        destruct l1 as [| k2 tl | k2 tl | kx tl | k2 tl | k2 tl | k2 tl | c tl]; try reflexivity.
        -- destruct (N.leb 2 kx) eqn:Hbel; [| reflexivity].
           apply N.leb_le in Hbel.
           rewrite IH, pushCL_spec, pushXRawL_spec; cbn [encCL encL N.mul].
           rewrite repX_0, <- repX_add.
           replace (3 + (kx - 2)) with (kx + 1) by lia; reflexivity.
        -- destruct (N.eqb (firstM c) 0) eqn:Hfm; [| reflexivity].
           apply N.eqb_eq in Hfm; rewrite firstM_eq_splitFirst in Hfm.
           pose proof (splitFirst_spec c (encL tl)) as Hsp.
           rewrite Hfm in Hsp.
           destruct (splitFirst c) as [m0 [c' | ]]; cbn [snd] in Hsp.
           ++ rewrite IH, pushDL0RawL1_spec, pushCL_spec; cbn [encL N.mul] in Hsp |- *.
              rewrite Hsp, repX_0, repDL0_1, repY_2; reflexivity.
           ++ rewrite IH, pushDL0RawL1_spec; cbn [encL N.mul] in Hsp |- *.
              rewrite Hsp, repX_0, repDL0_1, repY_2; reflexivity.
      * destruct (N.eqb ky 1) eqn:Hky1; [| reflexivity].
        apply N.eqb_eq in Hky1; subst ky.
        destruct l1 as [| k2 tl | k2 tl | kx tl | k2 tl | k2 tl | k2 tl | c tl]; try reflexivity.
        destruct (N.leb 6 kx) eqn:H6.
        -- apply N.leb_le in H6.
           rewrite IH, pushULRawL1_spec, pushXRawL_spec; cbn [encL].
           rewrite repUL_1, <- repX_add.
           replace (7 + (kx - 6)) with (kx + 1) by lia; reflexivity.
        -- destruct (N.leb 2 kx) eqn:H2; [| reflexivity].
           apply N.leb_le in H2.
           rewrite IH, pushDL0RawL1_spec, pushXRawL_spec; cbn [encL].
           rewrite repDL0_1, <- repX_add.
           replace (3 + (kx - 2)) with (kx + 1) by lia; reflexivity.
Qed.

Lemma coalesceL_spec (ls : LSide) : encL (coalesceL ls) = encL ls.
Proof. exact (coalesceLAux_spec 3%nat ls). Qed.

Lemma pushXL_spec (cnt : N) (ls : LSide) :
  encL (pushXL cnt ls) = repX cnt (encL ls).
Proof.
  unfold pushXL; destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite repX_0; reflexivity.
  - rewrite coalesceL_spec, pushXRawL_spec; reflexivity.
Qed.

Lemma pushXL1_spec (ls : LSide) : encL (pushXL1 ls) = repX 1 (encL ls).
Proof. unfold pushXL1; rewrite coalesceL_spec, pushXRawL1_spec; reflexivity. Qed.

Lemma pushXL2_spec (ls : LSide) : encL (pushXL2 ls) = repX 2 (encL ls).
Proof. unfold pushXL2; rewrite coalesceL_spec, pushXRawL2_spec; reflexivity. Qed.

Lemma pushYL1_spec (ls : LSide) : encL (pushYL1 ls) = repY 1 (encL ls).
Proof. unfold pushYL1; rewrite coalesceL_spec, pushYRawL1_spec; reflexivity. Qed.

Lemma Pos_iter_pushYL1_spec (p : positive) (ls : LSide) :
  encL (Pos.iter pushYL1 ls p) = repYn (Pos.to_nat p) (encL ls).
Proof.
  induction p as [| p' IHp] using Pos.peano_ind.
  - cbn [Pos.iter Pos.to_nat repYn]; rewrite pushYL1_spec, repY_1; reflexivity.
  - rewrite Pos.iter_succ, Pos2Nat.inj_succ, pushYL1_spec, IHp, repY_1; cbn [repYn]; reflexivity.
Qed.

Lemma pushYL_spec (n : N) (ls : LSide) : encL (pushYL n ls) = repY n (encL ls).
Proof.
  destruct n as [| p]; [rewrite repY_0; reflexivity | exact (Pos_iter_pushYL1_spec p ls)].
Qed.

Lemma normTopL_spec (ls : LSide) : encL (normTopL ls) = encL ls.
Proof.
  unfold normTopL.
  destruct ls as [| k tl | k1 l1 | k tl | k tl | k tl | k tl | t tl]; try reflexivity.
  destruct (N.eqb k1 1) eqn:Hk1.
  - apply N.eqb_eq in Hk1; subst k1.
    destruct l1 as [| kb0 tl | k2 l2 | k2 l2 | k2 l2 | k2 l2 | k2 l2 | t2 l2]; try reflexivity.
    rewrite pushXL1_spec, pushB0L_spec; cbn [encL N.add].
    rewrite rep1_2, repX_1; replace (kb0 + 1) with (1 + kb0) by lia; rewrite rep0_add, rep0_1; reflexivity.
  - destruct (N.eqb k1 0) eqn:Hk0; [| reflexivity].
    apply N.eqb_eq in Hk0; subst k1.
    destruct l1 as [| k2 l2 | k2 l2 | k2 l2 | k2 l2 | k2 l2 | k2 l2 | t2 l2]; try reflexivity.
    destruct (N.eqb k2 1) eqn:Hk2; [| reflexivity].
    apply N.eqb_eq in Hk2; subst k2.
    destruct l2 as [| k3 l3 | k3 l3 | k3 l3 | k3 l3 | k3 l3 | k3 l3 | t3 l3]; try reflexivity.
    destruct (N.eqb k3 0) eqn:Hk3; [| reflexivity].
    apply N.eqb_eq in Hk3; subst k3.
    destruct l3 as [| kb0 tl | k4 l4 | k4 l4 | k4 l4 | k4 l4 | k4 l4 | t4 l4]; try reflexivity.
    rewrite pushYL1_spec, pushB0L_spec; cbn [encL N.add].
    rewrite rep1_1, rep0_2, repY_1; replace (kb0 + 1) with (1 + kb0) by lia; rewrite rep0_add, rep0_1; reflexivity.
Qed.

Lemma pushBitL1_spec (ls : LSide) : encL (pushBitL1 ls) = S1 >> encL ls.
Proof. unfold pushBitL1; rewrite normTopL_spec, pushB1RawL1_spec; reflexivity. Qed.

Lemma popBitL_spec (ls : LSide) :
  encL ls = (if fst (popBitL ls) then S1 else S0) >> encL (snd (popBitL ls)).
Proof.
  destruct ls as [| k tl | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [popBitL].
  - cbn [fst snd encL]; apply const_unfold.
  - destruct (N.eqb k 0) eqn:H0; cbn [fst snd encL].
    + apply N.eqb_eq in H0; subst k; rewrite rep0_1; reflexivity.
    + apply N.eqb_neq in H0; replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite rep0_add, rep0_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; cbn [fst snd encL].
    + apply N.eqb_eq in H0; subst k; rewrite rep1_1; reflexivity.
    + apply N.eqb_neq in H0; replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite rep1_add, rep1_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; cbn [fst snd encL].
    + apply N.eqb_eq in H0; subst k; rewrite pushBitL1_spec, pushB0L1_spec, repX_1; reflexivity.
    + apply N.eqb_neq in H0; rewrite rep1_1, rep0_1.
      replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite repX_add, repX_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; cbn [fst snd encL].
    + apply N.eqb_eq in H0; subst k; rewrite !pushB0L1_spec, pushBitL1_spec, pushB0L1_spec, repY_1; reflexivity.
    + apply N.eqb_neq in H0; rewrite rep0_2, rep1_1, rep0_1.
      replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite repY_add, repY_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; cbn [fst snd encL].
    + apply N.eqb_eq in H0; subst k; rewrite rep0_2, rep1_1, rep0_1, repY_1, pushXRawL3_spec, repDL0_1, repY_2, repY_1; reflexivity.
    + apply N.eqb_neq in H0; rewrite rep0_2, rep1_1, rep0_1, repY_1.
      replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite repDL0_add, repDL0_1, repY_2, repY_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; cbn [fst snd encL].
    + apply N.eqb_eq in H0; subst k; rewrite rep0_2, rep1_1, rep0_1, repY_1, pushXRawL_spec, repUL_1, repY_2, repY_1; reflexivity.
    + apply N.eqb_neq in H0; rewrite rep0_2, rep1_1, rep0_1, repY_1.
      replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite repUL_add, repUL_1, repY_2, repY_1; reflexivity.
  - pose proof (splitFirst_spec t (encL tl)) as Hsp.
    destruct (splitFirst t) as [m0 [c' | ]]; cbn [fst snd] in Hsp |- *.
    + destruct (N.eqb m0 0) eqn:Hm0; cbn [fst snd encL].
      * apply N.eqb_eq in Hm0; subst m0; cbn [N.mul] in Hsp.
        rewrite Hsp, repX_0, rep0_2, rep1_1, rep0_1, pushXRawL3_spec; cbn [encL]; rewrite repY_1; reflexivity.
      * apply N.eqb_neq in Hm0.
        rewrite Hsp, rep1_1, rep0_1, pushXRawL_spec;
        cbn [encL]; rewrite pushXRawL3_spec; cbn [encL].
        replace (2 * m0) with (1 + (2 * (m0 - 1) + 1)) by lia; rewrite repX_add, repX_1; reflexivity.
    + destruct (N.eqb m0 0) eqn:Hm0; cbn [fst snd encL].
      * apply N.eqb_eq in Hm0; subst m0; cbn [N.mul] in Hsp.
        rewrite Hsp, repX_0, rep0_2, rep1_1, rep0_1, pushXRawL3_spec, repY_1; reflexivity.
      * apply N.eqb_neq in Hm0.
        rewrite Hsp, rep1_1, rep0_1, pushXRawL_spec; cbn [encL]; rewrite pushXRawL3_spec.
        replace (2 * m0) with (1 + (2 * (m0 - 1) + 1)) by lia; rewrite repX_add, repX_1; reflexivity.
Qed.

Lemma pushB0R1_spec (wt : side) (rs : RSide) :
  encR wt (pushB0R1 rs) = S0 >> encR wt rs.
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushB0R1 encR];
    try (rewrite rep0_1; reflexivity).
  - apply const_unfold.
  - replace (k + 1 + 1) with (1 + (k + 1)) by lia; rewrite rep0_add, rep0_1; reflexivity.
Qed.

Lemma pushOR_spec (wt : side) (cnt : N) (rs : RSide) :
  encR wt (pushOR cnt rs) = rep1 cnt (encR wt rs).
Proof.
  unfold pushOR; destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite rep1_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [encR];
      try (f_equal; lia).
    replace (k + cnt + 1) with (cnt + (k + 1)) by lia; apply rep1_add.
Qed.

Lemma pushOR1_spec (wt : side) (rs : RSide) : encR wt (pushOR1 rs) = rep1 1 (encR wt rs).
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushOR1 encR]; try reflexivity.
  replace (k + 1 + 1) with (1 + (k + 1)) by lia; apply rep1_add.
Qed.

Lemma pushOR2_spec (wt : side) (rs : RSide) : encR wt (pushOR2 rs) = rep1 2 (encR wt rs).
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushOR2 encR]; try reflexivity.
  replace (k + 2 + 1) with (2 + (k + 1)) by lia; apply rep1_add.
Qed.

Lemma pushOR3_spec (wt : side) (rs : RSide) : encR wt (pushOR3 rs) = rep1 3 (encR wt rs).
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushOR3 encR]; try reflexivity.
  replace (k + 3 + 1) with (3 + (k + 1)) by lia; apply rep1_add.
Qed.

Lemma pushOR4_spec (wt : side) (rs : RSide) : encR wt (pushOR4 rs) = rep1 4 (encR wt rs).
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushOR4 encR]; try reflexivity.
  replace (k + 4 + 1) with (4 + (k + 1)) by lia; apply rep1_add.
Qed.

Lemma pushOR6_spec (wt : side) (rs : RSide) : encR wt (pushOR6 rs) = rep1 6 (encR wt rs).
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushOR6 encR]; try reflexivity.
  replace (k + 6 + 1) with (6 + (k + 1)) by lia; apply rep1_add.
Qed.

Lemma pushOR8_spec (wt : side) (rs : RSide) : encR wt (pushOR8 rs) = rep1 8 (encR wt rs).
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [pushOR8 encR]; try reflexivity.
  replace (k + 8 + 1) with (8 + (k + 1)) by lia; apply rep1_add.
Qed.

Lemma pushZR_spec (wt : side) (cnt : N) (rs : RSide) :
  encR wt (pushZR cnt rs) = repZ cnt (encR wt rs).
Proof.
  unfold pushZR; destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite repZ_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [encR];
      try (f_equal; lia).
    replace (k + cnt + 1) with (cnt + (k + 1)) by lia; apply repZ_add.
Qed.

Lemma pushDR0R_spec (wt : side) (cnt : N) (rs : RSide) :
  encR wt (pushDR0R cnt rs) = repDR0 cnt (encR wt rs).
Proof.
  unfold pushDR0R; destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite repDR0_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [encR];
      try (f_equal; lia).
    replace (k + cnt + 1) with (cnt + (k + 1)) by lia; apply repDR0_add.
Qed.

Lemma pushURR_spec (wt : side) (cnt : N) (rs : RSide) :
  encR wt (pushURR cnt rs) = repUR cnt (encR wt rs).
Proof.
  unfold pushURR; destruct (N.eqb cnt 0) eqn:H0.
  - apply N.eqb_eq in H0; subst cnt; rewrite repUR_0; reflexivity.
  - apply N.eqb_neq in H0.
    destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [encR];
      try (f_equal; lia).
    replace (k + cnt + 1) with (cnt + (k + 1)) by lia; apply repUR_add.
Qed.

Lemma pushCRR_spec (wt : side) (c : CTree) (rs : RSide) :
  encR wt (pushCRR c rs) = encCR c (encR wt rs).
Proof.
  destruct rs; reflexivity.
Qed.

Lemma popBitR_spec (wt : side) (rs : RSide) (b : bool) (rs' : RSide) :
  popBitR rs = Some (b, rs') ->
  encR wt rs = (if b then S1 else S0) >> encR wt rs'.
Proof.
  destruct rs as [| | k tl | k tl | k tl | k tl | k tl | t tl]; cbn [popBitR]; intro H.
  - inversion H; subst; cbn [encR]; apply const_unfold.
  - discriminate.
  - destruct (N.eqb k 0) eqn:H0; inversion H; subst; clear H; cbn [encR].
    + apply N.eqb_eq in H0; subst k; rewrite rep0_1; reflexivity.
    + apply N.eqb_neq in H0; replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite rep0_add, rep0_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; inversion H; subst; clear H; cbn [encR].
    + apply N.eqb_eq in H0; subst k; rewrite rep1_1; reflexivity.
    + apply N.eqb_neq in H0; replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite rep1_add, rep1_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; inversion H; subst; clear H; cbn [encR].
    + apply N.eqb_eq in H0; subst k; rewrite repZ_1, rep1_4, pushB0R1_spec; reflexivity.
    + apply N.eqb_neq in H0; rewrite rep1_4, rep0_1.
      replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite repZ_add, repZ_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; inversion H; subst; clear H; cbn [encR].
    + apply N.eqb_eq in H0; subst k; rewrite rep0_1, pushOR3_spec, repDR0_1; reflexivity.
    + apply N.eqb_neq in H0; rewrite !rep0_1.
      replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite repDR0_add, repDR0_1; reflexivity.
  - destruct (N.eqb k 0) eqn:H0; inversion H; subst; clear H; cbn [encR].
    + apply N.eqb_eq in H0; subst k; rewrite rep0_1, pushOR3_spec, repUR_1; reflexivity.
    + apply N.eqb_neq in H0; rewrite !rep0_1.
      replace (k + 1) with (1 + (k - 1 + 1)) by lia; rewrite repUR_add, repUR_1; reflexivity.
  - pose proof (splitLast_spec t (encR wt tl)) as Hsp.
    destruct (splitLast t) as [[c' | ] m0]; cbn [fst snd] in Hsp; inversion H; subst; clear H.
    + cbn [encR]; rewrite Hsp, rep0_1, pushZR_spec, pushOR4_spec, pushCRR_spec, rep1_9, rep1_8; reflexivity.
    + cbn [encR]; rewrite Hsp, rep0_1, pushZR_spec, pushOR4_spec, rep1_9, rep1_8; reflexivity.
Qed.

(** ** Section 4: Parametric TM Macro Accelerations & Right-Wall Bounce (Lemma 1) *)

Ltac fast_steps :=
  intros;
  repeat match goal with
  | |- _ -[ _ ]->* _ =>
    solve [apply evstep_refl'; reflexivity] ||
    (eapply evstep_step; [prove_step | simpl_tape])
  end.

Ltac fast_plus :=
  intros; eapply progress_intro; [prove_step | simpl_tape]; fast_steps.

Lemma stream_eta2 (r : side) :
  Streams.hd r = S1 -> Streams.hd (Streams.tl r) = S1 -> r = S1 >> S1 >> Streams.tl (Streams.tl r).
Proof.
  intros H1 H2; destruct r as [x0 [x1 r2]]; cbn [Streams.hd Streams.tl] in H1, H2 |- *; subst x0 x1; reflexivity.
Qed.

Lemma entry_step_init :
  c0 -[ tm ]->* encCfg (const S0) false (LB1 0 LNil) RNil.
Proof.
  unfold c0, tape0, encCfg; cbn [encL encR N.add]; rewrite rep1_1; fast_steps.
Qed.

Lemma tm_sweep_Z1 (l r : side) :
  l {{B}}> (repZn 1 r) -[ tm ]->* (repXn 2 l) {{B}}> r.
Proof. cbn [repZn repXn]; fast_steps. Qed.

Lemma tm_sweep_Zn (k : nat) :
  forall l r : side,
    l {{B}}> (repZn k r) -[ tm ]->* (repXn (2 * k) l) {{B}}> r.
Proof.
  induction k as [| k' IH]; intros l r.
  - cbn [repZn Nat.mul repXn]; finish.
  - change (repZn (S k') r) with (repZn 1 (repZn k' r)).
    eapply evstep_trans; [apply tm_sweep_Z1 | ].
    eapply evstep_trans; [apply IH | ].
    rewrite <- repXn_add; replace (2 * k' + 2)%nat with (2 * S k')%nat by lia; finish.
Qed.

Lemma tm_sweep_Z (k : N) (l r : side) :
  l {{B}}> (repZ k r) -[ tm ]->* (repX (2 * k) l) {{B}}> r.
Proof.
  unfold repZ, repX; replace (N.to_nat (2 * k)) with (2 * N.to_nat k)%nat by lia.
  apply tm_sweep_Zn.
Qed.

Lemma tm_sweep_Z_plus (k : N) (l r : side) :
  1 <= k ->
  l {{B}}> (repZ k r) -[ tm ]->+ (repX (2 * k) l) {{B}}> r.
Proof.
  intro Hk.
  assert (Hstep1 : forall l0 r0 : side, l0 {{B}}> (repZn 1 r0) -[ tm ]->+ (repXn 2 l0) {{B}}> r0).
  { intros l0 r0; cbn [repZn repXn]; fast_plus. }
  unfold repZ, repX.
  destruct (N.to_nat k) as [| k'] eqn:Hkn; [lia | ].
  change (repZn (S k') r) with (repZn 1 (repZn k' r)).
  eapply progress_evstep_trans; [apply Hstep1 | ].
  eapply evstep_trans; [apply tm_sweep_Zn | ].
  rewrite <- repXn_add; replace (2 * k' + 2)%nat with (N.to_nat (2 * k)) by lia; finish.
Qed.

Lemma tm_sweep_O1 (l r0 : side) :
  l {{B}}> (S1 >> S1 >> S1 >> S1 >> S1 >> r0) -[ tm ]->* (repXn 1 l) {{B}}> (S1 >> S1 >> r0).
Proof. cbn [repXn]; fast_steps. Qed.

Lemma tm_sweep_On (q : nat) :
  forall (r : side), Streams.hd r = S1 -> Streams.hd (Streams.tl r) = S1 ->
  forall l : side,
    l {{B}}> (rep1n (3 * q) r) -[ tm ]->* (repXn q l) {{B}}> r.
Proof.
  induction q as [| q' IH]; intros r H1 H2 l.
  - cbn [Nat.mul rep1n repXn]; finish.
  - replace (3 * S q')%nat with (3 + 3 * q')%nat by lia.
    rewrite rep1n_add.
    assert (Hr2 : exists r0, rep1n (3 * q') r = S1 >> S1 >> r0).
    { destruct q' as [| q''].
      - exists (Streams.tl (Streams.tl r)); cbn [Nat.mul rep1n]; exact (stream_eta2 r H1 H2).
      - replace (3 * S q'')%nat with (2 + (3 * q'' + 1))%nat by lia.
        rewrite rep1n_add; exists (rep1n (3 * q'' + 1) r); reflexivity. }
    destruct Hr2 as [r0 Hr0].
    eapply evstep_trans.
    + cbn [rep1n]; rewrite Hr0; apply tm_sweep_O1.
    + rewrite <- Hr0.
      eapply evstep_trans; [apply (IH r H1 H2 (repXn 1 l)) | ].
      rewrite <- repXn_add; replace (q' + 1)%nat with (S q') by lia; finish.
Qed.

Lemma tm_sweep_O (q : N) (r : side) :
  Streams.hd r = S1 -> Streams.hd (Streams.tl r) = S1 ->
  forall l : side,
    l {{B}}> (rep1 (3 * q) r) -[ tm ]->* (repX q l) {{B}}> r.
Proof.
  intros H1 H2 l; unfold rep1, repX.
  replace (N.to_nat (3 * q)) with (3 * N.to_nat q)%nat by lia.
  exact (tm_sweep_On (N.to_nat q) r H1 H2 l).
Qed.

Lemma tm_left_X2_step (l r : side) :
  (S1 >> repXn 2 l) {{B}}> (S0 >> r) -[ tm ]->*
  (S1 >> l) {{B}}> (S0 >> S1 >> S1 >> S1 >> S0 >> S1 >> S1 >> r).
Proof. cbn [repXn]; fast_steps. Qed.

Lemma tm_left_X2n (q : nat) :
  forall l r : side,
    (S1 >> repXn (2 * (q + 1)) l) {{B}}> (S0 >> r) -[ tm ]->*
    (S1 >> l) {{B}}> (S0 >> S1 >> S1 >> S1 >> S0 >> repZn q (S1 >> S1 >> r)).
Proof.
  induction q as [| q' IH]; intros l r.
  - cbn [Nat.add Nat.mul repZn]; apply tm_left_X2_step.
  - replace (2 * (S q' + 1))%nat with (2 + 2 * (q' + 1))%nat by lia.
    rewrite repXn_add.
    eapply evstep_trans; [apply tm_left_X2_step | ].
    eapply evstep_trans; [apply IH | ].
    change (S1 >> S1 >> S1 >> S1 >> S1 >> S0 >> S1 >> S1 >> r) with (repZn 1 (S1 >> S1 >> r)).
    rewrite <- repZn_add; replace (q' + 1)%nat with (S q') by lia; finish.
Qed.

Lemma tm_left_X2 (q : N) (l r : side) :
  (S1 >> repX (2 * (q + 1)) l) {{B}}> (S0 >> r) -[ tm ]->*
  (S1 >> l) {{B}}> (S0 >> S1 >> S1 >> S1 >> S0 >> repZ q (S1 >> S1 >> r)).
Proof.
  unfold repX, repZ.
  replace (N.to_nat (2 * (q + 1))) with (2 * (N.to_nat q + 1))%nat by lia.
  apply tm_left_X2n.
Qed.

Lemma tm_20_after_X2 (l r : side) :
  (S1 >> repY 1 (repX 3 l)) {{B}}> (S0 >> S1 >> S1 >> S1 >> S0 >> r) -[ tm ]->*
  (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (rep1 9 (S0 >> r)))).
Proof.
  unfold repY, repX, rep1; cbn [N.to_nat Pos.to_nat repYn repXn rep1n]; fast_steps.
Qed.

Lemma tm_20_after_X2_x2 (l r0 : side) :
  (S1 >> repX 2 (repY 1 (repX 3 l))) {{B}}> (S0 >> S1 >> S1 >> S1 >> S0 >> r0) -[ tm ]->*
  (S1 >> repX 2 l) {{B}}> (S0 >> S1 >> S1 >> rep1 9 (S0 >> S1 >> S1 >> S1 >> S1 >> S1 >> S0 >> r0)).
Proof.
  unfold repX, repY, rep1; cbn [N.to_nat Pos.to_nat repXn repYn rep1n]; fast_steps.
Qed.

Lemma tm_jump_left_ctree (t : CTree) :
  forall l r : side,
    (S1 >> repX 2 (encCL t l)) {{B}}> (S0 >> S1 >> S1 >> r) -[ tm ]->*
    (S1 >> repX 2 l) {{B}}> (S0 >> S1 >> S1 >> encCR t r).
Proof.
  induction t as [m | a IHa b IHb]; intros l r.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m; cbn [encCL encCR N.mul].
      unfold repX, repY, repZ, rep1; cbn [N.to_nat Pos.to_nat repXn repYn repZn rep1n]; fast_steps.
    + apply N.eqb_neq in Hm0; cbn [encCL encCR].
      rewrite <- repX_add.
      replace (2 + 2 * m) with (2 * ((m - 1) + 1) + 2) by lia.
      rewrite repX_add.
      eapply evstep_trans; [apply (tm_left_X2 (m - 1) (repX 2 (repY 1 (repX 3 l))) (S1 >> S1 >> r)) | ].
      change (S1 >> S1 >> S1 >> S1 >> r) with (rep1 4 r).
      eapply evstep_trans; [apply tm_20_after_X2_x2 | ].
      change (S1 >> S1 >> S1 >> S1 >> S1 >> S0 >> repZ (m - 1) (rep1 4 r)) with (repZ 1 (repZ (m - 1) (rep1 4 r))).
      rewrite <- repZ_add; replace (1 + (m - 1)) with m by lia; finish.
  - cbn [encCL encCR]; eapply evstep_trans; [apply IHa | apply IHb].
Qed.

Lemma tm_jump_left_ctree_direct (t : CTree) :
  forall l r : side,
    (S1 >> encCL t l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 r)) -[ tm ]->*
    (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encCR t r))).
Proof.
  induction t as [m | a IHa b IHb]; intros l r.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m; cbn [encCL encCR N.mul].
      unfold repX, repY, repZ, rep1; cbn [N.to_nat Pos.to_nat repXn repYn repZn rep1n]; fast_steps.
    + apply N.eqb_neq in Hm0; cbn [encCL encCR].
      replace (2 * m) with (2 * ((m - 1) + 1)) by lia.
      eapply evstep_trans; [apply (tm_left_X2 (m - 1) (repY 1 (repX 3 l)) (rep1 3 (S0 >> rep1 4 r))) | ].
      change (S1 >> S1 >> rep1 3 (S0 >> rep1 4 r)) with (repZ 1 (rep1 4 r)).
      rewrite <- repZ_add; replace (m - 1 + 1) with m by lia.
      apply tm_20_after_X2.
  - cbn [encCL encCR]; eapply evstep_trans; [apply IHa | apply IHb].
Qed.

Lemma tm_jump_right_ctree_mid (l r0 : side) :
  (repX 3 l) {{B}}> (rep1 4 (S0 >> r0)) -[ tm ]->*
  (repY 1 (repX 3 l)) {{B}}> r0.
Proof.
  unfold repX, repY, rep1; cbn [N.to_nat Pos.to_nat repXn repYn rep1n]; fast_steps.
Qed.

Lemma tm_jump_right_ctree (t : CTree) :
  forall l r : side,
    l {{B}}> (rep1 4 (encCR t r)) -[ tm ]->*
    (encCL t l) {{B}}> (rep1 4 r).
Proof.
  induction t as [m0 | a IHa b IHb]; intros l r.
  - cbn [encCR encCL].
    rewrite <- rep1_add; replace (4 + 9) with (3 * 3 + 4) by lia; rewrite rep1_add.
    eapply evstep_trans.
    + apply (tm_sweep_O 3 (rep1 4 (S0 >> repZ m0 (rep1 4 r)))); reflexivity.
    + eapply evstep_trans; [apply tm_jump_right_ctree_mid | apply tm_sweep_Z].
  - cbn [encCR encCL]; eapply evstep_trans; [apply IHb | apply IHa].
Qed.

Lemma tm_jump_left_dl0_1 (l r : side) :
  (S1 >> repXn 2 (repDL0n 1 l)) {{B}}> (S0 >> S1 >> S1 >> r) -[ tm ]->*
  (S1 >> repXn 2 l) {{B}}> (S0 >> S1 >> S1 >> repDR0n 1 r).
Proof.
  cbn [repDL0n repDR0n repYn repXn repZn rep1n]; fast_steps.
Qed.

Lemma tm_jump_left_dl0n (k : nat) :
  forall l r : side,
    (S1 >> repXn 2 (repDL0n k l)) {{B}}> (S0 >> S1 >> S1 >> r) -[ tm ]->*
    (S1 >> repXn 2 l) {{B}}> (S0 >> S1 >> S1 >> repDR0n k r).
Proof.
  induction k as [| k' IH]; intros l r.
  - cbn [repDL0n repDR0n]; finish.
  - change (repDL0n (S k') l) with (repDL0n 1 (repDL0n k' l)).
    eapply evstep_trans; [apply tm_jump_left_dl0_1 | ].
    eapply evstep_trans; [apply IH | ].
    rewrite <- repDR0n_add; replace (k' + 1)%nat with (S k') by lia; finish.
Qed.

Lemma tm_jump_left_dl0 (k : N) (l r : side) :
  (S1 >> repX 2 (repDL0 k l)) {{B}}> (S0 >> S1 >> S1 >> r) -[ tm ]->*
  (S1 >> repX 2 l) {{B}}> (S0 >> S1 >> S1 >> repDR0 k r).
Proof.
  unfold repX, repDL0, repDR0; cbn [N.to_nat Pos.to_nat]; apply tm_jump_left_dl0n.
Qed.

Lemma tm_jump_left_ul_1 (l r : side) :
  (S1 >> repXn 2 (repULn 1 l)) {{B}}> (S0 >> S1 >> S1 >> r) -[ tm ]->*
  (S1 >> repXn 2 l) {{B}}> (S0 >> S1 >> S1 >> repURn 1 r).
Proof.
  cbn [repULn repURn repYn repXn repZn rep1n]; fast_steps.
Qed.

Lemma tm_jump_left_uln (k : nat) :
  forall l r : side,
    (S1 >> repXn 2 (repULn k l)) {{B}}> (S0 >> S1 >> S1 >> r) -[ tm ]->*
    (S1 >> repXn 2 l) {{B}}> (S0 >> S1 >> S1 >> repURn k r).
Proof.
  induction k as [| k' IH]; intros l r.
  - cbn [repULn repURn]; finish.
  - change (repULn (S k') l) with (repULn 1 (repULn k' l)).
    eapply evstep_trans; [apply tm_jump_left_ul_1 | ].
    eapply evstep_trans; [apply IH | ].
    rewrite <- repURn_add; replace (k' + 1)%nat with (S k') by lia; finish.
Qed.

Lemma tm_jump_left_ul (k : N) (l r : side) :
  (S1 >> repX 2 (repUL k l)) {{B}}> (S0 >> S1 >> S1 >> r) -[ tm ]->*
  (S1 >> repX 2 l) {{B}}> (S0 >> S1 >> S1 >> repUR k r).
Proof.
  unfold repX, repUL, repUR; cbn [N.to_nat Pos.to_nat]; apply tm_jump_left_uln.
Qed.

Lemma tm_jump_right_dr0_3_base (l r : side) :
  l {{B}}> (rep1n 3 (repDR0n 1 r)) -[ tm ]->*
  (repYn 1 (repXn 3 (repYn 1 l))) {{B}}> (rep1n 3 r).
Proof.
  cbn [rep1n repDR0n repYn repXn repZn]; fast_steps.
Qed.

Lemma tm_jump_right_dr0_3n (k : nat) :
  forall l r : side,
    l {{B}}> (rep1n 3 (repDR0n (S k) r)) -[ tm ]->*
    (repYn 1 (repXn 3 (repDL0n k (repYn 1 l)))) {{B}}> (rep1n 3 r).
Proof.
  induction k as [| k' IH]; intros l r.
  - cbn [repDL0n]; apply tm_jump_right_dr0_3_base.
  - change (repDR0n (S (S k')) r) with (repDR0n 1 (repDR0n (S k') r)).
    eapply evstep_trans; [apply tm_jump_right_dr0_3_base | ].
    eapply evstep_trans; [apply IH | ].
    change (repYn 1 (repYn 1 (repXn 3 (repYn 1 l)))) with (repDL0n 1 (repYn 1 l)).
    rewrite <- repDL0n_add; replace (k' + 1)%nat with (S k') by lia; finish.
Qed.

Lemma tm_jump_right_dr0_3 (k : N) (l r : side) :
  l {{B}}> (rep1 3 (repDR0 (k + 1) r)) -[ tm ]->*
  (repY 1 (repX 3 (repDL0 k (repY 1 l)))) {{B}}> (rep1 3 r).
Proof.
  unfold rep1, repDR0, repY, repX, repDL0.
  replace (N.to_nat (k + 1)) with (S (N.to_nat k)) by lia.
  cbn [N.to_nat Pos.to_nat]; apply tm_jump_right_dr0_3n.
Qed.

Lemma tm_jump_right_dr0_4_base (l r : side) :
  l {{B}}> (rep1n 4 (repDR0n 1 r)) -[ tm ]->*
  (repYn 1 (repXn 3 (repXn 2 l))) {{B}}> (rep1n 3 r).
Proof.
  cbn [rep1n repDR0n repYn repXn repZn]; fast_steps.
Qed.

Lemma tm_jump_right_dr0_4 (k : N) (l r : side) :
  l {{B}}> (rep1 4 (repDR0 (k + 1) r)) -[ tm ]->*
  (repY 1 (repX 3 (repDL0 k (repX 2 l)))) {{B}}> (rep1 3 r).
Proof.
  unfold rep1, repDR0, repY, repX, repDL0.
  replace (N.to_nat (k + 1)) with (S (N.to_nat k)) by lia.
  cbn [N.to_nat Pos.to_nat].
  destruct (N.to_nat k) as [| k'].
  - cbn [repDL0n]; apply tm_jump_right_dr0_4_base.
  - change (repDR0n (S (S k')) r) with (repDR0n 1 (repDR0n (S k') r)).
    eapply evstep_trans; [apply tm_jump_right_dr0_4_base | ].
    eapply evstep_trans; [apply tm_jump_right_dr0_3n | ].
    change (repYn 1 (repYn 1 (repXn 3 (repXn 2 l)))) with (repDL0n 1 (repXn 2 l)).
    rewrite <- repDL0n_add; replace (k' + 1)%nat with (S k') by lia; finish.
Qed.

Lemma tm_jump_right_ur_3_base (l r : side) :
  l {{B}}> (rep1n 3 (repURn 1 r)) -[ tm ]->*
  (repYn 1 (repXn 7 (repYn 1 l))) {{B}}> (rep1n 3 r).
Proof.
  cbn [rep1n repURn repYn repXn repZn]; fast_steps.
Qed.

Lemma tm_jump_right_ur_3n (k : nat) :
  forall l r : side,
    l {{B}}> (rep1n 3 (repURn (S k) r)) -[ tm ]->*
    (repYn 1 (repXn 7 (repULn k (repYn 1 l)))) {{B}}> (rep1n 3 r).
Proof.
  induction k as [| k' IH]; intros l r.
  - cbn [repULn]; apply tm_jump_right_ur_3_base.
  - change (repURn (S (S k')) r) with (repURn 1 (repURn (S k') r)).
    eapply evstep_trans; [apply tm_jump_right_ur_3_base | ].
    eapply evstep_trans; [apply IH | ].
    change (repYn 1 (repYn 1 (repXn 7 (repYn 1 l)))) with (repULn 1 (repYn 1 l)).
    rewrite <- repULn_add; replace (k' + 1)%nat with (S k') by lia; finish.
Qed.

Lemma tm_jump_right_ur_3 (k : N) (l r : side) :
  l {{B}}> (rep1 3 (repUR (k + 1) r)) -[ tm ]->*
  (repY 1 (repX 7 (repUL k (repY 1 l)))) {{B}}> (rep1 3 r).
Proof.
  unfold rep1, repUR, repY, repX, repUL.
  replace (N.to_nat (k + 1)) with (S (N.to_nat k)) by lia.
  cbn [N.to_nat Pos.to_nat]; apply tm_jump_right_ur_3n.
Qed.

Lemma tm_jump_right_ur_4_base (l r : side) :
  l {{B}}> (rep1n 4 (repURn 1 r)) -[ tm ]->*
  (repYn 1 (repXn 7 (repXn 2 l))) {{B}}> (rep1n 3 r).
Proof.
  cbn [rep1n repURn repYn repXn repZn]; fast_steps.
Qed.

Lemma tm_jump_right_ur_4 (k : N) (l r : side) :
  l {{B}}> (rep1 4 (repUR (k + 1) r)) -[ tm ]->*
  (repY 1 (repX 7 (repUL k (repX 2 l)))) {{B}}> (rep1 3 r).
Proof.
  unfold rep1, repUR, repY, repX, repUL.
  replace (N.to_nat (k + 1)) with (S (N.to_nat k)) by lia.
  cbn [N.to_nat Pos.to_nat].
  destruct (N.to_nat k) as [| k'].
  - cbn [repULn]; apply tm_jump_right_ur_4_base.
  - change (repURn (S (S k')) r) with (repURn 1 (repURn (S k') r)).
    eapply evstep_trans; [apply tm_jump_right_ur_4_base | ].
    eapply evstep_trans; [apply tm_jump_right_ur_3n | ].
    change (repYn 1 (repYn 1 (repXn 7 (repXn 2 l)))) with (repULn 1 (repXn 2 l)).
    rewrite <- repULn_add; replace (k' + 1)%nat with (S k') by lia; finish.
Qed.

Lemma tm_jump_right_list (s : list N) :
  forall l r : side,
    l {{B}}> (rep1 4 (encCRList s r)) -[ tm ]->*
    (encCLList s l) {{B}}> (rep1 4 r).
Proof.
  induction s as [| m ms IH]; intros l r; cbn [encCRList encCLList].
  - finish.
  - eapply evstep_trans; [apply IH | apply (tm_jump_right_ctree (CLeaf m))].
Qed.

Lemma tm_jump_left_list_direct (s : list N) :
  forall l r : side,
    (S1 >> encCLList s l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 r)) -[ tm ]->*
    (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encCRList s r))).
Proof.
  induction s as [| m ms IH]; intros l r; cbn [encCLList encCRList].
  - finish.
  - eapply evstep_trans; [apply (tm_jump_left_ctree_direct (CLeaf m)) | apply IH].
Qed.

Lemma tm_wall_X4_O4_plus (m : side) :
  (repX 4 m) {{B}}> (rep1 4 (const S0)) -[ tm ]->+
  (S1 >> m) {{B}}> (S0 >> rep1 3 (S0 >> repZ 1 (rep1 8 (const S0)))).
Proof.
  unfold repX, rep1, repZ; cbn [N.to_nat Pos.to_nat repXn rep1n repZn]; fast_plus.
Qed.

Lemma tm_wall_X2_O8_plus (m : side) :
  (repX 2 m) {{B}}> (rep1 8 (const S0)) -[ tm ]->+
  (S1 >> m) {{B}}> (S0 >> rep1 3 (S0 >> repZ 1 (rep1 4 (const S0)))).
Proof.
  unfold repX, rep1, repZ; cbn [N.to_nat Pos.to_nat repXn rep1n repZn]; fast_plus.
Qed.

Lemma tm_wall_empty_0 (l : side) :
  (encCL (CLeaf 0) l) {{B}}> (rep1 4 (const S0)) -[ tm ]->+
  (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encRWall RWO12 (const S0)))).
Proof.
  cbn [encCL encRWall N.mul];
  unfold repX, repY, rep1; cbn [N.to_nat Pos.to_nat repXn repYn rep1n]; fast_plus.
Qed.

Lemma tm_wall_empty_1 (l : side) :
  (encCL (CLeaf 1) l) {{B}}> (rep1 4 (const S0)) -[ tm ]->+
  (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encRWall RWO908 (const S0)))).
Proof.
  cbn [encCL encRWall N.mul];
  unfold repX, repY, rep1; cbn [N.to_nat Pos.to_nat repXn repYn rep1n]; fast_plus.
Qed.

Lemma tm_wall_empty_ge2 (q : N) (l : side) :
  (encCL (CLeaf (q + 2)) l) {{B}}> (rep1 4 (const S0)) -[ tm ]->+
  (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encRWall (RWO90Z q) (const S0)))).
Proof.
  cbn [encCL encRWall].
  replace (2 * (q + 2)) with (4 + 2 * q) by lia.
  rewrite repX_add.
  eapply progress_evstep_trans; [apply tm_wall_X4_O4_plus | ].
  destruct (N.eqb q 0) eqn:Hq0.
  - apply N.eqb_eq in Hq0; subst q; cbn [N.mul N.add]; rewrite repX_0.
    apply tm_20_after_X2.
  - apply N.eqb_neq in Hq0.
    replace (2 * q) with (2 * ((q - 1) + 1)) by lia.
    eapply evstep_trans; [apply (tm_left_X2 (q - 1) (repY 1 (repX 3 l)) (rep1 3 (S0 >> repZ 1 (rep1 8 (const S0))))) | ].
    change (S1 >> S1 >> rep1 3 (S0 >> repZ 1 (rep1 8 (const S0)))) with (repZ 2 (rep1 8 (const S0))).
    rewrite <- repZ_add; replace (q - 1 + 2) with (q + 1) by lia.
    apply tm_20_after_X2.
Qed.

Lemma tm_wall_o908 (l : side) :
  l {{B}}> (rep1 4 (encRWall RWO908 (const S0))) -[ tm ]->+
  (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encCR (CLeaf 0) (const S0)))).
Proof.
  cbn [encRWall encCR];
  unfold rep1, repZ; cbn [N.to_nat Pos.to_nat rep1n repZn]; fast_plus.
Qed.

Lemma tm_wall_o90z (q : N) (l : side) :
  l {{B}}> (rep1 4 (encRWall (RWO90Z q) (const S0))) -[ tm ]->+
  (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encCR (CLeaf (q + 1)) (const S0)))).
Proof.
  cbn [encRWall encCR].
  rewrite <- rep1_add; replace (4 + 9) with (3 * 3 + 4) by lia; rewrite rep1_add.
  eapply evstep_progress_trans.
  - apply (tm_sweep_O 3 (rep1 4 (S0 >> repZ (q + 1) (rep1 8 (const S0))))); reflexivity.
  - eapply evstep_progress_trans; [apply tm_jump_right_ctree_mid | ].
    eapply evstep_progress_trans; [apply tm_sweep_Z | ].
    replace (2 * (q + 1)) with (2 + 2 * q) by lia; rewrite repX_add.
    eapply progress_evstep_trans; [apply tm_wall_X2_O8_plus | ].
    destruct (N.eqb q 0) eqn:Hq0.
    + apply N.eqb_eq in Hq0; subst q; cbn [N.mul N.add]; rewrite repX_0.
      apply tm_20_after_X2.
    + apply N.eqb_neq in Hq0.
      replace (2 * q) with (2 * ((q - 1) + 1)) by lia.
      eapply evstep_trans; [apply (tm_left_X2 (q - 1) (repY 1 (repX 3 l)) (rep1 3 (S0 >> repZ 1 (rep1 4 (const S0))))) | ].
      change (S1 >> S1 >> rep1 3 (S0 >> repZ 1 (rep1 4 (const S0)))) with (repZ 2 (rep1 4 (const S0))).
      rewrite <- repZ_add; replace (q - 1 + 2) with (q + 1) by lia.
      apply tm_20_after_X2.
Qed.

Lemma wall_bounce_plus (l : side) (s : list N) (w : RWallShape) :
  5 <= fuelRW s w ->
  l {{B}}> (rep1 4 (encWall s w)) -[ tm ]->+
  (S1 >> l) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encWall (fst (bounceRW (s, w))) (snd (bounceRW (s, w)))))).
Proof.
  intro Hfuel; destruct w as [ | | | q].
  - destruct s as [| m0 s'].
    + unfold fuelRW in Hfuel; cbn [fuelList fuelRWall] in Hfuel; lia.
    + unfold encWall; cbn [encCRList bounceRW].
      eapply evstep_progress_trans; [apply tm_jump_right_list | ].
      eapply evstep_progress_trans; [apply (tm_jump_right_ctree (CLeaf m0)) | ].
      cbn [encRWall].
      destruct (N.eqb m0 0) eqn:Hm0.
      * apply N.eqb_eq in Hm0; subst m0; cbn [fst snd].
        eapply progress_evstep_trans; [apply tm_wall_empty_0 | apply tm_jump_left_list_direct].
      * apply N.eqb_neq in Hm0.
        destruct (N.eqb m0 1) eqn:Hm1.
        -- apply N.eqb_eq in Hm1; subst m0; cbn [fst snd].
           eapply progress_evstep_trans; [apply tm_wall_empty_1 | apply tm_jump_left_list_direct].
        -- apply N.eqb_neq in Hm1; cbn [fst snd].
           replace m0 with ((m0 - 2) + 2) at 1 by lia.
           eapply progress_evstep_trans; [apply tm_wall_empty_ge2 | apply tm_jump_left_list_direct].
  - destruct s as [| m0 s'].
    + unfold fuelRW in Hfuel; cbn [fuelList fuelRWall] in Hfuel; lia.
    + unfold encWall; cbn [bounceRW fst snd encCRList].
      eapply evstep_progress_trans; [apply tm_jump_right_list | ].
      eapply evstep_progress_trans; [apply (tm_jump_right_ctree (CLeaf m0)) | ].
      cbn [encRWall].
      rewrite <- rep1_add; replace (4 + 12) with (3 * 4 + 4) by lia; rewrite rep1_add.
      eapply evstep_progress_trans.
      * apply (tm_sweep_O 4 (rep1 4 (const S0))); reflexivity.
      * assert (Hx4 : repX 4 (encCL (CLeaf m0) (encCLList s' l)) = encCL (CLeaf (m0 + 2)) (encCLList s' l)).
        { cbn [encCL]; rewrite <- repX_add; f_equal; lia. }
        rewrite Hx4.
        eapply progress_evstep_trans; [apply tm_wall_empty_ge2 | apply tm_jump_left_list_direct].
  - unfold encWall; cbn [bounceRW fst snd encCRList].
    eapply evstep_progress_trans; [apply tm_jump_right_list | ].
    eapply progress_evstep_trans; [apply tm_wall_o908 | ].
    cbn [encRWall]; apply tm_jump_left_list_direct.
  - unfold encWall; cbn [bounceRW fst snd encCRList].
    eapply evstep_progress_trans; [apply tm_jump_right_list | ].
    eapply progress_evstep_trans; [apply tm_wall_o90z | ].
    cbn [encRWall]; apply tm_jump_left_list_direct.
Qed.

Lemma wall_merge_bounce_plus (t : CTree) (lrest : side) (s : list N) (w : RWallShape) :
  5 <= fuelRW s w ->
  (encCL t lrest) {{B}}> (rep1 4 (encWall s w)) -[ tm ]->+
  (S1 >> lrest) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (encCR t (encWall (fst (bounceRW (s, w))) (snd (bounceRW (s, w))))))).
Proof.
  intro Hfuel.
  eapply progress_evstep_trans; [apply (wall_bounce_plus (encCL t lrest) s w Hfuel) | ].
  apply tm_jump_left_ctree_direct.
Qed.

(** ** Section 5: L1 Macro Stepper, Unified Wall-Reachability Soundness & Certificate *)

Ltac unfold_reps :=
  unfold rep0, rep1, repX, repY, repZ, repDL0, repUL, repDR0, repUR;
  cbn [N.add N.mul N.to_nat Pos.to_nat Pos.iter_op Init.Nat.add
       rep0n rep1n repXn repYn repZn repDL0n repULn repDR0n repURn].

Definition isConduitHeadL (ls : LSide) : bool :=
  match ls with
  | LC _ _ | LUL _ _ | LDL0 _ _ => true
  | _ => false
  end.

Definition stepAMicro (ls : LSide) (rs : RSide) (bnc : N) : MState :=
  match popBitL ls with
  | (false, l1) => ModeB (pushBitL1 l1) rs bnc
  | (true, LNil) => ModeB (LB1 0 LNil) (pushOR2 rs) bnc
  | (true, l1) =>
    match popBitL l1 with
    | (false, l2) => ModeA l2 (pushOR2 rs) bnc
    | (true, l2) => ModeA l2 (RB0 0 (pushOR1 rs)) bnc
    end
  end.

Definition stepBModeBR0 (ls : LSide) (r1 : RSide) (bnc : N) : MState :=
  match ls with
  | LB1 k1 l1 =>
    if N.eqb k1 0 then
      match l1 with
      | LC t lrest =>
        let '(m0, optC) := splitFirst t in
        let r2 := if N.eqb m0 0 then pushOR6 r1
                  else RO 8 (RB0 0 (pushZR (m0 - 1) (pushOR2 r1))) in
        let r3 := match optC with None => r2 | Some c' => pushCRR c' r2 end in
        ModeB (pushBitL1 lrest) (RB0 0 (RO 2 (RB0 0 (pushOR4 r3)))) bnc
      | LX kx lrest =>
        if N.leb 1 kx then
          let totX := kx + 1 in
          if andb (isConduitHeadL lrest) (andb (N.leb 3 kx) (N.eqb (N.modulo totX 2) 0)) then
            let qm1 := N.div (totX - 2) 2 - 1 in
            ModeB (LB1 0 (LX 1 lrest)) (RB0 0 (RO 2 (RB0 0 (pushZR qm1 (pushOR2 r1))))) bnc
          else
            let qm1 := N.div totX 2 - 1 in
            let remX := N.modulo totX 2 in
            ModeB (pushBitL1 (pushXL remX lrest)) (RB0 0 (RO 2 (RB0 0 (pushZR qm1 (pushOR2 r1))))) bnc
        else ModeA ls (pushOR1 r1) bnc
      | _ => ModeA ls (pushOR1 r1) bnc
      end
    else ModeA ls (pushOR1 r1) bnc
  | _ => ModeA ls (pushOR1 r1) bnc
  end.

Definition stepBMicro1 (ls : LSide) (rs : RSide) (bnc : N) : MState :=
  match popBitR rs with
  | None => MErr
  | Some (false, _) => MErr
  | Some (true, r1) =>
    match popBitR r1 with
    | None => MErr
    | Some (false, _) => MErr
    | Some (true, r2) =>
      match popBitR r2 with
      | None => MErr
      | Some (false, r3) => ModeB (pushXL1 ls) r3 bnc
      | Some (true, r3) =>
        match popBitR r3 with
        | None => MErr
        | Some (b4, r4) =>
          match popBitR r4 with
          | None => MErr
          | Some (b5, r5) =>
            if b4 then
              if b5 then ModeB (pushXL1 ls) (pushOR2 r5) bnc
              else ModeB (pushYL1 ls) r5 bnc
            else
              let r6 := if b5 then pushB0R1 r5 else pushOR1 r5 in
              ModeA ls (pushOR4 r6) bnc
          end
        end
      end
    end
  end.

Definition stepBModeBO (ls : LSide) (ko : N) (rrest : RSide) (bnc : N) : MState :=
  let ones := ko + 1 in
  let nextZ := match rrest with RNil | RB0 _ _ => true | _ => false end in
  if andb nextZ (andb (N.leb 1 ko) (N.eqb (N.modulo ones 3) 2)) then
    let qp1 := N.div (ones - 2) 3 + 1 in
    let r1 := match rrest with
              | RNil => RNil
              | RB0 kb tl => if N.eqb kb 0 then tl else RB0 (kb - 1) tl
              | _ => rrest
              end in
    ModeB (pushXL qp1 ls) r1 bnc
  else if andb nextZ (andb (N.leb 3 ko) (N.eqb (N.modulo ones 3) 1)) then
    let q := N.div (ones - 4) 3 in
    let r1 := match rrest with
              | RNil => RNil
              | RB0 kb tl => if N.eqb kb 0 then tl else RB0 (kb - 1) tl
              | _ => rrest
              end in
    ModeB (pushYL1 (pushXL q ls)) r1 bnc
  else if N.leb 4 ko then
    let q := N.div (ones - 2) 3 in
    let rem := ones - 3 * q in
    ModeB (pushXL q ls) (pushOR rem rrest) bnc
  else stepBMicro1 ls (RO ko rrest) bnc.

Definition stepBOnO6 (ls : LSide) (r1 : RSide) (bnc : N) : MState :=
  match r1 with
  | RB0 kb1 r2 =>
    if N.eqb kb1 0 then
      match r2 with
      | RO ko1 r3 =>
        if N.eqb ko1 3 then
          match r3 with
          | RB0 kb2 r4 =>
            if N.eqb kb2 0 then
              match r4 with
              | RZ kz rrest =>
                let cnt := 2 * (kz + 1) in
                ModeB (pushXL cnt (pushYL1 (pushYL1 (pushXL1 ls)))) rrest bnc
              | _ => stepBModeBO ls 6 r1 bnc
              end
            else stepBModeBO ls 6 r1 bnc
          | _ => stepBModeBO ls 6 r1 bnc
          end
        else stepBModeBO ls 6 r1 bnc
      | _ => stepBModeBO ls 6 r1 bnc
      end
    else stepBModeBO ls 6 r1 bnc
  | _ => stepBModeBO ls 6 r1 bnc
  end.

Definition stepA (ls : LSide) (rs : RSide) (bnc : N) : MState :=
  match ls with
  | LNil => ModeB (LB1 0 LNil) rs bnc
  | LB0 kv tl =>
    if N.eqb kv 0 then ModeB (pushBitL1 tl) rs bnc
    else ModeB (LB1 0 (LB0 (kv - 1) tl)) rs bnc
  | LX kv tl => ModeB (pushBitL1 (pushXRawL kv tl)) (RB0 0 (pushOR1 rs)) bnc
  | LY kv tl => ModeB (pushXL1 (pushYL kv tl)) (pushOR2 rs) bnc
  | LDL0 kv tl => ModeB (pushXL1 (pushYL1 (pushXL 3 (pushDL0RawL kv tl)))) (pushOR2 rs) bnc
  | LUL kv tl => ModeB (pushXL1 (pushYL1 (pushXL 7 (pushULRawL kv tl)))) (pushOR2 rs) bnc
  | LC t tl =>
    let '(m0, optC) := splitFirst t in
    let tl' := match optC with None => tl | Some c' => LC c' tl end in
    if N.eqb m0 0 then ModeB (pushXL 4 tl') (pushOR2 rs) bnc
    else
      let xcnt := 2 * (m0 - 1) + 1 in
      ModeB (LB1 0 (pushXRawL xcnt (LY 0 (pushXRawL3 tl')))) (RB0 0 (pushOR1 rs)) bnc
  | LB1 k1 l1 =>
    if N.eqb k1 0 then
      match l1 with
      | LY tkv tl =>
        if N.eqb tkv 0 then ModeA tl (pushOR6 rs) bnc
        else ModeB (pushXL1 (pushYL (tkv - 1) tl)) (pushOR8 rs) bnc
      | LDL0 tkv tl => ModeB (pushXL 4 (pushDL0RawL tkv tl)) (pushOR8 rs) bnc
      | LUL tkv tl => ModeB (pushXL 8 (pushULRawL tkv tl)) (pushOR8 rs) bnc
      | LX tkv tl =>
        if N.eqb tkv 0 then ModeA tl (RO 1 (RB0 0 (pushOR1 rs))) bnc
        else ModeB (pushBitL1 (pushXRawL (tkv - 1) tl)) (RB0 0 (RO 2 (RB0 0 (pushOR1 rs)))) bnc
      | _ => stepAMicro ls rs bnc
      end
    else stepAMicro ls rs bnc
  end.

Definition stepB (ls : LSide) (rs : RSide) (bnc : N) : MState :=
  match rs with
  | RNil => stepBModeBR0 ls RNil bnc
  | RWall => MErr
  | RB0 kb r1 =>
    if N.eqb kb 0 then
      match r1 with
      | RO ko rrest =>
        if N.leb 1 ko then
          match ls with
          | LB1 k1 l1 =>
            if N.eqb k1 0 then
              match l1 with
              | LX kx l2 =>
                if N.eqb kx 1 then
                  match l2 with
                  | LC t lrest =>
                    ModeB (pushBitL1 (pushXL2 lrest)) (RB0 0 (RO 1 (pushCRR t (pushOR (ko - 1) rrest)))) bnc
                  | LUL ku lrest =>
                    ModeB (pushBitL1 (pushXL2 lrest)) (RB0 0 (RO 1 (pushURR (ku + 1) (pushOR (ko - 1) rrest)))) bnc
                  | LDL0 kd lrest =>
                    ModeB (pushBitL1 (pushXL2 lrest)) (RB0 0 (RO 1 (pushDR0R (kd + 1) (pushOR (ko - 1) rrest)))) bnc
                  | _ => stepBModeBR0 ls r1 bnc
                  end
                else stepBModeBR0 ls r1 bnc
              | _ => stepBModeBR0 ls r1 bnc
              end
            else stepBModeBR0 ls r1 bnc
          | _ => stepBModeBR0 ls r1 bnc
          end
        else stepBModeBR0 ls r1 bnc
      | _ => stepBModeBR0 ls r1 bnc
      end
    else stepBModeBR0 ls (RB0 (kb - 1) r1) bnc
  | RZ rv rrest => ModeB (pushXL (2 * (rv + 1)) ls) rrest bnc
  | RO ko r1 =>
    if N.eqb ko 3 then
      match r1 with
      | RWall =>
        let bnc' := bnc + 1 in
        match ls with
        | LC t lrest => ModeB (pushBitL1 lrest) (RB0 0 (RO 2 (RB0 0 (RO 3 (RCR t RWall))))) bnc'
        | _ => ModeB (pushBitL1 ls) (RB0 0 (RO 2 (RB0 0 (RO 3 RWall)))) bnc'
        end
      | RCR t rrest => ModeB (coalesceL (pushCL t ls)) (pushOR4 rrest) bnc
      | RUR ku rrest => ModeB (pushYL1 (pushXL 7 (pushULRawL ku (pushXL2 ls)))) (pushOR3 rrest) bnc
      | RDR0 kd rrest => ModeB (pushYL1 (pushXL 3 (pushDL0RawL kd (pushXL2 ls)))) (pushOR3 rrest) bnc
      | _ => stepBModeBO ls 3 r1 bnc
      end
    else if N.eqb ko 2 then
      match r1 with
      | RUR ku rrest => ModeB (pushYL1 (pushXL 7 (pushULRawL ku (pushYL1 ls)))) (pushOR3 rrest) bnc
      | RDR0 kd rrest => ModeB (pushYL1 (pushXL 3 (pushDL0RawL kd (pushYL1 ls)))) (pushOR3 rrest) bnc
      | RB0 kb r2 =>
        if N.eqb kb 0 then
          match r2 with
          | RO ko2 rrest => ModeA ls (RO 3 (RB0 0 (pushOR ko2 rrest))) bnc
          | RZ kz rrest => ModeA ls (RO 3 (RB0 0 (RO 3 (RB0 0 (pushZR kz rrest))))) bnc
          | _ => stepBModeBO ls 2 r1 bnc
          end
        else stepBModeBO ls 2 r1 bnc
      | _ => stepBModeBO ls 2 r1 bnc
      end
    else if N.eqb ko 6 then stepBOnO6 ls r1 bnc
    else stepBModeBO ls ko r1 bnc
  | RDR0 _ _ | RUR _ _ | RCR _ _ => stepBMicro1 ls rs bnc
  end.

Definition stepOne (st : MState) : MState :=
  match st with
  | ModeA ls rs bnc => stepA ls rs bnc
  | ModeB ls rs bnc => stepB ls rs bnc
  | MErr => MErr
  end.

Definition ReachWallCore (isA1 : bool) (l1 : LSide) (r1 : RSide) (b1 : N)
    (isA2 : bool) (l2 : LSide) (r2 : RSide) (b2 : N) : Prop :=
  b1 <= b2 /\
  forall (s : list N) (w : RWallShape),
    (b1 < b2 -> (b2 - b1) + 4 <= fuelRW s w) ->
    let p := bounceRWIterNat (N.to_nat (b2 - b1)) (s, w) in
    if N.ltb b1 b2 then
      encCfg (encWall s w) isA1 l1 r1 -[ tm ]->+ encCfg (encWall (fst p) (snd p)) isA2 l2 r2
    else
      encCfg (encWall s w) isA1 l1 r1 -[ tm ]->* encCfg (encWall (fst p) (snd p)) isA2 l2 r2.

Definition ReachWall (isA1 : bool) (l1 : LSide) (r1 : RSide) (b1 : N) (st : MState) : Prop :=
  match st with
  | ModeA l2 r2 b2 => ReachWallCore isA1 l1 r1 b1 true l2 r2 b2
  | ModeB l2 r2 b2 => ReachWallCore isA1 l1 r1 b1 false l2 r2 b2
  | MErr => True
  end.

Definition ReachWallSt (st1 st2 : MState) : Prop :=
  match st1 with
  | ModeA l1 r1 b1 => ReachWall true l1 r1 b1 st2
  | ModeB l1 r1 b1 => ReachWall false l1 r1 b1 st2
  | MErr => st2 = MErr
  end.

Lemma ReachWallCore_refl (isA : bool) (l : LSide) (r : RSide) (b : N) :
  ReachWallCore isA l r b isA l r b.
Proof.
  split; [lia | intros s w _].
  rewrite N.ltb_irrefl, N.sub_diag; cbn [N.to_nat bounceRWIterNat fst snd].
  apply evstep_refl'; reflexivity.
Qed.

Lemma ReachWallCore_of_star {isA1 isA2 : bool} {l1 l2 : LSide} {r1 r2 : RSide} {b : N}
    (H : forall wt : side, encCfg wt isA1 l1 r1 -[ tm ]->* encCfg wt isA2 l2 r2) :
  ReachWallCore isA1 l1 r1 b isA2 l2 r2 b.
Proof.
  split; [lia | intros s w _].
  rewrite N.ltb_irrefl, N.sub_diag; cbn [N.to_nat bounceRWIterNat fst snd].
  exact (H (encWall s w)).
Qed.

Lemma ReachWallCore_of_bounce {l1 l2 : LSide} {r1 r2 : RSide} {b : N}
    (H : forall (s : list N) (w : RWallShape),
      5 <= fuelRW s w ->
      encCfg (encWall s w) false l1 r1 -[ tm ]->+
      encCfg (encWall (fst (bounceRW (s, w))) (snd (bounceRW (s, w)))) false l2 r2) :
  ReachWallCore false l1 r1 b false l2 r2 (b + 1).
Proof.
  split; [lia | intros s w Hf].
  assert (Hlt : b < b + 1) by lia.
  assert (Hltb : N.ltb b (b + 1) = true) by (apply N.ltb_lt; lia).
  rewrite Hltb.
  replace (N.to_nat (b + 1 - b)) with 1%nat by lia.
  cbn [bounceRWIterNat].
  apply H; specialize (Hf Hlt); lia.
Qed.

Lemma ReachWallCore_trans {a1 a2 a3 : bool} {l1 l2 l3 : LSide} {r1 r2 r3 : RSide} {b1 b2 b3 : N}
    (H1 : ReachWallCore a1 l1 r1 b1 a2 l2 r2 b2)
    (H2 : ReachWallCore a2 l2 r2 b2 a3 l3 r3 b3) :
  ReachWallCore a1 l1 r1 b1 a3 l3 r3 b3.
Proof.
  destruct H1 as [Hle1 Hr1], H2 as [Hle2 Hr2].
  split; [lia | intros s w Hf].
  destruct (N.ltb_spec0 b1 b2) as [Hlt1 | Hnlt1].
  - assert (Hlt13 : b1 < b3) by lia.
    assert (Hltb13 : N.ltb b1 b3 = true) by (apply N.ltb_lt; lia).
    cbv zeta; rewrite Hltb13.
    assert (Hf13 : (b3 - b1) + 4 <= fuelRW s w) by (apply Hf; lia).
    assert (Hf12 : (b2 - b1) + 4 <= fuelRW s w) by lia.
    pose proof (Hr1 s w (fun _ => Hf12)) as Hs1; cbv zeta in Hs1.
    destruct (bounceRWIterNat (N.to_nat (b2 - b1)) (s, w)) as [s1 w1] eqn:Hp1.
    cbn [fst snd] in Hs1.
    assert (Hfn12 : N.of_nat (N.to_nat (b2 - b1)) + 4 <= fuelRW s w) by lia.
    pose proof (fuelRW_bounceRWIterNat (N.to_nat (b2 - b1)) s w Hfn12) as Hfuel1.
    rewrite Hp1 in Hfuel1; cbn [fst snd] in Hfuel1.
    assert (Hiter : bounceRWIterNat (N.to_nat (b3 - b2)) (s1, w1) =
                    bounceRWIterNat (N.to_nat (b3 - b1)) (s, w)).
    { rewrite <- Hp1, bounceRWIterNat_add; f_equal; lia. }
    destruct (N.ltb_spec0 b2 b3) as [Hlt2 | Hnlt2].
    + assert (Hf23 : (b3 - b2) + 4 <= fuelRW s1 w1) by lia.
      pose proof (Hr2 s1 w1 (fun _ => Hf23)) as Hs2; cbv zeta in Hs2.
      rewrite Hiter in Hs2.
      exact (progress_trans _ _ _ _ Hs1 Hs2).
    + pose proof (Hr2 s1 w1 (fun H => False_ind _ (Hnlt2 H))) as Hs2; cbv zeta in Hs2.
      rewrite Hiter in Hs2.
      exact (progress_evstep_trans _ _ _ _ Hs1 Hs2).
  - pose proof (Hr1 s w (fun H => False_ind _ (Hnlt1 H))) as Hs1; cbv zeta in Hs1.
    assert (Heq12 : b1 = b2) by lia; subst b2.
    rewrite N.sub_diag in Hs1; cbn [N.to_nat bounceRWIterNat fst snd] in Hs1.
    pose proof (Hr2 s w Hf) as Hs2; cbv zeta in Hs2 |- *.
    destruct (N.ltb b1 b3).
    + exact (evstep_progress_trans _ _ _ _ Hs1 Hs2).
    + exact (evstep_trans _ _ _ _ Hs1 Hs2).
Qed.

Lemma ReachWallSt_trans (st1 st2 st3 : MState) :
  ReachWallSt st1 st2 -> ReachWallSt st2 st3 -> ReachWallSt st1 st3.
Proof.
  destruct st1 as [l1 r1 b1 | l1 r1 b1 | ],
           st2 as [l2 r2 b2 | l2 r2 b2 | ],
           st3 as [l3 r3 b3 | l3 r3 b3 | ];
    cbn [ReachWallSt ReachWall]; intros H1 H2;
    try exact I; try discriminate; try reflexivity;
    exact (ReachWallCore_trans H1 H2).
Qed.

Lemma stepAMicro_sound (ls : LSide) (rs : RSide) (bnc : N) :
  ReachWall true ls rs bnc (stepAMicro ls rs bnc).
Proof.
  unfold stepAMicro.
  pose proof (popBitL_spec ls) as Hl1.
  destruct (popBitL ls) as [b1 l1]; cbn [fst snd] in Hl1.
  destruct b1.
  - assert (Hnonnil : ReachWall true ls rs bnc
      (match popBitL l1 with
       | (false, l2) => ModeA l2 (pushOR2 rs) bnc
       | (true, l2) => ModeA l2 (RB0 0 (pushOR1 rs)) bnc
       end)).
    { pose proof (popBitL_spec l1) as Hl2.
      destruct (popBitL l1) as [[|] l2]; cbn [fst snd] in Hl2; cbn [ReachWall];
        apply ReachWallCore_of_star; intro wt; unfold encCfg;
        rewrite Hl1, Hl2; cbn [encR];
        rewrite ?pushOR2_spec, ?pushOR1_spec; unfold_reps; fast_steps. }
    destruct l1; try exact Hnonnil.
    cbn [ReachWall]; apply ReachWallCore_of_star; intro wt; unfold encCfg.
    rewrite Hl1; cbn [encL]; rewrite pushOR2_spec; unfold_reps; fast_steps.
  - cbn [ReachWall]; apply ReachWallCore_of_star; intro wt; unfold encCfg.
    rewrite Hl1, pushBitL1_spec; fast_steps.
Qed.

Lemma stepA_sound (ls : LSide) (rs : RSide) (bnc : N) :
  ReachWall true ls rs bnc (stepA ls rs bnc).
Proof.
  destruct ls as [| kv tl | k1 l1 | kv tl | kv tl | kv tl | kv tl | t tl].
  - cbn [stepA ReachWall]; apply ReachWallCore_of_star; intro wt; unfold encCfg; cbn [encL]; unfold_reps; fast_steps.
  - cbn [stepA]; destruct (N.eqb kv 0) eqn:H0.
    + apply N.eqb_eq in H0; subst kv; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
      unfold encCfg; cbn [encL]; rewrite pushBitL1_spec; unfold_reps; fast_steps.
    + apply N.eqb_neq in H0; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
      unfold encCfg; cbn [encL]; replace (kv + 1) with (1 + (kv - 1 + 1)) by lia.
      rewrite rep0_add; unfold_reps; fast_steps.
  - unfold stepA; destruct (N.eqb k1 0) eqn:Hk1; [| exact (stepAMicro_sound _ rs bnc)].
    apply N.eqb_eq in Hk1; subst k1.
    destruct l1 as [| tkv tl | tkv tl | tkv tl | tkv tl | tkv tl | tkv tl | tc tl];
      try exact (stepAMicro_sound _ rs bnc).
    + (* LX *)
      destruct (N.eqb tkv 0) eqn:H0.
      * apply N.eqb_eq in H0; subst tkv; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL encR]; rewrite pushOR1_spec; unfold_reps; fast_steps.
      * apply N.eqb_neq in H0; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL encR]; rewrite pushBitL1_spec, pushXRawL_spec, pushOR1_spec.
        replace (tkv + 1) with (2 + (tkv - 1)) by lia; rewrite repX_add; unfold_reps; fast_steps.
    + (* LY *)
      destruct (N.eqb tkv 0) eqn:H0.
      * apply N.eqb_eq in H0; subst tkv; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL]; rewrite pushOR6_spec; unfold_reps; fast_steps.
      * apply N.eqb_neq in H0; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL]; rewrite pushXL1_spec, pushYL_spec, pushOR8_spec.
        replace (tkv + 1) with (2 + (tkv - 1)) by lia; rewrite repY_add; unfold_reps; fast_steps.
    + (* LDL0 *)
      cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
      unfold encCfg; cbn [encL]; rewrite pushXL_spec, pushDL0RawL_spec, pushOR8_spec.
      replace (tkv + 1) with (1 + tkv) by lia; rewrite repDL0_add.
      replace 4 with (1 + 3) by lia; rewrite repX_add; unfold_reps; fast_steps.
    + (* LUL *)
      cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
      unfold encCfg; cbn [encL]; rewrite pushXL_spec, pushULRawL_spec, pushOR8_spec.
      replace (tkv + 1) with (1 + tkv) by lia; rewrite repUL_add.
      replace 8 with (1 + 7) by lia; rewrite repX_add; unfold_reps; fast_steps.
  - (* LX *)
    cbn [stepA ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; cbn [encL encR]; rewrite pushBitL1_spec, pushXRawL_spec, pushOR1_spec.
    replace (kv + 1) with (1 + kv) by lia; rewrite repX_add; unfold_reps; fast_steps.
  - (* LY *)
    cbn [stepA ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; cbn [encL]; rewrite pushXL1_spec, pushYL_spec, pushOR2_spec.
    replace (kv + 1) with (1 + kv) by lia; rewrite repY_add; unfold_reps; fast_steps.
  - (* LDL0 *)
    cbn [stepA ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; cbn [encL]; rewrite pushXL1_spec, pushYL1_spec, pushXL_spec, pushDL0RawL_spec, pushOR2_spec.
    replace (kv + 1) with (1 + kv) by lia; rewrite repDL0_add; unfold_reps; fast_steps.
  - (* LUL *)
    cbn [stepA ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; cbn [encL]; rewrite pushXL1_spec, pushYL1_spec, pushXL_spec, pushULRawL_spec, pushOR2_spec.
    replace (kv + 1) with (1 + kv) by lia; rewrite repUL_add; unfold_reps; fast_steps.
  - (* LC *)
    cbn [stepA]; pose proof (splitFirst_spec t (encL tl)) as Hsp.
    destruct (splitFirst t) as [m0 [c' | ]]; cbn [fst snd] in Hsp.
    + destruct (N.eqb m0 0) eqn:Hm0.
      * apply N.eqb_eq in Hm0; subst m0; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL]; rewrite Hsp, pushXL_spec, pushOR2_spec; cbn [encL]; unfold_reps; fast_steps.
      * apply N.eqb_neq in Hm0; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL encR]; rewrite Hsp, pushXRawL_spec; cbn [encL];
        rewrite pushXRawL3_spec, pushOR1_spec; cbn [encL].
        replace (2 * m0) with (1 + (2 * (m0 - 1) + 1)) by lia; rewrite repX_add; unfold_reps; fast_steps.
    + destruct (N.eqb m0 0) eqn:Hm0.
      * apply N.eqb_eq in Hm0; subst m0; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL]; rewrite Hsp, pushXL_spec, pushOR2_spec; unfold_reps; fast_steps.
      * apply N.eqb_neq in Hm0; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL encR]; rewrite Hsp, pushXRawL_spec; cbn [encL];
        rewrite pushXRawL3_spec, pushOR1_spec.
        replace (2 * m0) with (1 + (2 * (m0 - 1) + 1)) by lia; rewrite repX_add; unfold_reps; fast_steps.
Qed.

Lemma stepBModeBR0_sound (ls : LSide) (r0 r1 : RSide) (bnc : N)
    (Hr0 : forall wt : side, encR wt r0 = S0 >> encR wt r1) :
  ReachWall false ls r0 bnc (stepBModeBR0 ls r1 bnc).
Proof.
  assert (Hfall : ReachWall false ls r0 bnc (ModeA ls (pushOR1 r1) bnc)).
  { cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; rewrite Hr0, pushOR1_spec; unfold_reps; fast_steps. }
  unfold stepBModeBR0.
  destruct ls as [| kv tl | k1 l1 | kv tl | kv tl | kv tl | kv tl | tc tl]; try exact Hfall.
  destruct (N.eqb k1 0) eqn:Hk1; [| exact Hfall].
  apply N.eqb_eq in Hk1; subst k1.
  destruct l1 as [| tkv tl | tkv tl | kx lrest | tkv tl | tkv tl | tkv tl | t lrest]; try exact Hfall.
  - (* LX *)
    destruct (N.leb 1 kx) eqn:Hkx1; [| exact Hfall].
    apply N.leb_le in Hkx1.
    destruct (andb (isConduitHeadL lrest) (andb (N.leb 3 kx) (N.eqb (N.modulo (kx + 1) 2) 0))) eqn:Hcond.
    + apply Bool.andb_true_iff in Hcond; destruct Hcond as [_ Hcond2].
      apply Bool.andb_true_iff in Hcond2; destruct Hcond2 as [Hkx3 Hev].
      apply N.leb_le in Hkx3; apply N.eqb_eq in Hev.
      destruct (N_div_mod_2 (kx + 1)) as [Hdm _].
      destruct (N_div_mod_2 (kx + 1 - 2)) as [Hdm2 Hmod2].
      cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
      unfold encCfg; cbn [encL encR]; rewrite Hr0, pushZR_spec, pushOR2_spec.
      set (qm1 := N.div (kx + 1 - 2) 2 - 1).
      replace (kx + 1) with (2 * (qm1 + 1) + 2) by (unfold qm1; lia).
      rewrite repX_add, !rep1_1, !rep0_1, !rep1_3, !rep1_2.
      exact (tm_left_X2 qm1 (repX 2 (encL lrest)) (encR wt r1)).
    + destruct (N_div_mod_2 (kx + 1)) as [Hdm Hmod].
      cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
      unfold encCfg; cbn [encL encR]; rewrite Hr0, pushBitL1_spec, pushXL_spec, pushZR_spec, pushOR2_spec.
      set (qm1 := N.div (kx + 1) 2 - 1).
      set (rem := N.modulo (kx + 1) 2).
      replace (kx + 1) with (2 * (qm1 + 1) + rem) by (unfold qm1, rem; lia).
      rewrite repX_add, !rep1_1, !rep0_1, !rep1_3, !rep1_2.
      exact (tm_left_X2 qm1 (repX rem (encL lrest)) (encR wt r1)).
  - (* LC *)
    pose proof (splitFirst_spec t (encL lrest)) as Hsp.
    destruct (splitFirst t) as [m0 optC]; cbn [fst snd] in Hsp.
    cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; cbn [encL]; rewrite Hr0, Hsp, pushBitL1_spec.
    set (l_mid := match optC with None => encL lrest | Some r => encCL r (encL lrest) end).
    destruct (N.eqb m0 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m0.
      assert (Hfirst : (rep1 (0 + 1) (repX (2 * 0) (repY 1 (repX 3 l_mid)))) {{B}}> (S0 >> encR wt r1) -[ tm ]->*
                       (S1 >> l_mid) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (rep1 6 (encR wt r1))))).
      { unfold_reps; fast_steps. }
      destruct optC as [c' | ]; cbn [encR];
        rewrite !rep0_1, pushOR4_spec, ?pushCRR_spec, pushOR6_spec.
      * eapply evstep_trans; [exact Hfirst | exact (tm_jump_left_ctree_direct c' (encL lrest) (rep1 6 (encR wt r1)))].
      * exact Hfirst.
    + apply N.eqb_neq in Hm0.
      set (d := m0 - 1).
      replace m0 with (d + 1) by (unfold d; lia).
      assert (Hfirst : (rep1 (0 + 1) (repX (2 * (d + 1)) (repY 1 (repX 3 l_mid)))) {{B}}> (S0 >> encR wt r1) -[ tm ]->*
                       (S1 >> l_mid) {{B}}> (S0 >> rep1 3 (S0 >> rep1 4 (rep1 9 (S0 >> repZ d (rep1 2 (encR wt r1))))))).
      { cbn [N.add]; rewrite rep1_1.
        eapply evstep_trans; [exact (tm_left_X2 d (repY 1 (repX 3 l_mid)) (encR wt r1)) | ].
        rewrite <- rep1_2; exact (tm_20_after_X2 l_mid (repZ d (rep1 2 (encR wt r1)))). }
      destruct optC as [c' | ]; cbn [encR N.add];
        rewrite !rep0_1, pushOR4_spec, ?pushCRR_spec;
        cbn [encR N.add]; rewrite !rep0_1, pushZR_spec, pushOR2_spec.
      * eapply evstep_trans; [exact Hfirst | exact (tm_jump_left_ctree_direct c' (encL lrest) (rep1 9 (S0 >> repZ d (rep1 2 (encR wt r1)))))].
      * exact Hfirst.
Qed.

Lemma stepBMicro1_sound (ls : LSide) (rs : RSide) (bnc : N) :
  ReachWall false ls rs bnc (stepBMicro1 ls rs bnc).
Proof.
  unfold stepBMicro1.
  destruct (popBitR rs) as [[[|] r1] | ] eqn:H1; try exact I.
  destruct (popBitR r1) as [[[|] r2] | ] eqn:H2; try exact I.
  destruct (popBitR r2) as [[[|] r3] | ] eqn:H3; try exact I.
  - destruct (popBitR r3) as [[b4 r4] | ] eqn:H4; try exact I.
    destruct (popBitR r4) as [[b5 r5] | ] eqn:H5; try exact I.
    destruct b4, b5; cbn [ReachWall]; apply ReachWallCore_of_star; intro wt; unfold encCfg;
      rewrite (popBitR_spec wt _ _ _ H1), (popBitR_spec wt _ _ _ H2),
              (popBitR_spec wt _ _ _ H3), (popBitR_spec wt _ _ _ H4),
              (popBitR_spec wt _ _ _ H5),
              ?pushXL1_spec, ?pushYL1_spec, ?pushOR4_spec, ?pushOR2_spec, ?pushOR1_spec, ?pushB0R1_spec;
      unfold_reps; fast_steps.
  - cbn [ReachWall]; apply ReachWallCore_of_star; intro wt; unfold encCfg.
    rewrite (popBitR_spec wt _ _ _ H1), (popBitR_spec wt _ _ _ H2),
            (popBitR_spec wt _ _ _ H3), pushXL1_spec;
    unfold_reps; fast_steps.
Qed.

Lemma stepBModeBO_sound (ls : LSide) (ko : N) (rrest : RSide) (bnc : N) :
  ReachWall false ls (RO ko rrest) bnc (stepBModeBO ls ko rrest bnc).
Proof.
  assert (Hpop0 : (match rrest with RNil | RB0 _ _ => true | _ => false end) = true ->
    forall wt : side, encR wt rrest = S0 >> encR wt
      (match rrest with
       | RNil => RNil
       | RB0 kb tl => if N.eqb kb 0 then tl else RB0 (kb - 1) tl
       | _ => rrest
       end)).
  { intros Hz wt; destruct rrest as [| | kb tl | | | | | ]; try discriminate.
    - cbn [encR]; apply const_unfold.
    - destruct (N.eqb kb 0) eqn:Hkb; cbn [encR].
      + apply N.eqb_eq in Hkb; subst kb; rewrite rep0_1; reflexivity.
      + apply N.eqb_neq in Hkb; replace (kb + 1) with (1 + (kb - 1 + 1)) by lia;
        rewrite rep0_add, rep0_1; reflexivity. }
  unfold stepBModeBO.
  set (nextZ := match rrest with RNil | RB0 _ _ => true | _ => false end).
  destruct (andb nextZ (andb (N.leb 1 ko) (N.eqb (N.modulo (ko + 1) 3) 2))) eqn:Hc1.
  - apply Bool.andb_true_iff in Hc1; destruct Hc1 as [Hz Hc1'].
    apply Bool.andb_true_iff in Hc1'; destruct Hc1' as [Hko1 Hmod].
    apply N.leb_le in Hko1; apply N.eqb_eq in Hmod.
    destruct (N_div_mod_3 (ko + 1)) as [Hdm _].
    destruct (N_div_mod_3 (ko + 1 - 2)) as [Hdm2 Hmod2].
    set (q := N.div (ko + 1 - 2) 3).
    cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; cbn [encR]; rewrite pushXL_spec, (Hpop0 Hz wt).
    set (r0 := encR wt (match rrest with RNil => RNil | RB0 kb tl => if N.eqb kb 0 then tl else RB0 (kb - 1) tl | _ => rrest end)).
    replace (ko + 1) with (3 * q + 2) by (unfold q; lia); rewrite rep1_add.
    eapply evstep_trans.
    + apply (tm_sweep_O q (rep1 2 (S0 >> r0))); rewrite rep1_2; reflexivity.
    + replace (q + 1) with (1 + q) by lia; rewrite repX_add; unfold_reps; fast_steps.
  - destruct (andb nextZ (andb (N.leb 3 ko) (N.eqb (N.modulo (ko + 1) 3) 1))) eqn:Hc2.
    + apply Bool.andb_true_iff in Hc2; destruct Hc2 as [Hz Hc2'].
      apply Bool.andb_true_iff in Hc2'; destruct Hc2' as [Hko3 Hmod].
      apply N.leb_le in Hko3; apply N.eqb_eq in Hmod.
      destruct (N_div_mod_3 (ko + 1)) as [Hdm _].
      destruct (N_div_mod_3 (ko + 1 - 4)) as [Hdm2 Hmod2].
      set (q := N.div (ko + 1 - 4) 3).
      cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
      unfold encCfg; cbn [encR]; rewrite pushYL1_spec, pushXL_spec, (Hpop0 Hz wt).
      set (r0 := encR wt (match rrest with RNil => RNil | RB0 kb tl => if N.eqb kb 0 then tl else RB0 (kb - 1) tl | _ => rrest end)).
      replace (ko + 1) with (3 * q + 4) by (unfold q; lia); rewrite rep1_add.
      eapply evstep_trans.
      * apply (tm_sweep_O q (rep1 4 (S0 >> r0))); rewrite rep1_4; reflexivity.
      * unfold_reps; fast_steps.
    + destruct (N.leb 4 ko) eqn:Hc4.
      * apply N.leb_le in Hc4.
        destruct (N_div_mod_3 (ko + 1 - 2)) as [Hdm2 Hmod2].
        set (q := N.div (ko + 1 - 2) 3).
        set (rem := ko + 1 - 3 * q).
        cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encR]; rewrite pushXL_spec, pushOR_spec.
        replace (ko + 1) with (3 * q + rem) by (unfold q, rem; lia); rewrite rep1_add.
        assert (Hr_eta : rep1 rem (encR wt rrest) = S1 >> S1 >> rep1 (rem - 2) (encR wt rrest)).
        { replace rem with (2 + (rem - 2)) at 1 by (unfold rem, q; lia); rewrite rep1_add, rep1_2; reflexivity. }
        apply (tm_sweep_O q (rep1 rem (encR wt rrest))); rewrite Hr_eta; reflexivity.
      * exact (stepBMicro1_sound ls (RO ko rrest) bnc).
Qed.

Lemma stepBOnO6_sound (ls : LSide) (r1 : RSide) (bnc : N) :
  ReachWall false ls (RO 6 r1) bnc (stepBOnO6 ls r1 bnc).
Proof.
  unfold stepBOnO6.
  destruct r1 as [| | kb1 r2 | | | | | ]; try exact (stepBModeBO_sound ls 6 _ bnc).
  destruct (N.eqb kb1 0) eqn:H1; [| exact (stepBModeBO_sound ls 6 _ bnc)].
  apply N.eqb_eq in H1; subst kb1.
  destruct r2 as [| | | ko1 r3 | | | | ]; try exact (stepBModeBO_sound ls 6 _ bnc).
  destruct (N.eqb ko1 3) eqn:H2; [| exact (stepBModeBO_sound ls 6 _ bnc)].
  apply N.eqb_eq in H2; subst ko1.
  destruct r3 as [| | kb2 r4 | | | | | ]; try exact (stepBModeBO_sound ls 6 _ bnc).
  destruct (N.eqb kb2 0) eqn:H3; [| exact (stepBModeBO_sound ls 6 _ bnc)].
  apply N.eqb_eq in H3; subst kb2.
  destruct r4 as [| | | | kz rrest | | | ]; try exact (stepBModeBO_sound ls 6 _ bnc).
  cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
  unfold encCfg; cbn [encR N.add]; rewrite !rep0_1, pushXL_spec, !pushYL1_spec, pushXL1_spec.
  eapply evstep_trans.
  - instantiate (1 := (repY 1 (repY 1 (repX 1 (encL ls)))) {{B}}> (repZ (kz + 1) (encR wt rrest))).
    unfold rep1, repY, repX; cbn [N.to_nat Pos.to_nat Pos.iter_op Init.Nat.add rep1n repYn repXn]; fast_steps.
  - exact (tm_sweep_Z (kz + 1) (repY 1 (repY 1 (repX 1 (encL ls)))) (encR wt rrest)).
Qed.

Lemma stepB_sound (ls : LSide) (rs : RSide) (bnc : N) :
  ReachWall false ls rs bnc (stepB ls rs bnc).
Proof.
  destruct rs as [| | kb r1 | ko r1 | rv rrest | kd rrest | ku rrest | tc rrest].
  - (* RNil *)
    apply (stepBModeBR0_sound ls RNil RNil bnc); intro; apply const_unfold.
  - (* RWall *)
    exact I.
  - (* RB0 *)
    unfold stepB.
    destruct (N.eqb kb 0) eqn:Hkb.
    + apply N.eqb_eq in Hkb; subst kb.
      assert (Hbr0 : ReachWall false ls (RB0 0 r1) bnc (stepBModeBR0 ls r1 bnc)).
      { exact (stepBModeBR0_sound ls (RB0 0 r1) r1 bnc (fun wt => rep0_1 (encR wt r1))). }
      destruct r1 as [| | | ko rrest | | | | ]; try exact Hbr0.
      destruct (N.leb 1 ko) eqn:Hko1; [| exact Hbr0].
      apply N.leb_le in Hko1.
      destruct ls as [| | k1 l1 | | | | | ]; try exact Hbr0.
      destruct (N.eqb k1 0) eqn:Hk1; [| exact Hbr0].
      apply N.eqb_eq in Hk1; subst k1.
      destruct l1 as [| | | kx l2 | | | | ]; try exact Hbr0.
      destruct (N.eqb kx 1) eqn:Hkx; [| exact Hbr0].
      apply N.eqb_eq in Hkx; subst kx.
      destruct l2 as [| | | | | kd lrest | ku lrest | t lrest]; try exact Hbr0.
      * (* LDL0 *)
        cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL encR N.add];
        rewrite !rep0_1, !rep1_1, !rep1_2, pushBitL1_spec, pushXL2_spec, pushDR0R_spec, pushOR_spec.
        replace (ko + 1) with (2 + (ko - 1)) by lia; rewrite rep1_add, rep1_2.
        exact (tm_jump_left_dl0 (kd + 1) (encL lrest) (rep1 (ko - 1) (encR wt rrest))).
      * (* LUL *)
        cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL encR N.add];
        rewrite !rep0_1, !rep1_1, !rep1_2, pushBitL1_spec, pushXL2_spec, pushURR_spec, pushOR_spec.
        replace (ko + 1) with (2 + (ko - 1)) by lia; rewrite rep1_add, rep1_2.
        exact (tm_jump_left_ul (ku + 1) (encL lrest) (rep1 (ko - 1) (encR wt rrest))).
      * (* LC *)
        cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encL encR N.add];
        rewrite !rep0_1, !rep1_1, !rep1_2, pushBitL1_spec, pushXL2_spec, pushCRR_spec, pushOR_spec.
        replace (ko + 1) with (2 + (ko - 1)) by lia; rewrite rep1_add, rep1_2.
        exact (tm_jump_left_ctree t (encL lrest) (rep1 (ko - 1) (encR wt rrest))).
    + apply N.eqb_neq in Hkb.
      apply (stepBModeBR0_sound ls (RB0 kb r1) (RB0 (kb - 1) r1) bnc).
      intro wt; cbn [encR]; replace (kb + 1) with (1 + (kb - 1 + 1)) by lia.
      rewrite rep0_add, rep0_1; reflexivity.
  - (* RO *)
    unfold stepB.
    destruct (N.eqb ko 3) eqn:H3.
    + apply N.eqb_eq in H3; subst ko.
      destruct r1 as [| | | | | kd rrest | ku rrest | t rrest];
        try exact (stepBModeBO_sound ls 3 _ bnc).
      * (* RWall *)
        destruct ls as [| kv tl | kv tl | kv tl | kv tl | kv tl | kv tl | t lrest];
          cbn [ReachWall]; apply ReachWallCore_of_bounce; intros s w Hfuel;
          unfold encCfg; cbn [encR N.add]; rewrite pushBitL1_spec, !rep0_1.
        1-7: exact (wall_bounce_plus _ s w Hfuel).
        cbn [encL]; exact (wall_merge_bounce_plus t (encL lrest) s w Hfuel).
      * (* RDR0 *)
        cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encR N.add];
        rewrite pushYL1_spec, pushXL_spec, pushDL0RawL_spec, pushXL2_spec, pushOR3_spec.
        exact (tm_jump_right_dr0_4 kd (encL ls) (encR wt rrest)).
      * (* RUR *)
        cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encR N.add];
        rewrite pushYL1_spec, pushXL_spec, pushULRawL_spec, pushXL2_spec, pushOR3_spec.
        exact (tm_jump_right_ur_4 ku (encL ls) (encR wt rrest)).
      * (* RCR *)
        cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
        unfold encCfg; cbn [encR N.add];
        rewrite coalesceL_spec, pushCL_spec, pushOR4_spec.
        exact (tm_jump_right_ctree t (encL ls) (encR wt rrest)).
    + destruct (N.eqb ko 2) eqn:H2.
      * apply N.eqb_eq in H2; subst ko.
        destruct r1 as [| | kb r2 | | | kd rrest | ku rrest | ];
          try exact (stepBModeBO_sound ls 2 _ bnc).
        -- (* RB0 *)
           destruct (N.eqb kb 0) eqn:Hkb; [| exact (stepBModeBO_sound ls 2 _ bnc)].
           apply N.eqb_eq in Hkb; subst kb.
           destruct r2 as [| | | ko2 rrest | kz rrest | | | ];
             try exact (stepBModeBO_sound ls 2 _ bnc).
           ++ (* RO *)
              cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
              unfold encCfg; cbn [encR N.add]; rewrite !rep0_1, pushOR_spec.
              replace (ko2 + 1) with (1 + ko2) by lia; rewrite rep1_add.
              rewrite rep1_3, rep1_4, rep1_1; fast_steps.
           ++ (* RZ *)
              cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
              unfold encCfg; cbn [encR N.add]; rewrite !rep0_1, pushZR_spec.
              replace (kz + 1) with (1 + kz) by lia; rewrite repZ_add.
              rewrite rep1_3, !rep1_4, repZ_1; fast_steps.
        -- (* RDR0 *)
           cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
           unfold encCfg; cbn [encR N.add];
           rewrite pushYL1_spec, pushXL_spec, pushDL0RawL_spec, pushYL1_spec, pushOR3_spec.
           exact (tm_jump_right_dr0_3 kd (encL ls) (encR wt rrest)).
        -- (* RUR *)
           cbn [ReachWall]; apply ReachWallCore_of_star; intro wt.
           unfold encCfg; cbn [encR N.add];
           rewrite pushYL1_spec, pushXL_spec, pushULRawL_spec, pushYL1_spec, pushOR3_spec.
           exact (tm_jump_right_ur_3 ku (encL ls) (encR wt rrest)).
      * destruct (N.eqb ko 6) eqn:H6.
        -- apply N.eqb_eq in H6; subst ko; exact (stepBOnO6_sound ls r1 bnc).
        -- exact (stepBModeBO_sound ls ko r1 bnc).
  - (* RZ *)
    cbn [stepB ReachWall]; apply ReachWallCore_of_star; intro wt.
    unfold encCfg; cbn [encR]; rewrite pushXL_spec.
    exact (tm_sweep_Z (rv + 1) (encL ls) (encR wt rrest)).
  - (* RDR0 *)
    exact (stepBMicro1_sound ls (RDR0 kd rrest) bnc).
  - (* RUR *)
    exact (stepBMicro1_sound ls (RUR ku rrest) bnc).
  - (* RCR *)
    exact (stepBMicro1_sound ls (RCR tc rrest) bnc).
Qed.

Lemma stepOne_sound (st : MState) :
  ReachWallSt st (stepOne st).
Proof.
  destruct st as [ls rs bnc | ls rs bnc | ]; cbn [stepOne ReachWallSt].
  - exact (stepA_sound ls rs bnc).
  - exact (stepB_sound ls rs bnc).
  - reflexivity.
Qed.

Lemma Pos_iter_stepOne_sound (p : positive) :
  forall st : MState, ReachWallSt st (Pos.iter stepOne st p).
Proof.
  induction p as [| p' IHp] using Pos.peano_ind; intro st.
  - exact (stepOne_sound st).
  - rewrite Pos.iter_succ.
    exact (ReachWallSt_trans st (Pos.iter stepOne st p') _ (IHp st) (stepOne_sound _)).
Qed.

Definition after_entry (st : MState) : option (LSide * list N * CTree) :=
  match st with
  | ModeB l_cyc (RO ko1 (RCR t_entry RNil)) bnc1 =>
    if andb (N.eqb ko1 3) (N.eqb bnc1 0) then
      let '(bot, topList) := splitAtN 3031%positive (flattenCTree t_entry) in
      match topList with
      | [] => None
      | t0 :: trems =>
        let topTree := ofListCTreeNE t0 trems in
        if N.leb 43211 (fuelList bot) then Some (l_cyc, topList, topTree) else None
      end
    else None
  | _ => None
  end.

Definition finish_cycle (l_cyc : LSide) (topList : list N) (st2 : MState) : bool :=
  match st2 with
  | ModeB l_end (RO ko2 (RCR t_end RWall)) bnc2 =>
    if andb (N.eqb ko2 3) (N.eqb bnc2 43207) then
      if beqLSideSem l_end l_cyc then
        let '(w_list, topList') := splitAtN 6505%positive (flattenCTree t_end) in
        andb (beqListN topList topList') (N.leb 43207 (fuelList w_list))
      else false
    else false
  | _ => false
  end.

Definition check_certificate_gen (p1 p2 : positive) : bool :=
  match after_entry (Pos.iter stepOne (ModeB (LB1 0 LNil) RNil 0) p1) with
  | None => false
  | Some (l_cyc, topList, topTree) =>
    finish_cycle l_cyc topList
      (Pos.iter stepOne (ModeB l_cyc (RO 3 (RCR topTree RWall)) 0) p2)
  end.

Lemma after_entry_spec (st : MState) (l_cyc : LSide) (topList : list N) (topTree : CTree) :
  after_entry st = Some (l_cyc, topList, topTree) ->
  exists (t_entry : CTree) (bot : list N),
    st = ModeB l_cyc (RO 3 (RCR t_entry RNil)) 0 /\
    bot ++ topList = flattenCTree t_entry /\
    flattenCTree topTree = topList /\
    43211 <= fuelList bot.
Proof.
  destruct st as [| lc rs1 bnc1 | ]; try discriminate.
  destruct rs1 as [| | | ko1 r1_tl | | | | ]; try discriminate.
  destruct r1_tl as [| | | | | | | t_entry r1_end]; try discriminate.
  destruct r1_end; try discriminate.
  cbn [after_entry]; intro H.
  destruct (andb (N.eqb ko1 3) (N.eqb bnc1 0)) eqn:Hkb; [| discriminate].
  apply Bool.andb_true_iff in Hkb; destruct Hkb as [Hko Hbnc].
  apply N.eqb_eq in Hko; apply N.eqb_eq in Hbnc; subst ko1 bnc1.
  pose proof (splitAtN_append 3031%positive (flattenCTree t_entry)) as Hsplit.
  destruct (splitAtN 3031%positive (flattenCTree t_entry)) as [bot tl0]; cbn [fst snd] in Hsplit.
  destruct tl0 as [| t0 trems]; [discriminate | ].
  destruct (N.leb 43211 (fuelList bot)) eqn:Hbot; [| discriminate].
  apply N.leb_le in Hbot.
  inversion H; subst lc topList topTree; clear H.
  exists t_entry, bot.
  repeat split; [exact Hsplit | apply ofListCTreeNE_spec | exact Hbot].
Qed.

Lemma finish_cycle_spec (l_cyc : LSide) (topList : list N) (st2 : MState) :
  finish_cycle l_cyc topList st2 = true ->
  exists (l_end : LSide) (t_end : CTree) (w_list : list N),
    st2 = ModeB l_end (RO 3 (RCR t_end RWall)) 43207 /\
    encL l_end = encL l_cyc /\
    w_list ++ topList = flattenCTree t_end /\
    43207 <= fuelList w_list.
Proof.
  destruct st2 as [| l_end rs2 bnc2 | ]; try discriminate.
  destruct rs2 as [| | | ko2 r2_tl | | | | ]; try discriminate.
  destruct r2_tl as [| | | | | | | t_end r2_end]; try discriminate.
  destruct r2_end; try discriminate.
  cbn [finish_cycle]; intro H.
  destruct (andb (N.eqb ko2 3) (N.eqb bnc2 43207)) eqn:Hkb; [| discriminate].
  apply Bool.andb_true_iff in Hkb; destruct Hkb as [Hko Hbnc].
  apply N.eqb_eq in Hko; apply N.eqb_eq in Hbnc; subst ko2 bnc2.
  destruct (beqLSideSem l_end l_cyc) eqn:Hlend; [| discriminate].
  apply beqLSideSem_enc in Hlend.
  pose proof (splitAtN_append 6505%positive (flattenCTree t_end)) as Hsplit.
  destruct (splitAtN 6505%positive (flattenCTree t_end)) as [w_list topList']; cbn [fst snd] in Hsplit.
  apply Bool.andb_true_iff in H; destruct H as [HtopEq HwFuel].
  apply beqListN_eq in HtopEq; subst topList'.
  apply N.leb_le in HwFuel.
  exists l_end, t_end, w_list.
  repeat split; assumption.
Qed.

Lemma run_stepOne_modeB (p : positive) (ls : LSide) (rs : RSide) (bnc : N) (st : MState) :
  Pos.iter stepOne (ModeB ls rs bnc) p = st ->
  ReachWall false ls rs bnc st.
Proof.
  intro H; subst st.
  exact (Pos_iter_stepOne_sound p (ModeB ls rs bnc)).
Qed.

Lemma prove_nonhalt_core
    (b_cnt : N) (Hb : 0 < b_cnt)
    (l_cyc l_end : LSide)
    (t_entry topTree t_end : CTree)
    (bot w_list topList : list N)
    (Hsound1 : ReachWallCore false (LB1 0 LNil) RNil 0 false l_cyc (RO 3 (RCR t_entry RNil)) 0)
    (Hsound2 : ReachWallCore false l_cyc (RO 3 (RCR topTree RWall)) 0 false l_end (RO 3 (RCR t_end RWall)) b_cnt)
    (Hlend : encL l_end = encL l_cyc)
    (Hsplit1 : bot ++ topList = flattenCTree t_entry)
    (HtopFlat : flattenCTree topTree = topList)
    (Hsplit2 : w_list ++ topList = flattenCTree t_end)
    (Hbot : b_cnt + 4 <= fuelList bot)
    (HwFuel : b_cnt <= fuelList w_list) :
  ~ halts tm c0.
Proof.
  assert (HentryTree : encCR t_entry (const S0) = encCR topTree (encWall bot RWEmpty)).
  { rewrite encCR_eq_encCRList, <- Hsplit1, <- HtopFlat, encCRList_app, <- encCR_eq_encCRList; reflexivity. }
  assert (HendTree : forall (s' : list N) (w' : RWallShape),
    encCR t_end (encWall s' w') = encCR topTree (encWall (s' ++ w_list) w')).
  { intros s' w'.
    rewrite encCR_eq_encCRList, <- Hsplit2, <- HtopFlat, encCRList_app, <- encCR_eq_encCRList.
    unfold encWall; rewrite encCRList_app; reflexivity. }
  destruct Hsound1 as [_ Hr1].
  pose proof (Hr1 [] RWEmpty (fun H => False_ind _ (N.lt_irrefl 0 H))) as HreachEntry; cbv zeta in HreachEntry.
  rewrite N.ltb_irrefl, N.sub_diag in HreachEntry; cbn [N.to_nat bounceRWIterNat fst snd] in HreachEntry.
  assert (Hreach0 : c0 -[ tm ]->* (encL l_cyc) {{B}}> (rep1 4 (encCR topTree (encWall bot RWEmpty)))).
  { eapply evstep_trans; [exact entry_step_init | ].
    cbn [encCfg encR N.add] in HreachEntry; rewrite HentryTree in HreachEntry; exact HreachEntry. }
  eapply multistep_nonhalt; [exact Hreach0 | ].
  apply (progress_nonhalt_cond tm (list N * RWallShape) (bot, RWEmpty)
           (fun p => (encL l_cyc) {{B}}> (rep1 4 (encCR topTree (encWall (fst p) (snd p)))))
           (fun p => b_cnt + 4 <= fuelRW (fst p) (snd p))).
  - intros [s w] Hfuel; cbn [fst snd] in Hfuel |- *.
    destruct Hsound2 as [_ Hr2].
    assert (Hf2 : (b_cnt - 0) + 4 <= fuelRW s w) by lia.
    pose proof (Hr2 s w (fun _ => Hf2)) as Hcyc; cbv zeta in Hcyc.
    assert (Hltb : N.ltb 0 b_cnt = true) by (apply N.ltb_lt; lia).
    rewrite Hltb, N.sub_0_r in Hcyc.
    destruct (bounceRWIterNat (N.to_nat b_cnt) (s, w)) as [s' w'] eqn:Hbnc; cbn [fst snd] in Hcyc.
    assert (Hfn : N.of_nat (N.to_nat b_cnt) + 4 <= fuelRW s w) by lia.
    pose proof (fuelRW_bounceRWIterNat (N.to_nat b_cnt) s w Hfn) as Hfp.
    rewrite Hbnc in Hfp; cbn [fst snd] in Hfp.
    exists (s' ++ w_list, w'); cbn [fst snd]; split.
    + cbn [encCfg encR N.add] in Hcyc.
      rewrite Hlend, HendTree in Hcyc; exact Hcyc.
    + unfold fuelRW in *; rewrite fuelList_app; lia.
  - cbn [fst snd]; unfold fuelRW; cbn [fuelRWall]; lia.
Qed.

Lemma prove_nonhalt_from_cert_gen (p1 p2 : positive) :
  check_certificate_gen p1 p2 = true -> ~ halts tm c0.
Proof.
  unfold check_certificate_gen; intro Hcert.
  set (st1 := Pos.iter stepOne (ModeB (LB1 0 LNil) RNil 0) p1) in *.
  destruct (after_entry st1) as [[[l_cyc topList] topTree] | ] eqn:Hae; [| discriminate].
  destruct (after_entry_spec st1 l_cyc topList topTree Hae)
    as [t_entry [bot [Hst1 [Hsplit1 [HtopFlat Hbot]]]]].
  set (st2 := Pos.iter stepOne (ModeB l_cyc (RO 3 (RCR topTree RWall)) 0) p2) in *.
  destruct (finish_cycle_spec l_cyc topList st2 Hcert)
    as [l_end [t_end [w_list [Hst2 [Hlend [Hsplit2 HwFuel]]]]]].
  unfold st1 in Hst1; unfold st2 in Hst2.
  pose proof (run_stepOne_modeB p1 (LB1 0 LNil) RNil 0 _ Hst1) as Hsound1.
  pose proof (run_stepOne_modeB p2 l_cyc (RO 3 (RCR topTree RWall)) 0 _ Hst2) as Hsound2.
  assert (Hb : 0 < 43207) by lia.
  exact (prove_nonhalt_core 43207 Hb l_cyc l_end t_entry topTree t_end bot w_list topList
           Hsound1 Hsound2 Hlend Hsplit1 HtopFlat Hsplit2 Hbot HwFuel).
Qed.

Lemma cert_ok : check_certificate_gen 4427140%positive 3453426%positive = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

End M302_Internal.

Theorem nonhalt : ~ halts tm c0.
Proof.
  exact (M302_Internal.prove_nonhalt_from_cert_gen 4427140%positive 3453426%positive M302_Internal.cert_ok).
Qed.
