(* 1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB does not halt from the blank tape.

   With the head in state C, write the tape as two stacks L | R. The cells left of the head are runs of ones separated by single zeros, and L lists the run lengths, nearest the head first. The same for R, whose first run starts under the head. Blanks lie beyond both ends, so a missing entry counts as 0.

   The machine on stacks, for all stacks (rule1, rule2, rule3, turn_ok):
     R = p :: R', p >= 2:            R becomes (p - 2) :: R', push 1 on L.
     R = 1 :: p :: R', p >= 1:       R becomes (p - 1) :: R', the top t of L becomes t + 2, push 0 on L.
     R = 1 :: 0 :: 0 :: R':          R becomes R', the top t of L becomes t + 4.
     R = 1 :: 0 :: p :: R', p >= 1:  the head reads 1 0 0 1, the machine halts. This is the only halt.
     R = 0 :: p :: R':               a turn. Pop k from L, then the entries 1 that follow, m of them, then look at the next entry a.
       a >= 2: a becomes a - 2, push 1 on L. R gets on top of R': 2m + 2 + p if k = 0; else 2m + 1, then k - 1 zeros, then 1 + p (pushB).
       a = 0:  the next entry ns becomes ns + 1, push 0 on L. R gets on top of R': 2m + 1 + p if k = 0; else 2m, then k - 1 zeros, then 1 + p (pushA).
   mstep joins these: it reads all pairs of ones at once, and a turn with a = 0 and k >= 1 is followed by the transfer
   (0 :: a :: L | 2i :: b :: R becomes 0 :: a + i :: L | 0 :: b + i :: R, tloop) and one more turn. mstep_ok proves it for all stacks.
   mstep gives None for the halt and for a few cases it does not treat, such as a turn with a = 0 and k = 0. Inv excludes them all.

   The run lengths seem to follow a Collatz-like map. The proof does not look at them: the invariant Inv, closed under mstep (inv_step), only speaks of the top of each stack and, through zf, of the zero entries of R.
   Nothing is assumed about L below its top four entries. Below its top, R is a word W with no zero entry (zf says this).
   To halt, an odd run must be on top of one 0 entry and then a nonzero entry. Under Inv a turn has k = 0, 1, 4 or 5, so zero entries come from a turn with k >= 4, in a block of 3 or 4, and Inv lists what can happen to such a block.
   Top of L is 1, L = 1 :: x :: y :: u :: ..., R = z :: R1, just after a turn (Hub x y u z R1):
     H0  z W, with exceptions for z <= 2 and for W empty and z = 3, 5;
     H1  z 0 W, z even: the next turn is at 0 0 W and removes the zeros;
     H2e z 0 0 W, z even, x >= 2: the next turn is at 0 0 0 W with a = x >= 2, so it does not make an odd run on top of 0 W;
     H2o z 0 0 W, z odd, W <> [1]: the head reads 1 0 0 0 and goes on into W. W = [1] would read 1 0 0 0 twice in a row and make k = 9, a longer block;
     H3o z 0 0 0 W, z odd, and H4 z 0 0 0 0 W, z odd: the head reads 1 0 0 0 and gets to a 0 with k = 5. Then a >= 2 makes H4 again, and a = 0 makes z' 0 0 0 W;
     H3e z 0 0 0 W, z even, x large enough (S3e): this comes from a turn with a = 0 and k = 5, with x = ns + m - 1 and z = m + 2, so the next turn has a = x unless z <= 4;
     HP, HQ z 1 0 0 W, z 1 0 W, z odd >= 3: they come from a turn with a >= 2 at 0 0 0 0 W, 0 0 0 W; reading them leaves a 0 on top of L over the entry 3.
   Top of L is 0, L = 0 :: a :: y :: u :: ..., a >= 2 (Tr), R = p W, or 0 0 W, or 0 0 0 W (TR), just after the second reading rule. A turn there has k = 0 and a >= 2.
   Top of L is 5, just after H2o read 1 0 0 0: R is W, not [1].
   The rest is for small numbers. z = 1 comes from reading a last 1 at the end of the tape, from a turn with k = 5 and m = 0 after that, or from R = 2 ... under a top 5. The first two can lead to z = 2 with a small x, and a turn with k = 0 makes z = 2 with x = a - 2. Zr and Tr follow an even x there, so that x = 0 then never lies over a small entry. *)
From BusyCoq Require Import Individual62.
From Coq Require Import Lia PeanoNat String.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint ones (n : nat) : list Sym :=
  match n with O => [] | S n' => S1 :: ones n' end.
Fixpoint zeros (n : nat) : list Sym :=
  match n with O => [] | S n' => S0 :: zeros n' end.
Fixpoint oo (n : nat) : list Sym :=
  match n with O => [] | S n' => S1 :: S1 :: oo n' end.

Fixpoint enc (L : list nat) : side :=
  match L with
  | [] => const S0
  | n :: L' => ones n *> S0 >> enc L'
  end.

Definition CC (s : list nat * list nat) : Q * tape := enc (fst s) {{C}}> enc (snd s).

Lemma enc_nil : enc [] = S0 >> enc [].
Proof. simpl. apply const_unfold. Qed.

Lemma oo_shift : forall n (s : side), oo n *> S1 >> s = S1 >> oo n *> s.
Proof.
  induction n as [|n IH]; intros s; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma zeros_shift : forall n (s : side), zeros n *> S0 >> s = S0 >> zeros n *> s.
Proof.
  induction n as [|n IH]; intros s; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma oo_ones : forall m p (s : side), oo m *> ones p *> s = ones (2 * m + p) *> s.
Proof.
  induction m as [|m IH]; intros p s; [reflexivity|].
  simpl. rewrite IH. replace (m + S (m + 0) + p) with (S (2 * m + p)) by lia. reflexivity.
Qed.

Lemma enc_rep0 : forall k X, enc (repeat 0 k ++ X) = zeros k *> enc X.
Proof.
  induction k as [|k IH]; intros X; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

(* The three reading rules. *)
Definition bump (d : nat) (L : list nat) : list nat :=
  match L with [] => [d] | t :: L' => (d + t) :: L' end.

Lemma rule1 : forall L r, enc L {{C}}> S1 >> S1 >> r -->+ enc (1 :: L) {{C}}> r.
Proof. intros L r. simpl. start_progress. Qed.

Lemma rule2 : forall L r, enc L {{C}}> S1 >> S0 >> S1 >> r -->+ enc (0 :: bump 2 L) {{C}}> r.
Proof.
  intros L r. destruct L as [|t L].
  - simpl. rewrite <- const_unfold. start_progress.
  - simpl. start_progress.
Qed.

Lemma rule3 : forall L r, enc L {{C}}> S1 >> S0 >> S0 >> S0 >> r -->+ enc (bump 4 L) {{C}}> r.
Proof.
  intros L r. destruct L as [|t L].
  - simpl. rewrite <- const_unfold. start_progress.
  - simpl. start_progress.
Qed.

(* The turn: the head reads 0. *)
Lemma Dsweep : forall k l r, ones k *> l <{{D}} r -->* l <{{D}} zeros k *> r.
Proof.
  induction k as [|k IH]; intros l r.
  - finish.
  - simpl. step. follow IH. rewrite zeros_shift. finish.
Qed.

Definition pushB (m k p : nat) (rest : list nat) : list nat :=
  match k with
  | O => (2 * m + 2 + p) :: rest
  | S k' => (2 * m + 1) :: repeat 0 k' ++ (1 + p) :: rest
  end.

Definition pushA (m k p : nat) (rest : list nat) : list nat :=
  match k with
  | O => (2 * m + 1 + p) :: rest
  | S k' => (2 * m) :: repeat 0 k' ++ (1 + p) :: rest
  end.

Lemma ones_2m1 : forall m (s : side), ones (2 * m + 1) *> s = oo m *> S1 >> s.
Proof.
  intros m s. rewrite oo_shift.
  replace (2 * m + 1) with (S (2 * m + 0)) by lia.
  change (ones (S (2 * m + 0)) *> s) with (S1 >> ones (2 * m + 0) *> s).
  rewrite <- oo_ones. reflexivity.
Qed.

Lemma ones_2m : forall m (s : side), ones (2 * m) *> s = oo m *> s.
Proof.
  intros m s. replace (2 * m) with (2 * m + 0) by lia.
  rewrite <- oo_ones. reflexivity.
Qed.

Lemma pushB_ok : forall m k p rest,
  oo m *> S1 >> zeros k *> S1 >> ones p *> S0 >> enc rest = enc (pushB m k p rest).
Proof.
  intros m k p rest. destruct k as [|k]; unfold pushB.
  - change (enc ((2 * m + 2 + p) :: rest)) with (ones (2 * m + 2 + p) *> S0 >> enc rest).
    replace (2 * m + 2 + p) with (2 * m + (2 + p)) by lia.
    rewrite <- oo_ones. reflexivity.
  - change (enc ((2 * m + 1) :: repeat 0 k ++ (1 + p) :: rest))
      with (ones (2 * m + 1) *> S0 >> enc (repeat 0 k ++ (1 + p) :: rest)).
    rewrite enc_rep0. rewrite ones_2m1. reflexivity.
Qed.

Lemma pushA_ok : forall m k p rest,
  oo m *> zeros k *> S1 >> ones p *> S0 >> enc rest = enc (pushA m k p rest).
Proof.
  intros m k p rest. destruct k as [|k]; unfold pushA.
  - change (enc ((2 * m + 1 + p) :: rest)) with (ones (2 * m + 1 + p) *> S0 >> enc rest).
    replace (2 * m + 1 + p) with (2 * m + (1 + p)) by lia.
    rewrite <- oo_ones. reflexivity.
  - change (enc ((2 * m) :: repeat 0 k ++ (1 + p) :: rest))
      with (ones (2 * m) *> S0 >> enc (repeat 0 k ++ (1 + p) :: rest)).
    rewrite enc_rep0. rewrite ones_2m. reflexivity.
Qed.

Fixpoint turnE (m : nat) (L1 : list nat) (k p : nat) (rest : list nat) : list nat * list nat :=
  match L1 with
  | [] => ([0; 1], pushA m k p rest)
  | [0] => ([0; 1], pushA m k p rest)
  | 0 :: ns :: L4 => (0 :: S ns :: L4, pushA m k p rest)
  | 1 :: L' => turnE (S m) L' k p rest
  | S (S a) :: L3 => (1 :: a :: L3, pushB m k p rest)
  end.

Lemma turnE_ok : forall L1 m k p rest,
  enc L1 <{{E}} oo m *> S1 >> zeros k *> S1 >> ones p *> S0 >> enc rest -->* CC (turnE m L1 k p rest).
Proof.
  induction L1 as [|a L1 IH]; intros m k p rest.
  - unfold CC. simpl turnE. simpl fst. simpl snd.
    rewrite <- pushA_ok. rewrite oo_shift. simpl enc.
    step. step. finish.
  - destruct a as [|[|a]].
    + destruct L1 as [|ns L4].
      * unfold CC. simpl turnE. simpl fst. simpl snd.
        rewrite <- pushA_ok. rewrite oo_shift. simpl enc.
        step. step. finish.
      * unfold CC. simpl turnE. simpl fst. simpl snd.
        rewrite <- pushA_ok. rewrite oo_shift. simpl enc. simpl ones.
        step. step. finish.
    + simpl turnE. simpl enc.
      rewrite oo_shift.
      do 4 step.
      specialize (IH (S m) k p rest).
      simpl oo in IH. simpl in IH.
      rewrite oo_shift in IH.
      follow IH. finish.
    + unfold CC. simpl turnE. simpl fst. simpl snd.
      rewrite <- pushB_ok. simpl enc. simpl ones.
      do 3 step. simpl. finish.
Qed.

Definition top (L : list nat) : nat * list nat :=
  match L with [] => (0, []) | x :: L' => (x, L') end.

Lemma top_ok : forall L, enc L = ones (fst (top L)) *> S0 >> enc (snd (top L)).
Proof.
  intros [|x L]; [apply enc_nil|reflexivity].
Qed.

Definition turn (L R1 : list nat) : list nat * list nat :=
  turnE 0 (snd (top L)) (fst (top L)) (fst (top R1)) (snd (top R1)).

Lemma turn_ok : forall L R1, enc L {{C}}> S0 >> enc R1 -->+ CC (turn L R1).
Proof.
  intros L R1. unfold turn.
  assert (HL := top_ok L). assert (HR := top_ok R1).
  destruct (top L) as [k L1]. destruct (top R1) as [p rest]. simpl fst in *. simpl snd in *.
  rewrite HL, HR.
  eapply progress_intro; [prove_step|simpl_tape].
  follow Dsweep.
  step.
  apply (turnE_ok L1 0 k p rest).
Qed.

(* Reading pairs of ones. *)
Fixpoint rep1 (q : nat) (L : list nat) : list nat :=
  match q with O => L | S q' => 1 :: rep1 q' L end.

Lemma rep1_shift : forall q L, rep1 q (1 :: L) = 1 :: rep1 q L.
Proof.
  induction q as [|q IH]; intros L; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma read : forall q L r, enc L {{C}}> oo q *> r -->* enc (rep1 q L) {{C}}> r.
Proof.
  induction q as [|q IH]; intros L r; [finish|].
  simpl oo. simpl.
  eapply evstep_trans; [apply progress_evstep; apply rule1|].
  eapply evstep_trans; [apply IH|].
  rewrite rep1_shift. finish.
Qed.

Lemma turnE_rep : forall q L m k p rest, turnE m (rep1 q L) k p rest = turnE (q + m) L k p rest.
Proof.
  induction q as [|q IH]; intros L m k p rest; [reflexivity|].
  simpl. rewrite IH. f_equal. lia.
Qed.

(* The transfer. *)
Lemma tloop : forall i a L4 b R,
  enc (0 :: a :: L4) {{C}}> enc ((2 * i) :: b :: R) -->* enc (0 :: (a + i) :: L4) {{C}}> enc (0 :: (b + i) :: R).
Proof.
  induction i as [|i IH]; intros a L4 b R.
  - simpl. rewrite !Nat.add_0_r. finish.
  - change (enc ((2 * S i) :: b :: R)) with (ones (2 * S i) *> S0 >> enc (b :: R)).
    rewrite ones_2m.
    eapply evstep_trans; [apply read|].
    eapply evstep_trans; [apply progress_evstep; apply turn_ok|].
    unfold turn, CC. simpl top. simpl fst. simpl snd.
    rewrite turnE_rep. simpl turnE.
    replace (i + 0) with i by lia.
    simpl pushA. simpl fst. simpl snd.
    replace (i + (i + 0) + 0) with (2 * i + 0) by lia.
    replace (2 * i + 0) with (2 * i) by lia.
    simpl repeat. simpl app.
    eapply evstep_trans; [apply (IH (S a) L4 (S b) R)|].
    replace (S a + i) with (a + S i) by lia.
    replace (S b + i) with (b + S i) by lia.
    finish.
Qed.

(* After a turn that met a 0: transfer, then a turn with k = 0. *)
Definition pushC (m k p : nat) (rest : list nat) : list nat :=
  match k with
  | O => []
  | 1 => (3 + p + m) :: rest
  | S (S k') => (2 + m) :: repeat 0 k' ++ (1 + p) :: rest
  end.

Definition Aout (m ns : nat) (L4 : list nat) (k p : nat) (rest : list nat) : option (list nat * list nat) :=
  match k with
  | O => None
  | S _ =>
    match ns + m with
    | O => None
    | S t => Some (1 :: t :: L4, pushC m k p rest)
    end
  end.

Lemma uturn : forall a' L4 b R,
  enc (0 :: S (S a') :: L4) {{C}}> enc (0 :: b :: R) -->+ enc (1 :: a' :: L4) {{C}}> enc ((2 + b) :: R).
Proof.
  intros a' L4 b R. exact (turn_ok (0 :: S (S a') :: L4) (b :: R)).
Qed.

Lemma Aout_ok : forall m ns L4 k p rest s', Aout m ns L4 k p rest = Some s' ->
  CC (0 :: S ns :: L4, pushA m k p rest) -->+ CC s'.
Proof.
  intros m ns L4 k p rest s' H. unfold Aout in H.
  destruct k as [|k]; [discriminate|].
  destruct (ns + m) as [|t] eqn:E; [discriminate|]. injection H as <-.
  unfold CC. simpl fst. simpl snd.
  destruct k as [|k'].
  - simpl pushA. simpl repeat. simpl app. simpl pushC.
    eapply evstep_progress_trans; [apply tloop|].
    replace (S ns + m) with (S (S t)) by lia.
    apply (uturn t L4 (1 + p + m) rest).
  - simpl pushA. simpl repeat. simpl app. simpl pushC.
    replace (m + (m + 0) + 0) with (2 * m) by lia.
    eapply evstep_progress_trans; [apply tloop|].
    replace (S ns + m) with (S (S t)) by lia.
    apply (uturn t L4 (0 + m) (repeat 0 k' ++ S p :: rest)).
Qed.

Fixpoint mturnE (m : nat) (L1 : list nat) (k p : nat) (rest : list nat) : option (list nat * list nat) :=
  match L1 with
  | [] => Aout m 0 [] k p rest
  | [0] => Aout m 0 [] k p rest
  | 0 :: ns :: L4 => Aout m ns L4 k p rest
  | 1 :: L' => mturnE (S m) L' k p rest
  | S (S a) :: L3 => Some (1 :: a :: L3, pushB m k p rest)
  end.

Lemma mturnE_ok : forall L1 m k p rest s', mturnE m L1 k p rest = Some s' -> CC (turnE m L1 k p rest) -->* CC s'.
Proof.
  induction L1 as [|a L1 IH]; intros m k p rest s' H.
  - apply progress_evstep. apply (Aout_ok m 0 [] k p rest s' H).
  - destruct a as [|[|a]].
    + destruct L1 as [|ns L4].
      * apply progress_evstep. apply (Aout_ok m 0 [] k p rest s' H).
      * apply progress_evstep. apply (Aout_ok m ns L4 k p rest s' H).
    + simpl in H. simpl turnE. apply IH. exact H.
    + simpl in H. injection H as <-. simpl turnE. finish.
Qed.

Definition mturn (L R1 : list nat) : option (list nat * list nat) :=
  mturnE 0 (snd (top L)) (fst (top L)) (fst (top R1)) (snd (top R1)).

Lemma mturn_ok : forall L R1 s', mturn L R1 = Some s' -> enc L {{C}}> S0 >> enc R1 -->+ CC s'.
Proof.
  intros L R1 s' H.
  eapply progress_evstep_trans; [apply turn_ok|].
  apply mturnE_ok. exact H.
Qed.

(* The head reads a run of exactly one. *)
Definition mone (L R1 : list nat) : option (list nat * list nat) :=
  match R1 with
  | [] => mturn (bump 4 L) []
  | S p2 :: R2 => Some (0 :: bump 2 L, p2 :: R2)
  | 0 :: 0 :: 0 :: R4 => mturn (bump 4 L) R4
  | 0 :: 0 :: S p4 :: R4 => Some (bump 4 L, S p4 :: R4)
  | _ => None
  end.

Lemma mone_ok : forall L R1 s', mone L R1 = Some s' -> enc L {{C}}> S1 >> S0 >> enc R1 -->+ CC s'.
Proof.
  intros L R1 s' H. destruct R1 as [|[|p2] R2].
  - simpl in H.
    assert (E : enc [] = S0 >> S0 >> S0 >> enc []).
    { rewrite enc_nil at 1. rewrite enc_nil at 1. rewrite enc_nil at 1. reflexivity. }
    rewrite E.
    eapply progress_trans; [apply rule3|].
    apply mturn_ok. exact H.
  - destruct R2 as [|[|p3] R3]; try discriminate.
    destruct R3 as [|[|p4] R4]; try discriminate.
    + simpl in H. simpl enc.
      eapply progress_trans; [apply rule3|].
      apply mturn_ok. exact H.
    + simpl in H. injection H as <-. simpl enc.
      apply rule3.
  - simpl in H. injection H as <-. simpl enc. apply rule2.
Qed.

Fixpoint mread (z : nat) (L R1 : list nat) : option (list nat * list nat) :=
  match z with
  | O => mturn L R1
  | 1 => mone L R1
  | S (S z') => mread z' (1 :: L) R1
  end.

Fixpoint mread_ok (z : nat) : forall L R1 s', mread z L R1 = Some s' -> enc L {{C}}> enc (z :: R1) -->+ CC s'.
Proof.
  intros L R1 s' H. destruct z as [|[|z]].
  - apply mturn_ok. exact H.
  - apply mone_ok. exact H.
  - simpl enc. simpl in H.
    eapply progress_trans; [apply rule1|].
    apply (mread_ok z _ _ _ H).
Qed.

Definition mstep (s : list nat * list nat) : option (list nat * list nat) :=
  match snd s with
  | [] => None
  | z :: R1 => mread z (fst s) R1
  end.

Theorem mstep_ok : forall s s', mstep s = Some s' -> CC s -->+ CC s'.
Proof.
  intros [L R] s' H. unfold mstep in H. simpl in H.
  destruct R as [|z R1]; [discriminate|].
  apply mread_ok. exact H.
Qed.

(* The invariant. It says nothing about L below its top four entries; after its top, R is any word without zero entries. *)
Fixpoint zf (W : list nat) : Prop :=
  match W with [] => True | w :: W' => 1 <= w /\ zf W' end.

Definition Zr (x y u : nat) : Prop := Nat.even x = true -> 2 <= y /\ (Nat.even y = true -> 2 <= u).

Definition Tr (a y u : nat) : Prop := 2 <= a /\ Zr a y u /\ (a = 3 -> ~ (y = 0 /\ u = 0)).

Definition S3e (x y q : nat) (W : list nat) : Prop :=
  match q with
  | 0 => 1 <= x /\ (x = 1 -> 2 <= y)
  | 1 => 1 <= x /\ (x = 1 -> W <> [1])
  | _ => 2 <= x
  end.

Inductive TR : nat -> list nat -> Prop :=
  | T1 : forall p W, zf W -> TR p W
  | T2 : forall W, W <> [] -> zf W -> TR 0 (0 :: W)
  | T3 : forall W, W <> [] -> zf W -> TR 0 (0 :: 0 :: W).

Inductive Hub (x y u : nat) : nat -> list nat -> Prop :=
  | H0 : forall z W, 1 <= z -> zf W ->
      (z = 1 -> x <> 0 /\ W <> []) ->
      (z = 2 -> Nat.even x = true -> 2 <= y) ->
      (W = [] -> z = 5 -> ~ (x = 0 /\ y = 0)) ->
      (W = [] -> z = 3 -> ~ (x = 1 /\ y = 0 /\ u = 0)) ->
      Hub x y u z W
  | H1 : forall z q W, z = 2 * S q -> W <> [] -> zf W -> Hub x y u z (0 :: W)
  | H2e : forall z q W, z = 2 * S q -> W <> [] -> zf W -> 2 <= x -> Hub x y u z (0 :: 0 :: W)
  | H2o : forall z q W, z = 2 * q + 1 -> W <> [] -> zf W -> W <> [1] -> Hub x y u z (0 :: 0 :: W)
  | H3e : forall z q W, z = 2 * S q -> W <> [] -> zf W -> S3e x y q W -> Hub x y u z (0 :: 0 :: 0 :: W)
  | H3o : forall z q W, z = 2 * q + 1 -> W <> [] -> zf W -> (q = 0 -> Zr x y u) -> Hub x y u z (0 :: 0 :: 0 :: W)
  | H4 : forall z q W, z = 2 * q + 1 -> W <> [] -> zf W -> (q = 0 -> Zr x y u) -> Hub x y u z (0 :: 0 :: 0 :: 0 :: W)
  | HP : forall z q W, z = 2 * S q + 1 -> W <> [] -> zf W -> Hub x y u z (1 :: 0 :: 0 :: W)
  | HQ : forall z q W, z = 2 * S q + 1 -> W <> [] -> zf W -> Hub x y u z (1 :: 0 :: W).

Definition Inv (s : list nat * list nat) : Prop :=
  match s with
  | (0 :: a :: L2, p :: W) => Tr a (nth 0 L2 0) (nth 1 L2 0) /\ TR p W
  | (1 :: L1, z :: R1) => Hub (nth 0 L1 0) (nth 1 L1 0) (nth 2 L1 0) z R1
  | (5 :: _, w :: W) => zf (w :: W) /\ w :: W <> [1]
  | _ => False
  end.

Definition OK (o : option (list nat * list nat)) : Prop := exists s', o = Some s' /\ Inv s'.

Lemma par : forall n, (exists q, n = 2 * q) \/ (exists q, n = 2 * q + 1).
Proof.
  intros n. destruct (Nat.Even_or_Odd n) as [[q E]|[q E]]; [left|right]; exists q; exact E.
Qed.

Lemma mread_even : forall q L R1, mread (2 * q) L R1 = mturn (rep1 q L) R1.
Proof.
  induction q as [|q IH]; intros L R1; [reflexivity|].
  replace (2 * S q) with (S (S (2 * q))) by lia.
  simpl mread. rewrite IH. rewrite rep1_shift. reflexivity.
Qed.

Lemma mread_odd : forall q L R1, mread (2 * q + 1) L R1 = mone (rep1 q L) R1.
Proof.
  induction q as [|q IH]; intros L R1; [reflexivity|].
  replace (2 * S q + 1) with (S (S (2 * q + 1))) by lia.
  simpl mread. rewrite IH. rewrite rep1_shift. reflexivity.
Qed.

Lemma mturnE_rep : forall q L m k p rest, mturnE m (rep1 q L) k p rest = mturnE (q + m) L k p rest.
Proof.
  induction q as [|q IH]; intros L m k p rest; [reflexivity|].
  simpl. rewrite IH. f_equal. lia.
Qed.

Lemma Aout_S : forall m ns L4 k p rest t, ns + m = S t ->
  Aout m ns L4 (S k) p rest = Some (1 :: t :: L4, pushC m (S k) p rest).
Proof.
  intros m ns L4 k p rest t E. unfold Aout. rewrite E. reflexivity.
Qed.

(* All cases of a turn: first the ones, then what lies under them. *)
Lemma tg : forall (P : option (list nat * list nat) -> Prop) k p rest L1 m,
  (forall i a L3, P (Some (1 :: a :: L3, pushB (i + m) k p rest))) ->
  (forall i L4, (forall j, j < i -> nth j L1 0 = 1) -> nth i L1 0 = 0 -> P (Aout (i + m) (nth (S i) L1 0) L4 k p rest)) ->
  P (mturnE m L1 k p rest).
Proof.
  intros P k p rest. induction L1 as [|a L1 IH]; intros m HB HA.
  - apply (HA 0 []); [intros; lia|reflexivity].
  - destruct a as [|[|a]].
    + destruct L1 as [|ns L4].
      * apply (HA 0 []); [intros; lia|reflexivity].
      * apply (HA 0 L4); [intros; lia|reflexivity].
    + simpl. apply IH.
      * intros i a L3. replace (i + S m) with (S i + m) by lia. apply HB.
      * intros i L4 Hj Hz. replace (i + S m) with (S i + m) by lia. apply (HA (S i) L4).
        -- intros [|j] Hlt; [reflexivity|simpl; apply Hj; lia].
        -- exact Hz.
    + apply (HB 0 a L1).
Qed.

(* k = 5 after at least one pair was read. *)
Lemma k5_gen : forall L1 m p rest, 1 <= m -> zf rest -> (1 + p) :: rest <> [1] -> OK (mturnE m L1 5 p rest).
Proof.
  intros L1 m p rest Hm Hrest Hne. apply tg.
  - intros i a L3. eexists. split; [reflexivity|]. simpl.
    apply H4 with (q := i + m); [reflexivity|discriminate|simpl; split; [lia|exact Hrest]|intros; lia].
  - intros i L4 Hj Hz.
    remember (nth (S i) L1 0) as ns.
    assert (Et : ns + (i + m) = S (ns + (i + m) - 1)) by lia.
    rewrite (Aout_S _ _ _ _ _ _ _ Et).
    eexists. split; [reflexivity|]. simpl.
    destruct (par (i + m)) as [[e He]|[e He]].
    + apply H3e with (q := e); [lia|discriminate|simpl; split; [lia|exact Hrest]|].
      destruct e as [|[|e]]; simpl; try lia.
      split; [lia|]. intros Hx. replace (S p :: rest) with ((1 + p) :: rest) by reflexivity. exact Hne.
    + apply H3o with (q := S e); [lia|discriminate|simpl; split; [lia|exact Hrest]|discriminate].
Qed.

(* k = 1 on a word without zeros after at least one pair was read. *)
Lemma k1_gen : forall L1 m p rest, 1 <= m -> zf rest ->
  (m = 1 -> nth 0 L1 0 = 0 -> nth 1 L1 0 = 0 -> rest <> [] \/ p <> 1) ->
  OK (mturnE m L1 1 p rest).
Proof.
  intros L1 m p rest Hm Hrest Hr. apply tg.
  - intros i a L3. eexists. split; [reflexivity|]. simpl.
    apply H0; simpl; try split; try lia; try discriminate; try exact Hrest.
  - intros i L4 Hj Hz.
    remember (nth (S i) L1 0) as ns.
    assert (Et : ns + (i + m) = S (ns + (i + m) - 1)) by lia.
    rewrite (Aout_S _ _ _ _ _ _ _ Et).
    eexists. split; [reflexivity|]. simpl.
    apply H0; try lia; try exact Hrest.
    intros E5 E [H1' H2'].
    assert (i = 0 /\ m = 1 /\ ns = 0 /\ p = 1) as [-> [-> [-> ->]]] by (subst; lia).
    destruct (Hr eq_refl Hz (eq_sym Heqns)) as [Hc|Hc]; [subst rest; congruence|lia].
Qed.

(* k = 5 with no pair read: z = 1 and nothing under the top but L1. *)
Lemma k5_zero : forall L1 p rest, zf rest -> (1 + p) :: rest <> [1] ->
  Zr (nth 0 L1 0) (nth 1 L1 0) (nth 2 L1 0) -> OK (mturnE 0 L1 5 p rest).
Proof.
  intros L1 p rest Hrest Hne Hz.
  destruct L1 as [|a L1].
  - simpl in Hz. destruct (Hz eq_refl) as [Hy _]. lia.
  - destruct a as [|[|a]].
    + simpl in Hz. destruct (Hz eq_refl) as [Hy Hu].
      destruct L1 as [|ns L4]; [simpl in Hy; lia|]. simpl in Hy.
      change (mturnE 0 (0 :: ns :: L4) 5 p rest) with (Aout 0 ns L4 5 p rest).
      assert (Et : ns + 0 = S (ns - 1)) by lia.
      rewrite (Aout_S _ _ _ _ _ _ _ Et).
      eexists. split; [reflexivity|]. simpl.
      apply H3e with (q := 0); [reflexivity|discriminate|simpl; split; [lia|exact Hrest]|].
      simpl. split; [lia|]. intros Ex.
      assert (ns = 2) by lia. subst ns. simpl in Hu. apply Hu. reflexivity.
    + simpl mturnE. apply k5_gen; [lia|exact Hrest|exact Hne].
    + eexists. split; [reflexivity|]. simpl.
      apply H4 with (q := 0); [reflexivity|discriminate|simpl; split; [lia|exact Hrest]|].
      intros _. simpl in Hz. exact Hz.
Qed.

Lemma inv_t5 : forall L2 w W, zf (w :: W) -> w :: W <> [1] -> OK (mstep (5 :: L2, w :: W)).
Proof.
  intros L2 w W Hz Hne. destruct Hz as [Hw HW]. unfold mstep. cbn [fst snd].
  destruct (par w) as [[q E]|[q E]]; subst w.
  - destruct q as [|q]; [lia|].
    rewrite mread_even. unfold mturn.
    change (rep1 (S q) (5 :: L2)) with (1 :: rep1 q (5 :: L2)). cbn [top fst snd].
    rewrite mturnE_rep.
    destruct W as [|p rest].
    + eexists. split; [reflexivity|]. simpl.
      apply H0; simpl; try split; try lia; try discriminate.
    + destruct HW as [Hp Hrest].
      eexists. split; [reflexivity|]. simpl.
      apply H0; simpl; try split; try lia; try discriminate; try exact Hrest.
  - rewrite mread_odd. destruct W as [|p rest].
    + destruct q as [|q]; [simpl in Hne; contradiction|].
      unfold mone, mturn.
      change (rep1 (S q) (5 :: L2)) with (1 :: rep1 q (5 :: L2)). cbn [bump top fst snd].
      rewrite mturnE_rep.
      eexists. split; [reflexivity|]. simpl.
      apply H4 with (q := q + 0); [lia|discriminate|simpl; split; [lia|exact I]|].
      intros _. unfold Zr. simpl. discriminate.
    + destruct HW as [Hp Hrest]. destruct p as [|p]; [lia|].
      destruct q as [|q].
      * eexists. split; [reflexivity|]. simpl. split; [|apply T1; exact Hrest].
        unfold Tr, Zr. simpl. split; [lia|]. split; [discriminate|lia].
      * eexists. split; [reflexivity|]. simpl. split; [|apply T1; exact Hrest].
        unfold Tr, Zr. simpl. split; [lia|]. split; [discriminate|].
        intros _ [Hy _]. destruct q; simpl in Hy; lia.
Qed.

Lemma inv_t0 : forall a L2 p W, Tr a (nth 0 L2 0) (nth 1 L2 0) -> TR p W -> OK (mstep (0 :: a :: L2, p :: W)).
Proof.
  intros a L2 p W HT HR. destruct HT as [Ha [HZ H3]].
  destruct a as [|[|a]]; try lia. unfold mstep. cbn [fst snd].
  assert (HZ' : Zr a (nth 0 L2 0) (nth 1 L2 0)) by exact HZ.
  destruct HR as [p W HW|W HN HW|W HN HW].
  - destruct (par p) as [[q E]|[q E]]; subst p.
    + destruct q as [|q].
      * (* p = 0 *)
        destruct W as [|p2 rest].
        -- eexists. split; [reflexivity|]. simpl.
           apply H0; simpl; try lia; try exact I.
           intros _ Ev. destruct (HZ' Ev) as [Hy _]. exact Hy.
        -- destruct HW as [Hp Hrest].
           eexists. split; [reflexivity|]. simpl.
           apply H0; try lia; try exact Hrest.
           intros Ehere _ [Hx Hy]. subst a. destruct (HZ' eq_refl) as [Hy2 _]. lia.
      * (* p = 2 * S q *)
        rewrite mread_even. unfold mturn.
        change (rep1 (S q) (0 :: S (S a) :: L2)) with (1 :: rep1 q (0 :: S (S a) :: L2)). cbn [top fst snd].
        rewrite mturnE_rep.
        destruct W as [|p2 rest].
        -- cbn [top fst snd mturnE].
           assert (Et : S (S a) + (q + 0) = S (S a + (q + 0))) by lia.
           rewrite (Aout_S _ _ _ _ _ _ _ Et).
           eexists. split; [reflexivity|]. simpl.
           apply H0; simpl; try lia; try exact I.
           intros _ E3 [Hx [Hy Hu]].
           assert (a = 0) by lia. subst a. destruct (HZ' eq_refl) as [Hy2 _]. lia.
        -- destruct HW as [Hp Hrest].
           cbn [top fst snd mturnE].
           assert (Et : S (S a) + (q + 0) = S (S a + (q + 0))) by lia.
           rewrite (Aout_S _ _ _ _ _ _ _ Et).
           eexists. split; [reflexivity|]. simpl.
           apply H0; try lia; try exact Hrest.
    + rewrite mread_odd. destruct W as [|p2 rest].
      * unfold mone, mturn. destruct q as [|q].
        -- eexists. split; [reflexivity|]. simpl.
           apply H3o with (q := 0); [reflexivity|discriminate|simpl; split; [lia|exact I]|].
           intros _. exact HZ'.
        -- change (rep1 (S q) (0 :: S (S a) :: L2)) with (1 :: rep1 q (0 :: S (S a) :: L2)). cbn [bump top fst snd].
           change (4 + 1) with 5.
           rewrite mturnE_rep. cbn [mturnE].
           assert (Et : S (S a) + (q + 0) = S (S a + (q + 0))) by lia.
           rewrite (Aout_S _ _ _ _ _ _ _ Et).
           eexists. split; [reflexivity|]. simpl.
           destruct (par (q + 0)) as [[e He]|[e He]].
           ++ apply H3e with (q := e); [lia|discriminate|simpl; split; [lia|exact I]|].
              destruct e as [|[|e]]; simpl; try lia.
              split; [lia|]. intros Ex. assert (a = 0) by lia. subst a.
              destruct (HZ' eq_refl) as [Hy2 _]. exact Hy2.
           ++ apply H3o with (q := S e); [lia|discriminate|simpl; split; [lia|exact I]|discriminate].
      * destruct HW as [Hp Hrest]. destruct p2 as [|p2]; [lia|].
        destruct q as [|q].
        -- eexists. split; [reflexivity|]. simpl. split; [|apply T1; exact Hrest].
           unfold Tr, Zr. simpl. split; [lia|]. split; [|discriminate].
           intros _. split; [lia|]. intros Ev. destruct (HZ' Ev) as [Hy _]. exact Hy.
        -- eexists. split; [reflexivity|]. simpl. split; [|apply T1; exact Hrest].
           unfold Tr, Zr. simpl. split; [lia|]. split; [discriminate|].
           intros _ [Hy Hu]. destruct q as [|q]; simpl in Hy, Hu; lia.
  - (* R = 0 0 W *)
    destruct W as [|w W']; [contradiction|].
    eexists. split; [reflexivity|]. simpl.
    apply H0; try lia; try exact HW; try discriminate.
    intros _ Ev. destruct (HZ' Ev) as [Hy _]. exact Hy.
  - (* R = 0 0 0 W *)
    eexists. split; [reflexivity|]. simpl.
    apply H1 with (q := 0); [reflexivity|exact HN|exact HW].
Qed.

(* The hub: L = 1 :: L1. *)
Lemma inv_hub : forall L1 z R1, Hub (nth 0 L1 0) (nth 1 L1 0) (nth 2 L1 0) z R1 -> OK (mstep (1 :: L1, z :: R1)).
Proof.
  intros L1 z R1 H. unfold mstep. cbn [fst snd].
  destruct H as [z W Hz HW H1z H2z H5 H3|z q W E HN HW|z q W E HN HW Hx|z q W E HN HW Hne|z q W E HN HW Hs|z q W E HN HW Hq|z q W E HN HW Hq|z q W E HN HW|z q W E HN HW].
  - (* H0 *)
    destruct (par z) as [[q E]|[q E]]; subst z.
    + destruct q as [|q]; [lia|].
      rewrite mread_even. unfold mturn.
      change (rep1 (S q) (1 :: L1)) with (1 :: rep1 q (1 :: L1)). cbn [top fst snd].
      rewrite mturnE_rep. simpl mturnE.
      assert (Hrest : zf (snd (top W))) by (destruct W as [|w W']; [exact I|exact (proj2 HW)]).
      apply k1_gen; [lia|exact Hrest|].
      intros Eq Hx Hy. assert (q = 0) by lia. subst q.
      specialize (H2z eq_refl). rewrite Hx in H2z. specialize (H2z eq_refl). lia.
    + rewrite mread_odd. destruct W as [|p rest].
      * destruct q as [|q]; [specialize (H1z eq_refl); destruct H1z; contradiction|].
        unfold mone, mturn.
        change (rep1 (S q) (1 :: L1)) with (1 :: rep1 q (1 :: L1)). cbn [bump top fst snd].
        change (4 + 1) with 5.
        rewrite mturnE_rep. simpl mturnE.
        apply tg.
        -- intros i a L3. eexists. split; [reflexivity|]. simpl.
           apply H4 with (q := i + S (q + 0)); [reflexivity|discriminate|simpl; split; [lia|exact I]|intros; lia].
        -- intros i L4 Hj Hzz.
           remember (nth (S i) L1 0) as ns.
           assert (Et : ns + (i + S (q + 0)) = S (ns + (i + S (q + 0)) - 1)) by lia.
           rewrite (Aout_S _ _ _ _ _ _ _ Et).
           eexists. split; [reflexivity|]. simpl.
           destruct (par (i + S (q + 0))) as [[e He]|[e He]].
           ++ apply H3e with (q := e); [lia|discriminate|simpl; split; [lia|exact I]|].
              destruct e as [|[|e]]; simpl; try lia.
              split; [lia|]. intros Ex Hc. clear Hc.
              assert (ns = 0) by lia. subst ns.
              destruct i as [|[|i]]; [|destruct q|lia]; try lia.
              apply (H3 eq_refl eq_refl). split; [|split; [exact Hzz|assumption]].
              apply Hj. lia.
           ++ apply H3o with (q := S e); [lia|discriminate|simpl; split; [lia|exact I]|discriminate].
      * destruct HW as [Hp Hrest]. destruct p as [|p]; [lia|].
        destruct q as [|q].
        -- eexists. split; [reflexivity|]. simpl. split; [|apply T1; exact Hrest].
           unfold Tr, Zr. simpl. split; [lia|]. split; [discriminate|].
           intros _ [Hx _]. destruct (H1z eq_refl) as [Hx0 _]. contradiction.
        -- eexists. split; [reflexivity|]. simpl. split; [|apply T1; exact Hrest].
           unfold Tr, Zr. simpl. split; [lia|]. split; [discriminate|].
           intros _ [Hy _]. destruct q; simpl in Hy; lia.
  - (* H1 *)
    subst z. rewrite mread_even. unfold mturn.
    change (rep1 (S q) (1 :: L1)) with (1 :: rep1 q (1 :: L1)). cbn [top fst snd].
    rewrite mturnE_rep. simpl mturnE.
    destruct W as [|w W']; [contradiction|].
    apply k1_gen; [lia|exact HW|]. intros _ _ _. left. discriminate.
  - (* H2e *)
    subst z. rewrite mread_even. unfold mturn.
    change (rep1 (S q) (1 :: L1)) with (1 :: rep1 q (1 :: L1)). cbn [top fst snd].
    rewrite mturnE_rep. simpl mturnE.
    destruct L1 as [|a L2]; [simpl in Hx; lia|].
    destruct a as [|[|a]]; simpl in Hx; try lia.
    eexists. split; [reflexivity|]. simpl.
    apply HQ with (q := q + 0); [lia|exact HN|exact HW].
  - (* H2o *)
    subst z. rewrite mread_odd.
    destruct W as [|w W']; [contradiction|].
    destruct HW as [Hw HW']. destruct w as [|w]; [lia|].
    destruct q as [|q].
    + eexists. split; [reflexivity|]. simpl. split; [simpl; split; [lia|exact HW']|exact Hne].
    + eexists. split; [reflexivity|]. simpl. split; [simpl; split; [lia|exact HW']|exact Hne].
  - (* H3e *)
    subst z. rewrite mread_even. unfold mturn.
    change (rep1 (S q) (1 :: L1)) with (1 :: rep1 q (1 :: L1)). cbn [top fst snd].
    rewrite mturnE_rep. simpl mturnE.
    destruct L1 as [|a L2].
    + destruct q as [|[|q]]; simpl in Hs; lia.
    + destruct a as [|[|a]].
      * destruct q as [|[|q]]; simpl in Hs; lia.
      * simpl mturnE.
        destruct q as [|[|q]].
        -- simpl in Hs. destruct Hs as [_ Hy]. specialize (Hy eq_refl).
           destruct L2 as [|b L3]; [simpl in Hy; lia|]. simpl in Hy.
           destruct b as [|[|b]]; try lia.
           eexists. split; [reflexivity|]. simpl.
           apply HP with (q := 1); [lia|exact HN|exact HW].
        -- simpl in Hs. destruct Hs as [_ Hne]. specialize (Hne eq_refl).
           apply tg.
           ++ intros i a' L3. eexists. split; [reflexivity|]. simpl.
              apply HP with (q := i + 2); [lia|exact HN|exact HW].
           ++ intros i L4 Hj Hzz.
              remember (nth (S i) L2 0) as ns.
              assert (Et : ns + (i + S (S (1 + 0))) = S (ns + (i + 3) - 1)) by lia.
              rewrite (Aout_S _ _ _ _ _ _ _ Et).
              eexists. split; [reflexivity|]. simpl.
              destruct (par (i + 3)) as [[e He]|[e He]].
              ** apply H2o with (q := e + 1); [lia|exact HN|exact HW|exact Hne].
              ** apply H2e with (q := e + 1); [lia|exact HN|exact HW|lia].
        -- simpl in Hs. lia.
      * eexists. split; [reflexivity|]. simpl.
        apply HP with (q := q + 0); [lia|exact HN|exact HW].
  - (* H3o *)
    subst z. rewrite mread_odd. destruct W as [|w W']; [contradiction|].
    destruct HW as [Hw HW'].
    assert (Hne : 1 + w :: W' <> [1]) by (intros Hc; injection Hc; lia).
    unfold mone, mturn.
    destruct q as [|q].
    + cbn [rep1 bump top fst snd]. change (4 + 1) with 5.
      apply k5_zero; [exact HW'|exact Hne|exact (Hq eq_refl)].
    + change (rep1 (S q) (1 :: L1)) with (1 :: rep1 q (1 :: L1)). cbn [bump top fst snd].
      change (4 + 1) with 5. rewrite mturnE_rep. simpl mturnE.
      apply k5_gen; [lia|exact HW'|exact Hne].
  - (* H4 *)
    subst z. rewrite mread_odd. destruct W as [|w W']; [contradiction|].
    assert (Hne : 1 + 0 :: w :: W' <> [1]) by discriminate.
    unfold mone, mturn.
    destruct q as [|q].
    + cbn [rep1 bump top fst snd]. change (4 + 1) with 5.
      apply k5_zero; [exact HW|exact Hne|exact (Hq eq_refl)].
    + change (rep1 (S q) (1 :: L1)) with (1 :: rep1 q (1 :: L1)). cbn [bump top fst snd].
      change (4 + 1) with 5. rewrite mturnE_rep. simpl mturnE.
      apply k5_gen; [lia|exact HW|exact Hne].
  - (* HP *)
    subst z. rewrite mread_odd.
    eexists. split; [reflexivity|]. simpl. split.
    + unfold Tr, Zr. simpl. split; [lia|]. split; [discriminate|].
      intros _ [Hy _]. destruct q; simpl in Hy; lia.
    + apply T3; [exact HN|exact HW].
  - (* HQ *)
    subst z. rewrite mread_odd.
    eexists. split; [reflexivity|]. simpl. split.
    + unfold Tr, Zr. simpl. split; [lia|]. split; [discriminate|].
      intros _ [Hy _]. destruct q; simpl in Hy; lia.
    + apply T2; [exact HN|exact HW].
Qed.

Theorem inv_step : forall s, Inv s -> exists s', mstep s = Some s' /\ Inv s'.
Proof.
  intros [L R] H. destruct L as [|t L]; [destruct R; contradiction|].
  destruct R as [|z R1]; [destruct t as [|[|[|[|[|[|t]]]]]]; try contradiction; destruct L; contradiction|].
  destruct t as [|[|[|[|[|[|t]]]]]]; try contradiction.
  - destruct L as [|a L2]; [contradiction|].
    destruct H as [HT HR]. exact (inv_t0 a L2 z R1 HT HR).
  - exact (inv_hub L z R1 H).
  - destruct H as [HZ HN]. exact (inv_t5 L z R1 HZ HN).
Qed.

(* From the blank tape: 28 steps of the machine. *)
Definition s0 : list nat * list nat := ([1; 1; 0; 1], [2]).

Lemma start : c0 -->* CC s0.
Proof.
  unfold c0, tape0, CC, s0. simpl. execute.
Qed.

Lemma inv0 : Inv s0.
Proof.
  simpl. apply H0; simpl; try lia; try exact I; discriminate.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (c' := CC s0).
  - exact start.
  - apply (progress_nonhalt_cond tm _ _ CC Inv).
    + intros s Hs. destruct (inv_step s Hs) as [s' [E Hs']].
      exists s'. split; [apply mstep_ok; exact E|exact Hs'].
    + exact inv0.
Qed.

End TM1.

Print Assumptions TM1.nonhalt.
