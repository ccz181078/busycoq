(* 1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD (TM1), 1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF (TM2) and
   1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC (TM3) do not halt from the blank tape. They are one table: TM2 is TM1
   started in F and TM3 is TM1 mirrored and started in D, up to the names of the states. The comments are in TM1's names.

   Digits. Cells to the left of the head read as digits: digit g is (10)^g 01 ([dg]). A tape at the right end of a sweep ends in
     3^n and the partial digit (10)^3 0, the head in state D on a blank ([END]); the cells before 3^n are digits where the borrow law applies, not always (the marker P, the counters xr).

   Moves. State D on 0 with j ones and then a zero to its left does one of four things by the cells beyond ([D_Ra], [D_Rb], [D_L], [D_R]). State C goes right by a prefix code: 01 -> 10, 111 -> 010, 1011 -> 1010, 1000 -> 0110, it stops on 00, 110, 1010, and 1001 is the only way to the halt ([C_01] ...).

   Borrow law, for all digit stacks ([bw], [bw_ok], [sweep_tail]). A sweep goes left through digits 2 and 3 and writes them to the right as tokens; g >= 4 becomes g - 3 and it turns back; a digit 1 between x and z: if x >= 3 then x - 2, z + 1 and it turns back, if x <= 2 then x + 1, z + 1 and it goes on. If it stops before the wall the right pass restores the digits, so the two stacks are one digit word, and the tail gets one more 3, or a 4 below it when the digit below the tail is 1.

   Bulk laws, for all sizes. [r1] .. [r4]: passes over 3^n and over (3 1 2)^n. [hop_q]: the odd marker P = 1 0 0 1 0 0 1 before the tail moves two digits right per sweep and leaves (2 1 3)^q behind ("2 4 3 P 3 3" -> "2 1 3 2 4 3 P"). [eat_q]: a zone (3 4)^k below a short word (keys [key1], [key2]) loses 4 units and the tail gains 18 digits in 36 sweeps. [r5]: a mis-synchronized pass over the tokens of (3 1 2)^(2k), which happens when such a sweep finds no stopper, writes a counter xr^k: a block of 36 cells, and the tail starts again from a few digits.

   Simulator. [astep] works on stacks of cells and repeated blocks ([ex], [lift]), and [runp] iterates it, sound for any left part it does not read ([astep_ok], [runp_ok]). Which rule fires is decided by the data; nothing else is assumed about the run.

   The run. From the blank tape [runp] reaches, in 6902025 macro steps, a tape with a counter of at least K2 units on top of the left stack ([blank_run]). From there, for every X below the counter, 2037113 macro steps give the same top with a new counter of K2 units, K2 = 732592001087343581, and below it Lit and the old one 39 units shorter ([cyc_run]); nothing below the counter is ever read, so this is a translated cycle ([cycle]). K2, K3 and the words R0 and Lit are data in this file; [vm_cast_no_check] has the kernel compare them at Qed with what [runp] computes. Measured outside this file: the tail reaches about 3 * 10^18 digits in a cycle. The raw number of steps is not computed. *)
From BusyCoq Require Import Individual62.
From Coq Require Import Lia PeanoNat NArith String.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint ones (n : nat) : list Sym :=
  match n with O => [] | S n' => S1 :: ones n' end.

Fixpoint pr (n : nat) : list Sym :=
  match n with O => [] | S n' => S0 :: S1 :: pr n' end.

Lemma ones_shift : forall n (s : side), ones n *> S1 >> s = S1 >> ones n *> s.
Proof. induction n as [|n IH]; intros s; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma E_run : forall j l r, ones j *> l <{{E}} r -->* l <{{E}} ones j *> r.
Proof.
  induction j as [|j IH]; intros l r; [finish|].
  simpl. step. follow IH. rewrite ones_shift. finish.
Qed.

(* The four moves of the sweep state on 0, with j ones between head and the first 0 on its left. *)
Lemma D_Ra : forall j l r,
  ones j *> S0 >> S1 >> l {{D}}> S0 >> r -->* S0 >> S1 >> l {{C}}> ones j *> S1 >> r.
Proof. intros. step. follow E_run. do 5 step. finish. Qed.

Lemma D_Rb : forall j l r,
  ones j *> S0 >> S0 >> S0 >> l {{D}}> S0 >> r -->* S0 >> S1 >> S0 >> S1 >> l {{C}}> ones j *> r.
Proof.
  intros. step. follow E_run. do 7 step. rewrite ones_shift. do 3 step. finish.
Qed.

Lemma D_L : forall j l r,
  ones j *> S0 >> S0 >> S1 >> S0 >> l {{D}}> S0 >> r -->*
  l {{D}}> S0 >> S0 >> S0 >> S0 >> ones j *> S1 >> r.
Proof. intros. step. follow E_run. do 5 step. finish. Qed.

Lemma D_R : forall j l r,
  ones j *> S0 >> S0 >> S1 >> S1 >> S0 >> l {{D}}> S0 >> r -->*
  S0 >> S0 >> S1 >> l {{D}}> S0 >> S0 >> ones j *> S1 >> r.
Proof. intros. step. follow E_run. do 9 step. finish. Qed.

(* The reader state goes to the right by a prefix code. Every output ends in 1 0. *)
Lemma C_01 : forall l r, l {{C}}> S0 >> S1 >> r -->* S0 >> S1 >> l {{C}}> r.
Proof. intros. do 4 step. finish. Qed.
Lemma C_111 : forall l r, l {{C}}> S1 >> S1 >> S1 >> r -->* S0 >> S1 >> S0 >> l {{C}}> r.
Proof. intros. do 5 step. finish. Qed.
Lemma C_1011 : forall l r, l {{C}}> S1 >> S0 >> S1 >> S1 >> r -->* S0 >> S1 >> S0 >> S1 >> l {{C}}> r.
Proof. intros. do 10 step. finish. Qed.
Lemma C_1000 : forall l r, l {{C}}> S1 >> S0 >> S0 >> S0 >> r -->* S0 >> S1 >> S1 >> S0 >> l {{C}}> r.
Proof. intros. do 4 step. finish. Qed.
Lemma C_00 : forall l r, l {{C}}> S0 >> S0 >> r -->* S0 >> l {{D}}> S0 >> r.
Proof. intros. step. finish. Qed.
Lemma C_110 : forall l r, l {{C}}> S1 >> S1 >> S0 >> r -->* S0 >> S0 >> l {{D}}> S0 >> r.
Proof. intros. do 2 step. finish. Qed.
Lemma C_1010 : forall l r, l {{C}}> S1 >> S0 >> S1 >> S0 >> r -->* S0 >> S0 >> S1 >> l {{D}}> S0 >> r.
Proof. intros. do 7 step. finish. Qed.

(* Digits. A digit g is (10)^g 01 on the tape; a left side is written nearest the head first. *)
Definition dg (g : nat) (l : side) : side := S1 >> S0 >> pr g *> l.

Fixpoint lw (w : list nat) (l : side) : side :=
  match w with
  | [] => l
  | g :: w' => dg g (lw w' l)
  end.

Definition tk (a : nat) (r : side) : side := ones a *> S0 >> S0 >> S0 >> r.
Definition tk1 (a : nat) (r : side) : side := ones a *> S0 >> r.

Notation LS k l r := (ones k *> l {{D}}> S0 >> S0 >> S0 >> S0 >> r).
Notation LG g l r := (S0 >> pr g *> l {{D}}> S0 >> S0 >> r).
Notation HH v l r := (S0 >> S0 >> S1 >> S0 >> pr v *> l {{D}}> S0 >> S0 >> r).

Lemma xc : forall l T,
  S1 >> S0 >> S1 >> l {{D}}> S0 >> S0 >> S0 >> S0 >> T -->*
  S1 >> S1 >> l {{D}}> S0 >> S0 >> S0 >> S0 >> S1 >> T.
Proof.
  intros l T.
  mid (S0 >> S1 >> l {{C}}> S1 >> S1 >> S0 >> S0 >> S0 >> T).
  { exact (D_Ra 1 l (S0 >> S0 >> S0 >> T)). }
  follow C_110.
  follow (D_Rb 0 (S1 >> l) (S0 >> S0 >> T)). simpl.
  follow C_00.
  follow (D_L 0 (S1 >> S1 >> l) T). finish.
Qed.

Lemma stopx : forall l T,
  S1 >> S1 >> S0 >> S1 >> l {{D}}> S0 >> S0 >> S0 >> S0 >> T -->*
  S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> l {{D}}> S0 >> S0 >> T.
Proof.
  intros l T.
  mid (S0 >> S1 >> l {{C}}> S1 >> S1 >> S1 >> S0 >> S0 >> S0 >> T).
  { exact (D_Ra 2 l (S0 >> S0 >> S0 >> T)). }
  follow C_111. follow C_00. finish.
Qed.

Lemma ls_2 : forall k l r, LS k (dg 2 l) r -->* LS 1 l (tk (k + 2) r).
Proof.
  intros k l r. unfold dg. simpl pr. simpl.
  rewrite ones_shift.
  mid (S1 >> l {{D}}> S0 >> S0 >> S0 >> S0 >> ones (S k) *> S1 >> S0 >> S0 >> S0 >> r).
  { exact (D_L (S k) (S1 >> l) (S0 >> S0 >> S0 >> r)). }
  rewrite ones_shift. unfold tk.
  replace (k + 2) with (S (S k)) by lia. finish.
Qed.

Lemma ls_3 : forall k l r, LS k (dg 3 l) r -->* LS 2 l (tk (k + 3) r).
Proof.
  intros k l r. unfold dg. simpl pr. simpl.
  rewrite ones_shift.
  mid (S1 >> S0 >> S1 >> l {{D}}> S0 >> S0 >> S0 >> S0 >> ones (S k) *> S1 >> S0 >> S0 >> S0 >> r).
  { exact (D_L (S k) (S1 >> S0 >> S1 >> l) (S0 >> S0 >> S0 >> r)). }
  follow xc. rewrite ones_shift. unfold tk.
  replace (k + 3) with (S (S (S k))) by lia. simpl. finish.
Qed.

Lemma ls_g : forall k g l r, LS k (dg (g + 4) l) r -->* HH (g + 1) l (tk (k + 3) r).
Proof.
  intros k g l r.
  replace (g + 4) with (S (S (S (S g)))) by lia.
  replace (g + 1) with (S g) by lia.
  unfold dg. simpl pr. simpl.
  rewrite ones_shift.
  mid (S1 >> S0 >> S1 >> S0 >> S1 >> pr g *> l {{D}}> S0 >> S0 >> S0 >> S0 >> ones (S k) *> S1 >> S0 >> S0 >> S0 >> r).
  { exact (D_L (S k) (S1 >> S0 >> S1 >> S0 >> S1 >> pr g *> l) (S0 >> S0 >> S0 >> r)). }
  follow xc. follow stopx. rewrite ones_shift. unfold tk.
  replace (k + 3) with (S (S (S k))) by lia. simpl. finish.
Qed.

Lemma ls_1 : forall k x l r, LS k (dg 1 (dg x l)) r -->* LG (x + 1) l (tk (k + 2) r).
Proof.
  intros k x l r. unfold dg. simpl pr. simpl.
  rewrite ones_shift.
  mid (S0 >> S0 >> S1 >> pr x *> l {{D}}> S0 >> S0 >> ones (S k) *> S1 >> S0 >> S0 >> S0 >> r).
  { exact (D_R (S k) (pr x *> l) (S0 >> S0 >> S0 >> r)). }
  rewrite ones_shift. unfold tk.
  replace (x + 1) with (S x) by lia.
  replace (k + 2) with (S (S k)) by lia. finish.
Qed.

Lemma lg_2 : forall l r, LG 2 l r -->* LS 1 l (tk1 1 r).
Proof.
  intros l r. simpl pr.
  mid (S1 >> l {{D}}> S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> r).
  { exact (D_L 0 (S1 >> l) (S0 >> r)). }
  finish.
Qed.

Lemma lg_3 : forall l r, LG 3 l r -->* LS 2 l (tk1 2 r).
Proof.
  intros l r. simpl pr.
  mid (S1 >> S0 >> S1 >> l {{D}}> S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> r).
  { exact (D_L 0 (S1 >> S0 >> S1 >> l) (S0 >> r)). }
  follow xc. finish.
Qed.

Lemma lg_g : forall g l r, LG (g + 4) l r -->* HH (g + 1) l (tk1 2 r).
Proof.
  intros g l r.
  replace (g + 4) with (S (S (S (S g)))) by lia.
  replace (g + 1) with (S g) by lia.
  simpl pr.
  mid (S1 >> S0 >> S1 >> S0 >> S1 >> pr g *> l {{D}}> S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> r).
  { exact (D_L 0 (S1 >> S0 >> S1 >> S0 >> S1 >> pr g *> l) (S0 >> r)). }
  follow xc. follow stopx. finish.
Qed.

(* The right pass from a hand v. *)
Lemma hh_c : forall v l T,
  HH (S v) l T -->* S0 >> S1 >> dg (S v) l {{C}}> S1 >> S0 >> T.
Proof.
  intros v l T. unfold dg. simpl pr.
  mid (S0 >> S1 >> pr v *> l {{D}}> S0 >> S0 >> S0 >> S0 >> S1 >> S0 >> T).
  { exact (D_L 0 (S0 >> S1 >> pr v *> l) (S0 >> T)). }
  mid (S0 >> S1 >> pr v *> l {{C}}> S1 >> S0 >> S0 >> S0 >> S1 >> S0 >> T).
  { exact (D_Ra 0 (pr v *> l) (S0 >> S0 >> S0 >> S1 >> S0 >> T)). }
  follow C_1000. simpl. finish.
Qed.

Lemma hh_5 : forall v l r, HH (S v) l (tk 5 r) -->* HH 3 (dg (S v) l) r.
Proof.
  intros v l r. follow hh_c. unfold tk. simpl ones.
  follow C_1011. follow C_111. follow C_00. finish.
Qed.

(* After a stop 1 1 0 with hand (10)^(e+2): back to hand e+1, next token one longer. *)
Lemma back : forall e l r,
  S0 >> S0 >> pr (S (S e)) *> l {{D}}> S0 >> S0 >> S0 >> r -->*
  S0 >> S0 >> S1 >> S0 >> pr (S e) *> l {{D}}> S0 >> S0 >> S1 >> r.
Proof.
  intros e l r. simpl pr.
  follow (D_Rb 0 (S1 >> S0 >> S1 >> pr e *> l) (S0 >> S0 >> r)). simpl.
  follow C_00.
  follow (D_L 0 (S1 >> S1 >> S0 >> S1 >> pr e *> l) r).
  simpl.
  mid (S0 >> S1 >> pr e *> l {{C}}> S1 >> S1 >> S1 >> S0 >> S0 >> S0 >> S1 >> r).
  { exact (D_Ra 2 (pr e *> l) (S0 >> S0 >> S0 >> S1 >> r)). }
  follow C_111. follow C_00. finish.
Qed.

Lemma hh_4 : forall v l r, HH (S v) l (tk 4 r) -->* HH 2 (dg (S v) l) (S1 >> r).
Proof.
  intros v l r. follow hh_c. unfold tk. simpl ones.
  follow C_1011. follow C_110.
  exact (back 1 (dg (S v) l) r).
Qed.

Lemma hh_m3 : forall v l r, HH (S v) l (tk1 2 (tk 4 r)) -->* HH 4 (dg (S v) l) r.
Proof.
  intros v l r. follow hh_c. unfold tk, tk1. simpl ones.
  follow C_1011. follow C_01. follow C_111. follow C_00. finish.
Qed.

Lemma hh_m2 : forall v l r, HH (S v) l (tk1 2 (tk 3 r)) -->* HH 3 (dg (S v) l) (S1 >> r).
Proof.
  intros v l r. follow hh_c. unfold tk, tk1. simpl ones.
  follow C_1011. follow C_01. follow C_110.
  exact (back 2 (dg (S v) l) r).
Qed.

(* The tape at the right end of a sweep: partial digit <6><1>, blank to the right. *)
Definition END (l : side) : Q * tape := S0 >> pr 3 *> l {{D}}> const S0.

Lemma hh_end : forall v l, HH (S v) l (tk1 2 (const S0)) -->* END (dg (S v) l).
Proof.
  intros v l. follow hh_c. unfold tk1, END. simpl ones.
  mid (S0 >> S1 >> S0 >> S1 >> S0 >> S1 >> dg (S v) l {{C}}> S0 >> const S0).
  { exact (C_1011 _ _). }
  rewrite (const_unfold _ S0).
  follow C_00. finish.
Qed.

Lemma end_lg : forall l, END l = LG 3 l (const S0).
Proof. intros l. unfold END. rewrite <- !const_unfold. reflexivity. Qed.

(* One borrow, on the digit word. z is the digit to the right of w; the result h is its new value (z or z+1). *)
Fixpoint bw (z : nat) (w : list nat) : option (nat * list nat) :=
  match w with
  | [] => None
  | 0 :: _ => None
  | 1 :: w1 =>
      match w1 with
      | [] => None
      | 0 :: _ => None
      | 1 :: w2 => match bw 2 w2 with Some (h, W) => Some (z + 1, h :: W) | None => None end
      | 2 :: w2 => match bw 3 w2 with Some (h, W) => Some (z + 1, h :: W) | None => None end
      | S (S (S x)) :: w2 => Some (z + 1, S x :: w2)
      end
  | 2 :: w1 => match bw 2 w1 with Some (h, W) => Some (z, h :: W) | None => None end
  | 3 :: w1 => match bw 3 w1 with Some (h, W) => Some (z, h :: W) | None => None end
  | S (S (S (S g))) :: w1 => Some (z, S g :: w1)
  end.

(* read form: the raw right stack as the hand reads it. *)
Definition rf (z : nat) (r : side) : side := if Nat.eqb z 2 then S1 >> r else r.

Lemma hh_z : forall z v l r, (z = 2 \/ z = 3) ->
  HH (S v) l (tk (z + 2) r) -->* HH z (dg (S v) l) (rf z r).
Proof.
  intros z v l r [-> | ->].
  - apply hh_4.
  - apply hh_5.
Qed.

Lemma hh_zm : forall z v l r, (z = 2 \/ z = 3) ->
  HH (S v) l (tk1 2 (tk (z + 1) r)) -->* HH (z + 1) (dg (S v) l) (rf z r).
Proof.
  intros z v l r [-> | ->].
  - apply hh_m2.
  - apply hh_m3.
Qed.

Lemma bw_hand : forall w z h W, (z = 2 \/ z = 3) -> bw z w = Some (h, W) -> exists v, h = S v.
Proof.
  destruct w as [|g w]; intros z h W Hz H; [discriminate|].
  destruct g as [|[|[|[|g]]]]; simpl in H.
  - discriminate.
  - destruct w as [|x w]; [discriminate|].
    destruct x as [|[|[|x]]];
      [discriminate| |destruct (bw 3 w) as [[h1 W1]|]; [|discriminate] |];
      try (destruct (bw 2 w) as [[h1 W1]|]; [|discriminate]);
      injection H as <- <-; exists z; lia.
  - destruct (bw 2 w) as [[h1 W1]|]; [|discriminate]. injection H as <- <-.
    destruct Hz as [-> | ->]; eauto.
  - destruct (bw 3 w) as [[h1 W1]|]; [|discriminate]. injection H as <- <-.
    destruct Hz as [-> | ->]; eauto.
  - injection H as <- <-. destruct Hz as [-> | ->]; eauto.
Qed.

(* The law: from a left pass form with prev digit z, the borrow comes back with hand h. *)
Lemma bw_ok : forall w z h W l r, (z = 2 \/ z = 3) -> bw z w = Some (h, W) ->
  LS (z - 1) (lw w l) r -->* HH h (lw W l) (rf z r).
Proof.
  fix IH 1.
  intros w z h W l r Hz H.
  destruct w as [|g w]; [discriminate|].
  destruct g as [|[|[|[|g]]]]; simpl in H.
  - discriminate.
  - (* digit 1 *)
    destruct w as [|x w]; [discriminate|].
    destruct x as [|[|[|x]]].
    + discriminate.
    + (* x = 1 *)
      destruct (bw 2 w) as [[h1 W1]|] eqn:E; [|discriminate]. injection H as <- <-.
      destruct (bw_hand _ _ _ _ (or_introl eq_refl) E) as [v ->].
      simpl lw.
      follow ls_1. simpl (1 + 1). follow lg_2.
      follow (IH w 2 (S v) W1 l (tk1 1 (tk (z - 1 + 2) r)) (or_introl eq_refl) E).
      replace (rf 2 (tk1 1 (tk (z - 1 + 2) r))) with (tk1 2 (tk (z + 1) r)).
      2:{ unfold rf, tk1. simpl. replace (z - 1 + 2) with (z + 1) by (destruct Hz; lia). reflexivity. }
      apply hh_zm. exact Hz.
    + (* x = 2 *)
      destruct (bw 3 w) as [[h1 W1]|] eqn:E; [|discriminate]. injection H as <- <-.
      destruct (bw_hand _ _ _ _ (or_intror eq_refl) E) as [v ->].
      simpl lw.
      follow ls_1. simpl (2 + 1). follow lg_3.
      follow (IH w 3 (S v) W1 l (tk1 2 (tk (z - 1 + 2) r)) (or_intror eq_refl) E).
      replace (rf 3 (tk1 2 (tk (z - 1 + 2) r))) with (tk1 2 (tk (z + 1) r)).
      2:{ unfold rf. simpl. replace (z - 1 + 2) with (z + 1) by (destruct Hz; lia). reflexivity. }
      apply hh_zm. exact Hz.
    + (* x >= 3 *)
      injection H as <- <-.
      simpl lw.
      follow ls_1.
      replace (S (S (S x)) + 1) with (x + 4) by lia.
      follow lg_g. replace (x + 1) with (S x) by lia.
      replace (z - 1 + 2) with (z + 1) by (destruct Hz; lia).
      simpl lw. apply hh_zm. exact Hz.
  - (* digit 2 *)
    destruct (bw 2 w) as [[h1 W1]|] eqn:E; [|discriminate]. injection H as <- <-.
    destruct (bw_hand _ _ _ _ (or_introl eq_refl) E) as [v ->].
    simpl lw.
    follow ls_2.
    follow (IH w 2 (S v) W1 l (tk (z - 1 + 2) r) (or_introl eq_refl) E).
    replace (rf 2 (tk (z - 1 + 2) r)) with (tk (z + 2) r).
    2:{ unfold rf, tk. simpl. replace (z + 2) with (S (z - 1 + 2)) by (destruct Hz; lia). reflexivity. }
    apply hh_z. exact Hz.
  - (* digit 3 *)
    destruct (bw 3 w) as [[h1 W1]|] eqn:E; [|discriminate]. injection H as <- <-.
    destruct (bw_hand _ _ _ _ (or_intror eq_refl) E) as [v ->].
    simpl lw.
    follow ls_3.
    follow (IH w 3 (S v) W1 l (tk (z - 1 + 3) r) (or_intror eq_refl) E).
    replace (rf 3 (tk (z - 1 + 3) r)) with (tk (z + 2) r).
    2:{ unfold rf. simpl. replace (z - 1 + 3) with (z + 2) by (destruct Hz; lia). reflexivity. }
    apply hh_z. exact Hz.
  - (* digit g + 4: stop *)
    injection H as <- <-.
    replace (S (S (S (S g)))) with (g + 4) by lia.
    simpl lw.
    follow ls_g. replace (g + 1) with (S g) by lia.
    replace (z - 1 + 3) with (z + 2) by (destruct Hz; lia).
    apply hh_z. exact Hz.
Qed.

(* Repeated blocks. *)
Fixpoint rep (c : list Sym) (n : nat) (s : side) : side :=
  match n with
  | O => s
  | S n' => c *> rep c n' s
  end.

Lemma rep_shift : forall c n s, rep c n (c *> s) = c *> rep c n s.
Proof. induction n as [|n IH]; intros s; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma rep_add : forall c a b s, rep c (a + b) s = rep c a (rep c b s).
Proof. induction a as [|a IH]; intros b s; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Definition x3 : list Sym := [S1;S0;S0;S1;S0;S1;S0;S1].
Definition y5 : list Sym := [S1;S1;S1;S1;S1;S0;S0;S0].
Definition xcc : list Sym := [S1;S0;S0;S1;S0;S1;S0;S1; S1;S0;S0;S1; S1;S0;S0;S1;S0;S1].
Definition ycc : list Sym := [S1;S1;S0; S1;S1;S1;S1;S0;S0;S0; S1;S1;S1;S1;S1;S0;S0;S0].
Definition x43 : list Sym := [S1;S0;S0;S1;S0;S1;S0;S1;S0;S1; S1;S0;S0;S1;S0;S1;S0;S1].
(* one unit of the counter, nearest the head first *)
Definition xr : list Sym :=
  [S0;S1;S0;S1;S1;S0;S0;S1;S0;S1;S1;S1;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S0;S1;S0;S1;S1;S0;S0;S1;S0;S1].

Lemma x3_dg : forall l, x3 *> l = dg 3 l.
Proof. reflexivity. Qed.
Lemma y5_tk : forall r, y5 *> r = tk 5 r.
Proof. reflexivity. Qed.
Lemma xcc_dg : forall l, xcc *> l = dg 3 (dg 1 (dg 2 l)).
Proof. reflexivity. Qed.
Lemma ycc_tk : forall r, ycc *> r = tk1 2 (tk 4 (tk 5 r)).
Proof. reflexivity. Qed.
Lemma x43_dg : forall l, x43 *> l = dg 4 (dg 3 l).
Proof. reflexivity. Qed.

Lemma r1 : forall n l r, LS 2 (rep x3 n l) r -->* LS 2 l (rep y5 n r).
Proof.
  induction n as [|n IH]; intros l r; [finish|].
  change (rep x3 (S n) l) with (dg 3 (rep x3 n l)).
  follow ls_3.
  simpl (2 + 3). follow IH.
  rewrite <- y5_tk. rewrite rep_shift. finish.
Qed.

Lemma r2 : forall n l r, LS 2 (rep xcc n l) r -->* LS 2 l (rep ycc n r).
Proof.
  induction n as [|n IH]; intros l r; [finish|].
  change (rep xcc (S n) l) with (dg 3 (dg 1 (dg 2 (rep xcc n l)))).
  follow ls_3. simpl (2 + 3).
  follow ls_1. simpl (2 + 2).
  simpl (2 + 1). follow lg_3.
  follow IH.
  rewrite <- ycc_tk.
  rewrite rep_shift. finish.
Qed.

Lemma r3 : forall n l r, HH 3 l (rep y5 n r) -->* HH 3 (rep x3 n l) r.
Proof.
  induction n as [|n IH]; intros l r; [finish|].
  change (rep y5 (S n) r) with (tk 5 (rep y5 n r)).
  follow hh_5. follow IH.
  rewrite <- x3_dg. rewrite rep_shift. finish.
Qed.

Lemma r4 : forall n l r, HH 3 l (rep ycc n r) -->* HH 3 (rep x43 n l) r.
Proof.
  induction n as [|n IH]; intros l r; [finish|].
  change (rep ycc (S n) r) with (tk1 2 (tk 4 (tk 5 (rep ycc n r)))).
  follow hh_m3. follow hh_5. follow IH.
  rewrite <- x43_dg. rewrite rep_shift. finish.
Qed.

(* The mis-synchronized pass over the conversion zone writes the counter units. *)
Lemma r5_one : forall l r,
  S0 >> l {{D}}> ycc *> ycc *> r -->* S0 >> xr *> l {{D}}> r.
Proof.
  intros l r. simpl. do 272 step. finish.
Qed.

Lemma r5 : forall k l r,
  S0 >> l {{D}}> rep ycc (k + k) r -->* S0 >> rep xr k l {{D}}> r.
Proof.
  induction k as [|k IH]; intros l r; [finish|].
  replace (S k + S k) with (S (S (k + k))) by lia.
  change (rep ycc (S (S (k + k))) r) with (ycc *> ycc *> rep ycc (k + k) r).
  follow r5_one.
  follow IH.
  rewrite rep_shift. finish.
Qed.

(* A sweep with a tail of 3s: only the word below the tail changes. *)
Lemma sweep_tail : forall n ds h W l, bw 3 ds = Some (h, W) ->
  END (rep x3 (S n) (lw ds l)) -->* END (rep x3 (S n) (lw (h :: W) l)).
Proof.
  intros n ds h W l H.
  destruct (bw_hand _ _ _ _ (or_intror eq_refl) H) as [v ->].
  rewrite end_lg.
  follow lg_3.
  follow r1.
  follow (bw_ok ds 3 (S v) W l (rep y5 (S n) (tk1 2 (const S0))) (or_intror eq_refl) H).
  unfold rf. simpl Nat.eqb. cbv iota.
  change (rep y5 (S n) (tk1 2 (const S0))) with (tk 5 (rep y5 n (tk1 2 (const S0)))).
  follow hh_5.
  follow r3.
  change (rep x3 (S n) (lw (S v :: W) l)) with (dg 3 (rep x3 n (dg (S v) (lw W l)))).
  exact (hh_end 2 _).
Qed.

Fixpoint iterT (p : nat) (x : list nat) : option (list nat) :=
  match p with
  | O => Some x
  | S p' =>
      match bw 3 x with
      | Some (h, W) => iterT p' (h :: W)
      | None => None
      end
  end.

Lemma iterT_ok : forall p x y n l, iterT p x = Some y ->
  END (rep x3 (S n) (lw x l)) -->* END (rep x3 (S n) (lw y l)).
Proof.
  induction p as [|p IH]; intros x y n l H; simpl in H.
  - injection H as <-. finish.
  - destruct (bw 3 x) as [[h W]|] eqn:E; [|discriminate].
    follow (sweep_tail n x h W l E).
    apply IH. exact H.
Qed.

(* The cycles of a zone of (4 3) being eaten: 36 sweeps take 4 units and add 18 digits to the tail. *)
Definition key1 : list nat := [1;1;1;1;3].
Definition key2 : list nat := [1;1;2;4;1].
Definition units4 : list nat := [4;3;4;3;4;3;4;3].

Lemma lw_app : forall a b l, lw (a ++ b) l = lw a (lw b l).
Proof. induction a as [|g a IH]; intros b l; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma lw_rep3 : forall b l, lw (repeat 3 b) l = rep x3 b l.
Proof. induction b as [|b IH]; intros l; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma cyc1 : iterT 36 (key1 ++ units4) = Some (repeat 3 18 ++ key1).
Proof. vm_compute. reflexivity. Qed.
Lemma cyc2 : iterT 36 (key2 ++ units4) = Some (repeat 3 18 ++ key2).
Proof. vm_compute. reflexivity. Qed.

Lemma eat_one : forall key n l, iterT 36 (key ++ units4) = Some (repeat 3 18 ++ key) ->
  END (rep x3 (S n) (lw key (rep x43 4 l))) -->* END (rep x3 (S n + 18) (lw key l)).
Proof.
  intros key n l H.
  pose proof (iterT_ok _ _ _ n l H) as H1.
  rewrite !lw_app, lw_rep3 in H1.
  rewrite rep_add. exact H1.
Qed.

Lemma eat_q : forall key q n l, iterT 36 (key ++ units4) = Some (repeat 3 18 ++ key) ->
  END (rep x3 (S n) (lw key (rep x43 (4 * q) l))) -->* END (rep x3 (S n + 18 * q) (lw key l)).
Proof.
  intros key. induction q as [|q IH]; intros n l H.
  - replace (4 * 0) with 0 by lia. replace (S n + 18 * 0) with (S n) by lia. finish.
  - replace (4 * S q) with (4 + 4 * q) by lia.
    rewrite rep_add.
    follow (eat_one key n (rep x43 (4 * q) l) H).
    replace (S n + 18) with (S (n + 18)) by lia.
    follow (IH (n + 18) l H).
    replace (S (n + 18) + 18 * q) with (S n + 18 * S q) by lia. finish.
Qed.

(* The marker P = 1 0 0 1 0 0 1. A hop: P goes two digits to the right. *)
Definition Pc (l : side) : side := S1 >> S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> l.

Lemma hop_in : forall l R,
  LS 2 (Pc l) (tk 5 (tk 5 R)) -->* LS 1 l (tk1 1 (tk 2 (tk1 1 (tk 3 (tk 6 R))))).
Proof.
  intros l R. unfold Pc, tk, tk1. simpl. do 88 step. finish.
Qed.

Lemma hop_out : forall v l R,
  HH (S v) l (tk1 2 (tk 2 (tk1 1 (tk 3 (tk 6 R))))) -->*
  HH 1 (S0 >> S0 >> S1 >> dg 3 (dg 4 (dg (S v) l))) R.
Proof.
  intros v l R. follow hh_c. unfold tk, tk1. simpl ones.
  follow C_1011. follow C_01. follow C_1000. follow C_1011. follow C_1000.
  follow C_111. follow C_111. follow C_00. finish.
Qed.

Lemma hop_mid : forall l R,
  LS 2 (Pc (dg 3 (dg 4 (dg 2 l)))) (tk 5 (tk 5 (tk 5 R))) -->*
  HH 3 (Pc (dg 3 (dg 4 (dg 2 (xcc *> l))))) R.
Proof.
  intros l R.
  follow hop_in.
  follow ls_3. simpl (1 + 3).
  change (dg 4 (dg 2 l)) with (dg (0 + 4) (dg 2 l)).
  follow ls_g. simpl (0 + 1). simpl (2 + 3).
  follow hh_5.
  follow hh_4.
  change (S1 >> tk1 1 (tk 2 (tk1 1 (tk 3 (tk 6 (tk 5 R)))))) with (tk1 2 (tk 2 (tk1 1 (tk 3 (tk 6 (tk 5 R)))))).
  follow hop_out.
  follow hh_5.
  finish.
Qed.

Lemma hop1 : forall m l,
  END (rep x3 (m + 3) (Pc (dg 3 (dg 4 (dg 2 l))))) -->*
  END (rep x3 (m + 1) (Pc (dg 3 (dg 4 (dg 2 (xcc *> l)))))).
Proof.
  intros m l.
  rewrite end_lg.
  follow lg_3.
  follow r1.
  replace (m + 3) with (S (S (S m))) by lia.
  change (rep y5 (S (S (S m))) (tk1 2 (const S0))) with (tk 5 (tk 5 (tk 5 (rep y5 m (tk1 2 (const S0)))))).
  follow hop_mid.
  follow r3.
  replace (m + 1) with (S m) by lia.
  change (rep x3 (S m) (Pc (dg 3 (dg 4 (dg 2 (xcc *> l)))))) with (dg 3 (rep x3 m (Pc (dg 3 (dg 4 (dg 2 (xcc *> l))))))).
  exact (hh_end 2 _).
Qed.

Lemma hop_q : forall q m l,
  END (rep x3 (2 * q + (m + 1)) (Pc (dg 3 (dg 4 (dg 2 l))))) -->*
  END (rep x3 (m + 1) (Pc (dg 3 (dg 4 (dg 2 (rep xcc q l)))))).
Proof.
  induction q as [|q IH]; intros m l.
  - replace (2 * 0 + (m + 1)) with (m + 1) by lia. finish.
  - replace (2 * S q + (m + 1)) with ((2 * q + m) + 3) by lia.
    follow hop1.
    replace (2 * q + m + 1) with (2 * q + (m + 1)) by lia.
    follow IH.
    rewrite rep_shift. finish.
Qed.
(* A macro simulator. A stack is a list of items, nearest the head first: a cell, or a block repeated n times. *)
Inductive blk := bx3 | by5 | bxc | byc | bx43 | bxr.

Definition cells (b : blk) : list Sym :=
  match b with
  | bx3 => x3
  | by5 => y5
  | bxc => xcc
  | byc => ycc
  | bx43 => x43
  | bxr => xr
  end.

Inductive item := I0 | I1 | IR (b : blk) (n : N).

Fixpoint ex (t : list item) (s : side) : side :=
  match t with
  | [] => s
  | I0 :: t' => S0 >> ex t' s
  | I1 :: t' => S1 >> ex t' s
  | IR b n :: t' => rep (cells b) (N.to_nat n) (ex t' s)
  end.

Definition it (s : Sym) : item := match s with S0 => I0 | S1 => I1 end.

Fixpoint ofl (c : list Sym) (t : list item) : list item :=
  match c with
  | [] => t
  | s :: c' => it s :: ofl c' t
  end.

Lemma ex_ofl : forall c t s, ex (ofl c t) s = c *> ex t s.
Proof.
  induction c as [|a c IH]; intros t s; [reflexivity|].
  destruct a; simpl; rewrite IH; reflexivity.
Qed.

Lemma ex_app : forall a b s, ex (a ++ b) s = ex a (ex b s).
Proof.
  induction a as [|i a IH]; intros b s; [reflexivity|].
  destruct i; simpl; rewrite IH; reflexivity.
Qed.

Definition blk_eqb (a b : blk) : bool :=
  match a, b with
  | bx3, bx3 | by5, by5 | bxc, bxc | byc, byc | bx43, bx43 | bxr, bxr => true
  | _, _ => false
  end.

Lemma blk_eqb_true : forall a b, blk_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

Definition mkrep (b : blk) (n : N) (t : list item) : list item :=
  match n with
  | N0 => t
  | _ => IR b n :: t
  end.

Lemma ex_mkrep : forall b n t s, ex (mkrep b n t) s = rep (cells b) (N.to_nat n) (ex t s).
Proof. intros b n t s. destruct n; reflexivity. Qed.

Definition pushrep (b : blk) (n : N) (t : list item) : list item :=
  match n with
  | N0 => t
  | _ =>
    match t with
    | IR b' m :: t' => if blk_eqb b b' then IR b (n + m) :: t' else IR b n :: t
    | _ => IR b n :: t
    end
  end.

Lemma ex_pushrep : forall b n t s, ex (pushrep b n t) s = rep (cells b) (N.to_nat n) (ex t s).
Proof.
  intros b n t s. destruct n as [|p]; [reflexivity|].
  destruct t as [|[| |b' m] t']; try reflexivity.
  simpl pushrep. destruct (blk_eqb b b') eqn:E; [|reflexivity].
  apply blk_eqb_true in E. subst b'.
  transitivity (rep (cells b) (N.to_nat (N.pos p + m)) (ex t' s)); [reflexivity|].
  rewrite N2Nat.inj_add, rep_add. reflexivity.
Qed.

Lemma to_nat_pos : forall p, N.to_nat (Npos p) = S (N.to_nat (N.pred (Npos p))).
Proof.
  intros p. rewrite <- N2Nat.inj_succ, N.succ_pred; [reflexivity|discriminate].
Qed.

Definition popi (t : list item) : option (Sym * list item) :=
  match t with
  | [] => None
  | I0 :: t' => Some (S0, t')
  | I1 :: t' => Some (S1, t')
  | IR b n :: t' =>
    match n with
    | N0 => None
    | Npos p =>
      match cells b with
      | [] => None
      | s :: c => Some (s, ofl c (mkrep b (N.pred (Npos p)) t'))
      end
    end
  end.

Lemma rep_cons : forall b s c m X, cells b = s :: c ->
  rep (cells b) (S m) X = s >> c *> rep (cells b) m X.
Proof. intros b s c m X H. simpl. rewrite H. reflexivity. Qed.

Lemma popi_ok : forall t c t' s, popi t = Some (c, t') -> ex t s = c >> ex t' s.
Proof.
  intros t c t' s H.
  destruct t as [|[| |b n] t1]; simpl in H; try discriminate.
  - injection H as <- <-. reflexivity.
  - injection H as <- <-. reflexivity.
  - destruct n as [|p]; [discriminate|].
    destruct (cells b) as [|s0 c0] eqn:Ec; [discriminate|].
    injection H as <- <-.
    transitivity (rep (cells b) (N.to_nat (N.pos p)) (ex t1 s)); [reflexivity|].
    rewrite to_nat_pos, (rep_cons _ _ _ _ _ Ec), ex_ofl, ex_mkrep. reflexivity.
Qed.

Definition popR (t : list item) : option (Sym * list item) :=
  match t with
  | [] => Some (S0, [])
  | _ => popi t
  end.

Lemma popR_ok : forall t c t', popR t = Some (c, t') -> ex t (const S0) = c >> ex t' (const S0).
Proof.
  intros t c t' H. destruct t as [|i t1].
  - simpl in H. injection H as <- <-. simpl. apply const_unfold.
  - apply popi_ok. exact H.
Qed.

Definition popL (ab : bool) (t : list item) : option (Sym * list item) :=
  match t with
  | [] => if ab then Some (S0, []) else None
  | _ => popi t
  end.

Lemma popL_ok : forall ab t c t' X, (ab = true -> X = const S0) -> popL ab t = Some (c, t') -> ex t X = c >> ex t' X.
Proof.
  intros ab t c t' X HX H. destruct t as [|i t1].
  - simpl in H. destruct ab; [|discriminate]. injection H as <- <-.
    rewrite (HX eq_refl). simpl. apply const_unfold.
  - apply popi_ok. exact H.
Qed.

Definition pushL (ab : bool) (w : Sym) (t : list item) : list item :=
  match ab, t, w with
  | true, [], S0 => []
  | _, _, _ => it w :: t
  end.

Lemma ex_pushL : forall ab w t X, (ab = true -> X = const S0) -> ex (pushL ab w t) X = w >> ex t X.
Proof.
  intros ab w t X HX. destruct ab, t, w; try reflexivity.
  rewrite (HX eq_refl). simpl. apply const_unfold.
Qed.

Definition pushR (w : Sym) (t : list item) : list item :=
  match t, w with
  | [], S0 => []
  | _, _ => it w :: t
  end.

Lemma ex_pushR : forall w t, ex (pushR w t) (const S0) = w >> ex t (const S0).
Proof.
  intros w t. destruct t, w; try reflexivity.
  simpl. apply const_unfold.
Qed.

Definition Cfg : Type := (Q * list item * list item)%type.

Definition lift (c : Cfg) (X : side) : Q * tape :=
  match c with
  | (q, ll, rr) => ex ll X {{q}}> ex rr (const S0)
  end.

Lemma mv_r : forall q s w q' l r, tm (q, s) = Some (w, R, q') ->
  l {{q}}> s >> r --> w >> l {{q'}}> r.
Proof. intros q s w q' l r H. exact (step_right H). Qed.

Lemma mv_l : forall q s w q' s2 l r, tm (q, s) = Some (w, L, q') ->
  s2 >> l {{q}}> s >> r --> l {{q'}}> s2 >> w >> r.
Proof. intros q s w q' s2 l r H. exact (step_left H). Qed.

Definition cstep (ab : bool) (c : Cfg) : option Cfg :=
  match c with
  | (q, ll, rr) =>
    match popR rr with
    | None => None
    | Some (s, r1) =>
      match tm (q, s) with
      | None => None
      | Some (w, R, q') => Some (q', pushL ab w ll, r1)
      | Some (w, L, q') =>
        match popL ab ll with
        | None => None
        | Some (s2, l1) => Some (q', l1, pushR s2 (pushR w r1))
        end
      end
    end
  end.

Lemma cstep_ok : forall ab c c' X, (ab = true -> X = const S0) -> cstep ab c = Some c' ->
  lift c X --> lift c' X.
Proof.
  intros ab [[q ll] rr] c' X HX H. unfold cstep in H.
  destruct (popR rr) as [[s r1]|] eqn:E1; [|discriminate].
  destruct (tm (q, s)) as [[[w d] q']|] eqn:E2; [|discriminate].
  destruct d.
  - destruct (popL ab ll) as [[s2 l1]|] eqn:E3; [|discriminate].
    injection H as <-. unfold lift.
    rewrite (popR_ok _ _ _ E1), (popL_ok _ _ _ _ _ HX E3), !ex_pushR.
    exact (mv_l _ _ _ _ _ _ _ E2).
  - injection H as <-. unfold lift.
    rewrite (popR_ok _ _ _ E1), (ex_pushL _ _ _ _ HX).
    exact (mv_r _ _ _ _ _ _ E2).
Qed.

(* Strip a literal prefix. *)
Fixpoint strip (c : list Sym) (t : list item) : option (list item) :=
  match c with
  | [] => Some t
  | S0 :: c' => match t with I0 :: t' => strip c' t' | _ => None end
  | S1 :: c' => match t with I1 :: t' => strip c' t' | _ => None end
  end.

Lemma strip_ok : forall c t t' s, strip c t = Some t' -> ex t s = c *> ex t' s.
Proof.
  induction c as [|a c IH]; intros t t' s H.
  - simpl in H. injection H as <-. reflexivity.
  - destruct a; simpl in H; destruct t as [|[| |b n] t1]; try discriminate; simpl; rewrite (IH _ _ _ H); reflexivity.
Qed.

Definition W3 : list Sym := [S0;S0;S1;S0;S0;S1;S0;S1;S0;S1].
Definition part : list Sym := [S0;S0;S1;S0;S1;S0;S1].
Definition hoppat : list Sym :=
  [S1;S0;S0;S1;S0;S0;S1; S1;S0;S0;S1;S0;S1;S0;S1; S1;S0;S0;S1;S0;S1;S0;S1;S0;S1; S1;S0;S0;S1;S0;S1].

Lemma part_end : forall l, part *> l {{D}}> const S0 = END l.
Proof. reflexivity. Qed.

(* Chain rules, from the laws above. *)
Definition ch12 (c : Cfg) : option Cfg :=
  match c with
  | (D, I1 :: I1 :: IR b n :: t, I0 :: I0 :: I0 :: I0 :: r) =>
    match b with
    | bx3 => Some (D, I1 :: I1 :: t, I0 :: I0 :: I0 :: I0 :: pushrep by5 n r)
    | bxc => Some (D, I1 :: I1 :: t, I0 :: I0 :: I0 :: I0 :: pushrep byc n r)
    | _ => None
    end
  | _ => None
  end.

Definition ch34 (c : Cfg) : option Cfg :=
  match c with
  | (D, ll, I0 :: I0 :: IR b n :: r) =>
    match b with
    | by5 => match strip W3 ll with Some t => Some (D, ofl W3 (pushrep bx3 n t), I0 :: I0 :: r) | None => None end
    | byc => match strip W3 ll with Some t => Some (D, ofl W3 (pushrep bx43 n t), I0 :: I0 :: r) | None => None end
    | _ => None
    end
  | _ => None
  end.

Definition ch5 (c : Cfg) : option Cfg :=
  match c with
  | (D, I0 :: t, IR byc n :: r) =>
    let k := N.div2 n in
    if andb (N.ltb 0 k) (N.leb (k + k) n)
    then Some (D, I0 :: pushrep bxr k t, mkrep byc (n - (k + k)) r)
    else None
  | _ => None
  end.

Lemma ch12_ok : forall c c' X, ch12 c = Some c' -> lift c X -->* lift c' X.
Proof.
  intros [[q ll] rr] c' X H. unfold ch12 in H.
  destruct q; try discriminate.
  destruct ll as [|[| |b0 n0] l1]; try discriminate.
  destruct l1 as [|[| |b1 n1] l2]; try discriminate.
  destruct l2 as [|[| |b n] l3]; try discriminate.
  destruct rr as [|[| |b2 n2] r1]; try discriminate.
  destruct r1 as [|[| |b3 n3] r2]; try discriminate.
  destruct r2 as [|[| |b4 n4] r3]; try discriminate.
  destruct r3 as [|[| |b5 n5] r4]; try discriminate.
  destruct b; try discriminate; injection H as <-; unfold lift; cbn [ex cells]; rewrite ex_pushrep; cbn [cells].
  - exact (r1 (N.to_nat n) (ex l3 X) (ex r4 (const S0))).
  - exact (r2 (N.to_nat n) (ex l3 X) (ex r4 (const S0))).
Qed.

Lemma ch3_aux : forall ll t n r X, strip W3 ll = Some t ->
  lift (D, ll, I0 :: I0 :: IR by5 n :: r) X -->* lift (D, ofl W3 (pushrep bx3 n t), I0 :: I0 :: r) X.
Proof.
  intros ll t n r X E. unfold lift.
  rewrite (strip_ok _ _ _ X E), ex_ofl, ex_pushrep. cbn [ex cells].
  exact (r3 (N.to_nat n) (ex t X) (ex r (const S0))).
Qed.

Lemma ch4_aux : forall ll t n r X, strip W3 ll = Some t ->
  lift (D, ll, I0 :: I0 :: IR byc n :: r) X -->* lift (D, ofl W3 (pushrep bx43 n t), I0 :: I0 :: r) X.
Proof.
  intros ll t n r X E. unfold lift.
  rewrite (strip_ok _ _ _ X E), ex_ofl, ex_pushrep. cbn [ex cells].
  exact (r4 (N.to_nat n) (ex t X) (ex r (const S0))).
Qed.

Lemma ch34_ok : forall c c' X, ch34 c = Some c' -> lift c X -->* lift c' X.
Proof.
  intros [[q ll] rr] c' X H. unfold ch34 in H.
  destruct q; try discriminate.
  destruct rr as [|[| |b2 n2] r1]; try discriminate.
  destruct r1 as [|[| |b3 n3] r2]; try discriminate.
  destruct r2 as [|[| |b n] r3]; try discriminate.
  destruct b; try discriminate; destruct (strip W3 ll) as [t|] eqn:E; try discriminate;
    injection H as <-.
  - exact (ch3_aux _ _ _ _ _ E).
  - exact (ch4_aux _ _ _ _ _ E).
Qed.

Lemma ch5_ok : forall c c' X, ch5 c = Some c' -> lift c X -->* lift c' X.
Proof.
  intros [[q ll] rr] c' X H. unfold ch5 in H.
  destruct q; try discriminate.
  destruct ll as [|[| |b0 n0] t]; try discriminate.
  destruct rr as [|[| |b n] r1]; try discriminate.
  destruct b; try discriminate.
  destruct (andb (N.ltb 0 (N.div2 n)) (N.leb (N.div2 n + N.div2 n) n)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [_ E2]. apply N.leb_le in E2.
  injection H as <-. unfold lift. cbn [ex cells]. rewrite ex_pushrep, ex_mkrep. cbn [cells].
  set (k := N.div2 n) in *.
  assert (En : N.to_nat n = (N.to_nat k + N.to_nat k) + N.to_nat (n - (k + k))).
  { rewrite <- !N2Nat.inj_add. f_equal. lia. }
  rewrite En, rep_add.
  exact (r5 (N.to_nat k) (ex t X) (rep ycc (N.to_nat (n - (k + k))) (ex r1 (const S0)))).
Qed.

(* Tail of 3s. *)
Definition tail1 (t : list item) : option (N * list item) :=
  match strip x3 t with
  | Some t' => Some (1%N, t')
  | None =>
    match t with
    | IR bx3 n :: t' => Some (n, t')
    | _ => None
    end
  end.

Lemma tail1_ok : forall t m t' X, tail1 t = Some (m, t') -> ex t X = rep x3 (N.to_nat m) (ex t' X).
Proof.
  intros t m t' X H. unfold tail1 in H.
  destruct (strip x3 t) as [t1|] eqn:E.
  - injection H as <- <-. rewrite (strip_ok _ _ _ X E). reflexivity.
  - destruct t as [|[| |b n] t1]; try discriminate.
    destruct b; try discriminate. injection H as <- <-. reflexivity.
Qed.

Fixpoint ftail (fuel : nat) (t : list item) (acc : N) : N * list item :=
  match fuel with
  | O => (acc, t)
  | S f =>
    match tail1 t with
    | Some (m, t') => ftail f t' (acc + m)
    | None => (acc, t)
    end
  end.

Lemma ftail_ok : forall fuel t acc n t' X, ftail fuel t acc = (n, t') ->
  rep x3 (N.to_nat acc) (ex t X) = rep x3 (N.to_nat n) (ex t' X).
Proof.
  induction fuel as [|f IH]; intros t acc n t' X H; simpl in H.
  - injection H as <- <-. reflexivity.
  - destruct (tail1 t) as [[m t1]|] eqn:E.
    + rewrite <- (IH _ _ _ _ X H). rewrite (tail1_ok _ _ _ X E).
      rewrite N2Nat.inj_add, rep_add. reflexivity.
    + injection H as <- <-. reflexivity.
Qed.

(* Digit parsing. *)
Fixpoint ppairs (t : list item) (g : nat) : nat * list item :=
  match t with
  | I0 :: I1 :: t' => ppairs t' (S g)
  | _ => (g, t)
  end.

Lemma ppairs_ok : forall t g g' t' s, ppairs t g = (g', t') ->
  pr g *> ex t s = pr g' *> ex t' s.
Proof.
  fix IH 1. intros t g g' t' s H.
  destruct t as [|[| |b n] t1]; simpl in H; try (injection H as <- <-; reflexivity).
  destruct t1 as [|[| |b n] t2]; try (injection H as <- <-; reflexivity).
  rewrite <- (IH _ _ _ _ s H).
  simpl ex. clear -g. revert g. induction g as [|g IH2]; [reflexivity|]. simpl. rewrite IH2. reflexivity.
Qed.

Fixpoint pdigs (fuel : nat) (t : list item) : list nat * list item :=
  match fuel with
  | O => ([], t)
  | S f =>
    match t with
    | I1 :: I0 :: t1 =>
      match ppairs t1 0 with
      | (O, _) => ([], t)
      | (g, t2) =>
        match pdigs f t2 with
        | (ds, t3) => (g :: ds, t3)
        end
      end
    | _ => ([], t)
    end
  end.

Lemma pdigs_ok : forall fuel t ds t' s, pdigs fuel t = (ds, t') -> ex t s = lw ds (ex t' s).
Proof.
  induction fuel as [|f IH]; intros t ds t' s H; simpl in H.
  - injection H as <- <-. reflexivity.
  - destruct t as [|[| |b n] t1]; try (injection H as <- <-; reflexivity).
    destruct t1 as [|[| |b n] t2]; try (injection H as <- <-; reflexivity).
    destruct (ppairs t2 0) as [g t3] eqn:E.
    destruct g as [|g].
    + injection H as <- <-. reflexivity.
    + destruct (pdigs f t3) as [ds1 t4] eqn:E2. injection H as <- <-.
      simpl ex. simpl lw. unfold dg. f_equal. f_equal.
      rewrite <- (IH _ _ _ s E2).
      exact (ppairs_ok t2 0 (S g) t3 s E).
Qed.

Fixpoint pairs (g : nat) (t : list item) : list item :=
  match g with
  | O => t
  | S g' => I0 :: I1 :: pairs g' t
  end.

Fixpoint enc (w : list nat) (t : list item) : list item :=
  match w with
  | [] => t
  | g :: w' => I1 :: I0 :: pairs g (enc w' t)
  end.

Lemma ex_pairs : forall g t s, ex (pairs g t) s = pr g *> ex t s.
Proof. induction g as [|g IH]; intros t s; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma ex_enc : forall w t s, ex (enc w t) s = lw w (ex t s).
Proof.
  induction w as [|g w IH]; intros t s; [reflexivity|].
  simpl. rewrite ex_pairs, IH. reflexivity.
Qed.
(* Rules at the right end of a sweep. *)
Definition nrm (c : Cfg) : Cfg :=
  match c with
  | (D, ll, []) =>
    match strip part ll with
    | Some t =>
      match ftail 64 t 0%N with
      | (n, t1) => (D, ofl part (mkrep bx3 n t1), [])
      end
    | None => c
    end
  | _ => c
  end.

Lemma nrm_ok : forall c X, lift (nrm c) X = lift c X.
Proof.
  intros [[q ll] rr] X. unfold nrm.
  destruct q; try reflexivity.
  destruct rr; try reflexivity.
  destruct (strip part ll) as [t|] eqn:E; [|reflexivity].
  destruct (ftail 64 t 0%N) as [n t1] eqn:E2.
  pose proof (ftail_ok _ _ _ _ _ X E2) as H. change (ex t X = rep x3 (N.to_nat n) (ex t1 X)) in H.
  unfold lift. rewrite ex_ofl, ex_mkrep, (strip_ok _ _ _ X E), H. reflexivity.
Qed.

Definition out (h : nat) (W : list nat) (n : N) (t : list item) : list item :=
  if Nat.eqb h 3 then IR bx3 (n + 1) :: enc W t else IR bx3 n :: enc (h :: W) t.

Lemma out_ok : forall h W n t X,
  ex (out h W n t) X = rep x3 (N.to_nat n) (lw (h :: W) (ex t X)).
Proof.
  intros h W n t X. unfold out.
  destruct (Nat.eqb h 3) eqn:E.
  - apply Nat.eqb_eq in E. subst h.
    transitivity (rep x3 (N.to_nat (n + 1)) (ex (enc W t) X)); [reflexivity|].
    rewrite N2Nat.inj_add, rep_add, ex_enc. reflexivity.
  - transitivity (rep x3 (N.to_nat n) (ex (enc (h :: W) t) X)); [reflexivity|].
    rewrite ex_enc. reflexivity.
Qed.

Definition e_hop (n : N) (t1 : list item) : option (list item) :=
  if N.leb 3 n then
    match strip hoppat t1 with
    | Some t2 =>
      let q := N.div2 (n - 1) in
      if N.leb (q + q + 1) n
      then Some (IR bx3 (n - (q + q)) :: ofl hoppat (pushrep bxc q t2))
      else None
    | None => None
    end
  else None.

Lemma hoppat_Pc : forall l, hoppat *> l = Pc (dg 3 (dg 4 (dg 2 l))).
Proof. reflexivity. Qed.

Lemma hop_a : forall a m l,
  END (rep x3 (2 * a + (m + 1)) (hoppat *> l)) -->* END (rep x3 (m + 1) (hoppat *> rep xcc a l)).
Proof.
  intros a m l. exact (hop_q a m l).
Qed.

Lemma ex_ir : forall b k t X, ex (IR b k :: t) X = rep (cells b) (N.to_nat k) (ex t X).
Proof. reflexivity. Qed.

Lemma e_hop_aux : forall n t1 t2 q X, strip hoppat t1 = Some t2 -> (q + q + 1 <= n)%N ->
  END (rep x3 (N.to_nat n) (ex t1 X)) -->*
  END (ex (IR bx3 (n - (q + q)) :: ofl hoppat (pushrep bxc q t2)) X).
Proof.
  intros n t1 t2 q X E1 E2.
  rewrite ex_ir, ex_ofl, ex_pushrep, (strip_ok _ _ _ X E1).
  change (cells bx3) with x3. change (cells bxc) with xcc.
  destruct (N.to_nat (n - (q + q))) as [|m] eqn:Eb; [lia|].
  assert (En : N.to_nat n = 2 * N.to_nat q + (m + 1)) by lia.
  rewrite En.
  replace (S m) with (m + 1) by lia.
  exact (hop_a _ _ _).
Qed.

Lemma e_hop_ok : forall n t1 o X, e_hop n t1 = Some o ->
  END (rep x3 (N.to_nat n) (ex t1 X)) -->* END (ex o X).
Proof.
  intros n t1 o X H. unfold e_hop in H.
  destruct (N.leb 3 n) eqn:E0; [|discriminate].
  destruct (strip hoppat t1) as [t2|] eqn:E1; [|discriminate].
  destruct (N.leb (N.div2 (n - 1) + N.div2 (n - 1) + 1) n) eqn:E2; [|discriminate].
  injection H as <-.
  apply N.leb_le in E2.
  exact (e_hop_aux n t1 t2 (N.div2 (n - 1)) X E1 E2).
Qed.

Definition iskey (ds : list nat) : bool :=
  match ds with
  | [1;1;1;1;3] => true
  | [1;1;2;4;1] => true
  | _ => false
  end.

Lemma iskey_ok : forall ds, iskey ds = true -> iterT 36 (ds ++ units4) = Some (repeat 3 18 ++ ds).
Proof.
  intros ds H.
  assert (K : ds = key1 \/ ds = key2).
  { unfold iskey in H.
    repeat match type of H with
    | context [match ?x with _ => _ end] => destruct x; try discriminate
    end; auto. }
  destruct K as [-> | ->]; [exact cyc1 | exact cyc2].
Qed.

Definition e_eat (n : N) (t1 : list item) : option (list item) :=
  if N.leb 1 n then
    match pdigs 64 t1 with
    | (ds, IR bx43 k :: t3) =>
      if iskey ds then
        let q := N.div (k - 1) 4 in
        if andb (N.ltb 4 k) (N.leb (4 * q + 1) k)
        then Some (IR bx3 (n + 18 * q) :: enc ds (IR bx43 (k - 4 * q) :: t3))
        else None
      else None
    | _ => None
    end
  else None.

Lemma e_eat_aux : forall n t1 ds k t3 q X, (1 <= n)%N -> pdigs 64 t1 = (ds, IR bx43 k :: t3) -> iskey ds = true ->
  (4 * q + 1 <= k)%N ->
  END (rep x3 (N.to_nat n) (ex t1 X)) -->*
  END (ex (IR bx3 (n + 18 * q) :: enc ds (IR bx43 (k - 4 * q) :: t3)) X).
Proof.
  intros n t1 ds k t3 q X E0 E1 E2 E32.
  rewrite (pdigs_ok _ _ _ _ X E1), !ex_ir, ex_enc, !ex_ir.
  change (cells bx3) with x3. change (cells bx43) with x43.
  destruct (N.to_nat n) as [|n1] eqn:En; [lia|].
  assert (Ek : N.to_nat k = 4 * N.to_nat q + N.to_nat (k - 4 * q)) by lia.
  assert (En2 : N.to_nat (n + 18 * q) = S n1 + 18 * N.to_nat q) by lia.
  rewrite Ek, En2, rep_add.
  exact (eat_q ds (N.to_nat q) n1 (rep x43 (N.to_nat (k - 4 * q)) (ex t3 X)) (iskey_ok ds E2)).
Qed.

Lemma e_eat_ok : forall n t1 o X, e_eat n t1 = Some o ->
  END (rep x3 (N.to_nat n) (ex t1 X)) -->* END (ex o X).
Proof.
  intros n t1 o X H. unfold e_eat in H.
  destruct (N.leb 1 n) eqn:E0; [|discriminate].
  destruct (pdigs 64 t1) as [ds t2] eqn:E1.
  destruct t2 as [|[| |b k] t3]; try discriminate.
  destruct b; try discriminate.
  destruct (iskey ds) eqn:E2; [|discriminate].
  destruct (andb (N.ltb 4 k) (N.leb (4 * N.div (k - 1) 4 + 1) k)) eqn:E3; [|discriminate].
  apply andb_prop in E3. destruct E3 as [_ E32]. apply N.leb_le in E32.
  apply N.leb_le in E0.
  injection H as <-.
  exact (e_eat_aux n t1 ds k t3 (N.div (k - 1) 4) X E0 E1 E2 E32).
Qed.

Definition e_sw (n : N) (t1 : list item) : option (list item) :=
  if N.leb 1 n then
    match pdigs 64 t1 with
    | (ds, t2) =>
      match bw 3 ds with
      | Some (h, W) => Some (out h W n t2)
      | None =>
        match t2 with
        | IR bx43 c :: t3 =>
          if N.ltb 0 c then
            match bw 3 (ds ++ [4;3]) with
            | Some (h, W) => Some (out h W n (mkrep bx43 (N.pred c) t3))
            | None => None
            end
          else None
        | _ => None
        end
      end
    end
  else None.

Lemma sw_core : forall n ds h W t X, (1 <= n)%N -> bw 3 ds = Some (h, W) ->
  END (rep x3 (N.to_nat n) (lw ds (ex t X))) -->* END (ex (out h W n t) X).
Proof.
  intros n ds h W t X H1 H2. rewrite out_ok.
  destruct (N.to_nat n) as [|n1] eqn:En; [lia|].
  exact (sweep_tail n1 ds h W (ex t X) H2).
Qed.

Lemma e_sw_ok : forall n t1 o X, e_sw n t1 = Some o ->
  END (rep x3 (N.to_nat n) (ex t1 X)) -->* END (ex o X).
Proof.
  intros n t1 o X H. unfold e_sw in H.
  destruct (N.leb 1 n) eqn:E0; [|discriminate].
  apply N.leb_le in E0.
  destruct (pdigs 64 t1) as [ds t2] eqn:E1.
  rewrite (pdigs_ok _ _ _ _ X E1).
  destruct (bw 3 ds) as [[h W]|] eqn:E2.
  - injection H as <-. exact (sw_core n ds h W t2 X E0 E2).
  - destruct t2 as [|[| |b c] t3]; try discriminate.
    destruct b; try discriminate.
    destruct (N.ltb 0 c) eqn:E3; [|discriminate].
    apply N.ltb_lt in E3.
    destruct (bw 3 (ds ++ [4;3])) as [[h W]|] eqn:E4; [|discriminate].
    injection H as <-.
    assert (Eq : ex (IR bx43 c :: t3) X = lw [4;3] (ex (mkrep bx43 (N.pred c) t3) X)).
    { rewrite ex_mkrep, ex_ir.
      assert (Ec : N.to_nat c = S (N.to_nat (N.pred c))) by lia.
      rewrite Ec. reflexivity. }
    rewrite Eq, <- lw_app.
    exact (sw_core n _ h W _ X E0 E4).
Qed.

Definition e_rules (c : Cfg) : option Cfg :=
  match c with
  | (D, ll, []) =>
    match strip part ll with
    | Some (IR bx3 n :: t1) =>
      match e_hop n t1 with
      | Some o => Some (D, ofl part o, [])
      | None =>
        match e_eat n t1 with
        | Some o => Some (D, ofl part o, [])
        | None =>
          match e_sw n t1 with
          | Some o => Some (D, ofl part o, [])
          | None => None
          end
        end
      end
    | _ => None
    end
  | _ => None
  end.

Lemma e_lift : forall ll n t1 o X, strip part ll = Some (IR bx3 n :: t1) ->
  END (rep x3 (N.to_nat n) (ex t1 X)) -->* END (ex o X) ->
  lift (D, ll, []) X -->* lift (D, ofl part o, []) X.
Proof.
  intros ll n t1 o X E H.
  unfold lift. rewrite (strip_ok _ _ _ X E), ex_ofl.
  exact H.
Qed.

Lemma e_rules_ok : forall c c' X, e_rules c = Some c' -> lift c X -->* lift c' X.
Proof.
  intros [[q ll] rr] c' X H. unfold e_rules in H.
  destruct q; try discriminate.
  destruct rr; try discriminate.
  destruct (strip part ll) as [t|] eqn:E; try discriminate.
  destruct t as [|[| |b n] t1]; try discriminate.
  destruct b; try discriminate.
  destruct (e_hop n t1) as [o|] eqn:E1.
  { injection H as <-. exact (e_lift _ _ _ _ _ E (e_hop_ok _ _ _ X E1)). }
  destruct (e_eat n t1) as [o|] eqn:E2.
  { injection H as <-. exact (e_lift _ _ _ _ _ E (e_eat_ok _ _ _ X E2)). }
  destruct (e_sw n t1) as [o|] eqn:E3; [|discriminate].
  injection H as <-. exact (e_lift _ _ _ _ _ E (e_sw_ok _ _ _ X E3)).
Qed.

Definition astep (ab : bool) (c : Cfg) : option Cfg :=
  let c1 := nrm c in
  match e_rules c1 with
  | Some c2 => Some c2
  | None =>
    match ch12 c1 with
    | Some c2 => Some c2
    | None =>
      match ch34 c1 with
      | Some c2 => Some c2
      | None =>
        match ch5 c1 with
        | Some c2 => Some c2
        | None => cstep ab c1
        end
      end
    end
  end.

Lemma astep_ok : forall ab c c' X, (ab = true -> X = const S0) -> astep ab c = Some c' ->
  lift c X -->* lift c' X.
Proof.
  intros ab c c' X HX H. unfold astep in H.
  rewrite <- (nrm_ok c X).
  destruct (e_rules (nrm c)) as [c2|] eqn:E1.
  { injection H as <-. exact (e_rules_ok _ _ _ E1). }
  destruct (ch12 (nrm c)) as [c2|] eqn:E2.
  { injection H as <-. exact (ch12_ok _ _ _ E2). }
  destruct (ch34 (nrm c)) as [c2|] eqn:E3.
  { injection H as <-. exact (ch34_ok _ _ _ E3). }
  destruct (ch5 (nrm c)) as [c2|] eqn:E4.
  { injection H as <-. exact (ch5_ok _ _ _ E4). }
  eapply evstep_step; [exact (cstep_ok _ _ _ _ HX H)|apply evstep_refl].
Qed.

Fixpoint runp (p : positive) (ab : bool) (c : Cfg) : option Cfg :=
  match p with
  | xH => astep ab c
  | xO p' =>
    match runp p' ab c with
    | Some c1 => runp p' ab c1
    | None => None
    end
  | xI p' =>
    match astep ab c with
    | Some c0 =>
      match runp p' ab c0 with
      | Some c1 => runp p' ab c1
      | None => None
      end
    | None => None
    end
  end.

Lemma runp_ok : forall p ab c c' X, (ab = true -> X = const S0) -> runp p ab c = Some c' ->
  lift c X -->* lift c' X.
Proof.
  induction p as [p IH|p IH|]; intros ab c c' X HX H; simpl in H.
  - destruct (astep ab c) as [c0|] eqn:E1; [|discriminate].
    destruct (runp p ab c0) as [c1|] eqn:E2; [|discriminate].
    eapply evstep_trans; [exact (astep_ok _ _ _ _ HX E1)|].
    eapply evstep_trans; [exact (IH _ _ _ _ HX E2)|].
    exact (IH _ _ _ _ HX H).
  - destruct (runp p ab c) as [c1|] eqn:E2; [|discriminate].
    eapply evstep_trans; [exact (IH _ _ _ _ HX E2)|].
    exact (IH _ _ _ _ HX H).
  - exact (astep_ok _ _ _ _ HX H).
Qed.

(* The run. *)
Definition K2 : N := 732592001087343581%N.
Definition K3 : N := 732592001087343542%N.
Definition R0 : list item := [I1;I1;I0;I1;I1;I1;I1;I0;I0;I0;I1;I1;I1;I1;I1;I0;I0;I0;I1;I1;I0;I1;I1;I1;I1;I0;I0;I0;I1;I1;I1;I1;I0;I0;I0;I1;I1;I1;I1;I0;I0;I0;I1;I1;I1;I1;I1;I0;I0;I0;I1;I1;I1;I1;I0;I0;I0;I1;I0;I1;I1;I1;I1;I0;I0;I0;I1;I1].
Definition Lit : list item := [I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I1;I1;I0;I0;I1;I0;I0;I1;I1;I0;I0;I1;I1;I0;I0;I1;I1;I0;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I1;I0;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I1;I0;I0;I1;I0;I1;I1;I1;I0;I0;I1;I0;I0;I1;I1;I0;I0;I1;I1;I0;I0;I1;I0;I1;I0;I1;I1;I0;I0;I1;I0;I1].

Definition Scf : Cfg := (D, [I0; IR bxr K2], R0).
Definition S1cf : Cfg := match cstep false Scf with Some c => c | None => Scf end.

Lemma cstep1 : cstep false Scf = Some S1cf.
Proof. reflexivity. Qed.

Lemma cyc_run : runp 2037112%positive false S1cf = Some (D, I0 :: IR bxr K2 :: Lit ++ [IR bxr K3], R0).
Proof. vm_cast_no_check (eq_refl (Some ((D, I0 :: IR bxr K2 :: Lit ++ [IR bxr K3], R0) : Cfg))). Qed.

Lemma lift_app : forall q a T r X, lift (q, a ++ T, r) X = lift (q, a, r) (ex T X).
Proof. intros q a T r X. unfold lift. rewrite ex_app. reflexivity. Qed.

Theorem cycle : forall X, exists X', lift Scf X -->+ lift Scf X'.
Proof.
  intros X. exists (ex (Lit ++ [IR bxr K3]) X).
  eapply progress_intro.
  - exact (cstep_ok false _ _ X (fun H => match H with end) cstep1).
  - pose proof (runp_ok _ false _ _ X (fun H => match H with end) cyc_run) as H.
    change (I0 :: IR bxr K2 :: Lit ++ [IR bxr K3]) with ([I0; IR bxr K2] ++ (Lit ++ [IR bxr K3])) in H.
    rewrite lift_app in H. exact H.
Qed.

Fixpoint items_eqb (a b : list item) : bool :=
  match a, b with
  | [], [] => true
  | I0 :: a', I0 :: b' => items_eqb a' b'
  | I1 :: a', I1 :: b' => items_eqb a' b'
  | _, _ => false
  end.

Lemma items_eqb_ok : forall a b, items_eqb a b = true -> a = b.
Proof.
  induction a as [|[| |x y] a IH]; intros [|[| |x2 y2] b] H; simpl in H; try discriminate; try reflexivity.
  - f_equal. apply IH. exact H.
  - f_equal. apply IH. exact H.
Qed.

Definition chk1 (o : option Cfg) : bool :=
  match o with
  | Some (D, I0 :: IR bxr k :: _, rr) => andb (N.leb K2 k) (items_eqb rr R0)
  | _ => false
  end.

Lemma chk1_ok : forall o, chk1 o = true ->
  exists k Z, o = Some (D, I0 :: IR bxr k :: Z, R0) /\ (K2 <= k)%N.
Proof.
  intros o H. unfold chk1 in H.
  destruct o as [[[q ll] rr]|]; try discriminate.
  destruct q; try discriminate.
  destruct ll as [|[| |b0 n0] l1]; try discriminate.
  destruct l1 as [|[| |b n] Z]; try discriminate.
  destruct b; try discriminate.
  apply andb_prop in H. destruct H as [H1 H2].
  apply N.leb_le in H1. apply items_eqb_ok in H2. subst rr.
  exists n, Z. split; [reflexivity|exact H1].
Qed.

Lemma blank_run : chk1 (runp 6902025%positive true (A, [], [])) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma split_top : forall K k Z X, (K <= k)%N ->
  lift (D, I0 :: IR bxr k :: Z, R0) X = lift (D, [I0; IR bxr K], R0) (rep xr (N.to_nat (k - K)) (ex Z X)).
Proof.
  intros K k Z X H.
  assert (E : N.to_nat k = N.to_nat K + N.to_nat (k - K)) by lia.
  assert (E2 : ex (I0 :: IR bxr k :: Z) X = ex [I0; IR bxr K] (rep xr (N.to_nat (k - K)) (ex Z X))).
  { change (S0 >> rep xr (N.to_nat k) (ex Z X) = S0 >> rep xr (N.to_nat K) (rep xr (N.to_nat (k - K)) (ex Z X))).
    rewrite E, rep_add. reflexivity. }
  unfold lift. rewrite E2. reflexivity.
Qed.

Lemma nonhalt_from : forall q p, chk1 (runp p true (q, [], [])) = true -> ~ halts tm (q;; tape0).
Proof.
  intros q p Hr.
  destruct (chk1_ok _ Hr) as [k [Z [E Hk]]].
  change (q;; tape0) with (lift (q, [], []) (const S0)).
  pose proof (runp_ok _ true _ _ (const S0) (fun _ => eq_refl) E) as Hrun.
  rewrite (split_top K2 k Z (const S0) Hk) in Hrun.
  eapply multistep_nonhalt; [exact Hrun|].
  apply (progress_nonhalt_simple tm side (fun X => lift Scf X)).
  exact cycle.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof. exact (nonhalt_from A _ blank_run). Qed.

End TM1.

(* The same table, renamed and started in F. Only the run from the blank tape is its own. *)
Module TM2.
Import TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF"%string).

Definition ren (q : Q) : Q :=
  match q with A => B | B => C | C => D | D => E | E => F | F => A end.

Lemma ren_perm : Perm TM1.tm tm ren.
Proof.
  split.
  - intros [] [] H; cbn in H; try discriminate; reflexivity.
  - intros [] [] s' d q' H; cbn in H; inversion H; reflexivity.
Qed.

Lemma blank_run : chk1 (runp 6622479%positive true (F, [], [])) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof. exact (perm_nonhalt' _ _ ren F tape0 ren_perm (nonhalt_from F _ blank_run)). Qed.

End TM2.

(* The same table, renamed, mirrored and started in D. Only the run from the blank tape is its own. *)
Module TM3.
Import TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC"%string).

Definition ren (q : Q) : Q :=
  match q with A => D | B => E | C => F | D => A | E => B | F => C end.

Lemma ren_perm : Perm TM1.tm (flip tm) ren.
Proof.
  split.
  - intros [] [] H; cbn in H; try discriminate; reflexivity.
  - intros [] [] s' d q' H; cbn in H; inversion H; reflexivity.
Qed.

Lemma blank_run : chk1 (runp 10880581%positive true (D, [], [])) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  intro H. apply flip_halts in H.
  exact (perm_nonhalt' _ _ ren D tape0 ren_perm (nonhalt_from D _ blank_run) H).
Qed.

End TM3.

Print Assumptions TM1.nonhalt.
Print Assumptions TM2.nonhalt.
Print Assumptions TM3.nonhalt.
